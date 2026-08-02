/* =====================================================================
   SANDTABLE engine v2 — reads window.BATTLE and runs the table.
   A battle is data: units {keyframes, kill schedule, melee windows},
   phases, terrain (elevation blobs + optional river / open sea).
   Visual DNA descends from The Murmuration (charts.thrain.ai):
   velocity streaks on a fading trail buffer, brightness by density.
   The fallen turn grey and stay on the table.

   v2: field-space buffers — trails and fallen marks live in battlefield
   coordinates, so the table can be panned and zoomed at any time (and
   especially after the battle, to read the story the motes left behind).
   ===================================================================== */
(() => {
'use strict';
const B = window.BATTLE;
const FW = B.field.w, FH = B.field.h;
const T_END = B.tEnd ?? 100;
/* small / low-memory devices get half-resolution history buffers and a
   lighter terrain target — four full-res buffers are ~90 MB of canvas,
   which is a crash on phones, and the moving bodies are vector anyway */
const LITE = Math.min(screen.width, screen.height) < 700
  || (navigator.deviceMemory && navigator.deviceMemory <= 4);
const FS = LITE ? 1 : 2;            // buffer pixels per field unit

/* colour strings are cached globally — 10 palette colours × 40 alpha
   steps beats fourteen thousand rgba() string allocations per frame */
const CCACHE = [];
function colStr(cid, a) {
  const q = (a * 40) | 0;
  const k = cid * 48 + q;
  return CCACHE[k] || (CCACHE[k] = `rgba(${PALSTR[cid]},${(q / 40).toFixed(3)})`);
}
const PALSTR = [];

const hexToRgb = (c) => [1, 3, 5].map((i) => parseInt(c.slice(i, i + 2), 16));
const rgba = (c, a) => `rgba(${c[0]},${c[1]},${c[2]},${a})`;
const smooth = (x) => x * x * (3 - 2 * x);
const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
const D2R = Math.PI / 180;

/* ---------------- terrain: an elevation field ----------------
   EVERYTHING that turns coordinates into ground lives in terrainKernel —
   one self-contained factory shared VERBATIM by this thread (physics,
   boot rough pass, banded fallback) and the raster Worker (all tile
   builds). Change terrain math here and both worlds change together;
   there is no second copy to forget. P = {FW, FH, TR} only. */
function terrainKernel(P) {
  const FW = P.FW, FH = P.FH, TR = P.TR;
  const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
  const sstep = (x) => x * x * (3 - 2 * x);

  /* the river's course is a smooth curve (wavelengths >=1000 units): a
     4-unit LUT reproduces it to sub-pixel error and spares two sin()
     calls at every terrain pixel and every river-shy entity. It spans far
     past the field — the river flows off the table like everything else
     in the continued world. */
  let riverY = null, RVY = null, RX0 = 0;
  if (TR.river) {
    const rf = (x) => TR.river.base + Math.sin(x * 0.006 + 2) * 16 + Math.sin(x * 0.0023) * 10;
    RX0 = -2 * FW;
    const RN = Math.ceil(5 * FW / 4) + 2;
    RVY = new Float32Array(RN);
    for (let i = 0; i < RN; i++) RVY[i] = rf(RX0 + i * 4);
    riverY = (x) => {
      const g = clamp((x - RX0) / 4, 0, RN - 2), i = g | 0;
      return RVY[i] + (RVY[i + 1] - RVY[i]) * (g - i);
    };
  }
  const riverSlope = (x) => {
    const g = clamp((x - RX0) / 4, 0, RVY.length - 2), i = g | 0;
    return (RVY[i + 1] - RVY[i]) * 0.25;
  };

  /* integer-mix hash, not sin(): white noise of the same character at a
     quarter of the cost — the innermost loop of every tile build */
  function hash2(ix, iy) {
    let h = Math.imul(ix | 0, 0x27d4eb2f) ^ Math.imul(iy | 0, 0x165667b1);
    h = Math.imul(h ^ (h >>> 15), 0x85ebca6b);
    h ^= h >>> 13;
    return (h >>> 0) * 2.3283064365386963e-10;
  }
  function vnoise(x, y) {
    const ix = Math.floor(x), iy = Math.floor(y), fx = x - ix, fy = y - iy;
    const sx = fx * fx * (3 - 2 * fx), sy = fy * fy * (3 - 2 * fy);
    const a = hash2(ix, iy), b = hash2(ix + 1, iy), c = hash2(ix, iy + 1), d = hash2(ix + 1, iy + 1);
    return a + (b - a) * sx + (c - a) * sy + (a - b - c + d) * sx * sy;
  }
  /* ---- REAL COASTLINES: TR.coast = { land: [ [[x,y],...], ... ] } ----
     Polygons of the actual shore in FIELD units (tools/fetch-coast.mjs
     projects them from OpenStreetMap). A signed distance field — exact
     Euclidean distance transform over a grid covering field + margins —
     makes the waterline the polygon itself: smooth, sub-cell accurate
     under bilinear sampling, and identical for physics, painter and
     worker. Blobs still compose ON TOP for relief; noise fades out near
     the waterline so the authored shore stays the authored shore. */
  const COAST = TR.coast && TR.coast.land && TR.coast.land.length ? TR.coast : null;
  let CD = null, CGW = 0, CGH = 0;
  const CGS = 2, CMARG = (COAST && COAST.margin) || 480;
  if (COAST) {
    CGW = Math.ceil((FW + 2 * CMARG) / CGS) + 1;
    CGH = Math.ceil((FH + 2 * CMARG) / CGS) + 1;
    const N = CGW * CGH;
    const mask = new Uint8Array(N);
    for (let j = 0; j < CGH; j++) {
      const py = -CMARG + j * CGS;
      const xs = [];
      for (const poly of COAST.land) {
        for (let i = 0, n = poly.length; i < n; i++) {
          const a = poly[i], b = poly[(i + 1) % n];
          if ((a[1] <= py) !== (b[1] <= py)) {
            xs.push(a[0] + (py - a[1]) / (b[1] - a[1]) * (b[0] - a[0]));
          }
        }
      }
      xs.sort((q, w) => q - w);
      for (let k = 0; k + 1 < xs.length; k += 2) {
        const i0 = Math.max(0, Math.ceil((xs[k] + CMARG) / CGS));
        const i1 = Math.min(CGW - 1, Math.floor((xs[k + 1] + CMARG) / CGS));
        for (let i = i0; i <= i1; i++) mask[j * CGW + i] = 1;
      }
    }
    /* Felzenszwalb exact EDT, squared distances, rows then columns */
    const INF = 1e12;
    const edt = (seed) => {
      const g = new Float64Array(N);
      const fz = new Float64Array(Math.max(CGW, CGH));
      const v = new Int32Array(Math.max(CGW, CGH));
      const z = new Float64Array(Math.max(CGW, CGH) + 1);
      for (let i = 0; i < N; i++) g[i] = seed[i] ? 0 : INF;
      const pass = (len, stride, base) => {
        for (let i = 0; i < len; i++) fz[i] = g[base + i * stride];
        let k = 0; v[0] = 0; z[0] = -INF; z[1] = INF;
        for (let q = 1; q < len; q++) {
          let s = ((fz[q] + q * q) - (fz[v[k]] + v[k] * v[k])) / (2 * q - 2 * v[k]);
          while (s <= z[k]) {
            k--;
            s = ((fz[q] + q * q) - (fz[v[k]] + v[k] * v[k])) / (2 * q - 2 * v[k]);
          }
          k++; v[k] = q; z[k] = s; z[k + 1] = INF;
        }
        k = 0;
        for (let q = 0; q < len; q++) {
          while (z[k + 1] < q) k++;
          g[base + q * stride] = (q - v[k]) * (q - v[k]) + fz[v[k]];
        }
      };
      for (let j = 0; j < CGH; j++) pass(CGW, 1, j * CGW);
      for (let i = 0; i < CGW; i++) pass(CGH, CGW, i);
      return g;
    };
    const inv = new Uint8Array(N);
    for (let i = 0; i < N; i++) inv[i] = mask[i] ? 0 : 1;
    const dToLand = edt(mask), dToWater = edt(inv);
    CD = new Float32Array(N);
    for (let i = 0; i < N; i++) {
      CD[i] = (mask[i] ? Math.sqrt(dToWater[i]) : -Math.sqrt(dToLand[i])) * CGS;
    }
  }
  function coastSd(x, y) {
    const gx = clamp((x + CMARG) / CGS, 0, CGW - 2);
    const gy = clamp((y + CMARG) / CGS, 0, CGH - 2);
    const ix = gx | 0, iy = gy | 0, fx = gx - ix, fy = gy - iy;
    const o = iy * CGW + ix;
    const a = CD[o], b = CD[o + 1], c = CD[o + CGW], d = CD[o + CGW + 1];
    return a + (b - a) * fx + (c - a) * fy + (a - b - c + d) * fx * fy;
  }

  function elevLand(x, y) {
    let e, nf = 1;
    if (COAST) {
      /* the shore profile hangs off signed distance: a low dry step at
         the waterline, rising gently inland (blobs supply mountains),
         deepening seaward. Noise is silenced within ~10 units of the
         line so the real coast never wobbles. BEYOND the mapped grid the
         terrain blends back to the generic continued country — clamping
         the edge row extruded it into straight comb-teeth columns on
         viewports whose world margins outreach the cartography. */
      const sd = coastSd(x, y);
      nf = Math.min(1, Math.abs(sd) / 10);
      e = sd >= 0
        ? 0.012 + 0.05 * sstep(Math.min(sd / 16, 1))
        : -0.012 - 0.62 * sstep(Math.min(-sd / 26, 1));
      const dOut = Math.max(0, -CMARG - x, x - FW - CMARG, -CMARG - y, y - FH - CMARG);
      if (dOut > 0) {
        const m = sstep(Math.min(dOut / 80, 1));
        const yc2 = clamp(y, -80, FH + 80);
        e = e * (1 - m) + (TR.base + TR.rise * (1 - yc2 / FH)) * m;
        nf = Math.max(nf, m);
      }
    } else {
      // the north-south rise is held just past the field's edge, so the
      // continued world rolls out level instead of climbing without end
      const yc = clamp(y, -80, FH + 80);
      e = TR.base + TR.rise * (1 - yc / FH);
    }
    let sea = 0;
    for (const b of TR.blobs) {
      const dx = (x - b.x) / b.r, dy = (y - b.y) / b.r;
      const d2 = dx * dx + dy * dy;
      if (d2 >= 1) continue;
      if (b.flat) {
        // flat-topped blob: full height inside flat*r, quadratic skirt
        // outside — how shelves, plateaus and islands are built. A plain
        // blob is a cone and will always render as "a circle with rings".
        const u = Math.sqrt(d2);
        const t = u <= b.flat ? 1 : 1 - ((u - b.flat) / (1 - b.flat)) ** 2;
        if (b.h < 0) sea += b.h * t;   // deliberate water: applied below the floor
        else e += b.h * t;
      } else {
        const t = 1 - d2; e += b.h * t * t;
      }
    }
    e += ((vnoise(x * 0.004, y * 0.004) - 0.5) * TR.noise
       + (vnoise(x * 0.013 + 40, y * 0.013) - 0.5) * TR.noise * 0.4) * nf;
    if (!COAST && TR.floor != null) e = Math.max(e, TR.floor);
    return e + sea;
  }
  /* the river is carved ANALYTICALLY per sample, never baked into the
     grid — exact math has no resolution */
  function carve(e, x, y) {
    if (!riverY) return e;
    const t = Math.abs(y - riverY(x)) / TR.river.halfW;
    if (t < 1) return Math.min(e, -0.30 * (1 - t * t) - 0.02);
    if (t < 2) {
      // the bank blends C1 to the ambient ground instead of a ramp that
      // releases at a fixed height — the release printed a tonal cliff
      // and a planar shelf wherever the valley sat lower than the
      // country around it (Cannae's Aufidus, caught at iPad zoom). The
      // waterline itself (t=1) is untouched: physics and the validator
      // key off it.
      const s = t - 1, w = s * s * (3 - 2 * s);
      return Math.min(e, 0.06 * s * (1 - w) + e * w);
    }
    return e;
  }
  function elevAt(x, y) { return carve(elevLand(x, y), x, y); }

  /* precomputed LAND grid — a physics CACHE, not the world */
  const GS = 2;
  const gw = Math.floor(FW / GS) + 3, gh = Math.floor(FH / GS) + 3;
  const EG = new Float32Array(gw * gh);
  for (let j = 0; j < gh; j++)
    for (let i = 0; i < gw; i++) EG[j * gw + i] = elevLand(i * GS, j * GS);
  function egLand(x, y) {
    const gx = clamp(x / GS, 0, gw - 2), gy = clamp(y / GS, 0, gh - 2);
    const ix = gx | 0, iy = gy | 0, fx = gx - ix, fy = gy - iy;
    const a = EG[iy * gw + ix], b = EG[iy * gw + ix + 1];
    const c = EG[(iy + 1) * gw + ix], d = EG[(iy + 1) * gw + ix + 1];
    return a + (b - a) * fx + (c - a) * fy + (a - b - c + d) * fx * fy;
  }
  function egAt(x, y) { return carve(egLand(x, y), x, y); }

  /* the elevation GRADIENT at the same lattice: hillshade and contour
     width need slope, not truth — two lerps replace four full samples */
  const GX = new Float32Array(gw * gh), GY = new Float32Array(gw * gh);
  for (let j = 0; j < gh; j++) {
    for (let i = 0; i < gw; i++) {
      const o = j * gw + i;
      GX[o] = (EG[j * gw + Math.min(gw - 1, i + 1)] - EG[j * gw + Math.max(0, i - 1)]) / (2 * GS);
      GY[o] = (EG[Math.min(gh - 1, j + 1) * gw + i] - EG[Math.max(0, j - 1) * gw + i]) / (2 * GS);
    }
  }
  const G2 = [0, 0];
  function gridGrad(x, y) {
    const gx = clamp(x / GS, 0, gw - 2), gy = clamp(y / GS, 0, gh - 2);
    const ix = gx | 0, iy = gy | 0, fx = gx - ix, fy = gy - iy;
    const o = iy * gw + ix;
    const a = GX[o], b = GX[o + 1], c = GX[o + gw], d = GX[o + gw + 1];
    G2[0] = a + (b - a) * fx + (c - a) * fy + (a - b - c + d) * fx * fy;
    const a2 = GY[o], b2 = GY[o + 1], c2 = GY[o + gw], d2 = GY[o + gw + 1];
    G2[1] = a2 + (b2 - a2) * fx + (c2 - a2) * fy + (a2 - b2 - c2 + d2) * fx * fy;
    return G2;
  }
  function shadeGrad(x, y, e) {
    if (x < 0 || y < 0 || x > FW || y > FH) {   // margins: the analytic field
      G2[0] = (elevAt(x + 2, y) - elevAt(x - 2, y)) / 4;
      G2[1] = (elevAt(x, y + 2) - elevAt(x, y - 2)) / 4;
      return G2;
    }
    /* a pixel ON the carved bank shades from the carve profile near the
       water and hands off to the grid gradient exactly as the carve hands
       off to ambient ground — the SAME blend weight in both, so the light
       always agrees with the terrain it falls on. Beds sit below the
       shade band, so the bank (1 <= t < 2) is the only carved case. */
    if (riverY) {
      const dy = y - riverY(x), t = Math.abs(dy) / TR.river.halfW;
      if (t >= 1 && t < 2) {
        const s = t - 1, w = s * s * (3 - 2 * s);
        const cap = 0.06 * s * (1 - w) + egLand(x, y) * w;
        if (e <= cap + 1e-6) {
          const sgn = (dy > 0 ? 0.06 : -0.06) / TR.river.halfW;
          gridGrad(x, y);
          G2[0] = (-sgn * riverSlope(x)) * (1 - w) + G2[0] * w;
          G2[1] = sgn * (1 - w) + G2[1] * w;
          return G2;
        }
      }
    }
    return gridGrad(x, y);
  }

  function crom(a, b, c, d, t) {
    return b + 0.5 * t * (c - a + t * (2 * a - 5 * b + 4 * c - d + t * (3 * (b - c) + d - a)));
  }
  function egSmooth(x, y) {
    const gx = clamp(x / GS, 1, gw - 3), gy = clamp(y / GS, 1, gh - 3);
    const ix = gx | 0, iy = gy | 0, fx = gx - ix, fy = gy - iy;
    let o = (iy - 1) * gw + ix;
    const r0 = crom(EG[o - 1], EG[o], EG[o + 1], EG[o + 2], fx); o += gw;
    const r1 = crom(EG[o - 1], EG[o], EG[o + 1], EG[o + 2], fx); o += gw;
    const r2 = crom(EG[o - 1], EG[o], EG[o + 1], EG[o + 2], fx); o += gw;
    const r3 = crom(EG[o - 1], EG[o], EG[o + 1], EG[o + 2], fx);
    return carve(crom(r0, r1, r2, r3, fy), x, y);
  }

  /* painting never ends at the field's edge: outside the grid the
     samplers hand over to the analytic field, which is defined
     everywhere — why the table has no border */
  function worldAt(x, y) {
    return (x < 0 || y < 0 || x > FW || y > FH) ? elevAt(x, y) : egAt(x, y);
  }
  function worldSmooth(x, y) {
    return (x < 0 || y < 0 || x > FW || y > FH) ? elevAt(x, y) : egSmooth(x, y);
  }

  const FE = 0.012;   // shoreline feather half-width (elevation units)
  /* one row of one tile. `row` is the LOCAL buffer row; dither keys off
     the ABSOLUTE pixel row so a tile built in worker chunks is
     pixel-identical to one built in a single pass. useSmooth earns the
     C1 sampler only at magnification (creases live past ~4 px/unit). */
  function terrainRow(px, row, pw, x0, y0, sc, useSmooth) {
    const sample = useSmooth ? worldSmooth : worldAt;
    const fy = y0 + row / sc;
    const aj = (Math.round(y0 * sc) + row) | 0;
    for (let i = 0; i < pw; i++) {
      const fx = x0 + i / sc;
      let e = sample(fx, fy);
      // every shoreline is exact: near the waterline the grid hands over
      // to the analytic field, so no coast inherits the grid's resolution.
      // The handoff is BLENDED at its top — the two samplers carry noise
      // of slightly different character, and a hard switch drew a faint
      // texture seam along the e=0.04 contour of every quiet valley
      if (e > -0.05 && e < 0.04) {
        const ea = elevAt(fx, fy);
        e = e > 0.028 ? ea + (e - ea) * sstep((e - 0.028) / 0.012) : ea;
      }
      const dith = (hash2(i, aj) - 0.5) * 2.4;
      let r, gg, b;
      /* the waterline is a BLEND, never a branch */
      let wr = 0, wg = 0, wb = 0;
      if (e < FE) {
        const depth = clamp(-e / 0.35, 0, 1);
        wr = 15 - 8 * depth; wg = 30 - 15 * depth; wb = 44 - 21 * depth;
        const sw2 = (vnoise(fx * 0.02, fy * 0.035) + 0.6 * vnoise(fx * 0.055 + 7, fy * 0.07 + 3)) / 1.6;
        wr += (sw2 - 0.5) * 4; wg += (sw2 - 0.5) * 6; wb += (sw2 - 0.5) * 8;
        if (e > -0.045) {               // shallows lighten toward the shore
          const f = Math.min(1, 1 + e / 0.045);
          wr += f * 8; wg += f * 18; wb += f * 28;
          if (TR.tropic) { wr -= f * 2; wg += f * 7; wb += f * 3; }
        }
        if (e > -0.026 && e < -0.004) { // surf: broken foam at shoal and shore
          const sf = 1 - Math.abs((e + 0.015) / 0.011);
          if (sf > 0) {
            const brk = vnoise(fx * 0.14 + 11, fy * 0.14 + 4);
            const f = sf * sf * (brk > 0.56 ? 1 : 0.15) * (TR.tropic ? 1 : 0.5);
            wr += f * 22; wg += f * 26; wb += f * 26;
          }
        }
        if (e > -0.008) {               // the waterline itself catches light
          const f = Math.min(1, 1 + e / 0.008);
          wr += f * 18; wg += f * 30; wb += f * 40;
        }
        wr += dith * 0.5; wg += dith * 0.6; wb += dith * 0.7;
        r = wr; gg = wg; b = wb;
      }
      if (e > -FE) {
        const g2 = shadeGrad(fx, fy, e);
        const gx = g2[0], gy = g2[1];
        const shade = clamp((gx * -0.707 + gy * -0.707) * 260, -7, 7);
        let L = 13 + e * 34 + shade;
        // contour lines, width tied to slope so flats don't band
        const slope = Math.sqrt(gx * gx + gy * gy);
        const lv = e * 11, frac = lv - Math.floor(lv);
        const w = clamp(11 * slope * 0.65, 0.025, 0.4);
        // contours FADE IN above their low-ground gate — a hard gate drew
        // the gate itself as a line where the texture suddenly began
        if (frac < w && e > 0.015) L += 7 * (1 - frac / w) * Math.min(1, (e - 0.015) / 0.03);
        L += dith;
        r = L + 1.5; gg = L + 1; b = L - 2;
        // a dry sand tone above the bank — a falloff, never a stripe
        if (e < 0.032) { const sf2 = Math.min(1, (0.032 - e) / 0.024); r += sf2 * 3; gg += sf2 * 1.5; }
        if (TR.tropic) {
          if (e < 0.028) { const f = 1 - e / 0.028; r += f * 8; gg += f * 5 + (1 - f) * 2.5; }
          else gg += 2.5;
        }
        // woods: dark stippled canopy with a faint green cast
        if (TR.woods) {
          let wf = 0;
          for (const wd of TR.woods) {
            const dx = (fx - wd.x) / wd.r, dy = (fy - wd.y) / wd.r;
            const d2 = dx * dx + dy * dy;
            if (d2 < 1) { const t = 1 - d2; wf += t * t; }
          }
          if (wf > 0.03) {
            const k = Math.min(1, wf * 1.5) * 0.9;
            const st = vnoise(fx * 0.12, fy * 0.12) + 0.6 * vnoise(fx * 0.31 + 5, fy * 0.29);
            const canopy = 12 + (st > 1.05 ? 3.5 : 0) + dith * 0.7;
            r += (canopy - r) * k;
            gg += (canopy + 3 - gg) * k;
            b += (canopy - 2 - b) * k;
          }
        }
        if (e < FE) {             // inside the feather band: mix over the water
          const m = sstep((e + FE) / (2 * FE));
          r = wr + (r - wr) * m; gg = wg + (gg - wg) * m; b = wb + (b - wb) * m;
        }
      }
      const k2 = (row * pw + i) * 4;
      px[k2] = r; px[k2 + 1] = gg; px[k2 + 2] = b; px[k2 + 3] = 255;
    }
  }

  return { riverY, elevAt, egAt, egSmooth, worldAt, worldSmooth, terrainRow };
}

const TR = B.terrain;
const K = terrainKernel({ FW, FH, TR });
const { riverY, elevAt, egAt, egSmooth, worldAt, worldSmooth, terrainRow } = K;
const GS = 2;   // grid cell (mirrors the kernel's) — resize() aligns the world rect to it

/* ---------------- units & entities ----------------
   A chassis is a physics contract, not a sprite. Every kind declares how
   fast it runs (maxV), how hard it chases its slot (k), how much room it
   keeps (sep), how restless it is (wander), and — the law that stops a
   destroyer behaving like a Dauntless — how fast it may change heading
   (turn, radians/sec). minV is airspeed: only things that fly have it. */
const KINDS = {
  inf:  { maxV: 105, k: 3.2, sep: 7,  wander: 1,   turn: 7 },
  cav:  { maxV: 240, k: 5.2, sep: 7,  wander: 1,   turn: 4.5 },
  tank: { maxV: 85,  k: 3.0, sep: 9,  wander: 0.5, turn: 1.8 },
  ship: { maxV: 60,  k: 2.2, sep: 13, wander: 0.2, turn: 0.9, hGate: 4 },
  air:  { maxV: 210, k: 4.2, sep: 4,  wander: 0.8, turn: 3.0, minV: 0.35 },
  // strategic aircraft: slow, straight, unhurried — a bomber on a route
  // holds its line and releases on the run; it never orbits a target.
  // Author its keyframes as one CONTINUOUS track (station speed ≥ ~20 u/s,
  // no holds) or the minimum airspeed will make even this chassis circle.
  b2bomber: { maxV: 110, k: 3.2, sep: 10, wander: 0.12, turn: 0.7, minV: 0.18 },
};
/* the element a chassis moves through. Things in different elements do not
   see each other at all — no flocking, no jostling, no contact. Aircraft
   pass OVER a fleet; they touch it only through volleys. */
const DOMAIN = { inf: 'land', cav: 'land', tank: 'land', ship: 'sea', air: 'air', b2bomber: 'air' };

/* how a chassis is drawn, in field units. One ladder, one place to tune it;
   the validator reads the same numbers to prove glyphs cannot pack solid. */
const GLYPH = {
  inf:  { len: 4.2, w: 1.7 },
  cav:  { len: 4.2, w: 1.7 },
  tank: { len: 7,   w: 3.4 },
  ship: { len: 12,  w: 3.6 },
  air:  { len: 8,   w: 1.4 },
  b2bomber: { len: 9, w: 1.5 },
};
/* how each chassis is DRAWN and what it leaves behind — the fixed set of
   primitives every kind (built-in or declared) resolves to */
const SHAPE = { inf: 'streak', cav: 'streak', tank: 'block', ship: 'hull', air: 'dart', b2bomber: 'chevron' };
const TRAIL = { inf: 'foot', cav: 'foot', tank: 'treads', ship: 'wake', air: 'contrail', b2bomber: 'contrail' };
const TRAILA = { air: 0.07, b2bomber: 0.045 };   // contrail alpha per kind

/* ---- declared chassis: battles may mint NEW kinds as pure data ----
   B.chassis = { name: { maxV, k?, sep?, wander?, turn?, minV?, hGate?,
   domain: 'land'|'sea'|'air', shape: 'streak'|'dart'|'chevron'|'block'|'hull',
   trail?: 'contrail'|'treads'|'foot'|'wake'|'none', trailAlpha?,
   glyph: {len, w} } }
   The engine stays frozen: a declared chassis composes existing physics
   and draw primitives. A platform needing a NEW primitive is still an
   engine change — that door stays human-shaped. */
const SHAPE_TRAIL_DEFAULT = { dart: 'contrail', chevron: 'contrail', block: 'treads', hull: 'wake', streak: 'foot' };
for (const [name, c] of Object.entries(B.chassis || {})) {
  KINDS[name] = { maxV: c.maxV || 100, k: c.k ?? 3.2, sep: c.sep ?? 8,
                  wander: c.wander ?? 0.3, turn: c.turn ?? 1.5,
                  minV: c.minV, hGate: c.hGate };
  DOMAIN[name] = c.domain || 'land';
  SHAPE[name] = c.shape || 'streak';
  TRAIL[name] = c.trail || SHAPE_TRAIL_DEFAULT[SHAPE[name]];
  GLYPH[name] = c.glyph || { len: 6, w: 1.5 };
  if (c.trailAlpha) TRAILA[name] = c.trailAlpha;
}

function unitState(u, t) {
  const kf = u.kf;
  if (t <= kf[0][0]) return kfObj(kf[0]);
  const last = kf[kf.length - 1];
  if (t >= last[0]) return kfObj(last);
  let i = 0;
  while (kf[i + 1][0] < t) i++;
  const a = kf[i], b = kf[i + 1];
  const f = smooth((t - a[0]) / (b[0] - a[0]));
  let da = (b[3] - a[3]) % 360;
  if (da > 180) da -= 360; if (da < -180) da += 360;
  return {
    cx: a[1] + (b[1] - a[1]) * f, cy: a[2] + (b[2] - a[2]) * f,
    ang: (a[3] + da * f) * D2R,
    w: a[4] + (b[4] - a[4]) * f, d: a[5] + (b[5] - a[5]) * f,
    bow: a[6] + (b[6] - a[6]) * f, scatter: a[7] + (b[7] - a[7]) * f,
  };
}
const kfObj = (k) => ({ cx: k[1], cy: k[2], ang: k[3] * D2R, w: k[4], d: k[5], bow: k[6], scatter: k[7] });

function sched(k, t) {
  if (!k || t <= k[0][0]) return 0;
  const last = k[k.length - 1];
  if (t >= last[0]) return last[1];
  let i = 0;
  while (k[i + 1][0] < t) i++;
  const a = k[i], b = k[i + 1];
  return a[1] + (b[1] - a[1]) * ((t - a[0]) / (b[0] - a[0]));
}
/* ships die by striking their colours (u.struck); men by u.kill */
const lossFrac = (u, t) => u.kind === 'ship' ? sched(u.struck, t) : sched(u.kill, t);

function meleeAmp(u, t) {
  let amp = 0;
  for (const [t0, t1, a] of u.melee || []) {
    if (t >= t0 && t <= t1) {
      const edge = Math.min(1, (t - t0) / 2, (t1 - t) / 2);
      amp = Math.max(amp, a * 0.75 * Math.max(0, edge));
    }
  }
  return amp;
}

/* ---- frame-flip normalization ---------------------------------------
   A formation's rect is 180°-symmetric: (ang+180, −bow) draws the SAME
   shape (w is the frontage axis; the bulge still bulges the same way —
   only the anonymous grain labels move). So an authored about-face
   (0 → 180) buys no geometry, but it used to make the whole frame PIVOT:
   every slot swept a half-circle arc and the unit spun like a propeller
   (Cannae's retreating velites, measured at 0.8 full circles per mote).
   Normalize ONCE at boot: walk each unit's keyframes and whenever a step
   would rotate the frame more than 90°, flip that row's representation
   (ang∓180, bow negated). The stored chain then never turns more than
   90° per step, and a reversal reads from VELOCITY — the men turn
   around; the line stays a line. */
for (const u of B.units) {
  if (u.deathOrder) continue;   // front/rear semantics forbid flips — the validator bars >90° steps instead
  for (let i = 1; i < u.kf.length; i++) {
    let da = (u.kf[i][3] - u.kf[i - 1][3]) % 360;
    if (da > 180) da -= 360; if (da < -180) da += 360;
    if (Math.abs(da) > 90) {
      u.kf[i][3] += da > 0 ? -180 : 180;
      u.kf[i][6] = -u.kf[i][6];
    }
  }
}
/* a MARGIN RESIDENT is a unit whose whole choreography lives beyond the
   field — Midnight Hammer's submarine, stationed in the Gulf of Oman.
   The edge dim-out exists so EXITS dissolve; it must not erase a unit
   that never was on the table, or its label floats over empty water. */
for (const u of B.units) {
  u.offField = u.kf.every((k2) => k2[1] < -40 || k2[1] > FW + 40 || k2[2] < -40 || k2[2] > FH + 40);
}

const ents = [];
for (const u of B.units) {
  const arr = [];
  const pal = B.sides[u.side].pal;
  const ang0 = u.kf[0][3] * D2R;
  for (let i = 0; i < u.n; i++) {
    const roll = Math.random();
    // mostly mid-tones, rare glint; cavalry rides a shade brighter
    const ci = roll < 0.9
      ? [0, 1, 2, 3][Math.floor(roll / 0.9 * (u.kind === 'cav' ? 3 : 4)) + (u.kind === 'cav' ? 1 : 0)]
      : 4;
    // one entity = one ship, in single file down the column; hull tones steady
    const isShip = u.kind === 'ship';
    arr.push({
      unit: u,
      u: isShip ? 0 : Math.random() - 0.5,
      v: isShip ? (i + 0.5) / u.n - 0.5 : Math.random() - 0.5,
      x: 0, y: 0, vx: 0, vy: 0, n: 0,
      hx: Math.cos(ang0), hy: Math.sin(ang0),
      n1: Math.random() * 2 - 1, n2: Math.random() * 2 - 1,
      ph: Math.random() * 6.2832, sp: 0.6 + Math.random() * 0.8,
      trav: 0, foot: i % 2 ? 1 : -1,
      c: hexToRgb(pal[isShip ? 1 + (i % 3) : Math.min(ci, 4)]),
      cid: (u.side === 'a' ? 0 : 5) + (isShip ? 1 + (i % 3) : Math.min(ci, 4)),
      alive: true, thr: 0,
    });
  }
  // loss order: outer ranks first (Polybius on Cannae), or from the head /
  // tail of a column — Trafalgar's lines were eaten from where they were cut
  const orderKey = u.deathOrder === 'front' ? (e) => e.v
    : u.deathOrder === 'rear' ? (e) => -e.v
    : (e) => Math.max(Math.abs(e.u), Math.abs(e.v));
  arr.slice().sort((a, b) => orderKey(b) - orderKey(a))
     .forEach((e, rank) => { e.thr = (rank + 0.5) / u.n; });
  u.ents = arr;
  ents.push(...arr);
}

/* palette strings for the colour cache: 5 tones per side, both sides */
for (const [si, sd] of [['a', 0], ['b', 5]]) {
  B.sides[si].pal.forEach((hx, i) => { const c = hexToRgb(hx); PALSTR[sd + i] = `${c[0]},${c[1]},${c[2]}`; });
}

function slotPos(e, st, t) {
  const fx = Math.cos(st.ang), fy = Math.sin(st.ang);
  const pxv = -fy, pyv = fx;
  const bowOff = st.bow * (1 - 4 * e.u * e.u);
  let x = st.cx + pxv * e.u * st.w + fx * (e.v * st.d + bowOff);
  let y = st.cy + pyv * e.u * st.w + fy * (e.v * st.d + bowOff);
  x += e.n1 * st.scatter; y += e.n2 * st.scatter;
  const m = meleeAmp(e.unit, t);
  if (m > 0) {
    x += Math.sin(t * 1.15 * e.sp + e.ph) * m;
    y += Math.cos(t * 0.95 * e.sp + e.ph * 1.3) * m;
  }
  return [x, y];
}

/* ---------------- canvas, layers, view ---------------- */
const cv = document.getElementById('field');
const cx2d = cv.getContext('2d');
let SW = 0, SH = 0, DPR = 1, S = 1, OX = 0, OY = 0;
/* the table opens slightly OVERSCANNED: 5% of the map hangs off-screen,
   so there is always a little room to pan before zooming — a sand table
   you cannot nudge feels bolted down. Zooming out to exactly 1 is still
   allowed; double-click returns here. */
const Z0 = 1.05;
let Z = Z0, VX = 0, VY = 0;         // user view: zoom + pan (screen px)
/* the zoom floor is wherever the WHOLE table fits the screen — not a
   fixed 1. On a landscape desktop that is 1 (Z=1 already fits). On a
   portrait phone, where the base scale covers the height, it is far
   below 1, and it is the only way to see the whole battle at once. */
let ZMIN = 1;
let detail = null, build = null, viewMoved = 0;   // re-rastered terrain tile
/* the WORLD rect: the field plus however much margin the most zoomed-out
   view can expose. resize() grows it; the world tile paints all of it. */
let WX0 = 0, WY0 = 0, WW = FW, WH = FH;
let WK = null;   // the raster Worker (constructed below; null = banded fallback)
let GLR = null;  // the WebGL renderer (?gl=1 opt-in; null = the canvas path)

function mkFieldLayer(sc) {
  const c = document.createElement('canvas');
  c.width = FW * sc; c.height = FH * sc;
  const ctx = c.getContext('2d');
  ctx.setTransform(sc, 0, 0, sc, 0, 0);
  return { cv: c, ctx };
}
const trail = mkFieldLayer(FS), tctx = trail.ctx;
const fallen = mkFieldLayer(FS), fctx = fallen.ctx;

const vx = (x) => VX + x * S * Z, vy = (y) => VY + y * S * Z;

/* the GROUND (terrain + the fallen) is its own canvas element behind the
   sim: it re-rasters only when the view moves, a tile completes, or
   someone dies — not sixty times a second. The sim canvas above it keeps
   only what genuinely changes per frame: trails and living bodies. */
const groundCv = document.createElement('canvas');
groundCv.style.cssText = 'position:fixed;inset:0;display:block;';
cv.parentNode.insertBefore(groundCv, cv);
const gctx = groundCv.getContext('2d');
let groundDirty = true;

/* Beyond the table's edge the world does not stop — the ground tile
   carries real terrain out to the world rect, so no zoom level can find
   a border. Beneath everything sits MEANC, the terrain's own average
   colour: if a resize outruns the tile for a moment, the gap is the
   colour of the country, never black. */
function drawGround() {
  groundDirty = false;
  gctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  gctx.fillStyle = MEANC;
  gctx.fillRect(0, 0, SW, SH);
  gctx.imageSmoothingEnabled = true;
  const u = S * Z;
  if (ground) {
    gctx.drawImage(ground.cv, VX + ground.x0 * u, VY + ground.y0 * u,
                   ground.w * u, ground.h * u);
  }
  // a world tile mid-build draws WHAT IT HAS — the country sweeps in row
  // by row instead of appearing all at once at the end
  if (wbuild && wbuild.wkLive) {
    gctx.drawImage(wbuild.cv, VX + wbuild.x0 * u, VY + wbuild.y0 * u,
                   wbuild.w * u, wbuild.h * u);
  }
  // the detail tile draws at ANY zoom — its rect is field-space, so a
  // stale tile rescales correctly and still beats every coarser layer.
  // Skip it only when the ground beneath is genuinely denser.
  if (detail && (!ground || detail.sc >= ground.ws * 0.9)) {
    gctx.drawImage(detail.cv, VX + detail.x0 * u, VY + detail.y0 * u,
                   detail.w * u, detail.h * u);
  }
  if (build && build.wkLive) {   // sharpness arrives as a visible sweep too
    gctx.drawImage(build.cv, VX + build.x0 * u, VY + build.y0 * u,
                   build.w * u, build.h * u);
  }
  gctx.drawImage(fallen.cv, VX, VY, FW * u, FH * u);
  /* names, marks and the title are drawn LIVE above the tiles at screen
     resolution — never baked into tile pixels. Baked lettering blinked:
     a mid-build sweep has no text until it publishes, so every rebuild
     made the map's names flicker out and back. Live overlay cannot. */
  paintOverlay(gctx, -VX / u, -VY / u, u);
}

/* pan is bounded by the WORLD rect — the country continues, so zoomed
   out you may still look around — while the FIELD must always keep at
   least a corner on screen so the battle can never be lost. The old
   rule centre-locked the view whenever the field fit the screen, which
   made every zoomed-out table immovable. */
function clampBounds() {
  const u = S * Z;
  const w = FW * u, h = FH * u;
  const KX = Math.min(220, SW * 0.25), KY = Math.min(220, SH * 0.25);
  const loX = Math.max(SW - (WX0 + WW) * u, KX - w);
  const hiX = Math.min(-WX0 * u, SW - KX);
  VX = loX > hiX ? (SW - w) / 2 : clamp(VX, loX, hiX);
  const loY = Math.max(SH - (WY0 + WH) * u, KY - h);
  const hiY = Math.min(-WY0 * u, SH - KY);
  VY = loY > hiY ? (SH - h) / 2 : clamp(VY, loY, hiY);
}
function clampView() { clampBounds(); viewChanged(); }

function kmbar() {
  const el2 = document.getElementById('kmbar');
  if (!el2) return;
  const perM = B.field.kmUnits / 1000 * S * Z;
  const cap = Math.min(300, SW * 0.28);   // a narrow screen gets a short bar
  let m = 100;
  for (const c of [200000, 100000, 50000, 20000, 10000, 5000, 2000, 1000, 500, 250, 100]) {
    if (c * perM <= cap) { m = c; break; }
  }
  el2.style.width = (m * perM) + 'px';
  el2.textContent = m >= 1000 ? (m / 1000) + ' km' : m + ' m';
}

function resize() {
  DPR = Math.min(2, window.devicePixelRatio || 1);
  SW = window.innerWidth; SH = window.innerHeight;
  cv.width = SW * DPR; cv.height = SH * DPR;
  cv.style.width = SW + 'px'; cv.style.height = SH + 'px';
  groundCv.width = SW * DPR; groundCv.height = SH * DPR;
  groundCv.style.width = SW + 'px'; groundCv.style.height = SH + 'px';
  if (GLR) GLR.resize();
  groundDirty = true;
  cx2d.setTransform(DPR, 0, 0, DPR, 0, 0);
  // portrait screens fit the table's HEIGHT and pan across it like a
  // scroll painting — letterboxing 16:9 into a phone leaves a 220px strip
  S = SH > SW ? SH / FH : Math.min(SW / FW, SH / FH);
  OX = (SW - FW * S) / 2; OY = (SH - FH * S) / 2;
  // zoom-out floor: well PAST the scale at which the whole map fits, so
  // every screen can pull back and see the table small on its continued
  // country — real terrain out there, so the pull-back is worth having
  ZMIN = Math.min(1, Math.min(SW / FW, SH / FH) / S) * 0.62;
  if (Z < ZMIN) Z = ZMIN;           // a rotate must not strand the view
  // how much world can the most zoomed-out view expose? Grow the world
  // rect to cover it (grid-aligned, grow-only) and re-lay the ground tile
  // cover what the most zoomed-out view exposes PLUS roam room — pan is
  // world-bounded, so without spare world the zoom floor cannot move
  const vw = SW / (S * ZMIN), vh = SH / (S * ZMIN);
  const mx = Math.ceil((Math.max(24, (vw - FW) / 2 + 8) + Math.min(0.15 * vw, 400)) / GS) * GS;
  const my = Math.ceil((Math.max(24, (vh - FH) / 2 + 8) + Math.min(0.15 * vh, 400)) / GS) * GS;
  if (-mx < WX0 || -my < WY0) {
    WX0 = Math.min(WX0, -mx); WY0 = Math.min(WY0, -my);
    WW = FW - 2 * WX0; WH = FH - 2 * WY0;
    worldStale = true;
    if (WK && wbuild) wkCancel(wbuild);
    wbuild = null;
  }
  if (Z === Z0) { VX = (SW - FW * S * Z) / 2; VY = (SH - FH * S * Z) / 2; }
  clampView(); kmbar();
}

/* ---------------- terrain rendering (once, field-space) --------------
   Hypsometric tint + hillshade + slope-weighted contour lines on land;
   depth-shaded water with swell texture and a lit shoreline. Dithered
   against banding. Built from the elevation grid, so it is smooth. */

/* Catmull-Rom in both axes over the elevation grid. Bilinear egAt is fine
   for physics, but its cell creases turn thresholded colour bands (the
   waterline above all) into stair-steps once the detail tile magnifies
   them — a 2-unit cell is ~55 device px at full zoom. C1 continuity is
   what makes a river bank read as a bank. */
/* place names, marks and the battle's own name — vector, so they resolve
   at whatever scale the tile is painted at */
function paintOverlay(g, x0, y0, sc) {
  const X = (x) => (x - x0) * sc, Y = (y) => (y - y0) * sc;
  g.font = `${9 * sc}px ui-monospace, Menlo, monospace`;
  for (const nm of TR.names || []) {
    g.fillStyle = nm.c || 'rgba(216,211,200,0.30)';
    g.textAlign = nm.align || 'center';
    g.fillText(nm.t, X(nm.x), Y(nm.y));
  }
  for (const mk of TR.marks || []) {
    // soft round marks — nothing hand-drawn on a map has square corners.
    // Size growth is capped so a dotted line stays a dotted line at 8×.
    const mx = X(mk.x) + 2 * sc, my = Y(mk.y) + 2 * sc;
    const ms = Math.min(sc, 4.5);
    g.fillStyle = 'rgba(216,211,200,0.12)';
    g.beginPath(); g.arc(mx, my, 3.1 * ms, 0, 6.2832); g.fill();
    g.fillStyle = 'rgba(216,211,200,0.38)';
    g.beginPath(); g.arc(mx, my, 1.7 * ms, 0, 6.2832); g.fill();
  }
  // the battle's name lives on the map, cartographer-style, in a zone
  // the validator proves no unit ever crosses. MAPTITLE lets the film
  // recorder (bench hook only) switch the inscription off — its camera
  // re-aims per phase and cannot pan back to read half a name.
  if (TR.title && MAPTITLE) {
    const ti = TR.title;
    g.textAlign = 'center';
    g.letterSpacing = `${5 * sc}px`;
    g.font = `${30 * sc}px 'Iowan Old Style', 'Palatino Linotype', Palatino, Georgia, serif`;
    g.fillStyle = 'rgba(216,211,200,0.5)';
    g.fillText(ti.name.toUpperCase(), X(ti.x), Y(ti.y));
    if (ti.sub) {
      g.letterSpacing = `${3 * sc}px`;
      g.font = `${10 * sc}px ui-monospace, Menlo, monospace`;
      g.fillStyle = 'rgba(143,138,128,0.6)';
      g.fillText(ti.sub.toUpperCase(), X(ti.x), Y(ti.y + 24));
    }
    g.letterSpacing = '0px';
  }
}

/* ---- the ground: rough pass now, the whole world in bands ------------
   Boot paints the field synchronously at half resolution (~20 ms with the
   integer hash) so the first frame is never empty; the detail tile then
   sharpens the visible screen within a few frames. Behind both, the WORLD
   tile rasters the full world rect — field plus margins — and swaps in as
   the pan/zoom fallback. Terrain past the field edge is sampled from the
   analytic field: the same country, genuinely continued. */
const TS = LITE ? 1 : 2;            // world tile ceiling: buffer px per field unit
function buildTerrainTile(x0, y0, w, h, sc) {
  const c = document.createElement('canvas');
  c.width = Math.ceil(w * sc); c.height = Math.ceil(h * sc);
  const g = c.getContext('2d');
  const img = g.createImageData(c.width, c.height);
  for (let j = 0; j < c.height; j++) terrainRow(img.data, j, c.width, x0, y0, sc);
  g.putImageData(img, 0, 0);
  return { cv: c, x0, y0, w, h, ws: sc };
}
/* built at boot, AFTER the view is known: the rough pass covers whatever
   the first frame will actually show — margins included, so a wide or
   tall screen never opens on a bare edge */
let ground = null;
let MEANC = '#10141a';   // terrain's mean colour: the backdrop beneath every draw
function bootGround() {
  const [x0, y0, x1, y1] = visRect();
  const px0 = Math.max(WX0, x0 - 12), py0 = Math.max(WY0, y0 - 12);
  const px1 = Math.min(WX0 + WW, x1 + 12), py1 = Math.min(WY0 + WH, y1 + 12);
  ground = buildTerrainTile(px0, py0, px1 - px0, py1 - py0, 0.5);
  const m = document.createElement('canvas');
  m.width = 1; m.height = 1;
  const mg = m.getContext('2d', { willReadFrequently: true });
  mg.imageSmoothingEnabled = true;
  mg.drawImage(ground.cv, 0, 0, 1, 1);
  const p = mg.getImageData(0, 0, 1, 1).data;
  MEANC = `rgb(${p[0]},${p[1]},${p[2]})`;
}
let wbuild = null, worldStale = true;
function startWorld() {
  worldStale = false;
  // spend a fixed pixel budget on however much world there is: a phone's
  // tall margins get a lighter weave, a desktop's get a denser one
  const ws = clamp(Math.sqrt((LITE ? 1.8e6 : 6e6) / (WW * WH)), 0.4, TS);
  const pw = Math.ceil(WW * ws), ph = Math.ceil(WH * ws);
  const c = document.createElement('canvas');
  c.width = pw; c.height = ph;
  const g = c.getContext('2d');
  wbuild = { cv: c, g, img: WK ? null : g.createImageData(pw, ph), row: 0, pw, ph, ws,
             x0: WX0, y0: WY0, w: WW, h: WH };
}
function publishWorld(o) {
  ground = o;
  if (wbuild === o) wbuild = null;
  groundDirty = true;
}
function stepWorld() {
  if (!wbuild) { if (worldStale) startWorld(); return; }
  if (!wbuild.img) wbuild.img = wbuild.g.createImageData(wbuild.pw, wbuild.ph);
  const t0 = performance.now();
  // wide open behind the loader plate; pushy while a live screen shows a
  // naked margin; polite once everything visible is covered
  const budget = loaderUp ? 26 : groundCovers() ? 6 : 14;
  while (wbuild.row < wbuild.ph) {
    terrainRow(wbuild.img.data, wbuild.row, wbuild.pw, wbuild.x0, wbuild.y0, wbuild.ws);
    wbuild.row++;
    if (performance.now() - t0 > budget) return;
  }
  wbuild.g.putImageData(wbuild.img, 0, 0);
  wbuild.img = null;
  publishWorld(wbuild);
}

/* ---- the loader: a table is set before it is shown --------------------
   The first instants of a boot are honest but ugly — a soft rough tile,
   map lettering not yet at device resolution. Rather than serve the table
   mid-lay, a brief Thrain plate (the segmented block T, the battle's
   name, a true progress line) holds the screen until the first device-
   resolution pass lands, then fades. Engine-provided: authors and the
   overnight agent do nothing to get it. */
let detailDone = false;
const LOADER = document.createElement('div');
LOADER.id = 'stloader';
LOADER.innerHTML = `
  <style>
    #stloader{position:fixed;inset:0;z-index:80;background:#0d0d0d;display:flex;
      flex-direction:column;align-items:center;justify-content:center;
      transition:opacity .3s ease;font-family:ui-monospace,Menlo,monospace;}
    #stloader.gone{opacity:0;pointer-events:none;}
    #stloader svg{width:60px;height:60px;}
    #stloader .seg{animation:stpulse 1.15s ease-in-out infinite;}
    #stloader .seg2{animation-delay:.15s;}
    #stloader .seg3{animation-delay:.3s;}
    @keyframes stpulse{0%,100%{opacity:.4}50%{opacity:1}}
    #stloader .bn{margin-top:28px;font-family:'Iowan Old Style','Palatino Linotype',Palatino,Georgia,serif;
      font-size:21px;letter-spacing:.4em;text-indent:.4em;color:rgba(216,211,200,.85);text-align:center;padding:0 20px;}
    #stloader .bs{margin-top:11px;font-size:9px;letter-spacing:.36em;text-indent:.36em;color:#8f8a80;}
    #stloader .bb{margin-top:24px;width:150px;height:2px;background:rgba(216,211,200,.12);}
    #stloader .bb i{display:block;height:100%;width:0%;background:#C14E24;}
    @media (prefers-reduced-motion:reduce){#stloader .seg{animation:none}}
  </style>
  <svg viewBox="0 0 100 100" aria-hidden="true">
    <rect class="seg seg1" x="14" y="18" width="72" height="18" rx="5" fill="#f4f4f5"/>
    <rect class="seg seg2" x="41" y="43" width="18" height="18" rx="5" fill="#f4f4f5"/>
    <rect class="seg seg3" x="41" y="68" width="18" height="18" rx="5" fill="#C14E24"/>
  </svg>
  <div class="bn"></div>
  <div class="bs">A THRAIN SAND TABLE</div>
  <div class="bb"><i></i></div>`;
LOADER.querySelector('.bn').textContent =
  ((TR.title && TR.title.name) || document.title || '').toUpperCase();
document.body.appendChild(LOADER);
let loaderUp = LOADER, loaderT0 = performance.now();
const loaderBar = LOADER.querySelector('.bb i');
function tendLoader() {
  if (!loaderUp) return;
  // readiness is COMPOSITE — the plate tracks everything the first view
  // needs: rough coverage laid, margins covered, and the first readable
  // detail sweep landed. It is not allowed to leave before the screen is
  // presentable, and its bar is the true sum of that work.
  const cov = groundCovers();
  const wprog = cov ? 1 : wbuild ? wbuild.row / wbuild.ph : 0;
  const dprog = detailDone ? 1 : build ? build.row / build.ph : 0;
  const prog = 0.15 + 0.35 * wprog + 0.5 * dprog;
  loaderBar.style.width = (prog * 100).toFixed(1) + '%';
  const t = performance.now() - loaderT0;
  // held a beat so a fast desktop gets a plate, not a flash; the failsafe
  // yields on machines where even the readable sweep is slow — a soft
  // table that responds beats a plate that lingers
  if ((cov && detailDone && t > 500) || t > 4000) {
    const n = loaderUp; loaderUp = null;
    n.classList.add('gone');
    setTimeout(() => n.remove(), 400);
  }
}

/* ---- detail tile: the visible screen at true device resolution ---------
   At EVERY zoom, once the view settles, the visible rectangle is repainted
   at device resolution in bands — this is what makes the table crisp at
   rest, from full zoom-out to 8×. Bounded by the screen, so the memory
   cost is one screenful no matter where the user goes; a monitor denser
   than the pixel cap gets the densest tile that fits instead of nothing. */

/* the slice of world currently on screen, clamped to the world rect */
function visRect() {
  return [
    clamp(-VX / (S * Z), WX0, WX0 + WW), clamp(-VY / (S * Z), WY0, WY0 + WH),
    clamp((SW - VX) / (S * Z), WX0, WX0 + WW), clamp((SH - VY) / (S * Z), WY0, WY0 + WH),
  ];
}

/* does the ground tile cover everything the screen can currently see?
   While it doesn't — a zoom-out has outrun it — filling the naked margin
   outranks sharpening the middle, and the scheduler flips priorities. */
function groundCovers() {
  if (!ground) return false;
  const [x0, y0, x1, y1] = visRect();
  return ground.x0 <= x0 + 0.5 && ground.y0 <= y0 + 0.5
      && ground.x0 + ground.w >= x1 - 0.5 && ground.y0 + ground.h >= y1 - 0.5;
}

function mkDetailBuild(x0, y0, w, h, sc, fullSc) {
  const pw = Math.round(w * sc), ph = Math.round(h * sc);
  if (pw < 8 || ph < 8) return;
  const c = document.createElement('canvas');
  c.width = pw; c.height = ph;
  const g = c.getContext('2d');
  build = { cv: c, g, img: WK ? null : g.createImageData(pw, ph), x0, y0, w, h, sc, fullSc,
            z: Z, pw, ph, row: 0 };
}
/* is the published tile still the right tile for this view? */
function detailFresh() {
  if (!detail || detail.z !== Z) return false;
  const [x0, y0, x1, y1] = visRect();
  return detail.x0 <= x0 + 0.5 && detail.y0 <= y0 + 0.5
      && detail.x0 + detail.w >= x1 - 0.5 && detail.y0 + detail.h >= y1 - 0.5;
}

/* the device-resolution scale a detail pass aims at for this view —
   shared by the scheduler and by viewSettled so they can never disagree */
function detailTarget() {
  let sc = S * Z * DPR;
  const [x0, y0, x1, y1] = visRect();
  const cap = LITE ? 6e6 : 14e6;
  if ((x1 - x0) * (y1 - y0) * sc * sc > cap) sc = Math.sqrt(cap / ((x1 - x0) * (y1 - y0)));
  return sc;
}
/* is the screen as sharp as this device can make it, right now? The film
   exporter holds frames on this after a camera move: motion hides a coarse
   tile, but the moment the camera stops the audience would see terrain pop
   into focus unless the cut waits for the detail pass to land. */
function viewSettled() {
  if (build || performance.now() - viewMoved < 200) return false;
  const sc = detailTarget();
  if (ground && sc <= ground.ws && ground.w >= WW) return true;
  return detailFresh() && detail.sc >= sc - 1e-9;
}

function startDetail() {
  let sc = detailTarget();
  const [x0, y0, x1, y1] = visRect();
  const w = x1 - x0, h = y1 - y0;
  // zoomed far out the world tile may already be the denser raster —
  // a detail pass would add blur, not sharpness
  if (ground && sc <= ground.ws && ground.w >= WW) { detailDone = true; return; }
  if (detailFresh() && detail.sc >= sc - 1e-9) return;   // already there
  // a big tile lands in TWO passes: a readable half-resolution sweep in a
  // quarter of the time, then true device resolution built silently
  // behind it. One monolithic pass made a 4K screen wait ten seconds
  // sharp-less; nobody notices the half-step, everybody notices the wait.
  let st = sc;
  if (w * h * sc * sc > 2.2e6) st = Math.max(sc * 0.5, 1.1);
  if (st >= sc * 0.85) st = sc;
  // when a readable sweep for this view already hangs on the wall, skip
  // straight to the full-resolution pass — that IS the upgrade path
  if (detailFresh() && detail.sc >= st - 1e-9) st = sc;
  mkDetailBuild(x0, y0, w, h, st, sc);
}

function publishDetail(o) {
  detail = o;
  if (build === o) build = null;
  detailDone = true;
  groundDirty = true;
}
function stepDetail() {
  if (!build) return;
  if (!build.img) build.img = build.g.createImageData(build.pw, build.ph);
  const t0 = performance.now();
  // while the loader plate covers the screen nothing animates for the
  // user, so the band budget runs wide open; once live, hand frames back
  const budget = loaderUp ? 26 : 7;
  while (build.row < build.ph) {
    terrainRow(build.img.data, build.row, build.pw, build.x0, build.y0, build.sc, build.sc > 4);
    build.row++;
    if (performance.now() - t0 > budget) return;
  }
  build.g.putImageData(build.img, 0, 0);
  build.img = null;
  publishDetail(build);
  // if this was the readable sweep, the scheduler sends the full-
  // resolution upgrade back through startDetail in its turn
}

/* any change of view invalidates the build and restarts the settle clock.
   The COMPLETED tile is kept and drawn rescaled — a zoom must degrade to
   yesterday's sharp raster, never to the rough pass — until its
   replacement lands. */
function viewChanged() {
  if (WK && build) wkCancel(build);
  build = null;
  viewMoved = performance.now();
  groundDirty = true;
}
function tendDetail() {
  if (build) { if (!WK) stepDetail(); return; }
  if (performance.now() - viewMoved < 200) return;
  startDetail();   // no-ops when the published tile already serves this view
}

/* ---- the raster Worker: terrain built OFF this thread ----------------
   The same terrainKernel source string runs in a Worker; tiles come back
   as transferable row-band chunks flushed straight into the tile canvas.
   The map fills progressively at full CPU speed and this thread never
   spends a frame on terrain. Banded stepping above survives as the
   no-Worker fallback (?wk=0 forces it, for QA). */
let wkSeq = 0, wkRun = null;
try {
  if (new URLSearchParams(location.search).get('wk') !== '0' && typeof Worker !== 'undefined') {
    const src = `'use strict';
const KF = ${terrainKernel.toString()};
let K = null;
const CANCEL = new Set();
onmessage = async (e) => {
  const m = e.data;
  if (m.t === 'init') { K = KF(m.P); return; }
  if (m.t === 'cancel') { CANCEL.add(m.id); return; }
  const { id, x0, y0, sc, sm, pw, ph } = m;
  const CH = Math.max(24, Math.round(6e5 / pw));
  for (let r = 0; r < ph; ) {
    if (CANCEL.has(id)) { CANCEL.delete(id); postMessage({ t: 'dead', id }); return; }
    const rows = Math.min(CH, ph - r);
    const px = new Uint8ClampedArray(pw * rows * 4);
    for (let j = 0; j < rows; j++) K.terrainRow(px, j, pw, x0, y0 + r / sc, sc, sm);
    postMessage({ t: 'chunk', id, r, rows, buf: px.buffer }, [px.buffer]);
    r += rows;
    await new Promise((res) => setTimeout(res, 0));
  }
  CANCEL.delete(id);
  postMessage({ t: 'done', id });
};`;
    WK = new Worker(URL.createObjectURL(new Blob([src], { type: 'text/javascript' })));
    WK.postMessage({ t: 'init', P: { FW, FH, TR } });
    WK.onmessage = (e) => {
      const m = e.data;
      const o = wkRun && wkRun.wkId === m.id ? wkRun : null;
      if (m.t === 'chunk') {
        if (!o) return;                       // superseded tile: drop quietly
        o.g.putImageData(new ImageData(new Uint8ClampedArray(m.buf), o.pw, m.rows), 0, m.r);
        o.row = m.r + m.rows;
        o.wkLive = true;
        groundDirty = true;
      } else if (m.t === 'done') {
        wkRun = null;
        if (o) {
          if (o.kind === 'world') { if (wbuild === o) publishWorld(o); }
          else if (build === o) publishDetail(o);
        }
        pumpWorker();
      } else if (m.t === 'dead') {
        wkRun = null;
        if (o) {
          if (o.kind === 'detail' && build === o) build = null;
          if (o.kind === 'world' && wbuild === o) { wbuild = null; worldStale = true; }
        }
        pumpWorker();
      }
    };
    WK.onerror = () => { WK = null; };        // banded fallback takes over
  }
} catch { WK = null; }

function wkCancel(o) {
  if (WK && wkRun === o) WK.postMessage({ t: 'cancel', id: o.wkId });
}
function wkSend(o, kind) {
  o.wkId = ++wkSeq; o.kind = kind;
  wkRun = o;
  WK.postMessage({ t: 'tile', id: o.wkId, x0: o.x0, y0: o.y0,
                   sc: kind === 'world' ? o.ws : o.sc,
                   sm: kind === 'detail' && o.sc > 4, pw: o.pw, ph: o.ph });
}
/* what should the worker do next? A naked margin someone can SEE
   outranks sharpness; otherwise the screen sharpens before the world
   fills in behind it. */
function pumpWorker() {
  if (!WK) return;
  if (wkRun) {
    if (wkRun.kind === 'detail' && wbuild && !wbuild.wkId && !groundCovers()) wkCancel(wkRun);
    return;
  }
  const naked = !groundCovers();
  const dj = build && !build.wkId ? build : null;
  const wj = wbuild && !wbuild.wkId ? wbuild : null;
  const next = naked ? (wj || dj) : (dj || wj);
  if (next) wkSend(next, next === wj ? 'world' : 'detail');
}

/* ---------------- simulation ---------------- */
let T = 0, playing = false, speed = 1, lastFrame = 0;
let settleT = 0, frozen = false, stillDirty = true, lastAlive = [];
let showLabels = true;
const DYING = [];
const PROJ = [];

/* ---- projectiles: volleys are battle data {from, to, t0, t1, rate, kind}.
   Each tracer stands for many missiles; they fly launch→target with no
   physics beyond a clock, so hundreds cost less than one flocking mote. */
/* `rng` is REAL RANGE IN METRES — converted to field units per battle via
   kmUnits. Without it a bowman could shoot the length of the map, over
   his own army's heads (Gaugamela shipped that way). A weapon that cannot
   reach simply does not fire. */
const PKINDS = {
  arrow:   { spd: 420, len: 4.5, w: 0.55, a: 0.85, lob: 1, rng: 250 },
  javelin: { spd: 260, len: 4, w: 0.7, a: 0.85, lob: 0.65, rng: 40 },
  shot:    { spd: 700, len: 8, w: 1.0, a: 0.95, lob: 0, rng: 3000 },
  // anti-aircraft: small pale sparks ending in a burst ring — nothing
  // like the darts they chase
  flak:    { spd: 520, len: 2.2, w: 0.5, a: 0.7, lob: 0, burst: true, rng: 4000 },
  // guided weapons: flat, fast, and a hot continuous exhaust trail —
  // one tracer = one missile wherever counts are known
  missile: { spd: 330, len: 9, w: 1.0, a: 0.95, lob: 0, hot: true, rng: 1600000 },
  // a bomb seen from above: a point that swells as it falls, then a
  // heavy impact and a permanent scar. No tracer line — bombs are
  // dropped, not shot.
  bomb:    { spd: 120, len: 0, w: 1.3, a: 0.95, lob: 0, bomb: true, rng: 600 },
};
const unitById = {};
for (const u of B.units) unitById[u.id] = u;
const aliveOf = (u) => {
  for (let tries = 0; tries < 6; tries++) {
    const e = u.ents[(Math.random() * u.ents.length) | 0];
    if (e.alive) return e;
  }
  return null;
};
/* the ENGAGEMENT FLOOR: a weapon's range is real, but a mote's position
   is schematic — on an operational table (Midway: 1 unit ≈ 270 m) a
   bomber IS over its target while the two motes sit ten units apart.
   Below 22 units the table cannot distinguish "adjacent" from "touching",
   so range never gates tighter than that. Without this floor a bomb's
   600 m became 0.8 units on the Iran table and every strike went silent;
   with it, Gaugamela's cross-field javelins (180 units) stay impossible. */
const ENGAGE = 22;
/* strikes are RUNS, not lines trading fire: when either end of a volley
   flies, the mote is a squadron centroid diving through its mark, and a
   22-unit gate makes the killing blow of Midway a coin flip. Air engages
   at 40. */
const AIR_ENGAGE = 40;
const rawRangeU = (k) => (k.rng || 250) / 1000 * (B.field.kmUnits || 1);
const engageU = (v, k) =>
  Math.max(DOMAIN[unitById[v.from].kind] === 'air' || DOMAIN[unitById[v.to].kind] === 'air'
    ? AIR_ENGAGE : ENGAGE, rawRangeU(k));
function nearestPair(su, tu, maxD) {
  const maxD2 = maxD * maxD;
  const ss = [], ts = [];
  // 12 samples a side: a big swarm's FRONT is a thin slice of it, and
  // five random motes routinely missed the men actually within reach
  for (let i = 0; i < 12; i++) { const e = aliveOf(su); if (e) ss.push(e); }
  for (let i = 0; i < 12; i++) { const e = aliveOf(tu); if (e) ts.push(e); }
  let best = null, bd = maxD2;
  for (const a of ss) for (const b of ts) {
    const dx = b.x - a.x, dy = b.y - a.y, d2 = dx * dx + dy * dy;
    if (d2 < bd) { bd = d2; best = [a, b]; }
  }
  return best;
}

/* every volley counts its shots — QA reads this to prove no window is
   silent (a range rule once muted two battles and nothing noticed) */
const VFIRED = B.volleys ? new Array(B.volleys.length).fill(0) : [];
if (B.volleys) B.volleys.forEach((v, i) => { v._i = i; });

function spawnVolleys(dt) {
  if (!B.volleys || PROJ.length > 500) return;
  for (const v of B.volleys) {
    if (T < v.t0 || T > v.t1) continue;
    v._acc = (v._acc || 0) + v.rate * dt * speed;
    while (v._acc >= 1) {
      v._acc -= 1;
      // deterministic per chassis: bombers drop bombs, whatever the data says
      const k = SHAPE[unitById[v.from].kind] === 'chevron'
        ? PKINDS.bomb : (PKINDS[v.kind] || PKINDS.arrow);
      // sample a few of each side and take the CLOSEST pair — men shoot at
      // what is in front of them. Out of range, nobody shoots.
      const pair = nearestPair(unitById[v.from], unitById[v.to], engageU(v, k));
      if (!pair) break;
      const [s, t] = pair;
      const x = s.x + (Math.random() - 0.5) * 8, y = s.y + (Math.random() - 0.5) * 8;
      const tx2 = t.x + (Math.random() - 0.5) * 14, ty2 = t.y + (Math.random() - 0.5) * 14;
      VFIRED[v._i]++;
      PROJ.push({
        x, y, tx: tx2, ty: ty2, p: 0,
        dur: Math.max(0.25, Math.hypot(tx2 - x, ty2 - y) / k.spd),
        k, c: s.c, tu: unitById[v.to],
      });
    }
  }
}
function renderProj(dt) {
  for (let i = PROJ.length - 1; i >= 0; i--) {
    const p = PROJ[i];
    if (playing && dir > 0) p.p += (dt * speed) / p.dur;
    if (p.p >= 1) {
      // a faint impact fleck on the trail, gone in a couple of seconds;
      // flak pops a small burst ring instead
      if (p.k.bomb) {
        // the thump: a bright fleck, a blast ring, and a crater that stays
        if (GLR) {
          GLR.t(p.tx, p.ty, p.tx, p.ty, 4.6, 0, 0, p.c, 0.4);
          GLR.t(p.tx, p.ty, p.tx, p.ty, 0.7, 4.4, 0, p.c, 0.22);
        } else {
          tctx.fillStyle = rgba(p.c, 0.4);
          tctx.beginPath(); tctx.arc(p.tx, p.ty, 2.3, 0, 6.2832); tctx.fill();
          tctx.strokeStyle = rgba(p.c, 0.22);
          tctx.lineWidth = 0.7;
          tctx.beginPath(); tctx.arc(p.tx, p.ty, 4.4, 0, 6.2832); tctx.stroke();
        }
        fctx.fillStyle = 'rgba(150,148,144,0.09)';
        fctx.beginPath(); fctx.arc(p.tx, p.ty, 1.7, 0, 6.2832); fctx.fill();
        groundDirty = true;
      } else if (p.k.burst) {
        if (GLR) GLR.t(p.tx, p.ty, p.tx, p.ty, 0.5, 2, 0, p.c, 0.3);
        else {
          tctx.strokeStyle = rgba(p.c, 0.3);
          tctx.lineWidth = 0.5;
          tctx.beginPath(); tctx.arc(p.tx, p.ty, 2, 0, 6.2832); tctx.stroke();
        }
      } else if (GLR) {
        GLR.t(p.tx, p.ty, p.tx, p.ty, 1.4, 0, 0, p.c, 0.3);
      } else {
        tctx.fillStyle = rgba(p.c, 0.3);
        tctx.beginPath(); tctx.arc(p.tx, p.ty, 0.7, 0, 6.2832); tctx.fill();
      }
      // missiles kill: if the target unit owes scheduled deaths, the
      // nearest living mote to the impact falls — visible causality,
      // totals still exactly on the historical record
      if (p.tu && dir > 0) {
        const u = p.tu;
        const quota = Math.round(lossFrac(u, T) * u.n);
        let dead = 0;
        for (const e2 of u.ents) if (!e2.alive) dead++;
        if (quota > dead) {
          let best = null, bd = 14 * 14;
          for (const e2 of u.ents) {
            if (!e2.alive) continue;
            const dx = e2.x - p.tx, dy = e2.y - p.ty, d2 = dx * dx + dy * dy;
            if (d2 < bd) { bd = d2; best = e2; }
          }
          if (best) killEnt(best);
        }
      }
      PROJ.splice(i, 1); continue;
    }
    const fx = p.x + (p.tx - p.x) * p.p, fy = p.y + (p.ty - p.y) * p.p;
    if (p.k.bomb) {
      if (GLR) {
        GLR.s(fx, fy, fx, fy, (1.2 + 2.4 * p.p) * p.k.w, 0, 2, 0, p.c, (0.45 + 0.5 * p.p) * p.k.a);
      } else {
        const r = (0.6 + 1.2 * p.p) * p.k.w * S * Z;
        cx2d.fillStyle = rgba(p.c, (0.45 + 0.5 * p.p) * p.k.a);
        cx2d.beginPath(); cx2d.arc(vx(fx), vy(fy), Math.max(1, r), 0, 6.2832); cx2d.fill();
      }
      continue;
    }
    const d = Math.hypot(p.tx - p.x, p.ty - p.y) || 1;
    const ux = (p.tx - p.x) / d, uy = (p.ty - p.y) / d;
    // lobbed weapons swell at apogee — nearer the eye from straight above;
    // shot stays flat and fast (missiles will get their own signature)
    const swell = 1 + (p.k.lob || 0) * 0.9 * Math.sin(Math.PI * p.p);
    const a = (0.3 + 0.7 * Math.sin(Math.PI * p.p)) * p.k.a;
    const len = p.k.len * swell;
    const pc = p.k.burst ? p.c.map((v) => (v + 255) >> 1) : p.c;  // flak burns pale
    // a short comet tail lives on the fading trail buffer — missiles burn
    // a hotter, heavier exhaust than anything thrown or shot
    if (GLR) {
      GLR.t(fx - ux * len * 2.4, fy - uy * len * 2.4, fx - ux * len * 0.6, fy - uy * len * 0.6,
            p.k.w * swell * (p.k.hot ? 1.5 : 1), 0, 0, pc, p.k.hot ? 0.38 : 0.2);
      GLR.s(fx - ux * len, fy - uy * len, fx, fy, p.k.w * swell, 0, 0.5, 0, pc, a);
      continue;
    }
    tctx.strokeStyle = rgba(pc, p.k.hot ? 0.38 : 0.2);
    tctx.lineWidth = p.k.w * swell * (p.k.hot ? 1.5 : 1);
    tctx.lineCap = 'round';
    tctx.beginPath();
    tctx.moveTo(fx - ux * len * 2.4, fy - uy * len * 2.4);
    tctx.lineTo(fx - ux * len * 0.6, fy - uy * len * 0.6);
    tctx.stroke();
    cx2d.strokeStyle = rgba(pc, a);
    cx2d.lineWidth = Math.max(0.5, p.k.w * swell * S * Z);
    cx2d.lineCap = 'round';
    cx2d.beginPath();
    cx2d.moveTo(vx(fx - ux * len), vy(fy - uy * len));
    cx2d.lineTo(vx(fx), vy(fy));
    cx2d.stroke();
  }
}
const reduceMotion = matchMedia('(prefers-reduced-motion: reduce)').matches;

function snapAll() {
  for (const e of ents) {
    const st = unitState(e.unit, T);
    const [sx, sy] = slotPos(e, st, T);
    e.x = sx + (Math.random() - 0.5) * 10;
    e.y = sy + (Math.random() - 0.5) * 10;
    const kn = KINDS[e.unit.kind] || KINDS.inf;
    if (kn.minV) {
      /* things that FLY snap in already flying: minimum airspeed, aligned
         with the formation. A random-heading start used to be scaled up
         to full speed by the airspeed floor, so every spawn and scrub
         opened with planes streaking off in random directions until the
         turn cap let them recover (Midway's opening). */
      const cs = kn.minV * kn.maxV;
      e.vx = Math.cos(st.ang) * cs + (Math.random() - 0.5) * 8;
      e.vy = Math.sin(st.ang) * cs + (Math.random() - 0.5) * 8;
    } else {
      e.vx = (Math.random() - 0.5) * 20; e.vy = (Math.random() - 0.5) * 20;
    }
    e.pxp = undefined;                 // contrails restart after a jump
  }
  tctx.clearRect(0, 0, FW, FH);
  if (GLR) GLR.clearTrail();
  DYING.length = 0;
  resurrect();
}

/* ---- deaths: the count follows the historical schedule, the victim is
   whoever is actually in contact with the enemy right now. Only when no
   one is (a surrounded press, a bombardment) do the outer ranks fall.
   Every death is logged with its time, so rewinding resurrects exactly. */
function killEnt(e) {
  e.alive = false; e.dieT = T;
  groundDirty = true;
  const kd = e.unit.kind;
  const sh = SHAPE[kd];
  const isHulk = sh === 'hull' || sh === 'block';
  if (isHulk) {
    // a struck ship or a knocked-out tank stays where it died, as a grey
    // hulk the size of the machine it was — these wrecks are the landmarks
    // the battle leaves behind
    const g = GLYPH[kd], hs = sh === 'hull' ? (e.unit.hull || 1) : 1;
    const back = sh === 'hull' ? 0.55 : 0.5, fwd = sh === 'hull' ? 0.45 : 0.5;
    fctx.strokeStyle = 'rgba(150,148,144,0.30)';
    fctx.lineWidth = g.w * Math.sqrt(hs);
    fctx.lineCap = sh === 'block' ? 'butt' : 'round';
    fctx.beginPath();
    fctx.moveTo(e.x - e.hx * g.len * back * hs, e.y - e.hy * g.len * back * hs);
    fctx.lineTo(e.x + e.hx * g.len * fwd * hs, e.y + e.hy * g.len * fwd * hs);
    fctx.stroke();
    fctx.lineCap = 'round';
  } else if (!(riverY && egAt(e.x, e.y) < 0.005)) {
    // grey where they fell — permanent, transparent, never in a river
    fctx.fillStyle = 'rgba(150,148,144,0.10)';
    fctx.beginPath(); fctx.arc(e.x, e.y, 0.9, 0, 6.2832); fctx.fill();
  }
  DYING.push({ x: e.x, y: e.y, c: e.c, age: 0, hx: e.hx, hy: e.hy, kd, hulk: isHulk, hs: e.unit.hull || 1 });
}

const CONTACT2 = 18 * 18;
function applyDeaths() {
  // units currently under missile fire get their remaining scheduled deaths
  // claimed by landing projectiles instead of the generic selector
  const FIRE = new Set();
  if (B.volleys) for (const v of B.volleys) if (T >= v.t0 && T <= v.t1) FIRE.add(v.to);
  for (const u of B.units) {
    const quota = Math.round(lossFrac(u, T) * u.n);
    let dead = 0;
    for (const e of u.ents) if (!e.alive) dead++;
    let need = quota - dead;
    if (need <= 0) continue;
    if (u.kind === 'ship') {
      // who struck is a matter of record — ships keep the scripted order
      const cands = u.ents.filter((e) => e.alive).sort((a, b) => a.thr - b.thr);
      for (let i = 0; i < need && i < cands.length; i++) killEnt(cands[i]);
      continue;
    }
    const near = [], rest = [];
    for (const e of u.ents) {
      if (!e.alive) continue;
      ((e.de2 ?? 1e9) < CONTACT2 ? near : rest).push(e);
    }
    near.sort((a, b) => (a.de2 ?? 1e9) - (b.de2 ?? 1e9));
    for (const e of near) { if (!need) break; killEnt(e); need--; }
    // during live playback, deaths under active fire are left for landing
    // tracers to claim — but tracers only fly while playing, so a paused
    // or scrubbed-to moment settles the full quota at once
    if (need && playing && dir > 0 && FIRE.has(u.id)) need = Math.max(0, need - 25);
    if (need) {
      rest.sort((a, b) => a.thr - b.thr);
      for (const e of rest) { if (!need) break; killEnt(e); need--; }
    }
  }
}

function resurrect() {
  for (const e of ents) {
    if (!e.alive && e.dieT !== undefined && e.dieT > T) { e.alive = true; e.dieT = undefined; }
  }
}

/* the spatial grid and the alive list persist across frames — allocating
   them per frame was pure GC pressure at seven thousand motes */
const GR = 26, GCOLS = Math.ceil(FW / GR) + 1, GROWS = Math.ceil(FH / GR) + 1;
const GRID = new Array(GCOLS * GROWS);
const GSTAMP = new Int32Array(GCOLS * GROWS);
const ALIVE = [];
let frameNo = 0;

function step(dt) {
  const R = GR, R2 = R * R;
  const cell = R, cols = GCOLS, rows = GROWS;
  const grid = GRID;
  frameNo++;
  const alive = ALIVE;
  alive.length = 0;
  for (const e of ents) {
    if (!e.alive) continue;
    if (e.x < -120 || e.x > FW + 120 || e.y < -120 || e.y > FH + 120) {
      e.n = 0; e.ci = undefined; alive.push(e); continue;
    }
    const ci = clamp(Math.floor(e.x / cell), 0, cols - 1);
    const cj = clamp(Math.floor(e.y / cell), 0, rows - 1);
    const idx = cj * cols + ci;
    let bkt = grid[idx];
    if (!bkt) bkt = grid[idx] = [];
    if (GSTAMP[idx] !== frameNo) { bkt.length = 0; GSTAMP[idx] = frameNo; }
    bkt.push(e);
    e.ci = ci; e.cj = cj;
    alive.push(e);
  }
  for (const e of alive) {
    const st = unitState(e.unit, T);
    const [sxT, syT] = e.ord ? [e.ord.x, e.ord.y] : slotPos(e, st, T);
    const kind = KINDS[e.unit.kind] || KINDS.inf;
    const dom = DOMAIN[e.unit.kind] || 'land';
    const maxV = kind.maxV, k = kind.k, damp = 2.8;
    const sep2 = kind.sep * kind.sep;
    let ax = (sxT - e.x) * k - e.vx * damp;
    let ay = (syT - e.y) * k - e.vy * damp;
    let de2 = 1e9;                     // squared distance to nearest enemy
    if (e.ci !== undefined) {
      let sxs = 0, sys = 0, avx = 0, avy = 0, n = 0;
      for (let gj = e.cj - 1; gj <= e.cj + 1; gj++) {
        if (gj < 0 || gj >= rows) continue;
        for (let gi = e.ci - 1; gi <= e.ci + 1; gi++) {
          if (gi < 0 || gi >= cols) continue;
          const bi = gj * cols + gi;
          const bkt = grid[bi];
          if (!bkt || GSTAMP[bi] !== frameNo) continue;
          for (const q of bkt) {
            if (q === e) continue;
            // a ship and an aeroplane share a map, not an element
            if (DOMAIN[q.unit.kind] !== dom) continue;
            const dx = q.x - e.x, dy = q.y - e.y, d2 = dx * dx + dy * dy;
            if (d2 > R2) continue;
            if (d2 < sep2 && d2 > 1e-4) { const inv = 1 / Math.sqrt(d2); sxs -= dx * inv; sys -= dy * inv; }
            if (q.unit.side !== e.unit.side) {
              // enemies press against each other but never flock together
              if (d2 < de2) de2 = d2;
              continue;
            }
            // formation-keeping is per chassis: horse does not set the pace
            // for foot, and no ship ever matches an aircraft's velocity
            if (q.unit.kind !== e.unit.kind) continue;
            n++; avx += q.vx; avy += q.vy;
          }
        }
      }
      e.n = n;
      if (n > 0) { ax += (avx / n - e.vx) * 0.9; ay += (avy / n - e.vy) * 0.9; }
      if (sxs || sys) { ax += sxs * 16; ay += sys * 16; }
    }
    e.de2 = de2;
    // wander calms down in a press so packed bodies read dense, not glitchy
    const wamp = 8 * kind.wander * (1 - 0.55 * Math.min(1, e.n / 16));
    ax += Math.sin(T * 1.9 * e.sp + e.ph) * wamp;
    ay += Math.cos(T * 2.3 * e.sp + e.ph * 0.7) * wamp;
    // land units keep out of the river
    if (riverY) {
      const dyR = e.y - riverY(e.x);
      const margin = TR.river.halfW + 10;
      if (Math.abs(dyR) < margin) ay += (dyR < 0 ? -1 : 1) * (margin - Math.abs(dyR)) * 8;
    }
    // soft sky walls: aircraft bank back onto the table — unless their
    // scripted path is genuinely leaving it
    if (DOMAIN[e.unit.kind] === 'air' && sxT > 0 && sxT < FW && syT > 0 && syT < FH) {
      const m2 = 50;
      if (e.x < m2) ax += (m2 - e.x) * 14;
      else if (e.x > FW - m2) ax -= (e.x - (FW - m2)) * 14;
      if (e.y < m2) ay += (m2 - e.y) * 14;
      else if (e.y > FH - m2) ay -= (e.y - (FH - m2)) * 14;
    }
    const pva = Math.atan2(e.vy, e.vx), pvs = Math.sqrt(e.vx * e.vx + e.vy * e.vy);
    e.vx += ax * dt; e.vy += ay * dt;
    let spd = Math.sqrt(e.vx * e.vx + e.vy * e.vy);
    if (spd > maxV) { e.vx = e.vx / spd * maxV; e.vy = e.vy / spd * maxV; spd = maxV; }
    // things that fly never hover: a minimum airspeed makes them orbit
    // their station instead of parking over it
    if (kind.minV) {
      const mv = maxV * kind.minV;
      if (spd < mv && spd > 1e-3) { e.vx *= mv / spd; e.vy *= mv / spd; spd = mv; }
    }
    // NOTHING on this table snap-turns. Heading change is capped per chassis
    // against the PREVIOUS velocity (capping against the smoothed display
    // heading glues everything to straight lines — bug burned once), with a
    // per-entity spread so formations stay irregular rather than geometric.
    if (kind.turn && pvs > 1) {
      const want = Math.atan2(e.vy, e.vx);
      let da2 = want - pva;
      while (da2 > Math.PI) da2 -= 6.2832;
      while (da2 < -Math.PI) da2 += 6.2832;
      const cap = kind.turn * (0.85 + 0.3 * e.sp) * dt;
      if (da2 > cap) da2 = cap; else if (da2 < -cap) da2 = -cap;
      const na = pva + da2;
      e.vx = Math.cos(na) * spd; e.vy = Math.sin(na) * spd;
    }
    e.x += e.vx * dt; e.y += e.vy * dt;
    // a drifting hull does not re-point itself: heading only follows velocity
    // once the thing is actually under way
    if (spd > (kind.hGate || 2)) {
      const a = Math.min(1, dt * 6);
      e.hx += (e.vx / spd - e.hx) * a; e.hy += (e.vy / spd - e.hy) * a;
      const hl = Math.sqrt(e.hx * e.hx + e.hy * e.hy) || 1;
      e.hx /= hl; e.hy /= hl;
    }
  }
  return alive;
}

/* stroke batching: the masses draw as a handful of beginPath/stroke calls
   instead of one per mote — grouped by cached colour string and width.
   Bucket objects persist across frames; only their point counts reset. */
function bktGet(map, list, key, style, width) {
  let b = map.get(key);
  if (!b) { b = { pts: [], n: 0, style, width }; map.set(key, b); }
  if (b.n === 0) list.push(b);
  return b;
}
function bktFlush(ctx2, list) {
  for (const b of list) {
    ctx2.strokeStyle = b.style; ctx2.lineWidth = b.width;
    ctx2.beginPath();
    const p = b.pts, n = b.n;
    for (let i = 0; i < n; i += 4) { ctx2.moveTo(p[i], p[i + 1]); ctx2.lineTo(p[i + 2], p[i + 3]); }
    ctx2.stroke();
    b.n = 0;
  }
  list.length = 0;
}
const TBM = new Map(), TBL = [];    // trail-buffer buckets
const BBM = new Map(), BBL = [];    // body buckets (screen canvas)

let fadeFlip = false;
function render(alive, rdt) {
  if (GLR) return renderGL(alive, rdt);
  // fading 5.8M buffer pixels every frame is a big slice of the raster
  // bill — every OTHER frame at double strength looks the same, costs half
  if (rdt > 0) fadeFlip = !fadeFlip;
  if (rdt > 0 && fadeFlip) {
    tctx.globalCompositeOperation = 'destination-out';
    tctx.fillStyle = 'rgba(0,0,0,0.26)';
    tctx.fillRect(0, 0, FW, FH);
    tctx.globalCompositeOperation = 'source-over';
  }
  tctx.lineCap = 'round';
  for (const e of alive) {
    if (!e.unit.offField && (e.x < -70 || e.x > FW + 70 || e.y < -70 || e.y > FH + 70)) { e.pxp = undefined; continue; }
    const tr = TRAIL[e.unit.kind] || 'none';
    if (tr === 'contrail') {
      // the contrail: a thin continuous line stitched from the previous
      // position. The aircraft itself is drawn on the screen canvas.
      // Stealth bombers barely leave one.
      if (e.pxp !== undefined) {
        const ca = TRAILA[e.unit.kind] ?? 0.06;
        const b = bktGet(TBM, TBL, e.cid * 1000 + ((ca * 100) | 0), colStr(e.cid, ca), 0.6);
        b.pts[b.n++] = e.pxp; b.pts[b.n++] = e.pyp; b.pts[b.n++] = e.x; b.pts[b.n++] = e.y;
      }
      e.pxp = e.x; e.pyp = e.y;
      continue;
    }
    if (tr === 'none') continue;
    if (tr === 'wake') {
      // the wake: a faint hull stamp left to fade behind the moving ship
      const g = GLYPH[e.unit.kind] || GLYPH.ship, hs = e.unit.hull || 1;
      tctx.strokeStyle = rgba(e.c, 0.3);
      tctx.lineWidth = g.w * Math.sqrt(hs);
      tctx.beginPath();
      tctx.moveTo(e.x - e.hx * g.len * 0.55 * hs, e.y - e.hy * g.len * 0.55 * hs);
      tctx.lineTo(e.x + e.hx * g.len * 0.45 * hs, e.y + e.hy * g.len * 0.45 * hs);
      tctx.stroke();
      continue;
    }
    if (tr === 'treads') {
      // tread marks: two continuous parallel lines, the width of the hull
      const g = GLYPH[e.unit.kind] || GLYPH.tank;
      if (e.pxp !== undefined) {
        const px2 = -e.hy * g.w * 0.42, py2 = e.hx * g.w * 0.42;
        tctx.strokeStyle = rgba(e.c, 0.10);
        tctx.lineWidth = 0.7;
        tctx.beginPath();
        tctx.moveTo(e.pxp + px2, e.pyp + py2); tctx.lineTo(e.x + px2, e.y + py2);
        tctx.moveTo(e.pxp - px2, e.pyp - py2); tctx.lineTo(e.x - px2, e.y - py2);
        tctx.stroke();
      }
      e.pxp = e.x; e.pyp = e.y;
      continue;
    }
    const dens = Math.min(1, e.n / 16);
    const spd = Math.sqrt(e.vx * e.vx + e.vy * e.vy);
    const kind = KINDS[e.unit.kind] || KINDS.inf;
    // signature ground trails, stamped by distance marched — men leave two
    // alternating footprints, horses a four-hoof double track (ships get
    // their wake from the hull stroke itself)
    if (spd > kind.maxV * 0.12 && (e.unit.kind === 'inf' || e.unit.kind === 'cav')) {
      e.trav += spd * rdt;
      const stride = e.unit.kind === 'cav' ? 8 : 5.5;
      if (e.trav > stride) {
        e.trav %= stride;
        const pxp = -e.hy, pyp = e.hx;
        tctx.fillStyle = rgba(e.c, 0.14);
        if (e.unit.kind === 'cav') {
          tctx.fillRect(e.x + pxp * 0.9 - 0.4, e.y + pyp * 0.9 - 0.4, 0.8, 0.8);
          tctx.fillRect(e.x - pxp * 0.9 - 0.4, e.y - pyp * 0.9 - 0.4, 0.8, 0.8);
        } else {
          e.foot = -e.foot;
          tctx.fillRect(e.x + pxp * 0.65 * e.foot - 0.35, e.y + pyp * 0.65 * e.foot - 0.35, 0.7, 0.7);
        }
      }
    }
    // the smear the mote leaves behind it — half the weight it used to carry,
    // because the mote's bright head is now drawn crisp on the screen canvas
    const g = GLYPH[e.unit.kind] || GLYPH.inf;
    const lf = clamp(spd / (kind.maxV * 0.45), 0.15, 1);
    const dq = (dens * 7.99) | 0;         // 8 density bands share one stroke
    const len = g.len * (0.38 + 0.62 * dens) * lf;
    const b = bktGet(TBM, TBL, (e.cid * 8 + dq) * 64 + ((g.w * 10) | 0),
      colStr(e.cid, 0.09 + 0.24 * dq / 8), g.w * (0.59 + 0.41 * dq / 8));
    b.pts[b.n++] = e.x - e.hx * len; b.pts[b.n++] = e.y - e.hy * len;
    b.pts[b.n++] = e.x; b.pts[b.n++] = e.y;
  }
  tctx.lineCap = 'round';
  bktFlush(tctx, TBL);
  // composite: the ground layer redraws itself only when something
  // changed; this canvas carries only the per-frame surfaces
  if (groundDirty) drawGround();
  cx2d.clearRect(0, 0, SW, SH);
  const dw = FW * S * Z, dh = FH * S * Z;
  cx2d.imageSmoothingEnabled = true;
  cx2d.drawImage(trail.cv, VX, VY, dw, dh);
  renderBodies(alive);
  drawScreenUI();
}

/* selection chrome + labels: pure screen-canvas vector UI, shared by the
   canvas and GL paths (in GL it is all the screen canvas still draws) */
function drawScreenUI() {
  if (cmdMode) {
    if (selStart && selRect && selMoved) {
      cx2d.strokeStyle = 'rgba(216,211,200,0.5)';
      cx2d.setLineDash([4, 4]);
      cx2d.lineWidth = 1;
      cx2d.strokeRect(selStart.x, selStart.y, selRect.x - selStart.x, selRect.y - selStart.y);
      cx2d.setLineDash([]);
    }
    cx2d.strokeStyle = 'rgba(216,211,200,0.4)';
    cx2d.lineWidth = 1;
    const rr = Math.max(2.5, 3 * S * Z);
    for (const e of SEL) {
      if (!e.alive) continue;
      cx2d.beginPath(); cx2d.arc(vx(e.x), vy(e.y), rr, 0, 6.2832); cx2d.stroke();
    }
  }
  if (showLabels) drawLabels();
}

/* ---- the living, drawn straight onto the screen canvas -----------------
   The buffers above hold HISTORY, and history is allowed to be soft. The
   things still fighting are not: they are re-drawn every frame from vector
   data anyway, so we draw them here at device resolution under a field-space
   transform. A carrier at 8× zoom is then a crisp 8×-larger hull instead of
   a magnified buffer pixel, at no cost — the geometry is identical, only the
   surface changes. */
function renderBodies(alive) {
  const k = DPR * S * Z;
  cx2d.save();
  cx2d.setTransform(k, 0, 0, k, DPR * VX, DPR * VY);   // now drawing in field units
  cx2d.lineCap = 'round';
  for (const e of alive) {
    /* past the field's edge the living DIM OUT across ~70 units instead
       of vanishing at a hard line — an exit dissolves into the country
       rather than falling off the table. Margin residents are exempt:
       they LIVE out there. */
    const ov = e.unit.offField ? 0 : Math.max(-e.x, e.x - FW, -e.y, e.y - FH, 0);
    if (ov >= 70) continue;
    const ef = 1 - ov / 70;
    const efq = (ef * 4.99) | 0, efv = (efq + 1) / 5;
    const kd = e.unit.kind;
    const g = GLYPH[kd] || GLYPH.inf;
    const shape = SHAPE[kd] || 'streak';
    if (shape === 'dart') {
      // one dart = one aircraft, nose forward
      const b = bktGet(BBM, BBL, e.cid * 64 + ((g.w * 10) | 0) + efq * 1e6,
        colStr(e.cid, 0.85 * efv), g.w);
      b.pts[b.n++] = e.x - e.hx * g.len * 0.72; b.pts[b.n++] = e.y - e.hy * g.len * 0.72;
      b.pts[b.n++] = e.x + e.hx * g.len * 0.28; b.pts[b.n++] = e.y + e.hy * g.len * 0.28;
      continue;
    }
    if (shape === 'chevron') {
      // a flying wing: two swept arms meeting at the nose — from above,
      // unmistakably not a fighter
      const nx = e.x + e.hx * g.len * 0.4, ny = e.y + e.hy * g.len * 0.4;
      const px2 = -e.hy * g.len * 0.62, py2 = e.hx * g.len * 0.62;
      cx2d.strokeStyle = colStr(e.cid, 0.9 * ef);
      cx2d.lineWidth = g.w;
      cx2d.beginPath();
      cx2d.moveTo(nx - e.hx * g.len * 0.85 + px2, ny - e.hy * g.len * 0.85 + py2);
      cx2d.lineTo(nx, ny);
      cx2d.lineTo(nx - e.hx * g.len * 0.85 - px2, ny - e.hy * g.len * 0.85 - py2);
      cx2d.stroke();
      continue;
    }
    if (shape === 'hull') {
      // one hull = one ship; unit.hull scales capitals up from their escorts
      const hs = e.unit.hull || 1;
      const bx = e.x + e.hx * g.len * 0.45 * hs, by = e.y + e.hy * g.len * 0.45 * hs;
      cx2d.strokeStyle = colStr(e.cid, 0.85 * ef);
      cx2d.lineWidth = g.w * Math.sqrt(hs);
      cx2d.beginPath();
      cx2d.moveTo(e.x - e.hx * g.len * 0.55 * hs, e.y - e.hy * g.len * 0.55 * hs);
      cx2d.lineTo(bx, by);
      cx2d.stroke();
      cx2d.fillStyle = colStr(e.cid, 0.95 * ef);
      cx2d.beginPath(); cx2d.arc(bx, by, g.w * 0.34 * hs, 0, 6.2832); cx2d.fill();
      continue;
    }
    if (shape === 'block') {
      // a blunt squared hull with a barrel — nothing on the table reads
      // less like a ship than this
      cx2d.lineCap = 'butt';
      cx2d.strokeStyle = colStr(e.cid, 0.88 * ef);
      cx2d.lineWidth = g.w;
      cx2d.beginPath();
      cx2d.moveTo(e.x - e.hx * g.len * 0.5, e.y - e.hy * g.len * 0.5);
      cx2d.lineTo(e.x + e.hx * g.len * 0.5, e.y + e.hy * g.len * 0.5);
      cx2d.stroke();
      cx2d.lineCap = 'round';
      cx2d.lineWidth = g.w * 0.22;
      cx2d.beginPath();
      cx2d.moveTo(e.x + e.hx * g.len * 0.45, e.y + e.hy * g.len * 0.45);
      cx2d.lineTo(e.x + e.hx * g.len * 0.9, e.y + e.hy * g.len * 0.9);
      cx2d.stroke();
      continue;
    }
    const dens = Math.min(1, e.n / 16);
    const kind = KINDS[kd] || KINDS.inf;
    const spd = Math.sqrt(e.vx * e.vx + e.vy * e.vy);
    const lf = clamp(spd / (kind.maxV * 0.45), 0.15, 1);
    const dq = (dens * 7.99) | 0;
    const len = g.len * (0.38 + 0.62 * dens) * lf;
    const b = bktGet(BBM, BBL, (e.cid * 8 + dq) * 64 + ((g.w * 10) | 0) + 32768 + efq * 1e6,
      colStr(e.cid, (0.16 + 0.42 * dq / 8) * efv), g.w * (0.59 + 0.41 * dq / 8));
    b.pts[b.n++] = e.x - e.hx * len; b.pts[b.n++] = e.y - e.hy * len;
    b.pts[b.n++] = e.x; b.pts[b.n++] = e.y;
  }
  bktFlush(cx2d, BBL);
  cx2d.restore();
}

function renderDying(dt) {
  const rr = Math.max(1.1, 1.4 * S * Z);
  for (let i = DYING.length - 1; i >= 0; i--) {
    const d = DYING[i];
    d.age += dt;
    if (d.age > 2) { DYING.splice(i, 1); continue; }
    const f = Math.min(1, d.age / 0.8);
    const r = Math.round(d.c[0] + (140 - d.c[0]) * f);
    const g = Math.round(d.c[1] + (139 - d.c[1]) * f);
    const b = Math.round(d.c[2] + (136 - d.c[2]) * f);
    const a = 0.55 * (1 - d.age / 2);
    if (d.hulk) {
      const gs = GLYPH[d.kd] || GLYPH.ship, hs = SHAPE[d.kd] === 'hull' ? (d.hs || 1) : 1;
      const back = SHAPE[d.kd] === 'hull' ? 0.55 : 0.5, fwd = SHAPE[d.kd] === 'hull' ? 0.45 : 0.5;
      if (GLR) {
        GLR.s(d.x - d.hx * gs.len * back * hs, d.y - d.hy * gs.len * back * hs,
              d.x + d.hx * gs.len * fwd * hs, d.y + d.hy * gs.len * fwd * hs,
              gs.w * Math.sqrt(hs), 0, 0, SHAPE[d.kd] === 'block' ? 1 : 0, [r, g, b], a);
        continue;
      }
      cx2d.strokeStyle = `rgba(${r},${g},${b},${a})`;
      cx2d.lineWidth = gs.w * Math.sqrt(hs) * S * Z;
      cx2d.lineCap = SHAPE[d.kd] === 'block' ? 'butt' : 'round';
      cx2d.beginPath();
      cx2d.moveTo(vx(d.x - d.hx * gs.len * back * hs), vy(d.y - d.hy * gs.len * back * hs));
      cx2d.lineTo(vx(d.x + d.hx * gs.len * fwd * hs), vy(d.y + d.hy * gs.len * fwd * hs));
      cx2d.stroke();
      cx2d.lineCap = 'round';
    } else if (GLR) {
      GLR.s(d.x, d.y, d.x, d.y, 2.8, 0, 2.2, 0, [r, g, b], a);
    } else {
      cx2d.fillStyle = `rgba(${r},${g},${b},${a})`;
      cx2d.beginPath(); cx2d.arc(vx(d.x), vy(d.y), rr, 0, 6.2832); cx2d.fill();
    }
  }
}

/* ---- the WebGL renderer: the same table, drawn by the GPU --------------
   Everything the sim draws per frame reduces to THREE primitives — a
   round- or butt-capped segment, a dot, a ring — so one instanced SDF
   shader renders all of it: mote bodies, trail stamps, tracers, the dying.
   Trails persist in a field-space framebuffer that fades exactly like the
   canvas buffer (every other frame, 0.26); bodies draw straight to the
   screen under the view transform. The formulas are copied VERBATIM from
   the canvas path — the parity harness diffs the two, and any tweak to
   one path lands in both or fails review. Canvas remains the default and
   the fallback (?gl=1 opts in; context loss falls back mid-session), so
   the table can never fail to draw.
   preserveDrawingBuffer stays TRUE: the reel exporter must be able to
   read frames back however it chooses. */
function mkGLRenderer() {
  const c = document.createElement('canvas');
  c.style.cssText = 'position:fixed;inset:0;display:block;pointer-events:none;';
  cv.parentNode.insertBefore(c, cv);
  const gl = c.getContext('webgl2', {
    alpha: true, antialias: false, premultipliedAlpha: true,
    preserveDrawingBuffer: true, powerPreference: 'high-performance',
  });
  if (!gl) { c.remove(); return null; }

  const sh = (type, src) => {
    const s = gl.createShader(type);
    gl.shaderSource(s, src); gl.compileShader(s);
    if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) throw new Error(gl.getShaderInfoLog(s));
    return s;
  };
  const prog = (vs, fs) => {
    const p = gl.createProgram();
    gl.attachShader(p, sh(gl.VERTEX_SHADER, vs));
    gl.attachShader(p, sh(gl.FRAGMENT_SHADER, fs));
    gl.linkProgram(p);
    if (!gl.getProgramParameter(p, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(p));
    return p;
  };

  /* the one primitive: an instanced quad wrapping a capsule/rect SDF.
     iP = segment endpoints (field units; equal endpoints = a dot),
     iS = (width, ringRadius, minPx, cap: 0 round / 1 butt),
     iC = straight rgba — premultiplied in the fragment. */
  const PRIM = prog(`#version 300 es
    layout(location=0) in vec4 iP;
    layout(location=1) in vec4 iS;
    layout(location=2) in vec4 iC;
    uniform vec3 uView;   // px-per-field-unit, offset px
    uniform vec2 uVp;     // viewport px
    out vec2 vL;
    flat out float fLen, fW, fRing, fCap;
    flat out vec4 fC;
    void main() {
      vec2 p0 = iP.xy * uView.x + uView.yz;
      vec2 p1 = iP.zw * uView.x + uView.yz;
      vec2 d = p1 - p0;
      float len = length(d);
      vec2 dir = len > 1e-4 ? d / len : vec2(1.0, 0.0);
      vec2 nrm = vec2(-dir.y, dir.x);
      float w = max(iS.x * uView.x, iS.z);
      float ring = iS.y * uView.x;
      float ext = w * 0.5 + ring + 1.5;
      float cu = (gl_VertexID == 0 || gl_VertexID == 1) ? -ext : len + ext;
      float cw = (gl_VertexID == 0 || gl_VertexID == 2) ? -ext : ext;
      vec2 pos = p0 + dir * cu + nrm * cw;
      vL = vec2(cu, cw);
      fLen = len; fW = w; fRing = ring; fCap = iS.w; fC = iC;
      vec2 clip = pos / uVp * 2.0 - 1.0;
      gl_Position = vec4(clip.x, -clip.y, 0.0, 1.0);
    }`, `#version 300 es
    precision highp float;
    in vec2 vL;
    flat in float fLen, fW, fRing, fCap;
    flat in vec4 fC;
    out vec4 o;
    void main() {
      float d;
      if (fCap > 0.5) {
        float du = max(max(-vL.x, vL.x - fLen), 0.0);
        d = max(abs(vL.y), du);
      } else {
        float uc = clamp(vL.x, 0.0, fLen);
        d = length(vec2(vL.x - uc, vL.y));
      }
      if (fRing > 0.0) d = abs(d - fRing);
      float cov = smoothstep(fW * 0.5 + 0.75, fW * 0.5 - 0.75, d);
      if (cov <= 0.003) discard;
      float a = fC.a * cov;
      o = vec4(fC.rgb * a, a);
    }`);
  const uPView = gl.getUniformLocation(PRIM, 'uView');
  const uPVp = gl.getUniformLocation(PRIM, 'uVp');

  /* composite: the trail texture laid over the screen under the view
     transform (the GL twin of drawImage(trail.cv, VX, VY, dw, dh)) */
  const TEX = prog(`#version 300 es
    uniform vec3 uView;
    uniform vec2 uVp, uField;
    out vec2 vUv;
    void main() {
      vec2 f = vec2((gl_VertexID == 0 || gl_VertexID == 1) ? 0.0 : uField.x,
                    (gl_VertexID == 0 || gl_VertexID == 2) ? 0.0 : uField.y);
      vUv = vec2(f.x / uField.x, 1.0 - f.y / uField.y);
      vec2 pos = f * uView.x + uView.yz;
      vec2 clip = pos / uVp * 2.0 - 1.0;
      gl_Position = vec4(clip.x, -clip.y, 0.0, 1.0);
    }`, `#version 300 es
    precision highp float;
    uniform sampler2D uTex;
    in vec2 vUv;
    out vec4 o;
    void main() { o = texture(uTex, vUv); }`);
  const uTView = gl.getUniformLocation(TEX, 'uView');
  const uTVp = gl.getUniformLocation(TEX, 'uVp');
  const uTField = gl.getUniformLocation(TEX, 'uField');

  /* fade: a fullscreen pass that multiplies the trail buffer by 0.74 —
     the blend does the work, the shader's colour is irrelevant */
  const FADE = prog(`#version 300 es
    void main() {
      vec2 c = vec2((gl_VertexID == 0 || gl_VertexID == 1) ? -1.0 : 1.0,
                    (gl_VertexID == 0 || gl_VertexID == 2) ? -1.0 : 1.0);
      gl_Position = vec4(c, 0.0, 1.0);
    }`, `#version 300 es
    precision highp float;
    out vec4 o;
    void main() { o = vec4(0.0); }`);

  /* the trail target: one field-space texture, faded in place */
  const tw = Math.min(8192, Math.round(FW * FS)), th = Math.min(8192, Math.round(FH * FS));
  const tex = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, tex);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, tw, th, 0, gl.RGBA, gl.UNSIGNED_BYTE, null);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  const fbo = gl.createFramebuffer();
  gl.bindFramebuffer(gl.FRAMEBUFFER, fbo);
  gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, tex, 0);
  gl.clearColor(0, 0, 0, 0);
  gl.clear(gl.COLOR_BUFFER_BIT);
  gl.bindFramebuffer(gl.FRAMEBUFFER, null);

  /* two instance streams: trail-bound and screen-bound. 12 floats each:
     x0 y0 x1 y1 · w ring minPx cap · r g b a */
  const mkStream = () => {
    const vao = gl.createVertexArray();
    gl.bindVertexArray(vao);
    const vbo = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
    for (let i = 0; i < 3; i++) {
      gl.enableVertexAttribArray(i);
      gl.vertexAttribPointer(i, 4, gl.FLOAT, false, 48, i * 16);
      gl.vertexAttribDivisor(i, 1);
    }
    gl.bindVertexArray(null);
    return { vao, vbo, arr: new Float32Array(4096 * 12), n: 0 };
  };
  const TB = mkStream(), SB = mkStream();
  const push = (B2, x0, y0, x1, y1, w, ring, minPx, cap, col, a) => {
    if ((B2.n + 1) * 12 > B2.arr.length) {
      const bigger = new Float32Array(B2.arr.length * 2);
      bigger.set(B2.arr); B2.arr = bigger;
    }
    const o = B2.n * 12, A = B2.arr;
    A[o] = x0; A[o + 1] = y0; A[o + 2] = x1; A[o + 3] = y1;
    A[o + 4] = w; A[o + 5] = ring; A[o + 6] = minPx; A[o + 7] = cap;
    A[o + 8] = col[0] / 255; A[o + 9] = col[1] / 255; A[o + 10] = col[2] / 255; A[o + 11] = a;
    B2.n++;
  };
  const drawStream = (B2, k, ox, oy, vw, vh) => {
    if (!B2.n) return;
    gl.useProgram(PRIM);
    gl.uniform3f(uPView, k, ox, oy);
    gl.uniform2f(uPVp, vw, vh);
    gl.bindVertexArray(B2.vao);
    gl.bindBuffer(gl.ARRAY_BUFFER, B2.vbo);
    gl.bufferData(gl.ARRAY_BUFFER, B2.arr.subarray(0, B2.n * 12), gl.STREAM_DRAW);
    gl.drawArraysInstanced(gl.TRIANGLE_STRIP, 0, 4, B2.n);
    gl.bindVertexArray(null);
  };

  /* colStr's palette, as numbers the shader can take */
  const PALRGB = PALSTR.map((s) => s.split(',').map(Number));

  gl.disable(gl.DEPTH_TEST);
  gl.enable(gl.BLEND);

  const R = {
    cv: c, lost: false, fade: false,
    pal: (cid) => PALRGB[cid],
    t: (x0, y0, x1, y1, w, ring, cap, col, a) => push(TB, x0, y0, x1, y1, w, ring, 0, cap, col, a),
    s: (x0, y0, x1, y1, w, ring, minPx, cap, col, a) => push(SB, x0, y0, x1, y1, w, ring, minPx, cap, col, a),
    clearTrail() {
      gl.bindFramebuffer(gl.FRAMEBUFFER, fbo);
      gl.clearColor(0, 0, 0, 0);
      gl.clear(gl.COLOR_BUFFER_BIT);
      gl.bindFramebuffer(gl.FRAMEBUFFER, null);
    },
    resize() {
      c.width = SW * DPR; c.height = SH * DPR;
      c.style.width = SW + 'px'; c.style.height = SH + 'px';
    },
    endFrame() {
      if (this.lost) return;
      const fs2 = tw / FW;
      gl.bindFramebuffer(gl.FRAMEBUFFER, fbo);
      gl.viewport(0, 0, tw, th);
      if (this.fade) {
        this.fade = false;
        gl.blendColor(0, 0, 0, 0.26);
        gl.blendFunc(gl.ZERO, gl.ONE_MINUS_CONSTANT_ALPHA);
        gl.useProgram(FADE);
        gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);
      }
      gl.blendFunc(gl.ONE, gl.ONE_MINUS_SRC_ALPHA);
      drawStream(TB, fs2, 0, 0, tw, th);
      gl.bindFramebuffer(gl.FRAMEBUFFER, null);
      gl.viewport(0, 0, c.width, c.height);
      gl.clearColor(0, 0, 0, 0);
      gl.clear(gl.COLOR_BUFFER_BIT);
      const k = S * Z * DPR;
      gl.useProgram(TEX);
      gl.uniform3f(uTView, k, VX * DPR, VY * DPR);
      gl.uniform2f(uTVp, c.width, c.height);
      gl.uniform2f(uTField, FW, FH);
      gl.bindTexture(gl.TEXTURE_2D, tex);
      gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);
      drawStream(SB, k, VX * DPR, VY * DPR, c.width, c.height);
      TB.n = 0; SB.n = 0;
    },
  };
  R.resize();
  c.addEventListener('webglcontextlost', (e) => {
    /* the table must never fail to draw: fall back to the canvas path.
       Trail history restarts soft — the same truce a scrub already makes. */
    e.preventDefault();
    R.lost = true;
    GLR = null;
    c.remove();
  });
  return R;
}

/* the GL twin of render()'s staging: identical formulas, different sink */
function renderGL(alive, rdt) {
  const G = GLR;
  if (rdt > 0) fadeFlip = !fadeFlip;
  if (rdt > 0 && fadeFlip) G.fade = true;
  for (const e of alive) {
    if (!e.unit.offField && (e.x < -70 || e.x > FW + 70 || e.y < -70 || e.y > FH + 70)) { e.pxp = undefined; continue; }
    const tr = TRAIL[e.unit.kind] || 'none';
    if (tr === 'contrail') {
      if (e.pxp !== undefined) {
        const ca = TRAILA[e.unit.kind] ?? 0.06;
        G.t(e.pxp, e.pyp, e.x, e.y, 0.6, 0, 0, G.pal(e.cid), ca);
      }
      e.pxp = e.x; e.pyp = e.y;
    } else if (tr === 'wake') {
      const g = GLYPH[e.unit.kind] || GLYPH.ship, hs = e.unit.hull || 1;
      G.t(e.x - e.hx * g.len * 0.55 * hs, e.y - e.hy * g.len * 0.55 * hs,
          e.x + e.hx * g.len * 0.45 * hs, e.y + e.hy * g.len * 0.45 * hs,
          g.w * Math.sqrt(hs), 0, 0, e.c, 0.3);
    } else if (tr === 'treads') {
      const g = GLYPH[e.unit.kind] || GLYPH.tank;
      if (e.pxp !== undefined) {
        const px2 = -e.hy * g.w * 0.42, py2 = e.hx * g.w * 0.42;
        G.t(e.pxp + px2, e.pyp + py2, e.x + px2, e.y + py2, 0.7, 0, 0, e.c, 0.10);
        G.t(e.pxp - px2, e.pyp - py2, e.x - px2, e.y - py2, 0.7, 0, 0, e.c, 0.10);
      }
      e.pxp = e.x; e.pyp = e.y;
    } else if (tr !== 'none') {
      const dens = Math.min(1, e.n / 16);
      const spd = Math.sqrt(e.vx * e.vx + e.vy * e.vy);
      const kind = KINDS[e.unit.kind] || KINDS.inf;
      if (spd > kind.maxV * 0.12 && (e.unit.kind === 'inf' || e.unit.kind === 'cav')) {
        e.trav += spd * rdt;
        const stride = e.unit.kind === 'cav' ? 8 : 5.5;
        if (e.trav > stride) {
          e.trav %= stride;
          const pxp = -e.hy, pyp = e.hx;
          if (e.unit.kind === 'cav') {
            G.t(e.x + pxp * 0.9, e.y + pyp * 0.9, e.x + pxp * 0.9, e.y + pyp * 0.9, 0.8, 0, 0, e.c, 0.14);
            G.t(e.x - pxp * 0.9, e.y - pyp * 0.9, e.x - pxp * 0.9, e.y - pyp * 0.9, 0.8, 0, 0, e.c, 0.14);
          } else {
            e.foot = -e.foot;
            G.t(e.x + pxp * 0.65 * e.foot, e.y + pyp * 0.65 * e.foot,
                e.x + pxp * 0.65 * e.foot, e.y + pyp * 0.65 * e.foot, 0.7, 0, 0, e.c, 0.14);
          }
        }
      }
      const g = GLYPH[e.unit.kind] || GLYPH.inf;
      const lf = clamp(spd / (kind.maxV * 0.45), 0.15, 1);
      const dq = (dens * 7.99) | 0;
      const len = g.len * (0.38 + 0.62 * dens) * lf;
      G.t(e.x - e.hx * len, e.y - e.hy * len, e.x, e.y,
          g.w * (0.59 + 0.41 * dq / 8), 0, 0, G.pal(e.cid), 0.09 + 0.24 * dq / 8);
    }
    /* the living body, screen-bound (margin residents never dim) */
    const ov = e.unit.offField ? 0 : Math.max(-e.x, e.x - FW, -e.y, e.y - FH, 0);
    if (ov >= 70) continue;
    const ef = 1 - ov / 70;
    const efq = (ef * 4.99) | 0, efv = (efq + 1) / 5;
    const kd = e.unit.kind;
    const g = GLYPH[kd] || GLYPH.inf;
    const shape = SHAPE[kd] || 'streak';
    if (shape === 'dart') {
      G.s(e.x - e.hx * g.len * 0.72, e.y - e.hy * g.len * 0.72,
          e.x + e.hx * g.len * 0.28, e.y + e.hy * g.len * 0.28,
          g.w, 0, 0, 0, G.pal(e.cid), 0.85 * efv);
    } else if (shape === 'chevron') {
      const nx = e.x + e.hx * g.len * 0.4, ny = e.y + e.hy * g.len * 0.4;
      const px2 = -e.hy * g.len * 0.62, py2 = e.hx * g.len * 0.62;
      G.s(nx - e.hx * g.len * 0.85 + px2, ny - e.hy * g.len * 0.85 + py2, nx, ny,
          g.w, 0, 0, 0, G.pal(e.cid), 0.9 * ef);
      G.s(nx - e.hx * g.len * 0.85 - px2, ny - e.hy * g.len * 0.85 - py2, nx, ny,
          g.w, 0, 0, 0, G.pal(e.cid), 0.9 * ef);
    } else if (shape === 'hull') {
      const hs = e.unit.hull || 1;
      const bx = e.x + e.hx * g.len * 0.45 * hs, by = e.y + e.hy * g.len * 0.45 * hs;
      G.s(e.x - e.hx * g.len * 0.55 * hs, e.y - e.hy * g.len * 0.55 * hs, bx, by,
          g.w * Math.sqrt(hs), 0, 0, 0, G.pal(e.cid), 0.85 * ef);
      G.s(bx, by, bx, by, g.w * 0.68 * hs, 0, 0, 0, G.pal(e.cid), 0.95 * ef);
    } else if (shape === 'block') {
      G.s(e.x - e.hx * g.len * 0.5, e.y - e.hy * g.len * 0.5,
          e.x + e.hx * g.len * 0.5, e.y + e.hy * g.len * 0.5,
          g.w, 0, 0, 1, G.pal(e.cid), 0.88 * ef);
      G.s(e.x + e.hx * g.len * 0.45, e.y + e.hy * g.len * 0.45,
          e.x + e.hx * g.len * 0.9, e.y + e.hy * g.len * 0.9,
          g.w * 0.22, 0, 0, 0, G.pal(e.cid), 0.88 * ef);
    } else {
      const dens = Math.min(1, e.n / 16);
      const kind = KINDS[kd] || KINDS.inf;
      const spd = Math.sqrt(e.vx * e.vx + e.vy * e.vy);
      const lf = clamp(spd / (kind.maxV * 0.45), 0.15, 1);
      const dq = (dens * 7.99) | 0;
      const len = g.len * (0.38 + 0.62 * dens) * lf;
      G.s(e.x - e.hx * len, e.y - e.hy * len, e.x, e.y,
          g.w * (0.59 + 0.41 * dq / 8), 0, 0, 0, G.pal(e.cid), (0.16 + 0.42 * dq / 8) * efv);
    }
  }
  if (groundDirty) drawGround();
  cx2d.clearRect(0, 0, SW, SH);
  drawScreenUI();
}

/* a film camera watches CONSECUTIVE frames, which a browsing hand never
   does — so labels must be steady, not merely well-placed. Three rules
   keep them still: the anchor is a LOW-PASS of the unit's centroid in
   FIELD space (mote jitter smoothed, camera pans rigid), a label that
   held a slot last frame keeps it unless overlap grows past a margin a
   newcomer never gets (hysteresis), and every appearance or yield is a
   ~0.3s FADE. Labels self-clock so they keep easing while the sim is
   frozen and only the camera moves. */
let MAPTITLE = true;
let labClock = 0;
function drawLabels() {
  const now = performance.now();
  const ldt = labClock ? Math.min(0.1, (now - labClock) / 1000) : 0.016;
  labClock = now;
  const ke = 1 - Math.exp(-ldt / 0.15);   // anchor easing (~0.15s)
  const kf = ldt / 0.3;                   // fade step (~0.3s full swing)
  const vis = FW * S * Z;
  const la = vis <= 700 ? 0 : Math.min(1, (vis - 700) / 200);
  cx2d.textAlign = 'center';
  /* unit labels YIELD to the map's own lettering: names (and the title,
     when it is shown) are obstacles first, then units place
     biggest-first by AUTHORED size — a stable order can never swap two
     contending labels mid-scene. */
  const placed = [];
  const gu = S * Z;
  if (la > 0) {
    cx2d.font = `${9 * gu}px ui-monospace, Menlo, monospace`;
    for (const nm of TR.names || []) {
      const w = cx2d.measureText(nm.t).width;
      const nx = vx(nm.x), ny = vy(nm.y);
      const x0 = nm.align === 'left' ? nx : nm.align === 'right' ? nx - w : nx - w / 2;
      placed.push({ x: x0, y: ny - 9 * gu, w, h: 11 * gu });
    }
    if (TR.title && MAPTITLE) {
      cx2d.letterSpacing = `${5 * gu}px`;
      cx2d.font = `${30 * gu}px 'Iowan Old Style', 'Palatino Linotype', Palatino, Georgia, serif`;
      const tw = cx2d.measureText(TR.title.name.toUpperCase()).width;
      cx2d.letterSpacing = '0px';
      placed.push({ x: vx(TR.title.x) - tw / 2, y: vy(TR.title.y) - 26 * gu,
                    w: tw, h: (TR.title.sub ? 60 : 32) * gu });
    }
  }
  cx2d.font = `${Math.max(8, 9.5 * Math.max(0.8, S))}px ui-monospace, Menlo, monospace`;
  const cand = [];
  for (const u of B.units) {
    const st = u._lab || (u._lab = { fx: 0, fy: 0, live: false, on: 0, row: 0 });
    let n = 0, mx = 0, minY = 1e9;
    for (const e of u.ents) { if (e.alive) { n++; mx += e.x; minY = Math.min(minY, e.y); } }
    let want = la > 0 && n / u.n >= 0.08;
    if (want) {
      mx /= n;
      if (!st.live) { st.fx = mx; st.fy = minY; st.live = true; }
      st.fx += (mx - st.fx) * ke;         // the label says where the unit IS,
      st.fy += (minY - st.fy) * ke;       // not where its motes vibrate
      if (st.fx < 30 || st.fx > FW - 30) want = false;
    } else st.live = false;
    if (want) {
      const px = vx(st.fx), py = vy(st.fy) - 12;
      if (px < 40 || px > SW - 40 || py < 40 || py > SH - 20) want = false;
      else cand.push({ u, st, px, py });
    }
    if (!want) st.on = Math.max(0, st.on - kf);
  }
  cand.sort((a, b) => b.u.n - a.u.n);
  for (const c of cand) {
    const st = c.st;
    const wpx = cx2d.measureText(c.u.label).width;
    const rx = c.px - wpx / 2 - 4, rw = wpx + 8, rh = 12;
    /* an incumbent tests with a shrunken rect: it takes clearly-grown
       overlap to evict what the eye is already reading */
    const held = st.on > 0.5;
    const m = held ? 3.5 : -1;
    let ry = -1;
    const rows = held ? [st.row, 0, 1, 2] : [0, 1, 2];
    for (const k of rows) {
      const ty = c.py - 9 - 14 * k;
      if (ty < 12) continue;
      if (!placed.some((p) => rx + m < p.x + p.w && p.x < rx + rw - m
                           && ty + m < p.y + p.h && p.y < ty + rh - m)) {
        ry = ty; st.row = k; break;
      }
    }
    if (ry < 0) { st.on = Math.max(0, st.on - kf); continue; }
    st.on = Math.min(1, st.on + kf);
    placed.push({ x: rx, y: ry, w: rw, h: rh });
    st.dw = rw;
  }
  /* draw pass — position derives from the eased FIELD anchor every
     frame, so even a label mid-fade-out stays glued to the country
     while the camera pans. Yielded labels no longer hold a slot; they
     just finish their exit. */
  for (const u of B.units) {
    const st = u._lab;
    if (!st || st.on <= 0.01 || st.dw === undefined) continue;
    const a = st.on * la;
    if (a <= 0.01) continue;
    const px = vx(st.fx);
    const ry = vy(st.fy) - 21 - 14 * st.row;
    cx2d.fillStyle = `rgba(13,13,13,${0.55 * a})`;
    cx2d.fillRect(px - st.dw / 2, ry, st.dw, 12);
    cx2d.fillStyle = u.side === 'a' ? `rgba(134,182,239,${0.62 * a})` : `rgba(232,135,90,${0.62 * a})`;
    cx2d.fillText(u.label, px, ry + 9);
  }
}

/* ---------------- HUD ---------------- */
const el = (id) => document.getElementById(id);
const fmt = (n) => n.toLocaleString('en-US');
let phaseIdx = -1;

/* the narration card starts as a one-line bar; + expands the full account */
let narrMin = true;
const narr = el('narration');
const ntog = document.createElement('button');
ntog.id = 'narrtoggle';
narr.appendChild(ntog);
function setNarr(min) {
  narrMin = min;
  narr.classList.toggle('min', min);
  ntog.textContent = min ? '+' : '−';
  ntog.setAttribute('aria-label', min ? 'Expand phase details' : 'Collapse phase details');
  ntog.setAttribute('aria-expanded', String(!min));
  phaseIdx = -1;                    // re-render the phase line in the new mode
}
setNarr(true);
ntog.addEventListener('click', (e) => { e.stopPropagation(); setNarr(!narrMin); });
narr.addEventListener('click', () => { if (narrMin) setNarr(false); });

function updateHUD() {
  let da = 0, db = 0;
  for (const u of B.units) {
    if (u.score === false) continue;   // e.g. aircraft: reported in the aftermath
    // sea battles count ships struck; land battles count men fallen
    const dead = u.ents.reduce((a, e) => a + (e.alive ? 0 : 1), 0);
    const loss = u.kind === 'ship' ? dead : dead * B.scale;
    if (u.side === 'a') da += loss; else db += loss;
  }
  el('fallenA').textContent = fmt(da);
  el('fallenB').textContent = fmt(db);
  el('tlfill').style.width = (T / T_END * 100) + '%';
  // no clock: the timeline position IS the time. The slot only ever shows
  // the transport state (»2×, «) so fast-forward and rewind stay legible.
  el('clock').textContent = dir < 0 ? `«${speed > 1 ? speed + '×' : ''}` : speed > 1 ? `»${speed}×` : '';
  el('timeline').setAttribute('aria-valuenow', Math.round(T));
  let pi = 0;
  for (let i = 0; i < B.phases.length; i++) if (T >= B.phases[i].t) pi = i;
  if (pi !== phaseIdx) {
    phaseIdx = pi;
    const p = B.phases[pi];
    /* the card is the NARRATION: body and cite only. The same text is
       the on-screen caption and the reel's voiceover script — phase
       identity lives on the timeline numerals, nowhere else. */
    el('phasebody').textContent = p.body;
    el('phasecite').textContent = p.cite;
    document.querySelectorAll('.ticklabel').forEach((L2, i2) => L2.classList.toggle('active', i2 === pi));
  }
  if (T >= T_END && !aftOpened) { aftOpened = true; setAft(false); }
}

/* the summary is docked under the scoreboard from the first second —
   minimized to its header bar, expandable at ANY time, and it opens
   itself once when the battle ends */
let aftOpened = false;
function setAft(min) {
  el('aftermath').classList.toggle('min', min);
  el('afttoggle').textContent = min ? '+' : '−';
}
el('aftermath').classList.add('show');
setAft(true);
el('aftermath').querySelector('.ahead').addEventListener('click', () => {
  setAft(!el('aftermath').classList.contains('min'));
});

const tl = el('timeline');
/* ticks carry ROMAN NUMERALS — the only place phase identity is shown.
   Word labels collided at video width and duplicated the narration. */
const ROMAN = ['I', 'II', 'III', 'IV', 'V', 'VI', 'VII', 'VIII', 'IX', 'X', 'XI', 'XII'];
B.phases.forEach((p, pi2) => {
  const tick = document.createElement('div');
  tick.className = 'tick'; tick.style.left = (p.t / T_END * 100) + '%';
  tl.appendChild(tick);
  const lab = document.createElement('div');
  lab.className = 'ticklabel'; lab.style.left = (p.t / T_END * 100) + '%';
  lab.textContent = ROMAN[pi2] || String(pi2 + 1);
  if (p.t === 0) lab.style.transform = 'none';
  tl.appendChild(lab);
});
/* The timeline is a momentum bar: the colour under the playhead says who
   was winning at that moment. Losses come straight from the schedules —
   deterministic, computed once at boot — as fractions of each side's
   scoreboard total, so a small navy bleeding hulls reads as loudly as a
   big army bleeding men. Neutral grey means no clear advantage yet. */
function paintMomentum() {
  const N = 72;
  const pa = hexToRgb(B.sides.a.pal[1]), pb = hexToRgb(B.sides.b.pal[1]);
  const nc = [106, 102, 94];
  const adv = [];
  let mx = 0;
  for (let s = 0; s <= N; s++) {
    const t = s / N * T_END;
    let la = 0, lb = 0;
    for (const u of B.units) {
      if (u.score === false) continue;
      const dead = Math.round(lossFrac(u, t) * u.n);
      const loss = u.kind === 'ship' ? dead : dead * B.scale;
      if (u.side === 'a') la += loss; else lb += loss;
    }
    const v = lb / B.sides.b.total - la / B.sides.a.total;   // >0: side A ahead
    adv.push(v); mx = Math.max(mx, Math.abs(v));
  }
  if (!mx) return;
  const stops = adv.map((v, s) => {
    const k = Math.abs(v) / mx, p = v > 0 ? pa : pb;
    const c = [0, 1, 2].map((i2) => Math.round(nc[i2] + (p[i2] - nc[i2]) * k));
    return `rgb(${c[0]},${c[1]},${c[2]}) ${(s / N * 100).toFixed(1)}%`;
  });
  const fill = el('tlfill');
  fill.style.backgroundImage = `linear-gradient(90deg, ${stops.join(',')})`;
  // the fill is clipped to the playhead, so the gradient must be sized to
  // the whole rail or the colours would compress as the battle plays
  const size = () => { fill.style.backgroundSize = tl.offsetWidth + 'px 100%'; };
  size(); addEventListener('resize', size);
}
paintMomentum();

/* colliding phase labels stagger onto a second row (measured, not guessed) */
function staggerTicks() {
  let end0 = -1e9, end1 = -1e9;
  for (const L of tl.querySelectorAll('.ticklabel')) {
    L.classList.remove('row2', 'hidelab');
    const w = L.offsetWidth;
    const start = L.style.transform === 'none' ? L.offsetLeft : L.offsetLeft - w / 2;
    if (start > end0 + 8) end0 = start + w;
    else if (start > end1 + 8) { L.classList.add('row2'); end1 = start + w; }
    else L.classList.add('hidelab');
  }
}
requestAnimationFrame(staggerTicks);
addEventListener('resize', staggerTicks);

function setT(t, snap) {
  frozen = false; settleT = 0; stillDirty = true;   // any scrub wakes the table
  const back = t < T - 0.5;
  T = clamp(t, 0, T_END);
  if (back) {
    fctx.clearRect(0, 0, FW, FH);
    groundDirty = true;
    DYING.length = 0;
    resurrect();
  }
  PROJ.length = 0;
  if (snap) snapAll();
  updateHUD();
}

function scrub(ev) {
  const r = tl.getBoundingClientRect();
  const x = (ev.touches ? ev.touches[0].clientX : ev.clientX) - r.left;
  setT(x / r.width * T_END, true);
}
let scrubbing = false;
tl.addEventListener('pointerdown', (e) => { scrubbing = true; tl.setPointerCapture(e.pointerId); scrub(e); });
tl.addEventListener('pointermove', (e) => { if (scrubbing) scrub(e); });
tl.addEventListener('pointerup', () => { scrubbing = false; });
tl.addEventListener('keydown', (e) => {
  if (e.key === 'ArrowRight') setT(B.phases.find((p) => p.t > T + 0.01)?.t ?? T_END, true);
  if (e.key === 'ArrowLeft') setT([...B.phases].reverse().find((p) => p.t < T - 0.5)?.t ?? 0, true);
});

const playbtn = el('playbtn');
function setPlaying(p) {
  if (p) { frozen = false; settleT = 0; stillDirty = true; }
  playing = p;
  playbtn.innerHTML = p ? '&#9646;&#9646;' : '&#9654;';
  if (p && T >= T_END) { dir = 1; mi = 0; speed = 1; setT(0, true); }
  updateHUD();
}
playbtn.addEventListener('click', () => setPlaying(!playing));
el('replaybtn').addEventListener('click', () => {
  dir = 1; mi = 0; speed = 1;
  aftOpened = false; setAft(true);
  setT(0, true); setPlaying(true);
});
// (the summary header itself is the toggle — see setAft above)
/* VCR transport: » steps forward speed 1-2-4×, « plays time backwards */
const MAGS = [1, 2, 4];
let dir = 1, mi = 0;
el('ffbtn').addEventListener('click', () => {
  if (dir < 0) { dir = 1; mi = 0; } else mi = (mi + 1) % MAGS.length;
  speed = MAGS[mi];
  if (!playing && T < T_END) setPlaying(true);
});
el('rwbtn').addEventListener('click', () => {
  if (dir > 0) {
    dir = -1; mi = 0;
    fctx.clearRect(0, 0, FW, FH);   // marks re-accumulate on the way forward
    groundDirty = true;
    DYING.length = 0;
    PROJ.length = 0;
  } else mi = (mi + 1) % MAGS.length;
  speed = MAGS[mi];
  if (!playing && T > 0) setPlaying(true);
});
const syncLabelBtn = () => el('labelbtn').classList.toggle('off', !showLabels);
el('labelbtn').addEventListener('click', () => { showLabels = !showLabels; syncLabelBtn(); });
addEventListener('keydown', (e) => {
  if (e.key === ' ' && e.target.tagName !== 'BUTTON') { e.preventDefault(); setPlaying(!playing); }
  if (e.key === 'l' || e.key === 'L') { showLabels = !showLabels; syncLabelBtn(); }
});

/* ---- command mode (battles with command:true, i.e. the lab): box-select
   motes and order them anywhere — they murmurate over, and when released
   they flow back to their place in history */
let cmdMode = false, selStart = null, selRect = null, selMoved = false;
const SEL = new Set();
const toField = (sx, sy) => [(sx - VX) / (S * Z), (sy - VY) / (S * Z)];
if (B.command) {
  const btn = document.createElement('button');
  btn.id = 'cmdbtn';
  btn.textContent = 'COMMAND';
  el('console').insertBefore(btn, el('labelbtn'));
  const setCmd = (on) => {
    cmdMode = on;
    btn.classList.toggle('on', on);
    if (!on) { for (const e2 of ents) e2.ord = null; SEL.clear(); }
  };
  btn.addEventListener('click', () => setCmd(!cmdMode));
  addEventListener('keydown', (e) => {
    if (e.key === 'c' || e.key === 'C') setCmd(!cmdMode);
    if (e.key === 'Escape') SEL.clear();
  });
}
function cmdSelect() {
  SEL.clear();
  const [fx0, fy0] = toField(Math.min(selStart.x, selRect.x), Math.min(selStart.y, selRect.y));
  const [fx1, fy1] = toField(Math.max(selStart.x, selRect.x), Math.max(selStart.y, selRect.y));
  for (const e of ents) {
    if (e.alive && e.x >= fx0 && e.x <= fx1 && e.y >= fy0 && e.y <= fy1) SEL.add(e);
  }
}
function cmdOrder(sx, sy) {
  const [fx, fy] = toField(sx, sy);
  let i = 0;
  for (const e of SEL) {
    if (!e.alive) continue;
    // golden-angle spiral packs them into an organic disc at the target
    const r = 3.4 * Math.sqrt(i), a = i * 2.39996;
    e.ord = { x: fx + r * Math.cos(a), y: fy + r * Math.sin(a) };
    i++;
  }
}

/* ---------------- pan & zoom: the table is always explorable ------- */
function zoomAt(mx, my, factor) {
  const nz = clamp(Z * factor, ZMIN, 8);
  if (nz === Z) return;
  const fx = (mx - VX) / (S * Z), fy = (my - VY) / (S * Z);
  Z = nz;
  VX = mx - fx * S * Z; VY = my - fy * S * Z;
  clampView(); kmbar();
}
cv.addEventListener('wheel', (e) => {
  e.preventDefault();
  zoomAt(e.clientX, e.clientY, Math.pow(1.0015, -e.deltaY));
}, { passive: false });
cv.addEventListener('dblclick', () => {
  Z = Z0;
  VX = (SW - FW * S * Z) / 2; VY = (SH - FH * S * Z) / 2;
  viewChanged(); kmbar();
});
const zin = el('zin'), zout = el('zout');
if (zin) zin.addEventListener('click', () => zoomAt(SW / 2, SH / 2, 1.5));
if (zout) zout.addEventListener('click', () => zoomAt(SW / 2, SH / 2, 1 / 1.5));

const ptrs = new Map();
let lastPinch = 0;
cv.addEventListener('pointerdown', (e) => {
  ptrs.set(e.pointerId, { x: e.clientX, y: e.clientY });
  cv.setPointerCapture(e.pointerId);
  cv.classList.add('dragging');
  if (cmdMode && ptrs.size === 1) {
    selStart = { x: e.clientX, y: e.clientY };
    selRect = { x: e.clientX, y: e.clientY };
    selMoved = false;
  }
});
cv.addEventListener('pointermove', (e) => {
  const p = ptrs.get(e.pointerId);
  if (!p) return;
  if (cmdMode && selStart && ptrs.size === 1) {
    selRect = { x: e.clientX, y: e.clientY };
    if (Math.hypot(e.clientX - selStart.x, e.clientY - selStart.y) > 5) selMoved = true;
    p.x = e.clientX; p.y = e.clientY;
    return;
  }
  if (ptrs.size === 1) {
    VX += e.clientX - p.x; VY += e.clientY - p.y;
    clampView();
  } else if (ptrs.size === 2) {
    const [a, b] = [...ptrs.values()];
    const d = Math.hypot(a.x - b.x, a.y - b.y);
    if (lastPinch > 0) zoomAt((a.x + b.x) / 2, (a.y + b.y) / 2, d / lastPinch);
    lastPinch = d;
  }
  p.x = e.clientX; p.y = e.clientY;
});
const endPtr = (e) => {
  if (cmdMode && selStart && ptrs.has(e.pointerId)) {
    if (selMoved) cmdSelect();
    else if (SEL.size) cmdOrder(e.clientX, e.clientY);
    selStart = null; selRect = null;
  }
  ptrs.delete(e.pointerId);
  if (ptrs.size < 2) lastPinch = 0;
  if (!ptrs.size) cv.classList.remove('dragging');
};
cv.addEventListener('pointerup', endPtr);
cv.addEventListener('pointercancel', endPtr);

/* ---------------- main loop ---------------- */
function frame(now) {
  const dt = Math.min(0.05, (now - lastFrame) / 1000 || 0.016);
  lastFrame = now;
  if (playing) {
    T += dt * speed * dir;
    if (dir > 0 && T >= T_END) { T = T_END; setPlaying(false); }
    if (dir < 0 && T <= 0) { T = 0; dir = 1; mi = 0; speed = 1; setPlaying(false); }
  }
  /* the table SETS at the end: motes come to rest over ~2 s, then the
     sim freezes — the ended battle is a monument, pannable and battery-
     idle, redrawn only when the view or a tile changes. Any scrub,
     rewind or replay wakes it. */
  const atEnd = dir > 0 && !playing && T >= T_END - 1e-6;
  if (!atEnd) { settleT = 0; if (frozen) { frozen = false; stillDirty = true; } }
  if (frozen) {
    if (groundDirty || stillDirty) {
      render(lastAlive, 0);
      renderProj(0);
      renderDying(0);
      if (GLR) GLR.endFrame();
      updateHUD();
      stillDirty = false;
    }
  } else {
    const alive = step(dt);
    lastAlive = alive;
    if (dir > 0) applyDeaths(); else resurrect();   // dead rise on the way back
    if (playing && dir > 0) spawnVolleys(dt);
    if (atEnd) {
      settleT += dt;
      const f = Math.pow(0.03, dt / 1.6);   // glide to a stop, never a halt
      for (const e of ents) { if (e.alive) { e.vx *= f; e.vy *= f; } }
      if (settleT > 2.2) { frozen = true; stillDirty = true; }
    }
    render(alive, dt);
    renderProj(dt);
    renderDying(dt);
    if (GLR) GLR.endFrame();
    updateHUD();
  }
  if (WK) {
    /* the Worker rasters at full CPU speed off-thread; this thread only
       PLANS — start jobs, pick what the worker does next */
    tendDetail();
    if (!wbuild && worldStale) startWorld();
    pumpWorker();
  } else {
    /* no worker: banded fallback, one time-slice a frame by priority —
       (1) margins someone can SEE, (2) a readable pass, (3) the world,
       (4) silent upgrades */
    const worldPending = wbuild || worldStale;
    if (worldPending && !groundCovers()) stepWorld();
    else if (build) stepDetail();
    else if (worldPending && detailFresh()) stepWorld();
    else { tendDetail(); if (!build && worldPending) stepWorld(); }
  }
  tendLoader();
  requestAnimationFrame(frame);
}

/* The scoreboard is numbers. Whatever an author writes into a muster note
   is removed before it can paint — the rule cannot be opted out of. Scale
   honesty still gets said, but the ENGINE says it, computed from the
   scale NUMBER and shown with the scale bar where it belongs. */
document.querySelectorAll('#muster .mnote, #muster p, #muster div:not(.mhead):not(.mrow)')
  .forEach((n) => n.remove());
/* the compass corner is an INSTRUMENT: the north arrow and the scale row,
   nothing verbal. Weather colour, author asides — whatever ships there is
   deleted before it can paint. */
document.querySelectorAll('#compass > div').forEach((d) => {
  if (d.id === 'scalerow') return;
  if (/^N\s*↑$/.test(d.textContent.trim())) return;
  d.remove();
});
/* the summary is NUMBERS: any .note prose dies here too */
document.querySelectorAll('#aftermath .note').forEach((n) => n.remove());
/* scale honesty lives in the summary, engine-said, from the number */
if (B.scale > 1) {
  const aft = el('aftermath');
  if (aft) {
    const d = document.createElement('div');
    d.id = 'moteratio';
    d.className = 'sources';
    d.textContent = `1 mote = ${B.scale} men`;
    aft.insertBefore(d, aft.querySelector('.sources'));
  }
}

/* anywhere that isn't the live site announces itself — and opens a window
   into the simulation so headless QA can measure the physics instead of
   squinting at screenshots */
if (location.hostname !== 'sandtable.thrain.ai') {
  const badge = document.createElement('div');
  badge.id = 'envbadge';
  badge.textContent = 'BENCH';
  document.body.appendChild(badge);
  window.__sandtable = {
    ents, units: B.units, KINDS, GLYPH, DOMAIN,
    get t() { return T; },
    get zoom() { return Z; },
    get view() { return { z: Z, vx: VX, vy: VY, s: S, zmin: ZMIN }; },
    get detail() { return detail && { z: detail.z, w: detail.pw, h: detail.ph }; },
    get building() { return build && { row: build.row, of: build.ph }; },
    get ground() {
      return { world: ground.w === WW, ws: ground.ws,
               rect: [ground.x0, ground.y0, ground.w, ground.h],
               wrect: [WX0, WY0, WW, WH],
               building: wbuild ? wbuild.row / wbuild.ph : null };
    },
    get volleyFire() { return VFIRED.slice(); },
    get gl() { return !!GLR; },
    play(t, spd) {
      speed = clamp(spd || 1, 0.25, 8);
      setT(clamp(t, 0, T_END), true); setPlaying(true);
    },
    /* the CAMERA: centre the view on FIELD coordinates at zoom z. Runs the
       same clamps as a user gesture, and only an actual change of view
       restarts the detail settle clock — so an exporter easing toward a
       hold can call this every frame without starving the sharp pass. */
    look(o) {
      const pz = Z, px = VX, py = VY;
      if (o && Number.isFinite(o.z)) Z = clamp(o.z, ZMIN, 8);
      const cx = o && Number.isFinite(o.x) ? o.x : (SW / 2 - px) / (S * pz);
      const cy = o && Number.isFinite(o.y) ? o.y : (SH / 2 - py) / (S * pz);
      VX = SW / 2 - cx * S * Z;
      VY = SH / 2 - cy * S * Z;
      clampBounds();
      if (Z !== pz || VX !== px || VY !== py) { viewChanged(); kmbar(); }
      return { z: Z, vx: VX, vy: VY, s: S, zmin: ZMIN };
    },
    get viewSettled() { return viewSettled(); },
    /* the film carries its own corner title, and its camera cannot pan
       back to read half an inscription — so the recorder may switch the
       MAP title off. Terrain names stay. Bench-only by construction:
       this hook does not exist on the live hostname, so the browser's
       inscription can never be turned off. */
    setMapTitle(on) { MAPTITLE = !!on; groundDirty = true; },
  };
}

addEventListener('resize', resize);
resize();
snapAll();
/* ?t=42 deep-links a timeline moment (QA, sharing, agent screenshots);
   ?z=0.5 sets the boot zoom — z=0.01 clamps to the floor, which is how a
   screenshot proves the world has no border */
const qp = new URLSearchParams(location.search);
/* WebGL is the DEFAULT renderer (flipped 27 Jul after the iPad verdict:
   "way smoother"). ?gl=0 forces the canvas path — the permanent
   fallback, pinned by the reel exporter for episode stability — and any
   failure to build the context lands there silently, so the table
   always draws, on every device ever made. */
if (qp.get('gl') !== '0') {
  try { GLR = mkGLRenderer(); } catch { GLR = null; }
}
const qz = parseFloat(qp.get('z') || '');
if (Number.isFinite(qz)) {
  Z = clamp(qz, ZMIN, 8);
  VX = (SW - FW * S * Z) / 2; VY = (SH - FH * S * Z) / 2;
  clampView();
}
const qt = parseFloat(qp.get('t') || '');
if (Number.isFinite(qt)) { setT(clamp(qt, 0, T_END), true); setPlaying(false); }
else if (reduceMotion) { setT(B.phases[1]?.t ?? 0, true); setPlaying(false); }
else setPlaying(true);
bootGround();       // rough terrain over exactly what this first view shows
viewMoved = -1e9;   // boot is not a gesture: the first detail pass starts on frame one
requestAnimationFrame(frame);
})();
