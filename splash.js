/* the demo reel: an infantry column marches through leaving footprints,
   cavalry overtakes on a four-hoof track, a fleet crosses trailing wakes,
   and a murmuration closes the loop — the engine's grammar, on repeat */
(() => {
'use strict';
const cv = document.getElementById('sky');
const ctx = cv.getContext('2d');
if (matchMedia('(prefers-reduced-motion: reduce)').matches) return;
let W = 0, H = 0, DPR = 1, trail = null, ttx = null;
function resize() {
  DPR = Math.min(2, window.devicePixelRatio || 1);
  W = window.innerWidth; H = window.innerHeight;
  cv.width = W * DPR; cv.height = H * DPR;
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  trail = document.createElement('canvas');
  trail.width = W * DPR; trail.height = H * DPR;
  ttx = trail.getContext('2d');
  ttx.setTransform(DPR, 0, 0, DPR, 0, 0);
}
resize();
addEventListener('resize', resize);
if (location.hostname !== 'sandtable.thrain.ai') {
  const badge = document.createElement('div');
  badge.textContent = 'BENCH';
  badge.style.cssText = 'position:fixed;z-index:9;top:10px;left:50%;transform:translateX(-50%);'
    + 'font-family:ui-monospace,Menlo,monospace;font-size:9px;letter-spacing:0.3em;'
    + 'color:#e8875a;border:1px solid rgba(232,135,90,0.4);padding:3px 8px 3px 10px;pointer-events:none;';
  document.body.appendChild(badge);
}
const BLUES = ['#256abf', '#3987e5', '#5598e7', '#86b6ef'];
const RUSTS = ['#C14E24', '#d96a3a', '#e8875a'];
const hexToRgb = (c) => [1, 3, 5].map((i) => parseInt(c.slice(i, i + 2), 16));
const rgba = (c, a) => `rgba(${c[0]},${c[1]},${c[2]},${a})`;
const clampN = (v, a, b) => v < a ? a : v > b ? b : v;

const LOOP = 32, M = 280;
const af = clampN((innerWidth * innerHeight) / (1440 * 800), 0.35, 1);

function formation(o) {
  const motes = [];
  const rows = Math.ceil(o.n / o.cols);
  for (let i = 0; i < o.n; i++) {
    const col = i % o.cols, row = (i / o.cols) | 0;
    motes.push({
      row,
      // quincunx stagger: each rank offsets half a file, like a real column
      dx: (row - rows / 2) * o.gapX * -o.dir + (Math.random() - 0.5) * 2,
      dy: (col - o.cols / 2) * o.gapY + ((row % 2) - 0.5) * o.gapY * 0.5 + (Math.random() - 0.5) * 2,
      ph: Math.random() * 6.283,
      x: 0, y: 0, vx: 0, vy: 0, hx: o.dir, hy: 0,
      trav: 0, foot: i % 2 ? 1 : -1,
      c: hexToRgb(o.pal[i % o.pal.length]),
    });
  }
  return Object.assign({ motes, parked: false }, o);
}
const troupes = [
  formation({ kind: 'inf', n: Math.round(306 * af), cols: 18, gapX: 8.5, gapY: 8.5,
    pal: BLUES, lane: 0.36, dir: 1, t0: 0, t1: 22, maxV: 150, stride: 6.5 }),
  formation({ kind: 'cav', n: Math.round(96 * af), cols: 8, gapX: 12, gapY: 11,
    pal: RUSTS, lane: 0.52, dir: 1, t0: 4, t1: 12, maxV: 340, stride: 9 }),
  formation({ kind: 'cav', n: Math.round(72 * af), cols: 6, gapX: 12, gapY: 11,
    pal: BLUES, lane: 0.14, dir: -1, t0: 14, t1: 22, maxV: 340, stride: 9 }),
  formation({ kind: 'ship', n: 7, cols: 1, gapX: 95, gapY: 0,
    pal: RUSTS, lane: 0.74, dir: -1, t0: 8, t1: 28, maxV: 110 }),
];
const FN = Math.round(210 * af);
const flock = {
  t0: 19, t1: 31.5, parked: false,
  motes: Array.from({ length: FN }, (_, i) => ({
    x: 0, y: 0, vx: 0, vy: 0, n: 0,
    c: hexToRgb(i % 9 === 0 ? RUSTS[i % 3] : BLUES[i % 4]),
  })),
};

let T = 0, last = 0;
const anchorX = (t) => {
  const p = clampN((T - t.t0) / (t.t1 - t.t0), 0, 1);
  return t.dir > 0 ? -M + p * (W + 2 * M) : W + M - p * (W + 2 * M);
};

function stepTroupe(t, dt) {
  const active = T >= t.t0 - 0.5 && T <= t.t1 + 0.5;
  const ax = anchorX(t), ay = t.lane * H;
  if (!active) {
    if (!t.parked) {
      t.parked = true;
      for (const m of t.motes) {
        m.x = ax + m.dx; m.y = ay + m.dy;
        m.vx = 0; m.vy = 0; m.hx = t.dir; m.hy = 0;
      }
    }
    return;
  }
  t.parked = false;
  // a bob at walking cadence and a slow surge rippling through the ranks
  // keep grains reading as individual men, not rails
  const bobA = t.kind === 'cav' ? 1.6 : 1.0;
  const cad = t.kind === 'cav' ? 7 : 4.5;
  for (const m of t.motes) {
    const mtx = ax + m.dx + Math.sin(T * 2.6 + m.row * 0.55 + m.ph * 0.3) * 1.7;
    const mty = ay + m.dy + Math.sin(T * cad + m.ph) * bobA;
    const fx2 = (mtx - m.x) * 3.4 - m.vx * 2.8;
    const fy2 = (mty - m.y) * 3.4 - m.vy * 2.8;
    m.vx += fx2 * dt; m.vy += fy2 * dt;
    const sp = Math.hypot(m.vx, m.vy);
    if (sp > t.maxV) { m.vx = m.vx / sp * t.maxV; m.vy = m.vy / sp * t.maxV; }
    m.x += m.vx * dt; m.y += m.vy * dt;
    if (sp > 4) {
      const a = Math.min(1, dt * 6);
      m.hx += (m.vx / sp - m.hx) * a; m.hy += (m.vy / sp - m.hy) * a;
      const hl = Math.hypot(m.hx, m.hy) || 1;
      m.hx /= hl; m.hy /= hl;
    }
    if (m.x < -M - 60 || m.x > W + M + 60) continue;
    if (t.kind === 'ship') {
      ttx.strokeStyle = rgba(m.c, 0.8);
      ttx.lineWidth = 4.5; ttx.lineCap = 'round';
      ttx.beginPath();
      ttx.moveTo(m.x - m.hx * 11, m.y - m.hy * 11);
      ttx.lineTo(m.x + m.hx * 6, m.y + m.hy * 6);
      ttx.stroke();
      ttx.fillStyle = rgba(m.c, 0.95);
      ttx.beginPath(); ttx.arc(m.x + m.hx * 6, m.y + m.hy * 6, 1.7, 0, 6.2832); ttx.fill();
      continue;
    }
    // ground signature: two feet or four hooves, by distance marched
    m.trav += sp * dt;
    if (m.trav > t.stride) {
      m.trav %= t.stride;
      const px = -m.hy, py = m.hx;
      ttx.fillStyle = rgba(m.c, 0.12);
      if (t.kind === 'cav') {
        ttx.fillRect(m.x + px * 1.4 - 0.6, m.y + py * 1.4 - 0.6, 1.2, 1.2);
        ttx.fillRect(m.x - px * 1.4 - 0.6, m.y - py * 1.4 - 0.6, 1.2, 1.2);
      } else {
        m.foot = -m.foot;
        ttx.fillRect(m.x + px * 1.1 * m.foot - 0.55, m.y + py * 1.1 * m.foot - 0.55, 1.1, 1.1);
      }
    }
    ttx.strokeStyle = rgba(m.c, 0.5);
    ttx.lineWidth = t.kind === 'cav' ? 1.5 : 1.15;
    ttx.lineCap = 'round';
    const len = 1.8 + Math.min(1, sp / (t.maxV * 0.5)) * 2.4;
    ttx.beginPath();
    ttx.moveTo(m.x - m.hx * len, m.y - m.hy * len);
    ttx.lineTo(m.x, m.y);
    ttx.stroke();
  }
}

function stepFlock(dt) {
  const active = T >= flock.t0 - 0.5 && T <= flock.t1 + 0.5;
  const p2 = clampN((T - flock.t0) / (flock.t1 - flock.t0), 0, 1);
  // glide in from the right, wheel about the upper field, slip out the top
  const gx = p2 < 0.85
    ? W * (0.58 + 0.2 * Math.cos(T * 0.6)) : W * 0.5;
  const gy = p2 < 0.85
    ? H * (0.3 + 0.14 * Math.sin(T * 0.8)) : -300;
  if (!active) {
    if (!flock.parked) {
      flock.parked = true;
      for (const b of flock.motes) {
        b.x = W + 400 + Math.random() * 200; b.y = -100 + Math.random() * 300;
        b.vx = -60; b.vy = 20;
      }
    }
    return;
  }
  flock.parked = false;
  const R = Math.min(W, H) * 0.11, R2 = R * R;
  const maxV = Math.min(W, H) * 0.13;
  for (const b of flock.motes) {
    let cx2 = 0, cy2 = 0, ax2 = 0, ay2 = 0, sx = 0, sy = 0, n = 0;
    for (const q of flock.motes) {
      if (q === b) continue;
      const dx = q.x - b.x, dy = q.y - b.y, d2 = dx * dx + dy * dy;
      if (d2 > R2) continue;
      n++; cx2 += q.x; cy2 += q.y; ax2 += q.vx; ay2 += q.vy;
      if (d2 < 120 && d2 > 1e-4) { const inv = 1 / Math.sqrt(d2); sx -= dx * inv; sy -= dy * inv; }
    }
    b.n = n;
    let fx2 = 0, fy2 = 0;
    if (n) {
      fx2 += (cx2 / n - b.x) * 0.7 + (ax2 / n - b.vx) * 1.1;
      fy2 += (cy2 / n - b.y) * 0.7 + (ay2 / n - b.vy) * 1.1;
    }
    fx2 += sx * 26 + (gx - b.x) * 0.5 - b.vx * 0.4;
    fy2 += sy * 26 + (gy - b.y) * 0.5 - b.vy * 0.4;
    b.vx += fx2 * dt; b.vy += fy2 * dt;
    const sp = Math.hypot(b.vx, b.vy) || 1e-6;
    const cl = Math.max(maxV * 0.5, Math.min(maxV, sp));
    b.vx = b.vx / sp * cl; b.vy = b.vy / sp * cl;
    b.x += b.vx * dt; b.y += b.vy * dt;
    if (b.x < -60 || b.x > W + 60 || b.y < -60 || b.y > H + 60) continue;
    const dens = Math.min(1, b.n / 14);
    ttx.strokeStyle = rgba(b.c, 0.13 + 0.4 * dens);
    ttx.lineWidth = 1 + dens * 0.8;
    const ux = b.vx / sp, uy = b.vy / sp, len = 2.2 + dens * 3;
    ttx.beginPath();
    ttx.moveTo(b.x - ux * len, b.y - uy * len);
    ttx.lineTo(b.x, b.y);
    ttx.stroke();
  }
}


function frame(now) {
  const dt = Math.min(0.05, (now - last) / 1000 || 0.016);
  last = now;
  T = (T + dt) % LOOP;
  ttx.globalCompositeOperation = 'destination-out';
  ttx.fillStyle = 'rgba(0,0,0,0.17)';
  ttx.fillRect(0, 0, W, H);
  ttx.globalCompositeOperation = 'source-over';
  for (const t of troupes) stepTroupe(t, dt);
  stepFlock(dt);
  ctx.fillStyle = '#0d0d0d';
  ctx.fillRect(0, 0, W, H);
  ctx.drawImage(trail, 0, 0, W, H);
  requestAnimationFrame(frame);
}
requestAnimationFrame(frame);
})();

/* ---- catalog search: filter the shelf by name, era, place or army ---- */
(() => {
'use strict';
const input = document.getElementById('search');
if (!input) return;
/* the catalog never disagrees with itself: the count and the next
   battle's numeral are DERIVED from the shelf, not typed (the header
   once said 8 while 9 stood below it) */
const liveN = document.querySelectorAll('a.battle').length;
const cnt = document.getElementById('count');
if (cnt) cnt.textContent = liveN;
const soonNo = document.getElementById('soonno');
if (soonNo) soonNo.innerHTML = `N&ordm;${liveN + 1}`;

const cards = [...document.querySelectorAll('.battle')];
const none = document.getElementById('noresult');
const count = document.getElementById('count');
const hay = (c) => (c.textContent + ' ' + (c.dataset.tags || '')).toLowerCase();
input.addEventListener('input', () => {
  const q = input.value.trim().toLowerCase();
  let shown = 0, live = 0;
  for (const c of cards) {
    const hit = !q || hay(c).includes(q);
    c.classList.toggle('hide', !hit);
    if (hit) { shown++; if (!c.classList.contains('soon')) live++; }
  }
  none.classList.toggle('show', shown === 0);
  count.textContent = q ? live : cards.filter((c) => !c.classList.contains('soon')).length;
});
})();
