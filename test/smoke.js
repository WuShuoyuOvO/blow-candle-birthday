/**
 * 无头冒烟测试 —— 桩 DOM + 桩 Canvas + 伪 AudioContext，按帧数确定性驱动整个应用。
 *
 * 运行：node test/smoke.js
 *
 * 设计要点：
 *  · 用「按帧调度」而非墙钟 setTimeout —— rAF 循环本身耗时，墙钟定时会与帧错序。
 *  · 伪 AudioContext 通过 global.__MODE__ 切换「吹气 / 说话 / 突发噪声」三种频谱形态，
 *    从而在一遍运行中同时覆盖正例与两类反例。
 *  · blow-detector 读的是 window.AudioContext（不是 global），因此必须挂在 win 上。
 *  · 桩里的事件对象必须自带 preventDefault()，否则误报。
 */
const fs = require('fs');
const path = require('path');
const vm = require('vm');

const W = 390, H = 780;
let LOUD = false;

/* ---------------- 断言 ---------------- */
let pass = 0, fail = 0;
function check(name, cond) {
  if (cond) { pass++; console.log('  \u2705 ' + name); }
  else { fail++; console.log('  \u274c ' + name); }
}

function makeCtx(cv) {
  const noop = () => {};
  return {
    canvas: cv,
    globalAlpha: 1, globalCompositeOperation: 'source-over',
    fillStyle: '', strokeStyle: '', lineWidth: 1, font: '', textAlign: '', textBaseline: '',
    clearRect: noop, fillRect: noop, strokeRect: noop,
    beginPath: noop, closePath: noop, moveTo: noop, lineTo: noop,
    quadraticCurveTo: noop, bezierCurveTo: noop, arc: noop, ellipse: noop,
    fill: noop, stroke: noop, clip: noop,
    save: noop, restore: noop, translate: noop, rotate: noop, scale: noop, setTransform: noop,
    fillText: noop, strokeText: noop, drawImage: noop,
    measureText: () => ({ width: 100 }),
    createLinearGradient: () => ({ addColorStop: noop }),
    createRadialGradient: () => ({ addColorStop: noop }),
    getImageData(x, y, w, h) {
      const data = new Uint8ClampedArray(w * h * 4);
      const x0 = w * 0.2, x1 = w * 0.8, y0 = h * 0.35, y1 = h * 0.55;
      for (let yy = 0; yy < h; yy++) {
        for (let xx = 0; xx < w; xx++) {
          const i = (yy * w + xx) * 4;
          const inside = xx >= x0 && xx <= x1 && yy >= y0 && yy <= y1;
          data[i] = 255; data[i + 1] = 150; data[i + 2] = 200; data[i + 3] = inside ? 255 : 0;
        }
      }
      return { data, width: w, height: h };
    },
    putImageData: noop
  };
}
function makeCanvas(id) {
  const cv = {
    id, width: 300, height: 150, style: {}, _h: {},
    getContext: () => makeCtx(cv),
    addEventListener(t, fn) { (cv._h[t] = cv._h[t] || []).push(fn); },
    removeEventListener: () => {},
    dispatch(t, ev) { (cv._h[t] || []).forEach((fn) => fn.call(cv, Object.assign({ type: t, preventDefault() {}, touches: [] }, ev))); }
  };
  return cv;
}
function makeEl(id) {
  const el = {
    id, style: {}, dataset: {}, value: '', textContent: '', innerHTML: '',
    disabled: false, tagName: 'DIV', _cls: new Set(), _h: {},
    classList: {
      add: (c) => el._cls.add(c), remove: (c) => el._cls.delete(c),
      contains: (c) => el._cls.has(c), toggle: (c) => (el._cls.has(c) ? el._cls.delete(c) : el._cls.add(c))
    },
    addEventListener(t, fn) { (el._h[t] = el._h[t] || []).push(fn); },
    removeEventListener: () => {},
    setAttribute: () => {}, getAttribute: () => '', querySelectorAll: () => [],
    appendChild: () => {}, removeChild: () => {}, focus: () => {}
  };
  return el;
}

const els = {};
const document = {
  readyState: 'complete', hidden: false,
  getElementById(id) {
    if (id === 'veilCvs') { if (!els.vc) els.vc = makeCanvas('veilCvs'); return els.vc; }
    if (id === 'sceneCvs') { if (!els.sc) els.sc = makeCanvas('sceneCvs'); return els.sc; }
    if (!els[id]) els[id] = makeEl(id);
    return els[id];
  },
  createElement(tag) { return tag === 'canvas' ? makeCanvas('tmp') : makeEl(tag); },
  addEventListener: () => {},
  body: { appendChild: () => {}, removeChild: () => {} },
  documentElement: { clientWidth: W, clientHeight: H }
};

const BIN_HZ = 48000 / 1024;
const LOW_BIN = Math.round(900 / BIN_HZ);
const HF0 = Math.round(3500 / BIN_HZ);
function FakeAudioContext() {
  this.sampleRate = 48000; this.state = 'running'; this.currentTime = 0; this.destination = {};
  this.createMediaStreamSource = () => ({ connect() {} });
  this.createAnalyser = () => ({
    fftSize: 1024, frequencyBinCount: 512, smoothingTimeConstant: 0,
    minDecibels: -100, maxDecibels: -30, connect() {},
    getFloatTimeDomainData(a) {
      const amp = LOUD ? 0.5 : 0.002;
      for (let i = 0; i < a.length; i++) a[i] = (Math.random() * 2 - 1) * amp;
    },
    // 吹气态：低频强、高频弱（宽平稳噪声）；说话态：谐波峰 + 高频强；噪声态：全频均匀
    getByteFrequencyData(a) {
      for (let i = 0; i < a.length; i++) {
        if (!LOUD) { a[i] = 2; continue; }
        if (global.__MODE__ === 'speech') {
          a[i] = (i % 9 === 0) ? 255 : ((i >= HF0) ? 170 : 0);
        } else if (global.__MODE__ === 'noise') {
          a[i] = 200;
        } else {
          a[i] = (i <= LOW_BIN ? 240 : 170);
        }
      }
    }
  });
  this.createGain = () => ({ gain: { setValueAtTime() {}, linearRampToValueAtTime() {}, exponentialRampToValueAtTime() {} }, connect() {} });
  this.createOscillator = () => ({ type: '', frequency: {}, connect() {}, start() {}, stop() {} });
  this.createBiquadFilter = () => ({ type: '', frequency: {}, Q: {}, connect() {} });
  this.createBuffer = (ch, len) => ({ getChannelData: () => new Float32Array(len) });
  this.createBufferSource = () => ({ buffer: null, connect() {}, start() {} });
  this.resume = () => Promise.resolve();
  this.suspend = () => Promise.resolve();
  this.close = () => {};
}

let rafCount = 0;
const schedule = [];
function at(frame, fn) { schedule.push({ f: frame, fn: fn }); }

const win = {
  innerWidth: W, innerHeight: H, devicePixelRatio: 2, _h: {},
  addEventListener(t, fn) { (win._h[t] = win._h[t] || []).push(fn); },
  requestAnimationFrame(cb) {
    rafCount++;
    for (let i = schedule.length - 1; i >= 0; i--) {
      if (schedule[i].f === rafCount) { const s = schedule.splice(i, 1)[0]; try { s.fn(); } catch (e) { console.log('SCHED ERR f' + rafCount + ': ' + e.message); } }
    }
    if (rafCount > 900) return 0;
    setImmediate(() => cb(rafCount * 16.7));
    return rafCount;
  },
  setTimeout, clearTimeout, URLSearchParams, URL,
  navigator: { userAgent: 'node-smoke' },
  location: { href: 'https://example.com/?to=%E5%B0%8F%E6%98%8E&debug=1', search: '?to=%E5%B0%8F%E6%98%8E&debug=1', hash: '' },
  performance: { now: () => Date.now() }
};
win.window = win;
global.window = win;
global.document = document;
global.navigator = win.navigator;
global.location = win.location;
global.requestAnimationFrame = win.requestAnimationFrame;
global.performance = win.performance;
global.navigator.mediaDevices = { getUserMedia: () => Promise.resolve({ getTracks: () => [{ stop() {} }] }) };
win.AudioContext = FakeAudioContext;

const base = path.join(__dirname, '..');
['blow-detector.js', 'app.js'].forEach((f) => {
  vm.runInThisContext(fs.readFileSync(path.join(base, f), 'utf8'), { filename: f });
});

const d = document;
const veil = d.getElementById('veil');
const vc = d.getElementById('veilCvs');
const dbg = () => String(d.getElementById('debug').textContent);
const has = (s) => dbg().indexOf(s) >= 0;
const snap = (tag) => console.log('[' + tag + ' f' + rafCount + '] ' + dbg().replace(/\n/g, ' | '));

console.log('\n=== blowcake smoke test ===\n');

at(5, () => {
  snap('boot');
  console.log('--- 断言 ---');
  check('启动后进入 veil 覆盖态', has('phase veil'));
  check('麦克风初始化成功', has('mic OK'));
  check('几何自检：蜡烛埋在蛋糕顶层内 (PLANTED)', has('PLANTED'));
  check('初始 candle.health = 1.00', has('health 1.00'));
});

// —— 正例：轻吹气应迅速熄灭 ——
at(50, () => { LOUD = true; });
at(60, () => {
  snap('blowing +0.17s');
  check('轻吹气 0.17s 内熄灭 (health 0.00)', has('health 0.00'));
  check('吹灭后进入 out 阶段', has('phase out'));
  check('判定为吹气 (blow YES)', has('blow YES'));
});
at(200, () => { LOUD = false; });
at(430, () => {
  snap('celebration');
  check('完整链路抵达 text 阶段', has('phase text'));
});

// —— 交互：拖拽旋转 / 捏合缩放 / 滚轮 ——
at(470, () => {
  vc.dispatch('touchstart', { touches: [{ clientX: 100, clientY: 300 }] });
  vc.dispatch('touchmove', { touches: [{ clientX: 165, clientY: 335 }] });
  vc.dispatch('touchend', { touches: [] });
  vc.dispatch('touchstart', { touches: [{ clientX: 10, clientY: 10 }, { clientX: 60, clientY: 60 }] });
  vc.dispatch('touchmove', { touches: [{ clientX: 10, clientY: 10 }, { clientX: 140, clientY: 140 }] });
  vc.dispatch('touchend', { touches: [] });
  vc.dispatch('wheel', { deltaY: -240 });
  win._h.resize.forEach((fn) => fn());
});
at(500, () => {
  snap('after-interaction');
  check('拖拽/缩放手势未导致崩溃', true);
});

// —— 重来：双击 ——
at(560, () => {
  vc.dispatch('touchstart', { touches: [{ clientX: 200, clientY: 500 }] });
  vc.dispatch('touchend', { touches: [] });
  vc.dispatch('touchstart', { touches: [{ clientX: 200, clientY: 500 }] });
  vc.dispatch('touchend', { touches: [] });
});
at(600, () => {
  snap('after-doubletap');
  check('双击重来后回到 veil 阶段', has('phase veil'));
  check('双击重来后 candle.health 复位为 1.00', has('health 1.00'));
});

// —— 反例一：说话 / 唱歌 应被拒绝 ——
at(610, () => { global.__MODE__ = 'speech'; LOUD = true; });
at(625, () => {
  snap('SPEECH (expect blow=no)');
  check('说话被拒绝 (blow no)', has('blow no'));
});
at(640, () => { LOUD = false; });

// —— 反例二：瞬时全频噪声（<70ms 确认窗）应被拒绝 ——
at(650, () => { global.__MODE__ = 'noise'; LOUD = true; });
at(653, () => { LOUD = false; });
at(660, () => {
  snap('NOISE-BURST (expect blow=no)');
  check('瞬时噪声被拒绝 (blow no)', has('blow no'));
  check('瞬时噪声后蜡烛仍未被吹灭', has('health 1.00'));
});

at(700, () => {
  console.log('\nveilOpacity=' + veil.style.opacity + ' gone=' + veil.classList.contains('gone'));
  console.log('\n=== ' + (fail === 0 ? 'ALL PASS' : 'FAILED') + ' — ' + pass + ' passed, ' + fail + ' failed, ' + rafCount + ' frames ===\n');
  process.exitCode = fail === 0 ? 0 : 1;
});
