/**
 * 生日蛋糕吹蜡烛 · 零文案惊喜式互动（3D 粒子）
 *
 * · 覆盖层里是一整个生日蛋糕：三层糕体 + 糖霜 + 正中一支蜡烛，蜡烛底座嵌入顶层，不悬空
 * · 打开即进入全屏覆盖状态，无任何文字提示，靠火焰摇曳引导
 * · 火焰对麦克风气流量级做连续响应（未达阈值也摆动）；轻轻一口气即可吹灭
 * · 吹灭后保留完整的熄灭动画（火苗脱离飘散 + 闪光 + 烟雾消散），随后覆盖层淡出揭晓祝福
 */
(function () {
  'use strict';

  var veilEl = document.getElementById('veil');
  var vcv = document.getElementById('veilCvs');
  var scv = document.getElementById('sceneCvs');
  var vctx = vcv.getContext('2d', { alpha: false });
  var sctx = scv.getContext('2d', { alpha: false });
  function $(id) { return document.getElementById(id); }

  /* ============================================================
   * 一、世界常量：三层蛋糕 + 正中一支蜡烛
   * ========================================================== */
  var PLATE_R = 1.16, PLATE_Y = 0.00, PLATE_H = 0.07;
  var L1 = { r: 0.96, y0: 0.07, y1: 0.56 };
  var L2 = { r: 0.74, y0: 0.56, y1: 0.99 };
  var L3 = { r: 0.52, y0: 0.99, y1: 1.30 };
  // 蜡烛：底座嵌入顶层 0.06，保证不悬空、与蛋糕同轴
  var CANDLE_R = 0.075, CANDLE_Y0 = 1.24, CANDLE_Y1 = 2.02;
  var WICK_TOP = 2.09, FLAME_Y = 2.10;

  var DIST0 = 5.2, DIST_MIN = 3.0, DIST_MAX = 11;
  var WORLD_H = 2.62, WORLD_W = 2.42;
  var TEXT_W = 2.35, TEXT_CY = 1.32;
  var PW = 0.0135;
  var CAM_VEIL = { yaw: 0.30, pitch: 0.20, dist: 5.20, lookY: 1.05 };
  var CAM_GATHER = { yaw: 0.00, pitch: 0.14, dist: 5.20, lookY: 1.15 };

  var MODE_HOME = 0, MODE_FREE = 1, MODE_GATHER = 2;

  var PALETTE = [
    [255, 230, 241], [242, 168, 203],
    [255, 154, 196], [255, 134, 184], [255, 95, 156],
    [255, 192, 217], [255, 176, 205], [255, 136, 182],
    [255, 227, 239], [255, 208, 226], [255, 173, 210],
    [255, 244, 249], [255, 233, 243],
    [255, 247, 251], [255, 116, 171],
    [107, 66, 86], [255, 217, 234],
    [255, 243, 249], [255, 142, 194], [255, 61, 139], [255, 208, 230]
  ];
  var PAL = {
    plateTop: 0, plateSide: 1,
    l1a: 2, l1b: 3, l1c: 4,
    l2a: 5, l2b: 6, l2c: 7,
    l3a: 8, l3b: 9, l3c: 10,
    frost: 11, frost2: 12,
    cw: 13, cp: 14, wick: 15, pearl: 16,
    t0: 17, t1: 18, t2: 19, t3: 20
  };
  var SHADES = 8, NB = PALETTE.length * SHADES;
  var STYLE = new Array(NB);

  /* ============================================================
   * 二、运行时状态
   * ========================================================== */
  var W = 0, H = 0, DPR = 1, focal = 700, halfW = 0, halfH = 0;
  var quality = 1, downgrades = 0;
  var N = 0, home = null;                 // 共享的蛋糕点云（含蜡烛）
  var veilSet = null, sceneSet = null;
  var geo = { minY: 0, maxY: 0, candleN: 0, cakeR: 0, cakeTopY: 0, candleLowY: 0, candleTopY: 0 };

  var cam = { yaw: CAM_VEIL.yaw, pitch: CAM_VEIL.pitch, dist: CAM_VEIL.dist, lookY: CAM_VEIL.lookY,
              eye: [0, 0, 0], f: [0, 0, 0], r: [0, 0, 0], u: [0, 0, 0] };
  var camTween = 0, camT = { yaw: 0, pitch: 0, dist: 0, lookY: 0 };
  var drift = 1, idleT = 0;

  var candle = { out: false, health: 1 };
  // 熄灭耗时：确认窗 70ms + 排空时间。满强度 1/(2.2*4.8)=0.095s，最低强度
  // （strength 保底 0.7）1/(1.81*4.8)=0.115s → 从吹气到熄灭约 0.17~0.19s
  var DRAIN = 4.8;
  var phase = 'veil', phaseT = 0, veilAlpha = 1;
  var tSec = 0, brighten = 0, targetBrighten = 0;

  var breeze = 0, breezeAng = 0, gustT = 0, gustCd = 2.0;
  var wind = { power: 0, dx: 1, dz: 0 };

  var flame = [], smoke = [], ember = [], sparks = [];
  var emitAcc = 0, smokeAcc = 0, smokeFuel = 0, flash = 0;

  var bgScene = null, sprites = {};
  var det = null, micOK = false, micPending = false, holdToBlow = false, holdBlow = false, paused = false;
  var everSound = false;
  var lastT = 0, fpsAcc = 0, fpsN = 0;
  var DEBUG = /(\?|&)debug=1/.test(location.search);

  var params = new URLSearchParams(location.search);
  var toName = (params.get('to') || '').slice(0, 12).trim();
  var msgText = (params.get('msg') || '').slice(0, 16).trim();

  /* ============================================================
   * 三、工具
   * ========================================================== */
  function rnd(a, b) { return a + Math.random() * (b - a); }
  function clamp(v, a, b) { return v < a ? a : (v > b ? b : v); }

  function makeGlow(r, g, b, soft) {
    var c = document.createElement('canvas');
    c.width = c.height = 64;
    var g2 = c.getContext('2d');
    var grd = g2.createRadialGradient(32, 32, 0, 32, 32, 32);
    grd.addColorStop(0, 'rgba(' + r + ',' + g + ',' + b + ',1)');
    grd.addColorStop(soft ? 0.18 : 0.38, 'rgba(' + r + ',' + g + ',' + b + ',0.42)');
    grd.addColorStop(1, 'rgba(' + r + ',' + g + ',' + b + ',0)');
    g2.fillStyle = grd; g2.fillRect(0, 0, 64, 64);
    return c;
  }

  function buildStyles() {
    for (var c = 0; c < PALETTE.length; c++) {
      var p = PALETTE[c];
      for (var b = 0; b < SHADES; b++) {
        var lum = 0.26 + (b + 0.5) * (0.74 / SHADES);
        STYLE[c * SHADES + b] = 'rgb(' +
          Math.min(255, (p[0] * lum) | 0) + ',' +
          Math.min(255, (p[1] * lum) | 0) + ',' +
          Math.min(255, (p[2] * lum) | 0) + ')';
      }
    }
  }

  /* ============================================================
   * 四、粒子集合
   * ========================================================== */
  function makeSet(n) {
    return {
      n: n,
      px: new Float32Array(n), py: new Float32Array(n), pz: new Float32Array(n),
      vx: new Float32Array(n), vy: new Float32Array(n), vz: new Float32Array(n),
      tx: new Float32Array(n), ty: new Float32Array(n), tz: new Float32Array(n),
      pal: new Uint8Array(n), seed: new Float32Array(n), delay: new Float32Array(n),
      sx: new Float32Array(n), sy: new Float32Array(n), sz: new Float32Array(n),
      bucket: new Int32Array(n), vis: new Uint8Array(n),
      counts: new Int32Array(NB), offsets: new Int32Array(NB + 1), order: new Int32Array(n),
      ordA: new Array(n), ordB: new Array(n), keyA: new Float32Array(n), keyB: new Float32Array(n),
      mode: MODE_HOME, cull: true, brighten: 0,
      nx: null, ny: null, nz: null            // 与另一套共享（只读）
    };
  }

  function assignSet(S, pts, delayBase) {
    var n = S.n, i;
    for (i = 0; i < n; i++) {
      S.ordA[i] = i; S.ordB[i] = i;
      S.keyA[i] = Math.atan2(S.pz[i], S.px[i]);
      S.keyB[i] = Math.atan2(pts.z[i], pts.x[i]);
    }
    S.ordA.sort(function (a, b) { return S.keyA[a] - S.keyA[b]; });
    S.ordB.sort(function (a, b) { return S.keyB[a] - S.keyB[b]; });
    for (var k = 0; k < n; k++) {
      var p = S.ordA[k], q = S.ordB[k];
      S.tx[p] = pts.x[q]; S.ty[p] = pts.y[q]; S.tz[p] = pts.z[q];
      S.pal[p] = pts.pal[q];
      S.delay[p] = delayBase + (q / n) * 0.55 + Math.random() * 0.30;
    }
  }

  function simulateSet(S, dt) {
    var n = S.n, i;
    var k = Math.min(2, dt * 60);
    var spring = (S.mode === MODE_GATHER) ? 0.055 : 0.035;
    var damp = (S.mode === MODE_GATHER) ? 0.87 : 0.90;
    var breath = (S.mode === MODE_GATHER) ? 0.006 : 0.012;
    var t = tSec, dm = Math.pow(damp, k);
    for (i = 0; i < n; i++) {
      if (S.mode === MODE_FREE) {
        S.vy[i] += 0.010 * k;
        S.vx[i] += Math.sin(t * 1.4 + S.seed[i] * 9) * 0.006 * k;
        S.vz[i] += Math.cos(t * 1.2 + S.seed[i] * 7) * 0.006 * k;
        var dr = Math.pow(0.992, k);
        S.vx[i] *= dr; S.vy[i] *= dr; S.vz[i] *= dr;
      } else if (S.mode === MODE_GATHER && t < S.delay[i]) {
        S.vy[i] += 0.006 * k;
        S.vx[i] *= 0.99; S.vy[i] *= 0.99; S.vz[i] *= 0.99;
      } else {
        var s = S.seed[i] * 6.2832;
        var bx = Math.sin(t * 0.9 + s) * breath;
        var by = Math.cos(t * 1.2 + s * 1.7) * breath;
        var bz = Math.sin(t * 1.1 + s * 2.3) * breath;
        S.vx[i] += (S.tx[i] + bx - S.px[i]) * spring * k;
        S.vy[i] += (S.ty[i] + by - S.py[i]) * spring * k;
        S.vz[i] += (S.tz[i] + bz - S.pz[i]) * spring * k;
        S.vx[i] *= dm; S.vy[i] *= dm; S.vz[i] *= dm;
      }
      S.px[i] += S.vx[i] * k; S.py[i] += S.vy[i] * k; S.pz[i] += S.vz[i] * k;
    }
  }

  function projectSet(S) {
    var n = S.n, i;
    var ex = cam.eye[0], ey = cam.eye[1], ez = cam.eye[2];
    var fx = cam.f[0], fy = cam.f[1], fz = cam.f[2];
    var rx = cam.r[0], ry = cam.r[1], rz = cam.r[2];
    var ux = cam.u[0], uy = cam.u[1], uz = cam.u[2];
    var nxA = S.nx, nyA = S.ny, nzA = S.nz;

    var lx = -fx * 0.34 + ux * 0.72 + rx * 0.48;
    var ly = -fy * 0.34 + uy * 0.72 + ry * 0.48;
    var lz = -fz * 0.34 + uz * 0.72 + rz * 0.48;
    var ll = Math.sqrt(lx * lx + ly * ly + lz * lz) || 1;
    lx /= ll; ly /= ll; lz /= ll;

    var cull = S.cull, br = S.brighten, fogBase = cam.dist - 1.6;
    S.counts.fill(0);
    for (i = 0; i < n; i++) S.vis[i] = 0;

    for (i = 0; i < n; i++) {
      var dx = S.px[i] - ex, dy = S.py[i] - ey, dz = S.pz[i] - ez;
      var z = dx * fx + dy * fy + dz * fz;
      if (z < 0.25) continue;
      var anx = nxA[i], any = nyA[i], anz = nzA[i];
      if (cull && (anx * dx + any * dy + anz * dz) > 0) continue;
      var iz = focal / z;
      var sxp = halfW + (dx * rx + dy * ry + dz * rz) * iz;
      var syp = halfH - (dx * ux + dy * uy + dz * uz) * iz;
      if (sxp < -8 || sxp > W + 8 || syp < -8 || syp > H + 8) continue;

      var lum = 0.30 + 0.70 * Math.max(0, anx * lx + any * ly + anz * lz);
      var rimd = -(anx * fx + any * fy + anz * fz);
      if (rimd < 0) rimd = -rimd;
      var rim = 1 - rimd;
      lum += 0.26 * rim * rim * rim;
      lum *= 1 - 0.30 * clamp((z - fogBase) / 3.2, 0, 1);
      if (br > 0) lum = lum * (1 - br) + 1.0 * br;

      var b = ((lum - 0.26) / (0.74 / SHADES)) | 0;
      if (b < 0) b = 0; else if (b > SHADES - 1) b = SHADES - 1;

      var sz = PW * iz;
      if (sz < 1.0) sz = 1.0; else if (sz > 5) sz = 5;

      S.sx[i] = sxp; S.sy[i] = syp; S.sz[i] = sz;
      S.bucket[i] = S.pal[i] * SHADES + b;
      S.vis[i] = 1;
      S.counts[S.bucket[i]]++;
    }
    var acc = 0;
    for (i = 0; i < NB; i++) { S.offsets[i] = acc; acc += S.counts[i]; }
    S.offsets[NB] = acc;
    for (i = 0; i < NB; i++) S.counts[i] = S.offsets[i];
    for (i = 0; i < n; i++) if (S.vis[i]) S.order[S.counts[S.bucket[i]]++] = i;
  }

  function drawSet(S, c) {
    c.globalCompositeOperation = S.brighten > 0.4 ? 'lighter' : 'source-over';
    for (var b = 0; b < NB; b++) {
      var s0 = S.offsets[b], s1 = S.offsets[b + 1];
      if (s1 <= s0) continue;
      c.fillStyle = STYLE[b];
      var len = s1 - s0;
      var m = Math.max(1, Math.round(len * quality));
      var st = Math.max(1, len / m);
      for (var k = 0; k < len; k += st) {
        var i = S.order[s0 + (k | 0)];
        var s = S.sz[i];
        c.fillRect(S.sx[i], S.sy[i], s, s);
      }
    }
  }

  /* ============================================================
   * 五、完整生日蛋糕几何（三层糕体 + 正中一支蜡烛）
   * ========================================================== */
  function makeBirthdayCake(n) {
    var P = [], Nr = [], C = [];
    function push(x, y, z, a, b, c, pi) { P.push(x, y, z); Nr.push(a, b, c); C.push(pi); }
    var jobs = [];
    function job(w, f) { jobs.push({ w: w, f: f }); }

    // —— 盘子 ——
    job(1.05, function (k) {
      for (var i = 0; i < k; i++) {
        var a = Math.random() * 6.2832, r = Math.sqrt(Math.random()) * PLATE_R;
        push(Math.cos(a) * r, PLATE_Y + PLATE_H, Math.sin(a) * r, 0, 1, 0, PAL.plateTop);
      }
    });
    job(0.26, function (k) {
      for (var i = 0; i < k; i++) {
        var a = Math.random() * 6.2832, y = rnd(PLATE_Y, PLATE_Y + PLATE_H);
        var ca = Math.cos(a), sa = Math.sin(a);
        push(ca * PLATE_R, y, sa * PLATE_R, ca, 0, sa, PAL.plateSide);
      }
    });

    // —— 三层糕体 ——
    function layer(L, inner, pa, pb, pc, topPal) {
      job(0.64, function (k) {
        for (var i = 0; i < k; i++) {
          var a = Math.random() * 6.2832, y = rnd(L.y0, L.y1);
          var ca = Math.cos(a), sa = Math.sin(a);
          var t = (y - L.y0) / (L.y1 - L.y0);
          push(ca * L.r, y, sa * L.r, ca, 0, sa, t > 0.62 ? pa : (t > 0.3 ? pb : pc));
        }
      });
      job(0.32, function (k) {
        for (var i = 0; i < k; i++) {
          var a = Math.random() * 6.2832;
          var r2 = inner > 0
            ? Math.sqrt(rnd((inner / L.r) * (inner / L.r), 1)) * L.r
            : Math.sqrt(Math.random()) * L.r;
          push(Math.cos(a) * r2, L.y1, Math.sin(a) * r2, 0, 1, 0, topPal);
        }
      });
    }
    layer(L1, L2.r, PAL.l1a, PAL.l1b, PAL.l1c, PAL.frost2);
    layer(L2, L3.r, PAL.l2a, PAL.l2b, PAL.l2c, PAL.frost2);
    layer(L3, 0, PAL.l3a, PAL.l3b, PAL.l3c, PAL.frost2);

    // —— 糖霜圆管 / 滴落 / 糖珠 ——
    function torus(R, y, tube, pi) {
      return function (k) {
        for (var i = 0; i < k; i++) {
          var a = Math.random() * 6.2832, b = Math.random() * 6.2832;
          var rr = R + Math.cos(b) * tube * 0.55;
          var ca = Math.cos(a), sa = Math.sin(a), cb = Math.cos(b), sb = Math.sin(b);
          push(ca * rr, y + sb * tube, sa * rr, ca * cb, sb, sa * cb, pi);
        }
      };
    }
    job(0.58, torus(L1.r + 0.01, L1.y1 + 0.02, 0.085, PAL.frost));
    job(0.47, torus(L2.r + 0.01, L2.y1 + 0.02, 0.075, PAL.frost));
    job(0.38, torus(L3.r + 0.01, L3.y1 + 0.02, 0.065, PAL.frost));

    function drips(R, yTop, cnt) {
      return function (k) {
        for (var i = 0; i < k; i++) {
          var j = (Math.random() * cnt) | 0;
          var a = (j / cnt) * 6.2832 + rnd(-0.05, 0.05);
          var len = 0.10 + ((j * 37) % 11) / 11 * 0.30;
          var t = Math.random();
          var yy = yTop - 0.03 - t * len;
          var rad = 0.055 * (1 - t * 0.42), rr = R + 0.015;
          var u = Math.random() * 6.2832, v = Math.acos(2 * Math.random() - 1);
          var ox = Math.sin(v) * Math.cos(u), oy = Math.cos(v), oz = Math.sin(v) * Math.sin(u);
          push(Math.cos(a) * rr + ox * rad, yy + oy * rad, Math.sin(a) * rr + oz * rad,
            ox, oy, oz, t > 0.55 ? PAL.frost2 : PAL.frost);
        }
      };
    }
    job(0.50, drips(L1.r, L1.y1, 18));
    job(0.40, drips(L2.r, L2.y1, 14));
    job(0.32, drips(L3.r, L3.y1, 11));

    job(0.28, function (k) {
      var rings = [[L1.r * 0.86, L1.y1 + 0.075, 22], [L2.r * 0.84, L2.y1 + 0.07, 17], [L3.r * 0.8, L3.y1 + 0.06, 12]];
      for (var i = 0; i < k; i++) {
        var R = rings[(Math.random() * 3) | 0];
        var a = ((Math.random() * R[2]) | 0) / R[2] * 6.2832 + rnd(-0.05, 0.05);
        var rad = 0.036;
        var u = Math.random() * 6.2832, v = Math.acos(2 * Math.random() - 1);
        var ox = Math.sin(v) * Math.cos(u), oy = Math.cos(v), oz = Math.sin(v) * Math.sin(u);
        push(Math.cos(a) * R[0] + ox * rad, R[1] + oy * rad, Math.sin(a) * R[0] + oz * rad, ox, oy, oz, PAL.pearl);
      }
    });

    // —— 蜡烛：立在顶层正中，底部埋进糕体 0.06 ——
    job(0.80, function (k) {
      for (var i = 0; i < k; i++) {
        var a = Math.random() * 6.2832, y = rnd(CANDLE_Y1 - 0.62, CANDLE_Y1);
        var ca = Math.cos(a), sa = Math.sin(a);
        push(ca * CANDLE_R, y, sa * CANDLE_R, ca, 0, sa, ((y * 14) | 0) % 2 === 0 ? PAL.cw : PAL.cp);
      }
    });
    job(0.30, function (k) {
      for (var i = 0; i < k; i++) {
        var a = Math.random() * 6.2832, y = rnd(CANDLE_Y0, CANDLE_Y1 - 0.62);
        var ca = Math.cos(a), sa = Math.sin(a);
        push(ca * CANDLE_R, y, sa * CANDLE_R, ca, 0, sa, PAL.cw);
      }
    });
    job(0.14, function (k) {
      for (var i = 0; i < k; i++) {
        var a = Math.random() * 6.2832, r = Math.sqrt(Math.random()) * CANDLE_R;
        push(Math.cos(a) * r, CANDLE_Y1, Math.sin(a) * r, 0, 1, 0, PAL.cw);
      }
    });
    // 蜡烛根部的糖霜堆（视觉上把蜡烛"种"在蛋糕上）
    job(0.20, torus(0, L3.y1 + 0.015, 0.055, PAL.frost));
    // 蜡油
    job(0.26, function (k) {
      for (var i = 0; i < k; i++) {
        var j = (Math.random() * 7) | 0;
        var a = (j / 7) * 6.2832 + rnd(-0.08, 0.08);
        var len = 0.05 + ((j * 53) % 7) / 7 * 0.20;
        var t = Math.random();
        var yy = CANDLE_Y1 - 0.02 - t * len;
        var rad = 0.028 * (1 - t * 0.4), rr = CANDLE_R + 0.006;
        var u = Math.random() * 6.2832, v = Math.acos(2 * Math.random() - 1);
        var ox = Math.sin(v) * Math.cos(u), oy = Math.cos(v), oz = Math.sin(v) * Math.sin(u);
        push(Math.cos(a) * rr + ox * rad, yy + oy * rad, Math.sin(a) * rr + oz * rad, ox, oy, oz,
          t > 0.5 ? PAL.frost2 : PAL.frost);
      }
    });
    // 烛芯
    job(0.09, function (k) {
      for (var i = 0; i < k; i++) {
        var a = Math.random() * 6.2832, y = rnd(CANDLE_Y1 - 0.01, WICK_TOP);
        var ca = Math.cos(a), sa = Math.sin(a);
        push(ca * 0.013, y, sa * 0.013, ca, 0, sa, PAL.wick);
      }
    });

    var sum = 0, i;
    for (i = 0; i < jobs.length; i++) sum += jobs[i].w;
    for (i = 0; i < jobs.length; i++) jobs[i].f(Math.max(1, Math.round(n * jobs[i].w / sum)));

    var m = C.length;
    var x = new Float32Array(m), y = new Float32Array(m), z = new Float32Array(m);
    var nx = new Float32Array(m), ny = new Float32Array(m), nz = new Float32Array(m);
    for (i = 0; i < m; i++) {
      x[i] = P[i * 3]; y[i] = P[i * 3 + 1]; z[i] = P[i * 3 + 2];
      nx[i] = Nr[i * 3]; ny[i] = Nr[i * 3 + 1]; nz[i] = Nr[i * 3 + 2];
    }
    return { x: x, y: y, z: z, nx: nx, ny: ny, nz: nz, pal: new Uint8Array(C), n: m };
  }

  /* ============================================================
   * 六、文字点云
   * ========================================================== */
  var FONTS = '"PingFang SC","Hiragino Sans GB","Microsoft YaHei","Noto Sans CJK SC","Source Han Sans SC",sans-serif';

  function makeText(n) {
    var cv = document.createElement('canvas');
    cv.width = Math.max(1, Math.floor(W));
    cv.height = Math.max(1, Math.floor(H));
    var g = cv.getContext('2d');
    var line1 = '生日快乐', line2 = '';
    if (toName && msgText) line2 = toName + ' · ' + msgText;
    else if (toName) line2 = '祝 ' + toName;
    else if (msgText) line2 = msgText;

    var fs = Math.min(W * 0.86 / 4.15, H * 0.26);
    var fs2 = line2 ? fs * 0.30 : 0;
    var cy = H * 0.46;
    var y1 = line2 ? cy - fs * 0.28 : cy;
    var y2 = cy + fs * 0.58;

    g.textAlign = 'center'; g.textBaseline = 'middle';
    g.font = '900 ' + fs.toFixed(1) + 'px ' + FONTS;
    g.fillStyle = '#fff'; g.strokeStyle = '#fff';
    g.lineWidth = Math.max(1.5, fs * 0.022);
    g.fillText(line1, W / 2, y1); g.strokeText(line1, W / 2, y1);
    if (line2) {
      g.font = '700 ' + fs2.toFixed(1) + 'px ' + FONTS;
      g.fillText(line2, W / 2, y2); g.strokeText(line2, W / 2, y2);
    }

    var w = cv.width, h = cv.height;
    var d = g.getImageData(0, 0, w, h).data;
    var cxs = [], cys = [];
    for (var yy = 0; yy < h; yy++) {
      for (var xx = 0; xx < w; xx++) if (d[(yy * w + xx) * 4 + 3] > 110) { cxs.push(xx); cys.push(yy); }
    }
    var m = cxs.length;
    if (!m) { cxs.push(w / 2); cys.push(h / 2); m = 1; }

    var k = TEXT_W / Math.max(1, w * 0.86);
    var top = cy - fs * 0.72, bot = cy + fs * 0.72;
    var x = new Float32Array(n), y = new Float32Array(n), z = new Float32Array(n);
    var pl = new Uint8Array(n);
    for (var i = 0; i < n; i++) {
      var q = (Math.random() * m) | 0; if (q >= m) q = m - 1;
      x[i] = (cxs[q] + rnd(-0.5, 0.5) - w / 2) * k;
      y[i] = TEXT_CY - (cys[q] + rnd(-0.5, 0.5) - cy) * k;
      z[i] = 0;
      var t = clamp((cys[q] - top) / Math.max(1, bot - top), 0, 1);
      pl[i] = PAL.t0 + Math.min(3, (t * 4) | 0);
    }
    return { x: x, y: y, z: z, pal: pl, n: n };
  }

  /* ============================================================
   * 七、相机
   * ========================================================== */
  function updateCam() {
    var cp = Math.cos(cam.pitch), sp = Math.sin(cam.pitch);
    var cyw = Math.cos(cam.yaw), syw = Math.sin(cam.yaw);
    var e = cam.eye;
    e[0] = cam.dist * cp * syw;
    e[1] = cam.lookY + cam.dist * sp;
    e[2] = cam.dist * cp * cyw;
    var tx = -e[0], ty = cam.lookY - e[1], tz = -e[2];
    var L = Math.sqrt(tx * tx + ty * ty + tz * tz) || 1;
    cam.f[0] = tx / L; cam.f[1] = ty / L; cam.f[2] = tz / L;
    var rx = -cam.f[2], rz = cam.f[0];
    var rl = Math.sqrt(rx * rx + rz * rz) || 1;
    cam.r[0] = rx / rl; cam.r[1] = 0; cam.r[2] = rz / rl;
    cam.u[0] = cam.r[1] * cam.f[2] - cam.r[2] * cam.f[1];
    cam.u[1] = cam.r[2] * cam.f[0] - cam.r[0] * cam.f[2];
    cam.u[2] = cam.r[0] * cam.f[1] - cam.r[1] * cam.f[0];
  }
  function tweenCam(p) {
    camT.yaw = p.yaw; camT.pitch = p.pitch; camT.dist = p.dist; camT.lookY = p.lookY;
    camTween = 1;
  }

  /* ============================================================
   * 八、火焰 / 烟雾 / 火星 / 礼花
   * ========================================================== */
  function spawnFlame() {
    if (flame.length > 340) return;
    var a = Math.random() * 6.2832, r = Math.sqrt(Math.random()) * 0.030;
    flame.push({
      x: Math.cos(a) * r, y: FLAME_Y + rnd(-0.01, 0.03), z: Math.sin(a) * r,
      vx: Math.cos(a) * 0.14, vy: rnd(0.40, 0.68), vz: Math.sin(a) * 0.14,
      life: 0, max: rnd(0.40, 0.60), seed: Math.random(), det: 0
    });
  }
  function spawnSmoke(k) {
    for (var i = 0; i < k; i++) {
      if (smoke.length > 300) return;
      smoke.push({
        x: rnd(-0.016, 0.016), y: FLAME_Y + rnd(0, 0.10), z: rnd(-0.016, 0.016),
        vx: rnd(-0.07, 0.07) + wind.dx * wind.power * 0.30,
        vy: rnd(0.20, 0.40),
        vz: rnd(-0.07, 0.07) + wind.dz * wind.power * 0.30,
        life: 0, max: rnd(2.4, 4.2), seed: Math.random(), s0: rnd(0.075, 0.135)
      });
    }
  }
  function spawnEmber(x, y, z, hot) {
    if (ember.length > 160) return;
    var a = Math.random() * 6.2832, sp = rnd(0.3, 1.5);
    ember.push({
      x: x, y: y, z: z,
      vx: Math.cos(a) * sp + wind.dx * wind.power * 1.4,
      vy: rnd(0.5, 1.7),
      vz: Math.sin(a) * sp + wind.dz * wind.power * 1.4,
      life: 0, max: rnd(0.7, 1.6), s0: hot ? rnd(0.020, 0.036) : rnd(0.012, 0.024)
    });
  }
  function spawnSparks(k, cx, cy, cz, spd) {
    for (var i = 0; i < k; i++) {
      if (sparks.length > 420) return;
      var a = Math.random() * 6.2832, b = Math.acos(2 * Math.random() - 1);
      var s = spd * rnd(0.4, 1);
      sparks.push({
        x: cx, y: cy, z: cz,
        vx: Math.sin(b) * Math.cos(a) * s, vy: Math.cos(b) * s + 0.8, vz: Math.sin(b) * Math.sin(a) * s,
        life: 0, max: rnd(1.0, 2.2), s0: rnd(0.014, 0.030)
      });
    }
  }

  function updateFx(dt) {
    var i, p, u, s, tt = tSec;

    if (!candle.out) {
      emitAcc += 300 * dt;
      while (emitAcc >= 1) { emitAcc -= 1; spawnFlame(); }
    } else emitAcc = 0;

    var d = Math.exp(-2.6 * dt);
    for (i = flame.length - 1; i >= 0; i--) {
      p = flame[i];
      p.life += dt * (p.det ? 2.2 : 1);
      if (p.life >= p.max) { flame.splice(i, 1); continue; }
      u = p.life / p.max;
      if (!p.det) {
        p.vy += 1.95 * dt * (1 - u * 0.45);
        var pull = 5.5 * (1 - u);
        p.vx += -p.x * pull * dt;
        p.vz += -p.z * pull * dt;
        s = p.seed * 6.2832;
        p.vx += Math.sin(tt * 6.2 + s + p.y * 4.5) * 0.55 * dt;
        p.vz += Math.cos(tt * 5.4 + s * 1.7 + p.y * 3.6) * 0.55 * dt;
        // 摇曳引导：周期性起风 + 麦克风气流量级（阈下也会摆）
        p.vx += Math.cos(breezeAng) * breeze * 5.0 * dt;
        p.vz += Math.sin(breezeAng) * breeze * 5.0 * dt;
        p.vy += breeze * 0.5 * dt;
      } else {
        p.vy += 1.1 * dt;
        p.vx += Math.sin(tt * 4 + p.seed * 9) * 0.5 * dt;
        p.vz += Math.cos(tt * 4 + p.seed * 9) * 0.5 * dt;
      }
      p.vx *= d; p.vy *= d; p.vz *= d;
      p.x += p.vx * dt; p.y += p.vy * dt; p.z += p.vz * dt;
    }

    if (smokeFuel > 0) {
      smokeFuel -= dt / 2.6;
      smokeAcc += 34 * Math.max(0, smokeFuel) * dt;
      while (smokeAcc >= 1) { smokeAcc -= 1; spawnSmoke(1); }
    }
    for (i = smoke.length - 1; i >= 0; i--) {
      p = smoke[i];
      p.life += dt;
      if (p.life >= p.max) { smoke.splice(i, 1); continue; }
      u = p.life / p.max;
      p.vy += 0.34 * dt * (1 - u * 0.6);
      s = p.seed * 6.2832;
      var sw = 0.35 + u * 1.5;
      p.vx += Math.sin(tt * 1.5 + s + p.y * 2.2) * sw * dt;
      p.vz += Math.cos(tt * 1.3 + s * 1.4 + p.y * 1.9) * sw * dt;
      var dd = Math.exp(-0.85 * dt);
      p.vx *= dd; p.vy *= dd; p.vz *= dd;
      p.x += p.vx * dt; p.y += p.vy * dt; p.z += p.vz * dt;
    }

    for (i = ember.length - 1; i >= 0; i--) {
      p = ember[i];
      p.life += dt;
      if (p.life >= p.max) { ember.splice(i, 1); continue; }
      p.vy += (0.55 - 0.9 * (p.life / p.max)) * dt;
      var de = Math.exp(-1.5 * dt);
      p.vx *= de; p.vy *= de; p.vz *= de;
      p.x += p.vx * dt; p.y += p.vy * dt; p.z += p.vz * dt;
    }

    for (i = sparks.length - 1; i >= 0; i--) {
      p = sparks[i];
      p.life += dt;
      if (p.life >= p.max) { sparks.splice(i, 1); continue; }
      p.vy -= 1.4 * dt;
      var ds = Math.exp(-0.9 * dt);
      p.vx *= ds; p.vy *= ds; p.vz *= ds;
      p.x += p.vx * dt; p.y += p.vy * dt; p.z += p.vz * dt;
    }

    if (flash > 0) flash = Math.max(0, flash - dt * 2.6);
  }

  /* ============================================================
   * 九、熄灭 → 揭晓
   * ========================================================== */
  function extinguish() {
    candle.out = true;
    candle.health = 0;
    for (var i = 0; i < flame.length; i++) {
      var p = flame[i];
      p.det = 1;
      p.vy += 1.15;
      p.vx += Math.cos(breezeAng) * (0.5 + breeze) * 2.2 + rnd(-0.4, 0.4);
      p.vz += Math.sin(breezeAng) * (0.5 + breeze) * 2.2 + rnd(-0.4, 0.4);
    }
    for (var j = 0; j < 16; j++) spawnEmber(rnd(-0.02, 0.02), FLAME_Y + rnd(0, 0.08), rnd(-0.02, 0.02), false);
    spawnSmoke(34);
    smokeFuel = 1;
    flash = 1;
    puff();
    phase = 'out';
    phaseT = 0;
  }

  var T_OUT = 0.85, T_LIFT = 1.05, T_CAKE = 0.90, T_DISPERSE = 0.95, T_GATHER = 2.0;

  function startDisperse() {
    var S = sceneSet;
    S.mode = MODE_FREE;
    for (var i = 0; i < S.n; i++) {
      var dx = S.px[i], dy = S.py[i] - 1.0, dz = S.pz[i];
      var d = Math.sqrt(dx * dx + dy * dy + dz * dz) || 1;
      S.vx[i] = (dx / d) * rnd(1.6, 4.2) + rnd(-0.5, 0.5);
      S.vy[i] = (dy / d) * rnd(1.0, 3.0) + rnd(0.4, 1.9);
      S.vz[i] = (dz / d) * rnd(1.6, 4.2) + rnd(-0.5, 0.5);
    }
  }

  function startGather() {
    sceneSet.mode = MODE_GATHER;
    assignSet(sceneSet, makeText(sceneSet.n), tSec);
    targetBrighten = 1;
    tweenCam(CAM_GATHER);
    chimeSoft();
  }

  function phaseUpdate(dt) {
    phaseT += dt;
    if (phase === 'out' && phaseT > T_OUT) { phase = 'lift'; phaseT = 0; }
    else if (phase === 'lift' && phaseT > T_LIFT) { phase = 'cake'; phaseT = 0; veilEl.classList.add('gone'); }
    else if (phase === 'cake' && phaseT > T_CAKE) { phase = 'disperse'; phaseT = 0; startDisperse(); }
    else if (phase === 'disperse' && phaseT > T_DISPERSE) { phase = 'gather'; phaseT = 0; startGather(); }
    else if (phase === 'gather' && phaseT > T_GATHER) {
      phase = 'text'; phaseT = 0;
      spawnSparks(120, 0, TEXT_CY, 0, 2.2);
    } else if (phase === 'text') {
      if (Math.random() < dt * 0.75) spawnSparks(10, rnd(-1.4, 1.4), rnd(0.2, 2.0), rnd(-0.4, 0.4), 1.4);
    }
  }

  /* ============================================================
   * 十、重来（双击，无文字）
   * ========================================================== */
  function resetSet(S) {
    S.mode = MODE_HOME; S.cull = true;
    for (var i = 0; i < S.n; i++) {
      S.tx[i] = home.x[i]; S.ty[i] = home.y[i]; S.tz[i] = home.z[i];
      S.pal[i] = home.pal[i];
      S.vx[i] = 0; S.vy[i] = 0; S.vz[i] = 0;
      S.delay[i] = 0;
    }
  }
  function placeAtHome(S) {
    for (var i = 0; i < S.n; i++) { S.px[i] = home.x[i]; S.py[i] = home.y[i]; S.pz[i] = home.z[i]; }
  }
  function restart() {
    phase = 'veil'; phaseT = 0;
    veilAlpha = 1;
    veilEl.style.opacity = '1';
    veilEl.classList.remove('gone');
    candle.out = false; candle.health = 1;
    flame.length = 0; smoke.length = 0; ember.length = 0; sparks.length = 0;
    smokeFuel = 0; smokeAcc = 0; emitAcc = 0; flash = 0;
    resetSet(veilSet); resetSet(sceneSet);
    placeAtHome(veilSet); placeAtHome(sceneSet);
    sceneSet.brighten = 0; targetBrighten = 0; brighten = 0;
    tweenCam(CAM_VEIL);
  }

  /* ============================================================
   * 十一、背景与渲染
   * ========================================================== */
  function buildSceneBg() {
    bgScene = document.createElement('canvas');
    bgScene.width = Math.max(1, Math.floor(W * DPR));
    bgScene.height = Math.max(1, Math.floor(H * DPR));
    var g = bgScene.getContext('2d');
    g.setTransform(DPR, 0, 0, DPR, 0, 0);
    var grd = g.createLinearGradient(0, 0, 0, H);
    grd.addColorStop(0, '#26112f');
    grd.addColorStop(0.55, '#170b20');
    grd.addColorStop(1, '#0b040e');
    g.fillStyle = grd; g.fillRect(0, 0, W, H);
    for (var i = 0; i < 100; i++) {
      g.fillStyle = 'rgba(255,214,238,' + (Math.random() * 0.45 + 0.06).toFixed(3) + ')';
      g.beginPath(); g.arc(Math.random() * W, Math.random() * H, Math.random() * 1.2 + 0.3, 0, 6.2832); g.fill();
    }
    var rg = g.createRadialGradient(W / 2, H * 0.52, 0, W / 2, H * 0.52, Math.max(W, H) * 0.80);
    rg.addColorStop(0, 'rgba(148,28,88,0.55)');
    rg.addColorStop(1, 'rgba(0,0,0,0)');
    g.fillStyle = rg; g.fillRect(0, 0, W, H);
  }

  function drawVeilBg() {
    var g = vctx.createLinearGradient(0, 0, 0, H);
    g.addColorStop(0, '#180b1a');
    g.addColorStop(0.55, '#0b050d');
    g.addColorStop(1, '#060209');
    vctx.fillStyle = g;
    vctx.fillRect(0, 0, W, H);
  }

  var BB = [], bbN = 0, bbOrd = [], BC = null;
  function bbReset(c) { bbN = 0; BC = c; }
  function bbAdd(x, y, z, worldD, sp, a) {
    if (a <= 0.002) return;
    var dx = x - cam.eye[0], dy = y - cam.eye[1], dz = z - cam.eye[2];
    var zc = dx * cam.f[0] + dy * cam.f[1] + dz * cam.f[2];
    if (zc < 0.3) return;
    var iz = focal / zc;
    var o = BB[bbN];
    if (!o) { o = BB[bbN] = { z: 0, x: 0, y: 0, s: 0, a: 0, sp: null }; }
    o.z = zc;
    o.x = halfW + (dx * cam.r[0] + dy * cam.r[1] + dz * cam.r[2]) * iz;
    o.y = halfH - (dx * cam.u[0] + dy * cam.u[1] + dz * cam.u[2]) * iz;
    o.s = worldD * iz;
    o.a = a; o.sp = sp;
    bbN++;
  }
  function bbFlush() {
    if (!bbN || !BC) { bbN = 0; return; }
    bbOrd.length = bbN;
    for (var i = 0; i < bbN; i++) bbOrd[i] = i;
    bbOrd.sort(function (a, b) { return BB[b].z - BB[a].z; });
    for (var j = 0; j < bbN; j++) {
      var o = BB[bbOrd[j]];
      BC.globalAlpha = o.a;
      BC.drawImage(o.sp, o.x - o.s * 0.5, o.y - o.s * 0.5, o.s, o.s);
    }
    BC.globalAlpha = 1;
    bbN = 0;
  }

  function drawFlameAmbient() {
    if (candle.out && flash <= 0.01) return;
    var flick = 0.86 + 0.14 * Math.sin(tSec * 7) + 0.06 * Math.sin(tSec * 17);
    var a = 0.07 + 0.18 * flick * (1 - 0.4 * breeze) + flash * 0.16;
    var dx = -cam.eye[0], dy = FLAME_Y + 0.12 - cam.eye[1], dz = -cam.eye[2];
    var z = dx * cam.f[0] + dy * cam.f[1] + dz * cam.f[2];
    if (z < 0.3) return;
    var iz = focal / z;
    var gx = halfW + (dx * cam.r[0] + dy * cam.r[1] + dz * cam.r[2]) * iz;
    var gy = halfH - (dx * cam.u[0] + dy * cam.u[1] + dz * cam.u[2]) * iz;
    var r = Math.max(W, H) * 0.62;
    var grd = vctx.createRadialGradient(gx, gy, 0, gx, gy, r);
    grd.addColorStop(0, 'rgba(255,158,92,' + a.toFixed(3) + ')');
    grd.addColorStop(0.34, 'rgba(255,92,150,' + (a * 0.34).toFixed(3) + ')');
    grd.addColorStop(1, 'rgba(255,60,140,0)');
    vctx.globalCompositeOperation = 'lighter';
    vctx.fillStyle = grd;
    vctx.fillRect(0, 0, W, H);
  }

  function drawSmokePass() {
    if (!smoke.length) return;
    bbReset(vctx);
    for (var i = 0; i < smoke.length; i++) {
      var p = smoke[i], u = p.life / p.max;
      var sz = p.s0 * (0.55 + 3.0 * u);
      var a = (u < 0.14 ? u / 0.14 : 1) * Math.pow(1 - u, 1.4) * 0.16;
      bbAdd(p.x, p.y, p.z, sz * 2.2, sprites.smoke, a);
    }
    vctx.globalCompositeOperation = 'source-over';
    bbFlush();
  }

  function drawFlamePass() {
    bbReset(vctx);
    var i, p, u, a, sz;
    if (!candle.out || flash > 0.01) {
      var fl = 0.85 + 0.15 * Math.sin(tSec * 11) + 0.07 * Math.sin(tSec * 27);
      var glowA = (candle.out ? 0 : 0.34 * fl * (1 - 0.40 * breeze)) + flash * 0.6;
      var lean = breeze * 0.09;
      bbAdd(Math.cos(breezeAng) * lean, FLAME_Y + 0.10, Math.sin(breezeAng) * lean, 0.62, sprites.halo, glowA);
      if (!candle.out) bbAdd(0, FLAME_Y + 0.03, 0, 0.18, sprites.core, 0.6 * fl);
    }
    for (i = 0; i < flame.length; i++) {
      p = flame[i];
      u = p.life / p.max;
      sz = (0.050 + 0.115 * u) * 2.6;
      a = (u < 0.10 ? u / 0.10 : 1) * Math.pow(1 - u, 1.25) * 0.30;
      var ci = (u * 6) | 0; if (ci > 5) ci = 5;
      bbAdd(p.x, p.y, p.z, sz, sprites.flame[ci], a);
    }
    for (i = 0; i < ember.length; i++) {
      p = ember[i];
      u = p.life / p.max;
      bbAdd(p.x, p.y, p.z, p.s0 * 6.0, sprites.ember, (1 - u) * 0.85);
    }
    if (flash > 0.01) bbAdd(0, FLAME_Y + 0.05, 0, 0.45 + flash * 0.6, sprites.flash, flash * 0.5);
    vctx.globalCompositeOperation = 'lighter';
    bbFlush();
  }

  function drawSparkPass() {
    if (!sparks.length) return;
    bbReset(sctx);
    for (var i = 0; i < sparks.length; i++) {
      var p = sparks[i], u = p.life / p.max;
      bbAdd(p.x, p.y, p.z, p.s0 * 7.0, sprites.spark, (1 - u) * 0.9);
    }
    sctx.globalCompositeOperation = 'lighter';
    bbFlush();
  }

  /* ============================================================
   * 十二、音效
   * ========================================================== */
  function acx() {
    if (det && det.ctx) return det.ctx;
    var AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return null;
    try { return (acx._c = acx._c || new AC()); } catch (e) { return null; }
  }
  function puff() {
    var ac = acx(); if (!ac) return;
    var dur = 0.24, sr = ac.sampleRate;
    var buf = ac.createBuffer(1, Math.max(1, (sr * dur) | 0), sr);
    var d = buf.getChannelData(0);
    for (var i = 0; i < d.length; i++) d[i] = (Math.random() * 2 - 1) * (1 - i / d.length);
    var src = ac.createBufferSource(); src.buffer = buf;
    var bp = ac.createBiquadFilter(); bp.type = 'bandpass'; bp.frequency.value = 760; bp.Q.value = 0.8;
    var g = ac.createGain();
    g.gain.setValueAtTime(0.08, ac.currentTime);
    g.gain.exponentialRampToValueAtTime(0.0005, ac.currentTime + dur);
    src.connect(bp); bp.connect(g); g.connect(ac.destination);
    src.start();
  }
  function chimeSoft() {
    var ac = acx(); if (!ac) return;
    var notes = [523.25, 659.25, 783.99, 1046.5];
    for (var i = 0; i < notes.length; i++) {
      var o = ac.createOscillator(), g = ac.createGain();
      o.type = 'triangle'; o.frequency.value = notes[i];
      var t0 = ac.currentTime + i * 0.11;
      g.gain.setValueAtTime(0, t0);
      g.gain.linearRampToValueAtTime(0.07, t0 + 0.02);
      g.gain.exponentialRampToValueAtTime(0.0008, t0 + 0.8);
      o.connect(g); g.connect(ac.destination);
      o.start(t0); o.stop(t0 + 0.85);
    }
  }

  /* ============================================================
   * 十三、麦克风
   * ========================================================== */
  function bootMic() {
    det = new window.BlowDetector({ sensitivity: 2.2 });
    return det.start().then(function () {
      micOK = true; micPending = false;
      if (det.ctx && det.ctx.state === 'suspended') det.ctx.resume()['catch'](function () { });
      return true;
    });
  }
  function handleMicFail(err) {
    // 注意：Error 自带 name='Error'，必须优先读自定义 code
    var n = (err && (err.code || err.name)) || '';
    if (n === 'NO_GETUSERMEDIA' || n === 'NO_WEB_AUDIO') { holdToBlow = true; return; }
    armGestureMic();
  }
  function armGestureMic() {
    micPending = true;
    var once = function () {
      document.removeEventListener('touchend', once);
      document.removeEventListener('click', once);
      if (det && det.ctx && det.ctx.state === 'suspended') det.ctx.resume()['catch'](function () { });
      if (micOK) { micPending = false; return; }
      bootMic().then(function () { micPending = false; })['catch'](function () {
        micPending = false;
        holdToBlow = true;
      });
    };
    document.addEventListener('touchend', once);
    document.addEventListener('click', once);
  }

  /* ============================================================
   * 十四、交互
   * ========================================================== */
  var drag = { on: false, x: 0, y: 0, moved: 0, x0: 0, y0: 0, t0: 0 };
  var pinch = { on: false, d0: 0, dist0: 0 };
  var holdTimer = null, lastTapT = 0;

  function ptDown(x, y) {
    drag.on = true; drag.x = x; drag.y = y; drag.moved = 0;
    drag.x0 = x; drag.y0 = y; drag.t0 = tSec;
    camTween = 0; idleT = 0;
    if (holdToBlow) {
      clearTimeout(holdTimer);
      holdTimer = setTimeout(function () { if (drag.moved < 14) holdBlow = true; }, 340);
    }
  }
  function ptMove(x, y) {
    if (!drag.on) return;
    var dx = x - drag.x, dy = y - drag.y;
    drag.x = x; drag.y = y;
    drag.moved += Math.abs(dx) + Math.abs(dy);
    cam.yaw -= dx * 0.0080;
    cam.pitch = clamp(cam.pitch + dy * 0.0060, -0.60, 1.15);
    idleT = 0;
  }
  function ptUp() { drag.on = false; clearTimeout(holdTimer); holdBlow = false; }
  function onTap() {
    if (phase !== 'text') return;
    var moved = Math.abs(drag.x - drag.x0) + Math.abs(drag.y - drag.y0);
    var held = tSec - drag.t0;
    if (moved > 14 || held > 0.30) { lastTapT = 0; return; }
    var now = tSec;
    if (now - lastTapT < 0.40) { lastTapT = 0; restart(); }
    else lastTapT = now;
  }

  function bindControls(el) {
    el.addEventListener('mousedown', function (e) { ptDown(e.clientX, e.clientY); });
    el.addEventListener('touchstart', function (e) {
      if (e.touches.length === 1) ptDown(e.touches[0].clientX, e.touches[0].clientY);
      else if (e.touches.length === 2) {
        drag.on = false; clearTimeout(holdTimer); holdBlow = false; pinch.on = true;
        var a = e.touches[0], b = e.touches[1];
        pinch.d0 = Math.sqrt((a.clientX - b.clientX) * (a.clientX - b.clientX) + (a.clientY - b.clientY) * (a.clientY - b.clientY));
        pinch.dist0 = cam.dist;
      }
      e.preventDefault();
    }, { passive: false });
    el.addEventListener('touchmove', function (e) {
      if (pinch.on && e.touches.length === 2) {
        var a = e.touches[0], b = e.touches[1];
        var d = Math.sqrt((a.clientX - b.clientX) * (a.clientX - b.clientX) + (a.clientY - b.clientY) * (a.clientY - b.clientY));
        if (pinch.d0 > 4) cam.dist = clamp(pinch.dist0 * (pinch.d0 / Math.max(4, d)), DIST_MIN, DIST_MAX);
      } else if (drag.on && e.touches.length === 1) {
        ptMove(e.touches[0].clientX, e.touches[0].clientY);
      }
      e.preventDefault();
    }, { passive: false });
    el.addEventListener('touchend', function (e) {
      if (e.touches.length === 0) { pinch.on = false; ptUp(); onTap(); }
      else if (e.touches.length === 1) { pinch.on = false; ptDown(e.touches[0].clientX, e.touches[0].clientY); }
    });
    el.addEventListener('wheel', function (e) {
      e.preventDefault();
      cam.dist = clamp(cam.dist * Math.exp((e.deltaY || 0) * 0.0012), DIST_MIN, DIST_MAX);
      camTween = 0; idleT = 0;
    }, { passive: false });
  }

  /* ============================================================
   * 十五、主循环
   * ========================================================== */
  function frame(now) {
    if (!lastT) lastT = now;
    var dt = (now - lastT) / 1000;
    lastT = now;
    if (dt > 0.05) dt = 0.05;
    tSec += dt;

    var blow = false, strength = 0, air = 0;
    if (micOK && det && det.ready && !paused) {
      var r = det.update(dt);
      blow = r.blow; strength = r.strength; air = r.air;
      if (!everSound && det.peakEver() > 0.015) everSound = true;
    }
    if (holdBlow) { blow = true; strength = Math.max(strength, 0.95); air = 1; }

    // —— 摇曳引导 ——
    gustCd -= dt;
    if (gustCd <= 0) {
      gustCd = rnd(4.0, 7.0);
      gustT = 1;
      breezeAng = Math.random() * 6.2832;
    }
    if (gustT > 0) {
      gustT = Math.max(0, gustT - dt / 1.9);
      var g = Math.sin(Math.PI * clamp(1 - gustT, 0, 1));
      if (g > breeze) breeze += (g - breeze) * Math.min(1, dt * 6);
      else breeze += (g - breeze) * Math.min(1, dt * 3);
    }
    if (air > breeze) breeze += (air - breeze) * Math.min(1, dt * 9);
    else breeze += (air - breeze) * Math.min(1, dt * 3.2);
    wind.power = breeze;
    wind.dx = Math.cos(breezeAng); wind.dz = Math.sin(breezeAng);

    // 起风时溅出几粒火星，强化"有风"的视觉暗示
    if (!candle.out && breeze > 0.45 && Math.random() < dt * 6) {
      spawnEmber(rnd(-0.01, 0.01), FLAME_Y + 0.05, rnd(-0.01, 0.01), false);
    }

    // —— 吹灭判定 ——
    if (phase === 'veil' && !candle.out) {
      candle.health -= (0.9 + 1.3 * strength) * DRAIN * dt * (blow ? 1 : 0);
      if (blow && candle.health <= 0) extinguish();
    }

    phaseUpdate(dt);

    if (phase === 'lift') {
      var u = clamp(phaseT / T_LIFT, 0, 1);
      veilAlpha = 1 - u * u * (3 - 2 * u);
      veilEl.style.opacity = String(veilAlpha.toFixed(3));
    } else if (phase === 'cake' || phase === 'disperse' || phase === 'gather' || phase === 'text') {
      if (veilAlpha !== 0) { veilAlpha = 0; veilEl.style.opacity = '0'; }
    }

    brighten += (targetBrighten - brighten) * Math.min(1, dt * 2.6);
    sceneSet.brighten = brighten;

    veilSet.cull = (phase === 'veil' || phase === 'out' || phase === 'lift');
    sceneSet.cull = (phase === 'lift' || phase === 'cake');

    idleT += dt;
    var wantDrift = (!drag.on && idleT > 2.5) ? 1 : 0;
    drift += (wantDrift - drift) * Math.min(1, dt * 1.2);
    if (drift > 0.01) cam.yaw += Math.sin(tSec * 0.16) * 0.055 * drift * dt;

    if (camTween > 0) {
      camTween = Math.max(0, camTween - dt / 1.0);
      var e2 = Math.min(1, dt * 3.0);
      cam.yaw += (camT.yaw - cam.yaw) * e2;
      cam.pitch += (camT.pitch - cam.pitch) * e2;
      cam.dist += (camT.dist - cam.dist) * e2;
      cam.lookY += (camT.lookY - cam.lookY) * e2;
    }

    // —— 模拟：两层内容完全同源、同种子、同轨迹，淡出淡入无缝衔接 ——
    if (veilAlpha > 0.002) simulateSet(veilSet, dt);
    if (veilAlpha < 0.995) simulateSet(sceneSet, dt);
    updateFx(dt);
    updateCam();

    if (veilAlpha < 0.995) {
      sctx.setTransform(DPR, 0, 0, DPR, 0, 0);
      sctx.globalCompositeOperation = 'source-over';
      sctx.globalAlpha = 1;
      sctx.drawImage(bgScene, 0, 0, W, H);
      projectSet(sceneSet);
      drawSet(sceneSet, sctx);
      drawSparkPass();
      sctx.globalCompositeOperation = 'source-over';
    }

    if (veilAlpha > 0.002) {
      vctx.setTransform(DPR, 0, 0, DPR, 0, 0);
      vctx.globalCompositeOperation = 'source-over';
      vctx.globalAlpha = 1;
      drawVeilBg();
      drawFlameAmbient();
      projectSet(veilSet);
      drawSet(veilSet, vctx);
      drawSmokePass();
      drawFlamePass();
      vctx.globalCompositeOperation = 'source-over';
    }

    if (DEBUG) {
      var inf = det ? det.info : null;
      $('debug').textContent =
        'fps ' + (fpsN ? (1000 / (fpsAcc / fpsN)).toFixed(0) : '-') + ' q ' + quality.toFixed(2) +
        '\nmic ' + (micOK ? 'OK' : (micPending ? 'wait-gesture' : (holdToBlow ? 'hold' : '-'))) +
        '\nrms ' + (inf ? inf.rms.toFixed(4) : '-') + ' thr ' + (inf ? inf.thr.toFixed(4) : '-') +
        '\nlowR ' + (inf ? inf.lowRatio.toFixed(2) : '-') + ' crest ' + (inf ? inf.crest.toFixed(1) : '-') +
        ' flat ' + (inf ? inf.flat.toFixed(2) : '-') + ' hf ' + (inf ? inf.hfRatio.toFixed(2) : '-') +
        '\nair ' + air.toFixed(2) + ' breeze ' + breeze.toFixed(2) + ' cfm ' + (inf ? (inf.confirm * 1000).toFixed(0) : '-') +
        '\nblow ' + (blow ? 'YES' : 'no') + ' str ' + strength.toFixed(2) +
        '\nhealth ' + candle.health.toFixed(2) + ' phase ' + phase +
        '\nflame ' + flame.length + ' smoke ' + smoke.length + ' spark ' + sparks.length +
        '\ngeo y[' + geo.minY.toFixed(2) + ',' + geo.maxY.toFixed(2) + '] cakeR ' + geo.cakeR.toFixed(2) +
        ' cakeTopY ' + geo.cakeTopY.toFixed(2) +
        '\ncandle n ' + geo.candleN + ' y[' + geo.candleLowY.toFixed(2) + ',' + geo.candleTopY.toFixed(2) + ']' +
        (geo.candleLowY < geo.cakeTopY ? ' PLANTED' : ' FLOATING');
    }

    fpsAcc += dt * 1000; fpsN++;
    if (fpsN >= 45) {
      if (fpsAcc / fpsN > 27 && downgrades < 2) { downgrades++; quality = Math.max(0.45, quality - 0.28); }
      fpsAcc = 0; fpsN = 0;
    }
    requestAnimationFrame(frame);
  }

  /* ============================================================
   * 十六、尺寸
   * ========================================================== */
  function resize() {
    DPR = Math.min(window.devicePixelRatio || 1, 2);
    W = window.innerWidth || document.documentElement.clientWidth;
    H = window.innerHeight || document.documentElement.clientHeight;
    [vcv, scv].forEach(function (c) {
      c.width = Math.max(1, Math.floor(W * DPR));
      c.height = Math.max(1, Math.floor(H * DPR));
      c.style.width = W + 'px';
      c.style.height = H + 'px';
    });
    vctx.setTransform(DPR, 0, 0, DPR, 0, 0);
    sctx.setTransform(DPR, 0, 0, DPR, 0, 0);
    halfW = W / 2; halfH = H / 2;
    focal = Math.min(H * 0.66 * DIST0 / WORLD_H, W * 0.90 * DIST0 / WORLD_W);
    buildSceneBg();
  }

  var resizeTimer = null;
  function onResize() {
    resize();
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(function () {
      if (phase === 'gather' || phase === 'text') assignSet(sceneSet, makeText(sceneSet.n), tSec);
    }, 200);
  }

  /* ============================================================
   * 十七、初始化
   * ========================================================== */
  function init() {
    buildStyles();
    sprites.flame = [
      makeGlow(255, 252, 232, true), makeGlow(255, 236, 170, true), makeGlow(255, 196, 96, true),
      makeGlow(255, 142, 48, true), makeGlow(226, 88, 36, true), makeGlow(140, 46, 28, true)
    ];
    sprites.smoke = makeGlow(188, 178, 198, false);
    sprites.ember = makeGlow(255, 180, 90, true);
    sprites.spark = makeGlow(255, 200, 225, true);
    sprites.halo = makeGlow(255, 158, 88, false);
    sprites.core = makeGlow(255, 245, 220, true);
    sprites.flash = makeGlow(255, 250, 235, false);

    resize();

    N = Math.round(clamp((W * H) / 34, 4500, 10000));
    home = makeBirthdayCake(N);

    // 几何自检（仅 ?debug=1 展示）：
    //  · gr > 0.20  → 蛋糕本体 / 糖霜 / 糖珠，取其最高点 cakeTopY
    //  · gr < 0.12  → 蜡烛所在的"窄柱"，取其最低点 candleLowY 与最高点 candleTopY
    // 判定：candleLowY < cakeTopY 即蜡烛底部低于蛋糕装饰最高点 —— 埋在顶层里，绝非悬空。
    // 预期读数：cakeTopY≈1.40（顶层糖珠圈），candleLowY≈1.24（蜡底），candleTopY≈2.09（烛芯顶）。
    geo.minY = 1e9; geo.maxY = -1e9;
    geo.candleN = 0; geo.cakeR = 0;
    geo.cakeTopY = 0; geo.candleLowY = 1e9; geo.candleTopY = 0;
    for (var gi = 0; gi < N; gi++) {
      var gy = home.y[gi];
      if (gy < geo.minY) geo.minY = gy;
      if (gy > geo.maxY) geo.maxY = gy;
      var gr = Math.sqrt(home.x[gi] * home.x[gi] + home.z[gi] * home.z[gi]);
      if (gr > 0.20) {
        if (gr > geo.cakeR) geo.cakeR = gr;
        if (gy > geo.cakeTopY) geo.cakeTopY = gy;
      } else if (gr < 0.12) {
        geo.candleN++;
        if (gy > geo.candleTopY) geo.candleTopY = gy;
        if (gy > 0.9 && gy < geo.candleLowY) geo.candleLowY = gy;
      }
    }

    veilSet = makeSet(N);
    sceneSet = makeSet(N);
    veilSet.nx = sceneSet.nx = home.nx;
    veilSet.ny = sceneSet.ny = home.ny;
    veilSet.nz = sceneSet.nz = home.nz;

    // 两套粒子：完全相同的初始位置与随机种子 → 轨迹一致 → 淡出淡入看不出切换
    var scatterX = new Float32Array(N), scatterY = new Float32Array(N), scatterZ = new Float32Array(N);
    var seeds = new Float32Array(N);
    for (var i = 0; i < N; i++) {
      var a = Math.random() * 6.2832, b = Math.acos(2 * Math.random() - 1), rr = rnd(2.4, 4.6);
      scatterX[i] = Math.sin(b) * Math.cos(a) * rr;
      scatterY[i] = 1.05 + Math.cos(b) * rr * 0.7;
      scatterZ[i] = Math.sin(b) * Math.sin(a) * rr;
      seeds[i] = Math.random();
    }
    [veilSet, sceneSet].forEach(function (S) {
      for (var j = 0; j < N; j++) {
        S.px[j] = scatterX[j]; S.py[j] = scatterY[j]; S.pz[j] = scatterZ[j];
        S.vx[j] = 0; S.vy[j] = 0; S.vz[j] = 0;
        S.seed[j] = seeds[j];
      }
      assignSet(S, home, 0);
    });

    if (DEBUG) $('debug').classList.add('show');
    document.title = '🎂';
    try {
      $('ogTitle').setAttribute('content', '🎂');
      $('ogDesc').setAttribute('content', '🎂');
      $('metaDesc').setAttribute('content', '🎂');
    } catch (e) { }

    bindControls(vcv);
    bindControls(scv);
    window.addEventListener('mousemove', function (e) { ptMove(e.clientX, e.clientY); });
    window.addEventListener('mouseup', ptUp);
    window.addEventListener('resize', onResize);
    window.addEventListener('orientationchange', onResize);
    document.addEventListener('visibilitychange', function () {
      paused = document.hidden;
      if (paused) { if (det) det.suspend(); } else { if (det) det.resume(); lastT = 0; }
    });

    bootMic()['catch'](function (err) { handleMicFail(err); });
    setTimeout(function () { if (micOK && !everSound) holdToBlow = true; }, 9000);

    requestAnimationFrame(frame);
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
  else init();
})();
