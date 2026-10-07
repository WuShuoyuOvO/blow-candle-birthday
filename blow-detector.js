/**
 * BlowDetector —— 基于麦克风音频的「吹气」识别
 *
 * 识别依据（三者同时满足才判定为吹气）：
 *   1. 时域能量 RMS 显著高于自适应环境噪声基线（音量阈值）
 *   2. 频谱低频占比高（吹气是宽带低频气流噪声，能量集中在 ~0-900Hz）
 *   3. 频谱峰值比（crest）低 —— 排除说话/唱歌/音乐等有明显谐波峰的声音
 *
 * 只在本地实时分析，不做任何网络传输。
 */
(function (global) {
  'use strict';

  function clamp01(v) { return v < 0 ? 0 : (v > 1 ? 1 : v); }

  function ensureGetUserMedia() {
    if (navigator.mediaDevices && navigator.mediaDevices.getUserMedia) return true;
    var gum = navigator.getUserMedia || navigator.webkitGetUserMedia || navigator.mozGetUserMedia;
    if (!gum) return false;
    navigator.mediaDevices = {
      getUserMedia: function (constraints) {
        return new Promise(function (resolve, reject) {
          gum.call(navigator, constraints, resolve, reject);
        });
      }
    };
    return true;
  }

  // 全部阈值都朝「轻微吹气即可触发」下调：
  //  - floorMul / absFloor 更低：只要比环境噪声略高就判定
  //  - lowRatio / crest / flat 放宽：容忍更弱的低频特征
  //  - calibMs 更短：更快进入可吹状态
  //  - sensitivity 基准抬高：默认档位即为较灵敏
  var DEFAULTS = {
    fftSize: 1024,
    smoothing: 0.08,     // 频域平滑，越小越灵敏
    calibMs: 600,        // 环境噪声校准时长（越短越快进入可吹状态）
    absFloor: 0.0016,    // 绝对 RMS 下限
    floorMul: 1.10,      // RMS 只需略高于环境基线即可
    lowRatio: 0.20,      // 低频能量占比阈值
    crestMax: 20,        // 峰值比上限（线性幅值）：再大就像乐音/人声了
    flatMin: 0.18,       // 谱平坦度下限（线性幅值）：低于此说明有明显谐波结构
    harmCrest: 8,        // 超过此峰值比视为"有明显谐波"→ 疑似人声/音乐
    harmHF: 0.45,        // 谐波 + 高频过强 同时成立才否决
    confirmMs: 70,       // 条件需连续成立的时长（滤掉爆音/关门声等瞬时噪声）
    holdMs: 100,         // 条件消失后的保持时长
    sensitivity: 2.2     // 灵敏度：越大越容易触发
  };

  function BlowDetector(options) {
    this.opt = Object.assign({}, DEFAULTS, options || {});
    this.ready = false;
    this.ctx = null;
    this.stream = null;
    this.analyser = null;

    this.baseline = 0.006;
    this._calibSum = 0;
    this._calibN = 0;
    this._calibT = 0;

    this._smooth = 0;
    this._hold = 0;
    this._confirm = 0;
    this._peakEver = 0;

    this.info = { rms: 0, lowRatio: 0, crest: 0, flat: 0, hfRatio: 0, thr: 0, baseline: 0, confirm: 0 };
  }

  BlowDetector.prototype.start = async function () {
    if (!ensureGetUserMedia()) {
      var e1 = new Error('NO_GETUSERMEDIA'); e1.code = 'NO_GETUSERMEDIA'; throw e1;
    }
    var AC = global.AudioContext || global.webkitAudioContext;
    if (!AC) {
      var e2 = new Error('NO_WEB_AUDIO'); e2.code = 'NO_WEB_AUDIO'; throw e2;
    }

    var stream = await navigator.mediaDevices.getUserMedia({
      audio: {
        echoCancellation: false,   // 关闭 AGC/降噪，保证音量测量真实
        noiseSuppression: false,
        autoGainControl: false
      }
    });

    this.stream = stream;
    this.ctx = new AC();
    if (this.ctx.state === 'suspended') {
      try { await this.ctx.resume(); } catch (err) { /* 部分浏览器忽略 */ }
    }

    var src = this.ctx.createMediaStreamSource(stream);
    var an = this.ctx.createAnalyser();
    an.fftSize = this.opt.fftSize;
    an.smoothingTimeConstant = this.opt.smoothing;
    try { an.minDecibels = -95; an.maxDecibels = -12; } catch (err) { /* 只读属性时忽略 */ }
    src.connect(an);
    this.analyser = an;

    this.timeF = typeof an.getFloatTimeDomainData === 'function' ? new Float32Array(an.fftSize) : null;
    this.timeB = this.timeF ? null : new Uint8Array(an.fftSize);
    this.freq = new Uint8Array(an.frequencyBinCount);
    this.binHz = this.ctx.sampleRate / an.fftSize;

    // byte(0..255) → 线性幅值 查表：dB 压缩过的数据几乎分不出人声与吹气，
    // 还原成线性幅值后，"谱平坦度 / 峰值比" 才真正具有判别力。
    var minDb = (typeof an.minDecibels === 'number') ? an.minDecibels : -100;
    var maxDb = (typeof an.maxDecibels === 'number') ? an.maxDecibels : -30;
    this.lin = new Float32Array(256);
    for (var v = 0; v < 256; v++) {
      this.lin[v] = Math.pow(10, (minDb + (v / 255) * (maxDb - minDb)) / 20);
    }

    this.ready = true;
    this._calibSum = 0; this._calibN = 0; this._calibT = 0; this._peakEver = 0;
    return true;
  };

  BlowDetector.prototype.setSensitivity = function (s) { this.opt.sensitivity = s; };

  BlowDetector.prototype.resume = function () {
    if (this.ctx && this.ctx.state === 'suspended') this.ctx.resume().catch(function () {});
  };
  BlowDetector.prototype.suspend = function () {
    if (this.ctx && this.ctx.state === 'running') this.ctx.suspend().catch(function () {});
  };
  BlowDetector.prototype.stop = function () {
    this.ready = false;
    if (this.stream) { try { this.stream.getTracks().forEach(function (t) { t.stop(); }); } catch (e) {} }
    if (this.ctx) { try { this.ctx.close(); } catch (e) {} }
    this.stream = null; this.ctx = null; this.analyser = null;
  };

  /** 已观测到的最大电平，用于判断麦克风是否真的在采集声音 */
  BlowDetector.prototype.peakEver = function () { return this._peakEver; };

  /**
   * 每帧调用。
   * @param {number} dt 距上一帧的秒数
   * @returns {{level:number, blow:boolean, strength:number, rms:number}}
   */
  BlowDetector.prototype.update = function (dt) {
    var out = { level: 0, blow: false, strength: 0, rms: 0, air: 0 };
    if (!this.ready || !this.analyser) return out;
    if (!(dt > 0)) dt = 1 / 60;

    var an = this.analyser, i, v;

    // ---- 1. 时域 RMS ----
    var rms = 0;
    if (this.timeF) {
      an.getFloatTimeDomainData(this.timeF);
      var s = 0;
      for (i = 0; i < this.timeF.length; i++) { v = this.timeF[i]; s += v * v; }
      rms = Math.sqrt(s / this.timeF.length);
    } else {
      an.getByteTimeDomainData(this.timeB);
      var s2 = 0;
      for (i = 0; i < this.timeB.length; i++) { v = (this.timeB[i] - 128) / 128; s2 += v * v; }
      rms = Math.sqrt(s2 / this.timeB.length);
    }
    if (rms > this._peakEver) this._peakEver = rms;

    // ---- 2. 频域特征 ----
    an.getByteFrequencyData(this.freq);
    var f = this.freq, n = f.length, bz = this.binHz;
    var bi = function (hz) { return Math.min(n - 1, Math.max(1, Math.round(hz / bz))); };
    var lo = bi(900), mid = bi(3000), hi = bi(8000), start = bi(150);
    var hf0 = bi(3500), hf1 = bi(8000);
    var f4 = bi(4000);
    var nHF = Math.max(1, hf1 - hf0 + 1);
    var nLF = Math.max(1, lo - start + 1);
    var LIN = this.lin;

    var eL = 0, eM = 0, eH = 0, eHF = 0, eLF = 0, mx = 0, sum = 0, cnt = 0, logSum = 0;
    for (i = 2; i < n; i++) {
      var m = LIN[f[i]];                       // 线性幅值
      if (i <= lo) eL += m; else if (i <= mid) eM += m; else if (i <= hi) eH += m;
      if (i >= hf0 && i <= hf1) eHF += m;
      if (i >= start && i <= lo) eLF += m;
      if (i >= start && i <= f4) {             // 平坦度统计区间：150~4000Hz
        sum += m; cnt++;
        if (m > mx) mx = m;
        logSum += Math.log(m + 1e-9);
      }
    }
    var total = eL + eM + eH + 1e-9;
    var lowRatio = eL / total;
    var mean = sum / Math.max(1, cnt);
    var crest = mx / (mean + 1e-9);            // 峰值比：人声/音乐谐波尖锐 → 大
    var flat = Math.exp(logSum / Math.max(1, cnt)) / (mean + 1e-9);  // 谱平坦度：噪声→大，乐音→小
    // 高频/低频 能量密度比：说话的齿音与音乐有明显高频，吹气以低频为主
    var hfRatio = (eHF / nHF) / (eLF / nLF + 1e-9);

    // ---- 3. 自适应基线 ----
    if (this._calibT < this.opt.calibMs) {
      this._calibT += dt * 1000;
      this._calibSum += rms; this._calibN++;
      this.baseline = Math.max(0.0022, (this._calibSum / Math.max(1, this._calibN)) * 1.25);
    } else if (rms < this.baseline * 1.8) {
      // 缓慢跟随环境噪声变化
      this.baseline += (rms - this.baseline) * Math.min(1, dt * 0.35);
    }

    var sens = this.opt.sensitivity;
    var thr = Math.max(this.opt.absFloor, (this.baseline * this.opt.floorMul + 0.0008) / sens);

    // ---- 4. 判定 ----
    // 否决项：只在"有明显谐波峰"且"高频过强"同时成立时才否决，
    // 这样正常说话/唱歌会被挡掉，而弱吹气（宽平稳、无谐波）不会被误杀
    var harmonic = crest > this.opt.harmCrest && hfRatio > this.opt.harmHF;
    var ok = rms > thr && lowRatio > this.opt.lowRatio &&
             crest < this.opt.crestMax && flat > this.opt.flatMin && !harmonic;

    // 连续确认窗：滤掉爆音、关门、碰撞等瞬时噪声（<70ms 不算吹气）
    if (ok) this._confirm = Math.min(this.opt.confirmMs / 1000, this._confirm + dt);
    else this._confirm = Math.max(0, this._confirm - dt * 2);

    var fired = this._confirm >= this.opt.confirmMs / 1000;
    if (fired) this._hold = this.opt.holdMs / 1000;
    if (this._hold > 0) { this._hold -= dt; out.blow = true; }

    // 强度曲线极陡 + 保底 0.7：刚确认吹气就已具备足够"风力"，轻轻一口气即可
    out.strength = fired
      ? Math.max(0.7, Math.min(1, (rms / thr - 1) / 1.0))
      : 0;
    out.rms = rms;

    // 电平条：阈值固定在 25% 处，越过刻度线即视为吹气
    this._smooth = Math.max(rms, this._smooth * 0.86);
    out.level = Math.min(1, this._smooth / (thr * 4));

    // 连续「气流强度」：阈下也有值，驱动火焰轻微摇曳 —— 用户一靠近就能看到反应。
    // 用环境基线做归一化，安静房间与嘈杂房间都有一致的灵敏度。
    var b = Math.max(this.baseline, 0.002);
    out.air = clamp01((rms - b * 1.15) / (b * 3 + 0.02));

    this.info.rms = rms;
    this.info.lowRatio = lowRatio;
    this.info.crest = crest;
    this.info.flat = flat;
    this.info.hfRatio = hfRatio;
    this.info.thr = thr;
    this.info.baseline = this.baseline;
    this.info.confirm = this._confirm;
    return out;
  };

  global.BlowDetector = BlowDetector;
})(window);
