(() => {
  'use strict';

  const GRID = 22;
  const ART_CELL = 16;
  const FIELD_SIZE = GRID * ART_CELL;
  const FRAME = ART_CELL;
  const ART_SIZE = FIELD_SIZE + FRAME * 2;
  const BASE_STEP = 150;
  const MIN_STEP = 42;
  const SPEED_PER_FOOD = 1;
  const WALLS_MIN = 24;
  const WALLS_MAX = 34;
  const BEST_KEY = 'snake.best.v1';
  const TAU = Math.PI * 2;

  const canvas = document.getElementById('game');
  const ctx = canvas.getContext('2d');
  const scoreEl = document.getElementById('score');
  const bestEl = document.getElementById('best');
  const overlay = document.getElementById('overlay');
  const overlayTitle = document.getElementById('overlay-title');
  const overlayText = document.getElementById('overlay-text');
  const playBtn = document.getElementById('play-btn');
  const pauseBtn = document.getElementById('pause-btn');
  const soundBtn = document.getElementById('sound-btn');

  const state = {
    phase: 'idle', // idle | ready | playing | paused | over
    snake: [],
    prev: [],
    dir: { x: 1, y: 0 },
    pending: null,
    food: { x: 0, y: 0 },
    walls: new Set(),
    torches: [],
    score: 0,
    best: loadBest(),
    newBest: false,
    stepMs: BASE_STEP,
    acc: 0,
    size: ART_SIZE,
    cell: ART_CELL,
    shake: 0,
    hitFlash: 0,
  };

  const particles = [];
  const swipe = { active: false, x: 0, y: 0, pointerId: null };

  const KEY_DIRS = {
    ArrowUp: { x: 0, y: -1 },
    ArrowDown: { x: 0, y: 1 },
    ArrowLeft: { x: -1, y: 0 },
    ArrowRight: { x: 1, y: 0 },
    KeyW: { x: 0, y: -1 },
    KeyS: { x: 0, y: 1 },
    KeyA: { x: -1, y: 0 },
    KeyD: { x: 1, y: 0 },
    w: { x: 0, y: -1 },
    s: { x: 0, y: 1 },
    a: { x: -1, y: 0 },
    d: { x: 1, y: 0 },
  };

  const DPAD_DIRS = {
    up: { x: 0, y: -1 },
    down: { x: 0, y: 1 },
    left: { x: -1, y: 0 },
    right: { x: 1, y: 0 },
  };

  // ---------- Audio ----------

  const Sound = (() => {
    const AudioCtor = window.AudioContext || window.webkitAudioContext;
    const supported = Boolean(AudioCtor);
    const MUTE_KEY = 'snake.muted.v1';

    // Dark-fantasy DOS soundtrack: 116 BPM, 16th-note grid, 128 steps.
    const MUSIC_STEP_SEC = 60 / 116 / 4;
    const MUSIC_LEN = 128;

    // D natural/harmonic minor. MIDI 38 = D2.
    const BASS_INTRO = [
      38, null, null, null, null, null, null, null,
      38, null, null, null, 45, null, null, null,
    ];
    const BASS_BUILD = [
      38, null, 38, null, 41, null, 38, null,
      45, null, 38, null, 43, null, 45, null,
    ];
    const BASS_A = [
      38, 38, 38, 41, 38, 38, 45, 38,
      38, 38, 48, 38, 46, 45, 43, 45,
    ];
    const BASS_B = [
      38, 38, 41, 41, 38, 38, 45, 45,
      48, 48, 46, 46, 45, 45, 43, 43,
    ];
    const BASS_BREAK = [
      null, null, null, null, 38, null, null, null,
      null, null, null, null, 46, null, null, null,
    ];
    const BASS_C = [
      38, 38, 38, 41, 38, 38, 45, 38,
      46, 46, 45, 45, 43, 43, 41, 41,
    ];
    const BASS_D = [
      38, 41, 43, 45, 46, 45, 43, 41,
      38, 41, 43, 45, 48, 46, 45, 43,
    ];

    const BASS = [
      ...BASS_INTRO, ...BASS_BUILD, ...BASS_A, ...BASS_B,
      ...BASS_BREAK, ...BASS_C, ...BASS_A, ...BASS_D,
    ];

    const LEAD_A = [
      null, null, 74, null, 77, null, 76, null,
      74, null, 72, null, 70, null, 69, null,
    ];
    const LEAD_B = [
      81, null, 79, null, 77, null, 76, null,
      74, null, 72, null, 70, 72, 74, null,
    ];
    const LEAD_C = [
      86, null, 84, 81, 79, null, 77, 76,
      74, null, 77, 79, 81, 79, 77, 74,
    ];
    const LEAD_D = [
      81, 79, 77, 76, 74, 72, 70, 69,
      67, 65, 64, 62, 65, 64, 62, null,
    ];

    const LEAD = [
      ...Array(32).fill(null), ...LEAD_A, ...LEAD_B,
      ...Array(32).fill(null), ...LEAD_C, ...LEAD_D,
    ];

    const BELL_ARP = [62, 65, 69, 74, 69, 65, 62, 65];

    // One chord every eight steps: Dm, Bb, Gm, A.
    const CHORDS = [
      [50, 53, 57], [50, 53, 57],
      [50, 53, 57], [46, 50, 53],
      [50, 53, 57], [46, 50, 53],
      [43, 46, 50], [45, 49, 52],
      [50, 53, 57], [46, 50, 53],
      [43, 46, 50], [45, 49, 52],
      [50, 53, 57], [46, 50, 53],
      [43, 46, 50], [45, 49, 52],
    ];

    let ctx = null;
    let master = null;
    let sfxBus = null;
    let musicGain = null;
    let musicBus = null;
    let delay = null;
    let feedback = null;
    let wet = null;
    let noiseBuffer = null;

    let ambientGain = null;
    let ambientOn = false;

    let muted = loadMuted();
    let musicOn = false;
    let musicTimer = null;
    let musicNextTime = 0;
    let musicStep = 0;

    function loadMuted() {
      try {
        return localStorage.getItem(MUTE_KEY) === '1';
      } catch {
        return false;
      }
    }

    function saveMuted() {
      try {
        localStorage.setItem(MUTE_KEY, muted ? '1' : '0');
      } catch {
        /* storage may be unavailable */
      }
    }

    function midi(note) {
      return 440 * Math.pow(2, (note - 69) / 12);
    }

    function unlock() {
      if (!supported) return false;

      if (!ctx) {
        ctx = new AudioCtor();

        master = ctx.createGain();
        master.gain.value = muted ? 0.0001 : 0.9;

        const compressor = ctx.createDynamicsCompressor();
        compressor.threshold.value = -18;
        compressor.knee.value = 24;
        compressor.ratio.value = 3;
        compressor.attack.value = 0.003;
        compressor.release.value = 0.25;
        master.connect(compressor);
        compressor.connect(ctx.destination);

        sfxBus = ctx.createGain();
        sfxBus.gain.value = 0.55;
        sfxBus.connect(master);

        musicGain = ctx.createGain();
        musicGain.gain.value = 0.0001;
        musicGain.connect(master);

        musicBus = ctx.createGain();
        musicBus.gain.value = 1;
        musicBus.connect(musicGain);

        // Dotted-eighth echo at 116 BPM: adds space without washing out the mix.
        delay = ctx.createDelay(0.8);
        delay.delayTime.value = 0.387;
        feedback = ctx.createGain();
        feedback.gain.value = 0.3;
        wet = ctx.createGain();
        wet.gain.value = 0.2;

        musicBus.connect(delay);
        delay.connect(feedback);
        feedback.connect(delay);
        delay.connect(wet);
        wet.connect(musicGain);

        ambientGain = ctx.createGain();
        ambientGain.gain.value = 0.0001;
        ambientGain.connect(master);

        noiseBuffer = ctx.createBuffer(1, ctx.sampleRate * 2, ctx.sampleRate);
        const noiseData = noiseBuffer.getChannelData(0);
        for (let i = 0; i < noiseData.length; i++) {
          noiseData[i] = Math.random() * 2 - 1;
        }

        buildAmbient();
      }

      if (ctx.state === 'suspended') {
        ctx.resume().catch(() => {});
      }
      return true;
    }

    function ready() {
      return supported && !muted && unlock();
    }

    // ---------- Ambient bed: a low, breathing dungeon drone ----------

    function buildAmbient() {
      // Pure low tones only — no noise layers, so the bed stays clean.
      const droneFilter = ctx.createBiquadFilter();
      droneFilter.type = 'lowpass';
      droneFilter.frequency.value = 220;
      droneFilter.Q.value = 0.9;

      const droneGain = ctx.createGain();
      droneGain.gain.value = 0.1;

      droneFilter.connect(droneGain);
      droneGain.connect(ambientGain);

      // Slow swell and filter drift keep the drone alive without hiss.
      const swell = ctx.createOscillator();
      const swellGain = ctx.createGain();
      swell.frequency.value = 0.035;
      swellGain.gain.value = 0.03;
      swell.connect(swellGain);
      swellGain.connect(droneGain.gain);
      swell.start();

      const sweep = ctx.createOscillator();
      const sweepGain = ctx.createGain();
      sweep.frequency.value = 0.021;
      sweepGain.gain.value = 35;
      sweep.connect(sweepGain);
      sweepGain.connect(droneFilter.frequency);
      sweep.start();

      // Very slow detune drift adds movement like a distant choir.
      const drift = ctx.createOscillator();
      const driftGain = ctx.createGain();
      drift.frequency.value = 0.017;
      driftGain.gain.value = 3;
      drift.connect(driftGain);
      drift.start();

      for (const [note, type, level, detune] of [
        [26, 'sine', 0.55, -4],
        [38, 'triangle', 0.28, 5],
        [45, 'sine', 0.18, -3],
      ]) {
        const osc = ctx.createOscillator();
        const gain = ctx.createGain();
        osc.type = type;
        osc.frequency.value = midi(note);
        osc.detune.value = detune;
        gain.gain.value = level;
        osc.connect(gain);
        gain.connect(droneFilter);
        driftGain.connect(osc.detune);
        osc.start();
      }
    }

    function startAmbient() {
      if (!ctx || !ambientGain || ambientOn) return;
      ambientOn = true;
      const now = ctx.currentTime;
      ambientGain.gain.cancelScheduledValues(now);
      ambientGain.gain.setValueAtTime(Math.max(0.0001, ambientGain.gain.value), now);
      ambientGain.gain.linearRampToValueAtTime(0.5, now + 1.4);
    }

    function stopAmbient(fade = 0.5) {
      if (!ctx || !ambientGain || !ambientOn) return;
      ambientOn = false;
      const now = ctx.currentTime;
      ambientGain.gain.cancelScheduledValues(now);
      ambientGain.gain.setValueAtTime(Math.max(0.0001, ambientGain.gain.value), now);
      ambientGain.gain.exponentialRampToValueAtTime(0.0001, now + fade);
    }

    // ---------- DOS-style sound effects ----------

    function beep(freq, when, duration, level, options = {}) {
      if (!ctx) return;
      const start = ctx.currentTime + when;
      const osc = ctx.createOscillator();
      const gain = ctx.createGain();

      osc.type = options.type || 'square';
      osc.frequency.setValueAtTime(freq, start);
      if (options.glideTo) {
        osc.frequency.exponentialRampToValueAtTime(options.glideTo, start + duration);
      }

      gain.gain.setValueAtTime(0.0001, start);
      gain.gain.exponentialRampToValueAtTime(level, start + 0.002);
      gain.gain.setValueAtTime(level, start + duration * 0.62);
      gain.gain.exponentialRampToValueAtTime(0.0001, start + duration);

      osc.connect(gain);
      gain.connect(sfxBus);
      osc.start(start);
      osc.stop(start + duration + 0.02);
    }

    function sfxNoise(when, duration, level, type, freq, q) {
      if (!ctx || !noiseBuffer) return;
      const start = ctx.currentTime + when;
      const src = ctx.createBufferSource();
      const filter = ctx.createBiquadFilter();
      const gain = ctx.createGain();

      src.buffer = noiseBuffer;
      filter.type = type;
      filter.frequency.value = freq;
      filter.Q.value = q;

      gain.gain.setValueAtTime(level, start);
      gain.gain.exponentialRampToValueAtTime(0.0001, start + duration);

      src.connect(filter);
      filter.connect(gain);
      gain.connect(sfxBus);
      src.start(start);
      src.stop(start + duration + 0.02);
    }

    function start() {
      if (!ready()) return;
      beep(midi(62), 0, 0.07, 0.16);
      beep(midi(69), 0.07, 0.07, 0.16);
      beep(midi(74), 0.14, 0.15, 0.18);
      beep(midi(38), 0, 0.2, 0.09, { type: 'triangle' });
    }

    function eat(score) {
      if (!ready()) return;
      const scale = [0, 2, 4, 7, 9];
      const base = 74 + scale[score % scale.length];
      beep(midi(base), 0, 0.05, 0.15);
      beep(midi(base + 7), 0.05, 0.07, 0.12);
      sfxNoise(0, 0.02, 0.045, 'highpass', 4200, 0.7);
    }

    function pause() {
      if (!ready()) return;
      beep(midi(69), 0, 0.07, 0.14);
      beep(midi(62), 0.07, 0.13, 0.14);
    }

    function resume() {
      if (!ready()) return;
      beep(midi(62), 0, 0.07, 0.14);
      beep(midi(69), 0.07, 0.13, 0.14);
    }

    function die(newBest) {
      if (!ready()) return;
      const notes = [69, 65, 62, 57, 53, 50, 45, 38];
      notes.forEach((note, i) => {
        beep(midi(note), i * 0.085, 0.09, 0.16);
      });
      beep(midi(38), 0.7, 0.75, 0.13, { type: 'triangle', glideTo: midi(26) });
      sfxNoise(0.02, 0.45, 0.09, 'lowpass', 900, 0.8);
      if (newBest) {
        [74, 77, 81, 86].forEach((note, i) => {
          beep(midi(note), 1.35 + i * 0.08, 0.16, 0.11, { type: 'triangle' });
        });
      }
    }

    function win() {
      if (!ready()) return;
      [62, 65, 69, 74, 77, 81, 86].forEach((note, i) => {
        beep(midi(note), i * 0.09, 0.14, 0.15);
      });
      beep(midi(74), 0.65, 0.5, 0.1, { type: 'triangle' });
      beep(midi(81), 0.65, 0.5, 0.08, { type: 'triangle' });
    }

    function musicTone(freq, time, duration, type, level, bus, options = {}) {
      const osc = ctx.createOscillator();
      const gain = ctx.createGain();

      osc.type = type;
      osc.frequency.setValueAtTime(freq, time);
      if (options.glideTo) {
        osc.frequency.exponentialRampToValueAtTime(
          options.glideTo,
          time + (options.glideTime || duration)
        );
      }

      gain.gain.setValueAtTime(0.0001, time);
      gain.gain.exponentialRampToValueAtTime(level, time + (options.attack || 0.006));
      gain.gain.exponentialRampToValueAtTime(0.0001, time + duration);

      osc.connect(gain);
      gain.connect(bus);
      osc.start(time);
      osc.stop(time + duration + 0.03);
    }

    function noiseBurst(time, duration, level, type, freq, q, bus) {
      if (!noiseBuffer) return;
      const src = ctx.createBufferSource();
      const filter = ctx.createBiquadFilter();
      const gain = ctx.createGain();

      src.buffer = noiseBuffer;
      filter.type = type;
      filter.frequency.value = freq;
      filter.Q.value = q;

      gain.gain.setValueAtTime(level, time);
      gain.gain.exponentialRampToValueAtTime(0.0001, time + duration);

      src.connect(filter);
      filter.connect(gain);
      gain.connect(bus);
      src.start(time);
      src.stop(time + duration + 0.02);
    }

    function kick(time, level = 0.5) {
      musicTone(150, time, 0.16, 'sine', level, musicGain, {
        glideTo: 42,
        glideTime: 0.06,
        attack: 0.002,
      });
      noiseBurst(time, 0.015, 0.035, 'highpass', 3000, 0.7, musicGain);
    }

    function snare(time) {
      noiseBurst(time, 0.14, 0.14, 'bandpass', 1700, 0.9, musicGain);
      musicTone(190, time, 0.08, 'triangle', 0.06, musicGain, {
        glideTo: 130,
        attack: 0.002,
      });
    }

    function hat(time, level) {
      noiseBurst(time, 0.035, level, 'highpass', 7600, 0.6, musicGain);
    }

    function openHat(time, level) {
      noiseBurst(time, 0.12, level, 'highpass', 6800, 0.5, musicGain);
    }

    function tom(time, level) {
      musicTone(120, time, 0.12, 'sine', level, musicGain, {
        glideTo: 68,
        glideTime: 0.1,
        attack: 0.002,
      });
    }

    function crash(time) {
      noiseBurst(time, 0.9, 0.075, 'highpass', 3800, 0.4, musicGain);
    }

    // FM bell: sine carrier with a decaying sine modulator — AdLib-style chime.
    function fmBell(time, note, duration = 1.4, level = 0.05) {
      const freq = midi(note);
      const carrier = ctx.createOscillator();
      const modulator = ctx.createOscillator();
      const modGain = ctx.createGain();
      const gain = ctx.createGain();

      carrier.type = 'sine';
      carrier.frequency.value = freq;

      modulator.type = 'sine';
      modulator.frequency.value = freq * 2.01;
      modGain.gain.setValueAtTime(freq * 1.6, time);
      modGain.gain.exponentialRampToValueAtTime(freq * 0.05, time + duration * 0.7);

      gain.gain.setValueAtTime(0.0001, time);
      gain.gain.exponentialRampToValueAtTime(level, time + 0.006);
      gain.gain.exponentialRampToValueAtTime(0.0001, time + duration);

      modulator.connect(modGain);
      modGain.connect(carrier.frequency);
      carrier.connect(gain);
      gain.connect(musicBus);

      modulator.start(time);
      carrier.start(time);
      modulator.stop(time + duration + 0.03);
      carrier.stop(time + duration + 0.03);
    }

    // Slow detuned triangles: the "dark chapel" pad under the intro and breaks.
    function padChord(time, notes, duration, level = 0.025) {
      const filter = ctx.createBiquadFilter();
      const gain = ctx.createGain();

      filter.type = 'lowpass';
      filter.frequency.value = 1100;
      filter.Q.value = 0.8;

      gain.gain.setValueAtTime(0.0001, time);
      gain.gain.exponentialRampToValueAtTime(level, time + 0.45);
      gain.gain.setValueAtTime(level, time + duration * 0.7);
      gain.gain.exponentialRampToValueAtTime(0.0001, time + duration);

      filter.connect(gain);
      gain.connect(musicGain);

      for (const note of notes) {
        for (const detune of [-5, 5]) {
          const osc = ctx.createOscillator();
          osc.type = 'triangle';
          osc.frequency.value = midi(note);
          osc.detune.value = detune;
          osc.connect(filter);
          osc.start(time);
          osc.stop(time + duration + 0.05);
        }
      }
    }

    // Square-wave bass with a triangle sub: punchy, unmistakably DOS.
    function bassNote(time, note, duration, level = 0.11) {
      const freq = midi(note);
      const osc = ctx.createOscillator();
      const sub = ctx.createOscillator();
      const subGain = ctx.createGain();
      const filter = ctx.createBiquadFilter();
      const gain = ctx.createGain();

      osc.type = 'square';
      osc.frequency.value = freq;

      sub.type = 'triangle';
      sub.frequency.value = freq / 2;
      subGain.gain.value = 0.5;

      filter.type = 'lowpass';
      filter.frequency.setValueAtTime(900, time);
      filter.frequency.exponentialRampToValueAtTime(320, time + duration);
      filter.Q.value = 1.5;

      gain.gain.setValueAtTime(0.0001, time);
      gain.gain.exponentialRampToValueAtTime(level, time + 0.006);
      gain.gain.setValueAtTime(level * 0.8, time + duration * 0.55);
      gain.gain.exponentialRampToValueAtTime(0.0001, time + duration);

      osc.connect(filter);
      sub.connect(subGain);
      subGain.connect(filter);
      filter.connect(gain);
      gain.connect(musicGain);

      osc.start(time);
      sub.start(time);
      osc.stop(time + duration + 0.03);
      sub.stop(time + duration + 0.03);
    }

    // Thin square lead with vibrato, sent through the dotted-eighth echo.
    function leadNote(time, note, duration, level = 0.045) {
      const freq = midi(note);
      const osc = ctx.createOscillator();
      const osc2 = ctx.createOscillator();
      const gain = ctx.createGain();
      const vibrato = ctx.createOscillator();
      const vibratoGain = ctx.createGain();

      osc.type = 'square';
      osc.frequency.value = freq;

      osc2.type = 'triangle';
      osc2.frequency.value = freq;
      osc2.detune.value = 7;

      gain.gain.setValueAtTime(0.0001, time);
      gain.gain.exponentialRampToValueAtTime(level, time + 0.02);
      gain.gain.setValueAtTime(level * 0.85, time + duration * 0.5);
      gain.gain.exponentialRampToValueAtTime(0.0001, time + duration);

      vibrato.frequency.value = 5.2;
      vibratoGain.gain.value = 6;
      vibrato.connect(vibratoGain);
      vibratoGain.connect(osc.detune);
      vibratoGain.connect(osc2.detune);

      osc.connect(gain);
      osc2.connect(gain);
      gain.connect(musicBus);

      osc.start(time);
      osc2.start(time);
      vibrato.start(time);
      osc.stop(time + duration + 0.04);
      osc2.stop(time + duration + 0.04);
      vibrato.stop(time + duration + 0.04);
    }

    // Noise sweep that drags the break back into the driving section.
    function riser(time, duration) {
      const src = ctx.createBufferSource();
      src.buffer = noiseBuffer;
      src.loop = true;

      const filter = ctx.createBiquadFilter();
      filter.type = 'bandpass';
      filter.Q.value = 3;
      filter.frequency.setValueAtTime(300, time);
      filter.frequency.exponentialRampToValueAtTime(3200, time + duration);

      const gain = ctx.createGain();
      gain.gain.setValueAtTime(0.0001, time);
      gain.gain.exponentialRampToValueAtTime(0.05, time + duration);
      gain.gain.exponentialRampToValueAtTime(0.0001, time + duration + 0.08);

      src.connect(filter);
      filter.connect(gain);
      gain.connect(musicGain);
      src.start(time);
      src.stop(time + duration + 0.1);
    }

    // Eight 16-step sections: intro, build, A, B, break, C, A, climax.
    function playMusicStep(index, time) {
      const section = Math.floor(index / 16);
      const pos = index % 16;

      const bass = BASS[index];
      if (bass !== null && bass !== undefined) {
        const long = section === 0 || section === 4;
        const duration = MUSIC_STEP_SEC * (long ? 2.6 : 0.82);
        const level = [0.1, 0.11, 0.12, 0.13, 0.085, 0.12, 0.12, 0.14][section];
        bassNote(time, bass, duration, level);
      }

      if (index % 8 === 0) {
        const chord = CHORDS[Math.floor(index / 8) % CHORDS.length];
        const padLevel = [0.03, 0.02, 0.022, 0.018, 0.032, 0.018, 0.022, 0.028][section];
        padChord(time, chord, MUSIC_STEP_SEC * 7.5, padLevel);
      }

      switch (section) {
        case 0:
          if (pos === 0 || pos === 8) {
            fmBell(time, BELL_ARP[pos / 8], 1.6, 0.05);
          }
          break;
        case 1:
          if (pos === 0 || pos === 8) kick(time, 0.4);
          if (pos === 12) snare(time);
          if (pos >= 8 && pos % 2 === 0) hat(time, 0.03);
          if (pos === 0) fmBell(time, BELL_ARP[0], 1.4, 0.045);
          break;
        case 2:
          if (pos === 0 || pos === 6 || pos === 8 || pos === 14) kick(time, 0.5);
          if (pos === 4 || pos === 12) snare(time);
          hat(time, pos % 2 === 0 ? 0.032 : 0.016);
          break;
        case 3:
          if (pos % 4 === 0) kick(time, 0.46);
          if (pos === 4 || pos === 12) snare(time);
          hat(time, pos % 2 === 0 ? 0.034 : 0.018);
          if (pos === 14) openHat(time, 0.03);
          break;
        case 4:
          if (pos === 0) {
            kick(time, 0.42);
            crash(time);
          }
          if (pos === 8) fmBell(time, BELL_ARP[2], 1.8, 0.05);
          if (pos % 4 === 2) {
            fmBell(time, BELL_ARP[(pos / 2) % BELL_ARP.length], 0.8, 0.026);
          }
          if (pos === 12) riser(time, MUSIC_STEP_SEC * 4);
          break;
        case 5:
          if (pos === 0 || pos === 6 || pos === 8 || pos === 14) kick(time, 0.52);
          if (pos === 4 || pos === 12) snare(time);
          hat(time, pos % 2 === 0 ? 0.036 : 0.02);
          if (pos >= 12) tom(time, 0.03 + (pos - 12) * 0.007);
          break;
        case 6:
          if (pos === 0) crash(time);
          if (pos === 0 || pos === 6 || pos === 8 || pos === 14) kick(time, 0.5);
          if (pos === 4 || pos === 12) snare(time);
          hat(time, pos % 2 === 0 ? 0.034 : 0.018);
          if (pos === 0 || pos === 8) {
            fmBell(time, BELL_ARP[(index / 8) % BELL_ARP.length], 1.2, 0.04);
          }
          break;
        case 7:
          if (pos === 0) crash(time);
          if (pos % 4 === 0) kick(time, 0.56);
          if (pos === 4 || pos === 12) snare(time);
          hat(time, pos % 2 === 0 ? 0.038 : 0.022);
          break;
      }

      const lead = LEAD[index];
      if (lead !== null && lead !== undefined) {
        const level = section === 7 ? 0.055 : section === 5 ? 0.05 : 0.045;
        leadNote(time, lead, MUSIC_STEP_SEC * 2.6, level);
      }
    }

    function scheduleMusic() {
      if (!musicOn || !ctx) return;
      if (musicNextTime < ctx.currentTime - 0.1) {
        musicNextTime = ctx.currentTime + 0.05;
      }
      const horizon = ctx.currentTime + 0.4;
      while (musicNextTime < horizon) {
        playMusicStep(musicStep, musicNextTime);
        musicStep = (musicStep + 1) % MUSIC_LEN;
        musicNextTime += MUSIC_STEP_SEC;
      }
    }

    function startMusic() {
      if (!ready() || musicOn) return;
      musicOn = true;
      musicStep = 0;
      musicNextTime = ctx.currentTime + 0.45;

      const now = ctx.currentTime;
      musicGain.gain.cancelScheduledValues(now);
      musicGain.gain.setValueAtTime(Math.max(0.0001, musicGain.gain.value), now);
      musicGain.gain.exponentialRampToValueAtTime(0.4, now + 1.2);

      startAmbient();
      scheduleMusic();
      musicTimer = setInterval(scheduleMusic, 120);
    }

    function stopMusic(fade = 0.45) {
      stopAmbient(fade + 0.2);
      if (!musicOn) return;
      musicOn = false;
      if (musicTimer) clearInterval(musicTimer);
      musicTimer = null;
      if (!ctx || !musicGain) return;

      const now = ctx.currentTime;
      musicGain.gain.cancelScheduledValues(now);
      musicGain.gain.setValueAtTime(Math.max(0.0001, musicGain.gain.value), now);
      musicGain.gain.exponentialRampToValueAtTime(0.0001, now + fade);
    }

    function setMuted(value) {
      muted = Boolean(value);
      saveMuted();

      if (muted) {
        stopMusic(0.15);
        if (ctx && master) {
          const now = ctx.currentTime;
          master.gain.cancelScheduledValues(now);
          master.gain.setTargetAtTime(0.0001, now, 0.03);
        }
      } else if (unlock()) {
        const now = ctx.currentTime;
        master.gain.cancelScheduledValues(now);
        master.gain.setTargetAtTime(0.9, now, 0.03);
      }

      return muted;
    }

    return {
      isSupported: () => supported,
      isMuted: () => muted,
      setMuted,
      start,
      eat,
      pause,
      resume,
      die,
      win,
      startMusic,
      stopMusic,
      unlock,
    };
  })();

  // ---------- Storage ----------

  function loadBest() {
    try {
      return Number(localStorage.getItem(BEST_KEY)) || 0;
    } catch {
      return 0;
    }
  }

  function saveBest(value) {
    try {
      localStorage.setItem(BEST_KEY, String(value));
    } catch {
      /* storage may be unavailable, e.g. strict file:// mode */
    }
  }

  // ---------- Game setup ----------

  function reset() {
    const mid = Math.floor(GRID / 2);
    state.snake = [
      { x: mid + 1, y: mid },
      { x: mid, y: mid },
      { x: mid - 1, y: mid },
    ];
    state.prev = state.snake.map((seg) => ({ x: seg.x, y: seg.y }));
    state.dir = { x: 1, y: 0 };
    state.pending = null;
    state.score = 0;
    state.newBest = false;
    state.stepMs = BASE_STEP;
    state.acc = 0;
    state.shake = 0;
    state.hitFlash = 0;
    particles.length = 0;
    scoreEl.textContent = '0';
    scoreEl.classList.remove('bump');
    generateWalls();
    placeFood();
  }

  function cellKey(x, y) {
    return y * GRID + x;
  }

  function isSpawnSafe(x, y) {
    const mid = Math.floor(GRID / 2);
    return (
      x >= mid - 4 && x <= mid + 6 &&
      y >= mid - 1 && y <= mid + 1
    );
  }

  function generateWalls() {
    const target = WALLS_MIN + Math.floor(Math.random() * (WALLS_MAX - WALLS_MIN + 1));
    const startKey = cellKey(state.snake[0].x, state.snake[0].y);
    state.walls = new Set();

    let attempts = 0;
    while (state.walls.size < target && attempts < 300) {
      attempts += 1;
      const cluster = buildWallCluster();
      if (cluster.length === 0) continue;

      for (const key of cluster) state.walls.add(key);
      if (!isMapConnected(startKey)) {
        for (const key of cluster) state.walls.delete(key);
      }
    }

    state.torches = [];
    selectTorches();
    buildGloom();
  }

  // Torches line the castle walls and the map edge, so their light defines the room.
  function selectTorches() {
    const edgeTop = [];
    const edgeBottom = [];
    const edgeLeft = [];
    const edgeRight = [];

    for (let x = 2; x <= GRID - 3; x++) {
      edgeTop.push({ x, y: -1 });
      edgeBottom.push({ x, y: GRID });
    }
    for (let y = 2; y <= GRID - 3; y++) {
      edgeLeft.push({ x: -1, y });
      edgeRight.push({ x: GRID, y });
    }

    const edge = [...edgeTop, ...edgeBottom, ...edgeLeft, ...edgeRight];
    const edgeGroups = [edgeTop, edgeBottom, edgeLeft, edgeRight];

    const interior = [];
    for (const key of state.walls) {
      const x = key % GRID;
      const y = (key / GRID) | 0;
      if (y < 1 || y > GRID - 2) continue;
      if (state.walls.has(cellKey(x, y + 1))) continue;
      interior.push({ x, y });
    }

    for (const group of edgeGroups) shuffle(group);
    shuffle(edge);
    shuffle(interior);

    const chosen = [];
    const add = (cell, minGap) => {
      const tooClose = chosen.some(
        (torch) =>
          Math.abs(torch.x - cell.x) + Math.abs(torch.y - cell.y) < minGap
      );
      if (tooClose) return false;
      chosen.push({ x: cell.x, y: cell.y, seed: Math.random() * TAU });
      return true;
    };

    // At least one sconce on every outer wall, then a fifth one.
    for (const group of edgeGroups) {
      for (const cell of group) {
        if (add(cell, 6)) break;
      }
    }
    for (const cell of edge) {
      if (chosen.length >= 5) break;
      add(cell, 5);
    }

    // Four more on the dungeon's inner walls.
    for (const cell of interior) {
      if (chosen.length >= 9) break;
      add(cell, 5);
    }

    // Sparse wall layouts can leave fewer than four usable inner faces.
    if (chosen.length < 8) {
      for (const cell of edge) {
        if (chosen.length >= 9) break;
        add(cell, 3);
      }
    }

    if (chosen.length < 7) {
      for (const key of state.walls) {
        if (chosen.length >= 9) break;
        const x = key % GRID;
        const y = (key / GRID) | 0;
        add({ x, y }, 3);
      }
    }

    state.torches = chosen;
  }

  function shuffle(items) {
    for (let i = items.length - 1; i > 0; i--) {
      const j = (Math.random() * (i + 1)) | 0;
      [items[i], items[j]] = [items[j], items[i]];
    }
  }

  function buildWallCluster() {
    const horizontal = Math.random() < 0.5;
    const length = 2 + Math.floor(Math.random() * 3);
    const startX = 1 + Math.floor(Math.random() * (GRID - 2));
    const startY = 1 + Math.floor(Math.random() * (GRID - 2));
    const cells = [];

    for (let i = 0; i < length; i++) {
      const x = startX + (horizontal ? i : 0);
      const y = startY + (horizontal ? 0 : i);
      if (x < 1 || x > GRID - 2 || y < 1 || y > GRID - 2) return [];
      if (isSpawnSafe(x, y)) return [];
      const key = cellKey(x, y);
      if (state.walls.has(key)) return [];
      cells.push(key);
    }

    return cells;
  }

  // Every free cell must stay reachable from the snake, otherwise a wall
  // cluster is discarded and generation continues with the next one.
  function isMapConnected(startKey) {
    const visited = new Uint8Array(GRID * GRID);
    const stack = [startKey];
    visited[startKey] = 1;
    let reachable = 0;

    while (stack.length) {
      const key = stack.pop();
      reachable += 1;
      const x = key % GRID;
      const y = (key / GRID) | 0;

      if (x > 0 && !visited[key - 1] && !state.walls.has(key - 1)) {
        visited[key - 1] = 1;
        stack.push(key - 1);
      }
      if (x < GRID - 1 && !visited[key + 1] && !state.walls.has(key + 1)) {
        visited[key + 1] = 1;
        stack.push(key + 1);
      }
      if (y > 0 && !visited[key - GRID] && !state.walls.has(key - GRID)) {
        visited[key - GRID] = 1;
        stack.push(key - GRID);
      }
      if (y < GRID - 1 && !visited[key + GRID] && !state.walls.has(key + GRID)) {
        visited[key + GRID] = 1;
        stack.push(key + GRID);
      }
    }

    return reachable === GRID * GRID - state.walls.size;
  }

  function placeFood() {
    const occupied = new Set(state.snake.map((seg) => cellKey(seg.x, seg.y)));
    for (const key of state.walls) occupied.add(key);
    const free = [];
    for (let i = 0; i < GRID * GRID; i++) {
      if (!occupied.has(i)) free.push(i);
    }
    if (free.length === 0) return false;
    const index = free[(Math.random() * free.length) | 0];
    state.food = { x: index % GRID, y: Math.floor(index / GRID) };
    return true;
  }

  function startGame(autoStart = false) {
    reset();
    state.phase = 'ready';
    state.acc = 0;
    setPauseIcon(false);

    if (autoStart) {
      beginRun();
      return;
    }

    showOverlay(
      'Приготовься',
      'Нажмите ПРОБЕЛ, чтобы змейка побежала. Стрелки — выбрать направление.',
      'Начать'
    );
  }

  function beginRun() {
    if (state.phase !== 'ready') return;
    state.phase = 'playing';
    state.acc = 0;
    hideOverlay();
    setPauseIcon(false);
    Sound.start();
    Sound.startMusic();
  }

  function pauseGame() {
    if (state.phase !== 'playing') return;
    state.phase = 'paused';
    setPauseIcon(true);
    Sound.stopMusic(0.25);
    Sound.pause();
    showOverlay('Пауза', 'Пробел или кнопка ниже — продолжить.', 'Продолжить');
  }

  function resumeGame() {
    if (state.phase !== 'paused') return;
    state.phase = 'playing';
    state.acc = 0;
    setPauseIcon(false);
    hideOverlay();
    Sound.resume();
    Sound.startMusic();
  }

  function togglePause() {
    if (state.phase === 'playing') pauseGame();
    else if (state.phase === 'paused') resumeGame();
  }

  function setPauseIcon(paused) {
    if (pauseBtn) pauseBtn.textContent = paused ? '▶' : '❚❚';
  }

  function die() {
    state.phase = 'over';
    state.shake = 16;
    state.hitFlash = 1;
    setPauseIcon(false);
    Sound.stopMusic(0.3);
    Sound.die(state.newBest);
    const text = state.newBest ? `Новый рекорд — ${state.score}!` : `Счёт: ${state.score}`;
    showOverlay('Игра окончена', text, 'Заново');
  }

  function win() {
    state.phase = 'over';
    setPauseIcon(false);
    Sound.stopMusic(0.3);
    Sound.win();
    showOverlay('Победа!', 'Вся доска заполнена. Невероятно!', 'Заново');
  }

  function showOverlay(title, text, buttonLabel) {
    overlayTitle.textContent = title;
    overlayText.textContent = text;
    playBtn.textContent = buttonLabel;
    overlay.classList.add('is-visible');
  }

  function hideOverlay() {
    overlay.classList.remove('is-visible');
  }

  function updateSoundUi() {
    if (!soundBtn) return;
    const muted = Sound.isMuted();
    soundBtn.dataset.muted = muted ? 'true' : 'false';
    soundBtn.setAttribute('aria-pressed', String(!muted));
    soundBtn.setAttribute('aria-label', muted ? 'Включить звук' : 'Выключить звук');
    soundBtn.title = muted ? 'Включить звук (M)' : 'Выключить звук (M)';
  }

  function toggleSound() {
    if (!Sound.isSupported()) return;
    const muted = Sound.setMuted(!Sound.isMuted());
    updateSoundUi();
    if (!muted && state.phase === 'playing') {
      Sound.startMusic();
    }
  }

  // ---------- Simulation ----------

  function queueDir(dir) {
    // Repeating the current direction cancels an already buffered turn,
    // so a quick correction never causes an unwanted extra move.
    if (dir.x === state.dir.x && dir.y === state.dir.y) {
      state.pending = null;
      return;
    }
    if (dir.x === -state.dir.x && dir.y === -state.dir.y) return;
    // Latest input wins: only one turn is buffered for the next tick.
    state.pending = dir;
  }

  // While waiting on the ready screen the snake can be aimed without moving.
  function chooseReadyDir(dir) {
    if (dir.x === -state.dir.x && dir.y === -state.dir.y) return;
    state.dir = dir;
    state.pending = null;
  }

  function step() {
    if (state.pending) {
      const next = state.pending;
      state.pending = null;
      if (next.x !== -state.dir.x || next.y !== -state.dir.y) {
        state.dir = next;
      }
    }

    state.prev = state.snake.map((seg) => ({ x: seg.x, y: seg.y }));

    const head = {
      x: state.snake[0].x + state.dir.x,
      y: state.snake[0].y + state.dir.y,
    };

    if (head.x < 0 || head.y < 0 || head.x >= GRID || head.y >= GRID) {
      die();
      return;
    }
    if (state.walls.has(cellKey(head.x, head.y))) {
      die();
      return;
    }

    const willGrow = head.x === state.food.x && head.y === state.food.y;
    const body = willGrow ? state.snake : state.snake.slice(0, -1);
    if (body.some((seg) => seg.x === head.x && seg.y === head.y)) {
      die();
      return;
    }

    const foodPx = {
      x: FRAME + (state.food.x + 0.5) * state.cell,
      y: FRAME + (state.food.y + 0.5) * state.cell,
    };

    state.snake.unshift(head);
    if (willGrow) {
      state.score += 1;
      scoreEl.textContent = String(state.score);
      bumpScore();
      Sound.eat(state.score);
      spawnParticles(foodPx.x, foodPx.y, 16);

      if (state.score > state.best) {
        state.best = state.score;
        state.newBest = true;
        bestEl.textContent = String(state.best);
        saveBest(state.best);
      }

      state.stepMs = Math.max(MIN_STEP, BASE_STEP - state.score * SPEED_PER_FOOD);

      if (!placeFood()) {
        win();
      }
    } else {
      state.snake.pop();
    }
  }

  function bumpScore() {
    scoreEl.classList.remove('bump');
    void scoreEl.offsetWidth;
    scoreEl.classList.add('bump');
  }

  // ---------- Particles ----------

  function spawnParticles(x, y, count) {
    for (let i = 0; i < count; i++) {
      const angle = Math.random() * TAU;
      const speed = 0.03 + Math.random() * 0.09;
      particles.push({
        x,
        y,
        vx: Math.cos(angle) * speed,
        vy: Math.sin(angle) * speed,
        life: 1,
        size: Math.random() < 0.75 ? 1 : 2,
        color: PARTICLE_COLORS[(Math.random() * PARTICLE_COLORS.length) | 0],
      });
    }
    if (particles.length > 240) {
      particles.splice(0, particles.length - 240);
    }
  }

  function updateParticles(dt) {
    for (let i = particles.length - 1; i >= 0; i--) {
      const p = particles[i];
      p.x += p.vx * dt;
      p.y += p.vy * dt;
      p.vx *= 0.99;
      p.vy *= 0.99;
      p.life -= dt / 480;
      if (p.life <= 0) particles.splice(i, 1);
    }
  }

  // ---------- Rendering ----------

  // 20x20 apple sprite. '.' is transparent.
  const APPLE_SPRITE = [
    '....................',
    '....................',
    '.........SS.........',
    '.........SS..LLl....',
    '.........SS.LLLLl...',
    '....DDDDDDDDDDDD....',
    '...DDRRRRRRRRRRDD...',
    '..DDRRRRRRRRRRRRDD..',
    '.DDRRRRRRRRRRRRRRDD.',
    '.DRRRRRRRRRRRRRRRRD.',
    'DDRRHRRRRRRRRRRRRRDD',
    'DRRHHRRRRRRRRRRRRRRD',
    'DRRRRRRRRRRRRRRRRRRD',
    'DRRRRRRRRRRRRRRRRRRD',
    'DRRRRRRRRRRRRRRRRRRD',
    'DDRRRRRRRRRRRRRRRRDD',
    '.DRRRRRRRRRRRRRRRRD.',
    '.DDRRRRRRRRRRRRRRDD.',
    '..DDDRRRRRRRRRRDDD..',
    '....DDDDDDDDDDDD....',
  ];

  const APPLE_PALETTE = {
    L: '#7cc45c',
    l: '#4a7a38',
    S: '#6b4423',
    D: '#5c0a1e',
    R: '#d92b4b',
    H: '#ff9db0',
  };

  // Tiny twinkles around the apple; positions are relative to its top-left corner.
  const APPLE_SPARKLES = [
    { dx: -6, dy: 4, size: 3, phase: 0.2 },
    { dx: 23, dy: 7, size: 3, phase: 2.4 },
    { dx: 1, dy: -5, size: 2, phase: 4.1 },
    { dx: 16, dy: -4, size: 2, phase: 1.3 },
    { dx: 6, dy: 22, size: 3, phase: 3.5 },
    { dx: 18, dy: 20, size: 2, phase: 5.4 },
  ];

  const PARTICLE_COLORS = ['#ffb347', '#ffd166', '#c77dff', '#e0aaff', '#ff7b00'];

  const FLOOR_TONES = ['#1a1026', '#1e132b', '#221630'];
  const WALL_TONES = ['#2b183c', '#301c43', '#271534', '#35204a'];
  const WALL_LIGHTS = ['#4d2f66', '#56366f', '#46295c', '#5e3c7c'];
  const WALL_MORTAR = '#0d0714';

  const SKULL_SPRITE = [
    '.BBBB.',
    'BBBBBB',
    'BBBBBB',
    'BBBBBB',
    '.B..B.',
    '..BB..',
  ];
  const SKULL_PALETTE = { B: '#c9b6d6' };

  const TORCH_PALETTE = {
    o: '#8f2d00',
    O: '#ff6b1a',
    Y: '#ffc300',
    W: '#fff3bf',
    S: '#241626',
    H: '#4a3350',
  };

  const TORCH_FRAMES = [
    [
      '....o....',
      '...oOo...',
      '...oOo...',
      '..oOYOo..',
      '..oOYOo..',
      '.oOYYYoo.',
      '.oOYYYoo.',
      '..oOYOo..',
      '...oYo...',
      '...SSS...',
      '..SSSSS..',
      '...S.S...',
    ],
    [
      '...o.....',
      '..oOo....',
      '..oOo....',
      '.oOYOo...',
      '.oOYOo...',
      'oOYYYoo..',
      'oOYYYoo..',
      '.oOYOo...',
      '..oYo....',
      '...SSS...',
      '..SSSSS..',
      '...S.S...',
    ],
    [
      '.....o...',
      '....oOo..',
      '....oOo..',
      '...oOYOo.',
      '...oOYOo.',
      '..ooYYYoo',
      '..ooYYYoo',
      '...oOYOo.',
      '....oYo..',
      '...SSS...',
      '..SSSSS..',
      '...S.S...',
    ],
  ];

  const BAYER4 = [
    [0, 8, 2, 10],
    [12, 4, 14, 6],
    [3, 11, 1, 9],
    [15, 7, 13, 5],
  ];

  const MOTES = Array.from({ length: 26 }, (_, i) => ({
    x: (i * 71 + 23) % ART_SIZE,
    y: (i * 113 + 47) % ART_SIZE,
    drift: 3 + (i % 5) * 2,
    phase: i * 1.37,
    warm: i % 7 === 0,
  }));

  function hash2(x, y) {
    let h = Math.imul(x + 1, 374761393) ^ Math.imul(y + 1, 668265263);
    h = Math.imul(h ^ (h >>> 13), 1274126177);
    return (h ^ (h >>> 16)) >>> 0;
  }

  // Dithered, quantized light sprites keep the glow pixelated instead of smooth.
  function makeGlow(size, color, maxAlpha) {
    const c = document.createElement('canvas');
    c.width = size;
    c.height = size;
    const g = c.getContext('2d');
    const img = g.createImageData(size, size);
    const data = img.data;
    const half = size / 2;
    const [r, gr, b] = color;

    for (let y = 0; y < size; y++) {
      for (let x = 0; x < size; x++) {
        const dx = (x + 0.5 - half) / half;
        const dy = (y + 0.5 - half) / half;
        const d = Math.sqrt(dx * dx + dy * dy);
        if (d >= 1) continue;

        const falloff = (1 - d) * (1 - d);
        const threshold = BAYER4[y % 4][x % 4] / 16;
        const q = Math.min(
          maxAlpha,
          Math.floor(falloff * maxAlpha * 6 + threshold) / 6
        );
        if (q <= 0) continue;

        const i = (y * size + x) * 4;
        data[i] = r;
        data[i + 1] = gr;
        data[i + 2] = b;
        data[i + 3] = Math.round(Math.min(1, q) * 255);
      }
    }

    g.putImageData(img, 0, 0);
    return c;
  }

  function makeVignette(size) {
    const c = document.createElement('canvas');
    c.width = size;
    c.height = size;
    const g = c.getContext('2d');
    const img = g.createImageData(size, size);
    const data = img.data;
    const half = size / 2;
    const maxDist = Math.hypot(half, half);

    for (let y = 0; y < size; y++) {
      for (let x = 0; x < size; x++) {
        const dx = x + 0.5 - half;
        const dy = y + 0.5 - half;
        const d = Math.hypot(dx, dy) / maxDist;
        const threshold = BAYER4[y % 4][x % 4] / 16;
        const q =
          Math.floor(Math.max(0, d - 0.42) * 0.8 * 5 + threshold) / 5;
        if (q <= 0) continue;

        const i = (y * size + x) * 4;
        data[i] = 8;
        data[i + 1] = 2;
        data[i + 2] = 16;
        data[i + 3] = Math.round(Math.min(1, q) * 255);
      }
    }

    g.putImageData(img, 0, 0);
    return c;
  }

  // A quarter-web for a wall corner. Each ring is slightly warped.
  function makeWeb(size, rings = 4, rayCount = 5) {
    const c = document.createElement('canvas');
    c.width = size;
    c.height = size;
    const g = c.getContext('2d');
    const rays = [];
    for (let i = 0; i < rayCount; i++) {
      rays.push((Math.PI / 2) * (i / (rayCount - 1)));
    }

    for (const angle of rays) {
      for (let r = 2; r < size; r++) {
        const x = Math.round(Math.cos(angle) * r);
        const y = Math.round(Math.sin(angle) * r);
        if (x >= size || y >= size) break;
        g.fillStyle =
          r % 8 === 0
            ? 'rgba(210, 195, 225, 0.7)'
            : 'rgba(160, 140, 180, 0.45)';
        g.fillRect(x, y, 1, 1);
      }
    }

    const step = (size - 1) / (rings + 0.4);
    for (let ring = 1; ring <= rings; ring++) {
      const radius = step * ring;
      for (let a = 0; a <= Math.PI / 2 + 0.001; a += 0.025) {
        const r = radius + Math.sin(a * 5 + ring) * 0.7;
        const x = Math.round(Math.cos(a) * r);
        const y = Math.round(Math.sin(a) * r);
        if (x >= size || y >= size) continue;
        if ((x * 11 + y * 7 + ring * 3) % 23 === 0) continue;
        g.fillStyle = 'rgba(150, 130, 172, 0.4)';
        g.fillRect(x, y, 1, 1);
      }
    }

    g.fillStyle = 'rgba(220, 205, 235, 0.8)';
    g.fillRect(0, 0, 2, 1);
    g.fillRect(0, 0, 1, 2);
    return c;
  }

  const TORCH_GLOW = makeGlow(96, [255, 138, 46], 0.55);
  const VIGNETTE = makeVignette(ART_SIZE);
  const WEB_CORNER = makeWeb(24, 4, 5);
  const WEB_SMALL = makeWeb(14, 3, 3);

  const GLOOM = document.createElement('canvas');
  GLOOM.width = ART_SIZE;
  GLOOM.height = ART_SIZE;
  const gloomCtx = GLOOM.getContext('2d');

  // Darkness between the torch pools. Rebuilt whenever a run places its torches.
  function buildGloom() {
    const lights = state.torches.map((torch) => ({
      x: FRAME + torch.x * state.cell + state.cell / 2,
      y: FRAME + torch.y * state.cell + state.cell * 0.55,
    }));

    const img = gloomCtx.createImageData(ART_SIZE, ART_SIZE);
    const data = img.data;

    if (lights.length === 0) {
      gloomCtx.clearRect(0, 0, ART_SIZE, ART_SIZE);
      return;
    }

    for (let y = 0; y < ART_SIZE; y++) {
      for (let x = 0; x < ART_SIZE; x++) {
        let nearest = Infinity;
        for (const light of lights) {
          const dx = x + 0.5 - light.x;
          const dy = y + 0.5 - light.y;
          const d = dx * dx + dy * dy;
          if (d < nearest) nearest = d;
        }

        const shade = Math.min(
          1,
          Math.max(0, (Math.sqrt(nearest) - 58) / 130)
        );
        if (shade <= 0) continue;

        const threshold = BAYER4[y % 4][x % 4] / 16;
        const alpha =
          (Math.min(5, Math.floor(shade * 5 + threshold)) / 5) * 0.42;
        if (alpha <= 0) continue;

        const i = (y * ART_SIZE + x) * 4;
        data[i] = 6;
        data[i + 1] = 3;
        data[i + 2] = 12;
        data[i + 3] = Math.round(alpha * 255);
      }
    }

    gloomCtx.putImageData(img, 0, 0);
  }

  function drawGloom() {
    if (state.torches.length === 0) return;
    ctx.drawImage(GLOOM, 0, 0);
  }

  function drawSprite(sprite, palette, x, y) {
    for (let row = 0; row < sprite.length; row++) {
      const line = sprite[row];
      for (let col = 0; col < line.length; col++) {
        const color = palette[line[col]];
        if (!color) continue;
        ctx.fillStyle = color;
        ctx.fillRect(x + col, y + row, 1, 1);
      }
    }
  }

  function drawBackground() {
    const { size, cell } = state;

    ctx.fillStyle = '#0b0612';
    ctx.fillRect(0, 0, size, size);

    for (let gy = 0; gy < GRID; gy++) {
      for (let gx = 0; gx < GRID; gx++) {
        const x = FRAME + gx * cell;
        const y = FRAME + gy * cell;
        const h = hash2(gx, gy);

        ctx.fillStyle = FLOOR_TONES[h % FLOOR_TONES.length];
        ctx.fillRect(x, y, cell, cell);

        // Mortar grid.
        ctx.fillStyle = '#0c0714';
        ctx.fillRect(x, y, cell, 1);
        ctx.fillRect(x, y, 1, cell);

        // Worn stone highlights.
        if (h % 5 === 0) {
          ctx.fillStyle = '#2c1d3e';
          ctx.fillRect(x + 3, y + 3, 4, 1);
          ctx.fillRect(x + 2, y + 4, 1, 1);
        }

        // Cracks.
        if (h % 9 === 0) {
          ctx.fillStyle = '#0a0611';
          ctx.fillRect(x + 5, y + 4, 1, 3);
          ctx.fillRect(x + 6, y + 7, 1, 3);
          ctx.fillRect(x + 7, y + 10, 1, 2);
        }

        // Damp moss in the seams.
        if (h % 11 === 0) {
          ctx.fillStyle = '#33493a';
          ctx.fillRect(x + 10, y + 12, 4, 1);
          ctx.fillRect(x + 12, y + 10, 2, 2);
          ctx.fillStyle = '#456150';
          ctx.fillRect(x + 12, y + 10, 1, 1);
        }
      }
    }

    // Recessed seam where the flagstones meet the wall ring.
    ctx.fillStyle = 'rgba(4, 2, 9, 0.55)';
    ctx.fillRect(FRAME, FRAME, FIELD_SIZE, 1);
    ctx.fillRect(FRAME, FRAME + FIELD_SIZE - 1, FIELD_SIZE, 1);
    ctx.fillRect(FRAME, FRAME, 1, FIELD_SIZE);
    ctx.fillRect(FRAME + FIELD_SIZE - 1, FRAME, 1, FIELD_SIZE);
  }

  function drawWallCell(x, y, h) {
    const { cell } = state;
    const tone = h % WALL_TONES.length;

    ctx.fillStyle = WALL_MORTAR;
    ctx.fillRect(x, y, cell, cell);
    ctx.fillStyle = WALL_TONES[tone];
    ctx.fillRect(x + 1, y + 1, cell - 2, cell - 2);

    // Purple-lit bevel.
    ctx.fillStyle = WALL_LIGHTS[tone];
    ctx.fillRect(x + 1, y + 1, cell - 2, 1);
    ctx.fillRect(x + 1, y + 1, 1, cell - 2);
    ctx.fillStyle = '#170c21';
    ctx.fillRect(x + 1, y + cell - 2, cell - 2, 1);
    ctx.fillRect(x + cell - 2, y + 1, 1, cell - 2);

    // Offset brick courses.
    ctx.fillStyle = '#120a1c';
    ctx.fillRect(x + 1, y + 8, cell - 2, 1);
    ctx.fillRect(x + 8, y + 1, 1, 7);
    ctx.fillRect(x + 4, y + 9, 1, 6);

    // A faint arcane glint.
    if (h % 3 === 0) {
      ctx.fillStyle = '#6b4a8a';
      ctx.fillRect(x + 3, y + 3, 2, 1);
      ctx.fillRect(x + 11, y + 11, 1, 1);
    }

    // Weathering.
    if (h % 4 === 0) {
      ctx.fillStyle = '#170c21';
      ctx.fillRect(x + 10, y + 3, 1, 2);
      ctx.fillRect(x + 11, y + 5, 1, 2);
    }
    if (h % 7 === 0) {
      ctx.fillStyle = '#3f5b45';
      ctx.fillRect(x + 2, y + 12, 2, 1);
      ctx.fillStyle = '#557a5b';
      ctx.fillRect(x + 3, y + 11, 1, 1);
    }
    if (h % 13 === 0) {
      drawSprite(SKULL_SPRITE, SKULL_PALETTE, x + 5, y + 5);
      ctx.fillStyle = '#170c20';
      ctx.fillRect(x + 6, y + 7, 1, 1);
      ctx.fillRect(x + 9, y + 7, 1, 1);
      ctx.fillRect(x + 7, y + 8, 2, 1);
    }
  }

  // The map edge is a one-cell wall ring around the playfield.
  function drawFrameWalls() {
    const { cell } = state;

    for (let gx = -1; gx <= GRID; gx++) {
      drawWallCell(FRAME + gx * cell, 0, hash2(gx + 53, 211));
      drawWallCell(
        FRAME + gx * cell,
        FRAME + GRID * cell,
        hash2(gx + 53, 307)
      );
    }

    for (let gy = 0; gy < GRID; gy++) {
      drawWallCell(0, FRAME + gy * cell, hash2(401, gy + 53));
      drawWallCell(
        FRAME + GRID * cell,
        FRAME + gy * cell,
        hash2(503, gy + 53)
      );
    }
  }

  function drawWalls() {
    const { cell } = state;

    drawFrameWalls();

    for (const key of state.walls) {
      const gx = key % GRID;
      const gy = (key / GRID) | 0;
      const x = FRAME + gx * cell;
      const y = FRAME + gy * cell;
      drawWallCell(x, y, hash2(gx + 31, gy + 17));
    }
  }

  function drawWeb(sprite, x, y, flipX, flipY, alpha = 1) {
    ctx.save();
    ctx.globalAlpha = alpha;
    ctx.translate(x, y);
    ctx.scale(flipX ? -1 : 1, flipY ? -1 : 1);
    ctx.drawImage(sprite, 0, 0);
    ctx.restore();
  }

  function drawCobwebs() {
    const { cell } = state;

    drawWeb(WEB_CORNER, FRAME, FRAME, false, false, 0.9);
    drawWeb(WEB_CORNER, FRAME + FIELD_SIZE, FRAME, true, false, 0.9);
    drawWeb(WEB_CORNER, FRAME, FRAME + FIELD_SIZE, false, true, 0.9);
    drawWeb(
      WEB_CORNER,
      FRAME + FIELD_SIZE,
      FRAME + FIELD_SIZE,
      true,
      true,
      0.9
    );

    const webWalls = [];
    for (const key of state.walls) {
      const gx = key % GRID;
      const gy = (key / GRID) | 0;
      if (
        state.torches.some(
          (t) => Math.abs(t.x - gx) + Math.abs(t.y - gy) <= 1
        )
      ) {
        continue;
      }
      if (hash2(gx + 31, gy + 17) % 13 === 0) continue;
      webWalls.push({ gx, gy, h: hash2(gx + 91, gy + 41) });
    }

    webWalls.sort((a, b) => a.h - b.h);
    for (let i = 0; i < Math.min(3, webWalls.length); i++) {
      const { gx, gy, h } = webWalls[i];
      const x = FRAME + gx * cell;
      const y = FRAME + gy * cell;
      const flipX = (h & 2) !== 0;
      const flipY = (h & 4) !== 0;
      drawWeb(
        WEB_SMALL,
        flipX ? x + cell : x,
        flipY ? y + cell : y,
        flipX,
        flipY,
        0.7
      );
    }
  }

  function drawGoldPile(x, y, h, time) {
    const spots = [
      [0, 0],
      [4, 1],
      [1, 3],
      [5, 3],
    ];
    const count = 2 + (h % 3);

    for (let i = 0; i < count; i++) {
      const ox = spots[i][0] + ((h >> (i + 4)) & 1);
      const oy = spots[i][1];

      ctx.fillStyle = '#5c4210';
      ctx.fillRect(x + ox, y + oy + 1, 3, 2);
      ctx.fillStyle = i % 2 === 0 ? '#c9a227' : '#e0b93a';
      ctx.fillRect(x + ox, y + oy, 3, 1);
      ctx.fillStyle = '#ffe27a';
      ctx.fillRect(x + ox, y + oy, 1, 1);
    }

    if ((Math.floor(time / 700) + h) % 7 === 0) {
      ctx.fillStyle = '#fff6c9';
      ctx.fillRect(x + 1, y, 1, 1);
    }
  }

  function drawGold(time) {
    const { cell } = state;

    for (let gy = 1; gy < GRID - 1; gy++) {
      for (let gx = 1; gx < GRID - 1; gx++) {
        if (isSpawnSafe(gx, gy)) continue;
        if (state.walls.has(cellKey(gx, gy))) continue;

        const h = hash2(gx + 173, gy + 89);
        if (h % 17 !== 0) continue;

        const nearWall =
          gx === 1 ||
          gy === 1 ||
          gx === GRID - 2 ||
          gy === GRID - 2 ||
          state.walls.has(cellKey(gx - 1, gy)) ||
          state.walls.has(cellKey(gx + 1, gy)) ||
          state.walls.has(cellKey(gx, gy - 1)) ||
          state.walls.has(cellKey(gx, gy + 1));
        if (!nearWall) continue;

        const x = FRAME + gx * cell + 2 + (h % 3);
        const y = FRAME + gy * cell + 9 + ((h >> 3) % 3);
        drawGoldPile(x, y, h, time);
      }
    }
  }

  function drawDecor(time) {
    drawCobwebs();
    drawGold(time);
  }

  function drawTorchLight(time) {
    if (state.torches.length === 0) return;

    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    for (const torch of state.torches) {
      const flicker =
        0.86 +
        0.09 * Math.sin(time / 90 + torch.seed) +
        0.05 * Math.sin(time / 37 + torch.seed * 2.3);
      const cx = Math.round(FRAME + torch.x * state.cell + state.cell / 2);
      const cy = Math.round(FRAME + torch.y * state.cell + state.cell * 0.55);

      ctx.globalAlpha = 0.52 * flicker;
      ctx.drawImage(TORCH_GLOW, cx - 60, cy - 46, 120, 92);

      ctx.globalAlpha = 0.24 * flicker;
      ctx.drawImage(TORCH_GLOW, cx - 30, cy - 30, 60, 60);
    }
    ctx.restore();
  }

  function drawTorches(time) {
    if (state.torches.length === 0) return;
    const { cell } = state;

    for (const torch of state.torches) {
      const x = FRAME + torch.x * cell + 3;
      const y = FRAME + torch.y * cell + 2;
      const frame = Math.floor(time / 130 + torch.seed) % TORCH_FRAMES.length;
      drawSprite(TORCH_FRAMES[frame], TORCH_PALETTE, x, y);

      // Embers drift up from the flame.
      for (let k = 0; k < 3; k++) {
        const phase = (time / 850 + torch.seed * 0.17 + k * 0.31) % 1;
        const ex = Math.round(
          FRAME +
            torch.x * cell +
            8 +
            Math.sin(time / 240 + k * 2 + torch.seed) * 4
        );
        const ey = Math.round(
          FRAME + torch.y * cell + 7 - phase * 16
        );
        if (ey < FRAME + torch.y * cell - 1) continue;

        ctx.globalAlpha = (1 - phase) * 0.9;
        ctx.fillStyle = k === 0 ? '#ffe08a' : '#ff8c1a';
        ctx.fillRect(ex, ey, 1, 1);
      }
      ctx.globalAlpha = 1;
    }
  }

  function drawMotes(time) {
    for (const mote of MOTES) {
      const y = (mote.y - (time * mote.drift) / 1000) % ART_SIZE;
      const yy = y < 0 ? y + ART_SIZE : y;
      const x = mote.x + Math.round(Math.sin(time / 2400 + mote.phase) * 5);

      ctx.globalAlpha = 0.16 + 0.1 * Math.sin(time / 700 + mote.phase);
      ctx.fillStyle = mote.warm ? '#ffb86b' : '#b98ad6';
      ctx.fillRect(Math.round(x), Math.round(yy), 1, 1);
    }
    ctx.globalAlpha = 1;
  }

  function drawSparkle(px, py, size, alpha) {
    ctx.globalAlpha = alpha;
    ctx.fillStyle = '#ffd76a';
    ctx.fillRect(px - size, py, size * 2 + 1, 1);
    ctx.fillRect(px, py - size, 1, size * 2 + 1);
    ctx.fillStyle = '#fff8d8';
    ctx.fillRect(px, py, 1, 1);
    ctx.globalAlpha = alpha * 0.7;
    ctx.fillRect(px - 1, py - 1, 1, 1);
    ctx.fillRect(px + 1, py - 1, 1, 1);
    ctx.fillRect(px - 1, py + 1, 1, 1);
    ctx.fillRect(px + 1, py + 1, 1, 1);
  }

  function drawFood(time) {
    const { cell } = state;
    const bob = Math.floor(time / 360) % 2;
    const cx = FRAME + (state.food.x + 0.5) * cell;
    const cy = FRAME + (state.food.y + 0.5) * cell;
    const width = APPLE_SPRITE[0].length;
    const height = APPLE_SPRITE.length;
    const x = Math.round(cx - width / 2);
    const y = Math.round(cy - height / 2) + 1 - bob;

    drawSprite(APPLE_SPRITE, APPLE_PALETTE, x, y);

    // Tiny twinkles around the apple, plus a blinking highlight on its skin.
    ctx.save();
    ctx.globalCompositeOperation = 'lighter';
    for (const sparkle of APPLE_SPARKLES) {
      const wave = Math.sin(time / 210 + sparkle.phase);
      if (wave < 0.55) continue;
      const alpha = Math.pow((wave - 0.55) / 0.45, 1.6);
      drawSparkle(x + sparkle.dx, y + sparkle.dy, sparkle.size, alpha);
    }

    const glint = Math.sin(time / 170 + 1.7);
    if (glint > 0.8) {
      ctx.globalAlpha = (glint - 0.8) / 0.2;
      ctx.fillStyle = '#fffbe8';
      ctx.fillRect(x + 4, y + 10, 2, 1);
      ctx.fillRect(x + 3, y + 11, 1, 1);
    }
    ctx.restore();
  }

  function drawSnake(time) {
    const { cell } = state;
    const t = state.phase === 'playing' ? Math.min(1, state.acc / state.stepMs) : 1;
    const n = state.snake.length;
    const positions = state.snake.map((seg, i) => {
      const from = state.prev[i] || seg;
      return {
        x: Math.round(FRAME + (from.x + (seg.x - from.x) * t) * cell),
        y: Math.round(FRAME + (from.y + (seg.y - from.y) * t) * cell),
      };
    });

    for (let i = n - 1; i >= 0; i--) {
      const { x, y } = positions[i];
      const isHead = i === 0;

      ctx.fillStyle = isHead ? '#120a1c' : '#0c0614';
      ctx.fillRect(x + 1, y + 1, 14, 14);

      ctx.fillStyle = isHead ? '#9ef0a8' : i % 2 === 0 ? '#3fbf5a' : '#36a94e';
      ctx.fillRect(x + 2, y + 2, 12, 12);

      ctx.fillStyle = isHead ? '#d8ffe0' : '#7ce38b';
      ctx.fillRect(x + 3, y + 3, 3, 1);
      ctx.fillRect(x + 3, y + 4, 1, 1);

      if (!isHead) {
        ctx.fillStyle = '#2a8340';
        ctx.fillRect(x + 8, y + 7, 2, 2);
      }

      ctx.fillStyle = isHead ? '#5fd374' : '#1d7a35';
      ctx.fillRect(x + 3, y + 13, 10, 1);
    }

    // Fill the seams between adjacent cells so the body reads as one snake.
    for (let i = 0; i < n - 1; i++) {
      const a = positions[i];
      const b = positions[i + 1];
      const color = i === 0 ? '#5fd374' : i % 2 === 0 ? '#3fbf5a' : '#36a94e';

      if (a.x === b.x && Math.abs(a.y - b.y) === cell) {
        ctx.fillStyle = color;
        ctx.fillRect(a.x + 2, Math.min(a.y, b.y) + 14, 12, 4);
      } else if (a.y === b.y && Math.abs(a.x - b.x) === cell) {
        ctx.fillStyle = color;
        ctx.fillRect(Math.min(a.x, b.x) + 14, a.y + 2, 4, 12);
      }
    }

    const hx = positions[0].x;
    const hy = positions[0].y;
    const dir = state.dir;

    // Forked tongue flickers while the snake is moving.
    if (state.phase === 'playing' && Math.floor(time / 200) % 2 === 0) {
      ctx.fillStyle = '#ff4d6d';
      if (dir.x === 1) {
        ctx.fillRect(hx + 15, hy + 7, 2, 2);
        ctx.fillRect(hx + 17, hy + 6, 1, 1);
        ctx.fillRect(hx + 17, hy + 9, 1, 1);
      } else if (dir.x === -1) {
        ctx.fillRect(hx - 1, hy + 7, 2, 2);
        ctx.fillRect(hx - 2, hy + 6, 1, 1);
        ctx.fillRect(hx - 2, hy + 9, 1, 1);
      } else if (dir.y === -1) {
        ctx.fillRect(hx + 7, hy - 1, 2, 2);
        ctx.fillRect(hx + 6, hy - 2, 1, 1);
        ctx.fillRect(hx + 9, hy - 2, 1, 1);
      } else {
        ctx.fillRect(hx + 7, hy + 15, 2, 2);
        ctx.fillRect(hx + 6, hy + 17, 1, 1);
        ctx.fillRect(hx + 9, hy + 17, 1, 1);
      }
    }

    const eye = (ex, ey) => {
      ctx.fillStyle = '#0a0510';
      ctx.fillRect(ex, ey, 3, 3);
      ctx.fillStyle = '#fff3bf';
      ctx.fillRect(ex, ey, 1, 1);
    };

    if (dir.x === 1) {
      eye(hx + 10, hy + 4);
      eye(hx + 10, hy + 9);
    } else if (dir.x === -1) {
      eye(hx + 3, hy + 4);
      eye(hx + 3, hy + 9);
    } else if (dir.y === -1) {
      eye(hx + 4, hy + 3);
      eye(hx + 9, hy + 3);
    } else {
      eye(hx + 4, hy + 10);
      eye(hx + 9, hy + 10);
    }
  }

  function drawParticles() {
    for (const p of particles) {
      ctx.globalAlpha = Math.max(0, Math.min(1, p.life));
      ctx.fillStyle = p.color;
      ctx.fillRect(Math.round(p.x), Math.round(p.y), p.size, p.size);
    }
    ctx.globalAlpha = 1;
  }

  function draw(time) {
    const { size } = state;
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.clearRect(0, 0, size, size);

    drawBackground();

    ctx.save();
    if (state.shake > 0.2) {
      ctx.translate(
        Math.round((Math.random() * 2 - 1) * state.shake),
        Math.round((Math.random() * 2 - 1) * state.shake * 0.7)
      );
    }
    drawWalls();
    drawGloom();
    drawDecor(time);
    drawFood(time);
    drawSnake(time);
    drawParticles();
    drawTorchLight(time);
    drawTorches(time);
    ctx.restore();

    drawMotes(time);
    ctx.drawImage(VIGNETTE, 0, 0);

    if (state.hitFlash > 0.01) {
      ctx.fillStyle = `rgba(190, 60, 90, ${0.3 * state.hitFlash})`;
      ctx.fillRect(0, 0, size, size);
    }
  }

  // ---------- Main loop ----------

  let lastTime = performance.now();

  function frame(now) {
    const dt = Math.min(now - lastTime, 60);
    lastTime = now;

    updateParticles(dt);
    if (state.shake > 0) state.shake = Math.max(0, state.shake - dt * 0.035);
    if (state.hitFlash > 0) state.hitFlash = Math.max(0, state.hitFlash - dt * 0.0016);

    if (state.phase === 'playing') {
      state.acc += dt;
      let guard = 0;
      while (state.acc >= state.stepMs && guard < 3) {
        state.acc -= state.stepMs;
        step();
        guard += 1;
        if (state.phase !== 'playing') {
          state.acc = 0;
          break;
        }
      }
    }

    draw(now);
    requestAnimationFrame(frame);
  }

  // ---------- Input ----------

  window.addEventListener('keydown', (event) => {
    const key = event.key && event.key.length === 1 ? event.key.toLowerCase() : event.key;

    if (event.code === 'KeyM' || key === 'm' || key === 'ь') {
      event.preventDefault();
      if (!event.repeat) toggleSound();
      return;
    }

    const dir = KEY_DIRS[event.code] || KEY_DIRS[key];
    if (dir) {
      event.preventDefault();
      if (state.phase === 'playing') queueDir(dir);
      else if (state.phase === 'ready') chooseReadyDir(dir);
      return;
    }

    if (event.code === 'Space' || key === ' ') {
      event.preventDefault();
      if (state.phase === 'ready') beginRun();
      else if (state.phase === 'idle' || state.phase === 'over') startGame(true);
      else togglePause();
      return;
    }

    if (event.code === 'Enter' || key === 'Enter') {
      event.preventDefault();
      if (state.phase === 'ready') beginRun();
      else startGame(true);
      return;
    }

    if (event.code === 'KeyR' || key === 'r') {
      event.preventDefault();
      if (state.phase === 'ready') beginRun();
      else startGame(true);
    }
  });

  playBtn.addEventListener('click', () => {
    playBtn.blur();
    if (state.phase === 'paused') resumeGame();
    else if (state.phase === 'ready') beginRun();
    else startGame();
  });

  if (soundBtn) {
    if (Sound.isSupported()) {
      updateSoundUi();
      soundBtn.addEventListener('click', toggleSound);
    } else {
      soundBtn.hidden = true;
    }
  }

  document.querySelectorAll('[data-dir]').forEach((button) => {
    button.addEventListener('pointerdown', (event) => {
      event.preventDefault();
      const dir = DPAD_DIRS[button.dataset.dir];
      if (!dir) return;
      if (state.phase === 'playing') queueDir(dir);
      else if (state.phase === 'ready') chooseReadyDir(dir);
    });
  });

  if (pauseBtn) {
    pauseBtn.addEventListener('pointerdown', (event) => {
      event.preventDefault();
      togglePause();
    });
  }

  canvas.addEventListener('pointerdown', (event) => {
    swipe.active = true;
    swipe.x = event.clientX;
    swipe.y = event.clientY;
    swipe.pointerId = event.pointerId;
    if (canvas.setPointerCapture) {
      try {
        canvas.setPointerCapture(event.pointerId);
      } catch {
        /* pointer capture is optional */
      }
    }
  });

  canvas.addEventListener('pointerup', (event) => {
    if (!swipe.active) return;
    swipe.active = false;
    if (swipe.pointerId !== null && event.pointerId !== swipe.pointerId) return;

    const dx = event.clientX - swipe.x;
    const dy = event.clientY - swipe.y;
    if (Math.hypot(dx, dy) < 24) return;
    if (state.phase !== 'playing') return;

    if (Math.abs(dx) > Math.abs(dy)) {
      queueDir({ x: Math.sign(dx), y: 0 });
    } else {
      queueDir({ x: 0, y: Math.sign(dy) });
    }
  });

  canvas.addEventListener('pointercancel', () => {
    swipe.active = false;
  });

  document.addEventListener('visibilitychange', () => {
    if (document.hidden) pauseGame();
  });

  // ---------- Boot ----------

  canvas.width = ART_SIZE;
  canvas.height = ART_SIZE;
  ctx.imageSmoothingEnabled = false;

  bestEl.textContent = String(state.best);
  reset();
  requestAnimationFrame(frame);
})();
