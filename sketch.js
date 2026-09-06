// ============================================================================
// TABLETOP SPATIAL AUDIO ENGINE — color-tracked oscillators
// ============================================================================
// What this does, in plain terms:
//   An overhead camera watches a table. Each color swatch you place on it is
//   matched against a list of known HSV targets below. Every matched swatch
//   gets its own oscillator (its "voice"). Where you put it, how tall a
//   pillar you set it on, and how close it sits to other swatches all change
//   how that voice sounds:
//
//     table X position  -> stereo pan (left/right)
//     table Y position   -> how much of the voice goes to the shared reverb
//     blob size (pillar height) -> volume
//     distance to nearest other swatch -> pitch (jumps up a fifth when close),
//                                          and it opens the shared filter
//
// Signal path for one voice:
//   Oscillator -> pan (built into the oscillator) -> splits into:
//       dry path  -> straight to the speakers
//       wet path  -> shared BandPass filter -> shared Reverb -> speakers
//   The dry/wet split is what makes Y position feel like "distance/depth" —
//   a single shared reverb can't give every voice its own private send, so
//   each voice keeps its own pair of gain knobs (dryGain/wetGain) that blend
//   between "straight to the room" and "through the reverb bus".
//
// About the two extra libraries loaded in index.html (ml5, soundfont-player):
//   They're loaded per the library list this spec asked for, but the actual
//   tracking here is done with plain HSV pixel thresholding (more precise
//   and controllable for a fixed, calibrated set of physical swatches than a
//   generic ml5 detector would be), and the voices are plain oscillators
//   rather than sampled instruments. Nothing below calls into ml5 or
//   soundfont-player — they're just there if you want to extend this later.
//
// Requires a click/tap before any sound happens (browsers won't let audio
// start on its own) and a local server over http://localhost (or https on a
// phone) so the camera permission prompt works at all.
// ============================================================================


// ----------------------------------------------------------------------------
// TUNABLE SETTINGS — adjust these to fit your room, lighting, and table
// ----------------------------------------------------------------------------

const PIXEL_STEP = 4;          // check every Nth pixel instead of all of them (speed vs. accuracy)

const HUE_TOLERANCE = 15;      // degrees either side of a swatch's target hue that still count as a match
const SAT_TOLERANCE = 22;      // percent either side of target saturation
const VAL_TOLERANCE = 22;      // percent either side of target value/brightness

const AREA_MIN = 200;          // matched-pixel area below this = "nothing there", voice fades out
const AREA_MAX = 2500;         // matched-pixel area at or above this = full pillar height, max volume
const MIN_VOLUME = 0.15;
const MAX_VOLUME = 0.85;

const HARMONIZE_DISTANCE = 50; // px between two swatches' centers before they harmonize (~5cm on most tables)

const PAN_SMOOTHING = 0.15;    // how fast panning catches up to a moving blob (0-1, higher = snappier)
const DEPTH_SMOOTHING = 0.1;   // same idea, for the reverb send amount

const AMP_RAMP_TIME = 0.25;    // seconds — volume fade in/out, avoids clicks
const FREQ_RAMP_TIME = 0.3;    // seconds — pitch glide when harmonizing kicks in or releases
const DEPTH_RAMP_TIME = 0.3;   // seconds — dry/wet gain change
const FILTER_RAMP_TIME = 0.2;  // seconds — shared filter sweep speed

const FILTER_FREQ_NEAR = 4000; // filter cutoff when swatches are close together (bright/open)
const FILTER_FREQ_FAR = 600;   // filter cutoff when nothing is close (dull/closed)
const FILTER_RES_NEAR = 20;    // resonance when close (more "wow")
const FILTER_RES_FAR = 2;      // resonance baseline

const REVERB_SECONDS = 2;      // length of the shared reverb tail
const REVERB_DECAY = 2;        // decay rate of that tail


// ----------------------------------------------------------------------------
// COLOR TARGETS — one entry per physical swatch, plus its musical identity.
// Frequencies are a two-octave pentatonic scale (C D E G A x3), so any two
// voices sound pleasant together and the "jump up a fifth" harmonize trick
// in SwatchVoice.updateSound() always lands on a note in the same scale.
// Oscillator type follows how dark/light the swatch is: bright = sine (pure),
// darker = square/sawtooth (grittier) — just a starting point, change freely.
// ----------------------------------------------------------------------------

const SWATCH_DATA = [
  { name: "Panna Cotta", h: 45,  s: 12, v: 82, freq: 130.81, wave: "sine"     },
  { name: "White",       h: 50,  s: 5,  v: 86, freq: 146.83, wave: "sine"     },
  { name: "Cappuccino",  h: 32,  s: 26, v: 62, freq: 164.81, wave: "triangle" },
  { name: "Chocolate",   h: 15,  s: 22, v: 24, freq: 196.00, wave: "square"   },
  { name: "Mustard",     h: 38,  s: 58, v: 72, freq: 220.00, wave: "sine"     },
  { name: "Olive",       h: 80,  s: 32, v: 30, freq: 261.63, wave: "sawtooth" },
  { name: "Grey",        h: 0,   s: 0,  v: 42, freq: 293.66, wave: "sawtooth" },
  { name: "Black",       h: 0,   s: 0,  v: 16, freq: 329.63, wave: "square"   },
  { name: "Cognac",      h: 22,  s: 74, v: 72, freq: 392.00, wave: "sine"     },
  { name: "Bordeaux",    h: 10,  s: 65, v: 50, freq: 440.00, wave: "triangle" },
  { name: "Oyster",      h: 0,   s: 3,  v: 80, freq: 523.25, wave: "sine"     },
  { name: "Ash Rose",    h: 355, s: 22, v: 74, freq: 587.33, wave: "sine"     },
  { name: "Sky Blue",    h: 198, s: 24, v: 62, freq: 659.25, wave: "triangle" },
  { name: "Eucalyptus",  h: 145, s: 26, v: 46, freq: 783.99, wave: "triangle" }
];


// ----------------------------------------------------------------------------
// GLOBALS
// ----------------------------------------------------------------------------

let video;              // the overhead camera feed
let swatches = [];       // one SwatchVoice per row in SWATCH_DATA
let audioReady = false;  // becomes true once the user has clicked and the audio context is unlocked

let globalFilter;  // shared p5.BandPass — every voice's wet path runs through this
let globalReverb;  // shared p5.Reverb — sits after the filter


// ----------------------------------------------------------------------------
// SwatchVoice — one physical color swatch and the oscillator that plays it
// ----------------------------------------------------------------------------

class SwatchVoice {
  constructor(name, hue, sat, val, baseFreq, waveType) {
    this.name = name;
    this.targetH = hue;
    this.targetS = sat;
    this.targetV = val;
    this.baseFreq = baseFreq;
    this.waveType = waveType;

    // pixel accumulator — reset and refilled once per frame by scanTableForColors()
    this.sumX = 0;
    this.sumY = 0;
    this.count = 0;

    // this frame's tracking result
    this.rawArea = 0;
    this.active = false;
    this.canvasX = 0;
    this.canvasY = 0;
    this.tableX = 0; // table coordinates: center of the frame = 0,0
    this.tableY = 0;

    // smoothed control values, so a jittery blob doesn't zipper the sound
    this.smoothedPan = 0;
    this.smoothedWet = 0;

    // audio nodes stay null until createAudioChain() runs, after the user clicks
    this.osc = null;
    this.dryGain = null;
    this.wetGain = null;
  }

  // Builds this voice's oscillator and its dry/wet split. Only ever called
  // from inside startAudioEngine(), which itself only runs from a click —
  // this is what keeps oscillator creation "lazy" per the audio-safety rule.
  createAudioChain() {
    this.osc = new p5.Oscillator(this.baseFreq, this.waveType);
    this.osc.amp(0);   // silent until a matching blob actually shows up
    this.osc.start();
    this.osc.disconnect(); // cut its default straight-to-speakers connection

    this.dryGain = new p5.Gain();
    this.wetGain = new p5.Gain();
    this.dryGain.setInput(this.osc);
    this.wetGain.setInput(this.osc);
    this.dryGain.connect();            // dry path: straight to the speakers
    this.wetGain.connect(globalFilter); // wet path: into Filter -> Reverb -> speakers
    this.dryGain.amp(1);
    this.wetGain.amp(0);
  }

  resetFrame() {
    this.sumX = 0;
    this.sumY = 0;
    this.count = 0;
  }

  // Turns this frame's pixel matches into a centroid and an area estimate.
  finishFrame() {
    if (this.count > 0) {
      // we only sampled every PIXEL_STEP pixels, so scale the count back up
      // to estimate the real on-screen area of the blob
      this.rawArea = this.count * PIXEL_STEP * PIXEL_STEP;
      this.canvasX = this.sumX / this.count;
      this.canvasY = this.sumY / this.count;
      this.tableX = this.canvasX - width / 2;
      this.tableY = this.canvasY - height / 2;
    } else {
      this.rawArea = 0;
    }
    this.active = this.rawArea >= AREA_MIN;
  }

  // Pushes this frame's tracking result into the actual sound.
  // nearestDist = distance in pixels to the closest OTHER active swatch.
  updateSound(nearestDist) {
    // X position -> pan
    let targetPan = constrain(map(this.tableX, -width / 2, width / 2, -1, 1), -1, 1);
    this.smoothedPan = lerp(this.smoothedPan, targetPan, PAN_SMOOTHING);

    // Y position -> reverb send. Top of frame (far side of the table) reads
    // as "further away", so it gets more reverb; near the camera stays dry.
    let targetWet = constrain(map(this.tableY, -height / 2, height / 2, 1, 0), 0, 1);
    this.smoothedWet = lerp(this.smoothedWet, targetWet, DEPTH_SMOOTHING);

    // blob area (pillar height) -> volume
    let clampedArea = constrain(this.rawArea, AREA_MIN, AREA_MAX);
    let targetAmp = map(clampedArea, AREA_MIN, AREA_MAX, MIN_VOLUME, MAX_VOLUME);

    // proximity harmonization: when another swatch is close, both voices jump
    // up a fifth together (they're both on the same pentatonic scale already,
    // so this keeps their interval intact — just transposes the pair up).
    let targetFreq = this.baseFreq;
    if (nearestDist < HARMONIZE_DISTANCE) {
      targetFreq = this.baseFreq * 1.5;
    }

    if (audioReady && this.osc) {
      this.osc.pan(this.smoothedPan);
      this.osc.freq(targetFreq, FREQ_RAMP_TIME);
      this.osc.amp(targetAmp, AMP_RAMP_TIME);
      this.dryGain.amp(1 - this.smoothedWet * 0.6, DEPTH_RAMP_TIME);
      this.wetGain.amp(this.smoothedWet, DEPTH_RAMP_TIME);
    }
  }

  // Called every frame this swatch is NOT detected — smooth fade to silence
  // rather than an abrupt cut.
  fadeOut() {
    if (audioReady && this.osc) {
      this.osc.amp(0, AMP_RAMP_TIME);
    }
  }
}


// ----------------------------------------------------------------------------
// p5 lifecycle
// ----------------------------------------------------------------------------

function setup() {
  createCanvas(640, 480);
  pixelDensity(1);  // 1 canvas pixel = 1 pixel-array entry, keeps the math below simple
  frameRate(30);    // scanning every pixel is the expensive part; 30fps is plenty

  video = createCapture(VIDEO);
  video.size(640, 480);
  video.hide(); // we draw the feed ourselves with image(), so hide the raw <video> tag

  buildSwatchVoices();
}

function draw() {
  image(video, 0, 0, width, height);

  for (let i = 0; i < swatches.length; i++) swatches[i].resetFrame();
  scanTableForColors();
  for (let i = 0; i < swatches.length; i++) swatches[i].finishFrame();

  updateSpatialAudio();
  drawDebugOverlay();

  if (!audioReady) drawStartPrompt();
}

function mousePressed() {
  startAudioEngine();
}

function touchStarted() {
  startAudioEngine();
  return false; // stop the browser treating the tap as a scroll/zoom gesture
}


// ----------------------------------------------------------------------------
// Audio startup — everything audio-node-related happens inside this call
// chain, which only ever fires from a click or tap.
// ----------------------------------------------------------------------------

function startAudioEngine() {
  if (audioReady) return; // only need to do this once

  userStartAudio().then(function () {
    createGlobalAudioNodes();
    for (let i = 0; i < swatches.length; i++) {
      swatches[i].createAudioChain();
    }
    audioReady = true;
  });
}

function createGlobalAudioNodes() {
  globalFilter = new p5.BandPass();
  globalReverb = new p5.Reverb();
  globalReverb.set(REVERB_SECONDS, REVERB_DECAY, false);

  // the shared "Filter -> Reverb -> Output" tail that every voice's wet
  // signal passes through
  globalFilter.connect(globalReverb);
  globalReverb.connect(); // connect() with nothing given sends to the speakers
}


// ----------------------------------------------------------------------------
// Per-frame spatial logic: distances between swatches drive both the
// per-voice harmonizing and the shared filter sweep.
// ----------------------------------------------------------------------------

function updateSpatialAudio() {
  let active = swatches.filter(function (s) { return s.active; });

  // closest pair anywhere on the table -> how far open the shared filter is
  let closestPairDist = null;
  for (let i = 0; i < active.length; i++) {
    for (let j = i + 1; j < active.length; j++) {
      let d = dist(active[i].tableX, active[i].tableY, active[j].tableX, active[j].tableY);
      if (closestPairDist === null || d < closestPairDist) closestPairDist = d;
    }
  }
  updateGlobalFilter(closestPairDist);

  // each swatch's own nearest neighbor -> whether IT harmonizes
  for (let i = 0; i < swatches.length; i++) {
    let sw = swatches[i];
    if (!sw.active) {
      sw.fadeOut();
      continue;
    }
    let nearestDist = Infinity;
    for (let j = 0; j < active.length; j++) {
      if (active[j] === sw) continue;
      let d = dist(sw.tableX, sw.tableY, active[j].tableX, active[j].tableY);
      if (d < nearestDist) nearestDist = d;
    }
    sw.updateSound(nearestDist);
  }
}

function updateGlobalFilter(closestPairDist) {
  if (!audioReady || !globalFilter) return;
  // no pair close together -> treat as "far apart", filter stays closed
  let d = (closestPairDist === null) ? 9999 : closestPairDist;
  let f = constrain(
    map(d, 0, HARMONIZE_DISTANCE * 4, FILTER_FREQ_NEAR, FILTER_FREQ_FAR),
    FILTER_FREQ_FAR, FILTER_FREQ_NEAR
  );
  let q = constrain(
    map(d, 0, HARMONIZE_DISTANCE * 4, FILTER_RES_NEAR, FILTER_RES_FAR),
    FILTER_RES_FAR, FILTER_RES_NEAR
  );
  globalFilter.freq(f, FILTER_RAMP_TIME);
  globalFilter.res(q);
}


// ----------------------------------------------------------------------------
// Color tracking — scan the video for pixels matching each swatch's HSV target
// ----------------------------------------------------------------------------

function buildSwatchVoices() {
  for (let i = 0; i < SWATCH_DATA.length; i++) {
    let d = SWATCH_DATA[i];
    swatches.push(new SwatchVoice(d.name, d.h, d.s, d.v, d.freq, d.wave));
  }
}

function scanTableForColors() {
  video.loadPixels();
  if (video.pixels.length < width * height * 4) return; // camera not warmed up yet, skip this frame

  for (let y = 0; y < height; y += PIXEL_STEP) {
    for (let x = 0; x < width; x += PIXEL_STEP) {
      let idx = (y * width + x) * 4;
      let r = video.pixels[idx];
      let g = video.pixels[idx + 1];
      let b = video.pixels[idx + 2];
      let hsv = rgbToHsv(r, g, b);

      for (let i = 0; i < swatches.length; i++) {
        let sw = swatches[i];
        if (colorMatchesSwatch(hsv, sw)) {
          sw.sumX += x;
          sw.sumY += y;
          sw.count++;
        }
      }
    }
  }
}

function colorMatchesSwatch(hsv, sw) {
  if (Math.abs(hsv.v - sw.targetV) > VAL_TOLERANCE) return false;
  if (Math.abs(hsv.s - sw.targetS) > SAT_TOLERANCE) return false;

  // near-zero saturation (white/grey/black/oyster) has no reliable hue —
  // matching on hue there just adds noise, so skip it for those swatches
  if (sw.targetS < 10) return true;

  return hueDistance(hsv.h, sw.targetH) <= HUE_TOLERANCE;
}

function hueDistance(a, b) {
  let d = Math.abs(a - b);
  return d > 180 ? 360 - d : d;
}

function rgbToHsv(r, g, b) {
  r /= 255; g /= 255; b /= 255;
  let maxc = Math.max(r, g, b);
  let minc = Math.min(r, g, b);
  let delta = maxc - minc;

  let h = 0;
  if (delta !== 0) {
    if (maxc === r) h = 60 * (((g - b) / delta) % 6);
    else if (maxc === g) h = 60 * (((b - r) / delta) + 2);
    else h = 60 * (((r - g) / delta) + 4);
  }
  if (h < 0) h += 360;

  let s = maxc === 0 ? 0 : (delta / maxc) * 100;
  let v = maxc * 100;

  return { h: h, s: s, v: v };
}


// ----------------------------------------------------------------------------
// Debug drawing — circles over detected blobs, labeled with the swatch name
// ----------------------------------------------------------------------------

function drawDebugOverlay() {
  strokeWeight(2);
  textSize(12);
  textAlign(CENTER);

  for (let i = 0; i < swatches.length; i++) {
    let sw = swatches[i];
    if (!sw.active) continue;

    let radius = Math.sqrt(sw.rawArea / Math.PI);
    let rgb = hsvToRgbForDisplay(sw.targetH, sw.targetS, sw.targetV);

    noFill();
    stroke(rgb.r, rgb.g, rgb.b);
    circle(sw.canvasX, sw.canvasY, radius * 2);

    noStroke();
    fill(255);
    text(sw.name, sw.canvasX, sw.canvasY - radius - 6);
  }
}

function drawStartPrompt() {
  noStroke();
  fill(0, 0, 0, 160);
  rect(0, 0, width, height);
  fill(255);
  textAlign(CENTER, CENTER);
  textSize(20);
  text("Click or tap to start the audio engine", width / 2, height / 2);
}

// Only used for drawing debug circles in each swatch's approximate real color.
function hsvToRgbForDisplay(h, s, v) {
  s /= 100; v /= 100;
  let c = v * s;
  let x = c * (1 - Math.abs((h / 60) % 2 - 1));
  let m = v - c;
  let r = 0, g = 0, b = 0;

  if (h < 60)       { r = c; g = x; b = 0; }
  else if (h < 120) { r = x; g = c; b = 0; }
  else if (h < 180) { r = 0; g = c; b = x; }
  else if (h < 240) { r = 0; g = x; b = c; }
  else if (h < 300) { r = x; g = 0; b = c; }
  else              { r = c; g = 0; b = x; }

  return {
    r: Math.round((r + m) * 255),
    g: Math.round((g + m) * 255),
    b: Math.round((b + m) * 255)
  };
}
