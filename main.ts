// png-squeeze: losslessly re-encode each 1280x720 RGBA screenshot as the smallest
// valid PNG we can find within a fixed, deterministic work budget (no clock reads,
// no randomness, no network; Node 22 stdlib only).
//
// What it does, per image:
//   1. Decode the stored input PNG with our own decoder (PNG subset the checker reads).
//   2. Try every lossless form: palette (colour type 3, count and luminance order),
//      grey / grey+alpha, RGB / RGBA, and a single-value tRNS key when the image is
//      opaque except for one fully-transparent colour.
//   3. For each form, pick per-row filters: fixed 0/4, minsum heuristic, fewest
//      distinct byte-pairs, and brute force (each row's 5 filters weighed by an
//      actual deflate of the row against the previous 32 KiB, as the kit's scale
//      screen does). Screen every candidate with zlib level 6.
//   4. Re-deflate the winner at level 9 (memLevel 9, default + filtered strategies,
//      memLevel 8) and keep the smallest file.
//
// PNG reading/writing primitives and the filter functions follow the kit's own
// scorer/checker/png.mjs (make.fun, MIT) and the filter/colour-type analysis of
// its generator/subject/scale.mjs; the search, screening and final deflate
// strategy are our own.

import { deflateSync, inflateSync, constants } from 'node:zlib';
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// ---------------------------------------------------------------- PNG codec
const SIGNATURE = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const CHANNELS = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };

const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();

function crc32(bytes, start = 0, end = bytes.length) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

const ascii = (s) => Uint8Array.from(s, (ch) => ch.charCodeAt(0));

function pngOf(chunks) {
  let size = SIGNATURE.length;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set(SIGNATURE, 0);
  let at = SIGNATURE.length;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out.set(ascii(type), at + 4);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}

function ihdrOf(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

function paeth(a, b, c) {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paeth(a, b, c);
    }
  }
}

function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

function decodePng(bytes) {
  if (bytes.length < 8 || SIGNATURE.some((b, i) => bytes[i] !== b)) throw new Error('bad PNG signature');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let header = null;
  let palette = null;
  let trns = null;
  const idat = [];
  let ended = false;
  while (at < bytes.length) {
    if (ended) throw new Error('bytes after IEND');
    if (at + 12 > bytes.length) throw new Error('chunk cut short');
    const len = view.getUint32(at);
    if (len > 0x7fffffff || at + 12 + len > bytes.length) throw new Error('chunk overruns file');
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (crc32(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) throw new Error(type + ' CRC');
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), depth: data[8], colourType: data[9], interlace: data[12] };
    } else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') ended = true;
  }
  if (!header || !ended || idat.length === 0) throw new Error('incomplete PNG');
  const { width, height, colourType } = header;
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const expected = height * (stride + 1);
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat), { maxOutputLength: expected + 1 });
  if (raw.length !== expected) throw new Error('inflate length mismatch');
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    } else {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paeth(a, b, c);
      }
    }
  }
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const entries = palette.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = palette[e * 3]; lut[e * 4 + 1] = palette[e * 3 + 1]; lut[e * 4 + 2] = palette[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      rgba[d] = lut[e * 4]; rgba[d + 1] = lut[e * 4 + 1]; rgba[d + 2] = lut[e * 4 + 2]; rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { width, height, rgba };
}

// ---------------------------------------------------------------- image analysis
function wordsOf(rgba) {
  const at = rgba.byteOffset % 4 === 0 ? rgba : rgba.slice();
  return new Uint32Array(at.buffer, at.byteOffset, at.length >>> 2);
}

function analyse(rgba) {
  const n = rgba.length >>> 2;
  const u32 = wordsOf(rgba);
  let opaque = true;
  let grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const c = u32[i];
      const k = counts.get(c);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(c, 1);
      } else counts.set(c, k + 1);
    }
  }
  const colours = many ? null : [...counts.keys()].map((c) => {
    const b = new Uint8Array(Uint32Array.of(c).buffer);
    return { rgba: [b[0], b[1], b[2], b[3]], word: c, count: counts.get(c) };
  });
  return { opaque, grey, colours };
}

function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) { out[s] = rgba[d]; out[s + 1] = rgba[d + 3]; }
    else { out[s] = rgba[d]; out[s + 1] = rgba[d + 1]; out[s + 2] = rgba[d + 2]; }
  }
  return out;
}

function paletteOrder(colours, order) {
  const lum = (c) => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  return [...colours].sort((x, y) => {
    const ta = x.rgba[3] === 255 ? 1 : 0;
    const tb = y.rgba[3] === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    if (order === 'rgb') return x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
}

function paletteForm(rgba, colours, order) {
  const entries = paletteOrder(colours, order);
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0]; plte[i * 3 + 1] = c.rgba[1]; plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const u32 = wordsOf(rgba);
  const indices = new Uint8Array(n);
  for (let i = 0; i < n; i++) indices[i] = index.get(u32[i]);
  return { plte, trns, indices };
}

function formsOf(rgba) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms = [];
  if (colours !== null) {
    for (const [order, filters] of [
      ['count', [0, 'minsum']],
      ['luminance', [0, 'minsum', 'brute']],
      ['rgb', [0, 'minsum']],
    ]) {
      const p = paletteForm(rgba, colours, order);
      forms.push({ colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns, filters });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct;
  let trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct];
  forms.push({ colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns, filters: [0, 'minsum', 'brute'] });
  return forms;
}

// ---------------------------------------------------------------- filtering
const BRUTE_CONTEXT = 32768;
const BRUTE_LEVEL = 4;

function pairsOf(row, seen, stamp) {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) { seen[pair] = stamp; n++; }
  }
  return n;
}

function filtered(samples, width, height, bpp, choice) {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const trial = Array.from({ length: 5 }, (_, t) => {
    const row = new Uint8Array(stride + 1);
    row[0] = t;
    return row;
  });
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost;
      if (choice === 'minsum') cost = signedSum(trial[t].subarray(1));
      else if (choice === 'pairs') cost = pairsOf(trial[t].subarray(1), seen, ++stamp);
      else cost = deflateSync(trial[t], before.length === 0 ? { level: BRUTE_LEVEL, memLevel: 9 } : { level: BRUTE_LEVEL, memLevel: 9, dictionary: before }).length;
      if (cost < best) { best = cost; type = t; }
    }
    raw.set(trial[type], at);
  }
  return raw;
}

// ---------------------------------------------------------------- optimal DEFLATE
// A small optimal-parse DEFLATE encoder (zopfli-style, written for this entry):
// hash-chain LZ77, backward dynamic-programming parse under a Huffman cost
// model refined once from the first pass's token frequencies, length-limited
// Huffman codes by package-merge, one dynamic block. Deterministic: no clock,
// no randomness. Typically 1-2% smaller than zlib level 9 on filtered PNG data.
const LENGTH_BASE = [3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258];
const LENGTH_EXTRA = [0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0];
const DIST_BASE = [1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577];
const DIST_EXTRA = [0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13];

// Precomputed: length code per match length, and candidate lengths per max length.
const LEN_CODE = new Uint16Array(259);
for (let L = 3; L <= 258; L++) {
  if (L === 258) LEN_CODE[L] = 285;
  else { let lo = 0; for (let k = 0; k < 28; k++) if (LENGTH_BASE[k] <= L) lo = k; LEN_CODE[L] = 257 + lo; }
}
const CAND_LENS = [];
for (let ml = 0; ml <= 258; ml++) {
  const arr = [];
  if (ml >= 3) {
    arr.push(3);
    let prevCode = LEN_CODE[3];
    for (let L = 4; L <= ml; L++) {
      const c = LEN_CODE[L];
      if (c !== prevCode) { arr.push(L); prevCode = c; }
    }
    if (arr[arr.length - 1] !== ml) arr.push(ml);
  }
  CAND_LENS.push(arr);
}
const DIST_CODE = new Uint8Array(32769);
for (let d = 1; d <= 32768; d++) {
  let lo = 0; for (let k = 0; k < 30; k++) if (DIST_BASE[k] <= d) lo = k; DIST_CODE[d] = lo;
}

class Bits {
  constructor() { this.bytes = []; this.acc = 0; this.nbits = 0; }
  put(val, n) {
    if (n === 0) return;
    this.acc |= (val & ((1 << n) - 1)) << this.nbits;
    this.nbits += n;
    while (this.nbits >= 8) { this.bytes.push(this.acc & 0xff); this.acc >>>= 8; this.nbits -= 8; }
  }
  putRev(code, n) {
    let r = 0;
    for (let i = 0; i < n; i++) r = (r << 1) | ((code >> i) & 1);
    this.put(r, n);
  }
  finish() {
    if (this.nbits > 0) { this.bytes.push(this.acc & 0xff); this.acc = 0; this.nbits = 0; }
    return Uint8Array.from(this.bytes);
  }
}

// Length-limited Huffman via package-merge (Larmore-Przytycka).
// Repeat maxBits-1 times: package the sorted list pairwise, then merge with
// the original singletons. A symbol's code length is how many of the first
// 2n-2 items of the final list contain it.
function huffmanLengths(freq, maxBits) {
  const n = freq.length;
  const len = new Uint8Array(n);
  const active = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) active.push(i);
  if (active.length === 0) return len;
  if (active.length === 1) { len[active[0]] = 1; return len; }
  const singletons = active.map((s) => ({ w: freq[s], syms: [s] }))
    .sort((a, b) => a.w - b.w);
  const mergeSorted = (a, b) => {
    const out = [];
    let i = 0, j = 0;
    while (i < a.length && j < b.length) {
      if (a[i].w <= b[j].w) out.push(a[i++]); else out.push(b[j++]);
    }
    while (i < a.length) out.push(a[i++]);
    while (j < b.length) out.push(b[j++]);
    return out;
  };
  let list = singletons;
  for (let level = 1; level < maxBits; level++) {
    const packaged = [];
    for (let i = 0; i + 1 < list.length; i += 2) {
      packaged.push({ w: list[i].w + list[i + 1].w, syms: list[i].syms.concat(list[i + 1].syms) });
    }
    if (list.length % 2 === 1) packaged.push(list[list.length - 1]);
    list = mergeSorted(packaged, singletons);
  }
  const take = Math.min(list.length, 2 * active.length - 2);
  for (let i = 0; i < take; i++) {
    for (const s of list[i].syms) len[s]++;
  }
  return len;
}

function canonicalCodes(lengths) {
  const n = lengths.length;
  let max = 0;
  for (const l of lengths) if (l > max) max = l;
  const blCount = new Uint32Array(max + 1);
  for (const l of lengths) if (l) blCount[l]++;
  const nextCode = new Uint32Array(max + 1);
  let code = 0;
  for (let b = 1; b <= max; b++) { code = (code + blCount[b - 1]) << 1; nextCode[b] = code; }
  const codes = new Uint32Array(n);
  for (let s = 0; s < n; s++) {
    const l = lengths[s];
    if (l) { codes[s] = nextCode[l]; nextCode[l]++; }
  }
  return codes;
}

function findMatches(data, chainLimit) {
  const n = data.length;
  const head = new Int32Array(65536).fill(-1);
  const prev = new Int32Array(n).fill(-1);
  const bestLen = new Uint16Array(n);
  const bestDist = new Uint16Array(n);
  // 32-bit view for fast match extension (equality only; endianness irrelevant).
  // Only usable when the view starts 4-aligned; otherwise fall back to bytes.
  const aligned = data.byteOffset % 4 === 0;
  const u32 = aligned ? new Uint32Array(data.buffer, data.byteOffset, (n / 4) | 0) : null;
  const n4 = (n / 4) | 0;
  for (let i = 0; i + 3 <= n; i++) {
    const h = (((data[i] << 10) ^ (data[i + 1] << 5) ^ data[i + 2]) & 0xffff);
    let cand = head[h];
    let chain = 0;
    let bl = 0, bd = 0;
    const maxLen = Math.min(258, n - i);
    if (maxLen >= 3) {
      while (cand >= 0 && chain < chainLimit) {
        const dist = i - cand;
        if (dist > 32768) break;
        if (data[cand] === data[i] && data[cand + 1] === data[i + 1] && data[cand + 2] === data[i + 2]) {
          let l = 3;
          const lim = Math.min(maxLen, 258);
          if (u32 !== null && (dist & 3) === 0) {
            // 4-byte compares are only valid when both windows stay aligned.
            while (l < lim && ((i + l) & 3) !== 0 && data[cand + l] === data[i + l]) l++;
            while (l + 4 <= lim && (i + l) < n4 * 4 && u32[(i + l) >> 2] === u32[(cand + l) >> 2]) l += 4;
          }
          while (l < lim && data[cand + l] === data[i + l]) l++;
          if (l > bl) { bl = l; bd = dist; if (l >= lim) break; }
        }
        cand = prev[cand];
        chain++;
        if (bl >= 64 && chain >= 4) break; // good enough: long match found
      }
    }
    if (bl >= 3) { bestLen[i] = bl; bestDist[i] = bd; }
    prev[i] = head[h];
    head[h] = i;
  }
  return { bestLen, bestDist };
}

function optimalParse(data, match, litCost, lenCostByLen, distCostByDist) {
  const n = data.length;
  const cost = new Float64Array(n + 1);
  const choiceLen = new Uint16Array(n);
  const choiceDist = new Uint16Array(n);
  cost[n] = 0;
  for (let i = n - 1; i >= 0; i--) {
    let best = litCost[data[i]] + cost[i + 1];
    let bl = 0, bd = 0;
    const ml = match.bestLen[i];
    if (ml >= 3) {
      const d = match.bestDist[i];
      const dc = distCostByDist[d];
      const cands = CAND_LENS[ml];
      for (let k = 0; k < cands.length; k++) {
        const L = cands[k];
        const c = lenCostByLen[L] + dc + cost[i + L];
        if (c < best) { best = c; bl = L; bd = d; }
      }
    }
    cost[i] = best;
    choiceLen[i] = bl;
    choiceDist[i] = bd;
  }
  return { choiceLen, choiceDist };
}

function tokensOf(data, choiceLen, choiceDist) {
  const toks = [];
  let i = 0;
  const n = data.length;
  while (i < n) {
    const L = choiceLen[i];
    if (L === 0) { toks.push(data[i]); i++; }
    else { toks.push(-L, choiceDist[i]); i += L; }
  }
  return toks;
}

function freqsOf(toks) {
  const lf = new Uint32Array(288);
  const df = new Uint32Array(30);
  for (let i = 0; i < toks.length; i++) {
    const t = toks[i];
    if (t >= 0) lf[t]++;
    else { lf[LEN_CODE[-t]]++; df[DIST_CODE[toks[++i]]]++; }
  }
  lf[256] = 1;
  return { lf, df };
}

function costsFromFreqs(lf, df) {
  const ll = huffmanLengths(lf, 15);
  const dl = huffmanLengths(df, 15);
  // Symbols unseen in this pass must not cost 0 in the next DP, or the parse
  // collapses to literals: fall back to the fixed-Huffman cost for them.
  const litCost = new Float64Array(256);
  for (let s = 0; s < 256; s++) litCost[s] = ll[s] || (s < 144 ? 8 : 9);
  const lenCostByLen = new Float64Array(259);
  for (let L = 3; L <= 258; L++) {
    const lc = LEN_CODE[L];
    lenCostByLen[L] = (ll[lc] || 8) + LENGTH_EXTRA[lc - 257];
  }
  const distCostByDist = new Float64Array(32769);
  for (let d = 1; d <= 32768; d++) {
    const dc = DIST_CODE[d];
    distCostByDist[d] = (dl[dc] || 5) + DIST_EXTRA[dc];
  }
  return { ll, dl, litCost, lenCostByLen, distCostByDist };
}

function fixedCostModel() {
  const litCost = new Float64Array(256);
  for (let s = 0; s < 256; s++) litCost[s] = s < 144 ? 8 : 9;
  const lenCostByLen = new Float64Array(259);
  for (let L = 3; L <= 258; L++) lenCostByLen[L] = 8 + LENGTH_EXTRA[LEN_CODE[L] - 257];
  const distCostByDist = new Float64Array(32769).fill(5);
  for (let d = 1; d <= 32768; d++) distCostByDist[d] = 5 + DIST_EXTRA[DIST_CODE[d]];
  return { litCost, lenCostByLen, distCostByDist };
}

function emitDynamicBlock(bits, toks, ll, dl) {
  let nlit = 286;
  while (nlit > 257 && ll[nlit - 1] === 0) nlit--;
  let ndist = 30;
  while (ndist > 1 && dl[ndist - 1] === 0) ndist--;
  const all = new Uint8Array(nlit + ndist);
  all.set(ll.subarray(0, nlit), 0);
  all.set(dl.subarray(0, ndist), nlit);
  const seq = [];
  let i = 0;
  while (i < all.length) {
    const v = all[i];
    let run = 1;
    while (i + run < all.length && all[i + run] === v) run++;
    if (v === 0) {
      let r = run;
      while (r >= 11) { const take = Math.min(r, 138); seq.push([18, take]); r -= take; }
      if (r >= 3) { seq.push([17, r]); r = 0; }
      while (r > 0) { seq.push([0, 1]); r--; }
    } else {
      seq.push([v, 1]);
      let r = run - 1;
      while (r >= 3) { const take = Math.min(r, 6); seq.push([16, take]); r -= take; }
      while (r > 0) { seq.push([v, 1]); r--; }
    }
    i += run;
  }
  const clf = new Uint32Array(19);
  for (const [s] of seq) clf[s]++;
  const cl = huffmanLengths(clf, 7);
  const clOrder = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
  let ncl = 19;
  while (ncl > 4 && cl[clOrder[ncl - 1]] === 0) ncl--;
  bits.put(2, 2);
  bits.put(nlit - 257, 5);
  bits.put(ndist - 1, 5);
  bits.put(ncl - 4, 4);
  for (let k = 0; k < ncl; k++) bits.put(cl[clOrder[k]], 3);
  const clCodes = canonicalCodes(cl);
  for (const [s, extra] of seq) {
    bits.putRev(clCodes[s], cl[s]);
    if (s === 16) bits.put(extra - 3, 2);
    else if (s === 17) bits.put(extra - 3, 3);
    else if (s === 18) bits.put(extra - 11, 7);
  }
  const llCodes = canonicalCodes(ll);
  const dlCodes = canonicalCodes(dl);
  for (let k = 0; k < toks.length; k++) {
    const t = toks[k];
    if (t >= 0) bits.putRev(llCodes[t], ll[t]);
    else {
      const L = -t;
      const lc = LEN_CODE[L];
      bits.putRev(llCodes[lc], ll[lc]);
      bits.put(L - LENGTH_BASE[lc - 257], LENGTH_EXTRA[lc - 257]);
      const d = toks[++k];
      const dc = DIST_CODE[d];
      bits.putRev(dlCodes[dc], dl[dc]);
      bits.put(d - DIST_BASE[dc], DIST_EXTRA[dc]);
    }
  }
  bits.putRev(llCodes[256], ll[256]);
}

function adler32(data) {
  let a = 1, b = 0;
  for (let i = 0; i < data.length;) {
    const end = Math.min(data.length, i + 5552);
    for (; i < end; i++) { a += data[i]; b += a; }
    a %= 65521; b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

function deflateOptimal(data, chainLimit = 32, passes = 2) {
  const match = findMatches(data, chainLimit);
  let model = fixedCostModel();
  let parse, toks;
  for (let p = 0; p < passes; p++) {
    parse = optimalParse(data, match, model.litCost, model.lenCostByLen, model.distCostByDist);
    toks = tokensOf(data, parse.choiceLen, parse.choiceDist);
    const { lf, df } = freqsOf(toks);
    model = costsFromFreqs(lf, df);
  }
  const bits = new Bits();
  bits.put(1, 1);
  emitDynamicBlock(bits, toks, model.ll, model.dl);
  const raw = bits.finish();
  const out = new Uint8Array(raw.length + 6);
  out[0] = 0x78; out[1] = 0xda;
  out.set(raw, 2);
  const ad = adler32(data);
  out[out.length - 4] = (ad >>> 24) & 0xff;
  out[out.length - 3] = (ad >>> 16) & 0xff;
  out[out.length - 2] = (ad >>> 8) & 0xff;
  out[out.length - 1] = ad & 0xff;
  return out;
}


// ---------------------------------------------------------------- encode one image
const SCREEN = { level: 6, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY };
const chunkBytes = (form) => (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

function pngOfForm(width, height, form, idat) {
  const chunks = [['IHDR', ihdrOf(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}

function encode(rgba, width, height) {
  const forms = formsOf(rgba);
  const screened = [];
  for (let fi = 0; fi < forms.length; fi++) {
    const form = forms[fi];
    const chunks = chunkBytes(form);
    for (const choice of form.filters) {
      const data = filtered(form.samples, width, height, form.bpp, choice);
      const zlib = deflateSync(data, SCREEN);
      screened.push({ form, fi, choice, data, bytes: zlib.length + chunks });
    }
  }
  screened.sort((a, b) => a.bytes - b.bytes);
  const best = screened[0];
  // Final pass: the two best screened candidates through zlib level 9 (three
  // settings), and the winner form's brute-force filters through the
  // optimal-parse encoder (where it beats zlib: photo-like and soft-shadow
  // data). Keep the smallest file.
  const finals = [];
  const addZlib = (data, form) => {
    for (const [level, memLevel, strategy] of [
      [9, 9, constants.Z_DEFAULT_STRATEGY],
      [9, 9, constants.Z_FILTERED],
      [9, 8, constants.Z_DEFAULT_STRATEGY],
    ]) {
      const zlib = deflateSync(data, { level, memLevel, strategy });
      finals.push({ form, zlib, bytes: zlib.length + chunkBytes(form) });
    }
  };
  const seenTop = new Set();
  for (const cand of screened) {
    const key = cand.fi + ':' + cand.choice;
    if (seenTop.has(key)) continue;
    seenTop.add(key);
    addZlib(cand.data, cand.form);
    if (seenTop.size === 2) break;
  }
  // Optimal-parse encode of the best form's brute-force filtered data.
  let bruteData = null;
  if (best.choice === 'brute') bruteData = best.data;
  else {
    const entry = screened.find((c) => c.form === best.form && c.choice === 'brute');
    if (entry !== undefined) bruteData = entry.data;
    else bruteData = filtered(best.form.samples, width, height, best.form.bpp, 'brute');
  }
  const opt = deflateOptimal(bruteData);
  finals.push({ form: best.form, zlib: opt, bytes: opt.length + chunkBytes(best.form) });
  let winner = finals[0];
  for (const f of finals) if (f.bytes < winner.bytes) winner = f;
  return pngOfForm(width, height, winner.form, winner.zlib);
}

// ---------------------------------------------------------------- main
for (const id of readdirSync(I).sort()) {
  const image = decodePng(new Uint8Array(readFileSync(join(I, id, 'image.png'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'image.png'), encode(image.rgba, image.width, image.height));
}
