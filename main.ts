// png-squeeze: losslessly re-encode 1280x720 RGBA screenshots as the smallest
// valid PNG we can find inside a fixed, deterministic work budget.
//
// Pipeline, per image:
//   decode the stored input PNG with our own reader -> survey the pixels ->
//   build every lossless colour form worth trying (palette orders, grey,
//   grey+alpha, RGB, RGBA, single-colour tRNS) -> choose per-row filters for
//   each form (fixed, min-sum, brute-force deflate scoring) -> screen every
//   candidate with zlib level 6 -> re-deflate the best two at level 9 and the
//   best form's brute-force rows with our own optimal-parse DEFLATE encoder,
//   and keep the smallest file.
//
// Node 22 stdlib only, no clock, no randomness, no network, so two runs write
// identical bytes. The DEFLATE tables, the package-merge Huffman builder and
// the PNG filter/colour rules follow the PNG and DEFLATE specifications and
// the kit's own checker/generator analysis; the search order, screening and
// final selection are this entry's own.

import { deflateSync, inflateSync, constants } from 'node:zlib';
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// ------------------------------------------------------------------ tables
// DEFLATE length / distance code tables (RFC 1951). Length code 285 is the
// 258 special case; CANDIDATE_LENGTHS[max] lists the lengths worth trying in
// the dynamic-programming parse: 3, every length where the code changes, and
// the maximum itself.
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];

function codeForLength(len) {
  if (len === 258) return 285;
  let code = 257;
  for (let k = 0; k < 28; k++) if (LEN_BASE[k] <= len) code = 257 + k;
  return code;
}

function codeForDistance(dist) {
  let code = 0;
  for (let k = 0; k < 30; k++) if (DIST_BASE[k] <= dist) code = k;
  return code;
}

const LEN_CODE = new Uint16Array(259);
for (let len = 3; len <= 258; len++) LEN_CODE[len] = codeForLength(len);

const CANDIDATE_LENGTHS = [];
for (let max = 0; max <= 258; max++) {
  const list = [];
  if (max >= 3) {
    list.push(3);
    let prev = LEN_CODE[3];
    for (let len = 4; len <= max; len++) {
      if (LEN_CODE[len] !== prev) { list.push(len); prev = LEN_CODE[len]; }
    }
    if (list[list.length - 1] !== max) list.push(max);
  }
  CANDIDATE_LENGTHS.push(list);
}

const DIST_CODE = new Uint8Array(32769);
for (let d = 1; d <= 32768; d++) DIST_CODE[d] = codeForDistance(d);

// ------------------------------------------------------------------ CRC-32
const CRC_TABLE = (() => {
  const table = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    table[n] = c;
  }
  return table;
})();

function crc32(bytes, start = 0, end = bytes.length) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

function adler(data) {
  let a = 1, b = 0;
  for (let i = 0; i < data.length;) {
    const end = Math.min(data.length, i + 5552);
    for (; i < end; i++) { a += data[i]; b += a; }
    a %= 65521; b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

// ------------------------------------------------------------------ bit output
class BitWriter {
  constructor() { this.bytes = []; this.acc = 0; this.nbits = 0; }
  // Write the low `n` bits of `value`, least-significant bit first.
  write(value, n) {
    if (n === 0) return;
    this.acc |= (value & ((1 << n) - 1)) << this.nbits;
    this.nbits += n;
    while (this.nbits >= 8) { this.bytes.push(this.acc & 0xff); this.acc >>>= 8; this.nbits -= 8; }
  }
  // Write a Huffman code, most-significant bit first (codes are stored MSB-first).
  writeCode(code, n) {
    let reversed = 0;
    for (let i = 0; i < n; i++) reversed = (reversed << 1) | ((code >> i) & 1);
    this.write(reversed, n);
  }
  finish() {
    if (this.nbits > 0) { this.bytes.push(this.acc & 0xff); this.acc = 0; this.nbits = 0; }
    return Uint8Array.from(this.bytes);
  }
}

// ------------------------------------------------------------------ Huffman
// Length-limited Huffman code lengths by package-merge: repeat maxBits - 1
// times (package the sorted list pairwise, merge back with the singletons);
// a symbol's length is the number of the first 2n - 2 packaged items that
// contain it.
function codeLengths(freq, maxBits) {
  const n = freq.length;
  const lengths = new Uint8Array(n);
  const used = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) used.push(i);
  if (used.length === 0) return lengths;
  if (used.length === 1) { lengths[used[0]] = 1; return lengths; }
  const singletons = used.map((s) => ({ w: freq[s], syms: [s] }))
    .sort((a, b) => a.w - b.w);
  const mergeByWeight = (a, b) => {
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
    list = mergeByWeight(packaged, singletons);
  }
  const take = Math.min(list.length, 2 * used.length - 2);
  for (let i = 0; i < take; i++) for (const s of list[i].syms) lengths[s]++;
  return lengths;
}

function canonical(lengths) {
  const n = lengths.length;
  let max = 0;
  for (const l of lengths) if (l > max) max = l;
  const blCount = new Uint32Array(max + 1);
  for (const l of lengths) if (l) blCount[l]++;
  const nextCode = new Uint32Array(max + 1);
  let code = 0;
  for (let bits = 1; bits <= max; bits++) { code = (code + blCount[bits - 1]) << 1; nextCode[bits] = code; }
  const codes = new Uint32Array(n);
  for (let s = 0; s < n; s++) {
    const l = lengths[s];
    if (l) { codes[s] = nextCode[l]; nextCode[l]++; }
  }
  return codes;
}

// ------------------------------------------------------------------ optimal DEFLATE
// A small optimal-parse DEFLATE encoder in the zopfli style: hash-chain LZ77,
// a backward dynamic-programming parse under a Huffman cost model refined
// once from the first pass's token frequencies, length-limited codes by
// package-merge, one dynamic block. Deterministic throughout, and typically
// 1-2% smaller than zlib level 9 on filtered PNG data.
function scanMatches(data, chainLimit) {
  const n = data.length;
  const head = new Int32Array(65536).fill(-1);
  const prev = new Int32Array(n).fill(-1);
  const bestLen = new Uint16Array(n);
  const bestDist = new Uint16Array(n);
  // 32-bit view for fast match extension (equality only; endianness is
  // irrelevant). Only usable when the view starts 4-aligned.
  const aligned = data.byteOffset % 4 === 0;
  const words = aligned ? new Uint32Array(data.buffer, data.byteOffset, (n / 4) | 0) : null;
  const n4 = (n / 4) | 0;
  for (let i = 0; i + 3 <= n; i++) {
    const hash = ((data[i] << 10) ^ (data[i + 1] << 5) ^ data[i + 2]) & 0xffff;
    let cand = head[hash];
    let chain = 0;
    let bl = 0, bd = 0;
    const maxLen = Math.min(258, n - i);
    if (maxLen >= 3) {
      while (cand >= 0 && chain < chainLimit) {
        const dist = i - cand;
        if (dist > 32768) break;
        if (data[cand] === data[i] && data[cand + 1] === data[i + 1] && data[cand + 2] === data[i + 2]) {
          let len = 3;
          const lim = Math.min(maxLen, 258);
          if (words !== null && (dist & 3) === 0) {
            while (len < lim && ((i + len) & 3) !== 0 && data[cand + len] === data[i + len]) len++;
            while (len + 4 <= lim && (i + len) < n4 * 4 && words[(i + len) >> 2] === words[(cand + len) >> 2]) len += 4;
          }
          while (len < lim && data[cand + len] === data[i + len]) len++;
          if (len > bl) { bl = len; bd = dist; if (len >= lim) break; }
        }
        cand = prev[cand];
        chain++;
        if (bl >= 64 && chain >= 4) break; // good enough: long match found
      }
    }
    if (bl >= 3) { bestLen[i] = bl; bestDist[i] = bd; }
    prev[i] = head[hash];
    head[hash] = i;
  }
  return { bestLen, bestDist };
}

function parseOptimal(data, match, litCost, lenCostByLen, distCostByDist) {
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
      for (const len of CANDIDATE_LENGTHS[ml]) {
        const c = lenCostByLen[len] + dc + cost[i + len];
        if (c < best) { best = c; bl = len; bd = d; }
      }
    }
    cost[i] = best;
    choiceLen[i] = bl;
    choiceDist[i] = bd;
  }
  return { choiceLen, choiceDist };
}

// Tokens: a literal byte (>= 0), or a match as -length followed by distance.
function collectTokens(data, choiceLen, choiceDist) {
  const toks = [];
  let i = 0;
  const n = data.length;
  while (i < n) {
    const len = choiceLen[i];
    if (len === 0) { toks.push(data[i]); i++; }
    else { toks.push(-len, choiceDist[i]); i += len; }
  }
  return toks;
}

function countFrequencies(toks) {
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

function modelFromFrequencies(lf, df) {
  const ll = codeLengths(lf, 15);
  const dl = codeLengths(df, 15);
  // Symbols unseen in this pass must not cost 0 in the next DP, or the parse
  // collapses to literals: fall back to the fixed-Huffman cost for them.
  const litCost = new Float64Array(256);
  for (let s = 0; s < 256; s++) litCost[s] = ll[s] || (s < 144 ? 8 : 9);
  const lenCostByLen = new Float64Array(259);
  for (let len = 3; len <= 258; len++) {
    const lc = LEN_CODE[len];
    lenCostByLen[len] = (ll[lc] || 8) + LEN_EXTRA[lc - 257];
  }
  const distCostByDist = new Float64Array(32769);
  for (let d = 1; d <= 32768; d++) {
    const dc = DIST_CODE[d];
    distCostByDist[d] = (dl[dc] || 5) + DIST_EXTRA[dc];
  }
  return { ll, dl, litCost, lenCostByLen, distCostByDist };
}

function fixedModel() {
  const litCost = new Float64Array(256);
  for (let s = 0; s < 256; s++) litCost[s] = s < 144 ? 8 : 9;
  const lenCostByLen = new Float64Array(259);
  for (let len = 3; len <= 258; len++) lenCostByLen[len] = 8 + LEN_EXTRA[LEN_CODE[len] - 257];
  const distCostByDist = new Float64Array(32769);
  for (let d = 1; d <= 32768; d++) distCostByDist[d] = 5 + DIST_EXTRA[DIST_CODE[d]];
  return { litCost, lenCostByLen, distCostByDist };
}

function writeDynamicBlock(bits, toks, ll, dl) {
  let nlit = 286;
  while (nlit > 257 && ll[nlit - 1] === 0) nlit--;
  let ndist = 30;
  while (ndist > 1 && dl[ndist - 1] === 0) ndist--;
  const all = new Uint8Array(nlit + ndist);
  all.set(ll.subarray(0, nlit), 0);
  all.set(dl.subarray(0, ndist), nlit);
  // Run-length encode the combined code-length sequence (codes 16/17/18).
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
  const cl = codeLengths(clf, 7);
  const clOrder = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
  let ncl = 19;
  while (ncl > 4 && cl[clOrder[ncl - 1]] === 0) ncl--;
  bits.write(2, 2); // BTYPE = dynamic (BFINAL was written by the caller)
  bits.write(nlit - 257, 5);
  bits.write(ndist - 1, 5);
  bits.write(ncl - 4, 4);
  for (let k = 0; k < ncl; k++) bits.write(cl[clOrder[k]], 3);
  const clCodes = canonical(cl);
  for (const [s, extra] of seq) {
    bits.writeCode(clCodes[s], cl[s]);
    if (s === 16) bits.write(extra - 3, 2);
    else if (s === 17) bits.write(extra - 3, 3);
    else if (s === 18) bits.write(extra - 11, 7);
  }
  const llCodes = canonical(ll);
  const dlCodes = canonical(dl);
  for (let k = 0; k < toks.length; k++) {
    const t = toks[k];
    if (t >= 0) bits.writeCode(llCodes[t], ll[t]);
    else {
      const len = -t;
      const lc = LEN_CODE[len];
      bits.writeCode(llCodes[lc], ll[lc]);
      bits.write(len - LEN_BASE[lc - 257], LEN_EXTRA[lc - 257]);
      const d = toks[++k];
      const dc = DIST_CODE[d];
      bits.writeCode(dlCodes[dc], dl[dc]);
      bits.write(d - DIST_BASE[dc], DIST_EXTRA[dc]);
    }
  }
  bits.writeCode(llCodes[256], ll[256]); // end of block
}

function deflateBest(data, chainLimit = 32, passes = 2) {
  const match = scanMatches(data, chainLimit);
  let model = fixedModel();
  let toks;
  for (let p = 0; p < passes; p++) {
    const parse = parseOptimal(data, match, model.litCost, model.lenCostByLen, model.distCostByDist);
    toks = collectTokens(data, parse.choiceLen, parse.choiceDist);
    const { lf, df } = countFrequencies(toks);
    model = modelFromFrequencies(lf, df);
  }
  const bits = new BitWriter();
  bits.write(1, 1); // BFINAL
  writeDynamicBlock(bits, toks, model.ll, model.dl);
  const raw = bits.finish();
  const out = new Uint8Array(raw.length + 6);
  out[0] = 0x78; out[1] = 0xda; // zlib header: deflate, 32 KiB window
  out.set(raw, 2);
  const ad = adler(data);
  out[out.length - 4] = (ad >>> 24) & 0xff;
  out[out.length - 3] = (ad >>> 16) & 0xff;
  out[out.length - 2] = (ad >>> 8) & 0xff;
  out[out.length - 1] = ad & 0xff;
  return out;
}

// ------------------------------------------------------------------ PNG codec
const SIGNATURE = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
const CHANNELS = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };

const textBytes = (s) => Uint8Array.from(s, (ch) => ch.charCodeAt(0));

function assemblePng(chunks) {
  let size = SIGNATURE.length;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set(SIGNATURE, 0);
  let at = SIGNATURE.length;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out.set(textBytes(type), at + 4);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}

function ihdrChunk(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8; // bit depth 8
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

// Forward filter: turn a raw scanline into its filtered form (type byte is
// written by the caller; `out` holds the filtered bytes only).
function applyFilter(type, cur, prev, bpp, out) {
  const n = cur.length;
  const left = (i) => (i >= bpp ? cur[i - bpp] : 0);
  const up = (i) => (prev === null ? 0 : prev[i]);
  if (type === 0) { out.set(cur); return; }
  if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - left(i);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - up(i);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - ((left(i) + up(i)) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = left(i);
      const b = up(i);
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paeth(a, b, c);
    }
  }
}

// Inverse filter: rebuild a raw scanline from its filtered bytes, writing
// into `dest` (which already holds the previous row's raw bytes just above
// the destination when y > 0; here `prev` is that previous raw row or null).
function restoreRow(type, src, prev, bpp, dest) {
  const n = src.length;
  if (type === 0) { dest.set(src); return; }
  if (type === 1) {
    for (let i = 0; i < n; i++) dest[i] = src[i] + (i >= bpp ? dest[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) dest[i] = src[i] + (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) {
      dest[i] = src[i] + (((i >= bpp ? dest[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
    }
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? dest[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      dest[i] = src[i] + paeth(a, b, c);
    }
  }
}

function readPng(bytes) {
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
    const src = raw.subarray(y * (stride + 1) + 1, (y + 1) * (stride + 1));
    const dest = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    restoreRow(ft, src, prev, bpp, dest);
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

// ------------------------------------------------------------------ image survey
// 32-bit view over RGBA pixels (a copy when the buffer is not 4-aligned).
function asWords(rgba) {
  const aligned = rgba.byteOffset % 4 === 0 ? rgba : rgba.slice();
  return new Uint32Array(aligned.buffer, aligned.byteOffset, aligned.length >>> 2);
}

// Opaque? Grey (r == g == b everywhere)? And the distinct colours, when there
// are at most 256 of them (otherwise `colours` is null).
function survey(rgba) {
  const n = rgba.length >>> 2;
  const words = asWords(rgba);
  let opaque = true;
  let grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const c = words[i];
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

// When every non-opaque pixel is fully transparent and all of them share one
// colour (and no opaque pixel uses that colour), the image can carry that
// colour as a single tRNS key instead of an alpha channel. Returns the key
// (a grey value, or a packed RGB integer) or null.
function singleTransparentColour(rgba, grey) {
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

function extractSamples(rgba, ct) {
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

function orderPalette(colours, order) {
  const luminance = (c) => 299 * c.rgba[0] + 587 * c.rgba[1] + 114 * c.rgba[2];
  return [...colours].sort((x, y) => {
    const tx = x.rgba[3] === 255 ? 1 : 0;
    const ty = y.rgba[3] === 255 ? 1 : 0;
    if (tx !== ty) return tx - ty; // transparent entries first
    if (tx === 0 && x.rgba[3] !== y.rgba[3]) return x.rgba[3] - y.rgba[3];
    if (order === 'luminance') return luminance(x) - luminance(y) || x.word - y.word;
    if (order === 'rgb') return x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
}

function buildPalette(rgba, colours, order) {
  const entries = orderPalette(colours, order);
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.rgba[0]; plte[i * 3 + 1] = c.rgba[1]; plte[i * 3 + 2] = c.rgba[2];
    if (c.rgba[3] !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.rgba[3]);
  const n = rgba.length >>> 2;
  const words = asWords(rgba);
  const indices = new Uint8Array(n);
  for (let i = 0; i < n; i++) indices[i] = index.get(words[i]);
  return { plte, trns, indices };
}

// Every lossless colour form worth trying for this image, each with the
// filter strategies to try on it. Palette forms come first when the image
// has at most 256 colours; a grey image also tries its grey form.
function candidateForms(rgba) {
  const { opaque, grey, colours } = survey(rgba);
  const forms = [];
  if (colours !== null) {
    for (const [order, filters] of [
      ['count', [0, 'minsum']],
      ['luminance', [0, 'minsum', 'brute']],
      ['rgb', [0, 'minsum']],
    ]) {
      const p = buildPalette(rgba, colours, order);
      forms.push({ colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns, filters });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : singleTransparentColour(rgba, grey);
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
  forms.push({ colourType: ct, bpp, samples: extractSamples(rgba, ct), plte: null, trns, filters: [0, 'minsum', 'brute'] });
  return forms;
}

// ------------------------------------------------------------------ filter search
const BRUTE_CONTEXT = 32768;
const BRUTE_LEVEL = 4;

// Sum of |signed byte| over a filtered row (the classic minimum-sum heuristic).
function absSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

// Number of distinct adjacent byte pairs in a row, via a stamp array.
function distinctPairs(row, seen, stamp) {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) { seen[pair] = stamp; n++; }
  }
  return n;
}

// Filter every row of `samples` under one strategy:
//   a number: that fixed filter on every row;
//   'minsum': per row, the filter with the smallest signed-byte sum;
//   'pairs':  per row, the filter with the fewest distinct byte pairs;
//   'brute':  per row, the filter whose deflate (level 4, against the
//             previous 32 KiB of already-filtered output as dictionary)
//             is smallest.
function filterImage(samples, width, height, bpp, choice) {
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
      applyFilter(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      applyFilter(t, cur, prev, bpp, trial[t].subarray(1));
      let cost;
      if (choice === 'minsum') cost = absSum(trial[t].subarray(1));
      else if (choice === 'pairs') cost = distinctPairs(trial[t].subarray(1), seen, ++stamp);
      else {
        const opts = before.length === 0
          ? { level: BRUTE_LEVEL, memLevel: 9 }
          : { level: BRUTE_LEVEL, memLevel: 9, dictionary: before };
        cost = deflateSync(trial[t], opts).length;
      }
      if (cost < best) { best = cost; type = t; }
    }
    raw.set(trial[type], at);
  }
  return raw;
}

// ------------------------------------------------------------------ encode one image
const SCREEN = { level: 6, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY };

const overheadBytes = (form) =>
  (form.plte === null ? 0 : 12 + form.plte.length) +
  (form.trns === null ? 0 : 12 + form.trns.length);

function assembleForm(width, height, form, idat) {
  const chunks = [['IHDR', ihdrChunk(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return assemblePng(chunks);
}

function encodeImage(rgba, width, height) {
  const forms = candidateForms(rgba);
  const screened = [];
  for (let fi = 0; fi < forms.length; fi++) {
    const form = forms[fi];
    const overhead = overheadBytes(form);
    for (const choice of form.filters) {
      const data = filterImage(form.samples, width, height, form.bpp, choice);
      const zlib = deflateSync(data, SCREEN);
      screened.push({ form, fi, choice, data, bytes: zlib.length + overhead });
    }
  }
  screened.sort((a, b) => a.bytes - b.bytes);
  const best = screened[0];
  // Final pass: the two best screened candidates through zlib level 9 (three
  // settings), and the best form's brute-force filters through the
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
      finals.push({ form, zlib, bytes: zlib.length + overheadBytes(form) });
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
    else bruteData = filterImage(best.form.samples, width, height, best.form.bpp, 'brute');
  }
  const opt = deflateBest(bruteData);
  finals.push({ form: best.form, zlib: opt, bytes: opt.length + overheadBytes(best.form) });
  let winner = finals[0];
  for (const f of finals) if (f.bytes < winner.bytes) winner = f;
  return assembleForm(width, height, winner.form, winner.zlib);
}

// ------------------------------------------------------------------ main
for (const id of readdirSync(INPUT_DIR).sort()) {
  const image = readPng(new Uint8Array(readFileSync(join(INPUT_DIR, id, 'image.png'))));
  mkdirSync(join(OUTPUT_DIR, id), { recursive: true });
  writeFileSync(join(OUTPUT_DIR, id, 'image.png'), encodeImage(image.rgba, image.width, image.height));
}
