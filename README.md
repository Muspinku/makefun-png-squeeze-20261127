[![make.fun bounty](https://img.shields.io/badge/make.fun-png--squeeze--01-blue)](https://make.fun/bounty/png-squeeze-01-run-20261127)
[![Node.js](https://img.shields.io/badge/node-%3E%3D22-green)](https://nodejs.org)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

# png-squeeze — smallest lossless PNG for screenshots

Entry for [make.fun's "Squeeze screenshots into the smallest PNG"](https://make.fun/bounty/png-squeeze-01-run-20261127)
($100, deadline 29 November 2026). `main.ts` (Node 22, standard library only,
no network) re-encodes each 1280×720 RGBA screenshot as the smallest valid
PNG it can find: every pixel — including a fully-transparent pixel's colour —
decodes back exactly.

## How it works

1. **Decode** the stored input PNG with our own decoder (the PNG subset the
   checker reads: bit depth 8, non-interlaced, colour types 0/2/3/4/6, only
   IHDR/PLTE/tRNS/IDAT/IEND).
2. **Try every lossless form**: palette (colour type 3, in count, luminance
   and RGB order) when the image holds at most 256 colours; grey / grey+alpha
   when every pixel is grey; RGB / RGBA otherwise; and a single-value tRNS
   key when the image is opaque except for one fully-transparent colour.
3. **Pick per-row filters** for each form: fixed None, minimum-sum heuristic,
   and brute force (each row's five filters weighed by an actual deflate of
   the row against the previous 32 KiB, as the kit's scale screen does).
   Every candidate is screened with zlib level 6.
4. **Finish**: the two best screened candidates go through zlib level 9
   (default, filtered, and memLevel 8 settings), and the winner form's
   brute-force filtered data goes through our own **optimal-parse DEFLATE
   encoder** (hash-chain LZ77, backward dynamic-programming parse under a
   Huffman cost model refined from the first pass's token frequencies,
   length-limited Huffman codes by package-merge, one dynamic block) —
   typically 1–2% smaller than zlib level 9 on photo-like and soft-shadow
   data. The smallest file wins.

The run is fully deterministic (no clock reads, no randomness, fixed work
budget): two executions on the same set write byte-identical outputs. One
set of 8 takes about 30 seconds on one CPU, inside the 60-second wall.

## Practice-set score

On the kit's practice set (scored with the kit's own `program/scorer/score.ts`):

| instance | theme | bytes | points |
|----------|-------|-------|--------|
| i001 | flat | 12,496 | 718.4 |
| i002 | rich | 51,852 | 705.5 |
| i003 | alpha | 104,889 | 685.2 |
| i004 | grey | 104,857 | 700.8 |
| i005 | flat | 16,552 | 742.3 |
| i006 | rich | 175,065 | 703.5 |
| i007 | alpha | 60,890 | 701.9 |
| i008 | grey | 24,897 | 714.2 |

**Score 708,964, passed 8/8, all exact.** The house baseline (fixed-paeth
1.0.0) scores 420,399 on the same set.

## Run it

```sh
MAKEFUN_INPUT_DIR=practice/input MAKEFUN_OUTPUT_DIR=out node main.ts
```

Reads `/input/<id>/image.png` (or `$MAKEFUN_INPUT_DIR`) and writes
`/output/<id>/image.png` (or `$MAKEFUN_OUTPUT_DIR`).

## Attribution

PNG reading/writing primitives and the filter functions follow the kit's own
`scorer/checker/png.mjs` (make.fun, MIT) and the colour-type analysis of its
`generator/subject/scale.mjs`; the filter search, screening and the
optimal-parse DEFLATE encoder are our own work. The house baseline's encoder
is derived from pngjs 7.0.0 (MIT); see the kit for its NOTICE.
