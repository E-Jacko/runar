// ---------------------------------------------------------------------------
// conformance/sdk-vertical/matrix.ts — the C1 value-class matrix, applied to
// CONSTRUCTOR ARGS (remediation plan §3 C1/C3).
// ---------------------------------------------------------------------------
//
// Each row is one deployment of one compiled template. Rows vary a single
// value class at a time against fixed neighbours, so a failure names the
// class rather than "something in this contract changed".
//
// To add a row: append to MATRIX, run `npx tsx sdk-vertical/generate.ts` from
// conformance/, and review the golden diff. See README.md.
// ---------------------------------------------------------------------------

import type { TypedArg } from './reference/encode.js';

export interface MatrixRow {
  /** Case directory name under cases/. */
  name: string;
  /** Contract whose artifact this row deploys. */
  contract: 'SlotMatrix' | 'SlotBool' | 'CodeSepMatrix';
  /** Which value class this row exists to cover (echoed into the README table). */
  valueClass: string;
  constructorArgs: TypedArg[];
}

/** Standard secp256k1 generator-derived compressed pubkey, as used by
 *  conformance/sdk-output/generate-inputs.ts. */
export const PK = '0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798';

/** 76 bytes — one past the 75-byte direct-push ceiling, so the slot must use
 *  OP_PUSHDATA1 (a 2-byte header). Exercises the header-width class that a
 *  fixed "1 header byte" assumption gets wrong. */
const BYTES_76 = 'aa'.repeat(76);

const B = (v: string): TypedArg => ({ type: 'ByteString', value: v });
const N = (v: string): TypedArg => ({ type: 'bigint', value: v });
const P = (): TypedArg => ({ type: 'PubKey', value: PK });
const BOOL = (v: boolean): TypedArg => ({ type: 'bool', value: v ? 'true' : 'false' });

// SlotMatrix ctor: (count: bigint, tag: ByteString, owner: PubKey)
const slot = (name: string, valueClass: string, count: string, tag: string): MatrixRow => ({
  name,
  contract: 'SlotMatrix',
  valueClass,
  constructorArgs: [N(count), B(tag), P()],
});

// CodeSepMatrix ctor: (note: ByteString, tag: ByteString, owner: PubKey)
const codesep = (name: string, valueClass: string, tag: string): MatrixRow => ({
  name,
  contract: 'CodeSepMatrix',
  valueClass,
  constructorArgs: [B('48656c6c6f'), B(tag), P()],
});

export const MATRIX: MatrixRow[] = [
  // --- bigint edges (scriptnum slot; tag/owner held fixed) -----------------
  slot('bigint-0', 'bigint 0 → OP_0 (pushes the EMPTY item)', '0', '11'),
  slot('bigint-1', 'bigint 1 → OP_1 (single opcode, no push header)', '1', '11'),
  slot('bigint-neg1', 'bigint -1 → OP_1NEGATE (single opcode)', '-1', '11'),
  slot('bigint-16', 'bigint 16 → OP_16, the top of the single-opcode range', '16', '11'),
  slot('bigint-17', 'bigint 17 → first value that becomes a 1-byte push', '17', '11'),
  slot('bigint-127', 'bigint 127 → 1 payload byte, high bit clear', '127', '11'),
  slot('bigint-128', 'bigint 128 → 2 payload bytes (sign-magnitude pad)', '128', '11'),
  slot('bigint-neg128', 'bigint -128 → 2 payload bytes with the sign bit set', '-128', '11'),
  slot('bigint-large', 'bigint large (> 2^63) → multi-byte push', '12345678901234567890', '11'),
  slot('bigint-neg16', 'bigint -16 → negative mirror of OP_16, must NOT collapse to an opcode (0190)', '-16', '11'),
  slot('bigint-neg17', 'bigint -17 → one past the negative mirror (0191)', '-17', '11'),
  slot('bigint-neg129', 'bigint -129 → the append-a-pad-byte branch (028180); -128 alone cannot distinguish append from OR (both give 8080)', '-129', '11'),
  slot('bigint-neg-large', 'bigint -12345678901234567890 → large-negative append path (09d20a1feb8ca954ab80)', '-12345678901234567890', '11'),

  // --- ByteString value classes (data slot; count held fixed) --------------
  slot('bytes-empty', 'ByteString "" → OP_0 (byte-identical to the untouched placeholder)', '7', ''),
  slot('bytes-zero', 'ByteString 0x00 → MUST be the direct push 0100, never OP_0', '7', '00'),
  slot('bytes-op-n-low', 'ByteString 0x01 → OP_1 (MINIMALDATA collapse, no push header)', '7', '01'),
  slot('bytes-op-n-mid', 'ByteString 0x05 → OP_5', '7', '05'),
  slot('bytes-op-n-high', 'ByteString 0x10 → OP_16, top of the collapse range', '7', '10'),
  slot('bytes-op1negate', 'ByteString 0x81 → OP_1NEGATE', '7', '81'),
  slot('bytes-outside-low', 'ByteString 0x11 → 1 past the collapse range, direct push 0111', '7', '11'),
  slot('bytes-outside-high', 'ByteString 0xff → direct push 01ff', '7', 'ff'),
  slot('bytes-ab-trap', 'ByteString 0xab → push DATA equal to OP_CODESEPARATOR; a naive hex scan false-positives', '7', 'ab'),
  slot('bytes-multi-2', 'ByteString 0x0011 → 2-byte push', '7', '0011'),
  slot('bytes-multi-4', 'ByteString 0xdeadbeef → 4-byte push', '7', 'deadbeef'),
  slot('bytes-pushdata1', 'ByteString 76 bytes → OP_PUSHDATA1, a 2-byte push header', '7', BYTES_76),
  slot('bytes-75', 'ByteString 75 bytes → 0x4b + data, the top of the direct-push range (< vs <= the 0x4c PUSHDATA1 boundary)', '7', 'aa'.repeat(75)),
  slot('bytes-255', 'ByteString 255 bytes → OP_PUSHDATA1 top (0x4c ff + data)', '7', 'aa'.repeat(255)),
  slot('bytes-256', 'ByteString 256 bytes → first OP_PUSHDATA2 (0x4d 00 01 + data)', '7', 'aa'.repeat(256)),
  slot('bytes-pushdata2', 'ByteString 300 bytes → OP_PUSHDATA2 with BOTH length bytes non-zero (0x4d 2c 01 + data); a byte-swapped LE length is otherwise undetectable', '7', 'aa'.repeat(300)),

  // --- multi-slot combinations --------------------------------------------
  slot('multi-slot-mixed-a', 'mixed: scriptnum single-opcode + data collapse + fixed 33B', '-1', '05'),
  slot('multi-slot-mixed-b', 'mixed: multi-byte scriptnum + 1-byte 0x00 data + fixed 33B', '128', '00'),

  // --- bool ---------------------------------------------------------------
  { name: 'bool-true', contract: 'SlotBool', valueClass: 'bool true → OP_TRUE (0x51)', constructorArgs: [BOOL(true), P()] },
  { name: 'bool-false', contract: 'SlotBool', valueClass: 'bool false → OP_0 (0x00, identical to the placeholder byte)', constructorArgs: [BOOL(false), P()] },

  // --- codeSeparator offsets (C4): CodeSepMatrix has THREE public methods —
  //     bump, reseal, close, in that declaration order — each auto-injecting
  //     its own OP_CODESEPARATOR. `tag` sits inside `bump`'s branch, so it
  //     lands BEFORE bump's own separator (constant: nothing precedes it) but
  //     BEFORE reseal's and close's, whose baked codeSepIndexSlot values shift
  //     by tag's encoded width (remediation plan P0-1 — before `reseal` was
  //     added, the artifact's only codeSepIndexSlot targeted bump's own
  //     always-first, always-1-byte separator, so every row baked the SAME
  //     constant regardless of `tag`). Rows differ by exactly the value class,
  //     so the deployed codesep offsets — and reseal's baked value — must
  //     differ too.
  codesep('codesep-tag-empty', 'codesep shift 0: ByteString "" → OP_0', ''),
  codesep('codesep-tag-op-n', 'codesep shift 0: ByteString 0x05 → OP_5 (1 byte)', '05'),
  codesep('codesep-tag-zero', 'codesep shift +1: ByteString 0x00 → 0100 (2 bytes)', '00'),
  codesep('codesep-tag-multi', 'codesep shift +4: ByteString 0xdeadbeef (5 bytes)', 'deadbeef'),
  codesep('codesep-tag-ab-trap', 'codesep + 0xab bytes in push data near the separator', 'ababab'),
  codesep('codesep-tag-pushdata1', 'codesep shift +77: 76-byte ByteString via OP_PUSHDATA1', BYTES_76),
];
