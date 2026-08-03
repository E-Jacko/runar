/**
 * Shared Bitcoin Script push-data encoding helpers.
 *
 * Extracted from `06-emit.ts` so that other passes (notably the
 * array-form `asm({ body: [OP_DUP, push(...), ...] })` parser in
 * `01-parse.ts`) can compute the exact byte encoding a literal would
 * receive at emit time, without duplicating the script-number / push-
 * data encoding rules.
 *
 * The encoder is deliberately the SAME function used by the emit
 * pass — any future change to push-data encoding must therefore land
 * here (a single source of truth) so the array-form body and the
 * eventual emitted bytes stay byte-identical.
 */
export declare function byteToHex(b: number): string;
export declare function bytesToHex(bytes: Uint8Array): string;
/**
 * Encode a bigint as a Bitcoin Script number (little-endian, sign bit in MSB).
 *
 * - 0 is the empty byte array
 * - positive: little-endian bytes, MSB's high bit clear
 * - negative: little-endian bytes, MSB's high bit set
 * - if the high bit of the most significant byte is already set, append
 *   an extra 0x00 (positive) or 0x80 (negative) byte for the sign bit
 */
export declare function encodeScriptNumber(n: bigint): Uint8Array;
/**
 * Encode a push-data operation as Bitcoin Script bytes.
 *
 * - len 1..75   : single-byte length prefix + data
 * - len 76..255 : OP_PUSHDATA1 (0x4c) + 1-byte length + data
 * - len 256..65535: OP_PUSHDATA2 (0x4d) + 2-byte LE length + data
 * - len > 65535 : OP_PUSHDATA4 (0x4e) + 4-byte LE length + data
 * - len 0       : OP_0 (single 0x00 byte)
 */
export declare function encodePushData(data: Uint8Array): Uint8Array;
/**
 * Encode a bigint push as a Bitcoin Script byte sequence (hex string).
 *
 * Uses small-integer opcodes where possible (OP_0, OP_1NEGATE, OP_1..OP_16);
 * falls back to a length-prefixed push of the script-number encoding.
 */
export declare function encodePushBigIntHex(n: bigint): string;
/**
 * Encode a raw byte-array push (MINIMALDATA aware) as a hex string.
 *
 * Mirrors `encodePushValue(Uint8Array)` in `06-emit.ts`:
 * - empty -> OP_0 ('00')
 * - single byte 1..16 -> OP_1..OP_16
 * - single byte 0x81 -> OP_1NEGATE
 * - else length-prefixed push (with OP_PUSHDATA{1,2,4} as needed)
 *
 * Note: 0x00 is NOT converted to OP_0 because OP_0 pushes [] not [0x00].
 */
export declare function encodePushBytesHex(value: Uint8Array): string;
//# sourceMappingURL=push-encoding.d.ts.map