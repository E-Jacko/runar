/**
 * Bitcoin Script VM utilities.
 *
 * Script number encoding/decoding, truthiness checks, hex conversion, and
 * a disassembler for debugging.
 */

import { Opcode, opcodeName } from './opcodes.js';

// ---------------------------------------------------------------------------
// Script number encoding (Bitcoin's little-endian signed magnitude format)
// ---------------------------------------------------------------------------

/**
 * Encode a bigint as a Bitcoin script number (little-endian signed magnitude).
 *
 * Bitcoin script numbers use a sign-magnitude representation where the most
 * significant bit of the last byte is the sign bit.  Zero is represented as
 * an empty byte array.
 */
export function encodeScriptNumber(n: bigint): Uint8Array {
  if (n === 0n) {
    return new Uint8Array(0);
  }

  const negative = n < 0n;
  let abs = negative ? -n : n;

  const bytes: number[] = [];
  while (abs > 0n) {
    bytes.push(Number(abs & 0xffn));
    abs >>= 8n;
  }

  // If the high bit of the last byte is set, we need an extra byte for the
  // sign bit.
  const last = bytes[bytes.length - 1]!;
  if (last & 0x80) {
    bytes.push(negative ? 0x80 : 0x00);
  } else if (negative) {
    bytes[bytes.length - 1] = last | 0x80;
  }

  return new Uint8Array(bytes);
}

/**
 * Decode a Bitcoin script number from bytes to bigint.
 *
 * Empty array is 0.  Otherwise the last byte's high bit is the sign bit.
 */
export function decodeScriptNumber(bytes: Uint8Array): bigint {
  if (bytes.length === 0) {
    return 0n;
  }

  // Read bytes as little-endian unsigned.
  let result = 0n;
  for (let i = 0; i < bytes.length; i++) {
    result |= BigInt(bytes[i]!) << BigInt(8 * i);
  }

  // Check sign bit (MSB of last byte).
  const lastByte = bytes[bytes.length - 1]!;
  if (lastByte & 0x80) {
    // Clear the sign bit and negate.
    result &= ~(0x80n << BigInt(8 * (bytes.length - 1)));
    result = -result;
  }

  return result;
}

// ---------------------------------------------------------------------------
// Script-number bitwise / shift semantics (byte-array ops, NOT numeric)
// ---------------------------------------------------------------------------
//
// OP_AND/OP_OR/OP_XOR/OP_INVERT/OP_LSHIFT/OP_RSHIFT operate on the RAW BYTES of
// the operands' minimal script-number encoding, not on their numeric value
// (spec/opcodes.md). AND/OR/XOR require equal-length operands and fail
// otherwise; shifts treat the byte array as a big-endian bit string and
// preserve its length. These helpers reproduce EXACTLY what ScriptVM's opcode
// handlers do, so the interpreter (which models values as bigint) agrees with
// the deployed script byte-for-byte. A differential fuzz test pins the two
// together. Callers convert bigint -> minimal bytes -> byte op -> bigint.

// The *Bytes helpers below operate on RAW stack bytes (the exact byte array a
// value would occupy on the deployed script's stack), NOT on a value's minimal
// encoding. This matters for CHAINED expressions: OP_LSHIFT/OP_RSHIFT preserve
// their operand's byte-length and OP_AND/OP_OR/OP_XOR preserve the common
// length, so a shift/bitwise RESULT can be a NON-minimal byte array (e.g.
// `2 << 8` leaves a 1-byte 0x00, not the empty encoding of 0). When that result
// feeds a length-sensitive `& | ^` (or another shift), the deployed script sees
// the real length, so the interpreter must thread the real bytes too. Deriving
// the minimal encoding of the numeric value per-op instead would abort where the
// chain spends (and spend where the chain aborts) — a funds-relevant divergence.
// The interpreter carries these bytes on shift/bitwise/invert results and passes
// minimal encoding only for values from other sources (literals, arithmetic).

/** OP_AND/OP_OR/OP_XOR on raw stack bytes. Throws on length mismatch, exactly
 *  like the on-chain opcodes. */
export function scriptNumberBitwiseBytes(
  op: '&' | '|' | '^',
  av: Uint8Array,
  bv: Uint8Array,
): Uint8Array {
  if (av.length !== bv.length) {
    const name = op === '&' ? 'OP_AND' : op === '|' ? 'OP_OR' : 'OP_XOR';
    throw new Error(`${name}: operands must be same length`);
  }
  const result = new Uint8Array(av.length);
  for (let i = 0; i < av.length; i++) {
    const x = av[i]!;
    const y = bv[i]!;
    result[i] = op === '&' ? x & y : op === '|' ? x | y : x ^ y;
  }
  return result;
}

/** OP_INVERT: flip every bit of the operand's raw stack bytes (length-preserving). */
export function scriptNumberInvertBytes(av: Uint8Array): Uint8Array {
  const result = new Uint8Array(av.length);
  for (let i = 0; i < av.length; i++) result[i] = ~av[i]! & 0xff;
  return result;
}

/** OP_LSHIFT/OP_RSHIFT on raw stack bytes as a big-endian bit string, preserving
 *  byte length (LSHIFT masks off overflow MSBs). `shift` is the numeric shift
 *  count; the count operand is read as a number on-chain, so only `val`'s bytes
 *  are length-significant. Negative shifts fail like the opcodes. */
export function scriptNumberShiftBytes(
  op: '<<' | '>>',
  val: Uint8Array,
  shift: bigint,
): Uint8Array {
  if (shift < 0n) {
    throw new Error(op === '<<' ? 'OP_LSHIFT: negative shift' : 'OP_RSHIFT: negative shift');
  }
  const n = Number(shift);
  if (val.length === 0 || n === 0) return new Uint8Array(val);
  let num = 0n;
  for (let i = 0; i < val.length; i++) num = (num << 8n) | BigInt(val[i]!);
  if (op === '<<') {
    const bitLen = BigInt(val.length * 8);
    num = (num << BigInt(n)) & ((1n << bitLen) - 1n);
  } else {
    num >>= BigInt(n);
  }
  const result = new Uint8Array(val.length);
  for (let i = val.length - 1; i >= 0; i--) {
    result[i] = Number(num & 0xffn);
    num >>= 8n;
  }
  return result;
}

// bigint -> bigint convenience wrappers: encode each operand to its MINIMAL
// bytes, run the byte op, decode. Correct for a SINGLE op on freshly-minimal
// operands (what the per-tier truth-table tests pin); the interpreter uses the
// *Bytes helpers directly so it can thread non-minimal chained intermediates.

/** OP_AND/OP_OR/OP_XOR on two script-number-valued bigints (minimal operands). */
export function scriptNumberBitwise(op: '&' | '|' | '^', a: bigint, b: bigint): bigint {
  return decodeScriptNumber(scriptNumberBitwiseBytes(op, encodeScriptNumber(a), encodeScriptNumber(b)));
}

/** OP_INVERT on a script-number-valued bigint (minimal operand). */
export function scriptNumberInvert(a: bigint): bigint {
  return decodeScriptNumber(scriptNumberInvertBytes(encodeScriptNumber(a)));
}

/** OP_LSHIFT/OP_RSHIFT on a script-number-valued bigint (minimal operand). */
export function scriptNumberShift(op: '<<' | '>>', a: bigint, shift: bigint): bigint {
  return decodeScriptNumber(scriptNumberShiftBytes(op, encodeScriptNumber(a), shift));
}

// ---------------------------------------------------------------------------
// Stack element truthiness
// ---------------------------------------------------------------------------

/**
 * Check if a stack element is truthy.
 *
 * An element is false if it is empty, all zero bytes, or negative zero
 * (0x80 as the only non-zero byte in the last position).
 */
export function isTruthy(element: Uint8Array): boolean {
  if (element.length === 0) {
    return false;
  }

  for (let i = 0; i < element.length; i++) {
    if (element[i] !== 0) {
      // Check for negative zero: all bytes zero except the last which is 0x80.
      if (i === element.length - 1 && element[i] === 0x80) {
        return false;
      }
      return true;
    }
  }

  return false;
}

// ---------------------------------------------------------------------------
// Hex encoding / decoding
// ---------------------------------------------------------------------------

const HEX_CHARS = '0123456789abcdef';

/**
 * Convert a hex string to a Uint8Array.
 */
export function hexToBytes(hex: string): Uint8Array {
  if (hex.length % 2 !== 0) {
    throw new Error(`Invalid hex string: odd length (${hex.length})`);
  }
  const bytes = new Uint8Array(hex.length / 2);
  for (let i = 0; i < bytes.length; i++) {
    const hi = hex.charCodeAt(i * 2);
    const lo = hex.charCodeAt(i * 2 + 1);
    bytes[i] = (hexVal(hi) << 4) | hexVal(lo);
  }
  return bytes;
}

function hexVal(charCode: number): number {
  // 0-9
  if (charCode >= 48 && charCode <= 57) return charCode - 48;
  // a-f
  if (charCode >= 97 && charCode <= 102) return charCode - 87;
  // A-F
  if (charCode >= 65 && charCode <= 70) return charCode - 55;
  throw new Error(`Invalid hex character: ${String.fromCharCode(charCode)}`);
}

/**
 * Convert a Uint8Array to a lowercase hex string.
 */
export function bytesToHex(bytes: Uint8Array): string {
  let hex = '';
  for (let i = 0; i < bytes.length; i++) {
    const b = bytes[i]!;
    hex += HEX_CHARS[b >> 4];
    hex += HEX_CHARS[b & 0x0f];
  }
  return hex;
}

// ---------------------------------------------------------------------------
// Disassembler
// ---------------------------------------------------------------------------

/**
 * Disassemble a script byte array into a human-readable string of opcodes.
 */
export function disassemble(script: Uint8Array): string {
  const parts: string[] = [];
  let i = 0;

  while (i < script.length) {
    const byte = script[i]!;
    i++;

    // Direct push: 1-75 bytes
    if (byte >= 0x01 && byte <= 0x4b) {
      const data = script.slice(i, i + byte);
      parts.push(bytesToHex(data));
      i += byte;
      continue;
    }

    // OP_PUSHDATA1
    if (byte === Opcode.OP_PUSHDATA1) {
      if (i >= script.length) {
        parts.push('OP_PUSHDATA1 [TRUNCATED]');
        break;
      }
      const len = script[i]!;
      i++;
      const data = script.slice(i, i + len);
      parts.push(bytesToHex(data));
      i += len;
      continue;
    }

    // OP_PUSHDATA2
    if (byte === Opcode.OP_PUSHDATA2) {
      if (i + 1 >= script.length) {
        parts.push('OP_PUSHDATA2 [TRUNCATED]');
        break;
      }
      const len = script[i]! | (script[i + 1]! << 8);
      i += 2;
      const data = script.slice(i, i + len);
      parts.push(bytesToHex(data));
      i += len;
      continue;
    }

    // OP_PUSHDATA4
    if (byte === Opcode.OP_PUSHDATA4) {
      if (i + 3 >= script.length) {
        parts.push('OP_PUSHDATA4 [TRUNCATED]');
        break;
      }
      const len =
        script[i]! |
        (script[i + 1]! << 8) |
        (script[i + 2]! << 16) |
        (script[i + 3]! << 24);
      i += 4;
      const data = script.slice(i, i + len);
      parts.push(bytesToHex(data));
      i += len;
      continue;
    }

    // Known opcode
    parts.push(opcodeName(byte));
  }

  return parts.join(' ');
}
