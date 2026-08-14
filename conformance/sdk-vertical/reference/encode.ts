// ---------------------------------------------------------------------------
// conformance/sdk-vertical/reference/encode.ts
// ---------------------------------------------------------------------------
//
// An INDEPENDENT implementation of the deploy-time constructor-arg encoding,
// written from the artifact's declared `valueEncoding` contract (see
// `ConstructorSlot` in packages/runar-ir-schema/src/artifact.ts) plus the
// Bitcoin push-data rules. It imports nothing from any SDK or compiler.
//
// This is the SPECIFICATION side of the C3 pin. The semantic side lives in
// derive.ts, which additionally disassembles the finished script and checks
// that the stack item the slot actually pushes is the intended value — a
// check that holds no matter which of several byte encodings a tier picked.
// ---------------------------------------------------------------------------

export type ValueEncoding = 'data' | 'scriptnum' | 'bool';

/** A constructor argument as it appears in a case's `input.json`. */
export interface TypedArg {
  /** ABI type name: bigint / int / bool / ByteString / PubKey / Addr / ... */
  type: string;
  /** Decimal string for bigint, 'true'/'false' for bool, lowercase hex
   *  otherwise (the empty string is a legal, and load-bearing, hex value). */
  value: string;
}

/** Push-data encode raw value bytes, MINIMALDATA-collapsing the single-byte
 *  encodings that have a dedicated opcode.
 *
 *  The two collapses are the fund-safety-relevant part:
 *    - a 1-byte payload 0x01..0x10 becomes the single opcode OP_1..OP_16
 *    - a 1-byte payload 0x81 becomes the single opcode OP_1NEGATE
 *  and the two NON-collapses matter just as much:
 *    - a 1-byte payload 0x00 is `01 00`, NEVER OP_0. OP_0 pushes the EMPTY
 *      item; `01 00` pushes one zero byte. They are different stack values,
 *      and confusing them is the 2026-08 state-framing bug (PALMER-2) that
 *      shipped through all seven SDKs at once.
 *    - the empty payload IS OP_0, which pushes the empty item.
 */
export function encodePushData(dataHex: string): string {
  if (dataHex.length % 2 !== 0) {
    throw new Error(`push data hex has odd length ${dataHex.length}`);
  }
  const len = dataHex.length / 2;
  if (len === 0) return '00'; // OP_0 — pushes the empty item

  if (len === 1) {
    const byte = parseInt(dataHex, 16);
    if (byte >= 0x01 && byte <= 0x10) return (0x50 + byte).toString(16).padStart(2, '0');
    if (byte === 0x81) return '4f';
    // 0x00 deliberately falls through to the direct push `01 00`.
  }

  if (len <= 75) return len.toString(16).padStart(2, '0') + dataHex;
  if (len <= 0xff) return '4c' + len.toString(16).padStart(2, '0') + dataHex;
  if (len <= 0xffff) {
    const lo = (len & 0xff).toString(16).padStart(2, '0');
    const hi = ((len >> 8) & 0xff).toString(16).padStart(2, '0');
    return '4d' + lo + hi + dataHex;
  }
  const b = [len & 0xff, (len >> 8) & 0xff, (len >> 16) & 0xff, (len >>> 24) & 0xff];
  return '4e' + b.map((x) => x.toString(16).padStart(2, '0')).join('') + dataHex;
}

/** Minimal Script-number encoding: OP_0 / OP_1..OP_16 / OP_1NEGATE, else a
 *  push of the little-endian sign-magnitude bytes. */
export function encodeScriptNumber(n: bigint): string {
  if (n === 0n) return '00';
  if (n === -1n) return '4f';
  if (n >= 1n && n <= 16n) return (0x50 + Number(n)).toString(16).padStart(2, '0');

  const negative = n < 0n;
  let abs = negative ? -n : n;
  const bytes: number[] = [];
  while (abs > 0n) {
    bytes.push(Number(abs & 0xffn));
    abs >>= 8n;
  }
  if ((bytes[bytes.length - 1]! & 0x80) !== 0) {
    bytes.push(negative ? 0x80 : 0x00);
  } else if (negative) {
    bytes[bytes.length - 1]! |= 0x80;
  }
  return encodePushData(bytes.map((b) => b.toString(16).padStart(2, '0')).join(''));
}

/** Normalise a case's typed arg to the raw VALUE it is meant to place on the
 *  stack: a bigint for scriptnum slots, a boolean for bool slots, lowercase
 *  hex bytes for data slots. */
export function argValue(arg: TypedArg): bigint | boolean | string {
  switch (arg.type) {
    case 'bigint':
    case 'int':
      return BigInt(arg.value);
    case 'bool':
    case 'boolean':
      if (arg.value !== 'true' && arg.value !== 'false') {
        throw new Error(`bool arg must be 'true' or 'false', got '${arg.value}'`);
      }
      return arg.value === 'true';
    default:
      return arg.value.toLowerCase();
  }
}

/**
 * Encode one constructor argument for splicing into a template slot, using
 * the encoding class the COMPILER declared for that slot.
 *
 * Taking the class from the artifact rather than re-deriving it from the
 * argument's runtime type is deliberate: it makes the compiler's declaration
 * load-bearing, so a slot whose `valueEncoding` disagrees with the value the
 * ABI says goes there fails here rather than silently producing bytes.
 */
export function encodeSlotValue(encoding: ValueEncoding, arg: TypedArg): string {
  const value = argValue(arg);
  switch (encoding) {
    case 'scriptnum':
      if (typeof value !== 'bigint') {
        throw new Error(`slot declares valueEncoding 'scriptnum' but arg is ${arg.type}`);
      }
      return encodeScriptNumber(value);
    case 'bool':
      if (typeof value !== 'boolean') {
        throw new Error(`slot declares valueEncoding 'bool' but arg is ${arg.type}`);
      }
      return value ? '51' : '00';
    case 'data':
      if (typeof value !== 'string') {
        throw new Error(`slot declares valueEncoding 'data' but arg is ${arg.type}`);
      }
      if (!/^[0-9a-f]*$/.test(value)) {
        throw new Error(`data arg must be lowercase hex, got '${arg.value}'`);
      }
      return encodePushData(value);
    default:
      throw new Error(`unknown valueEncoding '${encoding}'`);
  }
}

/** The stack item a correctly-spliced slot must push, as lowercase hex.
 *  Mirrors `ScriptOp.pushedHex` from the walker so the two can be compared. */
export function expectedPushedHex(encoding: ValueEncoding, arg: TypedArg): string {
  const value = argValue(arg);
  if (encoding === 'bool') return value === true ? '01' : '';
  if (encoding === 'scriptnum') {
    const n = value as bigint;
    if (n === 0n) return '';
    const negative = n < 0n;
    let abs = negative ? -n : n;
    const bytes: number[] = [];
    while (abs > 0n) {
      bytes.push(Number(abs & 0xffn));
      abs >>= 8n;
    }
    if ((bytes[bytes.length - 1]! & 0x80) !== 0) {
      bytes.push(negative ? 0x80 : 0x00);
    } else if (negative) {
      bytes[bytes.length - 1]! |= 0x80;
    }
    return bytes.map((b) => b.toString(16).padStart(2, '0')).join('');
  }
  return value as string;
}
