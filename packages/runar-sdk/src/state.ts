// ---------------------------------------------------------------------------
// runar-sdk/state.ts -- State management for stateful contracts
// ---------------------------------------------------------------------------
//
// Stateful Runar contracts embed their state in the locking script as a
// suffix of OP_RETURN-delimited data pushes. The state section follows
// the contract's compiled code and is structured as:
//
//   <code> OP_RETURN <field0> <field1> ... <fieldN>
//
// Each field is encoded as a Bitcoin Script push according to its type.
// ---------------------------------------------------------------------------

import type { StateField, RunarArtifact } from 'runar-ir-schema';
import { STATE_FIELD_WIDTHS } from 'runar-ir-schema';

/**
 * Serialize a set of state values into a hex-encoded Bitcoin Script data
 * section (without the OP_RETURN prefix -- that is handled by the caller).
 *
 * Field order is determined by the `index` property of each StateField.
 *
 * Fields with a `fixedArray` annotation are expanded into N element writes
 * in declaration order; callers may supply either a plain array on the
 * grouped name (`values.Board = [...]`) or the underlying scalar fields
 * (`values.Board__0 = ..., values.Board__1 = ..., ...`) — scalars win if
 * both are present, for backward compatibility.
 */
export function serializeState(
  fields: StateField[],
  values: Record<string, unknown>,
): string {
  const sorted = [...fields].sort((a, b) => a.index - b.index);
  let hex = '';

  for (const field of sorted) {
    if (field.fixedArray) {
      const arr = values[field.name];
      const names = field.fixedArray.syntheticNames;
      // Derive the leaf scalar type by peeling off every FixedArray
      // layer from the declared `field.type`. The grouped entry's
      // `elementType` is only the immediate child — for nested arrays
      // it is itself another FixedArray<...>, which `encodeStateValue`
      // does not know how to serialise.
      const leafType = unwrapFixedArrayLeaf(field.type);
      const dims = parseFixedArrayDims(field.type);
      const flatFromArr = Array.isArray(arr) ? flattenNested(arr, dims) : null;
      for (let i = 0; i < names.length; i++) {
        let elem: unknown;
        const synthName = names[i]!;
        if (synthName in values) {
          elem = values[synthName];
        } else if (flatFromArr) {
          elem = flatFromArr[i];
        } else {
          elem = undefined;
        }
        hex += encodeStateValue(elem, leafType);
      }
    } else {
      const value = values[field.name];
      hex += encodeStateValue(value, field.type);
    }
  }

  return hex;
}

/**
 * Parse a nested `FixedArray<...>` type string into its outer
 * dimensions: `"FixedArray<FixedArray<bigint, 2>, 3>"` → `[3, 2]`.
 * Non-FixedArray types return `[]`.
 */
function parseFixedArrayDims(type: string): number[] {
  const dims: number[] = [];
  let current = type.trim();
  while (current.startsWith('FixedArray<')) {
    const inner = current.slice('FixedArray<'.length, -1);
    let depth = 0;
    let splitAt = -1;
    for (let i = inner.length - 1; i >= 0; i--) {
      const ch = inner[i]!;
      if (ch === '>') depth++;
      else if (ch === '<') depth--;
      else if (ch === ',' && depth === 0) {
        splitAt = i;
        break;
      }
    }
    if (splitAt < 0) return dims;
    const elemType = inner.slice(0, splitAt).trim();
    const lenStr = inner.slice(splitAt + 1).trim();
    const len = Number.parseInt(lenStr, 10);
    if (!Number.isFinite(len) || len <= 0) return dims;
    dims.push(len);
    current = elemType;
  }
  return dims;
}

/** Return the innermost scalar type of a (possibly nested) FixedArray string. */
function unwrapFixedArrayLeaf(type: string): string {
  let current = type.trim();
  while (current.startsWith('FixedArray<')) {
    const inner = current.slice('FixedArray<'.length, -1);
    let depth = 0;
    let splitAt = -1;
    for (let i = inner.length - 1; i >= 0; i--) {
      const ch = inner[i]!;
      if (ch === '>') depth++;
      else if (ch === '<') depth--;
      else if (ch === ',' && depth === 0) {
        splitAt = i;
        break;
      }
    }
    if (splitAt < 0) return current;
    current = inner.slice(0, splitAt).trim();
  }
  return current;
}

/** Flatten a nested JS array of depth `dims.length` to a flat leaf list. */
function flattenNested(value: unknown, dims: number[]): unknown[] {
  if (dims.length === 0) return [value];
  if (!Array.isArray(value)) {
    const total = dims.reduce((a, b) => a * b, 1);
    return new Array(total).fill(undefined);
  }
  const rest = dims.slice(1);
  const out: unknown[] = [];
  for (const v of value) out.push(...flattenNested(v, rest));
  return out;
}

/** Rebuild a nested JS array of depth `dims.length` from a flat leaf list. */
function regroupNested(flat: unknown[], dims: number[], offset = 0): { value: unknown[]; consumed: number } {
  const [outerLen, ...rest] = dims;
  if (outerLen === undefined) return { value: [], consumed: 0 };
  const value: unknown[] = new Array(outerLen);
  let consumed = 0;
  if (rest.length === 0) {
    for (let i = 0; i < outerLen; i++) value[i] = flat[offset + i];
    consumed = outerLen;
  } else {
    for (let i = 0; i < outerLen; i++) {
      const sub = regroupNested(flat, rest, offset + consumed);
      value[i] = sub.value;
      consumed += sub.consumed;
    }
  }
  return { value, consumed };
}

/**
 * Deserialize state values from a hex-encoded Bitcoin Script data section.
 *
 * The caller must strip the code prefix and OP_RETURN byte before passing
 * the data section.
 *
 * Fields with a `fixedArray` annotation are returned as a plain JS array on
 * the grouped name, not as N individual scalar fields.
 *
 * FAILS CLOSED (C28). The blob is read back out of a locking script that any
 * third party can construct, so it is untrusted input. A state section that
 * does not describe EXACTLY the artifact's `stateFields` is rejected:
 *
 *  - truncation — a field that runs past the end of the blob throws instead of
 *    yielding a short slice (which previously decoded as a plausible-but-wrong
 *    value: a missing `boolean` byte read as `true`, a clipped `bigint` as a
 *    different number, a clipped `PubKey` as a stub key);
 *  - overlong tails — bytes left over after the last declared field throw
 *    instead of being silently dropped.
 *
 * Restoring wrong-but-plausible state from a corrupted continuation is worse
 * than not restoring it at all: the caller then signs a continuation output
 * committing to that state.
 */
export function deserializeState(
  fields: StateField[],
  scriptHex: string,
): Record<string, unknown> {
  if (scriptHex.length % 2 !== 0) {
    throw new Error(
      `deserializeState: state blob is ${scriptHex.length} hex chars — not a whole number of bytes`,
    );
  }

  const sorted = [...fields].sort((a, b) => a.index - b.index);
  const result: Record<string, unknown> = {};
  let offset = 0;

  for (const field of sorted) {
    if (field.fixedArray) {
      const leafType = unwrapFixedArrayLeaf(field.type);
      const dims = parseFixedArrayDims(field.type);
      const total = field.fixedArray.syntheticNames.length;
      const flat: unknown[] = new Array(total);
      for (let i = 0; i < total; i++) {
        const { value, bytesRead } = decodeStateValue(
          scriptHex,
          offset,
          leafType,
          `${field.name}[${i}]`,
        );
        flat[i] = value;
        offset += bytesRead;
      }
      result[field.name] = regroupNested(flat, dims).value;
    } else {
      const { value, bytesRead } = decodeStateValue(scriptHex, offset, field.type, field.name);
      result[field.name] = value;
      offset += bytesRead;
    }
  }

  if (offset !== scriptHex.length) {
    throw new Error(
      `deserializeState: ${(scriptHex.length - offset) / 2} unexpected trailing byte(s) after the ` +
        `last state field (consumed ${offset / 2} of ${scriptHex.length / 2} bytes) — the state ` +
        `section does not match the artifact's stateFields`,
    );
  }

  return result;
}

/**
 * Extract state from a full locking script hex, given the artifact.
 *
 * Returns null if the artifact has no state fields or the script doesn't
 * contain a recognisable state section.
 */
export function extractStateFromScript(
  artifact: RunarArtifact,
  scriptHex: string,
): Record<string, unknown> | null {
  if (!artifact.stateFields || artifact.stateFields.length === 0) {
    return null;
  }

  const opReturnPos = findLastOpReturn(scriptHex);
  if (opReturnPos === -1) {
    return null;
  }

  // State data starts after the OP_RETURN byte (2 hex chars)
  const stateHex = scriptHex.slice(opReturnPos + 2);
  return deserializeState(artifact.stateFields, stateHex);
}

/**
 * Walk the script hex as Bitcoin Script opcodes to find the last OP_RETURN
 * (0x6a) at a real opcode boundary. Unlike `lastIndexOf('6a')`, this
 * properly skips push data so it won't match 0x6a bytes inside data payloads.
 *
 * Returns the hex-char offset of the last OP_RETURN, or -1 if not found.
 */
export function findLastOpReturn(scriptHex: string): number {
  let offset = 0;
  const len = scriptHex.length;

  while (offset + 2 <= len) {
    const opcode = parseInt(scriptHex.slice(offset, offset + 2), 16);

    if (opcode === 0x6a) {
      // OP_RETURN at a real opcode boundary. Everything after OP_RETURN is
      // raw state data (not opcodes), so stop walking immediately.
      return offset;
    } else if (opcode >= 0x01 && opcode <= 0x4b) {
      // Direct push: opcode is the number of bytes to push
      offset += 2 + opcode * 2;
    } else if (opcode === 0x4c) {
      // OP_PUSHDATA1: next 1 byte is the length
      if (offset + 4 > len) break;
      const pushLen = parseInt(scriptHex.slice(offset + 2, offset + 4), 16);
      offset += 4 + pushLen * 2;
    } else if (opcode === 0x4d) {
      // OP_PUSHDATA2: next 2 bytes (LE) are the length
      if (offset + 6 > len) break;
      const lo = parseInt(scriptHex.slice(offset + 2, offset + 4), 16);
      const hi = parseInt(scriptHex.slice(offset + 4, offset + 6), 16);
      const pushLen = lo | (hi << 8);
      offset += 6 + pushLen * 2;
    } else if (opcode === 0x4e) {
      // OP_PUSHDATA4: next 4 bytes (LE) are the length
      if (offset + 10 > len) break;
      const b0 = parseInt(scriptHex.slice(offset + 2, offset + 4), 16);
      const b1 = parseInt(scriptHex.slice(offset + 4, offset + 6), 16);
      const b2 = parseInt(scriptHex.slice(offset + 6, offset + 8), 16);
      const b3 = parseInt(scriptHex.slice(offset + 8, offset + 10), 16);
      const pushLen = b0 | (b1 << 8) | (b2 << 16) | (b3 << 24);
      offset += 10 + pushLen * 2;
    } else {
      // All other opcodes (OP_0, OP_1..OP_16, OP_IF, OP_ADD, etc.)
      offset += 2;
    }
  }

  return -1;
}

// ---------------------------------------------------------------------------
// Encoding helpers
// ---------------------------------------------------------------------------

/**
 * Encode a state field as raw bytes (no push opcode wrapper) matching the
 * compiler's OP_NUM2BIN-based fixed-width serialization.
 * The result is raw hex bytes that are concatenated after OP_RETURN.
 */
function encodeStateValue(value: unknown, type: string): string {
  switch (type) {
    case 'int':
    case 'bigint': {
      let n: bigint;
      if (typeof value === 'bigint') {
        n = value;
      } else if (typeof value === 'string' && value.endsWith('n')) {
        // BigInt string from JSON without reviver (e.g. "0n", "1000n")
        n = BigInt(value.slice(0, -1));
      } else {
        n = BigInt(value as number);
      }
      return encodeNum2Bin(n, 8);
    }
    case 'bool':
    case 'boolean': {
      // 1 raw byte — matches on-chain serialization (05-stack-lower.ts
      // `case 'boolean': propSizes.push(1)`), decodeStateValue, and the shared
      // STATE_FIELD_WIDTHS table. The canonical Rúnar primitive name is
      // `boolean`; `bool` is accepted as an alias. Without the `boolean` case
      // a real boolean state field fell through to the push-data `default`,
      // silently disagreeing with all three (the descriptor drift #115's
      // review flagged).
      return value ? '01' : '00';
    }
    case 'PubKey':
    case 'Addr':
    case 'Ripemd160':
    case 'Sha256':
    case 'Point':
      // Fixed-size byte types: raw hex, no framing needed.
      return String(value);
    default: {
      // Variable-length types (bytes, ByteString, etc.): use push-data
      // encoding so the decoder can determine the length.
      const hex = String(value);
      if (hex.length === 0) return '00'; // OP_0
      return encodePushDataState(hex);
    }
  }
}

/**
 * Encode an integer as a fixed-width LE sign-magnitude byte string,
 * matching OP_NUM2BIN behaviour. The sign bit is in the MSB of the last byte.
 */
function encodeNum2Bin(n: bigint, width: number): string {
  const bytes = new Uint8Array(width);
  const negative = n < 0n;
  let absVal = negative ? -n : n;

  for (let i = 0; i < width && absVal > 0n; i++) {
    bytes[i] = Number(absVal & 0xffn);
    absVal >>= 8n;
  }

  if (negative) {
    bytes[width - 1]! |= 0x80;
  }

  return Array.from(bytes)
    .map((b) => b.toString(16).padStart(2, '0'))
    .join('');
}

/**
 * Encode variable-length data as Bitcoin Script push data (with length prefix).
 *
 * Applies BSV consensus rule `SCRIPT_VERIFY_MINIMALDATA` for single-byte
 * pushes: a 1-byte payload whose value is in `{0x01..=0x10, 0x81}` MUST use
 * the corresponding minimal opcode (`OP_1..OP_16` / `OP_1NEGATE`) rather than
 * the direct push `01 NN`. Non-minimal direct pushes are rejected by ARC,
 * TAAL ARC, and WhatsOnChain at the relay layer with:
 * `non-mandatory-script-verify-flag (Data push larger than necessary)`.
 *
 * NOTE: 0x00 is deliberately NOT in that set. `OP_0` pushes the EMPTY byte
 * array, not a 1-byte `0x00` — so the minimal encoding of a 1-byte `0x00`
 * payload is the direct push `01 00` (matching the compiler's
 * `encodePushBytesHex` in push-encoding.ts), not `OP_0` (C9 / S1).
 */
function encodePushDataState(dataHex: string): string {
  const len = dataHex.length / 2;
  // MINIMALDATA: single-byte payloads in the OP_N range must use the
  // corresponding minimal opcode. The `encodeScriptNumber` path for Int
  // fields already short-circuits to OP_N; this brings the ByteString path
  // to the same standard so a 1-byte ByteString state field does not emit a
  // relay-rejected non-minimal direct push.
  if (len === 1) {
    const byte = parseInt(dataHex, 16);
    if (byte >= 0x01 && byte <= 0x10) return (0x50 + byte).toString(16).padStart(2, '0'); // OP_1..OP_16
    if (byte === 0x81) return '4f'; // OP_1NEGATE
  }
  if (len <= 75) {
    return len.toString(16).padStart(2, '0') + dataHex;
  } else if (len <= 0xff) {
    return '4c' + len.toString(16).padStart(2, '0') + dataHex;
  } else if (len <= 0xffff) {
    const lo = (len & 0xff).toString(16).padStart(2, '0');
    const hi = ((len >> 8) & 0xff).toString(16).padStart(2, '0');
    return '4d' + lo + hi + dataHex;
  }
  const b0 = (len & 0xff).toString(16).padStart(2, '0');
  const b1 = ((len >> 8) & 0xff).toString(16).padStart(2, '0');
  const b2 = ((len >> 16) & 0xff).toString(16).padStart(2, '0');
  const b3 = ((len >> 24) & 0xff).toString(16).padStart(2, '0');
  return '4e' + b0 + b1 + b2 + b3 + dataHex;
}

// ---------------------------------------------------------------------------
// Decoding helpers
// ---------------------------------------------------------------------------

function decodeStateValue(
  hex: string,
  offset: number,
  type: string,
  label: string,
): { value: unknown; bytesRead: number } {
  // Fixed-width types read exactly `size` raw bytes; widths come from the
  // shared runar-ir-schema table so the codec, the compiler's stateField
  // layout annotations, and verifier tooling can never drift apart.
  const width = STATE_FIELD_WIDTHS[type];
  if (width) {
    const hexWidth = width.size * 2;
    if (offset + hexWidth > hex.length) {
      throw new Error(
        `deserializeState: truncated state — field "${label}" (${type}) needs ${width.size} byte(s) ` +
          `at offset ${offset / 2} but only ${(hex.length - offset) / 2} byte(s) remain`,
      );
    }
    const data = hex.slice(offset, offset + hexWidth);
    switch (width.encoding) {
      case 'bool1':
        // 1 raw byte: 0x00 = false, 0x01 = true
        return { value: data !== '00', bytesRead: hexWidth };
      case 'num2bin-le8':
        // 8 raw bytes LE sign-magnitude (NUM2BIN 8)
        return { value: decodeNum2Bin(data), bytesRead: hexWidth };
      default:
        // Raw fixed-size byte types (PubKey 33, Addr/Ripemd160 20, Sha256 32, Point 64)
        return { value: data, bytesRead: hexWidth };
    }
  }
  // For variable-length / unknown types, fall back to push-data decoding
  const { data, bytesRead } = decodePushData(hex, offset, label);
  return { value: data, bytesRead };
}

/**
 * Decode a fixed-width LE sign-magnitude number.
 */
function decodeNum2Bin(hex: string): bigint {
  if (hex.length === 0) return 0n;
  const bytes: number[] = [];
  for (let i = 0; i < hex.length; i += 2) {
    bytes.push(parseInt(hex.slice(i, i + 2), 16));
  }

  const negative = (bytes[bytes.length - 1]! & 0x80) !== 0;
  bytes[bytes.length - 1]! &= 0x7f;

  let result = 0n;
  for (let i = bytes.length - 1; i >= 0; i--) {
    result = (result << 8n) | BigInt(bytes[i]!);
  }

  if (result === 0n) return 0n;
  return negative ? -result : result;
}

/**
 * Decode a Bitcoin Script push data at the given hex offset.
 * Returns the pushed data (hex) and the total number of hex chars consumed.
 *
 * Inverse of `encodePushDataState`'s MINIMALDATA short-circuit: `OP_1..OP_16`
 * (0x51..0x60) and `OP_1NEGATE` (0x4f) each push a single byte with no
 * separate data bytes in the script — the opcode itself encodes the value
 * (C9). `OP_0` (0x00) falls through to the `opcode <= 75` branch below and
 * correctly decodes as the empty byte array (0-length push), since the
 * encoder no longer emits OP_0 for a 1-byte `0x00` payload.
 */
function decodePushData(
  hex: string,
  offset: number,
  label: string,
): { data: string; bytesRead: number } {
  /** Assert `chars` hex chars are available from `offset`, else fail closed. */
  const need = (chars: number, what: string): void => {
    if (offset + chars > hex.length) {
      throw new Error(
        `deserializeState: truncated state — field "${label}" ${what} runs past the end of the ` +
          `state section (needs ${chars / 2} byte(s) at offset ${offset / 2}, ` +
          `only ${(hex.length - offset) / 2} remain)`,
      );
    }
  };

  need(2, 'push opcode');
  const opcode = parseInt(hex.slice(offset, offset + 2), 16);
  if (Number.isNaN(opcode)) {
    throw new Error(
      `deserializeState: field "${label}" — non-hex byte at offset ${offset / 2} in the state section`,
    );
  }

  if (opcode >= 0x51 && opcode <= 0x60) {
    // OP_1..OP_16
    return { data: (opcode - 0x50).toString(16).padStart(2, '0'), bytesRead: 2 };
  } else if (opcode === 0x4f) {
    // OP_1NEGATE
    return { data: '81', bytesRead: 2 };
  } else if (opcode <= 75) {
    // Direct push: opcode is the byte length
    const dataLen = opcode * 2;
    need(2 + dataLen, 'push payload');
    return {
      data: hex.slice(offset + 2, offset + 2 + dataLen),
      bytesRead: 2 + dataLen,
    };
  } else if (opcode === 0x4c) {
    // OP_PUSHDATA1
    need(4, 'OP_PUSHDATA1 length prefix');
    const len = parseInt(hex.slice(offset + 2, offset + 4), 16);
    const dataLen = len * 2;
    need(4 + dataLen, 'OP_PUSHDATA1 payload');
    return {
      data: hex.slice(offset + 4, offset + 4 + dataLen),
      bytesRead: 4 + dataLen,
    };
  } else if (opcode === 0x4d) {
    // OP_PUSHDATA2
    need(6, 'OP_PUSHDATA2 length prefix');
    const lo = parseInt(hex.slice(offset + 2, offset + 4), 16);
    const hi = parseInt(hex.slice(offset + 4, offset + 6), 16);
    const len = lo | (hi << 8);
    const dataLen = len * 2;
    need(6 + dataLen, 'OP_PUSHDATA2 payload');
    return {
      data: hex.slice(offset + 6, offset + 6 + dataLen),
      bytesRead: 6 + dataLen,
    };
  } else if (opcode === 0x4e) {
    // OP_PUSHDATA4
    need(10, 'OP_PUSHDATA4 length prefix');
    const b0 = parseInt(hex.slice(offset + 2, offset + 4), 16);
    const b1 = parseInt(hex.slice(offset + 4, offset + 6), 16);
    const b2 = parseInt(hex.slice(offset + 6, offset + 8), 16);
    const b3 = parseInt(hex.slice(offset + 8, offset + 10), 16);
    const len = b0 | (b1 << 8) | (b2 << 16) | (b3 << 24);
    const dataLen = len * 2;
    need(10 + dataLen, 'OP_PUSHDATA4 payload');
    return {
      data: hex.slice(offset + 10, offset + 10 + dataLen),
      bytesRead: 10 + dataLen,
    };
  }

  // Not a push opcode at all — `encodePushDataState` can never emit one, so the
  // state section is malformed. Previously this silently consumed one byte and
  // returned an empty value, which desynchronised every subsequent field.
  throw new Error(
    `deserializeState: field "${label}" — byte 0x${opcode.toString(16).padStart(2, '0')} at offset ` +
      `${offset / 2} is not a push opcode; the state section is malformed`,
  );
}

