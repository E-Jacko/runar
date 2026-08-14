// ---------------------------------------------------------------------------
// conformance/sdk-vertical/reference/script.ts
// ---------------------------------------------------------------------------
//
// An INDEPENDENT Bitcoin Script opcode walker, written from the push-data
// rules rather than derived from any tier's implementation.
//
// Nothing in `conformance/sdk-vertical/reference/**` may import from
// `packages/runar-sdk`, `packages/runar-compiler` or any other tier. That
// restriction is the entire point: a vertical pin whose "expected" side is
// computed by the code under test proves only that the code agrees with
// itself. See ../README.md ("Where the reference bytes come from").
//
// The walker is what turns an artifact's declared byte offsets into checkable
// claims. `constructorSlots[].byteOffset` and `codeSeparatorIndices[]` are
// bare integers: without a walk they can only be checked against the single
// byte they point at, which a neighbouring `0x00` or a `0xab` sitting inside
// push data satisfies just as well as the real thing.
// ---------------------------------------------------------------------------

export const OP_0 = 0x00;
export const OP_PUSHDATA1 = 0x4c;
export const OP_PUSHDATA2 = 0x4d;
export const OP_PUSHDATA4 = 0x4e;
export const OP_1NEGATE = 0x4f;
export const OP_1 = 0x51;
export const OP_16 = 0x60;
export const OP_CODESEPARATOR = 0xab;

/** One decoded script element at a genuine opcode boundary. */
export interface ScriptOp {
  /** Byte offset of this element's first byte (the opcode byte). */
  offset: number;
  /** The opcode byte. */
  opcode: number;
  /** Total encoded length in bytes (header + data). */
  byteLength: number;
  /** Push-header length in bytes. 0 for non-push opcodes and for the
   *  single-opcode push encodings (OP_0 / OP_1NEGATE / OP_1..OP_16). */
  headerBytes: number;
  /** True when this element pushes something onto the stack. */
  isPush: boolean;
  /** The bytes this element pushes onto the stack, as lowercase hex.
   *  '' for OP_0 (which pushes the EMPTY item, not a zero byte) and for
   *  non-push opcodes. Note OP_1..OP_16 push the single byte 0x01..0x10 and
   *  OP_1NEGATE pushes the single byte 0x81. */
  pushedHex: string;
}

function byteAt(scriptHex: string, i: number): number {
  const h = scriptHex.slice(i * 2, i * 2 + 2);
  if (h.length !== 2) {
    throw new Error(`script truncated: no byte at offset ${i} (script is ${scriptHex.length / 2} bytes)`);
  }
  return parseInt(h, 16);
}

function sliceBytes(scriptHex: string, start: number, length: number): string {
  const end = start + length;
  if (end * 2 > scriptHex.length) {
    throw new Error(
      `script truncated: push at ${start} claims ${length} bytes but only ` +
        `${scriptHex.length / 2 - start} remain`,
    );
  }
  return scriptHex.slice(start * 2, end * 2);
}

/**
 * Walk a script, returning every element in order. Throws if the script does
 * not decode cleanly (a truncated push, a length that runs off the end) —
 * which is itself a useful assertion: a splice that lands mid-push usually
 * produces an undecodable script.
 */
export function walkScript(scriptHex: string): ScriptOp[] {
  if (scriptHex.length % 2 !== 0) {
    throw new Error(`script hex has odd length ${scriptHex.length}`);
  }
  const total = scriptHex.length / 2;
  const ops: ScriptOp[] = [];
  let i = 0;

  while (i < total) {
    const opcode = byteAt(scriptHex, i);

    if (opcode === OP_0) {
      ops.push({ offset: i, opcode, byteLength: 1, headerBytes: 0, isPush: true, pushedHex: '' });
      i += 1;
    } else if (opcode >= 0x01 && opcode <= 0x4b) {
      const data = sliceBytes(scriptHex, i + 1, opcode);
      ops.push({ offset: i, opcode, byteLength: 1 + opcode, headerBytes: 1, isPush: true, pushedHex: data });
      i += 1 + opcode;
    } else if (opcode === OP_PUSHDATA1) {
      const len = byteAt(scriptHex, i + 1);
      const data = sliceBytes(scriptHex, i + 2, len);
      ops.push({ offset: i, opcode, byteLength: 2 + len, headerBytes: 2, isPush: true, pushedHex: data });
      i += 2 + len;
    } else if (opcode === OP_PUSHDATA2) {
      const len = byteAt(scriptHex, i + 1) | (byteAt(scriptHex, i + 2) << 8);
      const data = sliceBytes(scriptHex, i + 3, len);
      ops.push({ offset: i, opcode, byteLength: 3 + len, headerBytes: 3, isPush: true, pushedHex: data });
      i += 3 + len;
    } else if (opcode === OP_PUSHDATA4) {
      const len =
        byteAt(scriptHex, i + 1) |
        (byteAt(scriptHex, i + 2) << 8) |
        (byteAt(scriptHex, i + 3) << 16) |
        (byteAt(scriptHex, i + 4) * 0x1000000);
      const data = sliceBytes(scriptHex, i + 5, len);
      ops.push({ offset: i, opcode, byteLength: 5 + len, headerBytes: 5, isPush: true, pushedHex: data });
      i += 5 + len;
    } else if (opcode === OP_1NEGATE) {
      ops.push({ offset: i, opcode, byteLength: 1, headerBytes: 0, isPush: true, pushedHex: '81' });
      i += 1;
    } else if (opcode >= OP_1 && opcode <= OP_16) {
      const n = opcode - 0x50;
      ops.push({
        offset: i,
        opcode,
        byteLength: 1,
        headerBytes: 0,
        isPush: true,
        pushedHex: n.toString(16).padStart(2, '0'),
      });
      i += 1;
    } else {
      ops.push({ offset: i, opcode, byteLength: 1, headerBytes: 0, isPush: false, pushedHex: '' });
      i += 1;
    }
  }

  return ops;
}

/**
 * Byte offsets of every real `OP_CODESEPARATOR` in `scriptHex`.
 *
 * "Real" means: at an opcode boundary. A `0xab` byte inside push data — which
 * a `scriptHex.indexOf('ab')` scan happily reports, and which the 33-byte
 * PubKey constructor args in this suite's fixtures can easily contain — is
 * not an OP_CODESEPARATOR and is excluded here.
 */
export function findCodeSeparators(scriptHex: string): number[] {
  return walkScript(scriptHex)
    .filter((o) => o.opcode === OP_CODESEPARATOR)
    .map((o) => o.offset);
}

/**
 * Interpret a pushed stack item as a Bitcoin Script number (little-endian
 * sign-magnitude). Used to read a spliced bigint constructor arg back out of
 * a deployed script and compare it to the value that was meant to be baked.
 */
export function decodeScriptNumber(pushedHex: string): bigint {
  if (pushedHex.length === 0) return 0n;
  const bytes: number[] = [];
  for (let i = 0; i < pushedHex.length; i += 2) bytes.push(parseInt(pushedHex.slice(i, i + 2), 16));
  const last = bytes[bytes.length - 1]!;
  const negative = (last & 0x80) !== 0;
  bytes[bytes.length - 1] = last & 0x7f;
  let value = 0n;
  for (let i = bytes.length - 1; i >= 0; i--) value = (value << 8n) | BigInt(bytes[i]!);
  return negative ? -value : value;
}
