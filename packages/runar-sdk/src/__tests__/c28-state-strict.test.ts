/**
 * C28 — `deserializeState` silently tolerated truncated and overlong state.
 *
 * State is read back out of a deployed locking script's OP_RETURN tail. That
 * tail is attacker-influenceable: anybody can build a transaction whose
 * continuation output carries a state blob that is shorter or longer than the
 * artifact's `stateFields` describe.
 *
 * Before this fix `deserializeState` read fixed-width fields with a bare
 * `hex.slice(offset, offset + width)` — a short slice produced a
 * plausible-but-wrong value instead of an error (a truncated `bool` read the
 * empty string and decoded as `true`, a truncated `bigint` decoded as a
 * different number, a truncated `PubKey` yielded a short key) — and the field
 * loop simply stopped at the last declared field, so any trailing bytes were
 * dropped on the floor. Both cases restore a contract object that looks valid
 * and is not.
 *
 * The codec is now exact: every field must be fully present, and the blob must
 * be consumed to its last byte.
 */

import { describe, it, expect } from 'vitest';
import { serializeState, deserializeState, extractStateFromScript } from '../state.js';
import type { StateField, RunarArtifact } from 'runar-ir-schema';

function makeFields(...defs: { name: string; type: string; index: number }[]): StateField[] {
  return defs.map((d) => ({ name: d.name, type: d.type, index: d.index }));
}

// ---------------------------------------------------------------------------
// Truncation
// ---------------------------------------------------------------------------

describe('C28: deserializeState rejects truncated state', () => {
  it('throws on a bigint field one byte short', () => {
    const fields = makeFields({ name: 'count', type: 'bigint', index: 0 });
    const full = serializeState(fields, { count: 42n });
    expect(full).toHaveLength(16); // 8 bytes
    expect(() => deserializeState(fields, full.slice(0, 14))).toThrow(/truncat/i);
  });

  it('throws on a completely absent field rather than inventing a value', () => {
    const fields = makeFields(
      { name: 'a', type: 'bigint', index: 0 },
      { name: 'b', type: 'bigint', index: 1 },
    );
    const full = serializeState(fields, { a: 1n, b: 2n });
    expect(() => deserializeState(fields, full.slice(0, 16))).toThrow(/truncat/i);
  });

  it('throws on a missing bool byte instead of decoding it as true', () => {
    const fields = makeFields(
      { name: 'n', type: 'bigint', index: 0 },
      { name: 'active', type: 'boolean', index: 1 },
    );
    const full = serializeState(fields, { n: 7n, active: false });
    // Drop the trailing bool byte. Previously `'' !== '00'` → `active: true`.
    expect(() => deserializeState(fields, full.slice(0, 16))).toThrow(/truncat/i);
  });

  it('throws on a short PubKey rather than returning a stub key', () => {
    const fields = makeFields({ name: 'owner', type: 'PubKey', index: 0 });
    const full = serializeState(fields, { owner: 'ab'.repeat(33) });
    expect(() => deserializeState(fields, full.slice(0, 40))).toThrow(/truncat/i);
  });

  it('throws when a push-data field declares more bytes than remain', () => {
    const fields = makeFields({ name: 'blob', type: 'ByteString', index: 0 });
    // Direct push of 5 bytes, only 2 supplied.
    expect(() => deserializeState(fields, '05aabb')).toThrow(/truncat/i);
  });

  it('throws when a push-data field has no opcode byte at all', () => {
    const fields = makeFields(
      { name: 'n', type: 'bigint', index: 0 },
      { name: 'blob', type: 'ByteString', index: 1 },
    );
    expect(() => deserializeState(fields, serializeState(fields, { n: 1n, blob: 'aa' }).slice(0, 16))).toThrow(
      /truncat/i,
    );
  });

  it('throws when an OP_PUSHDATA1 length header is itself truncated', () => {
    const fields = makeFields({ name: 'blob', type: 'ByteString', index: 0 });
    expect(() => deserializeState(fields, '4c')).toThrow(/truncat/i);
  });

  it('throws on a truncated fixed-array element', () => {
    const fields: StateField[] = [
      {
        name: 'board',
        type: 'FixedArray<bigint, 3>',
        index: 0,
        fixedArray: { syntheticNames: ['board__0', 'board__1', 'board__2'], elementType: 'bigint' },
      } as unknown as StateField,
    ];
    const full = serializeState(fields, { board: [1n, 2n, 3n] });
    expect(full).toHaveLength(48);
    expect(() => deserializeState(fields, full.slice(0, 40))).toThrow(/truncat/i);
  });

  it('throws on an odd-length hex blob', () => {
    const fields = makeFields({ name: 'count', type: 'bigint', index: 0 });
    expect(() => deserializeState(fields, '00112233445566778')).toThrow();
  });
});

// ---------------------------------------------------------------------------
// Overlong tails
// ---------------------------------------------------------------------------

describe('C28: deserializeState rejects overlong state', () => {
  it('throws on a single unexpected trailing byte', () => {
    const fields = makeFields({ name: 'count', type: 'bigint', index: 0 });
    const full = serializeState(fields, { count: 42n });
    expect(() => deserializeState(fields, full + 'ff')).toThrow(/trailing/i);
  });

  it('throws on trailing bytes after a variable-length field', () => {
    const fields = makeFields({ name: 'blob', type: 'ByteString', index: 0 });
    const full = serializeState(fields, { blob: 'aabbcc' });
    expect(() => deserializeState(fields, full + '00')).toThrow(/trailing/i);
  });

  it('throws when a whole extra field is appended', () => {
    const fields = makeFields({ name: 'a', type: 'bigint', index: 0 });
    const two = makeFields(
      { name: 'a', type: 'bigint', index: 0 },
      { name: 'b', type: 'bigint', index: 1 },
    );
    const full = serializeState(two, { a: 1n, b: 2n });
    expect(() => deserializeState(fields, full)).toThrow(/trailing/i);
  });

  it('extractStateFromScript surfaces a corrupted continuation instead of restoring wrong state', () => {
    const artifact = {
      stateFields: [{ name: 'count', type: 'bigint', index: 0 }],
    } as unknown as RunarArtifact;
    const stateHex = serializeState(artifact.stateFields!, { count: 5n });
    const script = '51' + '6a' + stateHex + 'ff';
    expect(() => extractStateFromScript(artifact, script)).toThrow(/trailing/i);
  });
});

// ---------------------------------------------------------------------------
// Legitimate blobs still round-trip
// ---------------------------------------------------------------------------

describe('C28: well-formed state still round-trips', () => {
  it('round-trips a mixed-type record exactly', () => {
    const fields = makeFields(
      { name: 'count', type: 'bigint', index: 0 },
      { name: 'active', type: 'boolean', index: 1 },
      { name: 'owner', type: 'PubKey', index: 2 },
      { name: 'blob', type: 'ByteString', index: 3 },
    );
    const values = { count: -9n, active: true, owner: 'cd'.repeat(33), blob: 'deadbeef' };
    const hex = serializeState(fields, values);
    expect(deserializeState(fields, hex)).toEqual(values);
  });

  it('round-trips a 1-byte ByteString in the OP_1..OP_16 value range', () => {
    const fields = makeFields({ name: 'blob', type: 'ByteString', index: 0 });
    const hex = serializeState(fields, { blob: '05' });
    // <len><data>, matching the compiler's on-chain state codec. NOT the
    // MINIMALDATA opcode form (OP_5 = '55'): the state section lives after
    // OP_RETURN and is never executed, and a '55' here is unreadable to the
    // contract's own script.
    expect(hex).toBe('0105');
    expect(deserializeState(fields, hex)).toEqual({ blob: '05' });
  });

  it('rejects an OP_N-framed state field — the on-chain reader cannot parse it', () => {
    const fields = makeFields({ name: 'blob', type: 'ByteString', index: 0 });
    // '55' is what pre-fix SDKs wrote for a 1-byte 0x05. On-chain it reads as
    // a length-85 push, so it must fail closed here too rather than decode to
    // a plausible-looking '05' the contract can never actually spend.
    expect(() => deserializeState(fields, '55')).toThrow(/is not a push opcode/);
  });

  it('round-trips an empty ByteString', () => {
    const fields = makeFields({ name: 'blob', type: 'ByteString', index: 0 });
    const hex = serializeState(fields, { blob: '' });
    expect(deserializeState(fields, hex)).toEqual({ blob: '' });
  });

  it('accepts an empty blob for an empty field list', () => {
    expect(deserializeState([], '')).toEqual({});
  });
});
