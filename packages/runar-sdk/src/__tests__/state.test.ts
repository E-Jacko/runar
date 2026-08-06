// round-trip only — absolute pin: packages/runar-testing/src/__tests__/state-push-framing-vm.test.ts
//
// Every case below is deserializeState(serializeState(x)) === x, which holds
// for any self-consistent framing -- including a wrong one (exactly how the
// 2026-08 OP_N state-framing bug shipped in all seven SDKs: encode and decode
// moved together, so every round-trip stayed green). The two exceptions are
// the byte-level 'boolean' literal assertions and the decodeNum2Bin negative-
// zero block near the bottom of this file, which assert a hard-coded expected
// hex string on one side only and are absolute pins in their own right (see
// their inline comments) -- everything else here is smoke, not evidence.
import { describe, it, expect } from 'vitest';
import { serializeState, deserializeState } from '../state.js';
import type { StateField } from 'runar-ir-schema';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function makeFields(...defs: { name: string; type: string; index: number }[]): StateField[] {
  return defs.map(d => ({ name: d.name, type: d.type, index: d.index }));
}

// ---------------------------------------------------------------------------
// serializeState / deserializeState roundtrip
// ---------------------------------------------------------------------------

describe('serializeState / deserializeState roundtrip', () => {
  it('roundtrips a single bigint field', () => {
    const fields = makeFields({ name: 'count', type: 'bigint', index: 0 });
    const values = { count: 42n };
    const hex = serializeState(fields, values);
    const result = deserializeState(fields, hex);
    expect(result.count).toBe(42n);
  });

  it('roundtrips a zero bigint', () => {
    const fields = makeFields({ name: 'count', type: 'bigint', index: 0 });
    const values = { count: 0n };
    const hex = serializeState(fields, values);
    const result = deserializeState(fields, hex);
    expect(result.count).toBe(0n);
  });

  it('roundtrips a negative bigint', () => {
    const fields = makeFields({ name: 'count', type: 'bigint', index: 0 });
    const values = { count: -42n };
    const hex = serializeState(fields, values);
    const result = deserializeState(fields, hex);
    expect(result.count).toBe(-42n);
  });

  it('roundtrips a large bigint', () => {
    const fields = makeFields({ name: 'count', type: 'bigint', index: 0 });
    const values = { count: 1000000000000n };
    const hex = serializeState(fields, values);
    const result = deserializeState(fields, hex);
    expect(result.count).toBe(1000000000000n);
  });

  it('roundtrips multiple fields preserving order', () => {
    const fields = makeFields(
      { name: 'a', type: 'bigint', index: 0 },
      { name: 'b', type: 'bigint', index: 1 },
      { name: 'c', type: 'bigint', index: 2 },
    );
    const values = { a: 1n, b: 2n, c: 3n };
    const hex = serializeState(fields, values);
    const result = deserializeState(fields, hex);
    expect(result.a).toBe(1n);
    expect(result.b).toBe(2n);
    expect(result.c).toBe(3n);
  });
});

// ---------------------------------------------------------------------------
// Bigint state encoding/decoding
// ---------------------------------------------------------------------------

describe('bigint state encoding/decoding', () => {
  const bigintTestCases: Array<{ label: string; value: bigint }> = [
    { label: '0', value: 0n },
    { label: '1', value: 1n },
    { label: '-1', value: -1n },
    { label: '127', value: 127n },
    { label: '128', value: 128n },
    { label: '-128', value: -128n },
    { label: '255', value: 255n },
    { label: '256', value: 256n },
    { label: '-256', value: -256n },
    { label: 'large positive', value: 9999999999n },
    { label: 'large negative', value: -9999999999n },
  ];

  for (const tc of bigintTestCases) {
    it(`roundtrips bigint ${tc.label}`, () => {
      const fields = makeFields({ name: 'v', type: 'bigint', index: 0 });
      const hex = serializeState(fields, { v: tc.value });
      const result = deserializeState(fields, hex);
      expect(result.v).toBe(tc.value);
    });
  }
});

// ---------------------------------------------------------------------------
// Boolean state encoding/decoding
// ---------------------------------------------------------------------------

describe('boolean state encoding/decoding', () => {
  it('roundtrips true', () => {
    const fields = makeFields({ name: 'flag', type: 'bool', index: 0 });
    const hex = serializeState(fields, { flag: true });
    const result = deserializeState(fields, hex);
    expect(result.flag).toBe(true);
  });

  it('roundtrips false', () => {
    const fields = makeFields({ name: 'flag', type: 'bool', index: 0 });
    const hex = serializeState(fields, { flag: false });
    const result = deserializeState(fields, hex);
    expect(result.flag).toBe(false);
  });

  // The canonical Rúnar primitive name is `boolean` (not `bool`). Regression
  // for the encode drift the #115 review flagged: encodeStateValue only had
  // `case 'bool'`, so a `boolean` field fell through to the push-data default
  // while decode + the descriptor annotation + on-chain use 1 raw byte.
  it("roundtrips the canonical 'boolean' type", () => {
    const fields = makeFields({ name: 'flag', type: 'boolean', index: 0 });
    for (const v of [true, false]) {
      const hex = serializeState(fields, { flag: v });
      expect(deserializeState(fields, hex).flag).toBe(v);
    }
  });

  // Byte-level: a boolean state field must serialize to EXACTLY 1 raw byte
  // (0x01 / 0x00) — matching the on-chain layout (05-stack-lower.ts
  // `case 'boolean': propSizes.push(1)`), NOT a length-prefixed push. This
  // asserts against the on-chain ground truth, not just serialize↔deserialize
  // self-consistency.
  it("serializes a 'boolean' field as a single raw byte (matches on-chain)", () => {
    const fields = makeFields({ name: 'flag', type: 'boolean', index: 0 });
    expect(serializeState(fields, { flag: true })).toBe('01');
    expect(serializeState(fields, { flag: false })).toBe('00');
  });
});

// ---------------------------------------------------------------------------
// Byte string state encoding/decoding
// ---------------------------------------------------------------------------

describe('bytes state encoding/decoding', () => {
  it('roundtrips a byte string', () => {
    const fields = makeFields({ name: 'data', type: 'bytes', index: 0 });
    const hex = serializeState(fields, { data: 'aabbccdd' });
    const result = deserializeState(fields, hex);
    expect(result.data).toBe('aabbccdd');
  });

  it('roundtrips an empty byte string', () => {
    const fields = makeFields({ name: 'data', type: 'bytes', index: 0 });
    const hex = serializeState(fields, { data: '' });
    const result = deserializeState(fields, hex);
    // Empty push: decoding may return empty string
    expect(result.data).toBe('');
  });
});

// ---------------------------------------------------------------------------
// C9 — single-byte MINIMALDATA ByteString roundtrip (serializeState /
// deserializeState). `encodePushDataState` emits OP_0 / OP_1..OP_16 /
// OP_1NEGATE for single-byte payloads in that range (MINIMALDATA), but
// `decodePushData` only understood direct pushes and OP_PUSHDATA1/2/4 —
// every one of these minimal opcodes decoded as a zero-length push (''),
// corrupting the restored state value.
// ---------------------------------------------------------------------------

describe('C9 — single-byte ByteString state MINIMALDATA roundtrip', () => {
  const fields = makeFields({ name: 'b', type: 'bytes', index: 0 });
  const cases: Array<{ label: string; hex: string }> = [
    { label: '0x00 (OP_0)', hex: '00' },
    { label: '0x01 (OP_1)', hex: '01' },
    { label: '0x05 (OP_5, mid OP_1..OP_16 range)', hex: '05' },
    { label: '0x10 (OP_16)', hex: '10' },
    { label: '0x81 (OP_1NEGATE)', hex: '81' },
    { label: 'multi-byte value', hex: 'aabbccdd' },
    { label: 'empty', hex: '' },
  ];

  for (const tc of cases) {
    it(`roundtrips ${tc.label}`, () => {
      const encoded = serializeState(fields, { b: tc.hex });
      const decoded = deserializeState(fields, encoded);
      expect(decoded.b).toBe(tc.hex);
    });
  }
});

// ---------------------------------------------------------------------------
// Mixed field types
// ---------------------------------------------------------------------------

describe('mixed state fields', () => {
  it('roundtrips bigint and bool fields together', () => {
    const fields = makeFields(
      { name: 'count', type: 'bigint', index: 0 },
      { name: 'active', type: 'bool', index: 1 },
    );
    const values = { count: 100n, active: true };
    const hex = serializeState(fields, values);
    const result = deserializeState(fields, hex);
    expect(result.count).toBe(100n);
    expect(result.active).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// Fix #26: decodeNum2Bin negative zero edge case
// ---------------------------------------------------------------------------

describe('decodeNum2Bin negative zero edge cases', () => {
  it('decodes 8-byte negative zero as 0n', () => {
    // 8-byte NUM2BIN with only sign bit set → negative zero → 0n
    const fields = makeFields({ name: 'v', type: 'bigint', index: 0 });
    const hex = '0000000000000080';
    const result = deserializeState(fields, hex);
    expect(result.v).toBe(0n);
  });

  it('decodes 8-byte all-zeros as 0n', () => {
    const fields = makeFields({ name: 'v', type: 'bigint', index: 0 });
    const hex = '0000000000000000';
    const result = deserializeState(fields, hex);
    expect(result.v).toBe(0n);
  });

  it('correctly decodes -1 in NUM2BIN(8) format', () => {
    // -1: magnitude=1 in byte[0], sign bit in byte[7]
    const fields = makeFields({ name: 'v', type: 'bigint', index: 0 });
    const hex = '0100000000000080';
    const result = deserializeState(fields, hex);
    expect(result.v).toBe(-1n);
  });

  it('correctly decodes -128 in NUM2BIN(8) format', () => {
    // -128: magnitude=0x80 in byte[0], sign bit in byte[7]
    const fields = makeFields({ name: 'v', type: 'bigint', index: 0 });
    const hex = '8000000000000080';
    const result = deserializeState(fields, hex);
    expect(result.v).toBe(-128n);
  });
});
