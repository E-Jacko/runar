/**
 * A bigint state value whose MAGNITUDE does not fit the fixed 8-byte
 * little-endian sign-magnitude word must be REFUSED, not silently truncated.
 *
 * ===========================================================================
 * `num2bin-le8` gives a bigint state field exactly 63 bits of magnitude
 * (bytes 0..6 plus the low 7 bits of byte 7) and one sign bit (0x80 of byte
 * 7). `serializeState` wrote the low 8 bytes and dropped everything above,
 * then OR-ed the sign bit in on top of whatever landed there. Measured before
 * the guard:
 *
 *     value                     bytes written       reads back as
 *     2^63                      0000000000000080    0    (negative zero)
 *     -(2^63)                    0000000000000080    0
 *     2^63 + 5                  0500000000000080    -5   (SIGN FLIP)
 *     2^64                      0000000000000000    0
 *     2^70                      0000000000000000    0
 *
 * The deploy succeeded, the state section looked well-formed, and the UTXO was
 * unspendable: the covenant rebuilds the continuation with the COMPILER's
 * OP_NUM2BIN 8, which cannot produce those bytes from that number, so
 * hash256(outputs) never matches. `2^63 + 5` reading back as `-5` is the worst
 * of them — a positive balance that deserialises as a debt.
 * ===========================================================================
 *
 * The accepting controls are `±(2^63 - 1)`, the largest representable
 * magnitude, pinned to their exact bytes: the guard must reject what does not
 * fit and NOTHING else, or every contract at the edge of the range breaks.
 * Those two values are also the ones `conformance/tests/state-bigint-edges`
 * carries end to end.
 *
 * Expected bytes below are derived BY HAND from the encoding, never read off
 * the serializer.
 */

import { describe, it, expect } from 'vitest';
import { serializeState, deserializeState } from '../state.js';
import type { StateField } from 'runar-ir-schema';

const COUNT: StateField[] = [{ name: 'count', type: 'bigint', index: 0 }];

/** 2^63 — one past the largest magnitude the 63 magnitude bits can hold. */
const TWO_63 = 9_223_372_036_854_775_808n;
/** 2^63 - 1 — the largest magnitude that DOES fit. */
const MAX_MAGNITUDE = TWO_63 - 1n;

describe('serializeState: bigint magnitude bound', () => {
  it('rejects exactly 2^63 (positive)', () => {
    expect(() => serializeState(COUNT, { count: TWO_63 })).toThrow(
      /does not fit/i,
    );
  });

  it('rejects exactly -(2^63)', () => {
    expect(() => serializeState(COUNT, { count: -TWO_63 })).toThrow(
      /does not fit/i,
    );
  });

  it('rejects 2^63 + 5 — the value that read back as -5', () => {
    expect(() => serializeState(COUNT, { count: TWO_63 + 5n })).toThrow(
      /does not fit/i,
    );
  });

  it('rejects a magnitude well above the word (2^70)', () => {
    const big = 1n << 70n;
    expect(() => serializeState(COUNT, { count: big })).toThrow(/does not fit/i);
    expect(() => serializeState(COUNT, { count: -big })).toThrow(/does not fit/i);
  });

  it('names the field and the value it refused', () => {
    expect(() => serializeState(COUNT, { count: TWO_63 })).toThrow(/count/);
    expect(() => serializeState(COUNT, { count: TWO_63 })).toThrow(
      new RegExp(String(TWO_63)),
    );
  });

  it('rejects an out-of-range element of a fixed array', () => {
    const fields: StateField[] = [
      {
        name: 'Slots',
        type: 'FixedArray<bigint, 2>',
        index: 0,
        fixedArray: { syntheticNames: ['Slots__0', 'Slots__1'], length: 2 },
      } as StateField,
    ];
    expect(() => serializeState(fields, { Slots: [1n, TWO_63] })).toThrow(
      /does not fit/i,
    );
  });

  // -------------------------------------------------------------------------
  // Accepting controls — byte-exact, and they must stay byte-exact
  // -------------------------------------------------------------------------

  it('accepts 2^63 - 1 and writes ffffffffffffff7f', () => {
    // magnitude bytes 0..6 all 0xff, byte 7 = 0x7f (all seven magnitude bits
    // set, sign bit clear).
    expect(serializeState(COUNT, { count: MAX_MAGNITUDE })).toBe(
      'ffffffffffffff7f',
    );
    expect(deserializeState(COUNT, 'ffffffffffffff7f').count).toBe(
      MAX_MAGNITUDE,
    );
  });

  it('accepts -(2^63 - 1) and writes ffffffffffffffff', () => {
    // same magnitude, sign bit set: 0x7f | 0x80 = 0xff.
    expect(serializeState(COUNT, { count: -MAX_MAGNITUDE })).toBe(
      'ffffffffffffffff',
    );
    expect(deserializeState(COUNT, 'ffffffffffffffff').count).toBe(
      -MAX_MAGNITUDE,
    );
  });

  it('accepts the small values every shipped contract uses', () => {
    expect(serializeState(COUNT, { count: 0n })).toBe('0000000000000000');
    expect(serializeState(COUNT, { count: 1n })).toBe('0100000000000000');
    expect(serializeState(COUNT, { count: -1n })).toBe('0100000000000080');
  });
});
