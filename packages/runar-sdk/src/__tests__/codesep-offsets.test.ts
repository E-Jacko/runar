/**
 * Issue #42: terminal-method sighash subscript byte-walker.
 *
 * The on-chain script trims its sighash subscript at the method's
 * OP_CODESEPARATOR. `findCodesepOffsets` must recover the true byte position by
 * walking the script, correctly skipping push-data (which may itself contain a
 * 0xab byte) and all BSV push opcodes.
 */

import { describe, it, expect } from 'vitest';
import { findCodesepOffsets } from '../contract.js';

describe('findCodesepOffsets (issue #42)', () => {
  it('returns the real byte position, skipping 0xab inside push-data', () => {
    // 51            OP_1
    // 02 ab cd      push 2 bytes (0xab inside push-data, must be ignored)
    // ab            OP_CODESEPARATOR  <- real, byte offset 4
    // ac            OP_CHECKSIG
    expect(findCodesepOffsets('5102abcdabac')).toEqual([4]);
  });

  it('handles OP_PUSHDATA1', () => {
    // 4c (OP_PUSHDATA1) 02 (len) abab (data, contains 0xab) ab (real codesep)
    expect(findCodesepOffsets('4c02ababab')).toEqual([4]);
  });

  it('trims the subscript at the real codesep byte position', () => {
    const fullScript = '5102abcdabac'; // real codesep at byte index 4
    const offsets = findCodesepOffsets(fullScript);
    expect(offsets).toEqual([4]);
    const codeSepIdx = offsets[0]!;
    const subscript = fullScript.slice((codeSepIdx + 1) * 2);
    // Only the OP_CHECKSIG (ac) after the separator remains.
    expect(subscript).toBe('ac');
  });

  it('returns empty for a script with no OP_CODESEPARATOR', () => {
    expect(findCodesepOffsets('76a91400000000000000000000000000000000000000000088ac')).toEqual([]);
  });

  it('handles OP_PUSHDATA4, skipping 0xab inside push-data', () => {
    // 4e (OP_PUSHDATA4) 02000000 (len=2 LE) abab (data) ab (real codesep, byte 7)
    expect(findCodesepOffsets('4e02000000ababab')).toEqual([7]);
  });

  it('terminates when an OP_PUSHDATA4 length has the high bit set (issue #117)', () => {
    // 4e 00000080 — declared length 0x80000000. Signed 32-bit math makes the
    // push length negative, walking the cursor backwards forever.
    expect(findCodesepOffsets('4e00000080abab')).toEqual([]);
  });

  it('terminates when an OP_PUSHDATA4 length runs past the script end', () => {
    // 4e ffffff7f — declared length 0x7fffffff, far larger than the script.
    expect(findCodesepOffsets('4effffff7fab')).toEqual([]);
  });
});
