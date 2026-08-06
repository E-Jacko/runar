/**
 * Soft multi-null-Sig warning must fire for OR-CHECKSIG, not for OP_CHECKMULTISIG.
 */
import { describe, it, expect, vi } from 'vitest';
import { isLikelyOrCheckSigMethod } from '../contract.js';

describe('isLikelyOrCheckSigMethod', () => {
  it('returns false for OP_CHECKMULTISIG locking scripts (ASM)', () => {
    expect(
      isLikelyOrCheckSigMethod({
        asm: 'OP_0 OP_2 <pk> <pk> <pk> OP_3 OP_CHECKMULTISIG OP_VERIFY',
      }),
    ).toBe(false);
  });

  it('returns true for OP_BOOLOR + OP_CHECKSIG (OR-CHECKSIG)', () => {
    expect(
      isLikelyOrCheckSigMethod({
        asm: 'OP_DUP OP_HASH160 OP_EQUALVERIFY OP_CHECKSIG OP_SWAP OP_CHECKSIG OP_BOOLOR OP_VERIFY',
      }),
    ).toBe(true);
  });

  it('returns false when ASM empty but hex contains CHECKMULTISIG opcode ae', () => {
    // Minimal: ... ae
    expect(isLikelyOrCheckSigMethod({ script: 'ae', asm: '' })).toBe(false);
  });

  it('returns false for plain single-sig P2PKH-shaped ASM', () => {
    expect(
      isLikelyOrCheckSigMethod({
        asm: 'OP_DUP OP_HASH160 OP_EQUALVERIFY OP_CHECKSIG',
      }),
    ).toBe(false);
  });
});

describe('prepareCall soft warning integration (classification)', () => {
  it('MultiSig ASM is not classified as OR-CHECKSIG', () => {
    const multi = isLikelyOrCheckSigMethod({
      asm: 'OP_0 OP_2 OP_3 OP_CHECKMULTISIG',
      script: '00ae',
    });
    const orLike = isLikelyOrCheckSigMethod({
      asm: 'OP_CHECKSIG OP_BOOLOR OP_CHECKSIG',
    });
    expect(multi).toBe(false);
    expect(orLike).toBe(true);
  });
});
