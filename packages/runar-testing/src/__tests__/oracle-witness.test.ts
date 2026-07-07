import { describe, it, expect } from 'vitest';
import { buildWitness } from '../oracle/witness.js';
import { bytesToHex } from '../vm/index.js';

describe('buildWitness', () => {
  it('encodes a small positive bigint via its minimal-push opcode (OP_3)', () => {
    // 3 → OP_3 (0x53), the consensus minimal-push form (not a 1-byte data push)
    expect(bytesToHex(buildWitness([3n]))).toBe('53');
  });

  it('encodes small-int edge cases via OP_1NEGATE / OP_0 / OP_16', () => {
    expect(bytesToHex(buildWitness([-1n]))).toBe('4f'); // OP_1NEGATE
    expect(bytesToHex(buildWitness([0n]))).toBe('00'); // OP_0
    expect(bytesToHex(buildWitness([16n]))).toBe('60'); // OP_16
  });

  it('encodes a bigint above the OP_N range as a minimal data push', () => {
    // 100 (0x64) has no dedicated opcode → 1-byte data push
    expect(bytesToHex(buildWitness([100n]))).toBe('0164');
  });

  it('encodes booleans as OP_TRUE / OP_FALSE (0x51 / 0x00)', () => {
    expect(bytesToHex(buildWitness([true]))).toBe('51');
    expect(bytesToHex(buildWitness([false]))).toBe('00');
  });

  it('encodes raw bytes as a length-prefixed push', () => {
    expect(bytesToHex(buildWitness([new Uint8Array([0xde, 0xad])]))).toBe('02dead');
  });

  it('concatenates multiple args in order', () => {
    expect(bytesToHex(buildWitness([3n, 7n]))).toBe('5357');
  });
});
