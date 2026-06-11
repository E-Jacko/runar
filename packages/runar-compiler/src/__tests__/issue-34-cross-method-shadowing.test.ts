import { describe, it, expect } from 'vitest';
import { compile } from '../index.js';

/**
 * Regression test for issue #34 — cross-method parameter-name shadowing.
 *
 * `getParamType` used to search ALL methods' parameters for a name match, so
 * the local `x: bigint` in `walk` matched the `x: ByteString` parameter of
 * `other` and was mis-typed as bytes. The integer add `1n + x` was then
 * emitted as OP_CAT (byte concat, 0x7e) instead of OP_ADD (0x93), producing a
 * locking script that diverges from the interpreter.
 *
 * The fix scopes the param-type lookup to the current method (in all 7 tiers).
 * This test pins the corrected TS-reference behaviour; cross-tier byte parity
 * is gated by the `nested-if-multi-reassign` example in cross-compiler.test.ts.
 */
const REPRO = `
import { SmartContract, assert, substr, bin2num, num2bin, cat } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class Issue34Repro extends SmartContract {
  constructor() { super(); }

  public walk(buf: ByteString, count: bigint, target: ByteString) {
    let p: bigint = 0n;
    let found: boolean = false;
    if (0n < count) {
      const x: bigint = bin2num(cat(substr(buf, p, 1n), num2bin(0n, 1n)));
      const blob: ByteString = substr(buf, p, 1n + x);
      if (blob === target) { found = true; }
      p = p + 1n + x;
    }
    assert(found || !found);
  }

  public other(x: ByteString) { assert(x === x); }
}
`;

describe('issue #34: cross-method parameter-name shadowing', () => {
  it('compiles `1n + x` (local bigint) to OP_ADD, not OP_CAT', () => {
    const result = compile(REPRO, {
      fileName: 'Issue34Repro.runar.ts',
      disableConstantFolding: true,
    });
    expect(result.success).toBe(true);
    const hex = result.scriptHex.toLowerCase();
    // The fix must emit OP_ADD (0x93) for the integer add. Before the fix the
    // shadowing produced OP_CAT (0x7e) at the addition site.
    expect(hex).toContain('93'); // OP_ADD present
    // Byte 33 (0-indexed) is the `1n + x` addition opcode — must be OP_ADD.
    expect(hex.slice(66, 68)).toBe('93');
  });
});
