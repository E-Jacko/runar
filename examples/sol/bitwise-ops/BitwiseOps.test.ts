import { describe, it, expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { TestContract } from 'runar-testing';

const __dirname = dirname(fileURLToPath(import.meta.url));
const source = readFileSync(join(__dirname, 'BitwiseOps.runar.sol'), 'utf8');
const FILE_NAME = 'BitwiseOps.runar.sol';

// The asserts inside testShift / testBitwise are tautologies, so any non-erroring
// run successfully exercises the operators.
describe('BitwiseOps (Solidity)', () => {
  it('compiles via TestContract.fromSource', () => {
    const c = TestContract.fromSource(source, { a: 42n, b: 17n }, FILE_NAME);
    expect(c.state.a).toBe(42n);
  });

  it('testShift runs on positive values', () => {
    const c = TestContract.fromSource(source, { a: 42n, b: 17n }, FILE_NAME);
    expect(c.call('testShift').success).toBe(true);
  });

  it('testBitwise is UNSPENDABLE for these values (non-minimal AND result)', () => {
  // a=42, b=17 -> 42 & 17 = 0, and OP_AND PRESERVES the operands' 1-byte
  // length, so the result is the NON-MINIMAL [0x00]. The next line consumes it
  // with `>=`, a numeric op, and every numeric op on chain decodes with
  // fRequireMinimal=true and ABORTS. So this spend is impossible.
  //
  // Verified against consensus (`Spend.validate()`), not just the interpreter:
  //   a=42,b=17 -> interp=false spend=false      a=0,b=0 -> both accept
  //   a=1,b=1   -> interp=false spend=false      a=3,b=1 -> both accept
  //
  // Until 2026-08-17 the interpreter re-minimised the result and this asserted
  // `.toBe(true)` — a green test for a spend no node would accept.
    const c = TestContract.fromSource(source, { a: 42n, b: 17n }, FILE_NAME);
    expect(c.call('testBitwise').success).toBe(false);
  });
});
