import { describe, it, expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { TestContract } from 'runar-testing';

const __dirname = dirname(fileURLToPath(import.meta.url));
const source = readFileSync(join(__dirname, 'BitwiseOps.runar.ts'), 'utf8');

// The asserts inside testShift / testBitwise are tautologies (`x >= 0 || x < 0`)
// so any non-erroring run is a successful exercise of the operators.
describe('BitwiseOps', () => {
  it('compiles via TestContract.fromSource', () => {
    const c = TestContract.fromSource(source, { a: 42n, b: 17n });
    expect(c.state.a).toBe(42n);
    expect(c.state.b).toBe(17n);
  });

  it('testShift runs on positive values', () => {
    const c = TestContract.fromSource(source, { a: 42n, b: 17n });
    const r = c.call('testShift');
    expect(r.success).toBe(true);
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
    const c = TestContract.fromSource(source, { a: 42n, b: 17n });
    const r = c.call('testBitwise');
    expect(r.success).toBe(false);
  });

  it('testBitwise runs on zero', () => {
    const c = TestContract.fromSource(source, { a: 0n, b: 0n });
    const r = c.call('testBitwise');
    expect(r.success).toBe(true);
  });
});
