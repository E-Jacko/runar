import { describe, it, expect } from 'vitest';
import { runTriModalExecution } from '../oracle/index.js';

// A pure-arithmetic stateless contract: verify(a, b) asserts a + b === target.
const SUM_SRC = `
import { SmartContract, assert } from 'runar-lang';

export class Sum extends SmartContract {
  readonly target: bigint;
  constructor(target: bigint) { super(target); this.target = target; }
  public verify(a: bigint, b: bigint): void {
    assert(a + b === this.target);
  }
}
`;

// A loop contract exercising the shapes #121 unblocked: a NON-ZERO start
// counting up, plus a countdown loop with post-loop parameter read.
const LOOP_SRC = `
import { SmartContract, assert } from 'runar-lang';

export class LoopSum extends SmartContract {
  readonly target: bigint;
  constructor(target: bigint) { super(target); this.target = target; }
  public verify(base: bigint): void {
    let sum: bigint = 0n;
    for (let i: bigint = 2n; i < 5n; i++) { sum = sum + base + i; }
    for (let j: bigint = 3n; j > 0n; j--) { sum = sum - j; }
    // post-loop read of the parameter 'base'
    assert(sum + base === this.target);
  }
}
`;

// A byte-op contract: cat/substr/len over a ByteString PARAMETER.
const BYTES_SRC = `
import { SmartContract, assert, cat, substr, len } from 'runar-lang';
import type { ByteString } from 'runar-lang';

export class Bytes extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public verify(bs: ByteString): void {
    const doubled: ByteString = cat(bs, bs);
    const mid: ByteString = substr(doubled, 1n, 3n);
    assert(len(doubled) === this.n && len(mid) === 3n);
  }
}
`;

describe('runTriModalExecution', () => {
  it('all three engines ACCEPT a valid arithmetic witness and agree', () => {
    const r = runTriModalExecution({
      source: SUM_SRC,
      fileName: 'Sum.runar.ts',
      method: 'verify',
      args: [3n, 7n],
      constructorArgs: { target: 10n },
    });
    expect(r.interpreterAccepted).toBe(true);
    expect(r.vmAccepted).toBe(true);
    expect(r.spendAccepted).toBe(true);
    expect(r.agrees).toBe(true);
  });

  it('all three engines REJECT a witness that violates the assert and agree', () => {
    const r = runTriModalExecution({
      source: SUM_SRC,
      fileName: 'Sum.runar.ts',
      method: 'verify',
      args: [3n, 8n],
      constructorArgs: { target: 10n },
    });
    expect(r.interpreterAccepted).toBe(false);
    expect(r.vmAccepted).toBe(false);
    expect(r.spendAccepted).toBe(false);
    expect(r.agrees).toBe(true);
  });

  it('agrees on a loop contract (non-zero start + countdown + post-loop param read)', () => {
    // i = 2,3,4 -> sum += base + i  => 3*base + 9
    // j = 3,2,1 -> sum -= j         => -6
    // final: sum + base = 3*base + 9 - 6 + base = 4*base + 3
    // base = 5 -> 4*5 + 3 = 23
    const accept = runTriModalExecution({
      source: LOOP_SRC,
      fileName: 'LoopSum.runar.ts',
      method: 'verify',
      args: [5n],
      constructorArgs: { target: 23n },
    });
    expect(accept.interpreterAccepted).toBe(true);
    expect(accept.vmAccepted).toBe(true);
    expect(accept.spendAccepted).toBe(true);
    expect(accept.agrees).toBe(true);

    const reject = runTriModalExecution({
      source: LOOP_SRC,
      fileName: 'LoopSum.runar.ts',
      method: 'verify',
      args: [5n],
      constructorArgs: { target: 22n },
    });
    expect(reject.spendAccepted).toBe(false);
    expect(reject.agrees).toBe(true);
  });

  it('agrees on byte-ops (cat/substr/len) over a ByteString parameter', () => {
    const bs = new Uint8Array([0xaa, 0xbb, 0xcc, 0xdd]); // 4 bytes -> doubled = 8
    const accept = runTriModalExecution({
      source: BYTES_SRC,
      fileName: 'Bytes.runar.ts',
      method: 'verify',
      args: [bs],
      constructorArgs: { n: 8n },
    });
    expect(accept.interpreterAccepted).toBe(true);
    expect(accept.vmAccepted).toBe(true);
    expect(accept.spendAccepted).toBe(true);
    expect(accept.agrees).toBe(true);

    const reject = runTriModalExecution({
      source: BYTES_SRC,
      fileName: 'Bytes.runar.ts',
      method: 'verify',
      args: [bs],
      constructorArgs: { n: 9n }, // wrong length assertion
    });
    expect(reject.spendAccepted).toBe(false);
    expect(reject.agrees).toBe(true);
  });
});
