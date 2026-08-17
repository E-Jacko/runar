import { SmartContract, assert } from 'runar-lang';
export class P30 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f(flag: bigint) {
    let a: bigint = 0n; let b: bigint = 0n;
    if (flag > 0n) { a = 1n; b = 2n; } else { assert(false); }
    assert(a + b === 3n);
  }
}
