import { SmartContract, assert } from 'runar-lang';
export class P22 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public m1(flag: bigint) {
    let a: bigint = 1n; let b: bigint = 2n;
    if (flag > 0n) { a = 3n; b = 4n; }
    assert(a + b === 7n || a + b === 3n);
  }
  public m2(flag: bigint) {
    let a: bigint = 1n;
    if (flag > 0n) { a = 9n; }
    assert(a > 0n);
  }
}
