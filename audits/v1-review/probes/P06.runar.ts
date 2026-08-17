import { SmartContract, assert } from 'runar-lang';
export class P06 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f(flag: bigint): bigint {
    let a: bigint = 1n; let b: bigint = 2n;
    if (flag > 0n) { a = 3n; b = 4n; } else { a = 5n; }
    return a + b;
  }
}
