import { SmartContract, assert } from 'runar-lang';
export class P20 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f(flag: bigint): bigint {
    let a: bigint = 0n; let b: bigint = 0n; let c: bigint = 0n;
    if (flag > 0n) { a = 1n; b = 2n; c = 3n; }
    return a + b + c + this.n;
  }
}
