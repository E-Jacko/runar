import { SmartContract, assert } from 'runar-lang';
export class P05 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f(flag: bigint): bigint {
    let acc: bigint = this.n;
    if (flag > 0n) {
      acc = acc + 1n;
      return acc;
    }
    acc = acc + 2n;
    return acc;
  }
}
