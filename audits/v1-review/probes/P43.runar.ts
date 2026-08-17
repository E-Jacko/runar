import { SmartContract, assert } from 'runar-lang';
export class P43 extends SmartContract {
  public f(flag: bigint) {
    let a: bigint = 0n;
    if (flag > 0n) {
      const t1 = 1n; const t2 = 2n; const t3 = 3n; const t4 = 4n;
      a = t1 + t2 + t3 + t4;
    } else {
      a = 1n;
    }
    assert(a > 0n);
  }
}
