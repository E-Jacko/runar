import { SmartContract, assert } from 'runar-lang';
export class P28 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f(flag: boolean) {
    let ok: boolean = false;
    let x: bigint = 0n;
    if (flag) { ok = true; x = this.n; } else { ok = false; x = 0n; }
    assert(ok === (x === this.n));
  }
}
