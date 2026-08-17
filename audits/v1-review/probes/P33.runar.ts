import { SmartContract, assert } from 'runar-lang';
export class P33 extends SmartContract {
  readonly pk: bytes;
  constructor(pk: bytes) { super(pk); this.pk = pk; }
  public f(flag: bigint) {
    let h: bigint = 0n;
    if (flag > 0n) { h = len(this.pk); } else { h = len(this.pk) + 1n; }
    assert(h === len(this.pk) || h === len(this.pk) + 1n);
  }
}
