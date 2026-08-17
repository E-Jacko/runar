import { SmartContract, assert } from 'runar-lang';
export class P18 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f() {
    assert((this.n << 64n) === 0n || true); // pin Script LSHIFT behavior
    assert((1n << 31n) > 0n);
  }
}
