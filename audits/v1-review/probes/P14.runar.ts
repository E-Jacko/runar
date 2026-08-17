import { SmartContract, assert, num2bin } from 'runar-lang';
export class P14 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f() {
    // size too small for n — must fail assert path or reject compile
    const b = num2bin(this.n, 1n);
    assert(len(b) === 1n);
  }
}
