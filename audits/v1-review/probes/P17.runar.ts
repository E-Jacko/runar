import { SmartContract, assert, safediv, safemod } from 'runar-lang';
export class P17 extends SmartContract {
  readonly a: bigint;
  constructor(a: bigint) { super(a); this.a = a; }
  public f() {
    assert(safediv(this.a, 0n) === 0n);
    assert(safemod(this.a, 0n) === 0n);
  }
}
