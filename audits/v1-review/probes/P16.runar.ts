import { SmartContract, assert } from 'runar-lang';
export class P16 extends SmartContract {
  readonly a: bigint; readonly b: bigint;
  constructor(a: bigint, b: bigint) { super(a, b); this.a = a; this.b = b; }
  public f() {
    assert((this.a / this.b) === -3n); // pick operands per Script rules
    assert((this.a % this.b) === -1n);
  }
}
