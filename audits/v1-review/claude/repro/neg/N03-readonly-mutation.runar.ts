import { SmartContract, assert } from 'runar-lang';
export class N03 extends SmartContract {
  readonly a: bigint;
  constructor(a: bigint) { super(a); this.a = a; }
  public go(x: bigint) { this.a = x; assert(this.a > 0n); }
}
