import { SmartContract, assert } from 'runar-lang';
export class N07 extends SmartContract {
  readonly a: bigint;
  constructor(a: bigint) { super(a); this.a = a; }
  public go(x: bigint) { assert(neverDeclared > 0n); }
}
