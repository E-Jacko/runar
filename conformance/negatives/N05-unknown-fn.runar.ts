import { SmartContract, assert } from 'runar-lang';
export class N05 extends SmartContract {
  readonly a: bigint;
  constructor(a: bigint) { super(a); this.a = a; }
  public go(x: bigint) { assert(totallyNotARunarBuiltin(x) > 0n); }
}
