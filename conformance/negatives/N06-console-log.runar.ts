import { SmartContract, assert } from 'runar-lang';
export class N06 extends SmartContract {
  readonly a: bigint;
  constructor(a: bigint) { super(a); this.a = a; }
  public go(x: bigint) { console.log(x); assert(x > 0n); }
}
