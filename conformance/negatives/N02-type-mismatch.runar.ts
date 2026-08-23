import { SmartContract, assert } from 'runar-lang';
export class N02 extends SmartContract {
  readonly a: bigint;
  constructor(a: bigint) { super(a); this.a = a; }
  public go(x: bigint) { let b: bigint = true; assert(b === b); }
}
