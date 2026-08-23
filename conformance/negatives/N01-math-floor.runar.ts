import { SmartContract, assert } from 'runar-lang';
export class N01 extends SmartContract {
  readonly a: bigint;
  constructor(a: bigint) { super(a); this.a = a; }
  public go(x: bigint) { assert(Math.floor(x) > 0n); }
}
