import { SmartContract, assert } from 'runar-lang';
export class N08 extends SmartContract {
  readonly a: bigint;
  constructor(a: bigint) { super(a); this.a = a; }
  public go(x: bigint, f: boolean) { assert(f + x > 0n); }
}
