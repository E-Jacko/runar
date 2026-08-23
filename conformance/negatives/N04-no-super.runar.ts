import { SmartContract, assert } from 'runar-lang';
export class N04 extends SmartContract {
  readonly a: bigint;
  constructor(a: bigint) { this.a = a; }
  public go(x: bigint) { assert(x > 0n); }
}
