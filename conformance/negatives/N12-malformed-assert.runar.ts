import { SmartContract, assert } from 'runar-lang';

class N12 extends SmartContract {
  readonly owner: bigint;
  constructor(owner: bigint) { super(owner); this.owner = owner; }
  public spend(claim: bigint) { assert(claim ==); assert(true); }
}
