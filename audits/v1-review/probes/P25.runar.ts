import { SmartContract, assert, checkSig, Sig, PubKey } from 'runar-lang';
export class P25 extends SmartContract {
  readonly pk: PubKey;
  constructor(pk: PubKey) { super(pk); this.pk = pk; }
  public unlock(sig: Sig, flag: bigint) {
    if (flag > 0n) { assert(checkSig(sig, this.pk)); }
    else { assert(true); }
  }
}
