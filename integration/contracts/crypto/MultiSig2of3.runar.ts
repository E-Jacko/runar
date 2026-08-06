// TEST-ONLY — not a user example.
// checkMultiSig + array_literal ANF: 2-of-3 multisig. Unlocking supplies two
// DER sigs; locking is OP_0 <sigs> 2 <pks> 3 OP_CHECKMULTISIG OP_VERIFY.
// Order of sigs must match the order of the corresponding pubkeys.
import { SmartContract, assert, PubKey, Sig, checkMultiSig } from 'runar-lang';

class MultiSig2of3 extends SmartContract {
  readonly pk1: PubKey;
  readonly pk2: PubKey;
  readonly pk3: PubKey;

  constructor(pk1: PubKey, pk2: PubKey, pk3: PubKey) {
    super(pk1, pk2, pk3);
    this.pk1 = pk1;
    this.pk2 = pk2;
    this.pk3 = pk3;
  }

  public unlock(sig1: Sig, sig2: Sig): void {
    assert(checkMultiSig([sig1, sig2], [this.pk1, this.pk2, this.pk3]));
  }
}
