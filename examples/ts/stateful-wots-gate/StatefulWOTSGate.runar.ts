import { StatefulSmartContract, assert, verifyWOTS } from 'runar-lang';
import type { ByteString } from 'runar-lang';

// StatefulWOTSGate - stateful + post-quantum interaction fixture (GAP-407).
// A counter whose state mutation is gated on a WOTS+ one-time signature,
// composing the auto-injected stateful covenant (checkPreimage + 0x41 sighash
// pin + state continuation) with a ~10 KB post-quantum verify in one script.
class StatefulWOTSGate extends StatefulSmartContract {
  count: bigint;

  constructor(count: bigint) {
    super(count);
    this.count = count;
  }

  public advance(msg: ByteString, sig: ByteString, wotsPubKey: ByteString) {
    assert(verifyWOTS(msg, sig, wotsPubKey));
    this.count = this.count + 1n;
  }
}
