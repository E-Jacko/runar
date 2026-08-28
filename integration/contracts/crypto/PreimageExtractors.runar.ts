// TEST-ONLY — not a user example.
// Minimal preimage extract coverage: amount + outpoint + locktime (proven in
// auction/FT/covenant examples). Additional extract* can be added once verified.
import {
  StatefulSmartContract, assert,
  extractAmount, extractOutpoint, extractLocktime, extractVersion, len,
} from 'runar-lang';

class PreimageExtractors extends StatefulSmartContract {
  count: bigint;
  constructor(count: bigint) {
    super(count);
    this.count = count;
  }
  public tick() {
    assert(extractAmount(this.txPreimage) > 0n);
    assert(len(extractOutpoint(this.txPreimage)) === 36n);
    assert(extractLocktime(this.txPreimage) >= 0n);
    assert(extractVersion(this.txPreimage) >= 1n);
    this.count = this.count + 1n;
  }
}
