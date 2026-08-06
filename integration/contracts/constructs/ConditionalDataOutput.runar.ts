// TEST-ONLY — not a user example.
// Audit regression: addDataOutput on a conditional branch must keep the
// single-output computeStateOutput continuation path (not multi-output
// continuation). Uses 1-sat data outputs for SV Node dust policy
// (acceptnonstdtxn=0); mainnet/ARC still accept 0-sat OP_RETURN.
import { StatefulSmartContract, ByteString, assert } from 'runar-lang';

class ConditionalDataOutput extends StatefulSmartContract {
  amount: bigint;

  constructor(amount: bigint) {
    super(amount);
    this.amount = amount;
  }

  public pay(flag: boolean, payload: ByteString): void {
    this.amount = this.amount + 1n;
    if (flag) {
      // 1 satoshi: CI regtest dust policy rejects 0-sat OP_RETURN.
      this.addDataOutput(1n, payload);
    }
    assert(true);
  }
}
