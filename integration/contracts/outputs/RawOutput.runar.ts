// TEST-ONLY — not a user example.
// Exercises this.addRawOutput(satoshis, scriptBytes) alongside a state
// continuation. The raw output must appear in the spend tx with the
// caller-supplied script bytes; state count must increment.
import { StatefulSmartContract } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class RawOutput extends StatefulSmartContract {
  count: bigint;

  constructor(count: bigint) {
    super(count);
    this.count = count;
  }

  public sendToScript(scriptBytes: ByteString) {
    this.addRawOutput(1000n, scriptBytes);
    this.count = this.count + 1n;
    // Remaining sats go to the state continuation (and change via SDK).
    this.addOutput(2000n, this.count);
  }
}
