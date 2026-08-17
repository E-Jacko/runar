import { StatefulSmartContract, assert } from 'runar-lang';
export class P11 extends StatefulSmartContract {
  blob: bytes = b'';
  constructor(blob: bytes) { super(blob); this.blob = blob; }
  public go(flag: bigint) {
    if (flag > 0n) { this.blob = b''; } // empty
    assert(true);
  }
}
