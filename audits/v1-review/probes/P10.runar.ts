import { StatefulSmartContract, assert } from 'runar-lang';
export class P10 extends StatefulSmartContract {
  tag: bytes = b''; // harness: ByteString 0x05
  n: bigint = 0n;
  constructor(tag: bytes, n: bigint) { super(tag, n); this.tag = tag; this.n = n; }
  public go(flag: bigint) {
    let x: bigint = this.n; let y: bigint = 1n;
    if (flag > 0n) { x = x + 1n; y = 2n; } else { y = 3n; }
    this.n = x + y;
  }
}
