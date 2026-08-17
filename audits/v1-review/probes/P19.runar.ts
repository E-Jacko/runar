import { SmartContract, assert } from 'runar-lang';
export class P19 extends SmartContract {
  readonly bs: bytes;
  constructor(bs: bytes) { super(bs); this.bs = bs; }
  public f() {
    // if language allows ByteString as condition after bin2num
    const n = bin2num(this.bs);
    if (n) { assert(true); } else { assert(false); }
  }
}
// bs = 0x0100 (non-minimal 1)
