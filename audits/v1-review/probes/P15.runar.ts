import { SmartContract, assert, bin2num } from 'runar-lang';
export class P15 extends SmartContract {
  readonly bs: bytes;
  constructor(bs: bytes) { super(bs); this.bs = bs; }
  public f() {
    const n = bin2num(this.bs);
    assert(n === 1n);
  }
}
// constructor: non-minimal 0x0100... vs minimal 0x01
