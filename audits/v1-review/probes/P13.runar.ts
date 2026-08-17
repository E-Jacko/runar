import { SmartContract, assert, slice, len } from 'runar-lang';
export class P13 extends SmartContract {
  readonly bs: bytes;
  constructor(bs: bytes) { super(bs); this.bs = bs; }
  public f(at: bigint) {
    // Adjust names to actual Rúnar byte APIs available in lang
    const left = slice(this.bs, 0n, at);
    const right = slice(this.bs, at, len(this.bs));
    assert(len(left) + len(right) === len(this.bs));
  }
}
// at=0, at=len, at=middle
