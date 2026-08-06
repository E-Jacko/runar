// TEST-ONLY — not a user example.
// bigint & | ^ ~ << >> — assert exact results (not vacuous tautologies).
// Deploy with a=0x0f, b=0x33.
import { SmartContract, assert } from 'runar-lang';

class BitwiseOps extends SmartContract {
  readonly a: bigint;
  readonly b: bigint;
  constructor(a: bigint, b: bigint) {
    super(a, b);
    this.a = a;
    this.b = b;
  }
  public testBitwise(): void {
    // 0x0f & 0x33 = 0x03; | = 0x3f; ^ = 0x3c
    assert((this.a & this.b) === 0x03n);
    assert((this.a | this.b) === 0x3fn);
    assert((this.a ^ this.b) === 0x3cn);
    assert((~this.a) !== this.a);
  }
  public testShift(): void {
    // 0x0f << 2 = 0x3c; 0x0f >> 1 = 0x07
    assert((this.a << 2n) === 0x3cn);
    assert((this.a >> 1n) === 0x07n);
  }
}
