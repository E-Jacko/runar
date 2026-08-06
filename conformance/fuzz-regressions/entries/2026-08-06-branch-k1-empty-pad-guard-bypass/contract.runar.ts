import { SmartContract, assert, abs } from 'runar-lang';

class FuzzContract20 extends SmartContract {
  readonly prop13: bigint;
  readonly prop34: boolean;
  readonly prop94: boolean;

  constructor(prop13: bigint, prop34: boolean, prop94: boolean) {
    super(prop13, prop34, prop94);
    this.prop13 = prop13;
    this.prop34 = prop34;
    this.prop94 = prop94;
  }

  public method1(param85: boolean): void {
    const local79: bigint = ((-63n * this.prop13) * (49580n ^ -50035n));
    const local65: bigint = (abs(62n) % -17n);
    let merge0: bigint = abs(this.prop13);
    if ((param85 || param85)) {
      merge0 = abs(merge0);
    } else {
      merge0 = 43n;
    }
    assert((merge0 < (-89n * -36n)));
    let sum0: bigint = (-7n % -11n);
    for (let k0: bigint = 1n; k0 < 4n; k0++) {
      sum0 = (sum0 + this.prop13);
    }
    assert((sum0 > abs(21n)));
    assert(((53n % 7n) !== (this.prop13 - -32n)));
    assert((!(false) || (true || param85)));
  }

  public method4(param26: bigint, param13: bigint, param31: boolean): void {
    assert(((false && this.prop34) || (64n > param26)));
  }

  public method2(param59: boolean, param39: boolean, param78: bigint): void {
    const local22: bigint = ((89n - this.prop13) >> 1n);
    const local20: bigint = abs((this.prop13 % -16n));
    let merge0: bigint = abs(this.prop13);
    if ((-72n !== 13n)) {
      merge0 = merge0;
    } else {
      merge0 = ((33200n << 15n) ^ this.prop13);
    }
    assert((merge0 !== abs(79n)));
    let sum0: bigint = (this.prop13 + this.prop13);
    let sum1: bigint = ((-3n << 1n) ^ 27778n);
    for (let k0: bigint = 2n; k0 < 4n; k0++) {
      for (let k1: bigint = 0n; k1 < 2n; k1++) {
        sum0 = (sum0 + param78);
        sum1 = (sum1 + sum0);
      }
    }
    assert(((sum0 === (37n * -89n)) && (sum1 <= 74n)));
    assert(((45n << 8n) < abs(19n)));
    assert(((param59 || param59) || (false || this.prop94)));
  }
}
