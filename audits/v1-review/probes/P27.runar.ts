import { StatefulSmartContract, assert, toByteString } from 'runar-lang';
export class P27 extends StatefulSmartContract {
  n: bigint = 0n;
  constructor(n: bigint) { super(n); this.n = n; }
  public go(flag: bigint) {
    if (flag > 0n) {
      this.addDataOutput(0n, toByteString('dead'));
      this.n = this.n + 1n;
    } else {
      this.n = this.n + 2n;
    }
  }
}
