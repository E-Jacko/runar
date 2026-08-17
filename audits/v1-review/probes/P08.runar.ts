import { StatefulSmartContract, assert } from 'runar-lang';
export class P08 extends StatefulSmartContract {
  s: bigint = 0n;
  constructor(s: bigint) { super(s); this.s = s; }
  public go() {
    let outer: bigint = this.s;
    let acc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      for (let j: bigint = 0n; j < 2n; j++) {
        acc = acc + outer;
        outer = outer + 1n;
      }
    }
    this.s = acc + outer;
  }
}
