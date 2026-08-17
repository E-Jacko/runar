import { StatefulSmartContract, assert } from 'runar-lang';
export class P23 extends StatefulSmartContract {
  cells: bigint[] = [0n, 0n, 0n]; // or FixedArray syntax as supported
  constructor(c0: bigint, c1: bigint, c2: bigint) {
    super(c0, c1, c2);
    this.cells = [c0, c1, c2];
  }
  public go(i: bigint, flag: bigint) {
    let x: bigint = this.cells[0]; // expand to scalars
    let y: bigint = this.cells[1];
    if (flag > 0n) { x = x + 1n; y = y + 1n; }
    // write back via supported index assign
  }
}
