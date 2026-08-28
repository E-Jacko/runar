// TEST-ONLY — not a user example.
// Bare + - * / % against constructor targets.
import { SmartContract, assert } from 'runar-lang';

class ArithmeticOps extends SmartContract {
  readonly target: bigint;
  constructor(target: bigint) {
    super(target);
    this.target = target;
  }
  public verify(a: bigint, b: bigint): void {
    const sum = a + b;
    const diff = a - b;
    const prod = a * b;
    const quot = a / b;
    const rem = a % b;
    assert(sum + diff + prod + quot + rem === this.target);
  }
}
