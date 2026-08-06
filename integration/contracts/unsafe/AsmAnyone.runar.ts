// TEST-ONLY — not a user example.
// asm + UnsafeSmartContract — anyone-can-spend OP_1.
import { UnsafeSmartContract, asm } from 'runar-lang';

class AsmAnyone extends UnsafeSmartContract {
  constructor() {
    super();
  }
  public unlock() {
    asm({ body: '51', in_arity: 0, out_arity: 1 });
  }
}
