import { SmartContract, assert } from 'runar-lang';

/**
 * Regression reproducer — `<<` is OP_LSHIFT over the operand's script-number
 * BYTES, not a native bigint shift.
 *
 * 255 encodes as the 2-byte script number [0xff, 0x00] (the trailing 0x00 is
 * the sign byte). OP_LSHIFT shifts that byte array left one bit and PRESERVES
 * its length, giving [0xfe, 0x00] = 254. A native bigint shift would give 510.
 *
 * Both the literal-operand assert (which also pins that the constant folder
 * refuses to fold `<<`) and the witness-driven assert (which pins the runtime
 * OP_LSHIFT path independently of any folding decision) must hold.
 */
export class ShiftTruncation extends SmartContract {
  constructor() {
    super();
  }

  public testShift(x: bigint): void {
    // Literal operands — guards the constant folder.
    assert((255n << 1n) === 254n);
    // Witness operand — guards the runtime opcode + the ANF interpreter.
    assert((x << 1n) === 254n);
  }
}
