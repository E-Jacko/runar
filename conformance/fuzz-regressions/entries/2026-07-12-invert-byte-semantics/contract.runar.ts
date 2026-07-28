import { SmartContract, assert } from 'runar-lang';

/**
 * Regression reproducer — `~` is OP_INVERT over the operand's script-number
 * BYTES, not the numeric two's-complement `~n === -(n + 1)`.
 *
 * 5 encodes as the 1-byte script number [0x05]. OP_INVERT flips every bit,
 * giving [0xfa]. Decoded as a little-endian sign-magnitude script number the
 * high bit is the sign, so 0xfa is -(0x7a) = -122. A native bigint `~5` would
 * give -6.
 */
export class InvertBytes extends SmartContract {
  constructor() {
    super();
  }

  public testInvert(x: bigint): void {
    // Literal operand — guards the constant folder.
    assert((~5n) === -122n);
    // Witness operand — guards the runtime opcode + the ANF interpreter.
    assert((~x) === -122n);
  }
}
