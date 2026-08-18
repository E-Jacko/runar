import { SmartContract, assert } from 'runar-lang';

/**
 * WARNING — read before copying this shape.
 *
 * The two asserts below LOOK like tautologies (`x >= 0 || x < 0`), but this
 * contract is UNSPENDABLE for most values of `a`. Measured over
 * a = 0,1,2,4,8,16,32,64,128,256,1000: spendable for only 3 of 11.
 *
 * Why: `<<` and `>>` compile to `OP_LSHIFT` / `OP_RSHIFT`, which operate on the
 * operand's raw stack BYTES and PRESERVE its byte length — they are NOT numeric
 * shifts (spec/opcodes.md:176, docs/language-reference.md:287). So `16 << 3`
 * leaves the 1-byte `0x80` and `4 >> 2` leaves `0x00`, neither of which is a
 * MINIMALLY encoded script number. Every numeric consumer on chain — including
 * the `>=` and `<` here — decodes with fRequireMinimal=true and ABORTS on a
 * non-minimal operand. The comparison never runs; the script dies before it.
 *
 * This file exists as a CODEGEN fixture for the shift opcodes
 * (`conformance/tests/shift-ops`), not as a contract to imitate. For numeric
 * shifting use `a / pow(2n, b)` and `a * pow(2n, b)`, which compile to
 * OP_DIV / OP_MUL and stay minimally encoded.
 *
 * Until 2026-08-17 the ANF interpreter re-minimised these results and reported
 * the spend VALID, so `TestContract` was green on a contract no node would
 * accept. It now aborts exactly where the chain does.
 */
class ShiftOps extends SmartContract {
  readonly a: bigint;

  constructor(a: bigint) {
    super(a);
    this.a = a;
  }

  public testShift(): void {
    const left: bigint = this.a << 3n;
    const right: bigint = this.a >> 2n;
    assert(left >= 0n || left < 0n);
    assert(right >= 0n || right < 0n);
  }
}
