package runar.conformance.oversizebigintshift;

import runar.lang.StatefulSmartContract;
import runar.lang.annotations.Public;
import runar.lang.types.Bigint;

/**
 * OversizeBigintShift -- a length-sensitive byte op whose operand is a bigint
 * const too large for a JSON number (NEW-008). {@code 9007199254740993} is
 * 2^53 + 1, one past {@code Number.MAX_SAFE_INTEGER}, so the conformance
 * runner cannot narrow it back to a JSON number and the checked-in
 * {@code expected-ir.json} really does pin the {@code "<n>n"} STRING form that
 * {@code runar-cli compile} writes to disk. On chain the operand is the 7-byte
 * script number {@code 01 00 00 00 00 00 20}, {@code OP_LSHIFT} is
 * length-preserving, and {@code OP_INVERT} flips all seven bytes.
 */
class OversizeBigintShift extends StatefulSmartContract {

    Bigint out;

    OversizeBigintShift(Bigint out) {
        super(out);
        this.out = out;
    }

    /** Writes the inverted, shifted oversize constant to state. */
    @Public
    void shift() {
        this.out = Bigint.of(9007199254740993L).shl(Bigint.of(8)).not();
    }
}
