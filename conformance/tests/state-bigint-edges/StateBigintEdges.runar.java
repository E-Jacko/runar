package runar.conformance.statebigintedges;

import runar.lang.StatefulSmartContract;
import runar.lang.annotations.Public;
import runar.lang.types.Bigint;

/**
 * StateBigintEdges -- bigint state values at the SIGN boundary. A bigint state
 * field is a fixed 8-byte little-endian sign-magnitude word (OP_NUM2BIN
 * semantics): the sign lives in bit 0x80 of byte 7, so -1 is
 * {@code 0100000000000080} and NOT the two's-complement
 * {@code ffffffffffffffff}. {@code shift} moves the two fields in opposite
 * directions so one spend crosses the boundary in both senses.
 */
class StateBigintEdges extends StatefulSmartContract {

    Bigint lo;
    Bigint hi;

    StateBigintEdges(Bigint lo, Bigint hi) {
        super(lo, hi);
        this.lo = lo;
        this.hi = hi;
    }

    @Public
    void shift(Bigint delta) {
        this.lo = this.lo.minus(delta);
        this.hi = this.hi.plus(delta);
        this.addOutput(1000L, this.lo, this.hi);
    }
}
