pragma runar ^0.1.0;

/// @title StateBigintEdges
/// @notice bigint state values at the SIGN boundary. A bigint state field is a
/// fixed 8-byte little-endian sign-magnitude word (OP_NUM2BIN semantics): the
/// sign lives in bit 0x80 of byte 7, so -1 is `0100000000000080` and NOT the
/// two's-complement `ffffffffffffffff`. `shift` moves the two fields in
/// opposite directions so one spend crosses the boundary in both senses.
contract StateBigintEdges is StatefulSmartContract {
    bigint lo;
    bigint hi;

    constructor(bigint _lo, bigint _hi) {
        lo = _lo;
        hi = _hi;
    }

    function shift(bigint delta) public {
        this.lo = this.lo - delta;
        this.hi = this.hi + delta;
        this.addOutput(1000, this.lo, this.hi);
    }
}
