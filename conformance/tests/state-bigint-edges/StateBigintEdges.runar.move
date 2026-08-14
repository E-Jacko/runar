// StateBigintEdges -- bigint state values at the SIGN boundary. A bigint state
// field is a fixed 8-byte little-endian sign-magnitude word (OP_NUM2BIN
// semantics): the sign lives in bit 0x80 of byte 7, so -1 is
// `0100000000000080` and NOT the two's-complement `ffffffffffffffff`. `shift`
// moves the two fields in opposite directions so one spend crosses the
// boundary in both senses.
module StateBigintEdges {
    resource struct StateBigintEdges {
        lo: &mut bigint,
        hi: &mut bigint,
    }

    public fun shift(contract: &mut StateBigintEdges, delta: bigint) {
        contract.lo = contract.lo - delta;
        contract.hi = contract.hi + delta;
        contract.addOutput(1000, contract.lo, contract.hi);
    }
}
