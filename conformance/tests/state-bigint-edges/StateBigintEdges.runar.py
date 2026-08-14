from runar import (
    StatefulSmartContract, Bigint, public,
)


class StateBigintEdges(StatefulSmartContract):
    """bigint state values at the SIGN boundary. A bigint state field is a
    fixed 8-byte little-endian sign-magnitude word (OP_NUM2BIN semantics): the
    sign lives in bit 0x80 of byte 7, so -1 is `0100000000000080` and NOT the
    two's-complement `ffffffffffffffff`. `shift` moves the two fields in
    opposite directions so one spend crosses the boundary in both senses."""

    lo: Bigint
    hi: Bigint

    def __init__(self, lo: Bigint, hi: Bigint):
        super().__init__(lo, hi)
        self.lo = lo
        self.hi = hi

    @public
    def shift(self, delta: Bigint):
        self.lo = self.lo - delta
        self.hi = self.hi + delta
        self.add_output(1000, self.lo, self.hi)
