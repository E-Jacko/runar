const runar = @import("runar");

// StateBigintEdges -- bigint state values at the SIGN boundary. A bigint state
// field is a fixed 8-byte little-endian sign-magnitude word (OP_NUM2BIN
// semantics): the sign lives in bit 0x80 of byte 7, so -1 is
// `0100000000000080` and NOT the two's-complement `ffffffffffffffff`. `shift`
// moves the two fields in opposite directions so one spend crosses the
// boundary in both senses.
pub const StateBigintEdges = struct {
    pub const Contract = runar.StatefulSmartContract;

    lo: i64 = 0,
    hi: i64 = 0,

    pub fn init(lo: i64, hi: i64) StateBigintEdges {
        return .{ .lo = lo, .hi = hi };
    }

    pub fn shift(self: *StateBigintEdges, delta: i64) void {
        self.lo = self.lo - delta;
        self.hi = self.hi + delta;
        self.addOutput(1000, self.lo, self.hi);
    }
};
