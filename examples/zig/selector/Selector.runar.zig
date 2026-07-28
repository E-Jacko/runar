const runar = @import("runar");

// Selector -- regression fixture for deep-review finding C20: a dispatch method
// whose branches each end in a single state update and whose terminal else is
// runar.assert(false). The abort must survive ANF lowering so an out-of-range
// selector fails the script instead of producing a spendable no-op.
pub const Selector = struct {
    pub const Contract = runar.StatefulSmartContract;

    a: i64 = 0,
    b: i64 = 0,

    pub fn init(a: i64, b: i64) Selector {
        return .{ .a = a, .b = b };
    }

    pub fn set(self: *Selector, i: i64, v: i64) void {
        if (i == 0) {
            self.a = v;
        } else if (i == 1) {
            self.b = v;
        } else {
            runar.assert(false);
        }
    }
};
