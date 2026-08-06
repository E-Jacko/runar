const runar = @import("runar");

// MergeLocalsPropUpdates -- the branch-merge shape crossed with property
// mutation: one method that BOTH merges two locals across an `if` AND writes
// contract properties from the merged results. No contract in the repo did
// both before this one.
pub const MergeLocalsPropUpdates = struct {
    pub const Contract = runar.StatefulSmartContract;

    a: i64 = 0,
    b: i64 = 0,
    total: i64 = 0,

    pub fn init(a: i64, b: i64, total: i64) MergeLocalsPropUpdates {
        return .{ .a = a, .b = b, .total = total };
    }

    pub fn settle(self: *MergeLocalsPropUpdates, amount: i64, toFirst: i64) void {
        var na = self.a;
        var nb = self.b;
        if (toFirst > 0) {
            na = na + amount;
        } else {
            nb = nb + amount;
        }
        self.a = na;
        self.b = nb;
        self.total = na + nb;
        self.addOutput(1000, self.a, self.b, self.total);
    }
};
