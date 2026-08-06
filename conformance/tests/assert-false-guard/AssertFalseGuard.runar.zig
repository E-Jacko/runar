const runar = @import("runar");

// AssertFalseGuard -- the runar.assert(false)-else guard, in the two positions
// the multi-result branch node originally missed. `bump` is a single property
// written under a guard whose else is the dead abort -- recognised as a
// ONE-branch chain, so excluded from declaring its result, and not rewritten
// either because the lift only rewrites chains of two or more. `dispatch` is
// `Selector`'s exact chain one loop deeper, where the lift never walks.
pub const AssertFalseGuard = struct {
    pub const Contract = runar.StatefulSmartContract;

    count: i64 = 0,
    a: i64 = 0,
    b: i64 = 0,

    pub fn init(count: i64, a: i64, b: i64) AssertFalseGuard {
        return .{ .count = count, .a = a, .b = b };
    }

    pub fn bump(self: *AssertFalseGuard, n: i64) void {
        if (n > 0) {
            self.count = self.count + n;
        } else {
            runar.assert(false);
        }
    }

    pub fn dispatch(self: *AssertFalseGuard, sel: i64, v: i64) void {
        var i: i64 = 0;
        while (i < 2) : (i += 1) {
            if (sel == 0) {
                self.a = v;
            } else if (sel == 1) {
                self.b = v;
            } else {
                runar.assert(false);
            }
        }
    }
};
