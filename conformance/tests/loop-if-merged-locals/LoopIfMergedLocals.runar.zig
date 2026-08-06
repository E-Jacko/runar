const runar = @import("runar");

// LoopIfMergedLocals -- branch-merged locals whose merged values are DEAD in
// the enclosing scope, which is what an `if` inside a loop body always makes
// them. Companion to `merge-locals-shapes` (merged locals LIVE after the `if`)
// and `bounded-loop` (a loop with no branch in it) -- neither covers their
// intersection, which is where the merge block's premise fails.
pub const LoopIfMergedLocals = struct {
    pub const Contract = runar.StatefulSmartContract;

    a: i64 = 0,
    b: i64 = 0,
    c: i64 = 0,

    pub fn init(a: i64, b: i64, c: i64) LoopIfMergedLocals {
        return .{ .a = a, .b = b, .c = c };
    }

    pub fn guarded(self: *LoopIfMergedLocals, x: i64, limit: i64) void {
        var na: i64 = 0;
        var nb: i64 = 0;
        var i: i64 = 0;
        while (i < 2) : (i += 1) {
            if (i < limit) {
                na = na + x;
                nb = nb + na;
            }
        }
        self.addOutput(1000, na, nb, self.c);
    }

    pub fn afterIf(self: *LoopIfMergedLocals, x: i64, limit: i64) void {
        var na: i64 = 0;
        var nb: i64 = 0;
        var i: i64 = 0;
        while (i < 2) : (i += 1) {
            if (i < limit) {
                na = na + x;
            }
            nb = nb + na;
        }
        self.addOutput(1000, na, nb, self.c);
    }
};
