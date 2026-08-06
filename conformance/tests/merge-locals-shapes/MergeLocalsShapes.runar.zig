const runar = @import("runar");

// MergeLocalsShapes -- the three branch-merge arities that had no real-crypto
// evidence: k=2 symmetric (both arms rebind both locals), k=3, and a nested
// `if` whose merge lands at the outer level. Companion to
// `branch-merged-locals`, which pins the asymmetric k=2 case.
pub const MergeLocalsShapes = struct {
    pub const Contract = runar.StatefulSmartContract;

    a: i64 = 0,
    b: i64 = 0,
    c: i64 = 0,

    pub fn init(a: i64, b: i64, c: i64) MergeLocalsShapes {
        return .{ .a = a, .b = b, .c = c };
    }

    pub fn bothArms(self: *MergeLocalsShapes, x: i64, flag: i64) void {
        var na = self.a;
        var nb = self.b;
        if (flag > 0) {
            na = x + 1;
            nb = x + 2;
        } else {
            na = x + 3;
            nb = x + 4;
        }
        self.addOutput(1000, na, nb, self.c);
    }

    pub fn three(self: *MergeLocalsShapes, x: i64, flag: i64) void {
        var na = self.a;
        var nb = self.b;
        var nc = self.c;
        if (flag > 0) {
            na = x + 1;
            nb = x + 2;
            nc = x + 3;
        } else {
            na = x + 4;
            nb = x + 5;
            nc = x + 6;
        }
        self.addOutput(1000, na, nb, nc);
    }

    pub fn nested(self: *MergeLocalsShapes, x: i64, outer: i64, inner: i64) void {
        var na = self.a;
        var nb = self.b;
        if (outer > 0) {
            if (inner > 0) {
                na = x + 1;
            } else {
                nb = x + 2;
            }
        }
        self.addOutput(1000, na, nb, self.c);
    }
};
