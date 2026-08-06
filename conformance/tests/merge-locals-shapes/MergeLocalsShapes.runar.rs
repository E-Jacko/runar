use runar::prelude::*;

/// MergeLocalsShapes -- the three branch-merge arities that had no real-crypto
/// evidence: k=2 symmetric (both arms rebind both locals), k=3, and a nested
/// `if` whose merge lands at the outer level. Companion to
/// `branch-merged-locals`, which pins the asymmetric k=2 case.
#[runar::contract]
pub struct MergeLocalsShapes {
    pub a: Bigint,
    pub b: Bigint,
    pub c: Bigint,
}

impl MergeLocalsShapes {
    pub fn both_arms(&mut self, x: Bigint, flag: Bigint) {
        let mut na = self.a;
        let mut nb = self.b;
        if flag > 0 {
            na = x + 1;
            nb = x + 2;
        } else {
            na = x + 3;
            nb = x + 4;
        }
        self.add_output(1000, na, nb, self.c);
    }

    pub fn three(&mut self, x: Bigint, flag: Bigint) {
        let mut na = self.a;
        let mut nb = self.b;
        let mut nc = self.c;
        if flag > 0 {
            na = x + 1;
            nb = x + 2;
            nc = x + 3;
        } else {
            na = x + 4;
            nb = x + 5;
            nc = x + 6;
        }
        self.add_output(1000, na, nb, nc);
    }

    pub fn nested(&mut self, x: Bigint, outer: Bigint, inner: Bigint) {
        let mut na = self.a;
        let mut nb = self.b;
        if outer > 0 {
            if inner > 0 {
                na = x + 1;
            } else {
                nb = x + 2;
            }
        }
        self.add_output(1000, na, nb, self.c);
    }
}
