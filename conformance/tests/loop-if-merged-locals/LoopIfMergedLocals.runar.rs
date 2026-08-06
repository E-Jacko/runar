use runar::prelude::*;

/// LoopIfMergedLocals -- branch-merged locals whose merged values are DEAD in
/// the enclosing scope, which is what an `if` inside a loop body always makes
/// them. Companion to `merge-locals-shapes` (merged locals LIVE after the
/// `if`) and `bounded-loop` (a loop with no branch in it) -- neither covers
/// their intersection, which is where the merge block's premise fails.
#[runar::contract]
pub struct LoopIfMergedLocals {
    pub a: Bigint,
    pub b: Bigint,
    pub c: Bigint,
}

impl LoopIfMergedLocals {
    pub fn guarded(&mut self, x: Bigint, limit: Bigint) {
        let mut na: Bigint = 0;
        let mut nb: Bigint = 0;
        for i in 0..2 {
            if i < limit {
                na = na + x;
                nb = nb + na;
            }
        }
        self.add_output(1000, na, nb, self.c);
    }

    pub fn after_if(&mut self, x: Bigint, limit: Bigint) {
        let mut na: Bigint = 0;
        let mut nb: Bigint = 0;
        for i in 0..2 {
            if i < limit {
                na = na + x;
            }
            nb = nb + na;
        }
        self.add_output(1000, na, nb, self.c);
    }
}
