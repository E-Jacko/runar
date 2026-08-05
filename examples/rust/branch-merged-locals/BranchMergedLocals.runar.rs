use runar::prelude::*;

/// BranchMergedLocals -- regression fixture for the branch-merged-local
/// miscompilation reported privately on 2026-08-03: two locals initialised
/// from state, the arms of an `if` reassigning DIFFERENT ones, both feeding
/// the continuation. Post-branch references used to resolve to the dead
/// pre-branch binding.
#[runar::contract]
pub struct BranchMergedLocals {
    pub a: Bigint,
    pub b: Bigint,
}

impl BranchMergedLocals {
    pub fn bid(&mut self, amount: Bigint, to_first: Bigint) {
        let mut na = self.a;
        let mut nb = self.b;
        if to_first > 0 {
            na = amount;
        } else {
            nb = amount;
        }
        self.add_output(1000, na, nb);
    }
}
