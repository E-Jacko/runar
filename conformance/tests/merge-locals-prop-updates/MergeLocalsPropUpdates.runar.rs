use runar::prelude::*;

/// MergeLocalsPropUpdates -- the branch-merge shape crossed with property
/// mutation: one method that BOTH merges two locals across an `if` AND writes
/// contract properties from the merged results. No contract in the repo did
/// both before this one.
#[runar::contract]
pub struct MergeLocalsPropUpdates {
    pub a: Bigint,
    pub b: Bigint,
    pub total: Bigint,
}

impl MergeLocalsPropUpdates {
    pub fn settle(&mut self, amount: Bigint, to_first: Bigint) {
        let mut na = self.a;
        let mut nb = self.b;
        if to_first > 0 {
            na = na + amount;
        } else {
            nb = nb + amount;
        }
        self.a = na;
        self.b = nb;
        self.total = na + nb;
        self.add_output(1000, self.a, self.b, self.total);
    }
}
