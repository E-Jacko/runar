use runar::prelude::*;

/// AssertFalseGuard -- the `assert!(false)`-else guard, in the two positions
/// the multi-result branch node originally missed. `bump` is a single property
/// written under a guard whose else is the dead abort -- recognised as a
/// ONE-branch chain, so excluded from declaring its result, and not rewritten
/// either because the lift only rewrites chains of two or more. `dispatch` is
/// `Selector`'s exact chain one loop deeper, where the lift never walks.
#[runar::contract]
pub struct AssertFalseGuard {
    pub count: Bigint,
    pub a: Bigint,
    pub b: Bigint,
}

impl AssertFalseGuard {
    pub fn bump(&mut self, n: Bigint) {
        if n > 0 {
            self.count = self.count + n;
        } else {
            assert!(false);
        }
    }

    pub fn dispatch(&mut self, sel: Bigint, v: Bigint) {
        for i in 0..2 {
            if sel == 0 {
                self.a = v;
            } else {
                if sel == 1 {
                    self.b = v;
                } else {
                    assert!(false);
                }
            }
        }
    }
}
