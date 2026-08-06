// AssertFalseGuard -- the `assert!(false, 0)`-else guard, in the two positions
// the multi-result branch node originally missed. `bump` is a single property
// written under a guard whose else is the dead abort -- recognised as a
// ONE-branch chain, so excluded from declaring its result, and not rewritten
// either because the lift only rewrites chains of two or more. `dispatch` is
// `selector`'s exact chain one loop deeper, where the lift never walks.
module AssertFalseGuard {
    resource struct AssertFalseGuard {
        count: &mut bigint,
        a: &mut bigint,
        b: &mut bigint,
    }

    public fun bump(contract: &mut AssertFalseGuard, n: bigint) {
        if (n > 0) {
            contract.count = contract.count + n;
        } else {
            assert!(false, 0);
        };
    }

    public fun dispatch(contract: &mut AssertFalseGuard, sel: bigint, v: bigint) {
        let i: bigint = 0;
        while (i < 2) {
            if (sel == 0) {
                contract.a = v;
            } else {
                if (sel == 1) {
                    contract.b = v;
                } else {
                    assert!(false, 0);
                }
            };
            i = i + 1;
        };
    }
}
