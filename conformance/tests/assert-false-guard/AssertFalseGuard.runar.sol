pragma runar ^0.1.0;

/// @title AssertFalseGuard
/// @notice The `require(false)`-else guard, in the two positions the
/// multi-result branch node originally missed. `bump` is a single property
/// written under a guard whose else is the dead abort -- recognised as a
/// ONE-branch chain, so excluded from declaring its result, and not rewritten
/// either because the lift only rewrites chains of two or more. `dispatch` is
/// `selector`'s exact chain one `for` deeper, where the lift never walks.
contract AssertFalseGuard is StatefulSmartContract {
    bigint count;
    bigint a;
    bigint b;

    constructor(bigint _count, bigint _a, bigint _b) {
        count = _count;
        a = _a;
        b = _b;
    }

    function bump(bigint n) public {
        if (n > 0) {
            this.count = this.count + n;
        } else {
            require(false);
        }
    }

    function dispatch(bigint sel, bigint v) public {
        for (bigint i = 0; i < 2; i++) {
            if (sel == 0) {
                this.a = v;
            } else {
                if (sel == 1) {
                    this.b = v;
                } else {
                    require(false);
                }
            }
        }
    }
}
