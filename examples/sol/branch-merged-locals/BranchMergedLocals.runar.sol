pragma runar ^0.1.0;

/// @title BranchMergedLocals
/// @notice Regression fixture for the branch-merged-local miscompilation
/// reported privately on 2026-08-03: two locals initialised from state, the
/// arms of an `if` reassigning DIFFERENT ones, both feeding the continuation.
/// Post-branch references used to resolve to the dead pre-branch binding.
contract BranchMergedLocals is StatefulSmartContract {
    bigint a;
    bigint b;

    constructor(bigint _a, bigint _b) {
        a = _a;
        b = _b;
    }

    function bid(bigint amount, bigint toFirst) public {
        bigint na = this.a;
        bigint nb = this.b;
        if (toFirst > 0) {
            na = amount;
        } else {
            nb = amount;
        }
        this.addOutput(1000, na, nb);
    }
}
