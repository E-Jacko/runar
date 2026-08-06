pragma runar ^0.1.0;

/// @title MergeLocalsPropUpdates
/// @notice The branch-merge shape crossed with property mutation: one method
/// that BOTH merges two locals across an `if` AND writes contract properties
/// from the merged results. No contract in the repo did both before this one.
contract MergeLocalsPropUpdates is StatefulSmartContract {
    bigint a;
    bigint b;
    bigint total;

    constructor(bigint _a, bigint _b, bigint _total) {
        a = _a;
        b = _b;
        total = _total;
    }

    function settle(bigint amount, bigint toFirst) public {
        bigint na = this.a;
        bigint nb = this.b;
        if (toFirst > 0) {
            na = na + amount;
        } else {
            nb = nb + amount;
        }
        this.a = na;
        this.b = nb;
        this.total = na + nb;
        this.addOutput(1000, this.a, this.b, this.total);
    }
}
