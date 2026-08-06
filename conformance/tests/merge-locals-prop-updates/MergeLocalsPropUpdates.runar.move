// MergeLocalsPropUpdates -- the branch-merge shape crossed with property
// mutation: one method that BOTH merges two locals across an `if` AND writes
// contract properties from the merged results. No contract in the repo did
// both before this one.
module MergeLocalsPropUpdates {
    resource struct MergeLocalsPropUpdates {
        a: &mut bigint,
        b: &mut bigint,
        total: &mut bigint,
    }

    public fun settle(contract: &mut MergeLocalsPropUpdates, amount: bigint, toFirst: bigint) {
        let na = contract.a;
        let nb = contract.b;
        if (toFirst > 0) {
            na = na + amount;
        } else {
            nb = nb + amount;
        };
        contract.a = na;
        contract.b = nb;
        contract.total = na + nb;
        contract.addOutput(1000, contract.a, contract.b, contract.total);
    }
}
