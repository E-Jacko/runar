// BranchMergedLocals -- regression fixture for the branch-merged-local
// miscompilation reported privately on 2026-08-03: two locals initialised from
// state, the arms of an `if` reassigning DIFFERENT ones, both feeding the
// continuation. Post-branch references used to resolve to the dead pre-branch
// binding.
module BranchMergedLocals {
    resource struct BranchMergedLocals {
        a: &mut bigint,
        b: &mut bigint,
    }

    public fun bid(contract: &mut BranchMergedLocals, amount: bigint, toFirst: bigint) {
        let na = contract.a;
        let nb = contract.b;
        if (toFirst > 0) {
            na = amount;
        } else {
            nb = amount;
        };
        contract.addOutput(1000, na, nb);
    }
}
