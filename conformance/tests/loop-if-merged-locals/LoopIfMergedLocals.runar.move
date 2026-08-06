// LoopIfMergedLocals -- branch-merged locals whose merged values are DEAD in
// the enclosing scope, which is what an `if` inside a loop body always makes
// them. Companion to `merge-locals-shapes` (merged locals LIVE after the `if`)
// and `bounded-loop` (a loop with no branch in it) -- neither covers their
// intersection, which is where the merge block's premise fails.
module LoopIfMergedLocals {
    resource struct LoopIfMergedLocals {
        a: &mut bigint,
        b: &mut bigint,
        c: &mut bigint,
    }

    public fun guarded(contract: &mut LoopIfMergedLocals, x: bigint, limit: bigint) {
        let na: bigint = 0;
        let nb: bigint = 0;
        let i: bigint = 0;
        while (i < 2) {
            if (i < limit) {
                na = na + x;
                nb = nb + na;
            };
            i = i + 1;
        };
        contract.addOutput(1000, na, nb, contract.c);
    }

    public fun afterIf(contract: &mut LoopIfMergedLocals, x: bigint, limit: bigint) {
        let na: bigint = 0;
        let nb: bigint = 0;
        let i: bigint = 0;
        while (i < 2) {
            if (i < limit) {
                na = na + x;
            };
            nb = nb + na;
            i = i + 1;
        };
        contract.addOutput(1000, na, nb, contract.c);
    }
}
