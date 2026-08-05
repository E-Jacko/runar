package runar.examples.branchmergedlocals;

import runar.lang.StatefulSmartContract;
import runar.lang.annotations.Public;
import runar.lang.types.Bigint;

/**
 * BranchMergedLocals -- regression fixture for the branch-merged-local
 * miscompilation reported privately on 2026-08-03: two locals initialised from
 * state, the arms of an {@code if} reassigning DIFFERENT ones, both feeding
 * the continuation. Post-branch references used to resolve to the dead
 * pre-branch binding.
 */
class BranchMergedLocals extends StatefulSmartContract {

    Bigint a;
    Bigint b;

    BranchMergedLocals(Bigint a, Bigint b) {
        super(a, b);
        this.a = a;
        this.b = b;
    }

    @Public
    void bid(Bigint amount, Bigint toFirst) {
        Bigint na = this.a;
        Bigint nb = this.b;
        if (toFirst.gt(Bigint.ZERO)) {
            na = amount;
        } else {
            nb = amount;
        }
        this.addOutput(1000L, na, nb);
    }
}
