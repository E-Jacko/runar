package runar.conformance.mergelocalspropupdates;

import runar.lang.StatefulSmartContract;
import runar.lang.annotations.Public;
import runar.lang.types.Bigint;

/**
 * MergeLocalsPropUpdates -- the branch-merge shape crossed with property
 * mutation: one method that BOTH merges two locals across an {@code if} AND
 * writes contract properties from the merged results. No contract in the repo
 * did both before this one.
 */
class MergeLocalsPropUpdates extends StatefulSmartContract {

    Bigint a;
    Bigint b;
    Bigint total;

    MergeLocalsPropUpdates(Bigint a, Bigint b, Bigint total) {
        super(a, b, total);
        this.a = a;
        this.b = b;
        this.total = total;
    }

    @Public
    void settle(Bigint amount, Bigint toFirst) {
        Bigint na = this.a;
        Bigint nb = this.b;
        if (toFirst.gt(Bigint.ZERO)) {
            na = na.plus(amount);
        } else {
            nb = nb.plus(amount);
        }
        this.a = na;
        this.b = nb;
        this.total = na.plus(nb);
        this.addOutput(1000L, this.a, this.b, this.total);
    }
}
