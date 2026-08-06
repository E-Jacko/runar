pragma runar ^0.1.0;

/// @title LoopIfMergedLocals
/// @notice Branch-merged locals whose merged values are DEAD in the enclosing
/// scope, which is what an `if` inside a loop body always makes them. Companion
/// to `merge-locals-shapes` (merged locals LIVE after the `if`) and
/// `bounded-loop` (a loop with no branch in it) -- neither covers their
/// intersection, which is where the merge block's premise fails.
contract LoopIfMergedLocals is StatefulSmartContract {
    bigint a;
    bigint b;
    bigint c;

    constructor(bigint _a, bigint _b, bigint _c) {
        a = _a;
        b = _b;
        c = _c;
    }

    function guarded(bigint x, bigint limit) public {
        bigint na = 0;
        bigint nb = 0;
        for (bigint i = 0; i < 2; i++) {
            if (i < limit) {
                na = na + x;
                nb = nb + na;
            }
        }
        this.addOutput(1000, na, nb, this.c);
    }

    function afterIf(bigint x, bigint limit) public {
        bigint na = 0;
        bigint nb = 0;
        for (bigint i = 0; i < 2; i++) {
            if (i < limit) {
                na = na + x;
            }
            nb = nb + na;
        }
        this.addOutput(1000, na, nb, this.c);
    }
}
