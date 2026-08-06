package runar.conformance.loopifmergedlocals;

import runar.lang.StatefulSmartContract;
import runar.lang.annotations.Public;
import runar.lang.types.Bigint;

/**
 * LoopIfMergedLocals -- branch-merged locals whose merged values are DEAD in
 * the enclosing scope, which is what an {@code if} inside a loop body always
 * makes them. Companion to {@code merge-locals-shapes} (merged locals LIVE
 * after the {@code if}) and {@code bounded-loop} (a loop with no branch in it)
 * -- neither covers their intersection, which is where the merge block's
 * premise fails.
 */
class LoopIfMergedLocals extends StatefulSmartContract {

    Bigint a;
    Bigint b;
    Bigint c;

    LoopIfMergedLocals(Bigint a, Bigint b, Bigint c) {
        super(a, b, c);
        this.a = a;
        this.b = b;
        this.c = c;
    }

    @Public
    void guarded(Bigint x, Bigint limit) {
        Bigint na = Bigint.ZERO;
        Bigint nb = Bigint.ZERO;
        for (Bigint i = Bigint.ZERO; i.lt(Bigint.of(2)); i = i.plus(Bigint.ONE)) {
            if (i.lt(limit)) {
                na = na.plus(x);
                nb = nb.plus(na);
            }
        }
        this.addOutput(1000L, na, nb, this.c);
    }

    @Public
    void afterIf(Bigint x, Bigint limit) {
        Bigint na = Bigint.ZERO;
        Bigint nb = Bigint.ZERO;
        for (Bigint i = Bigint.ZERO; i.lt(Bigint.of(2)); i = i.plus(Bigint.ONE)) {
            if (i.lt(limit)) {
                na = na.plus(x);
            }
            nb = nb.plus(na);
        }
        this.addOutput(1000L, na, nb, this.c);
    }
}
