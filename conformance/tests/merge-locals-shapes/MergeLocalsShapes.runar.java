package runar.conformance.mergelocalsshapes;

import runar.lang.StatefulSmartContract;
import runar.lang.annotations.Public;
import runar.lang.types.Bigint;

/**
 * MergeLocalsShapes -- the three branch-merge arities that had no real-crypto
 * evidence: k=2 symmetric (both arms rebind both locals), k=3, and a nested
 * {@code if} whose merge lands at the outer level. Companion to
 * {@code branch-merged-locals}, which pins the asymmetric k=2 case.
 */
class MergeLocalsShapes extends StatefulSmartContract {

    Bigint a;
    Bigint b;
    Bigint c;

    MergeLocalsShapes(Bigint a, Bigint b, Bigint c) {
        super(a, b, c);
        this.a = a;
        this.b = b;
        this.c = c;
    }

    @Public
    void bothArms(Bigint x, Bigint flag) {
        Bigint na = this.a;
        Bigint nb = this.b;
        if (flag.gt(Bigint.ZERO)) {
            na = x.plus(Bigint.ONE);
            nb = x.plus(Bigint.of(2));
        } else {
            na = x.plus(Bigint.of(3));
            nb = x.plus(Bigint.of(4));
        }
        this.addOutput(1000L, na, nb, this.c);
    }

    @Public
    void three(Bigint x, Bigint flag) {
        Bigint na = this.a;
        Bigint nb = this.b;
        Bigint nc = this.c;
        if (flag.gt(Bigint.ZERO)) {
            na = x.plus(Bigint.ONE);
            nb = x.plus(Bigint.of(2));
            nc = x.plus(Bigint.of(3));
        } else {
            na = x.plus(Bigint.of(4));
            nb = x.plus(Bigint.of(5));
            nc = x.plus(Bigint.of(6));
        }
        this.addOutput(1000L, na, nb, nc);
    }

    @Public
    void nested(Bigint x, Bigint outer, Bigint inner) {
        Bigint na = this.a;
        Bigint nb = this.b;
        if (outer.gt(Bigint.ZERO)) {
            if (inner.gt(Bigint.ZERO)) {
                na = x.plus(Bigint.ONE);
            } else {
                nb = x.plus(Bigint.of(2));
            }
        }
        this.addOutput(1000L, na, nb, this.c);
    }
}
