pragma runar ^0.1.0;

/// @title MergeLocalsShapes
/// @notice The three branch-merge arities that had no real-crypto evidence:
/// k=2 symmetric (both arms rebind both locals), k=3, and a nested `if` whose
/// merge lands at the outer level. Companion to `branch-merged-locals`, which
/// pins the asymmetric k=2 case.
contract MergeLocalsShapes is StatefulSmartContract {
    bigint a;
    bigint b;
    bigint c;

    constructor(bigint _a, bigint _b, bigint _c) {
        a = _a;
        b = _b;
        c = _c;
    }

    function bothArms(bigint x, bigint flag) public {
        bigint na = this.a;
        bigint nb = this.b;
        if (flag > 0) {
            na = x + 1;
            nb = x + 2;
        } else {
            na = x + 3;
            nb = x + 4;
        }
        this.addOutput(1000, na, nb, this.c);
    }

    function three(bigint x, bigint flag) public {
        bigint na = this.a;
        bigint nb = this.b;
        bigint nc = this.c;
        if (flag > 0) {
            na = x + 1;
            nb = x + 2;
            nc = x + 3;
        } else {
            na = x + 4;
            nb = x + 5;
            nc = x + 6;
        }
        this.addOutput(1000, na, nb, nc);
    }

    function nested(bigint x, bigint outer, bigint inner) public {
        bigint na = this.a;
        bigint nb = this.b;
        if (outer > 0) {
            if (inner > 0) {
                na = x + 1;
            } else {
                nb = x + 2;
            }
        }
        this.addOutput(1000, na, nb, this.c);
    }
}
