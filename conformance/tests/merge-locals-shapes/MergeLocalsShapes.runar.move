// MergeLocalsShapes -- the three branch-merge arities that had no real-crypto
// evidence: k=2 symmetric (both arms rebind both locals), k=3, and a nested
// `if` whose merge lands at the outer level. Companion to
// `branch-merged-locals`, which pins the asymmetric k=2 case.
module MergeLocalsShapes {
    resource struct MergeLocalsShapes {
        a: &mut bigint,
        b: &mut bigint,
        c: &mut bigint,
    }

    public fun bothArms(contract: &mut MergeLocalsShapes, x: bigint, flag: bigint) {
        let na = contract.a;
        let nb = contract.b;
        if (flag > 0) {
            na = x + 1;
            nb = x + 2;
        } else {
            na = x + 3;
            nb = x + 4;
        };
        contract.addOutput(1000, na, nb, contract.c);
    }

    public fun three(contract: &mut MergeLocalsShapes, x: bigint, flag: bigint) {
        let na = contract.a;
        let nb = contract.b;
        let nc = contract.c;
        if (flag > 0) {
            na = x + 1;
            nb = x + 2;
            nc = x + 3;
        } else {
            na = x + 4;
            nb = x + 5;
            nc = x + 6;
        };
        contract.addOutput(1000, na, nb, nc);
    }

    public fun nested(contract: &mut MergeLocalsShapes, x: bigint, outer: bigint, inner: bigint) {
        let na = contract.a;
        let nb = contract.b;
        if (outer > 0) {
            if (inner > 0) {
                na = x + 1;
            } else {
                nb = x + 2;
            };
        };
        contract.addOutput(1000, na, nb, contract.c);
    }
}
