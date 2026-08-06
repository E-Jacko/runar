from runar import (
    StatefulSmartContract, Bigint, public,
)


class MergeLocalsShapes(StatefulSmartContract):
    """The three branch-merge arities that had no real-crypto evidence: k=2
    symmetric (both arms rebind both locals), k=3, and a nested `if` whose
    merge lands at the outer level. Companion to `branch-merged-locals`, which
    pins the asymmetric k=2 case."""

    a: Bigint
    b: Bigint
    c: Bigint

    def __init__(self, a: Bigint, b: Bigint, c: Bigint):
        super().__init__(a, b, c)
        self.a = a
        self.b = b
        self.c = c

    @public
    def both_arms(self, x: Bigint, flag: Bigint):
        na = self.a
        nb = self.b
        if flag > 0:
            na = x + 1
            nb = x + 2
        else:
            na = x + 3
            nb = x + 4
        self.add_output(1000, na, nb, self.c)

    @public
    def three(self, x: Bigint, flag: Bigint):
        na = self.a
        nb = self.b
        nc = self.c
        if flag > 0:
            na = x + 1
            nb = x + 2
            nc = x + 3
        else:
            na = x + 4
            nb = x + 5
            nc = x + 6
        self.add_output(1000, na, nb, nc)

    @public
    def nested(self, x: Bigint, outer: Bigint, inner: Bigint):
        na = self.a
        nb = self.b
        if outer > 0:
            if inner > 0:
                na = x + 1
            else:
                nb = x + 2
        self.add_output(1000, na, nb, self.c)
