from runar import (
    StatefulSmartContract, Bigint, public,
)


class LoopIfMergedLocals(StatefulSmartContract):
    """Branch-merged locals whose merged values are DEAD in the enclosing
    scope, which is what an `if` inside a loop body always makes them.
    Companion to `merge-locals-shapes` (merged locals LIVE after the `if`) and
    `bounded-loop` (a loop with no branch in it) -- neither covers their
    intersection, which is where the merge block's premise fails."""

    a: Bigint
    b: Bigint
    c: Bigint

    def __init__(self, a: Bigint, b: Bigint, c: Bigint):
        super().__init__(a, b, c)
        self.a = a
        self.b = b
        self.c = c

    @public
    def guarded(self, x: Bigint, limit: Bigint):
        na: Bigint = 0
        nb: Bigint = 0
        for i in range(2):
            if i < limit:
                na = na + x
                nb = nb + na
        self.add_output(1000, na, nb, self.c)

    @public
    def after_if(self, x: Bigint, limit: Bigint):
        na: Bigint = 0
        nb: Bigint = 0
        for i in range(2):
            if i < limit:
                na = na + x
            nb = nb + na
        self.add_output(1000, na, nb, self.c)
