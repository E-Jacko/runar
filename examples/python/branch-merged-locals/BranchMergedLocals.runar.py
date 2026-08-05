from runar import (
    StatefulSmartContract, Bigint, public,
)


class BranchMergedLocals(StatefulSmartContract):
    """Regression fixture for the branch-merged-local miscompilation reported
    privately on 2026-08-03: two locals initialised from state, the arms of an
    `if` reassigning DIFFERENT ones, both feeding the continuation. Post-branch
    references used to resolve to the dead pre-branch binding."""

    a: Bigint
    b: Bigint

    def __init__(self, a: Bigint, b: Bigint):
        super().__init__(a, b)
        self.a = a
        self.b = b

    @public
    def bid(self, amount: Bigint, to_first: Bigint):
        na = self.a
        nb = self.b
        if to_first > 0:
            na = amount
        else:
            nb = amount
        self.add_output(1000, na, nb)
