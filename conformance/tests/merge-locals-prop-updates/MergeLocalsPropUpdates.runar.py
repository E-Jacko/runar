from runar import (
    StatefulSmartContract, Bigint, public,
)


class MergeLocalsPropUpdates(StatefulSmartContract):
    """The branch-merge shape crossed with property mutation: one method that
    BOTH merges two locals across an `if` AND writes contract properties from
    the merged results. No contract in the repo did both before this one."""

    a: Bigint
    b: Bigint
    total: Bigint

    def __init__(self, a: Bigint, b: Bigint, total: Bigint):
        super().__init__(a, b, total)
        self.a = a
        self.b = b
        self.total = total

    @public
    def settle(self, amount: Bigint, to_first: Bigint):
        na = self.a
        nb = self.b
        if to_first > 0:
            na = na + amount
        else:
            nb = nb + amount
        self.a = na
        self.b = nb
        self.total = na + nb
        self.add_output(1000, self.a, self.b, self.total)
