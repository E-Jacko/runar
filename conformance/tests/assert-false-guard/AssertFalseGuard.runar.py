from runar import (
    StatefulSmartContract, Bigint, public, assert_,
)


class AssertFalseGuard(StatefulSmartContract):
    """The `assert_(False)`-else guard, in the two positions the multi-result
    branch node originally missed. `bump` is a single property written under a
    guard whose else is the dead abort -- recognised as a ONE-branch chain, so
    excluded from declaring its result, and not rewritten either because the
    lift only rewrites chains of two or more. `dispatch` is `selector`'s exact
    chain one loop deeper, where the lift never walks."""

    count: Bigint
    a: Bigint
    b: Bigint

    def __init__(self, count: Bigint, a: Bigint, b: Bigint):
        super().__init__(count, a, b)
        self.count = count
        self.a = a
        self.b = b

    @public
    def bump(self, n: Bigint):
        if n > 0:
            self.count = self.count + n
        else:
            assert_(False)

    @public
    def dispatch(self, sel: Bigint, v: Bigint):
        for i in range(2):
            if sel == 0:
                self.a = v
            elif sel == 1:
                self.b = v
            else:
                assert_(False)
