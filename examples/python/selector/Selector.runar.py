from runar import (
    StatefulSmartContract, Bigint, public, assert_,
)


class Selector(StatefulSmartContract):
    """Regression fixture for deep-review finding C20 -- a dispatch method whose
    branches each end in a single state update and whose terminal `else` is
    `assert_(False)`. The abort must survive ANF lowering so an out-of-range
    selector fails the script instead of producing a spendable no-op."""

    a: Bigint
    b: Bigint

    def __init__(self, a: Bigint, b: Bigint):
        super().__init__(a, b)
        self.a = a
        self.b = b

    @public
    def set(self, i: Bigint, v: Bigint):
        if i == 0:
            self.a = v
        elif i == 1:
            self.b = v
        else:
            assert_(False)
