from runar import (
    StatefulSmartContract, Bigint, public,
)


class CondWriteMultiField(StatefulSmartContract):
    """Regression fixture for GitHub issue #99 -- a conditional write of two
    mutable state fields in an `if` without an `else`."""

    a: Bigint
    b: Bigint

    def __init__(self, a: Bigint, b: Bigint):
        super().__init__(a, b)
        self.a = a
        self.b = b

    @public
    def bump(self, flag: Bigint):
        if flag > 0:
            self.a = self.a + 1
            self.b = self.b + 2
        self.add_output(1000, self.a, self.b)
