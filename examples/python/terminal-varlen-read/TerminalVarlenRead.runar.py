from runar import (
    StatefulSmartContract, Bigint, ByteString, public, assert_, len_,
)


class TerminalVarlenRead(StatefulSmartContract):
    """Regression fixture for GitHub issue #100 -- a terminal method that reads
    the mutable variable-length (ByteString) state field."""

    message: ByteString

    def __init__(self, message: ByteString):
        super().__init__(message)
        self.message = message

    @public
    def post(self, new_message: ByteString):
        self.message = new_message

    @public
    def reveal(self, min_len: Bigint):
        assert_(len_(self.message) > min_len)
