// TerminalVarlenRead -- regression fixture for GitHub issue #100: a terminal
// method that reads the mutable variable-length (ByteString) state field.
module TerminalVarlenRead {
    use runar::types::{ByteString};

    resource struct TerminalVarlenRead {
        message: &mut ByteString,
    }

    public fun post(contract: &mut TerminalVarlenRead, new_message: ByteString) {
        contract.message = new_message;
    }

    public fun reveal(contract: &TerminalVarlenRead, min_len: bigint) {
        assert!(len(contract.message) > min_len, 0);
    }
}
