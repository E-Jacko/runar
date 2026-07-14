pragma runar ^0.1.0;

/// @title TerminalVarlenRead
/// @notice Regression fixture for GitHub issue #100 -- a terminal method that
/// reads the mutable variable-length (ByteString) state field.
contract TerminalVarlenRead is StatefulSmartContract {
    ByteString message;

    constructor(ByteString _message) {
        message = _message;
    }

    function post(ByteString newMessage) public {
        this.message = newMessage;
    }

    function reveal(bigint minLen) public {
        require(len(this.message) > minLen);
    }
}
