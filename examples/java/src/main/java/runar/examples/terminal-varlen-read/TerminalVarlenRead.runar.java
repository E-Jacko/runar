package runar.examples.terminalvarlenread;

import runar.lang.StatefulSmartContract;
import runar.lang.annotations.Public;
import runar.lang.types.Bigint;
import runar.lang.types.ByteString;

import static runar.lang.Builtins.assertThat;
import static runar.lang.Builtins.len;

/**
 * TerminalVarlenRead -- regression fixture for GitHub issue #100: a terminal
 * method that reads the mutable variable-length (ByteString) state field.
 */
class TerminalVarlenRead extends StatefulSmartContract {

    ByteString message;

    TerminalVarlenRead(ByteString message) {
        super(message);
        this.message = message;
    }

    @Public
    void post(ByteString newMessage) {
        this.message = newMessage;
    }

    @Public
    void reveal(Bigint minLen) {
        assertThat(len(this.message).gt(minLen));
    }
}
