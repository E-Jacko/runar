import { StatefulSmartContract, assert, len } from 'runar-lang';
import type { ByteString } from 'runar-lang';

/**
 * TerminalVarlenRead -- regression fixture for GitHub issue #100.
 *
 * `reveal` is a terminal stateful method (no continuation output) that READS
 * the mutable variable-length (ByteString) state field `message`. Such a read
 * requires `_codePart` on the stack so the preimage-relative var-length
 * deserialization can compute the live state offset. The pre-fix compiler only
 * provisioned `_codePart` for continuation builders, so terminal var-length
 * reads silently deserialized against the wrong offset and returned the
 * deploy-time initial value. The compiler now provisions `_codePart` whenever a
 * method reads a mutable ByteString field, and the SDK prefixes the unlocking
 * script accordingly (`usesCodePart`).
 */
class TerminalVarlenRead extends StatefulSmartContract {
  message: ByteString;

  constructor(message: ByteString) {
    super(message);
    this.message = message;
  }

  public post(newMessage: ByteString) {
    this.message = newMessage;
  }

  public reveal(minLen: bigint) {
    assert(len(this.message) > minLen);
  }
}
