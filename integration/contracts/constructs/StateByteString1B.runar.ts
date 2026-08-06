// TEST-ONLY — not a user example.
// Palmer-2 / OP_N state framing: mutable ByteString state whose length is in
// the OP_1..OP_16 range (here: exactly 1 byte). Serializer must emit
// <len><data> push framing, never bare OP_N as a length. Deploy + update
// on regtest pins the live SDK↔compiler framing path.
import { StatefulSmartContract, assert, len } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class StateByteString1B extends StatefulSmartContract {
  tag: ByteString;

  constructor(tag: ByteString) {
    super(tag);
    this.tag = tag;
  }

  /** Replace the 1-byte tag. Caller must supply another 1-byte value. */
  public setTag(newTag: ByteString) {
    assert(len(newTag) === 1n);
    this.tag = newTag;
  }
}
