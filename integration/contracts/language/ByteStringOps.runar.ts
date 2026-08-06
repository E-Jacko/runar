// TEST-ONLY — not a user example.
import { SmartContract, assert, len, cat, left, right, reverseBytes, num2bin, bin2num } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class ByteStringOps extends SmartContract {
  readonly payload: ByteString;
  constructor(payload: ByteString) {
    super(payload);
    this.payload = payload;
  }
  public verify(): void {
    assert(len(this.payload) === 4n);
    const L = left(this.payload, 2n);
    const R = right(this.payload, 2n);
    assert(cat(L, R) === this.payload);
    assert(len(reverseBytes(this.payload)) === 4n);
    const n = bin2num(num2bin(42n, 8n));
    assert(n === 42n);
  }
}
