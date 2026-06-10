import { SmartContract, assert, substr, bin2num, num2bin, cat } from 'runar-lang';
import type { ByteString } from 'runar-lang';

/**
 * Regression test for issue #34 — cross-method parameter-name shadowing.
 *
 * The local `x: bigint` in `walk` must NOT inherit the byte type of the
 * `x: ByteString` parameter of `other`. Before the fix, the ANF param-type
 * lookup searched ALL methods' params, so `x` matched `other`'s parameter and
 * `1n + x` miscompiled to OP_CAT (byte concat, 0x7e) instead of OP_ADD (0x93),
 * making the compiled script diverge from the interpreter.
 */
class StackTrackerRepro extends SmartContract {
  constructor() { super(); }

  public walk(buf: ByteString, count: bigint, target: ByteString) {
    let p: bigint = 0n;
    let found: boolean = false;
    if (0n < count) {
      const x: bigint = bin2num(cat(substr(buf, p, 1n), num2bin(0n, 1n)));
      const blob: ByteString = substr(buf, p, 1n + x);
      if (blob === target) { found = true; }
      p = p + 1n + x;
    }
    assert(found || !found);
  }

  public other(x: ByteString) { assert(x === x); }
}
