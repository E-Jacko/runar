/**
 * Stack lowering across unrolled for-loops — outer-scope refs (method
 * params, pre-loop consts) must survive loop unrolling:
 *
 *  (a) a const defined before a loop and referenced inside it (including
 *      only inside a nested if-branch) failed compilation with
 *      "Value 'X' not found on stack" — the first iteration consumed it;
 *  (b) worse, a method PARAM referenced after an unrolled loop whose body
 *      also references it was silently lowered to an empty push (OP_0):
 *      compilation succeeded, the env-based interpreter passed, but the
 *      emitted Script failed at runtime (silent interpreter<->Script
 *      divergence).
 *
 * The fix: lowerLoop collects outer refs deeply (nested branches included)
 * and protects them in non-final iterations, and in the final iteration
 * whenever the enclosing scope still references them after the loop. The
 * old silent OP_0 fallbacks are now hard errors.
 */

import { describe, it, expect } from 'vitest';
import { compile, compileFromANF } from '../index.js';
import type { ANFProgram } from '../ir/index.js';

// ---------------------------------------------------------------------------
// Sources
// ---------------------------------------------------------------------------

/** V003 repro: multi-input tx walk — param `data` used inside AND after the loop. */
const LOOP_WALK_SOURCE = `
import { SmartContract, assert, substr, cat, bin2num } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class LoopWalk extends SmartContract {
  readonly pad00: ByteString = "00" as ByteString;

  constructor() {
    super();
  }

  public walk(data: ByteString) {
    let off = 5n;
    for (let i = 0n; i < 3n; i++) {
      if (i < bin2num(cat(substr(data, 4n, 1n), this.pad00))) {
        const sl = bin2num(cat(substr(data, off + 36n, 1n), this.pad00));
        assert(sl < 253n);
        off = off + 36n + 1n + sl + 4n;
      }
    }
    const tail = bin2num(cat(substr(data, off, 1n), this.pad00));
    assert(tail === 7n);
  }
}
`;

/** Symptom (a): const defined before the loop, referenced inside it. */
const CONST_BEFORE_LOOP_SOURCE = `
import { SmartContract, assert, substr, cat, bin2num } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class ConstLoop extends SmartContract {
  readonly pad00: ByteString = "00" as ByteString;

  constructor() {
    super();
  }

  public probe(data: ByteString) {
    const base = 5n;
    let acc = 0n;
    for (let i = 0n; i < 3n; i++) {
      const b = bin2num(cat(substr(data, base + i, 1n), this.pad00));
      acc = acc + b;
    }
    assert(acc === 6n);
  }
}
`;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('stack lowering: outer refs across unrolled loops', () => {
  it('param referenced after a loop is not lowered to an empty push', () => {
    const result = compile(LOOP_WALK_SOURCE, { fileName: 'LoopWalk.runar.ts' });
    expect(result.success).toBe(true);

    // The post-loop code (after the last OP_ENDIF) reads `data` via
    // substr(data, off, 1n). With the bug, `data` was emitted as OP_0
    // right after the final OP_ENDIF; fixed code brings the real param up.
    const asm = result.scriptAsm!;
    const postLoop = asm.slice(asm.lastIndexOf('OP_ENDIF'));
    expect(postLoop).not.toContain('OP_0');
  });

  it('const defined before a loop and referenced inside compiles', () => {
    const result = compile(CONST_BEFORE_LOOP_SOURCE, {
      fileName: 'ConstLoop.runar.ts',
    });
    // Previously: "Value 'base' not found on stack (...)"
    expect(result.success).toBe(true);
    expect(result.scriptHex).toBeDefined();
  });

  it('a load_param that cannot be satisfied is a loud error, not OP_0', () => {
    // Hand-written ANF referencing a parameter the method does not have —
    // the old code silently emitted OP_0 here.
    const program: ANFProgram = {
      contractName: 'Broken',
      properties: [],
      methods: [
        {
          name: 'run',
          isPublic: true,
          params: [{ name: 'x', type: 'bigint' }],
          body: [
            { name: 't0', value: { kind: 'load_param', name: 'ghost' } },
            { name: 't1', value: { kind: 'assert', value: 't0' } },
          ],
        },
      ],
    };

    expect(() => compileFromANF(program)).toThrow(
      /Refusing to emit a silent OP_0/,
    );
  });
});
