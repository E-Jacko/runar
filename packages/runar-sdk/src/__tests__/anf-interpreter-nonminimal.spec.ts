/**
 * The SDK's ANF interpreter must enforce the on-chain MINIMAL-ENCODING rule,
 * like the other six tiers' ANF interpreters and the AST interpreter.
 *
 * `OP_LSHIFT`/`OP_RSHIFT` preserve the operand's byte length, so `1 >> 1`
 * leaves `[0x00]` — a NON-MINIMAL zero. Every numeric consumer on chain
 * (`OP_ADD`…`OP_MOD`, `OP_NUMEQUAL`/`OP_NOT`, the relational ops, and a shift's
 * COUNT) decodes with `fRequireMinimal = true` and ABORTS. An interpreter that
 * re-minimises instead reports a spend valid that no node accepts.
 *
 * This one matters beyond off-chain smoke tests: `RunarContract.prepareCall`
 * runs this interpreter to compute the CONTINUATION STATE it then commits to a
 * real transaction. Getting it wrong builds a broadcast against a state the
 * covenant will not accept.
 *
 * Second defect pinned here: the `@ref:` alias. ANF lowering emits an alias
 * binding for every named local (`left = @ref:t2`), and the threaded stack
 * bytes live in a side map keyed by binding NAME. Returning `env[target]`
 * without carrying `scriptBytes[target]` drops them — which both blinds the
 * minimal check and breaks the chained byte-op threading itself, making
 * `(2 << 8) | 5` FALSE-abort on an OP_OR length mismatch the chain never
 * raises.
 */

import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { executeStrict } from '../anf-interpreter.js';

function anfFor(body: string): unknown {
  const src = `import { SmartContract, assert } from 'runar-lang';

export class S extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f(): void { ${body} }
}
`;
  const r = compile(src, { fileName: 'S.runar.ts', disableConstantFolding: true });
  if (!r.success || !r.anf) {
    throw new Error('compile failed: ' + r.diagnostics.map((d) => d.message).join('; '));
  }
  return r.anf;
}

describe('SDK ANF interpreter — minimal encoding on numeric consumption', () => {
  it('aborts when a non-minimal shift result feeds a comparison', () => {
    // 1 >> 1 -> [0x00]; `=== 0n` lowers to a numeric op and a node aborts.
    const anf = anfFor('assert((this.n >> 1n) === 0n);');
    expect(() => executeStrict(anf as never, 'f', {}, {}, [1n])).toThrow(
      /non-minimal/i,
    );
  });

  it('aborts when a non-minimal shift result feeds arithmetic', () => {
    const anf = anfFor('assert(((this.n >> 1n) + 0n) === 0n);');
    expect(() => executeStrict(anf as never, 'f', {}, {}, [1n])).toThrow(
      /non-minimal/i,
    );
  });

  // --- controls: these must keep working -----------------------------------

  it('a MINIMAL shift result is unaffected', () => {
    const anf = anfFor('assert((this.n >> 1n) === 1n);');
    expect(() => executeStrict(anf as never, 'f', {}, {}, [2n])).not.toThrow();
  });

  it('chained byte ops through a named-local alias still accept', () => {
    // `(2 << 8) | 5` — OP_LSHIFT leaves a 1-byte non-minimal 0x00, OP_OR with
    // [0x05] has MATCHING length and yields 5. Both engines must ACCEPT; this
    // is the shape pinned by fuzz-regressions/2026-07-14-chained-shift-or-nonminimal.
    // It goes through an alias, so it also pins the `@ref:` byte propagation.
    const anf = anfFor('const left: bigint = this.n << 8n; assert((left | 5n) === 5n);');
    expect(() => executeStrict(anf as never, 'f', {}, {}, [2n])).not.toThrow();
  });

  it('the byte-array ops themselves are NOT gated', () => {
    // `~` is a byte op: inverting the 1-byte 0x00 gives 0xff = -127 decoded.
    const anf = anfFor('const t: bigint = this.n << 8n; assert((~t) === -127n);');
    expect(() => executeStrict(anf as never, 'f', {}, {}, [2n])).not.toThrow();
  });
});
