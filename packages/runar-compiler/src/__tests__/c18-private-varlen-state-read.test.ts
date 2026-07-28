/**
 * Regression test for deep-review finding C18 (P1 funds-safety bug).
 *
 * `usesCodePart` / `methodReadsVarLenState` in `05-stack-lower.ts` only walks
 * a method's OWN bindings (plus `if`/`loop` bodies) looking for a direct
 * `load_prop` on a mutable variable-length (ByteString) state field. It does
 * NOT recurse into private helper methods invoked via `method_call` — unlike
 * its sibling walker `methodUsesCheckPreimage`, which already does this.
 *
 * Consequence: a PUBLIC method that reads a mutable ByteString state field
 * ONLY through a PRIVATE helper never sets `usesCodePart`, so `_codePart` is
 * never pushed as an implicit parameter and `lowerDeserializeState` takes the
 * "terminal method, skip variable-length deserialization" shortcut. The
 * private helper's `load_prop` then falls back to the deploy-time constant
 * (or constructor placeholder) instead of the live on-chain state — a silent
 * wrong-result / funds-safety bug for any call built against current state.
 */
import { describe, it, expect } from 'vitest';
import { parse } from '../passes/01-parse.js';
import { lowerToANF } from '../passes/04-anf-lower.js';
import { lowerToStack } from '../passes/05-stack-lower.js';
import { compile } from '../index.js';
import type { StackProgram } from '../ir/index.js';

function compileToStack(source: string): StackProgram {
  const parseResult = parse(source);
  if (!parseResult.contract) {
    throw new Error(`Parse failed: ${parseResult.errors.map(e => e.message).join(', ')}`);
  }
  const anf = lowerToANF(parseResult.contract);
  return lowerToStack(anf);
}

// Control: the public method reads the mutable ByteString field directly.
const DIRECT = `import { StatefulSmartContract, assert, len } from 'runar-lang';
import type { ByteString } from 'runar-lang';
class StateReadDirect extends StatefulSmartContract {
  tag: ByteString;
  constructor(tag: ByteString) { super(tag); this.tag = tag; }
  public check(expected: bigint): void { assert(len(this.tag) === expected); }
}`;

// Bug case: the public method reads the same field ONLY via a private helper.
const VIA_HELPER = `import { StatefulSmartContract, assert, len } from 'runar-lang';
import type { ByteString } from 'runar-lang';
class StateReadViaHelper extends StatefulSmartContract {
  tag: ByteString;
  constructor(tag: ByteString) { super(tag); this.tag = tag; }
  private tagLen(): bigint { return len(this.tag); }
  public check(expected: bigint): void { assert(this.tagLen() === expected); }
}`;

describe('C18 — private-helper read of mutable ByteString state must force _codePart', () => {
  it('control: direct read sets usesCodePart on the public method (Stack IR)', () => {
    const program = compileToStack(DIRECT);
    const check = program.methods.find(m => m.name === 'check');
    expect(check).toBeDefined();
    expect(check!.usesCodePart).toBe(true);
  });

  it('bug case: read via private helper must ALSO set usesCodePart on the public method (Stack IR)', () => {
    const program = compileToStack(VIA_HELPER);
    const check = program.methods.find(m => m.name === 'check');
    expect(check).toBeDefined();
    expect(check!.usesCodePart).toBe(true);
  });

  it('end-to-end: compiled artifact ABI reports usesCodePart identically for both variants', () => {
    const direct = compile(DIRECT, { fileName: 'StateReadDirect.runar.ts' });
    const viaHelper = compile(VIA_HELPER, { fileName: 'StateReadViaHelper.runar.ts' });

    expect(direct.success).toBe(true);
    expect(viaHelper.success).toBe(true);

    const directCheck = direct.artifact!.abi.methods.find(m => m.name === 'check');
    const viaHelperCheck = viaHelper.artifact!.abi.methods.find(m => m.name === 'check');
    expect(directCheck).toBeDefined();
    expect(viaHelperCheck).toBeDefined();

    expect(directCheck!.usesCodePart).toBe(true);
    expect(viaHelperCheck!.usesCodePart).toBe(true);
  });
});
