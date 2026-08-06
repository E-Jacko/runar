/**
 * KNOWN-OPEN DEFECT — an `if` arm that BOTH writes a contract property AND
 * rebinds a merged local compiles to an UNSPENDABLE script.
 *
 * ===========================================================================
 * NOT FIXED. This file PINS the defect so it cannot be lost again; the
 * `it.fails` cases below pass only while the defect is present, and go RED the
 * moment someone fixes it. Whoever fixes it must convert them to ordinary
 * assertions in the same change.
 * ===========================================================================
 *
 * Found 2026-08-06 while auditing the branch/loop "one carrier, N live values"
 * family, by adding a temporary stackMap-vs-physical-depth invariant to
 * `lowerIf` and running the whole suite under it. The invariant held for 4614
 * tests and fired on exactly one shape — the fuzzer's `prop-write-in-arm`
 * (packages/runar-testing/src/fuzzer/generator.ts) — reporting a parent
 * stackMap of 9 against 10 physical slots with no compensating drop.
 *
 * CONFIRMED PRE-EXISTING at 32b9cb2a, and confirmed a SEVEN-TIER defect: the
 * TS and Go compilers emit byte-identical (equally wrong) hex for it, which is
 * the signature every member of this family has had.
 *
 * WHAT BREAKS. The arm produces TWO results — the updated property and the
 * rebound local — but only the LOCAL goes through 04-anf-lower's merged-local
 * normalisation (`appendMergedLocalResults` merges LOCALS; a property written
 * in an arm is a different result kind it does not cover). So the arms end at
 * different depths with different layouts:
 *
 *   then: [ ..., p(new), na(new) ]   +2
 *   else: [ ..., na(new) ]           +1
 *
 * `lowerIf`'s phase-3 padding then pads the else arm on the assumption that the
 * MISSING slots are the topmost ones — but here the missing slot is `p`, which
 * sits BENEATH `na` in the then arm. It pushes an empty placeholder on top
 * instead, the layout check declines, and control falls to the single-slot
 * fallback: ONE stackMap name registered for TWO physical results. Execution
 * runs to the end and leaves a falsy top of stack, so `@bsv/sdk`'s `Spend`
 * rejects the spend outright — the funds are locked.
 *
 * WHY IT IS NOT PATCHED HERE. Every sibling in this family was closed with a
 * targeted predicate. This one cannot be: the padding loop's slot SELECTION is
 * what is wrong, not a liveness question, and correcting it means making an
 * arm's result set include property writes — i.e. giving the `if` node an
 * explicit multi-result contract. That is the design change assessed in
 * packages/runar-compiler/docs/multi-result-branch-node.md, and this defect is
 * the primary evidence in it.
 *
 * NOT REACHED BY ANY SHIPPED ARTIFACT. A 2026-08-06 structural sweep of every
 * `.runar.*` in the repo found ZERO methods with a property write and a local
 * rebind in the same `if` arm. `conformance/tests/cond-write-multi-field`
 * writes only properties in its arm (control C below, which passes), and
 * `conformance/tests/merge-locals-prop-updates` writes its properties AFTER
 * the `if`. The combination is unfixtured, which is why it survived.
 */

import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract, MockProvider, LocalSigner } from 'runar-sdk';
import { PrivateKey } from '@bsv/sdk';

const PRIV = PrivateKey.fromString('b1'.repeat(32), 16);
const PKH = PRIV.toPublicKey().toHash('hex') as string;

function contract(name: string, body: string, outputs: string): string {
  return `import { StatefulSmartContract } from 'runar-lang';

export class ${name} extends StatefulSmartContract {
  p: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.p = seed; }

  public go(x: bigint, flag: bigint) {
${body}
    this.addOutput(1000n, ${outputs});
  }
}
`;
}

/** Compile -> deploy -> call against @bsv/sdk's real `Spend` behind broadcast. */
async function run(
  source: string,
  fileName: string,
  disableConstantFolding: boolean,
  flag: bigint,
): Promise<Record<string, unknown>> {
  const r = compile(source, { fileName, disableConstantFolding });
  if (!r.success || !r.artifact) {
    throw new Error(`compile failed: ${r.diagnostics.map((d) => d.message).join('; ')}`);
  }
  const signer = new LocalSigner(PRIV.toString());
  const provider = new MockProvider();
  provider.enableBroadcastValidation();
  provider.addUtxo(await signer.getAddress(), {
    txid: 'ee'.repeat(32),
    outputIndex: 0,
    satoshis: 1_000_000,
    script: '76a914' + PKH + '88ac',
  });
  const c = new RunarContract(r.artifact as never, [0n]);
  c.connect(provider, signer);
  await c.deploy({ satoshis: 1000 });
  await c.call('go', [10n, flag], { satoshis: 1000 });
  return c.state as Record<string, unknown>;
}

/** A: property write + K=2 merged locals in the same arm. THE DEFECT. */
const A = contract('A', `    let na: bigint = 1n;
    let nb: bigint = 2n;
    if (flag > 0n) { this.p = x + 100n; na = x + 1n; } else { nb = x + 2n; }`,
  'this.p, na, nb');

/** D: property write + K=1 merged local in the same arm. THE DEFECT, arity 1. */
const D = contract('D', `    let na: bigint = 1n;
    if (flag > 0n) { this.p = x + 100n; na = x + 1n; } else { na = x + 2n; }`,
  'this.p, na, this.b');

/** C1: the same arm writing ONLY a property — the cond-write-multi-field shape. */
const C1 = contract('C1', `    if (flag > 0n) { this.p = x + 100n; }`,
  'this.p, this.a, this.b');

/** C2: the same arms rebinding ONLY merged locals — the merge-locals shape. */
const C2 = contract('C2', `    let na: bigint = 1n;
    let nb: bigint = 2n;
    if (flag > 0n) { na = x + 1n; } else { nb = x + 2n; }`,
  'this.p, na, nb');

describe('KNOWN OPEN: property write beside a merged local in one if arm', () => {
  for (const disableConstantFolding of [true, false]) {
    const mode = disableConstantFolding ? 'fold-OFF' : 'fold-ON';

    // Hand-derived from the source with x = 10, flag = 1 (then-arm taken):
    //   A: p = 110, na = 11, nb untouched at 2.
    //   D: p = 110, na = 11, b untouched at 0.
    it.fails(`${mode} A: prop write + K=2 merge — then-arm is UNSPENDABLE`, async () => {
      expect(await run(A, 'A.runar.ts', disableConstantFolding, 1n))
        .toMatchObject({ p: 110n, a: 11n, b: 2n });
    });

    it.fails(`${mode} D: prop write + K=1 merge — then-arm is UNSPENDABLE`, async () => {
      expect(await run(D, 'D.runar.ts', disableConstantFolding, 1n))
        .toMatchObject({ p: 110n, a: 11n, b: 0n });
    });

    // The arm the defect does NOT touch: the else-arm has no property write,
    // so it carries one result and reconciles correctly.
    it(`${mode} A: the else-arm (no property write) is correct`, async () => {
      expect(await run(A, 'A.runar.ts', disableConstantFolding, 0n))
        .toMatchObject({ p: 0n, a: 1n, b: 12n });
    });

    it(`${mode} C1 (control): property write alone in the arm`, async () => {
      expect(await run(C1, 'C1.runar.ts', disableConstantFolding, 1n))
        .toMatchObject({ p: 110n, a: 0n, b: 0n });
    });

    it(`${mode} C2 (control): merged locals alone in the arms`, async () => {
      expect(await run(C2, 'C2.runar.ts', disableConstantFolding, 1n))
        .toMatchObject({ p: 0n, a: 11n, b: 2n });
    });
  }
});
