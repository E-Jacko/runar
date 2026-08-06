/**
 * An `if` arm that BOTH writes a contract property AND rebinds a merged local.
 *
 * ===========================================================================
 * FIXED by the multi-result branch node. All three sub-shapes below now
 * compile and spend, and each is asserted against the post-state hand-derived
 * from the source — not against anything the compiler produced.
 * ===========================================================================
 *
 * Found 2026-08-06 while auditing the branch/loop "one carrier, N live values"
 * family, by adding a temporary stackMap-vs-physical-depth invariant to
 * `lowerIf` and running the whole suite under it. The invariant held for 4614
 * tests and fired on exactly one shape — the fuzzer's `prop-write-in-arm`
 * (packages/runar-testing/src/fuzzer/generator.ts).
 *
 * CONFIRMED PRE-EXISTING at 32b9cb2a, and confirmed a SEVEN-TIER defect: the
 * TS and Go compilers emitted byte-identical (equally wrong) hex for it, which
 * is the signature every member of this family has had.
 *
 * WHAT USED TO BREAK. The arm produced TWO results — the updated property and
 * the rebound local — but only the LOCAL went through 04-anf-lower's
 * merged-local normalisation (`appendMergedLocalResults` merged LOCALS; a
 * property written in an arm was a different result kind it did not cover).
 * The two arities then failed in two different ways:
 *
 *   K=1 (case D) — no `__merge$` block was appended at all, so the arms ended
 *   at different depths with different layouts:
 *
 *     then: [ ..., p(new), na(new) ]   +2
 *     else: [ ..., na(new) ]           +1
 *
 *   `lowerIf`'s phase-3 padding padded the else arm on the assumption that the
 *   MISSING slots were the topmost ones — but the missing slot was `p`, which
 *   sits BENEATH `na`. ONE stackMap name ended up registered for TWO physical
 *   results.
 *
 *   K>=2 (case A) — the `__merge$` block WAS appended, and the merged-local
 *   trim then dropped everything beneath the K results on the premise that it
 *   was dead. The arm's property write sat beneath them and was NOT dead, so
 *   the write was silently discarded and the script serialised the STALE value
 *   of `p` while the interpreter serialised the new one.
 *
 *   K=1 with the property READ AGAIN after the `if` (case E) — the extra read
 *   reordered the arm's slots so the depths agreed exactly and only the LAYOUT
 *   was wrong. Neither half of the Layer C invariant could see it, so it kept
 *   compiling to an unspendable script after A and D had been contained.
 *
 * All three ran to the end and left a falsy top of stack, so `@bsv/sdk`'s
 * `Spend` rejected the spend outright — the funds were locked.
 *
 * WHY THE FIX IS THE NODE AND NOT A PREDICATE. Every sibling in this family
 * was closed with a targeted predicate. This one could not be: the padding
 * loop's slot SELECTION was what was wrong, not a liveness question, and
 * correcting it meant making an arm's result set include property writes —
 * i.e. giving the `if` node an explicit multi-result contract. The `if` node
 * now declares `results` (see `If.results` in
 * packages/runar-compiler/src/ir/anf-ir.ts), both arms materialise exactly
 * that set in exactly that order, and stack lowering adopts them by the
 * declared order instead of inferring count, liveness or layout by name.
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

/**
 * E: the third sub-shape, and the one that survived the Layer C invariant.
 *
 * Same ingredients as D — a property write beside a K=1 merged local — but the
 * property is READ AGAIN after the `if` (`this.p = 32n + this.p`). That extra
 * read changed the arm's slot ORDER: the arm left `[ ..., p(new), na(new) ]`
 * while the parent modelled `[ ..., na, <if> ]`. The DEPTHS agreed exactly, so
 * neither half of the invariant fired — position 1 simply held the wrong value
 * and the parent still believed `p` lived at its old, stale slot. It compiled,
 * and the script was UNSPENDABLE.
 *
 * With the declared result list the `if` carries `results: ["na", "p"]`, both
 * arms materialise both slots in that order, and the parent adopts them by the
 * declared order — there is no ordering left to infer.
 */
const E = contract('E', `    let na: bigint = 7n;
    if (flag > 0n) { this.p = na * 2n; na = 5n; } else { na = x; }
    this.p = 32n + this.p;`,
  'this.p, na, this.b');

/** C1: the same arm writing ONLY a property — the cond-write-multi-field shape. */
const C1 = contract('C1', `    if (flag > 0n) { this.p = x + 100n; }`,
  'this.p, this.a, this.b');

/** C2: the same arms rebinding ONLY merged locals — the merge-locals shape. */
const C2 = contract('C2', `    let na: bigint = 1n;
    let nb: bigint = 2n;
    if (flag > 0n) { na = x + 1n; } else { nb = x + 2n; }`,
  'this.p, na, nb');

describe('property write beside a merged local in one if arm', () => {
  for (const disableConstantFolding of [true, false]) {
    const mode = disableConstantFolding ? 'fold-OFF' : 'fold-ON';

    // Each expectation is hand-derived from the source with x = 10, and does
    // not come from the compiler. THEN-arm (flag = 1) and ELSE-arm (flag = 0)
    // are both spent, because the defect was a property of the `if`, not of
    // the arm the spender happened to take.

    // A, then-arm: this.p = 10 + 100 = 110; na = 10 + 1 = 11; nb untouched = 2.
    it(`${mode} A: prop write + K=2 merge, then-arm`, async () => {
      expect(await run(A, 'A.runar.ts', disableConstantFolding, 1n))
        .toMatchObject({ p: 110n, a: 11n, b: 2n });
    });

    // A, else-arm: nb = 10 + 2 = 12; na untouched = 1; this.p untouched = 0.
    it(`${mode} A: prop write + K=2 merge, else-arm`, async () => {
      expect(await run(A, 'A.runar.ts', disableConstantFolding, 0n))
        .toMatchObject({ p: 0n, a: 1n, b: 12n });
    });

    // D, then-arm: this.p = 110; na = 11; this.b untouched = 0.
    it(`${mode} D: prop write + K=1 merge, then-arm`, async () => {
      expect(await run(D, 'D.runar.ts', disableConstantFolding, 1n))
        .toMatchObject({ p: 110n, a: 11n, b: 0n });
    });

    // D, else-arm: na = 10 + 2 = 12; this.p untouched = 0.
    it(`${mode} D: prop write + K=1 merge, else-arm`, async () => {
      expect(await run(D, 'D.runar.ts', disableConstantFolding, 0n))
        .toMatchObject({ p: 0n, a: 12n, b: 0n });
    });

    // E, then-arm: na starts 7 -> this.p = 7 * 2 = 14, na = 5; then
    // this.p = 32 + 14 = 46.
    it(`${mode} E: prop write read again after the if, then-arm`, async () => {
      expect(await run(E, 'E.runar.ts', disableConstantFolding, 1n))
        .toMatchObject({ p: 46n, a: 5n, b: 0n });
    });

    // E, else-arm: na = x = 10, this.p untouched 0; then this.p = 32 + 0 = 32.
    it(`${mode} E: prop write read again after the if, else-arm`, async () => {
      expect(await run(E, 'E.runar.ts', disableConstantFolding, 0n))
        .toMatchObject({ p: 32n, a: 10n, b: 0n });
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
