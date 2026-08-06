/**
 * Independent justification for the three conformance script goldens the
 * multi-result branch node moved.
 *
 * A regenerated golden is a self-produced artifact: the compiler asserting
 * that whatever it just emitted is what it meant to emit. This file is the
 * separate oracle for the three that moved, and it is what
 * `conformance/golden-provenance-allowlist.json` cites:
 *
 *   - `if-else`               14 -> 20 bytes
 *   - `branched-readonly-len` 1086 -> 1096 bytes
 *
 * They moved because each contains an `if` WITH AN ELSE whose arms carry at
 * least one result, which is exactly the set the node now normalises: both
 * arms materialise the declared result list in the declared order instead of
 * the stack lowerer inferring the count and layout from arm depths. `if-else`
 * merges one local (`result`); `branched-readonly-len` writes two properties
 * per arm, which is not a shape `liftBranchUpdateProps` can flatten (an arm
 * whose write is not its last side-effecting binding), so the `if` survives to
 * declare them.
 *
 * `selector` and `tic-tac-toe` do NOT move, and that is deliberate: their
 * `if`/`else if` property-dispatch chains are rewritten by
 * `liftBranchUpdateProps` into flat single-valued `if`s, so they never reach
 * the multi-result path. `selector` is exercised below anyway, as the control
 * that proves the exclusion holds.
 *
 * The oracles used here are NOT the compiler's own goldens:
 *   - stateless (`if-else`): the source-vs-script differential oracle runs the
 *     AST-walking interpreter and the compiled bytes on `@bsv/sdk`'s `Spend`
 *     and requires the same verdict. The two engines diverge upstream of ANF
 *     lowering, so a miscompile in the moved code shows up as a disagreement.
 *   - stateful (`branched-readonly-len`, and `selector` as the unchanged
 *     control): a real deploy -> call round-trip behind
 *     `MockProvider.enableBroadcastValidation()`, so the spend is validated by
 *     `Spend`, checked against a post-state hand-derived from the source.
 *     `selector` additionally re-asserts its original funds-safety property
 *     (deep-review finding C20): a selector value matching NO branch must abort
 *     rather than produce a spendable no-op continuation — the property whose
 *     enabling pass this change must not disturb.
 *
 * Both fold modes, because the goldens are stamped fold-OFF while the shipped
 * default is fold-ON.
 */

import { describe, it, expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { compile } from 'runar-compiler';
import { RunarContract, MockProvider, LocalSigner } from 'runar-sdk';
import { PrivateKey } from '@bsv/sdk';
import { runDifferentialExecution } from '../oracle/index.js';

const PRIV = PrivateKey.fromString('b1'.repeat(32), 16);
const PKH = PRIV.toPublicKey().toHash('hex') as string;

/** Repo root, from this file's location. */
const ROOT = join(__dirname, '..', '..', '..', '..');
const read = (rel: string): string => readFileSync(join(ROOT, rel), 'utf8');

/** Compile -> deploy -> call, with the spend validated by @bsv/sdk's `Spend`. */
async function spend(
  source: string,
  fileName: string,
  disableConstantFolding: boolean,
  ctorArgs: unknown[],
  method: string,
  args: unknown[],
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
  const c = new RunarContract(r.artifact as never, ctorArgs as never);
  c.connect(provider, signer);
  await c.deploy({ satoshis: 1000 });
  await c.call(method, args as never, { satoshis: 1000 });
  return c.state as Record<string, unknown>;
}

describe('moved goldens of the multi-result branch node', () => {
  for (const disableConstantFolding of [true, false]) {
    const mode = disableConstantFolding ? 'fold-OFF' : 'fold-ON';

    it(`${mode} if-else: script and interpreter agree on every arm`, () => {
      const source = read('examples/ts/if-else/IfElse.runar.ts');
      // limit = 10: mode=true -> value+10, mode=false -> value-10, then
      // assert(result > 0). Values chosen so the two arms disagree on the
      // verdict for the SAME input, which is what makes the merged local's
      // slot observable at all.
      for (const modeArg of [true, false]) {
        for (const value of [50n, 5n, -50n]) {
          const r = runDifferentialExecution({
            source,
            fileName: 'IfElse.runar.ts',
            method: 'check',
            args: [value, modeArg],
            constructorArgs: { limit: 10n },
            disableConstantFolding,
          });
          expect(
            r.agrees,
            `value=${value} mode=${modeArg}: interpreter=${r.interpreterAccepted} vm=${r.vmAccepted}`,
          ).toBe(true);
        }
      }
    });

    it(`${mode} selector (unchanged control): each arm spends and C20 still aborts`, async () => {
      const source = read('examples/ts/selector/Selector.runar.ts');
      // 985 bytes before and after — the `liftBranchUpdateProps` exclusion.
      // Constructed with a = 1, b = 2.
      // set(0, 77) takes the first arm: a := 77, b untouched.
      expect(await spend(source, 'Selector.runar.ts', disableConstantFolding, [1n, 2n], 'set', [0n, 77n]))
        .toMatchObject({ a: 77n, b: 2n });
      // set(1, 88) takes the second arm: b := 88, a untouched.
      expect(await spend(source, 'Selector.runar.ts', disableConstantFolding, [1n, 2n], 'set', [1n, 88n]))
        .toMatchObject({ a: 1n, b: 88n });
      // C20: a selector matching no branch must ABORT, not produce a
      // spendable no-op continuation. This is the property the fixture exists
      // for, and it survives the byte movement.
      await expect(
        spend(source, 'Selector.runar.ts', disableConstantFolding, [1n, 2n], 'set', [9n, 99n]),
      ).rejects.toThrow();
    });

    it(`${mode} branched-readonly-len: each arm spends and commits the hand-derived state`, async () => {
      const source = read('examples/ts/branched-readonly-len/BranchedReadonlyLen.runar.ts');
      // Constructed with count = 5, tag = aabb.
      // len(scratch) > 0 -> count := 6, tag := scratch.
      expect(await spend(source, 'BranchedReadonlyLen.runar.ts', disableConstantFolding, [5n, 'aabb'], 'spend', ['ccdd']))
        .toMatchObject({ count: 6n, tag: 'ccdd' });
      // len(scratch) == 0 -> count := 4, tag := '3030'.
      expect(await spend(source, 'BranchedReadonlyLen.runar.ts', disableConstantFolding, [5n, 'aabb'], 'spend', ['']))
        .toMatchObject({ count: 4n, tag: '3030' });
    });
  }
});
