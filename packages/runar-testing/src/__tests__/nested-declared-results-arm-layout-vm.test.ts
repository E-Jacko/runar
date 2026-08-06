/**
 * OPEN DEFECT — a declared-results `if` nested inside another `if`'s arm
 * rotates the slots it inherited from that arm.
 *
 * ===========================================================================
 * THIS SUITE IS SKIPPED BECAUSE THE DEFECT IS NOT FIXED. It is checked in as
 * the pinned reduction: un-skip it to work on the defect and it goes red
 * immediately, with post-state values derived from the source by hand.
 * ===========================================================================
 *
 * Found by an independent adversarial review of the multi-result branch node
 * (4b0f688f) as finding P1-1, and CONFIRMED PRE-EXISTING: the `taken/else`
 * case fails identically with 04-anf-lower.ts reverted to 4b0f688f, so this is
 * neither introduced nor widened by the assert-false-else / nesting fixes that
 * ship alongside this file.
 *
 * THE MECHANISM. The inner `if` merges one local in both arms with a non-empty
 * else, so it declares `results: ["a"]`. Adopting a declared result physically
 * ROLL+DROPs the stale slot out from under the results, and that scan covers
 * the WHOLE arm stack — including the region the arm inherited from the
 * ENCLOSING `if`'s arm. The enclosing `lowerIf` then reconciles by NAME SET
 * (`preIfNames` minus `thenCtx.stackMap.namedSlots()`) and by DEPTH (Layer C's
 * `stackMap.depth + postEndifDrops === armDepth`). Neither can see a slot
 * removed from the MIDDLE while a same-named slot appears on TOP: the name set
 * is unchanged and the depths agree exactly. Only the LAYOUT is wrong.
 *
 * So the outer `if`'s two paths leave the same depth with different layouts —
 * the then-path ends `[..., y, a_new]` where the else-path (empty, padded)
 * still has `a` at its original depth — and everything after OP_ENDIF is
 * generated against one assumed layout. The else path compiles to a script
 * that runs to the end and fails OP_VERIFY. Funds locked.
 *
 * WHY IT IS NOT FIXED HERE. The two invariants that catch it are both
 * over-strict at HEAD, measured rather than assumed:
 *
 *   - "parent model == arms' model minus the result slots" (the form §9 of
 *     packages/runar-compiler/docs/multi-result-branch-node.md prototyped and
 *     predicted would be clean once the K=1 alias rebind was deleted) fails
 *     41 test files at HEAD. The alias rebind was deleted only for DECLARING
 *     `if`s; every `if` without an else, and every lifted chain, still takes it
 *     and still moves a slot by design.
 *   - the arms-vs-arms variant ("both arms must agree on the layout they
 *     inherited") narrows that to three contracts, but one is TicTacToe, whose
 *     spendability is proven on a regtest node — so it is over-strict too.
 *
 * A real fix means teaching `lowerIf`'s reconcile about an arm that rearranged
 * inherited slots, which moves bytes in all seven tiers. That is deliberately
 * a separate change from the boundary fixes this file ships beside.
 */

import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract, MockProvider, LocalSigner } from 'runar-sdk';
import { PrivateKey } from '@bsv/sdk';

const PRIV = PrivateKey.fromString('b1'.repeat(32), 16);
const PKH = PRIV.toPublicKey().toHash('hex') as string;

/** Compile -> deploy -> call, with @bsv/sdk's real `Spend` behind broadcast. */
async function run(
  source: string,
  fold: boolean,
  args: bigint[],
): Promise<Record<string, unknown>> {
  const r = compile(source, {
    fileName: 'NestedAdopt.runar.ts',
    disableConstantFolding: fold,
  });
  if (!r.success || !r.artifact) {
    throw new Error('compile failed: ' + r.diagnostics
      .filter((d) => d.severity !== 'warning').map((d) => d.message).join('; '));
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
  await c.call('go', args, { satoshis: 1000 });
  return c.state as Record<string, unknown>;
}

/**
 * `y` is the live sibling slot the inner `if`'s adopt loop rotates past. Both
 * `a` and `y` are live after the outer `if` (the `assert` reads both), so
 * neither can be dropped and the inner arm's roll has something to move.
 */
const SRC = `import { StatefulSmartContract } from 'runar-lang';

export class NestedAdopt extends StatefulSmartContract {
  p: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.p = seed; }

  public go(x: bigint, c1: bigint, c2: bigint) {
    let a: bigint = 1n;
    let y: bigint = x + 2n;
    if (c1 > 0n) {
      if (c2 > 0n) { a = 5n; } else { a = 6n; }
    }
    assert(a + y > 0n);
    this.p = a * 10n + y;
  }
}
`;

describe.skip('OPEN: nested declared-results if rotates its enclosing arm', () => {
  for (const fold of [true, false]) {
    const mode = fold ? 'fold-OFF' : 'fold-ON';

    // Passes at HEAD. Kept so the fix cannot "succeed" by breaking this path.
    it(`inner then-arm taken (${mode})`, async () => {
      // x=3 -> y=5; c1>0 and c2>0 -> a=5; p = 5*10 + 5.
      expect((await run(SRC, fold, [3n, 1n, 1n])).p).toBe(55n);
    });

    // THE DEFECT. Same script, the inner ELSE arm.
    it(`inner else-arm taken (${mode})`, async () => {
      // x=3 -> y=5; c1>0 and c2==0 -> a=6; p = 6*10 + 5.
      expect((await run(SRC, fold, [3n, 1n, 0n])).p).toBe(65n);
    });

    // Passes at HEAD: the outer `if` is skipped entirely, so nothing rotates.
    it(`outer if skipped (${mode})`, async () => {
      // x=3 -> y=5; c1==0 leaves a at its initial 1n; p = 1*10 + 5.
      expect((await run(SRC, fold, [3n, 0n, 0n])).p).toBe(15n);
    });
  }
});
