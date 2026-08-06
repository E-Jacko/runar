/**
 * `lowerIf`'s stackMap-vs-physical-depth invariant.
 *
 * The branch/loop miscompile family all had one signature: `lowerIf` registers
 * FEWER stackMap names than the arms leave physical slots, so every later
 * operand resolves N-1 slots off. Because the stackMap is the compiler's only
 * model of the stack, nothing downstream notices — the result is a wrong-but-
 * accepted continuation, or an outright unspendable script.
 *
 * The invariant states the one thing that must always be true when `lowerIf`
 * returns:
 *
 *     parent stackMap depth + physical drops emitted after OP_ENDIF
 *       === the depth both arms ended at
 *
 * The naive form (`parent.depth === arm.depth`) is wrong: the post-ENDIF
 * reconcile legitimately ROLL/DROPs stale slots out from under the results, so
 * the drops have to be counted and added back.
 *
 * This is the same genre as the existing Layer B branch-balance guard (#99):
 * a codegen self-check, never a user error, that fails loudly at compile time
 * instead of on-chain. It emits no opcodes, so it is byte-neutral by
 * construction.
 */

import { describe, it, expect } from 'vitest';
import { compile } from '../index.js';

function compileSource(source: string, disableConstantFolding: boolean) {
  return compile(source, { fileName: 'Inv.runar.ts', disableConstantFolding });
}

function contract(body: string, outputs: string): string {
  return `import { StatefulSmartContract } from 'runar-lang';

export class Inv extends StatefulSmartContract {
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

/** Arm writes a property AND rebinds a merged local — two result kinds. */
const PROP_WRITE_K2 = contract(
  `    let na: bigint = 1n;
    let nb: bigint = 2n;
    if (flag > 0n) { this.p = x + 100n; na = x + 1n; } else { nb = x + 2n; }`,
  'this.p, na, nb',
);

const PROP_WRITE_K1 = contract(
  `    let na: bigint = 1n;
    if (flag > 0n) { this.p = x + 100n; na = x + 1n; } else { na = x + 2n; }`,
  'this.p, na, this.b',
);

/** Shapes that are known-good and MUST keep compiling — no spurious fires. */
const GOOD: Array<[string, string]> = [
  [
    'property write alone in the arm',
    contract(`    if (flag > 0n) { this.p = x + 100n; }`, 'this.p, this.a, this.b'),
  ],
  [
    'two property writes in each arm',
    contract(
      `    if (flag > 0n) { this.a = x + 1n; this.b = x + 2n; } else { this.a = x + 3n; this.b = x + 4n; }`,
      'this.p, this.a, this.b',
    ),
  ],
  [
    'K=2 merged locals',
    contract(
      `    let na: bigint = 1n;
    let nb: bigint = 2n;
    if (flag > 0n) { na = x + 1n; } else { nb = x + 2n; }`,
      'this.p, na, nb',
    ),
  ],
  [
    'K=1 merged local rebound in place by both arms',
    contract(
      `    let na: bigint = 1n;
    if (flag > 0n) { na = na + x; } else { na = na + 1n; }`,
      'this.p, na, this.b',
    ),
  ],
  [
    'K=2 merged locals dead after the if',
    contract(
      `    let na: bigint = 1n;
    let nb: bigint = 2n;
    if (flag > 0n) { na = x + 1n; nb = na + 1n; } else { nb = x + 2n; }`,
      'this.p, this.a, nb',
    ),
  ],
  [
    'loop-carried rebind under a nested if',
    contract(
      `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i = 0n; i < 2n; i++) {
      if (i < 5n) { acc = acc + x; wacc = wacc + acc; }
    }`,
      'this.p, acc, wacc',
    ),
  ],
  [
    'if-without-else rebinding a local',
    contract(
      `    let na: bigint = 1n;
    if (flag > 0n) { na = x + 1n; }`,
      'this.p, na, this.b',
    ),
  ],
];

describe('lowerIf stackMap-vs-physical-depth invariant', () => {
  for (const disableConstantFolding of [true, false]) {
    const mode = disableConstantFolding ? 'fold-OFF' : 'fold-ON';

    // The two shapes the invariant was built to catch. They used to compile
    // "successfully" to a script `Spend` rejects outright (locked funds); the
    // invariant then turned them into a compile error, which was containment,
    // not a fix — the source is legal Rúnar.
    //
    // CONVERTED TO ACCEPTING TESTS when the `if` node gained its multi-result
    // contract: an arm-written property is now a declared result of the `if`
    // alongside the merged locals, both arms materialise the whole result set
    // in the declared order, and the invariant holds because the compiler no
    // longer under-counts. The spend-level proof (deploy -> call -> `Spend`,
    // with the hand-derived post-state) lives in
    // packages/runar-testing/src/__tests__/branch-prop-write-with-merged-local-vm.ts.
    it(`${mode}: accepts a property write beside a K=2 merged local`, () => {
      const r = compileSource(PROP_WRITE_K2, disableConstantFolding);
      expect(r.diagnostics.map((d: { message: string }) => d.message).join('\n')).not.toMatch(
        /branch result depth|branch result layout/i,
      );
      expect(r.success).toBe(true);
    });

    it(`${mode}: accepts a property write beside a K=1 merged local`, () => {
      const r = compileSource(PROP_WRITE_K1, disableConstantFolding);
      expect(r.diagnostics.map((d: { message: string }) => d.message).join('\n')).not.toMatch(
        /branch result depth|branch result layout/i,
      );
      expect(r.success).toBe(true);
    });

    for (const [label, source] of GOOD) {
      it(`${mode}: accepts ${label}`, () => {
        const r = compileSource(source, disableConstantFolding);
        const messages = r.diagnostics.map((d: { message: string }) => d.message).join('\n');
        expect(messages).not.toMatch(/branch result depth|branch result layout/i);
        expect(r.success).toBe(true);
      });
    }
  }
});
