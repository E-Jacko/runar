/**
 * A K>=2 branch-merged-local block whose merged locals are NOT all live after
 * the `if` must still compile to a Script that computes what the source says.
 *
 * ===========================================================================
 * The sixth member of the "one carrier, N live values" family, and the last
 * known open one. The reported shape:
 *
 *   for (let i = 0n; i < 2n; i++) {
 *     if (i < 5n) { acc = acc + step; wacc = wacc + acc; }
 *   }
 *
 * with step = 3 the source says wacc = 9; the emitted script computed 3.
 * Silently, in all seven tiers.
 * ===========================================================================
 *
 * ROOT CAUSE — an unstated premise in `appendMergedLocalResults`.
 *
 * When both arms of an `if` reassign K>=2 locals of the enclosing scope,
 * 04-anf-lower appends the same K-result block to BOTH arms
 * (`appendMergedLocalResults`): a first pass copying every merged local to a
 * fresh `__merge$<i>` temp, a second rebinding each local from its temp. Its
 * docstring states the premise the whole reconcile rests on:
 *
 *   "pass 1 always COPIES ... either way stack lowering picks (never rolls)
 *    it, because a local live after the `if` is in `outerProtectedRefs`."
 *
 * The premise only holds when EVERY merged local is live after the `if`.
 * `outerProtectedRefs` is derived from the enclosing scope's last-use map, and
 * a merged local whose last enclosing use IS the `if` binding is absent from
 * it — so pass 1 ROLLED that local instead of copying it and the arm's stack
 * effect stopped being +K.
 *
 * The two arms then disagreed: the then-arm still grew by K (its own
 * arithmetic), the else-arm (source has no `else`; it holds only the appended
 * block) grew by fewer. Phase 3 padded the shortfall with EMPTY pushes, so
 * `elseMatchesThenNResultLayout` saw `null` where it needed the merged name,
 * the N>=2 reconcile declined to fire, and control fell through to the
 * single-slot fallback `this.stackMap.push(bindingName)` — ONE stackMap name
 * registered for K physical results. Every later operand resolved (K-1) slots
 * off, and the names `acc`/`wacc` still pointed at the dead pre-`if` slots.
 *
 * A LOOP is the reliable way to make a merged local dead after the `if`: the
 * body's last-use map ends at the `if` itself, so nothing in the enclosing
 * scope reads it later. But the defect is NOT loop-specific — `NL_DEAD` below
 * reproduces it with no loop at all, by making both merged locals dead after
 * the `if`.
 *
 * THE FIX makes the premise true instead of assuming it: when the arms carry a
 * K>=2 merge block, `lowerIf` protects all K merged locals inside the arms
 * regardless of enclosing-scope liveness. The block reads them in both arms —
 * that read is reconciliation, not a last use. Byte-neutral for every program
 * in which the merged locals were already live after the `if`, which is every
 * program that compiled correctly before.
 *
 * Invisible to every off-chain oracle in the repo, like its five siblings:
 * `TestContract` interprets the AST and the SDK's ANF interpreter keeps locals
 * in an environment map, so both report the SOURCE value. Only the emitted
 * Script disagrees — hence the real `Spend`-backed `ScriptVM` here, plus a
 * stateful deploy/call through `MockProvider` broadcast validation for the
 * fund-loss shape.
 *
 * All EXPECTED values below are derived BY HAND from the source semantics,
 * never from compiler output.
 */

import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract, MockProvider, LocalSigner } from 'runar-sdk';
import { PrivateKey } from '@bsv/sdk';
import type { RunarArtifact } from 'runar-ir-schema';
import { TestSmartContract, expectScriptSuccess, expectScriptFailure } from '../helpers.js';

const PRIV = PrivateKey.fromString('b1'.repeat(32), 16);
const PKH = PRIV.toPublicKey().toHash('hex') as string;

function compileOrThrow(source: string, fileName: string): RunarArtifact {
  const r = compile(source, { fileName });
  if (!r.success || !r.artifact) {
    throw new Error(`compile failed: ${r.diagnostics.map((d) => d.message).join('; ')}`);
  }
  return r.artifact as RunarArtifact;
}

/**
 * A stateless contract whose only job is to assert that the value its body
 * computed equals the constructor-supplied expectation. `verify` succeeds in
 * the real Script VM iff the emitted Script agrees with the source.
 */
function stateless(name: string, body: string): string {
  return `import { SmartContract, assert } from 'runar-lang';

export class ${name} extends SmartContract {
  readonly expected: bigint;
  constructor(expected: bigint) { super(expected); this.expected = expected; }

  public verify(step: bigint): void {
${body}
  }
}
`;
}

/** Run `verify(step)` against the real Script VM with `expected` baked in. */
function runVerify(source: string, fileName: string, expected: bigint, step: bigint) {
  const artifact = compileOrThrow(source, fileName);
  return TestSmartContract.fromArtifact(artifact, [expected]).call('verify', [step]);
}

/** Compile -> deploy -> call with the real `Spend` interpreter behind broadcast. */
async function deployAndCall(
  source: string,
  fileName: string,
  ctorArgs: unknown[],
  method: string,
  args: unknown[],
): Promise<Record<string, unknown>> {
  const artifact = compileOrThrow(source, fileName);
  const signer = new LocalSigner(PRIV.toString());
  const provider = new MockProvider();
  provider.enableBroadcastValidation();
  provider.addUtxo(await signer.getAddress(), {
    txid: 'ee'.repeat(32),
    outputIndex: 0,
    satoshis: 1_000_000,
    script: '76a914' + PKH + '88ac',
  });
  const contract = new RunarContract(artifact, ctorArgs);
  contract.connect(provider, signer);
  await contract.deploy({ satoshis: 1000 });
  await contract.call(method, args, { satoshis: 60_000 });
  return contract.state as Record<string, unknown>;
}

// ---------------------------------------------------------------------------
// The reported shape and its variants
// ---------------------------------------------------------------------------

/** K2: the reported shape. K=2 merged locals, `if` without `else`, in a loop. */
const K2 = stateless('K2', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < 5n) {
        acc = acc + step;
        wacc = wacc + acc;
      }
    }
    assert(wacc === this.expected);`);

/** K2ACC: the same loops, asserting the OTHER merged local. */
const K2ACC = stateless('K2ACC', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < 5n) {
        acc = acc + step;
        wacc = wacc + acc;
      }
    }
    assert(acc === this.expected);`);

/** K2BOTH: both merged locals read after the loop. */
const K2BOTH = stateless('K2BOTH', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < 5n) {
        acc = acc + step;
        wacc = wacc + acc;
      }
    }
    assert(wacc + acc === this.expected);`);

/** K2X3: the reported shape at three iterations. */
const K2X3 = stateless('K2X3', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 3n; i++) {
      if (i < 5n) {
        acc = acc + step;
        wacc = wacc + acc;
      }
    }
    assert(wacc === this.expected);`);

/**
 * K2NOCROSS: K=2 merged locals with NO cross-read between them. Proves the
 * defect is the merge block's arity, not the read-after-reassign ordering that
 * the loop-carried siblings keyed on.
 */
const K2NOCROSS = stateless('K2NOCROSS', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < 5n) {
        acc = acc + step;
        wacc = wacc + step;
      }
    }
    assert(acc + wacc === this.expected);`);

/** K3: three merged locals, chained. */
const K3 = stateless('K3', `    let a: bigint = 0n;
    let b: bigint = 0n;
    let c: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < 5n) {
        a = a + step;
        b = b + a;
        c = c + b;
      }
    }
    assert(c === this.expected);`);

/** HALF: the branch is taken on only some iterations. */
const HALF = stateless('HALF', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 4n; i++) {
      if (i < 2n) {
        acc = acc + step;
        wacc = wacc + acc;
      }
    }
    assert(wacc === this.expected);`);

/** NESTED_IF: the merge block one `if` deeper. */
const NESTED_IF = stateless('NESTED_IF', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < 5n) {
        if (i < 4n) {
          acc = acc + step;
          wacc = wacc + acc;
        }
      }
    }
    assert(wacc === this.expected);`);

/**
 * NL_DEAD: no loop at all. Both merged locals are dead after the `if` (the
 * assert reads only `step`), which is the same premise failure the loop
 * produces — so this reproduces WITHOUT a loop and pins the root cause to the
 * merge block rather than to `lowerLoop`.
 */
const NL_DEAD = stateless('NL_DEAD', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    if (step > 0n) {
      acc = acc + step;
      wacc = wacc + acc;
    }
    assert(step === this.expected);`);

/**
 * IFELSE: both arms rebind, `if` WITH `else`, inside a loop. The else arm now
 * has real work of its own, so its stack effect is no longer purely the
 * appended block — and it is still wrong, because the merged locals are still
 * dead in the enclosing loop body.
 */
const IFELSE = stateless('IFELSE', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < 1n) {
        acc = acc + step;
        wacc = wacc + acc;
      } else {
        acc = acc + 1n;
        wacc = wacc + acc;
      }
    }
    assert(wacc === this.expected);`);

/** K1: the K=1 arity — no merge block is appended; the local is aliased. */
const K1 = stateless('K1', `    let acc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < 5n) {
        acc = acc + step;
      }
    }
    assert(acc === this.expected);`);

/** K1ELSE: K=1 with both arms rebinding. */
const K1ELSE = stateless('K1ELSE', `    let acc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < 1n) { acc = acc + step; } else { acc = acc + 1n; }
    }
    assert(acc === this.expected);`);

/**
 * K1AFTER: K=1 merged local read AFTER the `if` but still inside the loop
 * body. The pre-fix compiler rejected this outright with
 * `Value 'acc' not found on stack` — the loud face of the same premise
 * failure at the K=1 arity, where 04-anf-lower aliases instead of appending a
 * merge block.
 */
const K1AFTER = stateless('K1AFTER', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < 5n) {
        acc = acc + step;
      }
      wacc = wacc + acc;
    }
    assert(wacc === this.expected);`);

// ---------------------------------------------------------------------------
// Accepting controls — byte-correct today and MUST stay accepted
// ---------------------------------------------------------------------------

/** C1: K=2 merged locals, both live after an `if` that is NOT in a loop. */
const C1_NL_LIVE = stateless('C1', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    if (step > 0n) {
      acc = acc + step;
      wacc = wacc + acc;
    }
    assert(wacc + acc === this.expected);`);

/** C2: a loop with a plain cross-read and no `if` (the fixed sibling). */
const C2_PLAIN_LOOP = stateless('C2', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      acc = acc + step;
      wacc = wacc + acc;
    }
    assert(wacc === this.expected);`);

/** C3: an `if` in a loop that reassigns NOTHING — a pure guard. */
const C3_GUARD = stateless('C3', `    let acc: bigint = 0n;
    for (let i: bigint = 0n; i < 3n; i++) {
      if (i < 5n) {
        assert(step > 0n);
      }
      acc = acc + step;
    }
    assert(acc === this.expected);`);

/** ITERVAR: the merged locals read the iteration variable. Also defective. */
const ITERVAR = stateless('ITERVAR', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 3n; i++) {
      if (i > 0n) {
        acc = acc + i;
        wacc = wacc + acc;
      }
    }
    assert(wacc === this.expected);`);

/** NESTED_LOOP: nested loops with a K=2 merge block inside the inner one. */
const NESTED_LOOP = stateless('C5', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      for (let j: bigint = 0n; j < 2n; j++) {
        if (j < 5n) {
          acc = acc + step;
          wacc = wacc + acc;
        }
      }
    }
    assert(wacc === this.expected);`);

// ---------------------------------------------------------------------------

describe('branch-merged locals dead after the if — real Script VM', () => {
  // Hand-derived from the source with step = 3n. Each taken iteration does
  // `acc += 3` then `wacc += acc`, so after n taken iterations acc = 3n and
  // wacc = 3*n*(n+1)/2.
  //   n = 2 => acc  6, wacc  9
  //   n = 3 => acc  9, wacc 18
  //   n = 4 => acc 12, wacc 30
  const STEP = 3n;

  it('K2: the reported shape computes wacc = 9 (3 + 6)', () => {
    expectScriptSuccess(runVerify(K2, 'K2.runar.ts', 9n, STEP));
  });

  it('K2: does NOT compute wacc = 3 (the desynced-slot value)', () => {
    expectScriptFailure(runVerify(K2, 'K2.runar.ts', 3n, STEP));
  });

  it('K2ACC: the other merged local is 6 after two iterations', () => {
    expectScriptSuccess(runVerify(K2ACC, 'K2ACC.runar.ts', 6n, STEP));
  });

  it('K2ACC: does NOT compute acc = 3', () => {
    expectScriptFailure(runVerify(K2ACC, 'K2ACC.runar.ts', 3n, STEP));
  });

  it('K2BOTH: both merged locals read after the loop — 6 + 9 = 15', () => {
    expectScriptSuccess(runVerify(K2BOTH, 'K2BOTH.runar.ts', 15n, STEP));
  });

  it('K2X3: three iterations compute wacc = 18 (3 + 6 + 9)', () => {
    expectScriptSuccess(runVerify(K2X3, 'K2X3.runar.ts', 18n, STEP));
  });

  it('K2NOCROSS: no cross-read — acc = wacc = 6, sum 12', () => {
    expectScriptSuccess(runVerify(K2NOCROSS, 'K2NOCROSS.runar.ts', 12n, STEP));
  });

  it('K2NOCROSS: does NOT compute a sum of 6', () => {
    expectScriptFailure(runVerify(K2NOCROSS, 'K2NOCROSS.runar.ts', 6n, STEP));
  });

  it('K3: three merged locals compute c = 12', () => {
    // iter 0: a 3, b 3, c 3.  iter 1: a 6, b 9, c 12.
    expectScriptSuccess(runVerify(K3, 'K3.runar.ts', 12n, STEP));
  });

  it('K3: does NOT compute c = 0', () => {
    expectScriptFailure(runVerify(K3, 'K3.runar.ts', 0n, STEP));
  });

  it('HALF: the branch taken on 2 of 4 iterations computes wacc = 9', () => {
    expectScriptSuccess(runVerify(HALF, 'HALF.runar.ts', 9n, STEP));
  });

  it('HALF: does NOT compute wacc = 0', () => {
    expectScriptFailure(runVerify(HALF, 'HALF.runar.ts', 0n, STEP));
  });

  it('NESTED_IF: a merge block one if deeper computes wacc = 9', () => {
    expectScriptSuccess(runVerify(NESTED_IF, 'NESTED_IF.runar.ts', 9n, STEP));
  });

  it('NESTED_IF: does NOT compute wacc = 3', () => {
    expectScriptFailure(runVerify(NESTED_IF, 'NESTED_IF.runar.ts', 3n, STEP));
  });

  it('NL_DEAD: no loop, both merged locals dead after the if — step survives', () => {
    // The assert reads only `step`, which the unlocking script supplies as 3.
    expectScriptSuccess(runVerify(NL_DEAD, 'NL_DEAD.runar.ts', 3n, STEP));
  });

  it('NL_DEAD: does NOT read a clobbered step of 0', () => {
    expectScriptFailure(runVerify(NL_DEAD, 'NL_DEAD.runar.ts', 0n, STEP));
  });

  it('IFELSE: both arms rebind, in a loop — wacc = 7', () => {
    // iter 0 (i < 1): acc 0+3 = 3, wacc 0+3 = 3.
    // iter 1 (else):  acc 3+1 = 4, wacc 3+4 = 7.
    expectScriptSuccess(runVerify(IFELSE, 'IFELSE.runar.ts', 7n, STEP));
  });

  it('IFELSE: does NOT compute wacc = 3', () => {
    expectScriptFailure(runVerify(IFELSE, 'IFELSE.runar.ts', 3n, STEP));
  });

  it('K1: the K=1 arity computes acc = 6', () => {
    expectScriptSuccess(runVerify(K1, 'K1.runar.ts', 6n, STEP));
  });

  it('K1ELSE: K=1 with both arms rebinding — acc = 3 + 1 = 4', () => {
    expectScriptSuccess(runVerify(K1ELSE, 'K1ELSE.runar.ts', 4n, STEP));
  });

  it('K1AFTER: K=1 read after the if inside the loop — wacc = 3 + 6 = 9', () => {
    expectScriptSuccess(runVerify(K1AFTER, 'K1AFTER.runar.ts', 9n, STEP));
  });

  it('K1AFTER: does NOT compute wacc = 6', () => {
    expectScriptFailure(runVerify(K1AFTER, 'K1AFTER.runar.ts', 6n, STEP));
  });

  it('C1 (control): K=2 merged locals live after a loop-free if — 3 + 3 = 6', () => {
    expectScriptSuccess(runVerify(C1_NL_LIVE, 'C1.runar.ts', 6n, STEP));
  });

  it('C2 (control): the plain loop cross-read still computes wacc = 9', () => {
    expectScriptSuccess(runVerify(C2_PLAIN_LOOP, 'C2.runar.ts', 9n, STEP));
  });

  it('C3 (control): a pure guard if reassigns nothing — acc = 9', () => {
    expectScriptSuccess(runVerify(C3_GUARD, 'C3.runar.ts', 9n, STEP));
  });

  it('ITERVAR: merged locals over the iteration variable — wacc = 4', () => {
    // i = 0 skipped. i = 1: acc 0+1 = 1, wacc 0+1 = 1.
    //                i = 2: acc 1+2 = 3, wacc 1+3 = 4.
    expectScriptSuccess(runVerify(ITERVAR, 'ITERVAR.runar.ts', 4n, STEP));
  });

  it('ITERVAR: does NOT compute wacc = 1', () => {
    expectScriptFailure(runVerify(ITERVAR, 'ITERVAR.runar.ts', 1n, STEP));
  });

  it('NESTED_LOOP: nested loops around a K=2 merge block — wacc = 30', () => {
    // Four taken iterations: acc 3/6/9/12, wacc 3/9/18/30.
    expectScriptSuccess(runVerify(NESTED_LOOP, 'C5.runar.ts', 30n, STEP));
  });

  it('NESTED_LOOP: does NOT compute wacc = 24', () => {
    expectScriptFailure(runVerify(NESTED_LOOP, 'C5.runar.ts', 24n, STEP));
  });
});

// ---------------------------------------------------------------------------
// Stateful: the same shape leaves a permanently unspendable UTXO
// ---------------------------------------------------------------------------

/**
 * The `loop-carried-locals-k2` construct with the carriers reassigned inside a
 * conditional. Same output topology as its siblings (three mutable properties,
 * three positional values, satoshis == the call amount), so a failure here is
 * the merge block, not the SDK transaction builder.
 */
const KG_ADDOUTPUT = `import { StatefulSmartContract, assert } from 'runar-lang';

export class KGuard extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }

  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < 5n) {
        acc = acc + bidAmount;
        wacc = wacc + acc;
      }
    }
    this.addOutput(bidAmount, this.closed, acc, wacc);
  }
}
`;

/** Control: the same output topology with no conditional around the carriers. */
const KG_ADDOUTPUT_NOGUARD = `import { StatefulSmartContract, assert } from 'runar-lang';

export class KPlain extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }

  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      acc = acc + bidAmount;
      wacc = wacc + acc;
    }
    this.addOutput(bidAmount, this.closed, acc, wacc);
  }
}
`;

const SG_STATEFUL = `import { StatefulSmartContract } from 'runar-lang';

export class SGuard extends StatefulSmartContract {
  total: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.total = seed; }

  public accumulate(step: bigint) {
    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      if (i < 5n) {
        acc = acc + step;
        wacc = wacc + acc;
      }
    }
    this.total = wacc;
  }
}
`;

describe('branch-merged locals dead after the if — stateful spend', () => {
  it('SG: the state continuation the covenant commits to is spendable', async () => {
    // Hand-derived: seed 0 => total 0. accumulate(3) runs the guarded loop, so
    // total := 9.
    const state = await deployAndCall(SG_STATEFUL, 'SGuard.runar.ts', [0n], 'accumulate', [3n]);
    expect(state.total).toBe(9n);
  });

  it('KG: two merged locals behind a guard, fed to addOutput', async () => {
    // Hand-derived with bidAmount = 60000 over two taken iterations:
    //   acc  = 60000, 120000
    //   wacc = 60000, 180000
    const state = await deployAndCall(KG_ADDOUTPUT, 'KGuard.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.closed).toBe(0n);
    expect(state.a).toBe(120_000n);
    expect(state.b).toBe(180_000n);
  });

  it('KG (control): the unguarded twin produces the same values', async () => {
    const state = await deployAndCall(
      KG_ADDOUTPUT_NOGUARD, 'KPlain.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.closed).toBe(0n);
    expect(state.a).toBe(120_000n);
    expect(state.b).toBe(180_000n);
  });
});
