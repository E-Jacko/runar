/**
 * A loop-carried local that is REASSIGNED and then READ AGAIN in the body of a
 * NESTED loop must compile to a Script that computes what the source says.
 *
 * ===========================================================================
 * The nested sibling of loop-carried-local-read-after-reassign-vm.test.ts.
 * That file fixed the SINGLE-level shape; this one is the variant its
 * predicate missed, and it was wrong both BEFORE and AFTER that fix:
 *
 *   for (let i = 0n; i < 2n; i++) {
 *     for (let j = 0n; j < 2n; j++) { acc = acc + step; wacc = wacc + acc; }
 *   }
 *
 * with step = 3 the source says wacc = 30; the emitted script computed 24.
 * Silently, in all seven tiers.
 * ===========================================================================
 *
 * Why the single-level predicate missed it. `collectLoopCarriedRebinds`
 * (05-stack-lower.ts and its six peers) protects a name the loop body REBINDS
 * and then READS AGAIN in the same iteration, keying on the body's TOP-LEVEL
 * binding names. At the OUTER loop's level the body has exactly one top-level
 * binding — the inner loop itself:
 *
 *   t6 = loop i (count 2)
 *     t5 = loop j (count 2)
 *       t2 = load_param step
 *       t3 = acc + t2
 *       acc = @ref:t3
 *       t4 = wacc + acc
 *       wacc = @ref:t4
 *
 * so `acc` is bound at no top-level index of the outer body: it is neither an
 * outer ref (`deepBodyBindingNames` excludes it precisely because the body
 * binds it, deeply) nor a top-level carried rebind. It fell through both, so
 * the outer loop never marked it live, and the INNER loop's final iteration
 * consumed it — `usedAfterLoop` asks the enclosing scope, and the enclosing
 * scope had not been told either. Every outer iteration therefore restarted
 * `acc` from the slot the previous outer iteration had left behind.
 *
 * The fix flattens nested loop bodies into the sequence the predicate scans,
 * so the outer level sees the same read/rebind/read ordering the inner level
 * already saw. A body with no nested loop flattens to itself, which is what
 * makes the change byte-neutral for every loop already in the tree.
 *
 * A sibling shape fails LOUDLY rather than silently — `SIB` below — because
 * the cross-read sits between the inner loop and the end of the outer body,
 * where nothing had put `acc` back on the stack at all.
 *
 * Invisible to every off-chain oracle in the repo for the same reason as the
 * single-level case: `TestContract` interprets the AST and the SDK's ANF
 * interpreter keeps `acc` in an environment map, so both report the SOURCE
 * value. Only the emitted Script disagrees — hence the real `Spend`-backed
 * `ScriptVM` here, plus a stateful deploy/call through `MockProvider`
 * broadcast validation for the fund-loss shape.
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
 * A stateless contract whose only job is to assert that the value its loops
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

/** The reported shape at `outer` x `inner` iterations, asserting `target`. */
function nested(name: string, outer: number, inner: number, target: 'acc' | 'wacc'): string {
  return stateless(name, `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < ${outer}n; i++) {
      for (let j: bigint = 0n; j < ${inner}n; j++) {
        acc = acc + step;
        wacc = wacc + acc;
      }
    }
    assert(${target} === this.expected);`);
}

// ---------------------------------------------------------------------------
// The reported shape and its variants
// ---------------------------------------------------------------------------

/** N22: the reported shape, 2 outer x 2 inner. */
const N22 = nested('N22', 2, 2, 'wacc');

/** N22ACC: the same loops, asserting the CARRIED local itself. */
const N22ACC = nested('N22ACC', 2, 2, 'acc');

/** N23 / N32: same total iteration count, different nesting split. */
const N23 = nested('N23', 2, 3, 'wacc');
const N32 = nested('N32', 3, 2, 'wacc');

/** N222: three levels deep. */
const N222 = stateless('N222', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      for (let j: bigint = 0n; j < 2n; j++) {
        for (let k: bigint = 0n; k < 2n; k++) {
          acc = acc + step;
          wacc = wacc + acc;
        }
      }
    }
    assert(wacc === this.expected);`);

/**
 * SIB: the LOUD sibling — the cross-read sits after the inner loop rather
 * than inside it. Same root cause; it threw
 * "Value 'acc' not found on stack" out of stack lowering instead of
 * miscompiling, so it never reached a script.
 */
const SIB = stateless('SIB', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      for (let j: bigint = 0n; j < 2n; j++) {
        acc = acc + step;
      }
      wacc = wacc + acc;
    }
    assert(wacc === this.expected);`);

// ---------------------------------------------------------------------------
// Accepting controls — byte-correct today and MUST stay accepted
// ---------------------------------------------------------------------------

/** C1: nested loops, ONE self-accumulating carrier, no cross-read. */
const C1_SINGLE_CARRIER = stateless('C1', `    let sum: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      for (let j: bigint = 0n; j < 3n; j++) {
        sum = sum + step;
      }
    }
    assert(sum === this.expected);`);

/** C2: nested loops, two carriers, neither reading the other. */
const C2_NO_CROSS_READ = stateless('C2', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      for (let j: bigint = 0n; j < 2n; j++) {
        acc = acc + step;
        wacc = wacc + step;
      }
    }
    assert(acc === this.expected && wacc === this.expected);`);

/** C3: nested loops reading BOTH iteration variables. */
const C3_ITER_VARS = stateless('C3', `    let sum: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      for (let j: bigint = 0n; j < 2n; j++) {
        sum = sum + i + j;
      }
    }
    assert(sum === this.expected);`);

/** C4: read BEFORE the reassignment, nested. No intra-iteration read-after-write. */
const C4_READ_BEFORE = stateless('C4', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      for (let j: bigint = 0n; j < 2n; j++) {
        wacc = wacc + acc;
        acc = acc + step;
      }
    }
    assert(wacc === this.expected);`);

/** C5: the SINGLE-level cross-read — already fixed; must stay fixed. */
const C5_SINGLE_LEVEL = stateless('C5', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      acc = acc + step;
      wacc = wacc + acc;
    }
    assert(wacc === this.expected);`);

// ---------------------------------------------------------------------------

describe('nested loop-carried local read after reassignment — real Script VM', () => {
  // Hand-derived from the source with step = 3n. The inner body runs
  // outer*inner times in total; per run `acc += 3` then `wacc += acc`, so
  // after n runs acc = 3n and wacc = 3*n*(n+1)/2.
  //   N22   n = 4  => acc 12,  wacc 3*4*5/2  = 30
  //   N23   n = 6  => acc 18,  wacc 3*6*7/2  = 63
  //   N32   n = 6  => acc 18,  wacc           = 63
  //   N222  n = 8  => acc 24,  wacc 3*8*9/2  = 108
  const STEP = 3n;

  it('N22: 2x2 computes wacc = 30 (3 + 9 + 18 + 30 running total)', () => {
    expectScriptSuccess(runVerify(N22, 'N22.runar.ts', 30n, STEP));
  });

  it('N22: does NOT compute wacc = 24 (the dead-slot value)', () => {
    expectScriptFailure(runVerify(N22, 'N22.runar.ts', 24n, STEP));
  });

  it('N22ACC: the carried local itself is 12 after 4 inner iterations', () => {
    expectScriptSuccess(runVerify(N22ACC, 'N22ACC.runar.ts', 12n, STEP));
  });

  it('N22ACC: does NOT compute acc = 6', () => {
    expectScriptFailure(runVerify(N22ACC, 'N22ACC.runar.ts', 6n, STEP));
  });

  it('N23: 2x3 computes wacc = 63', () => {
    expectScriptSuccess(runVerify(N23, 'N23.runar.ts', 63n, STEP));
  });

  it('N32: 3x2 computes wacc = 63 — same total, different split', () => {
    expectScriptSuccess(runVerify(N32, 'N32.runar.ts', 63n, STEP));
  });

  it('N222: three levels deep compute wacc = 108', () => {
    expectScriptSuccess(runVerify(N222, 'N222.runar.ts', 108n, STEP));
  });

  it('SIB: the loud sibling compiles and computes wacc = 18', () => {
    // Hand-derived: the inner loop leaves acc = 6 after outer iteration 0 and
    // acc = 12 after outer iteration 1, so wacc = 0 + 6 + 12 = 18.
    expectScriptSuccess(runVerify(SIB, 'SIB.runar.ts', 18n, STEP));
  });

  it('SIB: does NOT compute wacc = 12', () => {
    expectScriptFailure(runVerify(SIB, 'SIB.runar.ts', 12n, STEP));
  });

  it('C1 (control): nested single carrier — sum = 6 * 3 = 18', () => {
    expectScriptSuccess(runVerify(C1_SINGLE_CARRIER, 'C1.runar.ts', 18n, STEP));
  });

  it('C2 (control): nested, two carriers, no cross-read — both 12', () => {
    expectScriptSuccess(runVerify(C2_NO_CROSS_READ, 'C2.runar.ts', 12n, STEP));
  });

  it('C3 (control): nested loops over both iteration variables — sum = 4', () => {
    // (0+0) + (0+1) + (1+0) + (1+1) = 4
    expectScriptSuccess(runVerify(C3_ITER_VARS, 'C3.runar.ts', 4n, STEP));
  });

  it('C4 (control): nested read-before-reassign — wacc = 0+3+6+9 = 18', () => {
    // acc is 0, 3, 6, 9 at the four reads; wacc accumulates those.
    expectScriptSuccess(runVerify(C4_READ_BEFORE, 'C4.runar.ts', 18n, STEP));
  });

  it('C5 (control): the single-level cross-read still computes wacc = 9', () => {
    expectScriptSuccess(runVerify(C5_SINGLE_LEVEL, 'C5.runar.ts', 9n, STEP));
  });
});

// ---------------------------------------------------------------------------
// Stateful: the same shape leaves a permanently unspendable UTXO
// ---------------------------------------------------------------------------

/**
 * The `loop-carried-locals-k2` construct at nesting depth 2: two locals
 * carried across nested bounded loops, then fed to `addOutput`. Same output
 * topology as the `K2` case in loop-carried-local-read-after-reassign-vm.ts
 * (three mutable properties, three positional values, satoshis == the call
 * amount), so a failure here is the loops, not the SDK transaction builder.
 */
const K22_ADDOUTPUT_CROSSREAD = `import { StatefulSmartContract, assert } from 'runar-lang';

export class K22Cross extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }

  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      for (let j: bigint = 0n; j < 2n; j++) {
        acc = acc + bidAmount;
        wacc = wacc + acc;
      }
    }
    this.addOutput(bidAmount, this.closed, acc, wacc);
  }
}
`;

/** Control: the same nested addOutput shape with no cross-read. */
const K22_ADDOUTPUT_NO_CROSSREAD = `import { StatefulSmartContract, assert } from 'runar-lang';

export class K22Plain extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }

  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      for (let j: bigint = 0n; j < 2n; j++) {
        acc = acc + bidAmount;
        wacc = wacc + bidAmount;
      }
    }
    this.addOutput(bidAmount, this.closed, acc, wacc);
  }
}
`;

const S22_STATEFUL = `import { StatefulSmartContract } from 'runar-lang';

export class S22 extends StatefulSmartContract {
  total: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.total = seed; }

  public accumulate(step: bigint) {
    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      for (let j: bigint = 0n; j < 2n; j++) {
        acc = acc + step;
        wacc = wacc + acc;
      }
    }
    this.total = wacc;
  }
}
`;

describe('nested loop-carried local read after reassignment — stateful spend', () => {
  it('S22: the state continuation the covenant commits to is spendable', async () => {
    // Hand-derived: seed 0 => total 0. accumulate(3) runs the N22 loops, so
    // total := 30.
    const state = await deployAndCall(S22_STATEFUL, 'S22.runar.ts', [0n], 'accumulate', [3n]);
    expect(state.total).toBe(30n);
  });

  it('K22: two carried locals with a nested cross-read, fed to addOutput', async () => {
    // Hand-derived with bidAmount = 60000, four inner iterations:
    //   acc  = 60000, 120000, 180000, 240000
    //   wacc = 60000, 180000, 360000, 600000
    const state = await deployAndCall(
      K22_ADDOUTPUT_CROSSREAD, 'K22Cross.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.closed).toBe(0n);
    expect(state.a).toBe(240_000n);
    expect(state.b).toBe(600_000n);
  });

  it('K22 (control): nested carried locals with no cross-read, fed to addOutput', async () => {
    // Hand-derived: both accumulate bidAmount four times => 240000 each.
    const state = await deployAndCall(
      K22_ADDOUTPUT_NO_CROSSREAD, 'K22Plain.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.closed).toBe(0n);
    expect(state.a).toBe(240_000n);
    expect(state.b).toBe(240_000n);
  });
});
