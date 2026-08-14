/**
 * A bounded loop that REASSIGNS a loop-carried local and then READS it again
 * in the SAME iteration must compile to a Script that computes what the source
 * says.
 *
 * ===========================================================================
 * STATUS 2026-08-06 — FIXED, and unlike the branch-merge family the shape is
 * REPRESENTABLE, so it is now compiled correctly rather than refused. The fix
 * is in the ANF->Stack lowering of all seven tiers
 * (`collectLoopCarriedRebinds` + `lowerLoop`, 05-stack-lower.ts and peers).
 * Reverting it turns 8 of the 14 cases below red. The other 6 — the five
 * accepting controls plus the stateless single-iteration case R1 — stay green
 * either way, and the controls compiled to byte-identical hex before and
 * after: a loop without the shape does not move a single byte.
 *
 * The evidence that made the fix necessary, all reproduced against @bsv/sdk's
 * real `Spend` interpreter:
 *
 *   R2/R3  the stateless script computed `step*N` where the source says
 *          `step*N*(N+1)/2` — no error, just a different spending condition.
 *   R2ACC  the carried local itself read back as `step`, not `step*N`.
 *   S2     stateful: broadcast rejected, "The top stack element must be
 *          truthy after script evaluation" — a permanently unspendable UTXO.
 *   K1/K2  the ledger's `loop-carried-locals-k2` construct proper: two locals
 *          carried across the loop and fed to `addOutput`. K1 shows ONE
 *          iteration is already enough to lose the coins.
 * ===========================================================================
 *
 * Mechanism, read off the ANF + stack lowering (fold-OFF, N = 2):
 *
 *   t2 = load_param step
 *   t3 = acc + t2          <- reads the PRE-LOOP `acc`
 *   acc = @ref:t3          <- rebinds: renames t3's slot to `acc`, so the
 *                             stack now carries TWO slots named `acc`
 *   t4 = wacc + acc        <- last use of `acc` in the body => CONSUMES the
 *                             NEW slot (StackMap.findDepth returns the
 *                             topmost match)
 *   wacc = @ref:t4
 *
 * `lowerLoop` (05-stack-lower.ts) protects outer-scope refs from being
 * consumed mid-loop, but it excluded every name the body itself binds
 * (`deepBodyBindingNames`) — and `acc` is both: an outer ref for the read at
 * t3 and a body binding for the rebind. So the updated `acc` was rolled away
 * into `wacc`, and iteration 2's `OP_4 OP_PICK` resolved `acc` to the dead
 * pre-loop slot. Every iteration therefore added a constant `step` instead of
 * the running total:
 *
 *   N   source wacc = step*N*(N+1)/2   emitted script wacc = step*N
 *   2   9                              6
 *   3   18                             9
 *   4   30                             12          (step = 3)
 *
 * N = 1 is the trap: the two columns AGREE there (step*1 === step*1*2/2), so
 * the stateless `R1` case below passed even on the broken compiler. The
 * shadowed slot was still left behind, so the STATEFUL single-iteration case
 * (`K1`) was rejected by the real `Spend` all the same. One iteration is
 * enough to lose the coins; it is not enough to see it in a number — which is
 * exactly why a value-only oracle would have called this shape covered.
 *
 * This was invisible to every off-chain oracle in the repo: `TestContract`
 * interprets the AST and the SDK's ANF interpreter keeps `acc` in an
 * environment map, so both reported the SOURCE value. Only the emitted Script
 * disagreed — hence the real `Spend`-backed `ScriptVM` here, plus a stateful
 * deploy/call through `MockProvider` broadcast validation to show the
 * fund-loss shape (the continuation the covenant commits to was not the one
 * the SDK builds, so the UTXO was unspendable).
 *
 * Same "one stack carrier asked to hold N live values" root cause as the
 * branch-merge family; see branch-output-terminal-value-vm.test.ts.
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
 * A stateless contract whose only job is to assert that the value its loop
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

/** R2: the reported shape, two iterations. */
const R2 = stateless('R2', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      acc = acc + step;
      wacc = wacc + acc;
    }
    assert(wacc === this.expected);`);

/** R3: three iterations — widens the gap between source and script. */
const R3 = stateless('R3', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 3n; i++) {
      acc = acc + step;
      wacc = wacc + acc;
    }
    assert(wacc === this.expected);`);

/** R1: a SINGLE iteration. Same shape, `i < 1n`. */
const R1 = stateless('R1', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 1n; i++) {
      acc = acc + step;
      wacc = wacc + acc;
    }
    assert(wacc === this.expected);`);

/**
 * R2ACC: the reported shape, asserting the CARRIED local itself after the
 * loop rather than the derived one. Pins that `acc` — not just `wacc` — is
 * wrong on the stack.
 */
const R2ACC = stateless('R2ACC', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      acc = acc + step;
      wacc = wacc + acc;
    }
    assert(acc === this.expected);`);

// ---------------------------------------------------------------------------
// Accepting controls — these are byte-correct today and MUST stay accepted
// ---------------------------------------------------------------------------

/** C1: read BEFORE the reassignment. No intra-iteration read-after-write. */
const C1_READ_BEFORE = stateless('C1', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      wacc = wacc + acc;
      acc = acc + step;
    }
    assert(wacc === this.expected);`);

/** C2: two carried locals, neither reading the other. */
const C2_NO_CROSS_READ = stateless('C2', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      acc = acc + step;
      wacc = wacc + step;
    }
    assert(acc === this.expected && wacc === this.expected);`);

/** C3: the identical two statements OUTSIDE a loop. */
const C3_NO_LOOP = stateless('C3', `    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    acc = acc + step;
    wacc = wacc + acc;
    assert(wacc === this.expected);`);

/** C4: one carried local, self-accumulating only — the shipped `BoundedLoop` shape. */
const C4_SINGLE_CARRIER = stateless('C4', `    let sum: bigint = 0n;
    for (let i: bigint = 0n; i < 3n; i++) {
      sum = sum + step;
    }
    assert(sum === this.expected);`);

// ---------------------------------------------------------------------------

describe('loop-carried local read after reassignment — real Script VM', () => {
  // Hand-derived from the source with step = 3n:
  //   R1  i=0: acc=3,  wacc=0+3=3                                   => wacc 3
  //   R2  i=0: acc=3,  wacc=3;   i=1: acc=6,  wacc=3+6=9            => wacc 9
  //   R3  ... i=2: acc=9, wacc=9+9=18                               => wacc 18
  //   R2ACC same loop as R2                                          => acc  6
  const STEP = 3n;

  it('R1: one iteration computes wacc = 3', () => {
    expectScriptSuccess(runVerify(R1, 'R1.runar.ts', 3n, STEP));
  });

  it('R2: two iterations compute wacc = 9 (3 + 6)', () => {
    expectScriptSuccess(runVerify(R2, 'R2.runar.ts', 9n, STEP));
  });

  it('R2: does NOT compute wacc = 6 (step*N, the pre-loop-binding value)', () => {
    expectScriptFailure(runVerify(R2, 'R2.runar.ts', 6n, STEP));
  });

  it('R3: three iterations compute wacc = 18 (3 + 6 + 9)', () => {
    expectScriptSuccess(runVerify(R3, 'R3.runar.ts', 18n, STEP));
  });

  it('R3: does NOT compute wacc = 9 (step*N)', () => {
    expectScriptFailure(runVerify(R3, 'R3.runar.ts', 9n, STEP));
  });

  it('R2ACC: the carried local itself is 6 after two iterations', () => {
    expectScriptSuccess(runVerify(R2ACC, 'R2ACC.runar.ts', 6n, STEP));
  });

  it('C1 (control): read before reassign — wacc = 0 + 3 = 3', () => {
    expectScriptSuccess(runVerify(C1_READ_BEFORE, 'C1.runar.ts', 3n, STEP));
  });

  it('C2 (control): two carried locals with no cross-read — both 6', () => {
    expectScriptSuccess(runVerify(C2_NO_CROSS_READ, 'C2.runar.ts', 6n, STEP));
  });

  it('C3 (control): the same statements outside a loop — wacc = 3', () => {
    expectScriptSuccess(runVerify(C3_NO_LOOP, 'C3.runar.ts', 3n, STEP));
  });

  it('C4 (control): single self-accumulating carrier — sum = 9', () => {
    expectScriptSuccess(runVerify(C4_SINGLE_CARRIER, 'C4.runar.ts', 9n, STEP));
  });
});

// ---------------------------------------------------------------------------
// Stateful: the same shape leaves a permanently unspendable UTXO
// ---------------------------------------------------------------------------

const S2_STATEFUL = `import { StatefulSmartContract } from 'runar-lang';

export class S2 extends StatefulSmartContract {
  total: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.total = seed; }

  public accumulate(step: bigint) {
    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      acc = acc + step;
      wacc = wacc + acc;
    }
    this.total = wacc;
  }
}
`;

/**
 * The construct `conformance/construct-ledger.json` names
 * `loop-carried-locals-k2`: a bounded loop carrying TWO locals across
 * iterations, then feeding both to `addOutput`. Same output topology as the
 * `T6` control in branch-output-terminal-value-vm.test.ts (three mutable
 * properties, three positional values, satoshis == the call amount), so a
 * failure here is the loop, not the SDK transaction builder.
 */
const K2_ADDOUTPUT_CROSSREAD = `import { StatefulSmartContract, assert } from 'runar-lang';

export class K2Cross extends StatefulSmartContract {
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

/**
 * ONE iteration. Statelessly this shape is value-identical to the source
 * (`step*1 === step*1*2/2`), which is why R1 above passes even on the broken
 * compiler — but the residual shadowed slot still desyncs the frame the state
 * serialization reads, so the stateful spend is rejected. A single iteration
 * is enough to lose the coins; it is not enough to see it in a number.
 */
const K1_ADDOUTPUT_CROSSREAD = `import { StatefulSmartContract, assert } from 'runar-lang';

export class K1Cross extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }

  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let acc: bigint = 0n;
    let wacc: bigint = 0n;
    for (let i: bigint = 0n; i < 1n; i++) {
      acc = acc + bidAmount;
      wacc = wacc + acc;
    }
    this.addOutput(bidAmount, this.closed, acc, wacc);
  }
}
`;

/** Control: the same k=2 addOutput shape with no cross-read. */
const K2_ADDOUTPUT_NO_CROSSREAD = `import { StatefulSmartContract, assert } from 'runar-lang';

export class K2Plain extends StatefulSmartContract {
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
      wacc = wacc + bidAmount;
    }
    this.addOutput(bidAmount, this.closed, acc, wacc);
  }
}
`;

describe('loop-carried local read after reassignment — stateful spend', () => {
  it('S2: the state continuation the covenant commits to is spendable', async () => {
    // Hand-derived: seed 0 => total 0. accumulate(3) runs the R2 loop, so
    // total := 9.
    const state = await deployAndCall(S2_STATEFUL, 'S2.runar.ts', [0n], 'accumulate', [3n]);
    expect(state.total).toBe(9n);
  });

  it('K2: two carried locals with a cross-read, fed to addOutput', async () => {
    // Hand-derived with bidAmount = 60000:
    //   i=0: acc = 0 + 60000 = 60000;      wacc = 0 + 60000 = 60000
    //   i=1: acc = 60000 + 60000 = 120000; wacc = 60000 + 120000 = 180000
    //   addOutput(60000, closed=0, a := acc, b := wacc)
    const state = await deployAndCall(
      K2_ADDOUTPUT_CROSSREAD, 'K2Cross.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.closed).toBe(0n);
    expect(state.a).toBe(120_000n);
    expect(state.b).toBe(180_000n);
  });

  it('K1: a SINGLE iteration is already unspendable', async () => {
    // Hand-derived with bidAmount = 60000:
    //   i=0: acc = 0 + 60000 = 60000; wacc = 0 + 60000 = 60000
    const state = await deployAndCall(
      K1_ADDOUTPUT_CROSSREAD, 'K1Cross.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.closed).toBe(0n);
    expect(state.a).toBe(60_000n);
    expect(state.b).toBe(60_000n);
  });

  it('K2 (control): two carried locals with no cross-read, fed to addOutput', async () => {
    // Hand-derived: both accumulate bidAmount twice => 120000 each.
    const state = await deployAndCall(
      K2_ADDOUTPUT_NO_CROSSREAD, 'K2Plain.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.closed).toBe(0n);
    expect(state.a).toBe(120_000n);
    expect(state.b).toBe(120_000n);
  });
});
