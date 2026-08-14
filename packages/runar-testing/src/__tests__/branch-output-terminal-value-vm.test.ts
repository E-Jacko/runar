/**
 * A conditional arm that emits an output must LEAVE that output on top, and
 * must leave NOTHING ELSE the parent scope can still name.
 *
 * ===========================================================================
 * STATUS 2026-08-05 — FIXED. This file is now GREEN end to end, but the five
 * broken shapes did NOT become spendable: `04-anf-lower.ts` REFUSES them at
 * compile time (`branchOutputRejectionReason`), so their tests assert the
 * diagnostic instead of a successful spend. The originally observed real-VM
 * rejections are kept below as the evidence that made the refusal necessary —
 * every one was reproduced against @bsv/sdk's real `Spend` interpreter via
 * MockProvider broadcast validation.
 *
 *   T1   REJECTED — was: "The top stack element must be truthy after script
 *               evaluation" (the auto-injected continuation-hash assert was
 *               false; the branch committed a script NUMBER where the
 *               serialized output belonged). Now: "continues past its output".
 *   T1D  REJECTED — same, with the merged local DEAD after the `if`. Proves
 *               INV-A is independent of liveness, and is why the fix predicate
 *               cannot be liveness-only.
 *   T2   REJECTED — was: "OP_NUMEQUALVERIFY requires the top stack item to be
 *               truthy" (parent stack desynced by one slot). Now: "reassigns
 *               local variables read after it (na)".
 *   T2C  ACCEPTED — control. Same shape as T2 with the local dead after the
 *               `if`. Still compiles AND still spends.
 *   T3   REJECTED — was: did not even reach the VM; stack lowering aborted
 *               with the internal invariant error "Value 't27' not found on
 *               stack (stack has 4 items: [_codePart, txPreimage, t38, t42])".
 *               Now: a real diagnostic, "continues past its output".
 *   T5   REJECTED — was: "OP_NUM2BIN requires that the size expressed in the
 *               top stack item is large enough to hold the value expressed in
 *               the second-from-top stack item". The arm DOES end with its
 *               output; a property write earlier in the arm is enough. Now:
 *               "assigns contract properties (b) inside the branch".
 *   T6   ACCEPTED — control/baseline. Arm ends with its output and touches
 *               nothing else.
 *   T7   ACCEPTED — control. Arm rebinds a local that is dead after the `if`;
 *               a DIFFERENT pre-`if` local is live across it.
 *
 * The K>=2 merged-locals guard added by 23eb2d2b was on the wrong axis: T3 and
 * T5 have ZERO merged locals and were broken, while T2C and T7 have K=1 merged
 * locals and are fine. Widening that guard to K>=1 would have been
 * simultaneously too wide (kills T2C/T7) and too narrow (misses T3/T5). The
 * shipped predicate keeps K>=2 as one clause of four; the other three are
 * pinned by the ACCEPTED controls here and by the 7-tier negative suite
 * `packages/runar-compiler/src/__tests__/branch-outputs-merged-locals.test.ts`.
 * ===========================================================================
 *
 * Mechanism, as read off the compiled ANF:
 *
 * `lowerIfStatement` registers the if-expression's value as the branch's
 * contribution to the continuation hash (04-anf-lower.ts:956-962), and
 * `appendBranchOutputConcat` returns without appending when an arm has exactly
 * one output ref (04-anf-lower.ts:1068-1070). So "the branch's output bytes"
 * means "whatever the arm's LAST binding is" — an invariant nothing enforces.
 * Stack lowering then makes it lossy rather than merely wrong:
 * `drainBranchPrivateResidue` (05-stack-lower.ts:1015-1042) deletes every arm
 * slot below the top whose name is not a pre-`if` name, so the real serialized
 * output is physically dropped.
 *
 *   INV-A  a result-producing binding AFTER the output intrinsic inside the
 *          arm replaces the output bytes in the continuation hash with a bare
 *          script number. Needs ZERO merged locals — a trailing property write
 *          is enough (T3) — and does not care whether the local is live after
 *          the `if` (T1 vs T1D). Widening the K guard does not close it.
 *   INV-B  an arm that emits an output AND leaves any other slot the parent
 *          can still name — a rebound local live after the `if` (T2), or a
 *          property write anywhere in the arm (T5) — leaves 2+ results while
 *          `lowerIf` registers ONE stackMap name (05-stack-lower.ts:2349),
 *          desyncing the parent stack by one slot from there on.
 *          `drainBranchPrivateResidue` cannot save it: it filters BY NAME and
 *          those names are all in `preIfNames`.
 *
 * Neither is visible off-chain. The SDK's ANF interpreter copies branch
 * bindings back into the parent env (anf-interpreter.ts:461) so it reads the
 * RIGHT value for INV-B, and it SKIPS the auto-injected continuation assert
 * outright (anf-interpreter.ts:500-502, `isAutoInjectedStateCheck`) so INV-A
 * is invisible to it by construction. `TestContract` interprets the AST and is
 * likewise blind. The interpreter and the script DISAGREE in every RED case
 * below — the interpreter accepts and reports correct state. Only the real
 * `Spend` interpreter behind a broadcast sees it, hence this harness.
 */

import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract, MockProvider, LocalSigner } from 'runar-sdk';
import { PrivateKey } from '@bsv/sdk';
import type { RunarArtifact } from 'runar-ir-schema';
import type { ANFBinding } from 'runar-ir-schema';

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
 * A shape the compiler must REFUSE, naming `reason`. Refusal is the fix: the
 * IR has no multi-result `if`, so these branches cannot be represented, and
 * emitting anyway produced the permanently unspendable scripts documented in
 * the header.
 */
function expectRejected(source: string, fileName: string, reason: string): void {
  const r = compile(source, { fileName });
  expect(r.success).toBe(false);
  expect(r.artifact).toBeUndefined();
  const errors = r.diagnostics.filter((d) => d.severity === 'error');
  expect(errors.length).toBeGreaterThan(0);
  const messages = errors.map((d) => d.message).join('\n');
  expect(messages).toContain('Cannot compile conditional that both declares outputs and');
  expect(messages).toContain(reason);
  // Only the one workaround that actually works is advertised.
  expect(messages).toContain('Move the addOutput/addRawOutput/addDataOutput call after the if-statement');
  expect(messages).not.toContain('give each branch its own complete addOutput');
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

const OUTPUT_KINDS = new Set(['add_output', 'add_raw_output', 'add_data_output']);

/** The arms of the first top-level `if` binding in a method body. */
function armsOfFirstIf(
  artifact: RunarArtifact,
  methodName: string,
): { then: ANFBinding[]; else: ANFBinding[] } {
  const anf = (artifact as unknown as { anf?: { methods: Array<{ name: string; body: ANFBinding[] }> } }).anf;
  const method = anf?.methods.find((m) => m.name === methodName);
  if (!method) throw new Error(`no ANF for method '${methodName}'`);
  const ifBinding = method.body.find((b) => b.value.kind === 'if');
  if (!ifBinding) throw new Error(`no if-binding in '${methodName}'`);
  const v = ifBinding.value as unknown as { then: ANFBinding[]; else: ANFBinding[] };
  return { then: v.then, else: v.else };
}

/** The invariant: an arm that emits outputs must END with them (or their concat). */
function armEndsWithItsOutputs(arm: ANFBinding[]): boolean {
  if (!arm.some((b) => OUTPUT_KINDS.has(b.value.kind))) return true;
  const last = arm[arm.length - 1]!;
  if (OUTPUT_KINDS.has(last.value.kind)) return true;
  return last.value.kind === 'call' &&
    (last.value as unknown as { func: string }).func === 'cat';
}

const HEAD = `import { StatefulSmartContract, assert } from 'runar-lang';
import type { ByteString } from 'runar-lang';
`;

/**
 * T1 (INV-A, K=1): each arm emits its output and THEN rebinds the merged local.
 * The alias at 04-anf-lower.ts:980 fires, so `na` is correct after the `if`;
 * the damage is that the if's value — registered as the branch's output bytes —
 * is `na`'s NUMBER, and the arm's real output serialization is dropped by the
 * residue drain. Compiled ANF: the then-arm ends `na = load_const "@ref:t23"`,
 * and the continuation is `hash256(cat(t30, change))` with `t30` = that number.
 */
const T1_REBIND_AFTER_OUTPUT = `${HEAD}
export class T1 extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let na = this.a;
    if (this.a == 0n) {
      this.addOutput(bidAmount, this.closed, bidAmount, this.b);
      na = bidAmount;
    } else {
      this.addOutput(bidAmount, this.closed, this.a, this.b);
      na = this.a;
    }
    assert(na > 0n);
  }
}
`;

/**
 * T1D (INV-A, K=1, merged local DEAD after the `if`): identical to T1 minus the
 * post-`if` read of `na`. Isolates INV-A from any liveness effect — the if's
 * value is still the arm's trailing rebind, so the continuation still commits a
 * number. This is the case that rules out a liveness-only fix predicate.
 */
const T1D_REBIND_AFTER_OUTPUT_DEAD_AFTER = `${HEAD}
export class T1D extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let na = this.a;
    if (this.a == 0n) {
      this.addOutput(bidAmount, this.closed, bidAmount, this.b);
      na = bidAmount;
    } else {
      this.addOutput(bidAmount, this.closed, this.a, this.b);
      na = this.a;
    }
  }
}
`;

/**
 * T2 (INV-B, K=1): each arm rebinds the merged local BEFORE its output, and the
 * local is read after the `if`. Being live after the `if` puts `na` in
 * `outerProtectedRefs`, so `add_output` picks instead of rolling it and the arm
 * ends two deep against one registered stackMap name.
 */
const T2_REBIND_BEFORE_OUTPUT_LIVE_AFTER = `${HEAD}
export class T2 extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let na = this.a;
    if (this.a == 0n) {
      na = bidAmount;
      this.addOutput(bidAmount, this.closed, na, this.b);
    } else {
      na = bidAmount + 1n;
      this.addOutput(bidAmount, this.closed, na, this.b);
    }
    assert(na == bidAmount);
  }
}
`;

/**
 * T2C — control, EXPECTED GREEN. Identical to T2 except the merged local is
 * DEAD after the `if`, so `add_output` consumes the arm's own copy on last use
 * and the arm leaves exactly one result. Pins which K=1 sub-shape is genuinely
 * safe, so a future guard is not written too wide.
 */
const T2C_REBIND_BEFORE_OUTPUT_DEAD_AFTER = `${HEAD}
export class T2C extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let na = this.a;
    if (this.a == 0n) {
      na = bidAmount;
      this.addOutput(bidAmount, this.closed, na, this.b);
    } else {
      na = bidAmount + 1n;
      this.addOutput(bidAmount, this.closed, na, this.b);
    }
  }
}
`;

/**
 * T3 (INV-A with ZERO merged locals): each arm emits a data output and then
 * writes a property. `lowerUpdateProp` renames the physical top to the property
 * name, so the receipt bytes are no longer on top and the drain deletes them.
 * The if's binding `t27` — registered as the branch's data-output ref and later
 * consumed by `cat(t42, t27)` — is then not on the stack under any name, and
 * stack lowering aborts. The `liftBranchUpdateProps` pass cannot rescue this:
 * `allBindingsSideEffectFree` excludes `add_data_output`.
 */
const T3_PROP_WRITE_AFTER_OUTPUT = `${HEAD}
export class T3 extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public pay(payload: ByteString) {
    assert(this.closed == 0n);
    if (this.a == 0n) {
      this.addDataOutput(0n, payload);
      this.b = 1n;
    } else {
      this.addDataOutput(0n, payload);
      this.b = 2n;
    }
    this.a = this.a + 1n;
  }
}
`;

/**
 * T5 (INV-B with ZERO merged locals): the property write comes BEFORE the
 * output, so each arm DOES end with its output intrinsic — the ANF-shape
 * invariant holds — and it is still miscompiled. The property slot survives
 * `drainBranchPrivateResidue` (property names are pre-`if` names), so the arm
 * leaves two results against one registered stackMap name. This is the case
 * that rules out "arm ends with its output" as a sufficient fix predicate.
 */
const T5_PROP_WRITE_BEFORE_OUTPUT = `${HEAD}
export class T5 extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public pay(payload: ByteString) {
    assert(this.closed == 0n);
    if (this.a == 0n) {
      this.b = 1n;
      this.addDataOutput(0n, payload);
    } else {
      this.b = 2n;
      this.addDataOutput(0n, payload);
    }
    this.a = this.a + 1n;
  }
}
`;

/**
 * T6 — control/baseline, EXPECTED GREEN. Same output topology as T1/T2 (one
 * runtime state output emitted from inside the branch, plus change) with the
 * arm touching nothing but its own output. Exonerates the SDK transaction
 * builder: if `packages/runar-sdk/src/contract.ts` could not build this shape,
 * T6 would fail too, and every RED above would be ambiguous.
 */
const T6_BASELINE_OUTPUT_ONLY = `${HEAD}
export class T6 extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    if (this.a == 0n) {
      this.addOutput(bidAmount, this.closed, bidAmount, this.b);
    } else {
      this.addOutput(bidAmount, this.closed, this.a, this.b);
    }
  }
}
`;

/**
 * T7 — control, EXPECTED GREEN. A pre-`if` local IS live across the `if`, but
 * it is not one the arms bind. Pins that INV-B is about names the ARM binds,
 * not about post-`if` liveness generally, so the fix predicate is not written
 * to reject every `if` that has a live local around it.
 */
const T7_UNRELATED_LOCAL_LIVE_AFTER = `${HEAD}
export class T7 extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let guard = this.closed;
    let na = this.a;
    if (this.a == 0n) {
      na = bidAmount;
      this.addOutput(bidAmount, this.closed, na, this.b);
    } else {
      na = bidAmount + 1n;
      this.addOutput(bidAmount, this.closed, na, this.b);
    }
    assert(guard == 0n);
  }
}
`;

describe('branch output must be the arm terminal value — real Script VM', () => {
  // Hand-derived from the source, not from compiler output:
  // ctor seed 0 => closed=0, a=0, b=0. bid(60000n) takes the then-arm.
  //   T1/T1D: addOutput(60000, closed=0, a:=60000, b=0); na=60000.
  //   T2/T2C: na=60000; addOutput(60000, closed=0, a:=60000, b=0).
  //   T3/T5:  data output carries `payload`; b:=1; then a:=0+1=1.
  //   T6:     addOutput(60000, closed=0, a:=60000, b=0).
  //   T7:     as T2, plus an untouched `guard` local live across the `if`.

  it('T1: arm rebinds the merged local AFTER its addOutput (INV-A) [REJECTED]', () => {
    expectRejected(T1_REBIND_AFTER_OUTPUT, 'T1.runar.ts',
      'continues past its output in the then-branch');
  });

  it('T1D: same as T1 with the merged local dead after the if (INV-A) [REJECTED]', () => {
    expectRejected(T1D_REBIND_AFTER_OUTPUT_DEAD_AFTER, 'T1D.runar.ts',
      'continues past its output in the then-branch');
  });

  it('T2: arm rebinds the merged local BEFORE its addOutput, local read after the if (INV-B) [REJECTED]', () => {
    expectRejected(T2_REBIND_BEFORE_OUTPUT_LIVE_AFTER, 'T2.runar.ts',
      'reassigns local variables read after it (na)');
  });

  it('T2C (control): same shape with the local dead after the if is safe [GREEN]', async () => {
    const state = await deployAndCall(
      T2C_REBIND_BEFORE_OUTPUT_DEAD_AFTER, 'T2C.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.closed).toBe(0n);
    expect(state.a).toBe(60_000n);
    expect(state.b).toBe(0n);
  });

  it('T3: arm writes a property AFTER its addDataOutput (INV-A, zero merged locals) [REJECTED]', () => {
    expectRejected(T3_PROP_WRITE_AFTER_OUTPUT, 'T3.runar.ts',
      'continues past its output in the then-branch');
  });

  it('T5: arm writes a property BEFORE its addDataOutput (INV-B, zero merged locals) [REJECTED]', () => {
    expectRejected(T5_PROP_WRITE_BEFORE_OUTPUT, 'T5.runar.ts',
      'assigns contract properties (b) inside the branch');
  });

  it('T6 (control/baseline): arm emits its output and touches nothing else [GREEN]', async () => {
    const state = await deployAndCall(
      T6_BASELINE_OUTPUT_ONLY, 'T6.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.closed).toBe(0n);
    expect(state.a).toBe(60_000n);
    expect(state.b).toBe(0n);
  });

  it('T7 (control): an unrelated pre-if local live across the if is safe [GREEN]', async () => {
    const state = await deployAndCall(
      T7_UNRELATED_LOCAL_LIVE_AFTER, 'T7.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.closed).toBe(0n);
    expect(state.a).toBe(60_000n);
    expect(state.b).toBe(0n);
  });
});

describe('branch output must be the arm terminal value — ANF shape', () => {
  // SDK-independent pin of INV-A: whichever binding the parent registers as
  // the branch's output ref IS the arm's last binding, so an arm that emits
  // outputs must end with them (or the cat-chain over them). Anything that
  // does not is now refused by pass 4, so the property holds vacuously for
  // T1/T1D/T3 — asserted here as "no artifact exists to violate it" — and
  // concretely for every shape that still compiles.
  //
  // INV-B is a stack-slot-count property, not an ANF-shape one, which is
  // exactly why T2 and T5 satisfy this block and are still refused: this block
  // alone was never a sufficient fix predicate.
  it('T1: is refused rather than emitted with a non-terminal output [REJECTED]', () => {
    expect(() => compileOrThrow(T1_REBIND_AFTER_OUTPUT, 'T1.runar.ts')).toThrow(
      /both declares outputs and continues past its output/);
  });

  it('T1D: is refused rather than emitted with a non-terminal output [REJECTED]', () => {
    expect(() => compileOrThrow(T1D_REBIND_AFTER_OUTPUT_DEAD_AFTER, 'T1D.runar.ts')).toThrow(
      /both declares outputs and continues past its output/);
  });

  it('T3: is refused rather than emitted with a non-terminal output [REJECTED]', () => {
    expect(() => compileOrThrow(T3_PROP_WRITE_AFTER_OUTPUT, 'T3.runar.ts')).toThrow(
      /both declares outputs and continues past its output/);
  });

  it('T2C (control): both arms end with their output intrinsic [GREEN]', () => {
    const arms = armsOfFirstIf(
      compileOrThrow(T2C_REBIND_BEFORE_OUTPUT_DEAD_AFTER, 'T2C.runar.ts'), 'bid');
    expect(armEndsWithItsOutputs(arms.then)).toBe(true);
    expect(armEndsWithItsOutputs(arms.else)).toBe(true);
  });

  it('T6 (control): both arms end with their output intrinsic [GREEN]', () => {
    const arms = armsOfFirstIf(compileOrThrow(T6_BASELINE_OUTPUT_ONLY, 'T6.runar.ts'), 'bid');
    expect(armEndsWithItsOutputs(arms.then)).toBe(true);
    expect(armEndsWithItsOutputs(arms.else)).toBe(true);
  });

  it('T7 (control): both arms end with their output intrinsic [GREEN]', () => {
    const arms = armsOfFirstIf(compileOrThrow(T7_UNRELATED_LOCAL_LIVE_AFTER, 'T7.runar.ts'), 'bid');
    expect(armEndsWithItsOutputs(arms.then)).toBe(true);
    expect(armEndsWithItsOutputs(arms.else)).toBe(true);
  });
});
