/**
 * Spend-oracle fuzzer (testing-gap remediation Phase E3, plan §3 "E3.
 * Spend-oracle fuzzer — first-class job", design principle P8, reviewer
 * point #6).
 *
 * WHY THIS EXISTS — HORIZONTAL vs ABSOLUTE
 * ----------------------------------------
 * `anf-differential.ts`, `ir-differential.ts` and `tri-modal-differential.ts`
 * compare TIER AGAINST TIER. Seven compilers that share one bug agree with each
 * other perfectly, and every one of those fuzzers stays green. Both 2026-08
 * fund-safety bugs were of exactly that kind (all 7 compilers / all 7 SDKs).
 * Horizontal parity fuzz is necessary and is NOT fund-safety-complete on its
 * own.
 *
 * `execute-differential.ts` (`--execute`) already adds an ABSOLUTE oracle — the
 * real `@bsv/sdk` engine — but only for STATELESS fragments run against a
 * synthetic tx context, and only on accept/reject. Two things stay out of
 * reach: the full transaction context (BIP-143 sighash, `OP_CODESEPARATOR`,
 * `checkPreimage`) and the state CONTINUATION's VALUE.
 *
 * This mode closes both. Per generated case:
 *
 *   generate (construct-biased, see `spend-shapes.ts`)
 *     -> compile with the TS compiler, constant-folding ON (shipped default)
 *     -> real deploy tx + real call tx through the SDK with a real `LocalSigner`
 *     -> `MockProvider` replays every broadcast through real `@bsv/sdk` `Spend`
 *        (validation is default-on since Phase A1) and this harness ALSO
 *        re-validates the contract input itself
 *     -> decode the post-state out of the BROADCAST CALL TRANSACTION'S BYTES
 *        and compare it to the generator's own model
 *
 * It FAILS on any of:
 *   1. `reject-when-accept-intended`  — script rejected, generator said accept
 *   2. `accept-when-reject-intended`  — script accepted, generator said reject
 *   3. `interpreter-vs-spend`         — ANF interpreter and Spend disagree
 *   4. `deploy-state-mismatch`        — deployed state section != model bytes
 *   5. `expected-state-mismatch`      — continuation state section != model bytes
 *   6. `metamorphic-divergence`       — a semantics-preserving rewrite (renamed
 *                                       locals / swapped pure `if/else` arms)
 *                                       changed the verdict or the state
 *                                       (Phase E4, `--metamorphic`)
 *   7. `vacuous-validation`           — nothing actually reached the engine
 *
 * HOW THE STATE EXPECTATION AVOIDS BEING POISONED
 * -----------------------------------------------
 * This is the subtle part, and it is the reason the job exists.
 *
 * The SDK computes the next state by running the artifact's ANF through
 * `anf-interpreter.ts` (`computeNewStateAndDataOutputs`, called from
 * `RunarContract.prepareCall`). The covenant that validates the spend was
 * compiled from THE SAME ANF. A branch-merged-locals miscompile in ANF lowering
 * therefore corrupts both sides identically: the SDK writes the stale value,
 * the on-chain `hash256(outputs)` check is satisfied by that stale value, `Spend`
 * accepts, and `contract.state` reports the stale value back. Any expectation
 * read out of `contract.state`, out of `extractStateFromScript`'s round trip, or
 * out of a second run of the pipeline is derived from the bug and confirms it.
 *
 * So the expectation is NOT derived from the pipeline at all:
 *
 *   - `spend-shapes.ts` DECIDES the post-state when it picks the values — the
 *     rendered source is generated FROM that decision, not the other way round.
 *     The model is ~40 lines of plain TypeScript over the generator's own arm
 *     bookkeeping (which arm the chosen `p0` takes, which locals that arm
 *     rebinds, what value it rebinds them to).
 *   - The comparison is done in BYTES, against a SECOND, independent
 *     implementation of the state-section wire format
 *     (`encodeStateSectionHex`), written from the format documentation rather
 *     than imported from `runar-sdk`'s `serializeState`. PALMER-2 moved all
 *     seven SDK encoders AND all seven SDK decoders in one commit; every
 *     round-trip test stayed green. A pin that shares either side of that pair
 *     is worth nothing.
 *
 * Where a shape cannot be modelled independently, it is simply NOT modelled —
 * `expectedState: null` (today: every `intent: 'reject'` case, which has no
 * continuation). No self-confirming check is ever emitted.
 *
 * DETERMINISM
 * -----------
 * `--seed` reproduces the corpus exactly (`generateShapes` is a pure function
 * of `(seed, count)`), and the seed is printed on every failure and in the
 * summary so any finding is replayable with
 * `--spend-oracle --seed <n> --num <count>`.
 */

import { mkdirSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import { LockingScript, PrivateKey, Spend, Transaction } from '@bsv/sdk';

import { compile } from '../../packages/runar-compiler/src/index.js';
import {
  LocalSigner,
  MockProvider,
  RunarContract,
  buildP2PKHScript,
} from '../../packages/runar-sdk/src/index.js';
import { TestContract } from '../../packages/runar-testing/src/test-contract.js';

import {
  encodeStateSectionHex,
  generateShapes,
  type GeneratedShape,
  type ShapeTag,
  type ShapeValue,
} from './spend-shapes.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);
const ROOT = resolve(__dirname, '../..');

// ---------------------------------------------------------------------------
// Fixed signing key (deterministic; funds the deploy and signs the call)
// ---------------------------------------------------------------------------

const PRIV = PrivateKey.fromString('b1'.repeat(32), 16);
const PUB = PRIV.toPublicKey().encode(true, 'hex') as string;

// ---------------------------------------------------------------------------
// Failure taxonomy
// ---------------------------------------------------------------------------

export type SpendOracleFailureKind =
  | 'compile-error'
  | 'deploy-state-mismatch'
  | 'reject-when-accept-intended'
  | 'accept-when-reject-intended'
  | 'interpreter-vs-spend'
  | 'expected-state-mismatch'
  | 'metamorphic-divergence'
  | 'vacuous-validation'
  | 'harness-error';

export interface SpendOracleFinding {
  seed: number;
  index: number;
  id: string;
  family: string;
  kind: SpendOracleFailureKind;
  message: string;
  tags: ShapeTag[];
  source: string;
  constructorArgs: string[];
  methodArgs: string[];
  intent: 'accept' | 'reject';
  expectedStateHex?: string;
  actualStateTail?: string;
  expectedState?: Record<string, string>;
  spendAccepted?: boolean;
  interpreterAccepted?: boolean;
  engineError?: string;
  deployLockingHex?: string;
  continuationLockingHex?: string;
}

// ---------------------------------------------------------------------------
// One case
// ---------------------------------------------------------------------------

interface CaseOutcome {
  ok: boolean;
  findings: (Omit<
    SpendOracleFinding,
    'seed' | 'index' | 'id' | 'family' | 'tags' | 'source' | 'constructorArgs' | 'methodArgs' | 'intent'
  > & {
    /** Set only for a metamorphic VARIANT, whose source differs from the base. */
    source?: string;
  })[];
  spendAccepted: boolean;
  /** Inputs actually replayed through `Spend.validate()` by the provider. */
  validatedInputs: number;
}

function jsonValue(v: ShapeValue): string {
  return typeof v === 'bigint' ? `${v}n` : typeof v === 'boolean' ? String(v) : `0x${v}`;
}

/**
 * Re-validate `tx`'s input `inputIdx` against `sourceTx`'s output on the real
 * `@bsv/sdk` `Spend` engine. Mirrors `runStatefulSpend`'s `validateSpend` in
 * `packages/runar-testing/src/oracle/real-crypto-execution.ts`, reimplemented
 * here so this harness has its OWN engine call: `MockProvider`'s broadcast
 * validation is a different code path and could in principle skip an input
 * whose outpoint it never registered.
 */
function validateContractInput(tx: Transaction, sourceTx: Transaction): boolean {
  const input = tx.inputs[0]!;
  const sourceOutput = sourceTx.outputs[0]!;
  const spend = new Spend({
    sourceTXID: input.sourceTXID!,
    sourceOutputIndex: input.sourceOutputIndex,
    sourceSatoshis: sourceOutput.satoshis!,
    lockingScript: sourceOutput.lockingScript,
    transactionVersion: tx.version,
    otherInputs: tx.inputs.slice(1).map((inp, idx) => ({
      inputIndex: idx + 1,
      sourceOutputIndex: inp.sourceOutputIndex,
      sourceTXID: inp.sourceTXID!,
      sequence: inp.sequence,
      unlockingScript: undefined as never,
      sourceSatoshis: 0,
      lockingScript: LockingScript.fromHex(''),
    })),
    outputs: tx.outputs.map((o) => ({
      lockingScript: o.lockingScript,
      satoshis: o.satoshis ?? 0,
    })),
    unlockingScript: input.unlockingScript!,
    inputIndex: 0,
    inputSequence: input.sequence ?? 0xffffffff,
    lockTime: tx.lockTime,
  });
  return spend.validate();
}

/** Interpreter (source-semantics) verdict for the same spend. */
function interpreterVerdict(shape: GeneratedShape, source: string): boolean {
  try {
    const ctor: Record<string, bigint | boolean | string> = {};
    for (const s of shape.slots) ctor[s.name] = s.value;
    for (const f of shape.fields) ctor[f.name] = f.value;
    const tc = TestContract.fromSource(source, ctor, shape.fileName);
    const named: Record<string, unknown> = {};
    shape.methodParams.forEach((p, i) => {
      named[p.name] = shape.methodArgs[i];
    });
    return tc.call(shape.method, named).success;
  } catch {
    return false;
  }
}

/**
 * Everything one (shape, source) pair produces. `source` is a parameter, not
 * `shape.source`, so a Phase-E4 metamorphic variant runs through the exact same
 * pipeline and assertions as the original.
 */
interface Evaluation {
  spendAccepted: boolean;
  /** `true`/`false` when the model was checked, `null` when it did not apply. */
  stateMatchesModel: boolean | null;
  validatedInputs: number;
  findings: CaseOutcome['findings'];
}

async function evaluate(shape: GeneratedShape, source: string): Promise<Evaluation> {
  const findings: CaseOutcome['findings'] = [];
  const push = (
    kind: SpendOracleFailureKind,
    message: string,
    extra: Partial<SpendOracleFinding> = {},
  ): void => {
    findings.push({ kind, message, ...extra });
  };

  // 1. Compile — constant folding ON (the shipped default).
  const compiled = compile(source, { fileName: shape.fileName });
  if (!compiled.success || !compiled.artifact) {
    const errs = compiled.diagnostics
      .filter((d) => d.severity === 'error')
      .map((d) => d.message)
      .join('; ');
    push('compile-error', `compile failed: ${errs}`);
    return { spendAccepted: false, stateMatchesModel: null, validatedInputs: 0, findings };
  }
  const artifact = compiled.artifact;

  const signer = new LocalSigner(PRIV.toString());
  const provider = new MockProvider(); // broadcast validation is default-ON
  const address = await signer.getAddress();
  provider.addUtxo(address, {
    txid: 'ee'.repeat(32),
    outputIndex: 0,
    satoshis: 1_000_000,
    script: buildP2PKHScript(PUB),
  });

  const contract = new RunarContract(artifact, shape.constructorArgs as unknown[]);
  contract.connect(provider, signer);

  // 2. Deploy. The state section of the DEPLOYED locking script is written by
  //    the SDK's serializeState; pin it against the independent encoder before
  //    anything else, so a framing regression (PALMER-2) is reported as what it
  //    is rather than as a downstream spend rejection.
  let deployTx: Transaction;
  try {
    await contract.deploy({ satoshis: 50_000 });
    deployTx = Transaction.fromHex(provider.getBroadcastedTxs()[0]!);
  } catch (e) {
    push('harness-error', `deploy failed: ${e instanceof Error ? e.message : String(e)}`);
    return { spendAccepted: false, stateMatchesModel: null, validatedInputs: 0, findings };
  }

  const deployLockingHex = deployTx.outputs[0]!.lockingScript.toHex();
  const initialValues: Record<string, ShapeValue> = {};
  for (const f of shape.fields) initialValues[f.name] = f.value;
  const deployTail = '6a' + encodeStateSectionHex(shape.fields, initialValues);
  if (!deployLockingHex.endsWith(deployTail)) {
    push(
      'deploy-state-mismatch',
      `deployed locking script does not end with the independently encoded state section`,
      {
        expectedStateHex: deployTail,
        actualStateTail: deployLockingHex.slice(-Math.max(deployTail.length, 64)),
        deployLockingHex,
      },
    );
  }

  // 3. Call. `dryRun: true` makes a script rejection of the PRIMARY contract
  //    input report itself with a message unique to that path (see
  //    `dryRunContractInput` in runar-sdk/contract.ts), so a reject can be
  //    attributed to the on-chain guard rather than to an SDK error that never
  //    reached the engine.
  let spendAccepted = false;
  let engineError: string | undefined;
  let callTx: Transaction | undefined;
  let reachedEngine = false;
  try {
    await contract.call(shape.method, shape.methodArgs as unknown[], { dryRun: true });
    callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);
    reachedEngine = true;
    spendAccepted = validateContractInput(callTx, deployTx);
  } catch (e) {
    engineError = e instanceof Error ? e.message : String(e);
    spendAccepted = false;
    if (
      engineError.includes('local pre-broadcast dry-run rejected the primary contract input') ||
      (/\(C8\): input 0: /.test(engineError) && !engineError.includes('underfunded:'))
    ) {
      reachedEngine = true;
    }
  }

  const validatedInputs = provider.getValidationStats().validated;

  // 4. Verdict vs the generator's intent.
  if (shape.intent === 'accept' && !spendAccepted) {
    push('reject-when-accept-intended', `real Spend rejected a spend the generator intended to accept`, {
      spendAccepted,
      engineError,
      deployLockingHex,
    });
  }
  if (shape.intent === 'reject' && spendAccepted) {
    push('accept-when-reject-intended', `real Spend accepted a spend the generator intended to reject`, {
      spendAccepted,
      deployLockingHex,
    });
  }
  if (shape.intent === 'reject' && !spendAccepted && !reachedEngine) {
    // A rejection that never reached the engine proves nothing about the guard.
    push('vacuous-validation', `reject-intent case failed before the script guard ran: ${engineError}`, {
      engineError,
    });
  }

  // 5. Interpreter (source semantics, AST-level — NOT downstream of ANF
  //    lowering) vs the real engine.
  const interpreterAccepted = interpreterVerdict(shape, source);
  if (interpreterAccepted !== spendAccepted) {
    push('interpreter-vs-spend', `ANF interpreter and real Spend disagree`, {
      interpreterAccepted,
      spendAccepted,
      engineError,
    });
  }

  // 6. THE VALUE PIN. Compare the continuation output's state section, as it
  //    appears in the BROADCAST TRANSACTION'S BYTES, against the generator's
  //    own model encoded by the independent codec.
  let stateMatchesModel: boolean | null = null;
  if (shape.expectedState && spendAccepted && callTx) {
    const contHex = callTx.outputs[0]!.lockingScript.toHex();
    const expectedTail = '6a' + encodeStateSectionHex(shape.fields, shape.expectedState);
    stateMatchesModel = contHex.endsWith(expectedTail);
    if (!stateMatchesModel) {
      push(
        'expected-state-mismatch',
        `continuation state section != the generator's independent model ` +
          `(the spend was ACCEPTED — this is the quiet-corruption face)`,
        {
          spendAccepted,
          expectedStateHex: expectedTail,
          actualStateTail: contHex.slice(-Math.max(expectedTail.length, 64)),
          expectedState: Object.fromEntries(
            Object.entries(shape.expectedState).map(([k, v]) => [k, jsonValue(v)]),
          ),
          continuationLockingHex: contHex,
        },
      );
    }
  }

  // 7. Non-vacuity: an accepted case must have run real script.
  if (shape.intent === 'accept' && spendAccepted && validatedInputs === 0) {
    push('vacuous-validation', `no input was replayed through Spend.validate() — the pass is vacuous`);
  }

  return { spendAccepted, stateMatchesModel, validatedInputs, findings };
}

/**
 * One corpus case: the generated contract, plus (Phase E4, when enabled) its
 * semantics-preserving metamorphic variants. A variant that produces a
 * different verdict or a different model verdict is a miscompile that depends
 * on something the source semantics do not — a local's NAME, or which arm of a
 * pure `if/else` a value came from.
 */
async function runCase(shape: GeneratedShape, metamorphic: boolean): Promise<CaseOutcome> {
  const base = await evaluate(shape, shape.source);
  const findings = [...base.findings];
  let validatedInputs = base.validatedInputs;

  if (metamorphic && base.findings.length === 0) {
    const variants: [string, string][] = [['rename-locals', shape.variants.renameLocals]];
    if (shape.variants.swapArms !== null) variants.push(['swap-arms', shape.variants.swapArms]);
    for (const [name, src] of variants) {
      const v = await evaluate(shape, src);
      validatedInputs += v.validatedInputs;
      if (v.spendAccepted !== base.spendAccepted || v.stateMatchesModel !== base.stateMatchesModel) {
        findings.push({
          kind: 'metamorphic-divergence',
          message:
            `metamorphic transform '${name}' changed the outcome: ` +
            `base(accepted=${base.spendAccepted}, stateMatchesModel=${base.stateMatchesModel}) ` +
            `!= variant(accepted=${v.spendAccepted}, stateMatchesModel=${v.stateMatchesModel})`,
          source: src,
          spendAccepted: v.spendAccepted,
        });
      }
      // A variant that fails an assertion the base passed is itself a finding.
      for (const f of v.findings) findings.push({ ...f, source: src });
    }
  }

  return { ok: findings.length === 0, findings, spendAccepted: base.spendAccepted, validatedInputs };
}

// ---------------------------------------------------------------------------
// Findings persistence
// ---------------------------------------------------------------------------

function saveFinding(dir: string, f: SpendOracleFinding): string {
  const out = join(dir, `${f.seed}-${String(f.index).padStart(4, '0')}-${f.kind}`);
  mkdirSync(out, { recursive: true });
  writeFileSync(join(out, `${f.id.replace(/[^\w.-]/g, '_')}.runar.ts`), f.source, 'utf-8');
  writeFileSync(join(out, 'finding.json'), JSON.stringify(f, null, 2) + '\n', 'utf-8');
  return out;
}

// ---------------------------------------------------------------------------
// Public harness
// ---------------------------------------------------------------------------

export interface SpendOracleOptions {
  /** Number of generated contracts. */
  numCases: number;
  /** RNG seed; when omitted a random effective seed is chosen and reported. */
  seed?: number;
  /** Wall-clock budget in ms; the harness returns early once exceeded. */
  timeBudgetMs?: number;
  /** Findings directory. Default `conformance/fuzz-findings-spend/`. */
  findingsDir?: string;
  /**
   * Phase E4 — also run each case's semantics-preserving metamorphic variants
   * (renamed locals; swapped pure `if/else` arms) and require an identical
   * verdict AND identical `expectedState` outcome. Roughly triples runtime.
   */
  metamorphic?: boolean;
  verbose?: boolean;
}

export interface SpendOracleReport {
  totalCases: number;
  casesRun: number;
  acceptCount: number;
  rejectCount: number;
  failureCount: number;
  /** Per-failure-kind counts, for the CI summary. */
  byKind: Record<string, number>;
  /** Construct tags actually reached by this run. */
  tagsCovered: string[];
  /** Cumulative inputs replayed through `Spend.validate()`. */
  validatedInputs: number;
  earlyStop: boolean;
  durationMs: number;
  findings: string[];
  effectiveSeed: number;
}

export async function runSpendOracle(opts: SpendOracleOptions): Promise<SpendOracleReport> {
  const effectiveSeed = opts.seed ?? Math.floor(Math.random() * 0x7fffffff);
  const findingsDir = opts.findingsDir ?? join(ROOT, 'conformance', 'fuzz-findings-spend');
  const shapes = generateShapes({ seed: effectiveSeed, count: opts.numCases });

  const start = Date.now();
  let casesRun = 0;
  let acceptCount = 0;
  let rejectCount = 0;
  let failureCount = 0;
  let validatedInputs = 0;
  let earlyStop = false;
  const byKind: Record<string, number> = {};
  const tagsCovered = new Set<string>();
  const findings: string[] = [];

  // `RunarContract.deploy`/`finalizeCall` console.warn once per broadcast
  // because MockProvider's `getTransaction` has no record of the tx it just
  // accepted. Harmless, but two lines per case drowns the fuzzer's own output.
  const realWarn = console.warn;
  console.warn = (...args: unknown[]): void => {
    const first = args[0];
    if (typeof first === 'string' && first.startsWith('Failed to fetch transaction after broadcast')) return;
    realWarn(...(args as []));
  };

  try {
    for (const shape of shapes) {
      if (opts.timeBudgetMs !== undefined && Date.now() - start > opts.timeBudgetMs) {
        earlyStop = true;
        break;
      }
      casesRun += 1;
      for (const t of shape.tags) tagsCovered.add(t);

      let outcome: CaseOutcome;
      try {
        outcome = await runCase(shape, opts.metamorphic === true);
      } catch (e) {
        outcome = {
          ok: false,
          findings: [
            {
              kind: 'harness-error',
              message: e instanceof Error ? `${e.message}\n${e.stack ?? ''}` : String(e),
            },
          ],
          spendAccepted: false,
          validatedInputs: 0,
        };
      }

      validatedInputs += outcome.validatedInputs;
      if (outcome.spendAccepted) acceptCount += 1;
      else rejectCount += 1;

      if (outcome.ok) {
        if (opts.verbose) {
          console.log(
            `  ok   ${shape.id} → ${outcome.spendAccepted ? 'accept' : 'reject'} (${shape.tags.join(',')})`,
          );
        }
        continue;
      }

      for (const partial of outcome.findings) {
        failureCount += 1;
        byKind[partial.kind] = (byKind[partial.kind] ?? 0) + 1;
        const finding: SpendOracleFinding = {
          seed: effectiveSeed,
          index: shape.index,
          id: shape.id,
          family: shape.family,
          tags: shape.tags,
          constructorArgs: shape.constructorArgs.map(jsonValue),
          methodArgs: shape.methodArgs.map(jsonValue),
          intent: shape.intent,
          ...partial,
          // A metamorphic variant carries its OWN source; everything else is
          // the base shape's.
          source: partial.source ?? shape.source,
        };
        const dir = saveFinding(findingsDir, finding);
        findings.push(dir);
        console.error(
          `FAIL [${finding.kind}] ${shape.id} (${shape.family})\n` +
            `  ${finding.message}\n` +
            `  replay: --spend-oracle --seed ${effectiveSeed} --num ${opts.numCases}\n` +
            `  saved:  ${dir}`,
        );
      }
    }
  } finally {
    console.warn = realWarn;
  }

  return {
    totalCases: shapes.length,
    casesRun,
    acceptCount,
    rejectCount,
    failureCount,
    byKind,
    tagsCovered: [...tagsCovered].sort(),
    validatedInputs,
    earlyStop,
    durationMs: Date.now() - start,
    findings,
    effectiveSeed,
  };
}
