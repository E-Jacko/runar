/**
 * SCOPE (testing-gap remediation, plan design principle P8): this fuzzer's
 * oracle is ABSOLUTE (the real engine), but it is scoped to STATELESS
 * fragments against a synthetic transaction context and it compares VERDICTS
 * ONLY. A miscompile that leaves the script acceptable while committing the
 * WRONG continuation state is invisible here. Full transaction context plus a
 * post-state VALUE pin is `--spend-oracle`. See `conformance/fuzzer/README.md`.
 */

/**
 * Tri-modal source-vs-script EXECUTION oracle (issue #124) — fast-check
 * PROPERTY-mode harness.
 *
 * The `--execute` harness (`execute-differential.ts`) is bi-modal (ANF
 * interpreter vs. `ScriptVM`) and drives a `fc.sample` corpus (no shrinking).
 * This harness upgrades both axes:
 *
 *   - Tri-modal: every generated spend runs through the AST-walking `RunarInterpreter`
 *     (source semantics — the one genuinely independent implementation),
 *     `ScriptVM` (the upstream `@bsv/sdk` `Spend` engine stepped opcode by
 *     opcode, consensus wrappers off), and a strict `Spend.validate()` that
 *     additionally enforces the consensus clean-stack + push-only +
 *     minimal-push rules. An interpreter-vs-engine disagreement is a strong
 *     signal of a real, shared-design miscompile; a ScriptVM-vs-validate
 *     disagreement means the script evaluates but is not a valid spend.
 *
 *   - PROPERTY mode: it drives `arbExecCase` through `fc.check` so that ANY
 *     divergence is SHRUNK to a minimal (contract, inputs) counterexample —
 *     exactly the repro you want on a nightly failure or a PR-gate red.
 *
 * The `arbExecCase` corpus exercises the shapes that historically hid silent
 * miscompiles and only became correctly compilable after #121 (loop start/step)
 * and #130 (param shadow): non-zero-start + countdown `for` loops, `substr` /
 * `cat` / `len` byte-ops over ByteString parameters, and post-loop parameter
 * reads. Cases are constructed to always be valid, in-range Rúnar, so the only
 * way the three engines disagree is a genuine compiler bug.
 *
 * Determinism: fast-check's seed drives BOTH the contract structure and the
 * concrete inputs. `--seed` reproduces a run exactly; an unseeded run picks a
 * random seed and prints it. A failure writes the shrunk repro (source + inputs
 * + per-engine verdicts) to `conformance/fuzz-findings-trimodal/` and exits 1.
 */

import fc from 'fast-check';
import { writeFileSync, mkdirSync } from 'node:fs';
import { join, resolve, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

import {
  arbExecCase,
  renderTypeScript,
  type ExecCase,
  type ExecArg,
} from '../../packages/runar-testing/src/fuzzer/index.js';
import { runTriModalExecution } from '../../packages/runar-testing/src/oracle/index.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);
const ROOT = resolve(__dirname, '../..');

// ---------------------------------------------------------------------------
// Options / report
// ---------------------------------------------------------------------------

export interface TriModalDifferentialOptions {
  /** Number of property runs (generated cases). */
  numCases: number;
  /** fast-check seed; when omitted a random seed is chosen and reported. */
  seed?: number;
  /** Where to dump the shrunk repro on failure. Default
   *  `conformance/fuzz-findings-trimodal/`. */
  findingsDir?: string;
  /** Verbose fast-check output (prints the shrinking path). */
  verbose?: boolean;
}

export interface TriModalDifferentialReport {
  /** Runs fast-check actually executed before passing or finding a repro. */
  numRuns: number;
  /** The seed that reproduces this exact run (replay with --seed). */
  seed: number;
  /** True when a tri-modal disagreement (or a compile/engine throw) was found. */
  failed: boolean;
  /** Directories of saved findings (present iff failed). */
  findings: string[];
  durationMs: number;
  /** Human-readable one-line summary of the shrunk repro, when failed. */
  repro?: string;
}

// ---------------------------------------------------------------------------
// Finding persistence
// ---------------------------------------------------------------------------

function jsonifyArg(v: ExecArg): string {
  if (typeof v === 'bigint') return `${v}n`;
  if (typeof v === 'boolean') return String(v);
  return `0x${Buffer.from(v).toString('hex')}`;
}

interface TriModalFinding {
  seed: number;
  reason: string;
  contractName: string;
  method: string;
  source: string;
  constructorArgs: Record<string, string>;
  args: string[];
  interpreterAccepted?: boolean;
  vmAccepted?: boolean;
  spendAccepted?: boolean;
  lockingHex?: string;
  witnessHex?: string;
  interpreterError?: string;
  vmError?: string;
  spendError?: string;
  throwMessage?: string;
}

function saveFinding(dir: string, f: TriModalFinding): string {
  const ts = new Date().toISOString().replace(/[:.]/g, '-');
  const out = join(dir, `${ts}-${f.contractName}-${f.method}`);
  mkdirSync(out, { recursive: true });
  writeFileSync(join(out, 'contract.runar.ts'), f.source + '\n', 'utf-8');
  writeFileSync(join(out, 'finding.json'), JSON.stringify(f, null, 2) + '\n', 'utf-8');
  return out;
}

/** Re-run the tri-modal oracle on the shrunk counterexample to capture the
 *  per-engine verdicts for the finding record. */
function describeCase(
  c: ExecCase,
): { finding: Omit<TriModalFinding, 'seed'>; summary: string } {
  const source = renderTypeScript(c.contract);
  const fileName = `${c.contract.name}.runar.ts`;
  const constructorArgs = Object.fromEntries(
    Object.entries(c.constructorArgs).map(([k, v]) => [k, jsonifyArg(v)]),
  );
  const args = c.args.map(jsonifyArg);
  try {
    const r = runTriModalExecution({
      source,
      fileName,
      method: c.method,
      args: c.args,
      constructorArgs: c.constructorArgs,
    });
    const reason = `tri-modal disagreement: interpreter=${r.interpreterAccepted} vm=${r.vmAccepted} spend=${r.spendAccepted}`;
    return {
      finding: {
        reason,
        contractName: c.contract.name,
        method: c.method,
        source,
        constructorArgs,
        args,
        interpreterAccepted: r.interpreterAccepted,
        vmAccepted: r.vmAccepted,
        spendAccepted: r.spendAccepted,
        lockingHex: r.lockingHex,
        witnessHex: r.witnessHex,
        interpreterError: r.interpreterError,
        vmError: r.vmError,
        spendError: r.spendError,
      },
      summary: `${c.contract.name}.${c.method}: ${reason}`,
    };
  } catch (e) {
    const message = e instanceof Error ? e.message : String(e);
    return {
      finding: {
        reason: `tri-modal harness throw: ${message}`,
        contractName: c.contract.name,
        method: c.method,
        source,
        constructorArgs,
        args,
        throwMessage: message,
      },
      summary: `${c.contract.name}.${c.method}: THREW ${message}`,
    };
  }
}

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

export async function runTriModalDifferential(
  opts: TriModalDifferentialOptions,
): Promise<TriModalDifferentialReport> {
  const findingsDir =
    opts.findingsDir ?? join(ROOT, 'conformance', 'fuzz-findings-trimodal');
  const start = Date.now();

  // The property holds iff all three engines agree (and nothing throws). A
  // throw inside the predicate is treated by fast-check as a failing case and
  // is shrunk like any other counterexample.
  const property = fc.property(arbExecCase, (c: ExecCase): boolean => {
    let r;
    try {
      r = runTriModalExecution({
        source: renderTypeScript(c.contract),
        fileName: `${c.contract.name}.runar.ts`,
        method: c.method,
        args: c.args,
        constructorArgs: c.constructorArgs,
      });
    } catch {
      return false; // compile / engine throw — a distinct anomaly, still a fail
    }
    return r.agrees;
  });

  const result = fc.check(property, {
    numRuns: opts.numCases,
    seed: opts.seed,
    verbose: opts.verbose ? fc.VerbosityLevel.Verbose : fc.VerbosityLevel.None,
  });

  const report: TriModalDifferentialReport = {
    numRuns: result.numRuns,
    seed: result.seed,
    failed: result.failed,
    findings: [],
    durationMs: Date.now() - start,
  };

  if (result.failed && result.counterexample) {
    const shrunk = result.counterexample[0] as ExecCase;
    const { finding, summary } = describeCase(shrunk);
    const dir = saveFinding(findingsDir, { seed: result.seed, ...finding });
    report.findings.push(dir);
    report.repro = summary;
    console.error(`DIVERGENCE (shrunk): ${summary}`);
    console.error(`  saved: ${dir}`);
  }

  return report;
}
