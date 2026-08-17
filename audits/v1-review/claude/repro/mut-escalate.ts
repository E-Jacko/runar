#!/usr/bin/env npx tsx
/**
 * Survivor escalation (audit CC, obligation 4).
 *
 * A mutant that SURVIVES the 71-fixture byte-exact golden corpus is not yet a
 * coverage hole — it may be semantically equivalent, or live on a path no
 * fixture reaches. This escalates a survivor sample to the gates the curated
 * `conformance/mutation` harness maps its branch-merge mutants to, plus the
 * randomized absolute oracle. A mutant that survives ALL of them is either
 * equivalent or a real, measured hole in the whole net.
 *
 * Gates (in cost order, first hit wins):
 *   1. branch-result-depth-invariant  (Layer C of lowerIf)
 *   2. branch-merged-locals-vm        (deployed + called through @bsv/sdk Spend)
 *   3. state-push-framing-vm          (state <len><data> framing through Spend)
 *   4. tri-modal fuzz, 300 runs, fixed seed (absolute oracle)
 *
 * Usage: npx tsx mut-escalate.ts --in <results.json> --sample 30 [--regions branch-merge,frame-offset]
 */
import { readFileSync, writeFileSync, cpSync, rmSync, existsSync } from 'fs';
import { resolve, dirname, join } from 'path';
import { fileURLToPath } from 'url';
import { spawnSync } from 'child_process';

const __dirname = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(__dirname, '../../../..');
const PKG = join(ROOT, 'packages/runar-compiler');

const argv = process.argv.slice(2);
const arg = (k: string, d: string) => { const i = argv.indexOf(k); return i >= 0 ? argv[i + 1]! : d; };
const inFile = arg('--in', join(__dirname, 'mutation-results-ts.json'));
const SAMPLE = parseInt(arg('--sample', '30'), 10);
const REGIONS = arg('--regions', 'branch-merge,frame-offset').split(',');

const all = JSON.parse(readFileSync(inFile, 'utf8')) as any[];
const survivors = all.filter((r) => r.verdict === 'SURVIVED' && REGIONS.includes(r.region));
// Deterministic spread across the survivor set rather than the first N.
const step = Math.max(1, Math.floor(survivors.length / SAMPLE));
const sample = survivors.filter((_, i) => i % step === 0).slice(0, SAMPLE);
console.log(`survivors in ${REGIONS.join('/')}: ${survivors.length}; escalating ${sample.length}`);

const GATES: { name: string; cwd: string; cmd: string[] }[] = [
  { name: 'branch-result-depth-invariant', cwd: ROOT, cmd: ['npx', 'vitest', 'run', 'packages/runar-compiler/src/__tests__/branch-result-depth-invariant.test.ts'] },
  { name: 'branch-merged-locals-vm', cwd: ROOT, cmd: ['npx', 'vitest', 'run', 'packages/runar-testing/src/__tests__/branch-merged-locals-vm.test.ts'] },
  { name: 'state-push-framing-vm', cwd: ROOT, cmd: ['npx', 'vitest', 'run', 'packages/runar-testing/src/__tests__/state-push-framing-vm.test.ts'] },
  { name: 'tri-modal-300', cwd: join(ROOT, 'conformance'), cmd: [join(ROOT, 'conformance/node_modules/.bin/tsx'), 'fuzzer/index.ts', '--tri-modal', '--num', '300', '--seed', '31337'] },
];

const wdir = join(PKG, '.mut-esc');
if (existsSync(wdir)) rmSync(wdir, { recursive: true, force: true });
cpSync(join(PKG, 'src'), wdir, { recursive: true });

// The vitest gates resolve `runar-compiler` through the root vitest src alias,
// so they must observe the mutation in packages/runar-compiler/src ITSELF.
// Mutate in place and restore from the pristine copy after each mutant.
// Safety: this mutates the REAL packages/runar-compiler/src (the vitest gates
// resolve through the root src alias, so a copy would not be observed). Always
// restore, including on an interrupt.
const inFlight = new Map<string, string>();
function restoreAll() {
  for (const [p, txt] of inFlight) { try { writeFileSync(p, txt); } catch {} }
}
process.on('exit', restoreAll);
process.on('SIGINT', () => { restoreAll(); process.exit(130); });

const results: any[] = [];
for (const [i, mu] of sample.entries()) {
  const target = join(ROOT, mu.file);
  const pristine = readFileSync(join(wdir, mu.file.replace('packages/runar-compiler/src/', '')), 'utf8');
  const lines = pristine.split('\n');
  if (lines[mu.line - 1] !== mu.before) { results.push({ ...mu, escalation: 'LINE-DRIFT' }); continue; }
  lines[mu.line - 1] = mu.after;
  inFlight.set(target, pristine);
  writeFileSync(target, lines.join('\n'));

  let caughtBy = 'NONE';
  for (const g of GATES) {
    const r = spawnSync(g.cmd[0]!, g.cmd.slice(1), { cwd: g.cwd, encoding: 'utf8', timeout: 900_000 });
    const out = (r.stdout ?? '') + (r.stderr ?? '');
    const failed = r.status !== 0 || /Failures:\s*[1-9]/.test(out);
    if (failed) { caughtBy = g.name; break; }
  }
  writeFileSync(target, pristine); // restore

  results.push({ ...mu, escalation: caughtBy });
  console.log(`[${i + 1}/${sample.length}] ${mu.id} ${mu.region} ${mu.op} @${mu.file.split('/').pop()}:${mu.line} -> ${caughtBy}`);
  writeFileSync(join(__dirname, 'mutation-escalation.json'), JSON.stringify(results, null, 1));
}
rmSync(wdir, { recursive: true, force: true });

const none = results.filter((r) => r.escalation === 'NONE');
console.log(`\n=== escalation ===\nescalated=${results.length} caught-by-a-stronger-gate=${results.length - none.length} SURVIVED-EVERYTHING=${none.length}`);
