#!/usr/bin/env npx tsx
/**
 * Go-tier mutation harness (audit CC, obligation 4 — "the six non-TS tiers
 * have zero mutation coverage today").
 *
 * Generates mechanical mutants over compilers/go/codegen/{stack,emit,optimizer}.go,
 * biased to the branch-merge region (lowerIf 1903..2441), then per mutant:
 *   apply -> `go build` -> compile all 71 fixtures -> compare hex to goldens -> revert.
 *
 * CAUGHT   = build failure, or any fixture's bytes changed
 * SURVIVED = builds and every fixture is byte-identical
 *
 * Usage: npx tsx mut-go.ts [--limit N] [--workers 3] [--gen-only]
 */
import { readFileSync, writeFileSync, existsSync, readdirSync, cpSync, rmSync } from 'fs';
import { resolve, dirname, join } from 'path';
import { fileURLToPath } from 'url';
import { spawnSync } from 'child_process';

const __dirname = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(__dirname, '../../../..');
const TESTS = join(ROOT, 'conformance/tests');

const argv = process.argv.slice(2);
const arg = (k: string, d: string) => { const i = argv.indexOf(k); return i >= 0 ? argv[i + 1]! : d; };
const LIMIT = parseInt(arg('--limit', '0'), 10);
const WORKERS = parseInt(arg('--workers', '3'), 10);
const GEN_ONLY = argv.includes('--gen-only');

interface Mutant { id: string; file: string; line: number; before: string; after: string; op: string; region: string }

const TARGETS = [
  { file: 'codegen/stack.go', hot: [[1903, 2441]] as [number, number][] },
  { file: 'codegen/emit.go', hot: [] as [number, number][] },
  { file: 'codegen/optimizer.go', hot: [] as [number, number][] },
];

const RULES: { op: string; find: RegExp; make: (m: RegExpExecArray) => string }[] = [
  { op: 'idx-plus1-to-plus2', find: /(\b(?:depth|index|idx|offset|slot|pos|n|i|d)\s*\+\s*)1\b/g, make: (m) => `${m[1]}2` },
  { op: 'idx-minus1-to-minus2', find: /(\b(?:depth|index|idx|offset|slot|pos|n|i|d)\s*-\s*)1\b/g, make: (m) => `${m[1]}2` },
  { op: 'len-off-by-one', find: /(len\([A-Za-z_.]+\)\s*-\s*)1\b/g, make: (m) => `${m[1]}2` },
  { op: 'len-drop-minus', find: /(len\([A-Za-z_.]+\))\s*-\s*1\b/g, make: (m) => `${m[1]}` },
  { op: 'cmp-lt-to-le', find: /([^<>=!])<([^<=-])/g, make: (m) => `${m[1]}<=${m[2]}` },
  { op: 'cmp-gt-to-ge', find: /([^<>=!-])>([^>=])/g, make: (m) => `${m[1]}>=${m[2]}` },
  { op: 'cmp-ge-to-gt', find: />=/g, make: () => `>` },
  { op: 'cmp-le-to-lt', find: /<=/g, make: () => `<` },
  { op: 'eq-to-neq', find: /==/g, make: () => `!=` },
  { op: 'neq-to-eq', find: /!=/g, make: () => `==` },
  { op: 'bool-and-to-or', find: /&&/g, make: () => `||` },
  { op: 'bool-or-to-and', find: /\|\|/g, make: () => `&&` },
  { op: 'arith-plus-to-minus', find: /(\w|\))\s\+\s(\w)/g, make: (m) => `${m[1]} - ${m[2]}` },
  { op: 'arith-minus-to-plus', find: /(\w|\))\s-\s(\w)/g, make: (m) => `${m[1]} + ${m[2]}` },
];

function genMutants(goRoot: string): Mutant[] {
  const out: Mutant[] = [];
  let c = 0;
  for (const { file, hot } of TARGETS) {
    const lines = readFileSync(join(goRoot, file), 'utf8').split('\n');
    for (let li = 0; li < lines.length; li++) {
      const text = lines[li]!;
      const t = text.trim();
      if (!t || t.startsWith('//') || t.startsWith('*') || t.startsWith('import')) continue;
      for (const rule of RULES) {
        rule.find.lastIndex = 0;
        let m: RegExpExecArray | null; let occ = 0;
        while ((m = rule.find.exec(text)) !== null) {
          if (!m[0].length) { rule.find.lastIndex++; continue; }
          const mut = text.slice(0, m.index) + rule.make(m) + text.slice(m.index + m[0].length);
          if (mut !== text) {
            out.push({
              id: `G${String(++c).padStart(4, '0')}`, file, line: li + 1, before: text, after: mut, op: rule.op,
              region: hot.some(([a, b]) => li + 1 >= a && li + 1 <= b) ? 'branch-merge'
                : /OP_PICK|OP_ROLL|depth|slot|stackMap/.test(text) ? 'frame-offset'
                : file.includes('emit') ? 'emit' : file.includes('optimizer') ? 'optimizer' : 'other',
            });
          }
          if (++occ >= 2) break;
        }
      }
    }
  }
  return out;
}

// ---- fixtures + goldens ---------------------------------------------------
const fixtures: { name: string; src: string; golden: string }[] = [];
for (const name of readdirSync(TESTS)) {
  const dir = join(TESTS, name);
  const sj = join(dir, 'source.json');
  const gp = join(dir, 'expected-script.hex');
  if (!existsSync(sj) || !existsSync(gp)) continue;
  const rel = JSON.parse(readFileSync(sj, 'utf8')).sources?.['.runar.ts'];
  if (!rel) continue;
  const src = resolve(dir, rel);
  if (!existsSync(src)) continue;
  fixtures.push({ name, src, golden: readFileSync(gp, 'utf8').trim() });
}

function runGate(bin: string): boolean {
  // true = all fixtures byte-match (mutant survived)
  for (const f of fixtures) {
    const r = spawnSync(bin, ['--source', f.src, '--hex', '--disable-constant-folding'],
      { encoding: 'utf8', timeout: 60_000 });
    if (r.status !== 0) return false;
    if ((r.stdout ?? '').trim() !== f.golden) return false;
  }
  return true;
}

const baseMutants = genMutants(join(ROOT, 'compilers/go'));
console.log(`generated ${baseMutants.length} Go mutants`);
const byRegion: Record<string, number> = {};
for (const m of baseMutants) byRegion[m.region] = (byRegion[m.region] ?? 0) + 1;
console.log('by region:', byRegion);
writeFileSync(join(__dirname, 'mutants-go-all.json'), JSON.stringify(baseMutants, null, 1));
if (GEN_ONLY) process.exit(0);

// Sample: all branch-merge + frame-offset + emit, then fill from the rest.
let rngState = 20260816;
const rnd = () => ((rngState = (rngState * 1103515245 + 12345) & 0x7fffffff) / 0x7fffffff);
const prio = baseMutants.filter((m) => ['branch-merge', 'frame-offset', 'emit'].includes(m.region));
const rest = baseMutants.filter((m) => !['branch-merge', 'frame-offset', 'emit'].includes(m.region))
  .sort(() => rnd() - 0.5);
let sample = [...prio, ...rest];
if (LIMIT > 0) sample = sample.slice(0, LIMIT);
console.log(`running ${sample.length} Go mutants across ${WORKERS} workers`);

interface Res extends Mutant { verdict: 'CAUGHT' | 'SURVIVED' | 'ERROR'; detail?: string }
const results: Res[] = [];
const OUT = join(__dirname, 'mutation-results-go.json');

// IN-PLACE, SERIAL. A copied tree at $ROOT/.mut-go-wN is NOT one of the
// modules listed in go.work, so `go build` there fails with
// "current directory is contained in a module that is not one of the workspace
// modules listed in go.work" for EVERY mutant — which silently scores the whole
// run 100% CAUGHT/build-fail. That is a harness bug, not a compiler property;
// it is exactly the Go-worktree-escape trap. Mutating compilers/go directly
// keeps the workspace intact. Pristine contents are restored after each mutant
// and again on exit.
const PRISTINE = new Map<string, string>();
function restoreAll() {
  for (const [p, txt] of PRISTINE) { try { writeFileSync(p, txt); } catch {} }
}
process.on('exit', restoreAll);
process.on('SIGINT', () => { restoreAll(); process.exit(130); });

async function worker(wid: number, queue: Mutant[]) {
  const wdir = join(ROOT, 'compilers/go');
  const bin = join(wdir, `runar-mut-w${wid}`);
  const pristine = PRISTINE;

  for (const mu of queue) {
    const target = join(wdir, mu.file);
    if (!pristine.has(target)) pristine.set(target, readFileSync(target, 'utf8'));
    const orig = pristine.get(target)!;
    const lines = orig.split('\n');
    if (lines[mu.line - 1] !== mu.before) { results.push({ ...mu, verdict: 'ERROR', detail: 'line drift' }); continue; }
    lines[mu.line - 1] = mu.after;
    writeFileSync(target, lines.join('\n'));

    const b = spawnSync('go', ['build', '-o', bin, '.'], { cwd: wdir, encoding: 'utf8', timeout: 300_000 });
    let verdict: Res['verdict']; let detail: string | undefined;
    if (b.status !== 0) { verdict = 'CAUGHT'; detail = 'build-fail'; }
    else { const ok = runGate(bin); verdict = ok ? 'SURVIVED' : 'CAUGHT'; detail = ok ? 'all-golden-match' : 'hex-diff'; }

    writeFileSync(target, orig);
    results.push({ ...mu, verdict, detail });
    if (results.length % 10 === 0) {
      process.stderr.write(`  [${results.length}/${sample.length}] survived=${results.filter(r => r.verdict === 'SURVIVED').length}\n`);
      writeFileSync(OUT, JSON.stringify(results, null, 1));
    }
  }
  try { rmSync(bin, { force: true }); } catch {}
}

// Serial only: the tree is mutated in place, so concurrent workers would
// clobber each other.
await worker(0, sample);
restoreAll();
writeFileSync(OUT, JSON.stringify(results, null, 1));

const caught = results.filter(r => r.verdict === 'CAUGHT').length;
const surv = results.filter(r => r.verdict === 'SURVIVED').length;
console.log(`\n=== Go mutation score ===\ntotal=${results.length} caught=${caught} survived=${surv}`);
console.log(`score=${((caught / (caught + surv)) * 100).toFixed(1)}%`);
const agg: Record<string, { c: number; s: number }> = {};
for (const r of results) { agg[r.region] ??= { c: 0, s: 0 }; if (r.verdict === 'CAUGHT') agg[r.region]!.c++; else if (r.verdict === 'SURVIVED') agg[r.region]!.s++; }
for (const [k, v] of Object.entries(agg)) console.log(`  ${k}: caught=${v.c} survived=${v.s}`);
