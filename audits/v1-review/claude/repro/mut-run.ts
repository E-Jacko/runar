#!/usr/bin/env npx tsx
/**
 * Parallel mutation runner (audit CC, obligation 4).
 *
 * Each worker gets its own copy of packages/runar-compiler/src at
 * packages/runar-compiler/.mut-wN so mutants can be applied concurrently
 * without clobbering the real tree. Gate = mut-gate.ts (71 fixtures,
 * byte-exact golden hex).
 *
 *   CAUGHT   -> gate exits non-zero (some fixture's bytes changed / compile broke)
 *   SURVIVED -> gate exits 0: the entire 71-fixture golden corpus is blind to it
 *
 * Usage: npx tsx mut-run.ts --in <mutants.json> --out <results.json> [--workers 6] [--limit N]
 */
import { readFileSync, writeFileSync, cpSync, rmSync, existsSync, mkdirSync } from 'fs';
import { resolve, dirname, join } from 'path';
import { fileURLToPath } from 'url';
import { spawn } from 'child_process';

const __dirname = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(__dirname, '../../../..');
const PKG = join(ROOT, 'packages/runar-compiler');
const TSX = join(ROOT, 'conformance/node_modules/.bin/tsx');
const GATE = join(__dirname, 'mut-gate.ts');

const argv = process.argv.slice(2);
const arg = (k: string, d?: string) => {
  const i = argv.indexOf(k);
  return i >= 0 ? argv[i + 1]! : d;
};
const inFile = arg('--in', join(__dirname, 'mutants-generated.json'))!;
const outFile = arg('--out', join(__dirname, 'mutation-results.json'))!;
const WORKERS = parseInt(arg('--workers', '6')!, 10);
const LIMIT = parseInt(arg('--limit', '0')!, 10);

interface Mutant {
  id: string; file: string; line: number; before: string; after: string; op: string; region: string;
}
let mutants: Mutant[] = JSON.parse(readFileSync(inFile, 'utf8'));
if (LIMIT > 0) mutants = mutants.slice(0, LIMIT);

interface Result extends Mutant { verdict: 'CAUGHT' | 'SURVIVED' | 'ERROR'; ms: number; detail?: string }
const results: Result[] = [];

function runGate(entry: string): Promise<{ code: number; out: string }> {
  return new Promise((res) => {
    const p = spawn(TSX, [GATE, '--json'], {
      cwd: join(ROOT, 'conformance'),
      env: { ...process.env, MUT_COMPILER_ENTRY: entry },
    });
    let out = '';
    p.stdout.on('data', (d) => (out += d));
    p.stderr.on('data', (d) => (out += d));
    p.on('close', (code) => res({ code: code ?? 1, out }));
    // Hard cap: a mutant that makes the compiler loop forever must not wedge the run.
    setTimeout(() => { try { p.kill('SIGKILL'); } catch {} }, 180_000);
  });
}

async function worker(wid: number, queue: Mutant[]) {
  const wdir = join(PKG, `.mut-w${wid}`);
  if (existsSync(wdir)) rmSync(wdir, { recursive: true, force: true });
  cpSync(join(PKG, 'src'), wdir, { recursive: true });
  const entry = join(wdir, 'index.js');

  // Cache pristine file contents for fast revert.
  const pristine = new Map<string, string>();

  for (const mu of queue) {
    // Mutant file paths are repo-relative and always inside packages/runar-compiler/src.
    const relInSrc = mu.file.replace('packages/runar-compiler/src/', '');
    const target = join(wdir, relInSrc);
    if (!pristine.has(target)) pristine.set(target, readFileSync(target, 'utf8'));
    const orig = pristine.get(target)!;
    const lines = orig.split('\n');

    if (lines[mu.line - 1] !== mu.before) {
      results.push({ ...mu, verdict: 'ERROR', ms: 0, detail: 'line drift' });
      continue;
    }
    lines[mu.line - 1] = mu.after;
    writeFileSync(target, lines.join('\n'));

    const t0 = Date.now();
    const { code, out } = await runGate(entry);
    const ms = Date.now() - t0;

    writeFileSync(target, orig); // revert

    let detail: string | undefined;
    try {
      const j = JSON.parse(out.trim().split('\n').pop() ?? '{}');
      detail = `mismatches=${(j.mismatches ?? []).length}`;
    } catch { detail = out.slice(0, 160).replace(/\n/g, ' '); }

    results.push({ ...mu, verdict: code === 0 ? 'SURVIVED' : 'CAUGHT', ms, detail });
    if (results.length % 25 === 0) {
      const s = results.filter((r) => r.verdict === 'SURVIVED').length;
      process.stderr.write(`  [${results.length}/${mutants.length}] survived=${s}\n`);
      writeFileSync(outFile, JSON.stringify(results, null, 1));
    }
  }
  rmSync(wdir, { recursive: true, force: true });
}

const queues: Mutant[][] = Array.from({ length: WORKERS }, () => []);
mutants.forEach((m, i) => queues[i % WORKERS]!.push(m));

const t0 = Date.now();
await Promise.all(queues.map((q, i) => worker(i, q)));
writeFileSync(outFile, JSON.stringify(results, null, 1));

const caught = results.filter((r) => r.verdict === 'CAUGHT').length;
const survived = results.filter((r) => r.verdict === 'SURVIVED').length;
const err = results.filter((r) => r.verdict === 'ERROR').length;
console.log(`\n=== mutation score ===`);
console.log(`total=${results.length} caught=${caught} survived=${survived} error=${err}`);
console.log(`score=${((caught / (caught + survived)) * 100).toFixed(1)}%  wall=${((Date.now() - t0) / 1000).toFixed(0)}s`);
const byRegion: Record<string, { c: number; s: number }> = {};
for (const r of results) {
  byRegion[r.region] ??= { c: 0, s: 0 };
  if (r.verdict === 'CAUGHT') byRegion[r.region]!.c++;
  else if (r.verdict === 'SURVIVED') byRegion[r.region]!.s++;
}
for (const [k, v] of Object.entries(byRegion)) {
  console.log(`  ${k}: caught=${v.c} survived=${v.s} (${((v.c / (v.c + v.s)) * 100).toFixed(0)}%)`);
}
