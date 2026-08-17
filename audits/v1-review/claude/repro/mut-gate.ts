#!/usr/bin/env npx tsx
/**
 * Fast in-process golden gate for mutation scoring (audit CC, H1/H5).
 *
 * Compiles every conformance fixture's `.runar.ts` source through the TS
 * compiler IN PROCESS and compares `scriptHex` against `expected-script.hex`
 * (goldens are stamped fold-OFF, so folding is disabled here).
 *
 * Exit 0 = all fixtures byte-match (mutant SURVIVED the golden corpus).
 * Exit 1 = at least one mismatch/compile failure (mutant CAUGHT).
 *
 * Usage: npx tsx mut-gate.ts [--subset] [--json]
 */
import { readFileSync, existsSync, readdirSync } from 'fs';
import { resolve, dirname, join } from 'path';
import { fileURLToPath } from 'url';
const __dirname = dirname(fileURLToPath(import.meta.url));

// The compiler entry is parameterised so the mutation runner can point each
// parallel worker at its own mutated copy of packages/runar-compiler/src.
const ENTRY =
  process.env.MUT_COMPILER_ENTRY ??
  resolve(__dirname, '../../../../packages/runar-compiler/src/index.js');
const { compile } = (await import(ENTRY)) as typeof import('../../../../packages/runar-compiler/src/index.js');
const TESTS = resolve(__dirname, '../../../../conformance/tests');

const args = process.argv.slice(2);
const asJson = args.includes('--json');
const only = args.find((a) => a.startsWith('--only='))?.slice(7);

const names = readdirSync(TESTS).filter((n) => existsSync(join(TESTS, n, 'source.json')));
const selected = only ? only.split(',') : names;

let mismatches: string[] = [];
let compiled = 0;
let skipped = 0;

for (const name of selected) {
  const dir = join(TESTS, name);
  const srcJson = JSON.parse(readFileSync(join(dir, 'source.json'), 'utf8'));
  const rel = srcJson.sources?.['.runar.ts'];
  const goldenPath = join(dir, 'expected-script.hex');
  if (!rel || !existsSync(goldenPath)) { skipped++; continue; }
  const srcPath = resolve(dir, rel);
  if (!existsSync(srcPath)) { skipped++; continue; }

  const source = readFileSync(srcPath, 'utf8');
  const golden = readFileSync(goldenPath, 'utf8').trim();

  let hex: string | undefined;
  try {
    const res = compile(source, {
      fileName: srcPath.split('/').pop(),
      disableConstantFolding: true,
    });
    hex = res.success ? res.scriptHex : undefined;
    if (!res.success) { mismatches.push(`${name}: COMPILE-FAIL`); continue; }
  } catch (e) {
    mismatches.push(`${name}: THREW ${(e as Error).message?.slice(0, 80)}`);
    continue;
  }
  compiled++;
  if ((hex ?? '').trim() !== golden) {
    mismatches.push(`${name}: HEX-DIFF`);
  }
}

if (asJson) {
  console.log(JSON.stringify({ compiled, skipped, mismatches }));
} else {
  console.log(`compiled=${compiled} skipped=${skipped} mismatches=${mismatches.length}`);
  for (const m of mismatches.slice(0, 20)) console.log('  ' + m);
}
process.exit(mismatches.length > 0 ? 1 : 0);
