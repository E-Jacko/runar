#!/usr/bin/env npx tsx
/**
 * Mechanical mutant generator for the Rúnar TS compiler back half (audit CC).
 *
 * Emits {file, line, before, after, op, region} records. Biased toward the
 * branch-merge (`lowerIf` 2092..2664) and frame-offset (PICK/ROLL/depth/slot)
 * classes named in the audit brief.
 *
 * Output: mutants-generated.json
 */
import { readFileSync, writeFileSync } from 'fs';
import { resolve, dirname } from 'path';
import { fileURLToPath } from 'url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(__dirname, '../../../..');

interface Mutant {
  id: string;
  file: string;
  line: number;      // 1-indexed
  before: string;    // exact original line text
  after: string;     // mutated line text
  op: string;
  region: string;    // 'branch-merge' | 'frame-offset' | 'emit' | 'optimizer' | 'other'
}

const TARGETS = [
  { file: 'packages/runar-compiler/src/passes/05-stack-lower.ts', hot: [[2092, 2664]] as [number, number][] },
  { file: 'packages/runar-compiler/src/passes/06-emit.ts', hot: [] as [number, number][] },
  { file: 'packages/runar-compiler/src/optimizer/peephole.ts', hot: [] as [number, number][] },
  { file: 'packages/runar-compiler/src/optimizer/constant-fold.ts', hot: [] as [number, number][] },
  { file: 'packages/runar-compiler/src/optimizer/dce.ts', hot: [] as [number, number][] },
  { file: 'packages/runar-compiler/src/optimizer/anf-ec.ts', hot: [] as [number, number][] },
];

// Ordered: first matching rule wins per (line, occurrence).
const RULES: { op: string; find: RegExp; make: (m: RegExpExecArray) => string }[] = [
  // --- frame-offset / off-by-one on index arithmetic -------------------
  { op: 'idx-plus1-to-plus2', find: /(\b(?:depth|index|idx|offset|slot|pos|n|i|d)\s*\+\s*)1\b/g, make: (m) => `${m[1]}2` },
  { op: 'idx-minus1-to-minus2', find: /(\b(?:depth|index|idx|offset|slot|pos|n|i|d)\s*-\s*)1\b/g, make: (m) => `${m[1]}2` },
  { op: 'idx-minus1-to-plus1', find: /(\b(?:depth|index|idx|offset|slot|pos)\s*)-(\s*1\b)/g, make: (m) => `${m[1]}+${m[2]}` },
  { op: 'length-off-by-one', find: /(\.length\s*-\s*)1\b/g, make: (m) => `${m[1]}2` },
  { op: 'length-drop-minus', find: /\.length\s*-\s*1\b/g, make: () => `.length` },

  // --- comparison / relational -----------------------------------------
  { op: 'cmp-lt-to-le', find: /([^<>=!])<([^<=])/g, make: (m) => `${m[1]}<=${m[2]}` },
  { op: 'cmp-gt-to-ge', find: /([^<>=!])>([^>=])/g, make: (m) => `${m[1]}>=${m[2]}` },
  { op: 'cmp-ge-to-gt', find: />=/g, make: () => `>` },
  { op: 'cmp-le-to-lt', find: /<=/g, make: () => `<` },
  { op: 'eq-to-neq', find: /===/g, make: () => `!==` },
  { op: 'neq-to-eq', find: /!==/g, make: () => `===` },

  // --- arithmetic -------------------------------------------------------
  { op: 'arith-plus-to-minus', find: /(\w|\))\s\+\s(\w)/g, make: (m) => `${m[1]} - ${m[2]}` },
  { op: 'arith-minus-to-plus', find: /(\w|\))\s-\s(\w)/g, make: (m) => `${m[1]} + ${m[2]}` },
  { op: 'maxmin-swap', find: /Math\.max/g, make: () => `Math.min` },
  { op: 'minmax-swap', find: /Math\.min/g, make: () => `Math.max` },

  // --- boolean / control ------------------------------------------------
  { op: 'bool-and-to-or', find: /&&/g, make: () => `||` },
  { op: 'bool-or-to-and', find: /\|\|/g, make: () => `&&` },
  { op: 'cond-negate', find: /^(\s*(?:\}\s*else\s+)?if\s*\()(.+)(\)\s*\{\s*)$/g, make: (m) => `${m[1]}!(${m[2]})${m[3]}` },

  // --- stack-effect deletions ------------------------------------------
  { op: 'drop-op-verify', find: /^(\s*)(.*\bOP_VERIFY\b.*)$/g, make: (m) => `${m[1]}/* MUT-DROP */ void 0; // ${m[2].replace(/\*\//g, '* /')}` },
  { op: 'drop-push-stmt', find: /^(\s*)(this\.(?:emit|push|out)\w*\(.*\);)\s*$/g, make: (m) => `${m[1]}/* MUT-DROP */ void 0; // ${m[2].replace(/\*\//g, '* /')}` },
];

function regionOf(file: string, line: number, hot: [number, number][], text: string): string {
  if (hot.some(([a, b]) => line >= a && line <= b)) return 'branch-merge';
  if (/OP_PICK|OP_ROLL|depth|slot|frame|stackMap/.test(text)) return 'frame-offset';
  if (file.includes('06-emit')) return 'emit';
  if (file.includes('optimizer')) return 'optimizer';
  return 'other';
}

const mutants: Mutant[] = [];
let counter = 0;

for (const { file, hot } of TARGETS) {
  const abs = resolve(ROOT, file);
  const lines = readFileSync(abs, 'utf8').split('\n');

  for (let li = 0; li < lines.length; li++) {
    const text = lines[li]!;
    const trimmed = text.trim();
    // Skip comments, imports, empty, and pure type declarations.
    if (!trimmed || trimmed.startsWith('//') || trimmed.startsWith('*') || trimmed.startsWith('/*')) continue;
    if (trimmed.startsWith('import ') || trimmed.startsWith('export type') || trimmed.startsWith('interface ')) continue;

    for (const rule of RULES) {
      rule.find.lastIndex = 0;
      let m: RegExpExecArray | null;
      let occ = 0;
      while ((m = rule.find.exec(text)) !== null) {
        if (m[0].length === 0) { rule.find.lastIndex++; continue; }
        const mutatedLine =
          text.slice(0, m.index) + rule.make(m) + text.slice(m.index + m[0].length);
        if (mutatedLine === text) { occ++; continue; }
        mutants.push({
          id: `M${String(++counter).padStart(4, '0')}`,
          file,
          line: li + 1,
          before: text,
          after: mutatedLine,
          op: rule.op,
          region: regionOf(file, li + 1, hot, text),
        });
        occ++;
        if (occ >= 2) break; // cap per rule per line
      }
    }
  }
}

writeFileSync(resolve(__dirname, 'mutants-generated.json'), JSON.stringify(mutants, null, 1));
const byRegion: Record<string, number> = {};
const byOp: Record<string, number> = {};
for (const mu of mutants) {
  byRegion[mu.region] = (byRegion[mu.region] ?? 0) + 1;
  byOp[mu.op] = (byOp[mu.op] ?? 0) + 1;
}
console.log(`generated ${mutants.length} mutants`);
console.log('by region:', byRegion);
console.log('by op:', byOp);
