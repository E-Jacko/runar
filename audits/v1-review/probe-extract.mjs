// Extract Grok's PROBES.md contracts and run the TS-tier compile matrix
// (fold-OFF + fold-ON). Stage 1 of triage step 1.3.
import { readFileSync, writeFileSync, mkdirSync } from 'fs';
import { compile } from '../../packages/runar-compiler/dist/index.js';

const md = readFileSync(new URL('./grok/PROBES.md', import.meta.url), 'utf8');
const OUT = new URL('./probes/', import.meta.url).pathname;
mkdirSync(OUT, { recursive: true });

// `## P01 — title` ... ```typescript <code> ```
const probes = [];
const re = /^## (P\d+)\s+—\s+(.+?)$/gm;
let m;
const marks = [];
while ((m = re.exec(md)) !== null) marks.push({ id: m[1], title: m[2], idx: m.index });
for (let i = 0; i < marks.length; i++) {
  const seg = md.slice(marks[i].idx, i + 1 < marks.length ? marks[i + 1].idx : md.length);
  const cb = seg.match(/```typescript\n([\s\S]*?)```/);
  if (!cb) { probes.push({ ...marks[i], code: null }); continue; }
  const code = cb[1];
  const callLine = (code.match(/^\/\/\s*Call:.*$/m) || [])[0] ?? null;
  probes.push({ id: marks[i].id, title: marks[i].title, code, call: callLine });
}

const rows = [];
for (const p of probes) {
  if (!p.code) { rows.push({ ...p, verdict: 'NO-CODE' }); continue; }
  const cls = (p.code.match(/class\s+(\w+)/) || [])[1] ?? p.id;
  const file = `${OUT}${p.id}.runar.ts`;
  writeFileSync(file, p.code);
  const out = { id: p.id, title: p.title, cls, call: p.call };
  for (const [tag, dis] of [['foldOFF', true], ['foldON', false]]) {
    try {
      const r = compile(p.code, { fileName: `${cls}.runar.ts`, disableConstantFolding: dis });
      out[tag] = r.success
        ? { ok: true, hex: r.scriptHex, len: (r.scriptHex || '').length / 2 }
        : { ok: false, err: r.diagnostics.filter(d => d.severity === 'error').map(d => d.message)[0] };
    } catch (e) { out[tag] = { ok: false, err: 'THREW: ' + e.message }; }
  }
  out.foldDiffers = out.foldOFF.ok && out.foldON.ok && out.foldOFF.hex !== out.foldON.hex;
  rows.push(out);
}

writeFileSync(new URL('./probe-compile-matrix.json', import.meta.url), JSON.stringify(rows, null, 1));
const okc = rows.filter(r => r.foldOFF?.ok).length;
const failc = rows.filter(r => r.foldOFF && !r.foldOFF.ok).length;
console.log(`probes=${rows.length} compiled=${okc} rejected=${failc} noCode=${rows.filter(r=>r.verdict==='NO-CODE').length}`);
console.log('\n--- compile failures (candidate duds or real diagnostics) ---');
for (const r of rows.filter(r => r.foldOFF && !r.foldOFF.ok)) console.log(`  ${r.id}: ${String(r.foldOFF.err).slice(0, 110)}`);
console.log('\n--- fold-OFF vs fold-ON hex differs (expected for most; flag only if suspicious) ---');
console.log('  ' + rows.filter(r => r.foldDiffers).map(r => r.id).join(' '));
