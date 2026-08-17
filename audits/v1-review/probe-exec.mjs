// Stage 2 of triage step 1.3 — execute Grok's compiled probes.
// Signal used is MODEL-INDEPENDENT: ANF interpreter (source semantics) vs the
// real @bsv/sdk Spend engine driven through a real deploy -> call. A probe
// where the interpreter accepts and Spend rejects is a candidate defect.
import { readFileSync, writeFileSync, readdirSync } from 'fs';
import { compile } from '../../packages/runar-compiler/dist/index.js';
import { TestContract } from '../../packages/runar-testing/dist/index.js';
import {
  RunarContract, MockProvider, LocalSigner, buildP2PKHScript,
} from '../../packages/runar-sdk/dist/index.js';

const PRIV = '0000000000000000000000000000000000000000000000000000000000000007';
const PUBHEX = '02' + 'a1'.repeat(32);
const DIR = new URL('./probes/', import.meta.url).pathname;

function argFor(t, i) {
  switch (t) {
    case 'bigint': return [3n, 1n, 0n, 2n][i % 4];
    case 'boolean': return i % 2 === 0;
    case 'ByteString': return '05';
    case 'PubKey': return PUBHEX;
    case 'Sig': return '30'.repeat(35);
    case 'Sha256': return 'ab'.repeat(32);
    default: return 1n;
  }
}

const rows = [];
for (const f of readdirSync(DIR).filter((f) => f.endsWith('.runar.ts')).sort()) {
  const id = f.replace('.runar.ts', '');
  const src = readFileSync(DIR + f, 'utf8');
  const cls = (src.match(/class\s+(\w+)/) || [])[1] ?? id;
  const c = compile(src, { fileName: `${cls}.runar.ts` }); // fold-ON = shipped default
  if (!c.success) { rows.push({ id, verdict: 'COMPILE-REJECT' }); continue; }

  const ast = c.contract;
  // Derive constructor arity from the SOURCE signature, not from the property
  // list: a property with an initializer is excluded from the auto-generated
  // constructor but an explicit constructor may still take a seed parameter.
  const ctorSig = (src.match(/constructor\s*\(([^)]*)\)/) || [])[1] ?? '';
  const ctorParams = ctorSig.split(',').map((s) => s.trim()).filter(Boolean)
    .map((s) => (s.split(':')[1] ?? 'bigint').trim());
  const ctorArgs = ctorParams.map((t, i) => argFor(t, i));
  const method = (ast?.methods ?? []).find((m) => m.visibility === 'public' || m.isPublic);
  if (!method) { rows.push({ id, verdict: 'NO-PUBLIC-METHOD' }); continue; }
  const mArgs = (method.params ?? []).map((p, i) => argFor(p.type, i));

  // --- source semantics via the ANF interpreter -------------------------
  let interpAccepted = null, interpErr;
  try {
    const init = {};
    (ast?.properties ?? []).forEach((p, i) => {
      if (!p.readonly) init[p.name] = argFor(p.type, i);
    });
    const tc = TestContract.fromSource(src, init, `${cls}.runar.ts`);
    tc.call(method.name, ...mArgs);
    interpAccepted = true;
  } catch (e) { interpAccepted = false; interpErr = String(e.message).slice(0, 120); }

  // --- real deploy -> call through Spend --------------------------------
  let spendAccepted = false, engineErr;
  try {
    const signer = new LocalSigner(PRIV);
    const provider = new MockProvider();
    const address = await signer.getAddress();
    provider.addUtxo(address, {
      txid: 'ee'.repeat(32), outputIndex: 0, satoshis: 1_000_000,
      script: buildP2PKHScript(await signer.getPublicKey()),
    });
    const contract = new RunarContract(c.artifact, ctorArgs);
    contract.connect(provider, signer);
    await contract.deploy({ satoshis: 50_000 });
    await contract.call(method.name, mArgs, { dryRun: true });
    spendAccepted = true;
  } catch (e) { engineErr = String(e.message).slice(0, 220); }

  const divergent = interpAccepted === true && spendAccepted === false;
  rows.push({ id, cls, method: method.name, ctorArgs: ctorArgs.map(String), mArgs: mArgs.map(String),
    interpAccepted, interpErr, spendAccepted, engineErr, verdict: divergent ? 'DIVERGENT' : 'agree' });
  console.log(`${id.padEnd(5)} interp=${String(interpAccepted).padEnd(5)} spend=${String(spendAccepted).padEnd(5)} ${divergent ? '<<< DIVERGENT' : ''}`);
  if (divergent) console.log(`      engine: ${engineErr}`);
}
writeFileSync(new URL('./probe-exec-results.json', import.meta.url), JSON.stringify(rows, null, 1));
const d = rows.filter((r) => r.verdict === 'DIVERGENT');
console.log(`\nexecuted=${rows.length} DIVERGENT=${d.length}: ${d.map((r) => r.id).join(' ')}`);
