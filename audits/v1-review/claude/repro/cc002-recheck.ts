#!/usr/bin/env npx tsx
/**
 * Re-verify CC-001/CC-002 (session 1, S0) against HEAD 52de4384.
 *
 * CC-002 direction: the nested declared-results `if` layout defect yields a
 * WRONGLY-SPENDABLE script — the source rejects, the deployed script accepts.
 */
import { readFileSync } from 'fs';
import { resolve, dirname } from 'path';
import { fileURLToPath } from 'url';
import { runTriModalExecution } from '../../../../packages/runar-testing/src/oracle/tri-modal-execution.js';

const __dirname = dirname(fileURLToPath(import.meta.url));
const src = readFileSync(resolve(__dirname, 'CC-002-bypass.runar.ts'), 'utf8');

console.log('=== CC-002 re-check @ HEAD ===');
for (const fold of [false, true]) {
  for (const v of [0n, 1n, -1n, -2n, 5n]) {
    const r = runTriModalExecution({
      source: src,
      fileName: 'Bypass.runar.ts',
      method: 'run5',
      args: [v],
      constructorArgs: { q: 1n },
      disableConstantFolding: fold,
    });
    const flag =
      r.interpreterAccepted !== r.spendAccepted ? '  <<< DIVERGENCE' : '';
    console.log(
      `fold-${fold ? 'OFF' : 'ON'} param2=${v}  interp=${r.interpreterAccepted} vm=${r.vmAccepted} spend=${r.spendAccepted}${flag}`,
    );
    if (v === 0n && !fold) console.log(`  lockingHex=${r.lockingHex}`);
  }
}
