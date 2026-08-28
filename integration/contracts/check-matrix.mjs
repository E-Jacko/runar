#!/usr/bin/env node
/**
 * CI checker for integration/contracts/coverage-matrix.json.
 * Fails if a contract or listed test path is missing, or if a feature row
 * has neither regtest paths nor an explicit deferred reason.
 */
import { readFileSync, existsSync } from 'node:fs';
import { resolve, dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = resolve(__dirname, '..', '..');
const matrixPath = join(__dirname, 'coverage-matrix.json');

const matrix = JSON.parse(readFileSync(matrixPath, 'utf8'));
const errors = [];

for (const feat of matrix.features ?? []) {
  const id = feat.id ?? '<missing-id>';
  if (!feat.contract) {
    errors.push(`${id}: missing contract`);
    continue;
  }
  const contractAbs = join(__dirname, feat.contract);
  if (!existsSync(contractAbs)) {
    errors.push(`${id}: contract missing: integration/contracts/${feat.contract}`);
  }

  const regtest = feat.regtest ?? {};
  const deferred = feat.deferred ?? {};
  const tiers = ['ts', 'go', 'rust', 'python', 'ruby', 'zig', 'java'];
  let anyPath = false;
  for (const tier of tiers) {
    if (regtest[tier]) {
      anyPath = true;
      const p = join(REPO_ROOT, regtest[tier]);
      if (!existsSync(p)) {
        errors.push(`${id}: ${tier} test missing: ${regtest[tier]}`);
      }
    } else if (!deferred[tier] && !feat.deferredAll) {
      // Phase A rows should cover all tiers or explicit deferred
      const phaseA = new Set([
        'branch-merged-locals-k2-asymmetric',
        'cond-write-multi-field',
        'conditional-data-output',
        'state-bytestring-1byte-op-n',
        'add-raw-output',
        'checkMultiSig-2of3',
      ]);
      if (phaseA.has(feat.id)) {
        errors.push(`${id}: tier ${tier} missing from regtest and deferred`);
      }
    }
  }
  if (!anyPath && !feat.deferredAll) {
    if (Object.keys(deferred).length === 0) {
      errors.push(`${id}: no regtest paths and no deferred reason`);
    }
  }
}

if (errors.length > 0) {
  console.error('coverage-matrix check FAILED:');
  for (const e of errors) console.error('  -', e);
  process.exit(1);
}

console.log(
  `coverage-matrix OK: ${matrix.features.length} features, all listed paths exist`,
);
