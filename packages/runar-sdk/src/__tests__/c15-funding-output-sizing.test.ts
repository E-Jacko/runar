/**
 * Finding C15 — call funding selection must size ALL outputs, not just the
 * single continuation. `estimateDeployFee` / `selectUtxos` gained an
 * `extraOutputBytes` parameter (the serialized framing of multi-output / raw /
 * data outputs beyond the one already counted via `lockingScriptByteLen`);
 * `prepareCall` computes it so a multi-output or large-dataOutput call does not
 * stop one UTXO short — which, after finding C3, would then be rejected as
 * underfunded rather than silently stranding funds.
 */
import { describe, it, expect } from 'vitest';
import { estimateDeployFee, selectUtxos } from '../deployment.js';
import type { UTXO } from '../types.js';

describe('#C15 — funding fee sizes all outputs (extraOutputBytes)', () => {
  it('estimateDeployFee adds extraOutputBytes to the fee', () => {
    const base = estimateDeployFee(1, 100, 1000); // 1000 sat/KB, no extra
    const withOut = estimateDeployFee(1, 100, 1000, 0, 5000); // +5000 output bytes
    expect(withOut).toBeGreaterThan(base);
    // 5000 extra bytes at 1000 sat/KB == 5000 sats more.
    expect(withOut - base).toBe(5000);
  });

  it('selectUtxos picks more coins when extra output bytes tip the fee over the edge', () => {
    const utxos: UTXO[] = [
      { txid: 'aa'.repeat(32), outputIndex: 0, satoshis: 10_000, script: '' },
      { txid: 'bb'.repeat(32), outputIndex: 0, satoshis: 10_000, script: '' },
    ];
    // Target 9_000 at 1000 sat/KB. With no extra output bytes a single 10_000
    // coin covers 9_000 + a ~226-sat fee → 1 coin. Adding 2_000 output bytes
    // (2_000 sats of fee) pushes the requirement past 10_000 → 2 coins needed.
    const few = selectUtxos(utxos, 9_000, 25, 1000, 0, 0);
    const more = selectUtxos(utxos, 9_000, 25, 1000, 0, 2_000);
    expect(few.length).toBe(1);
    expect(more.length).toBe(2);
  });
});
