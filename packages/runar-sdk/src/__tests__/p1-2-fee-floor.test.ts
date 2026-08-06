/**
 * Testing-gap remediation, reviewer finding P1-2: `validateBroadcastTx`'s
 * fee check was conservation-only — it rejected only `totalOut >
 * totalKnownIn`, so a zero-fee tx, a 1-sat fee on a large tx, and an
 * `undefined` output value (silently treated as 0 sats via `o.satoshis ??
 * 0`) all passed. The provider already knows its `feeRate`
 * (`setFeeRate`/`getFeeRate`), and the SDK's own fee model is
 * `Math.ceil(txSize * feeRate / 1000)` (`deployment.ts`'s
 * `estimateDeployFee`).
 *
 * Fix: when all inputs are known, require `totalKnownIn - totalOut >=
 * Math.ceil((tx.toHex().length / 2) * feeRate / 1000)`. An explicitly-named
 * opt-out (`{ enforceFeeFloor: false }` / `disableFeeFloor()`) exists for
 * tests that intentionally underpay — distinct from the always-ack
 * `validateBroadcasts` escape hatch: a fee-floor opt-out still runs the real
 * `Spend` interpreter and the conservation check, it only stops requiring a
 * real-world fee.
 */
import { describe, it, expect } from 'vitest';
import { Transaction, UnlockingScript, LockingScript } from '@bsv/sdk';
import { MockProvider } from '../providers/mock.js';

const KNOWN_TXID = 'aa'.repeat(32);

function makeTx(inputSatoshisSpentAs: number, outSatoshis: number | undefined): Transaction {
  const tx = new Transaction();
  tx.addInput({
    sourceTXID: KNOWN_TXID,
    sourceOutputIndex: 0,
    unlockingScript: new UnlockingScript(),
    sequence: 0xffffffff,
  });
  tx.addOutput({ satoshis: outSatoshis, lockingScript: LockingScript.fromHex('51') });
  return tx;
}

function registerKnownUtxo(provider: MockProvider, satoshis: number): void {
  provider.addContractUtxo('p1-2-fee-floor', {
    txid: KNOWN_TXID,
    outputIndex: 0,
    satoshis,
    script: '51', // OP_TRUE
  });
}

describe('MockProvider — fee floor is enforced by default (P1-2)', () => {
  it('rejects a zero-fee tx (outputs === inputs exactly)', async () => {
    const provider = new MockProvider();
    registerKnownUtxo(provider, 10_000);
    await expect(provider.broadcast(makeTx(10_000, 10_000))).rejects.toThrow(/fee/i);
  });

  it('rejects a 1-sat fee on a tx whose required fee (at 100 sat/KB) exceeds 1 sat', async () => {
    const provider = new MockProvider();
    registerKnownUtxo(provider, 10_000);
    await expect(provider.broadcast(makeTx(10_000, 9_999))).rejects.toThrow(/fee/i);
  });

  it('accepts a tx that pays at least the modeled fee', async () => {
    const provider = new MockProvider();
    registerKnownUtxo(provider, 10_000);
    // The tx is well under 1KB, so the required fee at 100 sat/KB rounds up
    // to a handful of sats; leave a comfortable margin.
    const txid = await provider.broadcast(makeTx(10_000, 9_900));
    expect(txid).toMatch(/^[0-9a-f]{64}$/);
  });

  it('treats an undefined output satoshis value as an error, not 0 sats', async () => {
    // @bsv/sdk's own addOutput() rejects `satoshis: undefined` unless
    // `change: true` — the realistic way an output reaches broadcast() with
    // satoshis still unset is a `change: true` output whose amount `tx.fee()`
    // was never called to compute.
    const tx = new Transaction();
    tx.addInput({
      sourceTXID: KNOWN_TXID,
      sourceOutputIndex: 0,
      unlockingScript: new UnlockingScript(),
      sequence: 0xffffffff,
    });
    tx.addOutput({ lockingScript: LockingScript.fromHex('51'), change: true });

    const provider = new MockProvider();
    registerKnownUtxo(provider, 10_000);
    await expect(provider.broadcast(tx)).rejects.toThrow(/satoshis/i);
  });

  it('a higher configured feeRate raises the required fee accordingly', async () => {
    const provider = new MockProvider();
    provider.setFeeRate(100_000); // 100,000 sat/KB — a fee that passed at the default rate now fails
    registerKnownUtxo(provider, 10_000);
    await expect(provider.broadcast(makeTx(10_000, 9_900))).rejects.toThrow(/fee/i);
  });
});

describe('MockProvider — fee floor has a separate, explicitly-named opt-out (P1-2)', () => {
  it('{ enforceFeeFloor: false } accepts a zero-fee tx but still runs Spend + the conservation check', async () => {
    const provider = new MockProvider('testnet', { enforceFeeFloor: false });
    registerKnownUtxo(provider, 10_000);
    const txid = await provider.broadcast(makeTx(10_000, 10_000));
    expect(txid).toMatch(/^[0-9a-f]{64}$/);
    // Conservation still applies even with the fee floor off.
    await expect(provider.broadcast(makeTx(10_000, 10_001))).rejects.toThrow(/underfunded/i);
  });

  it('disableFeeFloor() accepts a zero-fee tx', async () => {
    const provider = new MockProvider();
    provider.disableFeeFloor();
    registerKnownUtxo(provider, 10_000);
    const txid = await provider.broadcast(makeTx(10_000, 10_000));
    expect(txid).toMatch(/^[0-9a-f]{64}$/);
  });

  it('enableFeeFloor() re-enables enforcement after disableFeeFloor()', async () => {
    const provider = new MockProvider('testnet', { enforceFeeFloor: false });
    provider.enableFeeFloor();
    registerKnownUtxo(provider, 10_000);
    await expect(provider.broadcast(makeTx(10_000, 10_000))).rejects.toThrow(/fee/i);
  });
});
