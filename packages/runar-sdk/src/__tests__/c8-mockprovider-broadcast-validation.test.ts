/**
 * Deep-review finding C8 (part 2): `MockProvider.broadcast()` unconditionally
 * acked — it never inspected the transaction, so a script-invalid or
 * underfunded tx was "successfully broadcast" (a deterministic fake txid was
 * returned) exactly like a valid one. Part 1 (the pre-broadcast local
 * dry-run in `finalizeCall`) already fails closed for the SDK's OWN call
 * path.
 *
 * Testing-gap remediation plan Phase A1 (reviewer #1, TG-001): broadcast
 * validation is no longer opt-in. `MockProvider` validates by default —
 * the switch that would have failed both Palmer bugs on the main SDK test
 * path is now the one every test hits unless it explicitly opts out via
 * `disableBroadcastValidation()` / `{ validateBroadcasts: false }`, which
 * Phase A2's machine-checked allowlist gates.
 */
import { describe, it, expect } from 'vitest';
import { Transaction, UnlockingScript, LockingScript } from '@bsv/sdk';
import { MockProvider, newAlwaysAckMockProvider } from '../providers/mock.js';

const OUTPOINT_TXID = 'aa'.repeat(32);

/** A tx spending a known UTXO whose locking script (OP_FALSE) can never be
 * satisfied by an empty unlocking script — always script-invalid. */
function makeScriptInvalidTx(): Transaction {
  const tx = new Transaction();
  tx.addInput({
    sourceTXID: OUTPOINT_TXID,
    sourceOutputIndex: 0,
    unlockingScript: new UnlockingScript(),
    sequence: 0xffffffff,
  });
  tx.addOutput({ satoshis: 500, lockingScript: LockingScript.fromHex('51') });
  return tx;
}

/** A tx whose single known input (500 sats, trivially-true OP_TRUE locking
 * script) is spent into an output far exceeding its value — script-valid but
 * economically impossible (outputs > inputs). */
function makeUnderfundedTx(): Transaction {
  const tx = new Transaction();
  tx.addInput({
    sourceTXID: OUTPOINT_TXID,
    sourceOutputIndex: 1,
    unlockingScript: new UnlockingScript(),
    sequence: 0xffffffff,
  });
  tx.addOutput({ satoshis: 10_000, lockingScript: LockingScript.fromHex('51') });
  return tx;
}

describe('MockProvider — broadcast validation is default-on (C8 part 2 / Phase A1)', () => {
  it('GREEN: a default MockProvider() rejects a script-invalid tx spending a KNOWN utxo', async () => {
    const provider = new MockProvider();
    provider.addContractUtxo('scriptinvalid', {
      txid: OUTPOINT_TXID,
      outputIndex: 0,
      satoshis: 500,
      script: '00', // OP_FALSE — unsatisfiable by an empty unlocking script
    });

    await expect(provider.broadcast(makeScriptInvalidTx())).rejects.toThrow();
  });

  it('GREEN: a default MockProvider() rejects an underfunded tx (outputs > known inputs)', async () => {
    const provider = new MockProvider();
    provider.addContractUtxo('underfunded', {
      txid: OUTPOINT_TXID,
      outputIndex: 1,
      satoshis: 500,
      script: '51', // OP_TRUE — script-valid regardless of amounts
    });

    await expect(provider.broadcast(makeUnderfundedTx())).rejects.toThrow();
  });

  it('GREEN: a default MockProvider() still accepts a script-valid, well-funded tx', async () => {
    const provider = new MockProvider();
    provider.addContractUtxo('wellfunded', {
      txid: OUTPOINT_TXID,
      outputIndex: 2,
      satoshis: 1000,
      script: '51', // OP_TRUE
    });

    const tx = new Transaction();
    tx.addInput({
      sourceTXID: OUTPOINT_TXID,
      sourceOutputIndex: 2,
      unlockingScript: new UnlockingScript(),
      sequence: 0xffffffff,
    });
    tx.addOutput({ satoshis: 900, lockingScript: LockingScript.fromHex('51') });

    const txid = await provider.broadcast(tx);
    expect(txid).toMatch(/^[0-9a-f]{64}$/);
  });

  it('GREEN: new MockProvider("testnet", { validateBroadcasts: false }) still acks the invalid tx', async () => {
    const provider = new MockProvider('testnet', { validateBroadcasts: false });
    provider.addContractUtxo('scriptinvalid', {
      txid: OUTPOINT_TXID,
      outputIndex: 0,
      satoshis: 500,
      script: '00',
    });

    await expect(provider.broadcast(makeScriptInvalidTx())).resolves.toMatch(/^[0-9a-f]{64}$/);
  });

  it('GREEN: disableBroadcastValidation() still acks the same invalid tx (opt-out API)', async () => {
    const provider = new MockProvider();
    provider.disableBroadcastValidation();
    provider.addContractUtxo('scriptinvalid', {
      txid: OUTPOINT_TXID,
      outputIndex: 0,
      satoshis: 500,
      script: '00',
    });

    await expect(provider.broadcast(makeScriptInvalidTx())).resolves.toMatch(/^[0-9a-f]{64}$/);
  });

  it('GREEN: enableBroadcastValidation(false) still acks the same invalid tx (back-compat)', async () => {
    const provider = new MockProvider();
    provider.enableBroadcastValidation(false);
    provider.addContractUtxo('scriptinvalid', {
      txid: OUTPOINT_TXID,
      outputIndex: 0,
      satoshis: 500,
      script: '00',
    });

    await expect(provider.broadcast(makeScriptInvalidTx())).resolves.toMatch(/^[0-9a-f]{64}$/);
  });

  it('GREEN: newAlwaysAckMockProvider() acks the invalid tx (allowlisted-tests-only convenience factory)', async () => {
    const provider = newAlwaysAckMockProvider();
    provider.addContractUtxo('scriptinvalid', {
      txid: OUTPOINT_TXID,
      outputIndex: 0,
      satoshis: 500,
      script: '00',
    });

    await expect(provider.broadcast(makeScriptInvalidTx())).resolves.toMatch(/^[0-9a-f]{64}$/);
  });

  it('GREEN: enableBroadcastValidation() (no args) re-enables validation after an opt-out', async () => {
    const provider = new MockProvider('testnet', { validateBroadcasts: false });
    provider.enableBroadcastValidation();
    provider.addContractUtxo('scriptinvalid', {
      txid: OUTPOINT_TXID,
      outputIndex: 0,
      satoshis: 500,
      script: '00',
    });

    await expect(provider.broadcast(makeScriptInvalidTx())).rejects.toThrow();
  });
});
