/**
 * Deep-review finding C8 (part 2): `MockProvider.broadcast()` unconditionally
 * acks — it never inspects the transaction, so a script-invalid or
 * underfunded tx is "successfully broadcast" (a deterministic fake txid is
 * returned) exactly like a valid one. Part 1 (the pre-broadcast local
 * dry-run in `finalizeCall`) already fails closed for the SDK's OWN call
 * path; this part adds an OPT-IN validating mode to `MockProvider` itself so
 * tests that talk to the provider directly (or a different code path
 * entirely) can also be held to a real bar.
 *
 * Default behaviour is UNCHANGED — validation is off unless
 * `enableBroadcastValidation()` is called — so the ~550 pre-existing SDK
 * tests that rely on MockProvider's permissive ack keep passing.
 */
import { describe, it, expect } from 'vitest';
import { Transaction, UnlockingScript, LockingScript } from '@bsv/sdk';
import { MockProvider } from '../providers/mock.js';

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

describe('MockProvider — opt-in broadcast validation (C8 part 2)', () => {
  it('RED: today, a script-invalid tx spending a KNOWN utxo is "successfully" broadcast', async () => {
    const provider = new MockProvider();
    provider.addContractUtxo('scriptinvalid', {
      txid: OUTPOINT_TXID,
      outputIndex: 0,
      satoshis: 500,
      script: '00', // OP_FALSE — unsatisfiable by an empty unlocking script
    });

    const txid = await provider.broadcast(makeScriptInvalidTx());
    expect(txid).toMatch(/^[0-9a-f]{64}$/);
  });

  it('RED: today, a tx spending more than its known inputs are worth is "successfully" broadcast', async () => {
    const provider = new MockProvider();
    provider.addContractUtxo('underfunded', {
      txid: OUTPOINT_TXID,
      outputIndex: 1,
      satoshis: 500,
      script: '51', // OP_TRUE — script-valid regardless of amounts
    });

    const txid = await provider.broadcast(makeUnderfundedTx());
    expect(txid).toMatch(/^[0-9a-f]{64}$/);
  });

  it('GREEN: enableBroadcastValidation() rejects the same script-invalid tx', async () => {
    const provider = new MockProvider();
    provider.enableBroadcastValidation();
    provider.addContractUtxo('scriptinvalid', {
      txid: OUTPOINT_TXID,
      outputIndex: 0,
      satoshis: 500,
      script: '00',
    });

    await expect(provider.broadcast(makeScriptInvalidTx())).rejects.toThrow();
  });

  it('GREEN: enableBroadcastValidation() rejects the same underfunded tx', async () => {
    const provider = new MockProvider();
    provider.enableBroadcastValidation();
    provider.addContractUtxo('underfunded', {
      txid: OUTPOINT_TXID,
      outputIndex: 1,
      satoshis: 500,
      script: '51',
    });

    await expect(provider.broadcast(makeUnderfundedTx())).rejects.toThrow();
  });

  it('GREEN: enableBroadcastValidation() still accepts a script-valid, well-funded tx', async () => {
    const provider = new MockProvider();
    provider.enableBroadcastValidation();
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

  it('validation is off by default (backward compatible with the ~550 pre-existing SDK tests)', async () => {
    const provider = new MockProvider();
    provider.addContractUtxo('scriptinvalid', {
      txid: OUTPOINT_TXID,
      outputIndex: 0,
      satoshis: 500,
      script: '00',
    });
    await expect(provider.broadcast(makeScriptInvalidTx())).resolves.toMatch(/^[0-9a-f]{64}$/);
  });
});
