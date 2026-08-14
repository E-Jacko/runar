/**
 * Testing-gap remediation, reviewer finding P1-1: `validateBroadcastTx`
 * treats an input whose outpoint the provider doesn't know as merely
 * "skipped" (`allInputsKnown = false; continue`). If NO input is known, zero
 * `Spend`s run, the fee check is skipped (guarded by `allInputsKnown`), and
 * `validateBroadcastTx` returns `{ valid: true }` — a broadcast that
 * "ran under validation" while validating nothing. `providers.test.ts`'s
 * `makeBsvTx()` helper hit exactly this hole: it spends `'00'.repeat(32):0`
 * with an empty unlocking script and never registers that outpoint.
 *
 * Fix: count validated inputs. When the provider is validating and the tx
 * has inputs but zero of them matched a known outpoint, `broadcast()` throws
 * instead of silently acking. `getValidationStats()` exposes cumulative
 * validated/skipped counts so a test can assert its broadcasts weren't
 * vacuous.
 */
import { describe, it, expect } from 'vitest';
import { Transaction, UnlockingScript, LockingScript } from '@bsv/sdk';
import { MockProvider } from '../providers/mock.js';

const UNKNOWN_TXID = '00'.repeat(32);
const KNOWN_TXID = 'aa'.repeat(32);

/** A tx with a single input whose outpoint the provider was never told about. */
function makeTxWithUnknownInput(): Transaction {
  const tx = new Transaction();
  tx.addInput({
    sourceTXID: UNKNOWN_TXID,
    sourceOutputIndex: 0,
    unlockingScript: new UnlockingScript(),
    sequence: 0xffffffff,
  });
  tx.addOutput({ satoshis: 50000, lockingScript: LockingScript.fromHex('51') });
  return tx;
}

describe('MockProvider — zero-validated-inputs is a hard failure, not a vacuous pass (P1-1)', () => {
  it('throws when broadcasting a tx whose only input outpoint is unregistered', async () => {
    const provider = new MockProvider();
    await expect(provider.broadcast(makeTxWithUnknownInput())).rejects.toThrow(
      new RegExp(`${UNKNOWN_TXID}:0`),
    );
  });

  it('the thrown error points at addUtxo/addContractUtxo/addTransaction', async () => {
    const provider = new MockProvider();
    await expect(provider.broadcast(makeTxWithUnknownInput())).rejects.toThrow(
      /addUtxo|addContractUtxo|addTransaction/,
    );
  });

  it('does not throw for an unregistered input when validation is disabled', async () => {
    const provider = new MockProvider('testnet', { validateBroadcasts: false });
    await expect(provider.broadcast(makeTxWithUnknownInput())).resolves.toMatch(/^[0-9a-f]{64}$/);
  });

  it('getValidationStats() starts at zero', () => {
    const provider = new MockProvider();
    expect(provider.getValidationStats()).toEqual({ validated: 0, skipped: 0 });
  });

  it('getValidationStats() records a real validated input on a well-funded broadcast', async () => {
    const provider = new MockProvider();
    provider.addContractUtxo('known', {
      txid: KNOWN_TXID,
      outputIndex: 0,
      satoshis: 100_000,
      script: '51', // OP_TRUE
    });

    const tx = new Transaction();
    tx.addInput({
      sourceTXID: KNOWN_TXID,
      sourceOutputIndex: 0,
      unlockingScript: new UnlockingScript(),
      sequence: 0xffffffff,
    });
    tx.addOutput({ satoshis: 50000, lockingScript: LockingScript.fromHex('51') });

    await provider.broadcast(tx);
    expect(provider.getValidationStats()).toEqual({ validated: 1, skipped: 0 });
  });

  it('getValidationStats() records the skipped input from the rejected zero-validated broadcast', async () => {
    const provider = new MockProvider();
    await expect(provider.broadcast(makeTxWithUnknownInput())).rejects.toThrow();
    expect(provider.getValidationStats()).toEqual({ validated: 0, skipped: 1 });
  });

  it('matches an input carrying only sourceTransaction (no explicit sourceTXID) against a known outpoint', async () => {
    const parent = new Transaction();
    parent.addInput({
      sourceTXID: KNOWN_TXID,
      sourceOutputIndex: 0,
      unlockingScript: new UnlockingScript(),
      sequence: 0xffffffff,
    });
    parent.addOutput({ satoshis: 100_000, lockingScript: LockingScript.fromHex('51') });

    const provider = new MockProvider();
    provider.addContractUtxo('parent-output', {
      txid: parent.id('hex'),
      outputIndex: 0,
      satoshis: 100_000,
      script: '51', // OP_TRUE
    });

    const child = new Transaction();
    child.addInput({
      sourceTransaction: parent, // no sourceTXID field set
      sourceOutputIndex: 0,
      unlockingScript: new UnlockingScript(),
      sequence: 0xffffffff,
    });
    child.addOutput({ satoshis: 90_000, lockingScript: LockingScript.fromHex('51') });

    await provider.broadcast(child);
    expect(provider.getValidationStats()).toEqual({ validated: 1, skipped: 0 });
  });
});
