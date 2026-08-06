/**
 * Testing-gap remediation, reviewer finding P2: @bsv/sdk's `Spend.isRelaxed()`
 * returns true whenever `transactionVersion > 1`, silently disabling
 * push-only / clean-stack / low-S / minimal-number enforcement. Every
 * builder in this SDK uses version 1 today, so C8 validation is strict — but
 * nothing else guards that invariant, and a future version bump (e.g. for
 * BIP-68 relative locktime) would silently downgrade every check with no
 * signal. `validateBroadcastTx` now warns when it sees `tx.version > 1`.
 */
import { describe, it, expect, vi, afterEach } from 'vitest';
import { Transaction, UnlockingScript, LockingScript } from '@bsv/sdk';
import { MockProvider } from '../providers/mock.js';

const KNOWN_TXID = 'aa'.repeat(32);

function makeTx(version: number): Transaction {
  const tx = new Transaction(version);
  tx.addInput({
    sourceTXID: KNOWN_TXID,
    sourceOutputIndex: 0,
    unlockingScript: new UnlockingScript(),
    sequence: 0xffffffff,
  });
  tx.addOutput({ satoshis: 900, lockingScript: LockingScript.fromHex('51') });
  return tx;
}

describe('MockProvider — warns when validating a "relaxed" (version > 1) tx (P2)', () => {
  afterEach(() => vi.restoreAllMocks());

  it('warns for a version-2 tx', async () => {
    const warn = vi.spyOn(console, 'warn').mockImplementation(() => {});
    const provider = new MockProvider('testnet', { enforceFeeFloor: false });
    provider.addContractUtxo('p2-relaxed', { txid: KNOWN_TXID, outputIndex: 0, satoshis: 900, script: '51' });

    await provider.broadcast(makeTx(2));

    expect(warn.mock.calls.some((args) => typeof args[0] === 'string' && /relaxed|version 2/i.test(args[0]))).toBe(
      true,
    );
  });

  it('does not warn for the default version-1 tx', async () => {
    const warn = vi.spyOn(console, 'warn').mockImplementation(() => {});
    const provider = new MockProvider('testnet', { enforceFeeFloor: false });
    provider.addContractUtxo('p2-strict', { txid: KNOWN_TXID, outputIndex: 0, satoshis: 900, script: '51' });

    await provider.broadcast(makeTx(1));

    expect(warn).not.toHaveBeenCalled();
  });
});
