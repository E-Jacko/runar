/**
 * RawOutput regtest — this.addRawOutput with state continuation.
 * Pins source order: [0]=raw(1000), [1]=state(2000), [2+]=change.
 */

import { describe, it, expect } from 'vitest';
import { Transaction } from '@bsv/sdk';
import { compileContract } from './helpers/compile.js';
import { RunarContract } from 'runar-sdk';
import { createFundedWallet } from './helpers/wallet.js';
import { createProvider, rpcCall } from './helpers/node.js';

const SOURCE = 'integration/contracts/outputs/RawOutput.runar.ts';

describe('RawOutput (regtest)', () => {
  it('emits raw then state in declaration order and re-spends continuation', async () => {
    const artifact = compileContract(SOURCE);
    const contract = new RunarContract(artifact, [0n]);
    const provider = createProvider();
    const { signer, pubKeyHash } = await createFundedWallet(provider);

    await contract.deploy(provider, signer, { satoshis: 50_000 });

    const p2pkh = '76a914' + pubKeyHash + '88ac';
    const { txid } = await contract.call('sendToScript', [p2pkh], provider, signer);
    expect(txid).toHaveLength(64);
    expect(contract.state.count).toBe(1n);

    const rawTxHex = (await rpcCall('getrawtransaction', txid)) as string;
    const tx = Transaction.fromHex(rawTxHex);
    expect(tx.outputs.length).toBeGreaterThanOrEqual(2);

    // Declaration order: addRawOutput first, addOutput (state) second
    expect(tx.outputs[0]!.satoshis).toBe(1000);
    expect(tx.outputs[0]!.lockingScript.toHex()).toBe(p2pkh);
    expect(tx.outputs[1]!.satoshis).toBe(2000);
    // State continuation must be the tracked UTXO index
    expect(contract.getUtxo()?.outputIndex).toBe(1);

    // Second spend proves the continuation is live
    const p2pkh2 = '76a914' + 'ab'.repeat(20) + '88ac';
    const { txid: txid2 } = await contract.call('sendToScript', [p2pkh2], provider, signer);
    expect(txid2).toHaveLength(64);
    expect(contract.state.count).toBe(2n);
  });
});
