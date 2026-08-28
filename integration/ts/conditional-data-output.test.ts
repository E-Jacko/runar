/**
 * ConditionalDataOutput regtest — addDataOutput on a branch must keep
 * single-output state continuation spendable on-chain.
 */

import { describe, it, expect } from 'vitest';
import { Transaction } from '@bsv/sdk';
import { compileContract } from './helpers/compile.js';
import { RunarContract } from 'runar-sdk';
import { createFundedWallet } from './helpers/wallet.js';
import { createProvider, rpcCall } from './helpers/node.js';

const SOURCE = 'integration/contracts/constructs/ConditionalDataOutput.runar.ts';

describe('ConditionalDataOutput (regtest)', () => {
  it('flag=true emits data at [1] between state and change; re-spends', async () => {
    const artifact = compileContract(SOURCE);
    const contract = new RunarContract(artifact, [0n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);

    await contract.deploy(provider, signer, { satoshis: 20_000 });

    // OP_RETURN "bsvm-test"
    const payload = '6a09' + '6273766d2d74657374';
    const { txid } = await contract.call('pay', [true, payload], provider, signer);
    expect(txid).toHaveLength(64);
    expect(contract.state.amount).toBe(1n);

    const rawTxHex = (await rpcCall('getrawtransaction', txid)) as string;
    const tx = Transaction.fromHex(rawTxHex);
    expect(tx.outputs.length).toBeGreaterThanOrEqual(2);
    const dataOut = tx.outputs[1]!;
    expect(dataOut.satoshis).toBe(1);
    expect(dataOut.lockingScript.toHex()).toBe(payload);

    // Continuation still spendable
    const { txid: t2 } = await contract.call('pay', [false, payload], provider, signer);
    expect(t2).toHaveLength(64);
    expect(contract.state.amount).toBe(2n);
  });

  it('flag=false has no data output matching payload', async () => {
    const artifact = compileContract(SOURCE);
    const contract = new RunarContract(artifact, [0n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);

    await contract.deploy(provider, signer, { satoshis: 20_000 });

    const payload = '6a04' + '6e6f6e65'; // OP_RETURN "none"
    const { txid } = await contract.call('pay', [false, payload], provider, signer);
    expect(txid).toHaveLength(64);
    expect(contract.state.amount).toBe(1n);

    const rawTxHex = (await rpcCall('getrawtransaction', txid)) as string;
    const tx = Transaction.fromHex(rawTxHex);
    const matching = tx.outputs.filter((o) => o.lockingScript.toHex() === payload);
    expect(matching).toHaveLength(0);
  });
});
