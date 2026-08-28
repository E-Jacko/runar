/**
 * CondWriteMultiField regtest — issue #99 multi-property if-without-else.
 * On-chain state decode required.
 */

import { describe, it, expect } from 'vitest';
import { compileContract } from './helpers/compile.js';
import { RunarContract } from 'runar-sdk';
import { createFundedWallet } from './helpers/wallet.js';
import { createProvider } from './helpers/node.js';
import { assertOnChainState } from './helpers/onchain.js';

const SOURCE = 'integration/contracts/constructs/CondWriteMultiField.runar.ts';

describe('CondWriteMultiField (regtest)', () => {
  it('flag>0 bumps a and b on-chain', async () => {
    const artifact = compileContract(SOURCE);
    const contract = new RunarContract(artifact, [1n, 2n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);

    await contract.deploy(provider, signer, { satoshis: 50_000 });
    const { txid } = await contract.call('bump', [1n], provider, signer);
    expect(txid).toHaveLength(64);
    await assertOnChainState(artifact, txid, 0, { a: 2n, b: 4n });
  });

  it('flag==0 leaves a and b unchanged on-chain', async () => {
    const artifact = compileContract(SOURCE);
    const contract = new RunarContract(artifact, [1n, 2n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);

    await contract.deploy(provider, signer, { satoshis: 50_000 });
    const { txid } = await contract.call('bump', [0n], provider, signer);
    expect(txid).toHaveLength(64);
    await assertOnChainState(artifact, txid, 0, { a: 1n, b: 2n });
  });
});
