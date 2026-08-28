/**
 * BranchMergedLocals regtest — Palmer-1 construct on a real BSV node.
 * Asserts on-chain state (decoded OP_RETURN), not only SDK memory.
 */

import { describe, it, expect } from 'vitest';
import { compileContract } from './helpers/compile.js';
import { RunarContract } from 'runar-sdk';
import { createFundedWallet } from './helpers/wallet.js';
import { createProvider } from './helpers/node.js';
import { assertOnChainState } from './helpers/onchain.js';

const SOURCE = 'integration/contracts/constructs/BranchMergedLocals.runar.ts';

describe('BranchMergedLocals (regtest)', () => {
  it('toFirst>0 rebinds a only; on-chain state is (amount, b)', async () => {
    const artifact = compileContract(SOURCE);
    const contract = new RunarContract(artifact, [10n, 20n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);

    await contract.deploy(provider, signer, { satoshis: 50_000 });
    const { txid } = await contract.call('bid', [99n, 1n], provider, signer);
    expect(txid).toHaveLength(64);
    expect(contract.state.a).toBe(99n);
    expect(contract.state.b).toBe(20n);
    await assertOnChainState(artifact, txid, 0, { a: 99n, b: 20n });
  });

  it('toFirst==0 rebinds b only; on-chain state is (a, amount)', async () => {
    const artifact = compileContract(SOURCE);
    const contract = new RunarContract(artifact, [10n, 20n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);

    await contract.deploy(provider, signer, { satoshis: 50_000 });
    const { txid } = await contract.call('bid', [77n, 0n], provider, signer);
    expect(txid).toHaveLength(64);
    await assertOnChainState(artifact, txid, 0, { a: 10n, b: 77n });
  });

  it('chains two bids (continuation spend proves live state)', async () => {
    const artifact = compileContract(SOURCE);
    const contract = new RunarContract(artifact, [1n, 2n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);

    await contract.deploy(provider, signer, { satoshis: 50_000 });
    const { txid: t1 } = await contract.call('bid', [10n, 1n], provider, signer);
    await assertOnChainState(artifact, t1, 0, { a: 10n, b: 2n });
    const { txid: t2 } = await contract.call('bid', [20n, 0n], provider, signer);
    await assertOnChainState(artifact, t2, 0, { a: 10n, b: 20n });
  });
});
