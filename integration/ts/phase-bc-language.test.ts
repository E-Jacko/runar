/**
 * Phase B/C language + residual feature regtests (TS).
 */

import { describe, it, expect } from 'vitest';
import { compileContract } from './helpers/compile.js';
import { RunarContract } from 'runar-sdk';
import { createFundedWallet } from './helpers/wallet.js';
import { createProvider } from './helpers/node.js';
import { assertOnChainState } from './helpers/onchain.js';

describe('Phase B language (regtest)', () => {
  it('ArithmeticOps', async () => {
    // a=10,b=2: sum=12,diff=8,prod=20,quot=5,rem=0 → total 45
    const artifact = compileContract('integration/contracts/language/ArithmeticOps.runar.ts');
    const contract = new RunarContract(artifact, [45n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);
    await contract.deploy(provider, signer, { satoshis: 5000 });
    const { txid } = await contract.call('verify', [10n, 2n], provider, signer);
    expect(txid).toHaveLength(64);
  });

  it('BooleanLogic', async () => {
    const artifact = compileContract('integration/contracts/language/BooleanLogic.runar.ts');
    const contract = new RunarContract(artifact, [5n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);
    await contract.deploy(provider, signer, { satoshis: 5000 });
    const { txid } = await contract.call('verify', [10n, 1n, false], provider, signer);
    expect(txid).toHaveLength(64);
  });

  it('BitwiseOps', async () => {
    const artifact = compileContract('integration/contracts/language/BitwiseOps.runar.ts');
    const contract = new RunarContract(artifact, [0x0fn, 0x33n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);
    await contract.deploy(provider, signer, { satoshis: 5000 });
    expect((await contract.call('testBitwise', [], provider, signer)).txid).toHaveLength(64);
    // redeploy for second method (stateless, spent)
    const c2 = new RunarContract(artifact, [0x0fn, 0x33n]);
    await c2.deploy(provider, signer, { satoshis: 5000 });
    expect((await c2.call('testShift', [], provider, signer)).txid).toHaveLength(64);
  });

  it('BoundedLoop', async () => {
    // start=1: sum = (1+0)+(1+1)+(1+2)+(1+3)+(1+4)=15
    const artifact = compileContract('integration/contracts/language/BoundedLoop.runar.ts');
    const contract = new RunarContract(artifact, [15n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);
    await contract.deploy(provider, signer, { satoshis: 5000 });
    const { txid } = await contract.call('verify', [1n], provider, signer);
    expect(txid).toHaveLength(64);
  });

  it('ByteStringOps', async () => {
    const artifact = compileContract('integration/contracts/language/ByteStringOps.runar.ts');
    const contract = new RunarContract(artifact, ['01020304']);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);
    await contract.deploy(provider, signer, { satoshis: 5000 });
    const { txid } = await contract.call('verify', [], provider, signer);
    expect(txid).toHaveLength(64);
  });

  it('IfElseSimple', async () => {
    const artifact = compileContract('integration/contracts/language/IfElseSimple.runar.ts');
    const contract = new RunarContract(artifact, [5n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);
    await contract.deploy(provider, signer, { satoshis: 5000 });
    const { txid } = await contract.call('check', [10n, true], provider, signer);
    expect(txid).toHaveLength(64);
  });

  it('TernaryOps', async () => {
    const artifact = compileContract('integration/contracts/language/TernaryOps.runar.ts');
    const contract = new RunarContract(artifact, [7n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);
    await contract.deploy(provider, signer, { satoshis: 5000 });
    const { txid } = await contract.call('verify', [true, 7n, 9n], provider, signer);
    expect(txid).toHaveLength(64);
  });

  it('PropertyInitializers', async () => {
    const artifact = compileContract('integration/contracts/constructs/PropertyInitializers.runar.ts');
    // only maxCount in ctor; count defaults to 0, active to true
    const contract = new RunarContract(artifact, [100n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);
    await contract.deploy(provider, signer, { satoshis: 10_000 });
    const { txid } = await contract.call('increment', [5n], provider, signer);
    expect(txid).toHaveLength(64);
    await assertOnChainState(artifact, txid, 0, { count: 5n });
  });
});

describe('Phase C residual (regtest)', () => {
  it('AsmAnyone', async () => {
    const artifact = compileContract('integration/contracts/unsafe/AsmAnyone.runar.ts');
    const contract = new RunarContract(artifact, []);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);
    await contract.deploy(provider, signer, { satoshis: 5000 });
    const { txid } = await contract.call('unlock', [], provider, signer);
    expect(txid).toHaveLength(64);
  });

  it('CurrentBlockHeight intent', async () => {
    const artifact = compileContract('integration/contracts/intents/CurrentBlockHeight.runar.ts');
    // deadline far in future (block height or timestamp-style; extractLocktime)
    const contract = new RunarContract(artifact, [2_000_000_000n, 0n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);
    await contract.deploy(provider, signer, { satoshis: 10_000 });
    const { txid } = await contract.call('spend', [], provider, signer);
    expect(txid).toHaveLength(64);
    await assertOnChainState(artifact, txid, 0, { count: 1n });
  });

  it('PreimageExtractors', async () => {
    const artifact = compileContract('integration/contracts/crypto/PreimageExtractors.runar.ts');
    const contract = new RunarContract(artifact, [0n]);
    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);
    await contract.deploy(provider, signer, { satoshis: 10_000 });
    const { txid } = await contract.call('tick', [], provider, signer);
    expect(txid).toHaveLength(64);
    await assertOnChainState(artifact, txid, 0, { count: 1n });
  });
});
