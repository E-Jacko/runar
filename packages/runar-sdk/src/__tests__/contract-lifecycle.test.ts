import { describe, it, expect } from 'vitest';
import { RunarContract } from '../contract.js';
import { MockProvider } from '../providers/mock.js';
import { LocalSigner } from '../signers/local.js';
import { buildP2PKHScript } from '../script-utils.js';
import type { RunarArtifact } from 'runar-ir-schema';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/**
 * Build a minimal artifact for testing the deploy/call lifecycle.
 * Only the fields that RunarContract actually reads are populated.
 */
function makeArtifact(
  overrides: Partial<RunarArtifact> & Pick<RunarArtifact, 'script' | 'abi'>,
): RunarArtifact {
  return {
    version: 'runar-v0.1.0',
    compilerVersion: '0.1.0',
    contractName: 'Test',
    asm: '',
    buildTimestamp: '2026-03-02T00:00:00.000Z',
    ...overrides,
  };
}

// Private key "1" — the smallest valid secp256k1 private key.
const PRIV_KEY =
  '0000000000000000000000000000000000000000000000000000000000000001';

/**
 * Set up a provider pre-loaded with a UTXO for the signer's address.
 * Returns the provider, signer, and the address used.
 */
async function setupFundedProvider(
  satoshis: number,
): Promise<{ provider: MockProvider; signer: LocalSigner; address: string }> {
  const signer = new LocalSigner(PRIV_KEY);
  const address = await signer.getAddress();
  const provider = new MockProvider('testnet');
  provider.addUtxo(address, {
    txid: 'aa'.repeat(32),
    outputIndex: 0,
    satoshis,
    script: buildP2PKHScript(await signer.getPublicKey()),
  });
  return { provider, signer, address };
}

// ---------------------------------------------------------------------------
// Deploy -> Call lifecycle
// ---------------------------------------------------------------------------

describe('RunarContract deploy/call lifecycle', () => {
  it('deploy broadcasts a transaction', async () => {
    const { provider, signer } = await setupFundedProvider(100_000);
    const artifact = makeArtifact({
      script: '51', // OP_TRUE
      abi: {
        constructor: { params: [] },
        methods: [],
      },
    });

    const contract = new RunarContract(artifact, []);
    await contract.deploy(provider, signer, { satoshis: 50_000 });

    const broadcasted = provider.getBroadcastedTxs();
    expect(broadcasted.length).toBe(1);
    // The broadcasted hex should be a valid hex string
    expect(/^[0-9a-f]+$/.test(broadcasted[0]!)).toBe(true);
  });

  it('deploy tracks currentUtxo so subsequent call does not throw "not deployed"', async () => {
    const { provider, signer } = await setupFundedProvider(100_000);
    const artifact = makeArtifact({
      script: '51', // OP_TRUE
      abi: {
        constructor: { params: [] },
        methods: [
          { name: 'spend', params: [], isPublic: true },
        ],
      },
    });

    const contract = new RunarContract(artifact, []);
    await contract.deploy(provider, signer, { satoshis: 50_000 });

    // call() should NOT throw "not deployed" — that means deploy tracked
    // the UTXO correctly. It may fail for other reasons (signing, etc.)
    // but we specifically check for absence of the "not deployed" error.
    await expect(
      contract.call('spend', [], provider, signer),
    ).resolves.toBeDefined();
  });

  it('deploy throws with no UTXOs', async () => {
    const signer = new LocalSigner(PRIV_KEY);
    const provider = new MockProvider('testnet');
    // Deliberately do NOT add any UTXOs to the provider.

    const artifact = makeArtifact({
      script: '51',
      abi: {
        constructor: { params: [] },
        methods: [],
      },
    });

    const contract = new RunarContract(artifact, []);
    await expect(
      contract.deploy(provider, signer, { satoshis: 50_000 }),
    ).rejects.toThrow('no UTXOs');
  });

  it('deploy throws with insufficient funds', async () => {
    const { provider, signer } = await setupFundedProvider(100);
    const artifact = makeArtifact({
      script: '51',
      abi: {
        constructor: { params: [] },
        methods: [],
      },
    });

    const contract = new RunarContract(artifact, []);
    await expect(
      contract.deploy(provider, signer, { satoshis: 50_000 }),
    ).rejects.toThrow('insufficient funds');
  });

  it('call throws on undeployed contract', async () => {
    const { provider, signer } = await setupFundedProvider(100_000);
    const artifact = makeArtifact({
      script: '51',
      abi: {
        constructor: { params: [] },
        methods: [
          { name: 'spend', params: [], isPublic: true },
        ],
      },
    });

    const contract = new RunarContract(artifact, []);
    // Do NOT deploy — call immediately.
    await expect(
      contract.call('spend', [], provider, signer),
    ).rejects.toThrow('not deployed');
  });

  it('call throws on unknown method', async () => {
    const { provider, signer } = await setupFundedProvider(100_000);
    const artifact = makeArtifact({
      script: '51',
      abi: {
        constructor: { params: [] },
        methods: [
          { name: 'spend', params: [], isPublic: true },
        ],
      },
    });

    const contract = new RunarContract(artifact, []);
    await contract.deploy(provider, signer, { satoshis: 50_000 });

    await expect(
      contract.call('nonexistent', [], provider, signer),
    ).rejects.toThrow('not found');
  });

  it('call throws on wrong arg count', async () => {
    const { provider, signer } = await setupFundedProvider(100_000);
    const artifact = makeArtifact({
      script: '51',
      abi: {
        constructor: { params: [] },
        methods: [
          {
            name: 'transfer',
            params: [
              { name: 'to', type: 'Addr' },
              { name: 'amount', type: 'bigint' },
            ],
            isPublic: true,
          },
        ],
      },
    });

    const contract = new RunarContract(artifact, []);
    await contract.deploy(provider, signer, { satoshis: 50_000 });

    // Pass only 1 arg when 2 are expected.
    await expect(
      contract.call('transfer', ['deadbeef'.repeat(5)], provider, signer),
    ).rejects.toThrow('expects 2 args, got 1');
  });
});
