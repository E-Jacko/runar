/**
 * Issue #133 — call() sweeps ALL wallet UTXOs as funding inputs.
 *
 * The non-terminal call path fetched provider.getUtxos(address) and forwarded
 * every UTXO (minus the contract UTXO) as funding — no coin selection (unlike
 * deploy, which uses selectUtxos). A wallet with N spare coins produced an
 * (N+1)-input tx regardless of how little funding the call actually needed.
 * Fix: smallest-sufficient largest-first selection via selectUtxos, plus a
 * CallOptions.maxFundingInputs cap.
 */
import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract } from '../contract.js';
import { MockProvider } from '../providers/mock.js';
import { LocalSigner } from '../signers/local.js';
import { Transaction } from '@bsv/sdk';
import type { RunarArtifact } from 'runar-ir-schema';

const COUNTER_SRC = `
  class Counter extends StatefulSmartContract {
    count: bigint;
    constructor(count: bigint) { super(count); this.count = count; }
    public increment(): void { this.count = this.count + 1n; }
  }
`;

function compileSource(source: string, fileName: string): RunarArtifact {
  const result = compile(source, { fileName });
  if (!result.artifact) throw new Error('compile failed');
  return result.artifact;
}

const PRIV_KEY = '00'.repeat(31) + '03';

async function setupWallet(provider: MockProvider, utxoSats: number[]) {
  const signer = new LocalSigner(PRIV_KEY);
  const address = await signer.getAddress();
  utxoSats.forEach((sats, i) => {
    provider.addUtxo(address, {
      txid: (i + 1).toString(16).padStart(2, '0').repeat(32),
      outputIndex: 0,
      satoshis: sats,
      script: '76a914' + '00'.repeat(20) + '88ac',
    });
  });
  return { signer };
}

describe('#133 — call() selects smallest-sufficient funding, not all UTXOs', () => {
  it('a call with 3 spare 100k UTXOs builds a 2-input tx (1 contract + 1 funding), NOT 4', async () => {
    const artifact = compileSource(COUNTER_SRC, 'Counter.runar.ts');
    const provider = new MockProvider();
    const { signer } = await setupWallet(provider, [100_000, 100_000, 100_000]);
    const contract = new RunarContract(artifact, [0n]);
    await contract.deploy(provider, signer, {});

    await contract.call('increment', [], provider, signer);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);

    expect(contract.state.count).toBe(1n);
    // 1 contract input + exactly 1 funding input = 2. The bug swept all 3.
    expect(callTx.inputs.length).toBe(2);
  });

  it('maxFundingInputs caps the funding inputs and errors clearly when it cannot cover', async () => {
    const artifact = compileSource(COUNTER_SRC, 'Counter.runar.ts');
    const provider = new MockProvider();
    // Small coins force >1 funding input for a value-increasing continuation.
    const { signer } = await setupWallet(provider, [3_000, 3_000, 3_000, 3_000]);
    const contract = new RunarContract(artifact, [0n]);
    await contract.deploy(provider, signer, { satoshis: 1_000 });

    // Continuation grows to 5000 sats => funding must cover ~4000 + fee, which
    // needs 2 of the 3000-sat coins. Cap at 1 => must throw.
    await expect(
      contract.call('increment', [], provider, signer, { satoshis: 5_000, maxFundingInputs: 1 }),
    ).rejects.toThrow(/maxFundingInputs/);
  });

  it('honors a maxFundingInputs cap that is sufficient', async () => {
    const artifact = compileSource(COUNTER_SRC, 'Counter.runar.ts');
    const provider = new MockProvider();
    const { signer } = await setupWallet(provider, [3_000, 3_000, 3_000, 3_000]);
    const contract = new RunarContract(artifact, [0n]);
    await contract.deploy(provider, signer, { satoshis: 1_000 });

    await contract.call('increment', [], provider, signer, { satoshis: 5_000, maxFundingInputs: 3 });
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);
    // 1 contract + 2 funding coins to cover the 4000-sat shortfall.
    expect(callTx.inputs.length).toBe(3);
  });
});
