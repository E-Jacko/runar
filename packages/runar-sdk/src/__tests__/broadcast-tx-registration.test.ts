/**
 * Audit finding C4 — `MockProvider.broadcast()` never registered the tx it
 * accepted, so every post-broadcast assertion was vacuous.
 *
 * `broadcast()` stored the raw hex in `rawTransactions` and the outputs in
 * `knownOutpoints`, but never called `this.transactions.set(...)`. Since
 * `getTransaction()` reads ONLY `this.transactions`, every lookup of a
 * just-broadcast txid threw `MockProvider: transaction <id> not found`.
 *
 * `RunarContract.deploy()` / `finalizeCall()` swallow that throw with a
 * `console.warn` and return an EMPTY SHELL (`inputs: []`, `outputs: []`)
 * that still looks like a real `TransactionData`. So every
 * `result.tx.outputs` assertion in the suite was asserting against `[]`.
 *
 * Two things are locked down here:
 *   1. `MockProvider.broadcast()` registers the tx, so `getTransaction()`
 *      resolves it with real inputs/outputs (and still throws for genuinely
 *      unknown txids).
 *   2. The `contract.ts` post-broadcast fallback no longer fabricates an
 *      empty shell: when a provider's `getTransaction()` legitimately fails
 *      (a real node can 404 a tx it has not indexed yet), the returned
 *      `TransactionData` is derived from the local transaction that was
 *      actually broadcast.
 */
import { describe, it, expect, vi, afterEach } from 'vitest';
import { compile } from 'runar-compiler';
import { Transaction as BsvTransaction, LockingScript, UnlockingScript } from '@bsv/sdk';
import { MockProvider } from '../providers/mock.js';
import { RunarContract } from '../contract.js';
import { LocalSigner } from '../signers/local.js';
import { buildP2PKHScript } from '../script-utils.js';
import type { Provider } from '../providers/provider.js';
import type { RunarArtifact } from 'runar-ir-schema';
import type { TransactionData, UTXO } from '../types.js';

const FUNDING_TXID = '11'.repeat(32);
const SIGNER_KEY = '0000000000000000000000000000000000000000000000000000000000000003';

/** OP_TRUE-funded single-input, two-output tx. Pair with
 * `registerFunding()` so the default-on C8 broadcast validation has a known
 * input to run `Spend.validate()` against. */
function makeBsvTx(): BsvTransaction {
  const tx = new BsvTransaction();
  tx.addInput({
    sourceTXID: FUNDING_TXID,
    sourceOutputIndex: 0,
    unlockingScript: new UnlockingScript(),
    sequence: 0xfffffffe,
  });
  tx.addOutput({ satoshis: 60000, lockingScript: LockingScript.fromHex('51') });
  tx.addOutput({ satoshis: 30000, lockingScript: LockingScript.fromHex('76a914' + 'ab'.repeat(20) + '88ac') });
  tx.lockTime = 0;
  return tx;
}

function registerFunding(provider: MockProvider): void {
  provider.addContractUtxo('c4-funding', {
    txid: FUNDING_TXID,
    outputIndex: 0,
    satoshis: 100000,
    script: '51', // OP_TRUE
  });
}

function compileSource(source: string, fileName: string): RunarArtifact {
  const result = compile(source, { fileName });
  if (!result.artifact) {
    const errors = (result.diagnostics || [])
      .filter((d: { severity: string }) => d.severity === 'error')
      .map((d: { message: string }) => d.message);
    throw new Error(`Compile failed: ${errors.join('; ')}`);
  }
  return result.artifact;
}

async function setupWallet(provider: MockProvider, privKey: string, satoshis: number) {
  const signer = new LocalSigner(privKey);
  const address = await signer.getAddress();
  const pubKeyHex = await signer.getPublicKey();
  provider.addUtxo(address, {
    txid: privKey.slice(0, 64),
    outputIndex: 0,
    satoshis,
    script: buildP2PKHScript(pubKeyHex),
  });
  return signer;
}

const COUNTER_SRC = `
  class C4Counter extends StatefulSmartContract {
    count: bigint;
    constructor(count: bigint) { super(count); this.count = count; }
    public increment(): void { this.count = this.count + 1n; }
  }
`;

afterEach(() => {
  vi.restoreAllMocks();
});

// ---------------------------------------------------------------------------
// 1. Provider level
// ---------------------------------------------------------------------------

describe('C4: MockProvider.broadcast registers the broadcast transaction', () => {
  it('getTransaction resolves a broadcast tx with populated inputs and outputs', async () => {
    const provider = new MockProvider('testnet');
    registerFunding(provider);
    const tx = makeBsvTx();

    const txid = await provider.broadcast(tx);

    // Before the fix this rejected with "MockProvider: transaction <id> not found".
    const data = await provider.getTransaction(txid);

    expect(data.txid).toBe(txid);
    expect(data.version).toBe(tx.version);
    expect(data.locktime).toBe(tx.lockTime);
    expect(data.raw).toBe(tx.toHex());

    expect(data.inputs).toHaveLength(1);
    expect(data.inputs[0]!.txid).toBe(FUNDING_TXID);
    expect(data.inputs[0]!.outputIndex).toBe(0);
    expect(data.inputs[0]!.sequence).toBe(0xfffffffe);

    expect(data.outputs).toHaveLength(2);
    expect(data.outputs[0]!.satoshis).toBe(60000);
    expect(data.outputs[0]!.script).toBe('51');
    expect(data.outputs[1]!.satoshis).toBe(30000);
    expect(data.outputs[1]!.script).toBe('76a914' + 'ab'.repeat(20) + '88ac');
  });

  it('still throws for a txid that was never broadcast or injected', async () => {
    const provider = new MockProvider('testnet');
    registerFunding(provider);
    await provider.broadcast(makeBsvTx());

    await expect(provider.getTransaction('ff'.repeat(32))).rejects.toThrow('not found');
  });
});

// ---------------------------------------------------------------------------
// 2. Contract level — the vacuous-assertion surface
// ---------------------------------------------------------------------------

describe('C4: RunarContract deploy/call return a populated tx via MockProvider', () => {
  it('deploy() and call() never hit the post-broadcast fallback warning', async () => {
    const warn = vi.spyOn(console, 'warn').mockImplementation(() => {});
    const artifact = compileSource(COUNTER_SRC, 'C4Counter.runar.ts');
    const provider = new MockProvider('testnet');
    const signer = await setupWallet(provider, SIGNER_KEY, 500_000);
    const contract = new RunarContract(artifact, [0n]);

    const deployed = await contract.deploy(provider, signer, {});
    expect(deployed.tx.inputs.length).toBeGreaterThan(0);
    expect(deployed.tx.outputs.length).toBeGreaterThan(0);
    expect(deployed.tx.txid).toBe(deployed.txid);

    const called = await contract.call('increment', [], provider, signer);
    expect(called.tx.inputs.length).toBeGreaterThan(0);
    expect(called.tx.outputs.length).toBeGreaterThan(0);
    expect(called.tx.txid).toBe(called.txid);

    const swallowed = warn.mock.calls.filter(
      (c) => typeof c[0] === 'string' && c[0].includes('Failed to fetch transaction after broadcast'),
    );
    expect(swallowed).toEqual([]);
  });

  it('call() returns outputs that match the transaction actually broadcast', async () => {
    const artifact = compileSource(COUNTER_SRC, 'C4Counter.runar.ts');
    const provider = new MockProvider('testnet');
    const signer = await setupWallet(provider, SIGNER_KEY, 500_000);
    const contract = new RunarContract(artifact, [0n]);
    await contract.deploy(provider, signer, {});

    const called = await contract.call('increment', [], provider, signer);
    const broadcast = BsvTransaction.fromHex(provider.getBroadcastedTxs().at(-1)!);

    expect(called.tx.outputs).toHaveLength(broadcast.outputs.length);
    for (let i = 0; i < broadcast.outputs.length; i++) {
      expect(called.tx.outputs[i]!.satoshis).toBe(broadcast.outputs[i]!.satoshis);
      expect(called.tx.outputs[i]!.script).toBe(broadcast.outputs[i]!.lockingScript.toHex());
    }
    expect(called.tx.inputs).toHaveLength(broadcast.inputs.length);
    expect(called.tx.raw).toBe(broadcast.toHex());
  });
});

// ---------------------------------------------------------------------------
// 3. The fallback itself must not fabricate an empty shell
// ---------------------------------------------------------------------------

/** A provider whose `getTransaction` always fails — the shape a real node
 * presents when a just-broadcast tx has not been indexed yet. Delegates
 * everything else to a real `MockProvider`. */
class UnindexedProvider implements Provider {
  constructor(private readonly inner: MockProvider) {}
  async getTransaction(txid: string): Promise<TransactionData> {
    throw new Error(`not indexed yet: ${txid}`);
  }
  broadcast(tx: BsvTransaction): Promise<string> {
    return this.inner.broadcast(tx);
  }
  getUtxos(address: string): Promise<UTXO[]> {
    return this.inner.getUtxos(address);
  }
  getContractUtxo(scriptHash: string): Promise<UTXO | null> {
    return this.inner.getContractUtxo(scriptHash);
  }
  getNetwork(): 'mainnet' | 'testnet' {
    return this.inner.getNetwork();
  }
  getFeeRate(): Promise<number> {
    return this.inner.getFeeRate();
  }
  getRawTransaction(txid: string): Promise<string> {
    return this.inner.getRawTransaction(txid);
  }
}

describe('C4: post-broadcast fallback is derived from the broadcast tx, not empty', () => {
  it('deploy() and call() still report real inputs/outputs when getTransaction fails', async () => {
    const warn = vi.spyOn(console, 'warn').mockImplementation(() => {});
    const artifact = compileSource(COUNTER_SRC, 'C4Counter.runar.ts');
    const inner = new MockProvider('testnet');
    const signer = await setupWallet(inner, SIGNER_KEY, 500_000);
    const provider = new UnindexedProvider(inner);
    const contract = new RunarContract(artifact, [0n]);

    const deployed = await contract.deploy(provider, signer, {});
    const deployTx = BsvTransaction.fromHex(inner.getBroadcastedTxs()[0]!);
    expect(deployed.tx.inputs).toHaveLength(deployTx.inputs.length);
    expect(deployed.tx.outputs).toHaveLength(deployTx.outputs.length);
    expect(deployed.tx.raw).toBe(deployTx.toHex());

    const called = await contract.call('increment', [], provider, signer);
    const callTx = BsvTransaction.fromHex(inner.getBroadcastedTxs()[1]!);
    expect(called.tx.inputs).toHaveLength(callTx.inputs.length);
    expect(called.tx.outputs).toHaveLength(callTx.outputs.length);
    for (let i = 0; i < callTx.outputs.length; i++) {
      expect(called.tx.outputs[i]!.satoshis).toBe(callTx.outputs[i]!.satoshis);
      expect(called.tx.outputs[i]!.script).toBe(callTx.outputs[i]!.lockingScript.toHex());
    }

    // The lookup failure must stay visible — it is degraded data, not a
    // confirmed transaction.
    const swallowed = warn.mock.calls.filter(
      (c) => typeof c[0] === 'string' && c[0].includes('Failed to fetch transaction after broadcast'),
    );
    expect(swallowed.length).toBe(2);
  });
});
