/**
 * Deep-review finding C29 (P2): `PreparedCall` hands the caller a live,
 * mutable `@bsv/sdk` `Transaction` (`prepared.tx`) with no consume guard.
 * Nothing stops the SAME `PreparedCall` from being finalized twice —
 * `finalizeCall` mutates `prepared.tx.inputs[0].unlockingScript` in place
 * and broadcasts, so a second call rebuilds and rebroadcasts against a tx
 * object that has already been consumed (and, on a real network, already
 * spent) by the first call — a tx whose signatures no longer correspond to
 * a fresh, still-live UTXO.
 *
 * Fix: track consumed `PreparedCall`s by object identity and throw a clear
 * error on any second `finalizeCall()` attempt.
 */
import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract } from '../contract.js';
import { MockProvider } from '../providers/mock.js';
import { LocalSigner } from '../signers/local.js';
import type { RunarArtifact } from 'runar-ir-schema';

const SIGNER_KEY = '0000000000000000000000000000000000000000000000000000000000000006';

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

const SRC = `
  import { StatefulSmartContract, assert, checkSig } from 'runar-lang';
  import type { PubKey, Sig } from 'runar-lang';

  class OwnerBump extends StatefulSmartContract {
    readonly owner: PubKey;
    counter: bigint;
    constructor(owner: PubKey, counter: bigint) {
      super(owner, counter);
      this.owner = owner;
      this.counter = counter;
    }
    public bump(sig: Sig): void {
      assert(checkSig(sig, this.owner));
      this.counter = this.counter + 1n;
    }
  }
`;

async function deployOwnerBump() {
  const artifact = compileSource(SRC, 'OwnerBump.runar.ts');
  const provider = new MockProvider();
  const signer = new LocalSigner(SIGNER_KEY);
  const address = await signer.getAddress();
  const pubKeyHex = await signer.getPublicKey();
  provider.addUtxo(address, {
    txid: SIGNER_KEY.slice(0, 64),
    outputIndex: 0,
    satoshis: 500_000,
    script: '76a914' + '00'.repeat(20) + '88ac',
  });
  const contract = new RunarContract(artifact, [pubKeyHex, 0n]);
  contract.connect(provider, signer);
  await contract.deploy(provider, signer, {});
  return { contract, provider, signer };
}

describe('C29 — PreparedCall consume guard', () => {
  it('finalizing the same PreparedCall twice throws clearly on the second attempt', async () => {
    const { contract, signer } = await deployOwnerBump();

    const prepared = await contract.prepareCall('bump', [null]);
    const sigSubscript = contract.getSubscriptForSigning(prepared._contractUtxo.script, 0);
    const sig = await signer.sign(
      prepared.tx.toHex(), 0, sigSubscript, prepared._contractUtxo.satoshis,
    );

    await contract.finalizeCall(prepared, { 0: sig });
    expect(contract.state.counter).toBe(1n);

    await expect(contract.finalizeCall(prepared, { 0: sig })).rejects.toThrow(/C29|already.*finaliz|consumed/i);
  });

  it('a fresh PreparedCall for a NEW call still finalizes normally', async () => {
    const { contract, signer } = await deployOwnerBump();

    const prepared1 = await contract.prepareCall('bump', [null]);
    const sig1 = await signer.sign(
      prepared1.tx.toHex(), 0,
      contract.getSubscriptForSigning(prepared1._contractUtxo.script, 0),
      prepared1._contractUtxo.satoshis,
    );
    await contract.finalizeCall(prepared1, { 0: sig1 });
    expect(contract.state.counter).toBe(1n);

    const prepared2 = await contract.prepareCall('bump', [null]);
    const sig2 = await signer.sign(
      prepared2.tx.toHex(), 0,
      contract.getSubscriptForSigning(prepared2._contractUtxo.script, 0),
      prepared2._contractUtxo.satoshis,
    );
    await contract.finalizeCall(prepared2, { 0: sig2 });
    expect(contract.state.counter).toBe(2n);
  });
});
