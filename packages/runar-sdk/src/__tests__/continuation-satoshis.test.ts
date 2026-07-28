/**
 * Deep-review follow-on (SDK funds bug, separate from C20/C27): the call path
 * must build a state continuation at the amount the contract's explicit
 * `this.addOutput(<sats>, ...)` specifies — NOT default it to the input value.
 *
 * The ANF interpreter already records the addOutput satoshis (finding G1 reads
 * it, but ONLY on the raw-output-present branch). A stateful method whose
 * continuation is `addOutput(1000, ...)` therefore had its continuation built
 * at the input value (e.g. 1 sat), so the covenant's hashOutputs binding
 * rejected the spend — funds stranded. Each spend is replayed through
 * @bsv/sdk's real `Spend` interpreter.
 */
import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract } from '../contract.js';
import { MockProvider } from '../providers/mock.js';
import { LocalSigner } from '../signers/local.js';
import { Spend, LockingScript, Transaction } from '@bsv/sdk';
import type { RunarArtifact } from 'runar-ir-schema';

const SIGNER_KEY = '0000000000000000000000000000000000000000000000000000000000000003';

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
  provider.addUtxo(address, {
    txid: privKey.slice(0, 64),
    outputIndex: 0,
    satoshis,
    script: '76a914' + '00'.repeat(20) + '88ac',
  });
  return { signer };
}

function validateSpend(tx: Transaction, inputIdx: number, sourceTx: Transaction, sourceOutputIdx: number): boolean {
  const input = tx.inputs[inputIdx]!;
  const sourceOutput = sourceTx.outputs[sourceOutputIdx]!;
  const spend = new Spend({
    sourceTXID: input.sourceTXID!,
    sourceOutputIndex: input.sourceOutputIndex,
    sourceSatoshis: sourceOutput.satoshis!,
    lockingScript: sourceOutput.lockingScript,
    transactionVersion: tx.version,
    otherInputs: tx.inputs
      .filter((_: unknown, i: number) => i !== inputIdx)
      .map((inp: { sourceOutputIndex: number; sourceTXID?: string; sequence?: number }, idx: number) => ({
        inputIndex: idx >= inputIdx ? idx + 1 : idx,
        sourceOutputIndex: inp.sourceOutputIndex,
        sourceTXID: inp.sourceTXID!,
        sequence: inp.sequence,
        unlockingScript: undefined as never,
        sourceSatoshis: 0,
        lockingScript: LockingScript.fromHex(''),
      })),
    outputs: tx.outputs.map((o: { lockingScript: unknown; satoshis?: number }) => ({
      lockingScript: o.lockingScript,
      satoshis: o.satoshis,
    })),
    unlockingScript: input.unlockingScript,
    inputIndex: inputIdx,
    inputSequence: input.sequence,
    lockTime: tx.lockTime,
  });
  return spend.validate();
}

describe('SDK derives state-continuation satoshis from an explicit addOutput(N)', () => {
  // A stateful method whose ONLY output is `this.addOutput(1000, this.count)`.
  const SRC = `
    class SatCounter extends StatefulSmartContract {
      count: bigint;
      constructor(count: bigint) { super(count); this.count = count; }
      public inc() {
        this.count = this.count + 1n;
        this.addOutput(1000n, this.count);
      }
    }
  `;

  async function deploy() {
    const artifact = compileSource(SRC, 'SatCounter.runar.ts');
    const provider = new MockProvider();
    const { signer } = await setupWallet(provider, SIGNER_KEY, 500_000);
    const contract = new RunarContract(artifact, [5n]);
    // Deploy at the default (1 sat); the call's addOutput(1000) must OVERRIDE it.
    await contract.deploy(provider, signer, {});
    const deployTx = Transaction.fromHex(provider.getBroadcastedTxs()[0]!);
    return { contract, provider, signer, deployTx };
  }

  it('builds the continuation at 1000 sats (not the input value) and spends', async () => {
    const { contract, provider, signer, deployTx } = await deploy();
    // NO options.satoshis — the SDK must derive 1000 from the addOutput.
    await contract.call('inc', [], provider, signer);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);
    expect(contract.state.count).toBe(6n);
    // Continuation output (index 0) must carry the addOutput amount.
    expect(callTx.outputs[0]!.satoshis).toBe(1000);
    // And the covenant must accept it on the real script interpreter.
    expect(validateSpend(callTx, 0, deployTx, 0)).toBe(true);
  });
});
