/**
 * Deep-review finding G1 (P1) — spending a method that calls
 * `this.addRawOutput(...)` via the SDK must build a transaction whose outputs
 * match the covenant's `hashOutputs` continuation, or input 0's OP_VERIFY fails
 * and the funds are stuck.
 *
 * The shipped example `RawOutputTest.sendToScript` emits, in SOURCE order:
 *
 *     this.addRawOutput(1000n, scriptBytes);  // raw output FIRST
 *     this.count = this.count + 1n;
 *     this.addOutput(0n, this.count);          // state continuation SECOND (0 sats)
 *
 * The compiler folds BOTH into the continuation `hashOutputs` in that order, so
 * the on-chain output layout the covenant reconstructs is
 * `[raw(1000, scriptBytes)] [stateContinuation(0)] [change]`. The SDK must emit
 * exactly that ordering; emitting only the state continuation (the pre-fix
 * behaviour) mismatches hashOutputs → the auto-injected state-check OP_VERIFY
 * rejects.
 *
 * This test deploys + calls `sendToScript` via MockProvider, then replays input
 * 0's unlocking script through @bsv/sdk's Spend interpreter (same harness as
 * issues #99/#100/#116/#123) to PROVE the covenant verifies, and asserts the
 * built tx's outputs are in the required order.
 */
import { describe, it, expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { compile } from 'runar-compiler';
import { RunarContract } from '../contract.js';
import { MockProvider } from '../providers/mock.js';
import { LocalSigner } from '../signers/local.js';
import { Spend, LockingScript, UnlockingScript, Transaction } from '@bsv/sdk';
import type { RunarArtifact } from 'runar-ir-schema';

const DEPLOYER_KEY = '0000000000000000000000000000000000000000000000000000000000000003';
const CALLER_KEY = '0000000000000000000000000000000000000000000000000000000000000004';

// The caller-supplied raw locking script: a plain P2PKH (76a914 <20 bytes> 88ac).
const RAW_SCRIPT = '76a914' + 'ab'.repeat(20) + '88ac';

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

async function fundedSigner(provider: MockProvider, privKey: string, satoshis: number) {
  const signer = new LocalSigner(privKey);
  const address = await signer.getAddress();
  provider.addUtxo(address, {
    txid: privKey.slice(0, 64),
    outputIndex: 0,
    satoshis,
    script: '76a914' + '00'.repeat(20) + '88ac',
  });
  return signer;
}

/** Replay a single input through @bsv/sdk's Spend interpreter. */
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

describe('G1 (P1) — addRawOutput spend builds a covenant-valid tx in source order', () => {
  const SRC = readFileSync(
    new URL('../../../../examples/ts/add-raw-output/RawOutputTest.runar.ts', import.meta.url),
    'utf8',
  );

  it('deploy + call(sendToScript) validates through Spend, outputs are [raw][state][change]', async () => {
    const artifact = compileSource(SRC, 'RawOutputTest.runar.ts');

    const provider = new MockProvider();
    const deployer = await fundedSigner(provider, DEPLOYER_KEY, 500_000);
    const caller = await fundedSigner(provider, CALLER_KEY, 500_000);

    const contract = new RunarContract(artifact, [0n]);
    await contract.deploy(provider, deployer, { satoshis: 50_000 });
    const deployTx = Transaction.fromHex(provider.getBroadcastedTxs()[0]!);

    await contract.call('sendToScript', [RAW_SCRIPT], provider, caller);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);

    // State advanced 0 -> 1 (this.count = this.count + 1n).
    expect(contract.state.count).toBe(1n);

    // --- The covenant proof: input 0's OP_PUSH_TX + hashOutputs OP_VERIFY. ---
    expect(validateSpend(callTx, 0, deployTx, 0)).toBe(true);

    // --- Output ordering: [0] raw, [1] state continuation, [2] change. ---
    expect(callTx.outputs.length).toBe(3);

    // [0] raw output: 1000 sats, script === the caller-supplied bytes.
    expect(callTx.outputs[0]!.satoshis).toBe(1000);
    expect(callTx.outputs[0]!.lockingScript.toHex()).toBe(RAW_SCRIPT);

    // [1] state continuation: 0 sats, codePart + OP_RETURN (6a) + serialized count.
    expect(callTx.outputs[1]!.satoshis).toBe(0);
    const stateScript = callTx.outputs[1]!.lockingScript.toHex();
    expect(stateScript).not.toBe(RAW_SCRIPT);
    expect(stateScript).toContain('6a');
    // The SDK tracks the continuation as the next spendable UTXO at index 1.
    expect(contract.currentUtxo?.outputIndex).toBe(1);
    expect(contract.currentUtxo?.script).toBe(stateScript);

    // [2] change: a P2PKH output (76a9…88ac) carrying the remainder.
    const changeScript = callTx.outputs[2]!.lockingScript.toHex();
    expect(changeScript.startsWith('76a914')).toBe(true);
    expect(changeScript.endsWith('88ac')).toBe(true);
    expect(callTx.outputs[2]!.satoshis!).toBeGreaterThan(0);
  });
});
