/**
 * Coverage: a stateful method that verifies `checkSig` at the PRIMARY covenant
 * input (input 0) is correctly signed by the SDK's `call()` path and validates
 * on-chain.
 *
 * This fills a real execution-coverage gap. The existing MockProvider-based
 * codeseparator tests build such a call and count pushdata items but never
 * EXECUTE the script, so they cannot distinguish a real signature from a
 * placeholder. That gap is what made GitHub PR #111 look plausible — it claimed
 * `buildStatefulUnlock`'s `if (inputIdx > 0)` guard left input 0 unsigned.
 *
 * In fact the guard is intentional: `prepareCall` is documented to build the tx
 * "without signing the primary contract input's Sig params" — `call()` (and any
 * multi-signer `finalizeCall` caller) signs input 0's user Sig itself at a
 * hardcoded input index 0 (contract.ts ~535) and `finalizeCall` rebuilds input
 * 0's unlock from those real signatures. So the primary input IS signed on the
 * real call path.
 *
 * This test drives the SDK's ACTUAL built call tx through @bsv/sdk's `Spend`
 * interpreter (real `OP_CHECKSIG` + `OP_CODESEPARATOR` + the BUG-100 on-chain
 * preimage check, no node) and asserts it validates — the coverage that would
 * have empirically refuted #111. (Harness mirrors issues-99-100-stateful-exec.)
 */
import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract } from '../contract.js';
import { MockProvider } from '../providers/mock.js';
import { LocalSigner } from '../signers/local.js';
import { Spend, LockingScript, Transaction } from '@bsv/sdk';
import type { RunarArtifact } from 'runar-ir-schema';

const SIGNER_KEY =
  '0000000000000000000000000000000000000000000000000000000000000005';

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
    script: '76a914' + '00'.repeat(20) + '88ac',
  });
  return { signer, pubKeyHex };
}

function validateSpend(
  tx: Transaction,
  inputIdx: number,
  sourceTx: Transaction,
  sourceOutputIdx: number,
): boolean {
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

describe('stateful contract: user checkSig at the primary covenant input (input 0)', () => {
  // A StatefulSmartContract whose method verifies checkSig against a
  // constructor-pinned owner AND continues state — the natural "owner-required
  // state update" shape. The user checkSig runs AFTER the auto-injected
  // OP_CODESEPARATOR.
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

  it('signs input 0 so the on-chain checkSig passes (Spend validates)', async () => {
    const artifact = compileSource(SRC, 'OwnerBump.runar.ts');
    expect(artifact.codeSeparatorIndex).toBeDefined();

    const provider = new MockProvider();
    const wallet = await setupWallet(provider, SIGNER_KEY, 500_000);

    // owner = the signer's OWN pubkey, so the auto-signed sig verifies.
    const contract = new RunarContract(artifact, [wallet.pubKeyHex, 0n]);
    await contract.deploy(provider, wallet.signer, {});
    const deployTx = Transaction.fromHex(provider.getBroadcastedTxs()[0]!);

    // [null] for the Sig param → SDK auto-signs input 0's user Sig.
    await contract.call('bump', [null], provider, wallet.signer);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);

    expect(contract.state.counter).toBe(1n);
    // Real OP_CHECKSIG at input 0 must accept the SDK-supplied signature.
    expect(validateSpend(callTx, 0, deployTx, 0)).toBe(true);
  });
});
