/**
 * Issue #130 — a method param that shadows a mutable state property must
 * compile to the PARAM value (the witness arg), not the stale deserialized
 * on-chain state.
 *
 * Root cause: declared method params were never registered as params in the
 * ANF lowering context (only their types were), so a bare identifier that
 * collides with a property name fell through to `load_prop` (old on-chain
 * state) instead of `load_param` (the witness value).
 *
 * The SDK's ANF interpreter masks the bug (its env overwrites the prop slot
 * with the param value), so it builds the continuation from the PARAM (22).
 * The on-chain script's `load_prop` re-uses the deserialized OLD state (11),
 * so the continuation-hash check fails and the spend is INVALID today. After
 * the fix the script reads the param (22) and the spend validates.
 *
 * This exercises the single-output stateful continuation (`this.x = x`), which
 * lowers the shadowed identifier through the exact same `lowerIdentifier` path
 * that the addOutput positional value uses. The IR-level addOutput direction
 * is pinned separately in the compiler's 04-anf-lower tests.
 */
import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract } from '../contract.js';
import { MockProvider } from '../providers/mock.js';
import { LocalSigner } from '../signers/local.js';
import { Spend, LockingScript, Transaction } from '@bsv/sdk';
import type { RunarArtifact } from 'runar-ir-schema';

const SIGNER_KEY = '0000000000000000000000000000000000000000000000000000000000000003';

// `balance` (mutable state) shadowed by the `retire` param `balance`.
const SRC = `
  class ShadowRepro extends StatefulSmartContract {
    balance: bigint;
    constructor(balance: bigint) { super(balance); this.balance = balance; }
    public retire(balance: bigint): void {
      this.balance = balance;
    }
  }
`;

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

describe('#130 — param shadowing a mutable state property', () => {
  it('retire(balance=22) commits the PARAM value, not the old state 11', async () => {
    const artifact = compileSource(SRC, 'ShadowRepro.runar.ts');
    const provider = new MockProvider();
    const wallet = await setupWallet(provider, SIGNER_KEY, 500_000);

    const contract = new RunarContract(artifact, [11n]);
    await contract.deploy(provider, wallet.signer, {});
    const deployTx = Transaction.fromHex(provider.getBroadcastedTxs()[0]!);

    await contract.call('retire', [22n], provider, wallet.signer);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);

    // The SDK computes the new state from the param (22).
    expect(contract.state.balance).toBe(22n);
    // The on-chain script must agree: with the bug it re-commits the old
    // deserialized state (11), so the continuation hash fails and the spend
    // is INVALID; the fix makes the script read the param (22) → VALID.
    expect(validateSpend(callTx, 0, deployTx, 0)).toBe(true);
  });
});
