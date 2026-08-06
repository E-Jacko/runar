/**
 * Real-Script execution regression tests for GitHub issues #99 (Bug 1) and #100.
 *
 * Drives a full stateful continuation spend offline through @bsv/sdk's Spend
 * interpreter (no node), exercising the paths the byte-parity conformance suite
 * never reached:
 *   - #99 Bug 1: a spend that TAKES the update branch of a conditional write of
 *     >=2 state fields (previously unspendable: OP_NUM2BIN "encoding impossible").
 *   - #100: a TERMINAL method reading a ByteString state field AFTER an on-chain
 *     update (live != initial) — must read the live value, not the deploy-time one.
 */
import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract } from '../contract.js';
import { MockProvider } from '../providers/mock.js';
import { LocalSigner } from '../signers/local.js';
import { buildP2PKHScript } from '../script-utils.js';
import { Spend, LockingScript, Transaction } from '@bsv/sdk';
import type { RunarArtifact } from 'runar-ir-schema';

const SIGNER_KEY = '0000000000000000000000000000000000000000000000000000000000000003';
const ADDR_A = 'aa'.repeat(20);
const ADDR_B = 'bb'.repeat(20);

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
  return { signer, pubKeyHex };
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

describe('#99 Bug 1 — conditional multi-field state write spendability', () => {
  const SRC = `
    class CondWrite2 extends StatefulSmartContract {
      best: bigint;
      who: Addr;
      constructor(best: bigint, who: Addr) { super(best, who); this.best = best; this.who = who; }
      public offer(v: bigint, addr: Addr): void {
        if (v < this.best) { this.best = v; this.who = addr; }
      }
    }
  `;

  it('spend that TAKES the update branch validates (best 100 -> offer 5)', async () => {
    const artifact = compileSource(SRC, 'CondWrite2.runar.ts');
    const provider = new MockProvider('testnet');
    const wallet = await setupWallet(provider, SIGNER_KEY, 500_000);
    const contract = new RunarContract(artifact, [100n, ADDR_A]);
    await contract.deploy(provider, wallet.signer, {});
    const deployTx = Transaction.fromHex(provider.getBroadcastedTxs()[0]!);

    await contract.call('offer', [5n, ADDR_B], provider, wallet.signer);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);

    expect(contract.state.best).toBe(5n);
    expect(validateSpend(callTx, 0, deployTx, 0)).toBe(true);
  });

  it('spend that SKIPS the update branch validates (best 3 -> offer 5)', async () => {
    const artifact = compileSource(SRC, 'CondWrite2.runar.ts');
    const provider = new MockProvider('testnet');
    const wallet = await setupWallet(provider, SIGNER_KEY, 500_000);
    const contract = new RunarContract(artifact, [3n, ADDR_A]);
    await contract.deploy(provider, wallet.signer, {});
    const deployTx = Transaction.fromHex(provider.getBroadcastedTxs()[0]!);

    await contract.call('offer', [5n, ADDR_B], provider, wallet.signer);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);

    expect(contract.state.best).toBe(3n);
    expect(validateSpend(callTx, 0, deployTx, 0)).toBe(true);
  });
});

describe('#100 — terminal method reads live ByteString state after on-chain update', () => {
  const SRC = `
    class StateRead extends StatefulSmartContract {
      s: ByteString;
      constructor(s: ByteString) { super(s); this.s = s; }
      public update(ns: ByteString): void { this.s = ns; }
      public termCheck(expected: ByteString): void { assert(substr(this.s, 8n, 20n) === expected); }
    }
  `;
  const INIT = '00'.repeat(8) + 'cc'.repeat(20); // [8:28] = cc*20
  const LIVE = '11'.repeat(8) + 'dd'.repeat(20); // [8:28] = dd*20

  it('terminal read after update sees the LIVE slice, not the deploy-time initial', async () => {
    const artifact = compileSource(SRC, 'StateRead.runar.ts');
    const provider = new MockProvider('testnet');
    const wallet = await setupWallet(provider, SIGNER_KEY, 500_000);
    const contract = new RunarContract(artifact, [INIT]);
    await contract.deploy(provider, wallet.signer, {});

    await contract.call('update', [LIVE], provider, wallet.signer);
    const updTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);

    await contract.call('termCheck', ['dd'.repeat(20)], provider, wallet.signer);
    const termTx = Transaction.fromHex(provider.getBroadcastedTxs()[2]!);
    expect(validateSpend(termTx, 0, updTx, 0)).toBe(true);
  });
});
