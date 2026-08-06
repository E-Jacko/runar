/**
 * Issue #131 — all-final input sequences defeat CallOptions.locktime.
 *
 * `buildCallTransaction` sets tx.lockTime from options.locktime but hardcoded
 * sequence 0xffffffff on every input. Per BIP-68/consensus, an all-0xffffffff
 * input set makes nLockTime a no-op — a locktime-gated method is script-enforced
 * (via extractLocktime(preimage)) but NOT consensus-enforced. Fix: when a
 * non-zero locktime is set, default every input's sequence to 0xfffffffe
 * (enforceable, non-final) unless the caller overrides with CallOptions.sequence.
 */
import { describe, it, expect } from 'vitest';
import { buildCallTransaction } from '../calling.js';
import { RunarContract } from '../contract.js';
import { MockProvider } from '../providers/mock.js';
import { LocalSigner } from '../signers/local.js';
import { buildP2PKHScript } from '../script-utils.js';
import { compile } from 'runar-compiler';
import { Transaction } from '@bsv/sdk';
import type { RunarArtifact } from 'runar-ir-schema';
import type { UTXO } from '../types.js';

function makeUtxo(satoshis: number, index = 0): UTXO {
  return {
    txid: 'aabbccdd'.repeat(8),
    outputIndex: index,
    satoshis,
    script: '76a914' + '00'.repeat(20) + '88ac',
  };
}

const CHANGE_SCRIPT = '76a914' + 'ff'.repeat(20) + '88ac';

describe('#131 — buildCallTransaction sequence honors locktime', () => {
  it('defaults every input sequence to 0xfffffffe when a non-zero locktime is set', () => {
    const utxo = makeUtxo(100000);
    const additional = [makeUtxo(50000, 1), makeUtxo(30000, 2)];
    const { tx } = buildCallTransaction(
      utxo, '51', undefined, undefined, 'changeaddr', CHANGE_SCRIPT, additional, 100,
      { locktime: 800000 },
    );
    expect(tx.lockTime).toBe(800000);
    expect(tx.inputs.length).toBe(3);
    for (const input of tx.inputs) {
      expect(input.sequence).toBe(0xfffffffe);
    }
  });

  it('keeps sequences at 0xffffffff when no locktime is set (back-compatible)', () => {
    const utxo = makeUtxo(100000);
    const additional = [makeUtxo(50000, 1)];
    const { tx } = buildCallTransaction(
      utxo, '51', undefined, undefined, 'changeaddr', CHANGE_SCRIPT, additional, 100,
    );
    for (const input of tx.inputs) {
      expect(input.sequence).toBe(0xffffffff);
    }
  });

  it('keeps sequences at 0xffffffff when locktime is explicitly 0', () => {
    const utxo = makeUtxo(100000);
    const { tx } = buildCallTransaction(
      utxo, '51', undefined, undefined, 'changeaddr', CHANGE_SCRIPT, undefined, 100,
      { locktime: 0 },
    );
    expect(tx.inputs[0]!.sequence).toBe(0xffffffff);
  });

  it('honors an explicit CallOptions.sequence override on every input', () => {
    const utxo = makeUtxo(100000);
    const additional = [makeUtxo(50000, 1)];
    const { tx } = buildCallTransaction(
      utxo, '51', undefined, undefined, 'changeaddr', CHANGE_SCRIPT, additional, 100,
      { locktime: 800000, sequence: 0x12345678 },
    );
    for (const input of tx.inputs) {
      expect(input.sequence).toBe(0x12345678);
    }
  });
});

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

async function setupWallet(provider: MockProvider, privKey: string, satoshis: number) {
  const signer = new LocalSigner(privKey);
  const address = await signer.getAddress();
  provider.addUtxo(address, {
    txid: privKey.slice(0, 64),
    outputIndex: 0,
    satoshis,
    script: buildP2PKHScript(await signer.getPublicKey()),
  });
  return { signer };
}

describe('#131 — end-to-end stateful call threads locktime -> sequence', () => {
  it('a stateful call with a future locktime produces non-final input sequences', async () => {
    const artifact = compileSource(COUNTER_SRC, 'Counter.runar.ts');
    const provider = new MockProvider('testnet');
    const { signer } = await setupWallet(provider, '00'.repeat(31) + '03', 500_000);
    const contract = new RunarContract(artifact, [0n]);
    await contract.deploy(provider, signer, {});

    await contract.call('increment', [], provider, signer, { locktime: 800000 });
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);

    expect(callTx.lockTime).toBe(800000);
    for (const input of callTx.inputs) {
      expect(input.sequence).toBe(0xfffffffe);
    }
  });
});
