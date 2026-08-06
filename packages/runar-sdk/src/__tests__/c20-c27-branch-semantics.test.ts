/**
 * Real-Script execution regression tests for deep-review findings C20 and C27
 * (both P1 funds-safety codegen bugs). Each spend is replayed through @bsv/sdk's
 * `Spend` interpreter (full BIP-143, no node) — the same harness as
 * issues-99-100-stateful-exec.test.ts.
 *
 * C20 — dropped `assert(false)` else in the update-dispatch chain
 *   (`04-anf-lower.ts` collectUpdateBranches / liftBranchUpdateProps).
 *   A method whose branches each end in a single `update_prop` and whose
 *   terminal else is `assert(false)` had that abort silently dropped: a selector
 *   value matching NO branch produced a spendable NO-OP state continuation
 *   instead of aborting. An out-of-range selector must FAIL the script.
 *
 * C27 — N-field reconcile missing on the else-PRESENT path
 *   (`05-stack-lower.ts` lowerIf result reconcile).
 *   With an if/else where BOTH branches write >=2 mutable fields, the reconcile
 *   fell through to `stackMap.push(bindingName)` — one name for N stack results
 *   — corrupting the stackMap so the state serialization emitted against the
 *   wrong slot (OP_NUM2BIN on a byte string) and the continuation was
 *   unspendable. Both branches must produce a spendable continuation encoding
 *   the correct state. The empty-else sibling (issue #99 Bug 1) already worked
 *   and must not regress.
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
    script: buildP2PKHScript(await signer.getPublicKey()),
  });
  return { signer };
}

// Copied VERBATIM from issues-99-100-stateful-exec.test.ts.
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

// A spend that fails the interpreter throws inside Spend.validate rather than
// returning false; treat either signal as "the script rejected the spend".
function spendRejects(tx: Transaction, inputIdx: number, sourceTx: Transaction, sourceOutputIdx: number): boolean {
  try {
    return validateSpend(tx, inputIdx, sourceTx, sourceOutputIdx) === false;
  } catch {
    return true;
  }
}

describe('C20 — terminal assert(false) else must abort an unmatched selector', () => {
  const SRC = `
    class Selector extends StatefulSmartContract {
      a: bigint; b: bigint;
      constructor(a: bigint, b: bigint) { super(a, b); this.a = a; this.b = b; }
      public set(i: bigint, v: bigint) {
        if (i == 0n) { this.a = v; } else if (i == 1n) { this.b = v; } else { assert(false); }
      }
    }
  `;

  /**
   * @param alwaysAck - Only for the out-of-range test below, which
   *   deliberately calls a selector the fixed compiler now aborts on-chain
   *   (dropped `assert(false)` regression). A validating provider refuses
   *   that broadcast before `spendRejects` can inspect and prove the
   *   rejection itself, so that one test opts out explicitly.
   */
  async function deploySelector(alwaysAck = false) {
    const artifact = compileSource(SRC, 'Selector.runar.ts');
    const provider = new MockProvider('testnet', alwaysAck ? { validateBroadcasts: false } : undefined);
    const { signer } = await setupWallet(provider, SIGNER_KEY, 500_000);
    const contract = new RunarContract(artifact, [5n, 7n]);
    await contract.deploy(provider, signer, {});
    const deployTx = Transaction.fromHex(provider.getBroadcastedTxs()[0]!);
    return { contract, provider, signer, deployTx };
  }

  it('in-range selector set(0,99) spends and encodes {a:99,b:7}', async () => {
    const { contract, provider, signer, deployTx } = await deploySelector();
    await contract.call('set', [0n, 99n], provider, signer);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);
    expect(contract.state.a).toBe(99n);
    expect(contract.state.b).toBe(7n);
    expect(validateSpend(callTx, 0, deployTx, 0)).toBe(true);
  });

  it('in-range selector set(1,99) spends and encodes {a:5,b:99}', async () => {
    const { contract, provider, signer, deployTx } = await deploySelector();
    await contract.call('set', [1n, 99n], provider, signer);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);
    expect(contract.state.a).toBe(5n);
    expect(contract.state.b).toBe(99n);
    expect(validateSpend(callTx, 0, deployTx, 0)).toBe(true);
  });

  it('out-of-range selector set(2,99) is REJECTED (no spendable no-op)', async () => {
    const { contract, provider, signer, deployTx } = await deploySelector(true);
    // The SDK's post-state interpreter is permissive (skips asserts), so it
    // still builds a continuation tx (a silent no-op keeping {5,7}). The real
    // script must reject it: the dropped assert(false) has to abort on-chain.
    await contract.call('set', [2n, 99n], provider, signer);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);
    expect(spendRejects(callTx, 0, deployTx, 0)).toBe(true);
  });
});

describe('C27 — else-present multi-field write must produce a spendable continuation', () => {
  const SRC = `
    class TwoField extends StatefulSmartContract {
      a: bigint; b: bigint;
      constructor(a: bigint, b: bigint) { super(a, b); this.a = a; this.b = b; }
      public upd(flag: bigint, x: bigint, y: bigint) {
        if (flag == 0n) { this.a = x; this.b = y; } else { this.a = y; this.b = x; }
      }
    }
  `;

  async function deployTwoField() {
    const artifact = compileSource(SRC, 'TwoField.runar.ts');
    const provider = new MockProvider('testnet');
    const { signer } = await setupWallet(provider, SIGNER_KEY, 500_000);
    const contract = new RunarContract(artifact, [1n, 2n]);
    await contract.deploy(provider, signer, {});
    const deployTx = Transaction.fromHex(provider.getBroadcastedTxs()[0]!);
    return { contract, provider, signer, deployTx };
  }

  it('then-branch upd(0,100,200) spends and encodes {a:100,b:200}', async () => {
    const { contract, provider, signer, deployTx } = await deployTwoField();
    await contract.call('upd', [0n, 100n, 200n], provider, signer);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);
    expect(contract.state.a).toBe(100n);
    expect(contract.state.b).toBe(200n);
    expect(validateSpend(callTx, 0, deployTx, 0)).toBe(true);
  });

  it('else-branch upd(1,100,200) spends and encodes {a:200,b:100}', async () => {
    const { contract, provider, signer, deployTx } = await deployTwoField();
    await contract.call('upd', [1n, 100n, 200n], provider, signer);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);
    expect(contract.state.a).toBe(200n);
    expect(contract.state.b).toBe(100n);
    expect(validateSpend(callTx, 0, deployTx, 0)).toBe(true);
  });
});

describe('C27 control — empty-else multi-field write (issue #99 Bug 1) must not regress', () => {
  const SRC = `
    class TwoFieldNoElse extends StatefulSmartContract {
      a: bigint; b: bigint;
      constructor(a: bigint, b: bigint) { super(a, b); this.a = a; this.b = b; }
      public upd(flag: bigint, x: bigint, y: bigint) {
        if (flag == 0n) { this.a = x; this.b = y; }
      }
    }
  `;

  it('taken branch upd(0,100,200) still spends and encodes {a:100,b:200}', async () => {
    const artifact = compileSource(SRC, 'TwoFieldNoElse.runar.ts');
    const provider = new MockProvider('testnet');
    const { signer } = await setupWallet(provider, SIGNER_KEY, 500_000);
    const contract = new RunarContract(artifact, [1n, 2n]);
    await contract.deploy(provider, signer, {});
    const deployTx = Transaction.fromHex(provider.getBroadcastedTxs()[0]!);

    await contract.call('upd', [0n, 100n, 200n], provider, signer);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);
    expect(contract.state.a).toBe(100n);
    expect(contract.state.b).toBe(200n);
    expect(validateSpend(callTx, 0, deployTx, 0)).toBe(true);
  });
});
