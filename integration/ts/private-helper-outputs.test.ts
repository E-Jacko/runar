/**
 * PrivateHelperOutputs integration test — 2026-04-30 audit regression
 * (F1 + F3).
 *
 * The contract delegates state mutation, addDataOutput, and addOutput
 * to private helpers. A correct compiler must auto-inject continuation
 * params (`_changePKH`, `_changeAmount`, `_newAmount`, `txPreimage`)
 * for each public method as if the public body called the intrinsic
 * directly. Before the F1 fix the auto-injection was a shallow scan
 * of the public body, so these methods were silently classified as
 * terminal and the deploy + call cycle would fail.
 */

import { describe, it, expect } from 'vitest';
import { compileContract, compileSource } from './helpers/compile.js';
import { RunarContract } from 'runar-sdk';
import { createFundedWallet } from './helpers/wallet.js';
import { createProvider } from './helpers/node.js';

// Inline private-helper variant whose `record()` helper emits a 1-satoshi
// (not 0) data output. The CI regtest node runs with acceptnonstdtxn=0
// (oracle hardening, PR #49) and rejects 0-satoshi OP_RETURN outputs as
// "dust" at sendrawtransaction. The shared conformance contract
// (examples/ts/private-helper-outputs/PrivateHelperOutputs.runar.ts) is
// deliberately left at 0n so its cross-tier hex goldens stay frozen; this
// inline source preserves the exact "data output routed through a private
// helper, broadcast to a live node" assertion without that golden churn.
const LOG_SOURCE = `
import { StatefulSmartContract, ByteString, assert } from 'runar-lang';

export class PrivateHelperLog extends StatefulSmartContract {
    counter: bigint;

    constructor(counter: bigint) {
        super(counter);
        this.counter = counter;
    }

    private record(payload: ByteString): void {
        this.addDataOutput(1n, payload);
    }

    public log(payload: ByteString): void {
        this.record(payload);
        assert(true);
    }
}
`;

describe('PrivateHelperOutputs', () => {
  it('commit invokes private state mutation and broadcasts a continuation tx', async () => {
    const artifact = compileContract('examples/ts/private-helper-outputs/PrivateHelperOutputs.runar.ts');
    const contract = new RunarContract(artifact, [0n]);

    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);

    const { txid: deployTxid } = await contract.deploy(provider, signer, {});
    expect(deployTxid).toBeTruthy();

    const { txid: callTxid } = await contract.call('commit', [], provider, signer);
    expect(callTxid).toBeTruthy();
    expect(contract.state.counter).toBe(1n);
  });

  it('log routes a data output through a private helper', async () => {
    const artifact = compileSource(LOG_SOURCE, 'PrivateHelperLog.runar.ts');
    const contract = new RunarContract(artifact, [0n]);

    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);

    await contract.deploy(provider, signer, {});

    const payload = '6a09' + '6273766d2d74657374';
    const { txid } = await contract.call('log', [payload], provider, signer);
    expect(txid).toBeTruthy();
  });

  it('repeated commit calls accumulate state across continuations', async () => {
    const artifact = compileContract('examples/ts/private-helper-outputs/PrivateHelperOutputs.runar.ts');
    const contract = new RunarContract(artifact, [0n]);

    const provider = createProvider();
    const { signer } = await createFundedWallet(provider);

    await contract.deploy(provider, signer, {});

    await contract.call('commit', [], provider, signer);
    await contract.call('commit', [], provider, signer);
    await contract.call('commit', [], provider, signer);

    expect(contract.state.counter).toBe(3n);
  });
});
