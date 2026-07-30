/**
 * Regression guard for the call path's fee sizing.
 *
 * `prepareCall` resolves a null `SigHashPreimage` argument to a fixed
 * `'00'.repeat(181)` stand-in. 181 bytes is the BIP-143 preimage length for a
 * 24-byte scriptCode:
 *
 *     4 (nVersion) + 32 (hashPrevouts) + 32 (hashSequence) + 36 (outpoint)
 *   + 1 (scriptCode varint) + 24 (scriptCode)
 *   + 8 (amount) + 4 (nSequence) + 32 (hashOutputs) + 4 (nLocktime) + 4 (sighash type)
 *   = 181
 *
 * A real Rúnar contract's scriptCode is its own locking script (for a stateful
 * contract, everything after OP_CODESEPARATOR) — ~1 KB, not 24 bytes. So the
 * stand-in understates the final unlocking script by hundreds of bytes.
 *
 * That is SAFE here only because `call()` re-runs `buildCallTransaction`
 * against the REAL unlocking script (contract.ts, "Rebuild TX with real
 * unlocking scripts") and takes the change amount from that pass — the fee is
 * derived from the bytes actually broadcast, not from the stand-in. The
 * stand-in survives only as a coin-selection estimate, which can over-select
 * (harmless) but no longer sets the fee.
 *
 * Delete that rebuild and this test fails: the Java tier had exactly that shape
 * — two layout passes, both against the stand-in, real unlock spliced in
 * afterwards — and under-paid its own broadcast by 22% (see
 * `CallFeeCoversBroadcastSizeTest` in packages/runar-java).
 */
import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract } from '../contract.js';
import { MockProvider } from '../providers/mock.js';
import { LocalSigner } from '../signers/local.js';
import { Transaction } from '@bsv/sdk';
import type { RunarArtifact } from 'runar-ir-schema';

const SIGNER_KEY = '0000000000000000000000000000000000000000000000000000000000000003';
const WALLET_SATS = 5_000_000;

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

/** Fee a miner requires for a tx of this size, at the quoted sat/KB rate. */
function requiredFee(txHex: string, feeRate: number): number {
  return Math.ceil(((txHex.length / 2) * feeRate) / 1000);
}

/**
 * Fee actually paid = sum(inputs) - sum(outputs). Input values are resolved
 * through the provider (MockProvider mints its own txids on broadcast, so the
 * source tx must be fetched by the id the SDK recorded, not recomputed).
 */
async function actualFee(provider: MockProvider, tx: Transaction): Promise<number> {
  let inSats = 0;
  for (const input of tx.inputs) {
    try {
      const raw = await provider.getRawTransaction(input.sourceTXID!);
      inSats += Transaction.fromHex(raw).outputs[input.sourceOutputIndex]!.satoshis!;
    } catch {
      inSats += WALLET_SATS; // the seeded wallet UTXO — never produced by a broadcast
    }
  }
  const outSats = tx.outputs.reduce((s, o) => s + (o.satoshis ?? 0), 0);
  return inSats - outSats;
}

/** BIP-143 preimage length for a scriptCode; every other field is fixed-width. */
function bip143PreimageLen(scriptCodeHex: string): number {
  const n = scriptCodeHex.length / 2;
  const varint = n < 0xfd ? 1 : n <= 0xffff ? 3 : 5;
  return 156 + varint + n;
}

const CASES: { name: string; source: string; fileName: string; args: unknown[]; method: string; methodArgs: unknown[] }[] = [
  {
    name: 'stateful counter (bigint state only)',
    fileName: 'Counter.runar.ts',
    method: 'inc',
    methodArgs: [],
    args: [5n],
    source: `
      class Counter extends StatefulSmartContract {
        count: bigint;
        constructor(count: bigint) { super(count); this.count = count; }
        public inc() { this.count = this.count + 1n; }
      }
    `,
  },
  {
    name: 'stateful counter with ByteString state and a readonly owner',
    fileName: 'FeeCounter.runar.ts',
    method: 'inc',
    methodArgs: [1n],
    args: [5n, 'ab'.repeat(8), 'cd'.repeat(20)],
    source: `
      class FeeCounter extends StatefulSmartContract {
        count: bigint;
        label: ByteString;
        readonly owner: ByteString;
        constructor(count: bigint, label: ByteString, owner: ByteString) {
          super(count, label, owner);
          this.count = count;
          this.label = label;
          this.owner = owner;
        }
        public inc(bump: bigint) {
          assert(bump > 0n);
          this.count = this.count + bump;
          assert(len(this.owner) == 20n);
        }
      }
    `,
  },
];

describe('call() funds the fee for the transaction it actually broadcasts', () => {
  for (const c of CASES) {
    it(`${c.name}: fee covers the broadcast size`, async () => {
      const artifact = compileSource(c.source, c.fileName);
      const provider = new MockProvider();
      const signer = new LocalSigner(SIGNER_KEY);
      provider.addUtxo(await signer.getAddress(), {
        txid: SIGNER_KEY.slice(0, 64),
        outputIndex: 0,
        satoshis: WALLET_SATS,
        script: '76a914' + '00'.repeat(20) + '88ac',
      });

      const contract = new RunarContract(artifact, c.args as never[]);
      await contract.deploy(provider, signer, { satoshis: 100_000 });
      await contract.call(c.method, c.methodArgs as never[], provider, signer);

      const callTxHex = provider.getBroadcastedTxs()[1]!;
      const callTx = Transaction.fromHex(callTxHex);
      const feeRate = await provider.getFeeRate();

      const paid = await actualFee(provider, callTx);
      const needed = requiredFee(callTxHex, feeRate);

      expect(paid).toBeGreaterThanOrEqual(needed);

      // The stand-in must be the ONLY thing that is wrong-sized: the real
      // preimage rides in the broadcast unlock, so if the fee were derived from
      // the stand-in the tx would be short by (realPreimageLen - 181) bytes'
      // worth of fee. Assert the gap is real, so this test cannot pass
      // vacuously on a contract whose scriptCode happens to be tiny.
      const csi = artifact.codeSeparatorIndex;
      const scriptCodeHex =
        csi !== undefined && csi >= 0 ? artifact.script.slice((csi + 1) * 2) : artifact.script;
      expect(bip143PreimageLen(scriptCodeHex)).toBeGreaterThan(181 + 100);
    });
  }
});
