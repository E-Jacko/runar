/**
 * Finding C4 — `estimateFeeForArtifact` mis-wires its `outputCount` option
 * into `estimateCallFee`'s `numFundingInputs` slot (each funding input is
 * priced at ~148 bytes, the size of a signed P2PKH input). A caller asking
 * "what does N continuation OUTPUTS cost" instead gets billed as if the call
 * had N extra P2PKH funding INPUTS — under/over-provisioning every caller
 * that pre-funds a call from this estimate.
 *
 * This test builds a REAL call transaction via `buildCallTransaction` (no
 * additional P2PKH funding UTXOs — just the contract input, N continuation
 * outputs, and a change output) and compares the fee implied by the tx's
 * actual serialized byte size against `estimateFeeForArtifact`'s estimate.
 * They must match, because `estimateFeeForArtifact`'s whole purpose is to
 * predict the fee for exactly this shape of transaction before building it.
 */
import { describe, it, expect } from 'vitest';
import { buildCallTransaction, estimateFeeForArtifact } from '../calling.js';
import type { UTXO } from '../types.js';
import type { RunarArtifact } from 'runar-ir-schema';

const LOCKING_SCRIPT_HEX = 'ab'.repeat(200); // 200-byte locking script
const UNLOCKING_SCRIPT_HEX = 'cd'.repeat(100); // 100-byte unlocking script
const FAKE_ARTIFACT = { script: LOCKING_SCRIPT_HEX } as unknown as RunarArtifact;
const FEE_RATE_SAT_PER_BYTE = 0.1; // estimateFeeForArtifact's own default
const FEE_RATE_SAT_PER_KB = FEE_RATE_SAT_PER_BYTE * 1000;

function makeUtxo(satoshis: number): UTXO {
  return {
    txid: 'aa'.repeat(32),
    outputIndex: 0,
    satoshis,
    script: '76a914' + '00'.repeat(20) + '88ac',
  };
}

/**
 * Build a real call tx with `outputCount` homogeneous continuation outputs
 * (each reusing LOCKING_SCRIPT_HEX, matching estimateFeeForArtifact's
 * single-artifact-script assumption) plus a change output, and return the
 * fee implied by the tx's actual serialized size at FEE_RATE_SAT_PER_KB.
 */
function impliedFeeFromBuiltTx(outputCount: number): number {
  const contractOutputs = Array.from({ length: outputCount }, () => ({
    script: LOCKING_SCRIPT_HEX,
    satoshis: 1000,
  }));
  const changeScript = '76a914' + 'ff'.repeat(20) + '88ac';
  // Fund generously so change stays comfortably positive — otherwise the
  // "omit change when <= 0" branch (finding C3) would change the output
  // count and break byte-for-byte parity with estimateCallFee's model
  // (which always assumes a change output is present).
  const utxo = makeUtxo(outputCount * 1000 + 100_000);

  const { tx } = buildCallTransaction(
    utxo,
    UNLOCKING_SCRIPT_HEX,
    undefined,
    undefined,
    undefined,
    changeScript,
    undefined,
    FEE_RATE_SAT_PER_KB,
    { contractOutputs },
  );

  const actualSize = tx.toHex().length / 2;
  return Math.ceil((actualSize * FEE_RATE_SAT_PER_KB) / 1000);
}

describe('#C4 — estimateFeeForArtifact vs actual built-tx size', () => {
  it('single continuation output: estimate matches the fee implied by the built tx', () => {
    const impliedFee = impliedFeeFromBuiltTx(1);
    const estimated = estimateFeeForArtifact(FAKE_ARTIFACT, {
      feeRate: FEE_RATE_SAT_PER_BYTE,
      unlockingScriptLen: 100,
      outputCount: 1,
    });
    // RED (current mis-wiring): actual=40, estimate=55 (a spurious 148-byte
    // "1 funding input" charge instead of correctly modeling 1 output).
    expect(estimated).toBe(impliedFee);
  });

  it('multi-output call (3 continuation outputs): estimate matches the fee implied by the built tx', () => {
    const impliedFee = impliedFeeFromBuiltTx(3);
    const estimated = estimateFeeForArtifact(FAKE_ARTIFACT, {
      feeRate: FEE_RATE_SAT_PER_BYTE,
      unlockingScriptLen: 100,
      outputCount: 3,
    });
    // RED (current mis-wiring): actual=82, estimate=84 (3 continuation
    // outputs priced as "3 funding inputs" at 148 bytes each, while the 2
    // extra 209-byte continuation outputs are never modeled at all).
    expect(estimated).toBe(impliedFee);
  });
});
