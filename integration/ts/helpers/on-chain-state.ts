/**
 * On-chain state read-back helper.
 *
 * Reads a contract's current state straight out of the transaction bytes
 * the node accepted, instead of RunarContract.state (the SDK's in-memory
 * next-state prediction).
 *
 * Why not `contract.state`: the SDK auto-computes the next state by running
 * the contract's ANF off-chain -- the same IR the compiled Script executes.
 * A miscompilation that makes the on-chain script commit a wrong-but-accepted
 * state can produce an off-chain prediction that silently agrees with it
 * (PALMER-1, commit 23ef2d2b -- "the off-chain interpreter agreed... because
 * it evaluates the same ANF"). Decoding the state section back out of the
 * broadcast transaction's own script bytes does not go through that
 * computation at all, so it can catch a divergence `contract.state` cannot.
 */

import { extractStateFromScript, type Provider, type RunarArtifact, type UTXO } from 'runar-sdk';

/**
 * Fetch `utxo.txid` from the node and decode the state section of
 * `utxo.outputIndex`'s output script using `artifact`'s state field layout.
 */
export async function readOnChainState(
  provider: Provider,
  artifact: RunarArtifact,
  utxo: UTXO,
): Promise<Record<string, unknown>> {
  const tx = await provider.getTransaction(utxo.txid);
  const output = tx.outputs[utxo.outputIndex];
  if (!output) {
    throw new Error(`readOnChainState: tx ${utxo.txid} has no output ${utxo.outputIndex}`);
  }
  const state = extractStateFromScript(artifact, output.script);
  if (state === null) {
    throw new Error(
      `readOnChainState: tx ${utxo.txid} output ${utxo.outputIndex} script has no decodable state section`,
    );
  }
  return state;
}
