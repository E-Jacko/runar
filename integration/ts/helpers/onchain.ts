/**
 * On-chain state / output assertions for regtest residual coverage.
 * Decodes the broadcast locking script via the real SDK extractors —
 * never trust only in-memory contract.state.
 */

import { Transaction } from '@bsv/sdk';
import { extractStateFromScript, findLastOpReturn } from 'runar-sdk';
import type { RunarArtifact } from 'runar-ir-schema';
import { rpcCall } from './node.js';

export async function fetchTx(txid: string): Promise<Transaction> {
  const raw = (await rpcCall('getrawtransaction', txid)) as string;
  return Transaction.fromHex(raw);
}

/** Decode state fields from locking script hex using the real SDK codec. */
export function decodeStateFromScript(
  artifact: RunarArtifact,
  scriptHex: string,
): Record<string, unknown> {
  const state = extractStateFromScript(artifact, scriptHex);
  if (!state) {
    throw new Error(`no OP_RETURN state section in script (${scriptHex.length / 2} bytes)`);
  }
  return state as Record<string, unknown>;
}

/**
 * Assert post-spend on-chain state for a continuation UTXO.
 * @param outputIndex - state continuation index (0 when no preceding raw/data outs;
 *   1 after a leading raw/data output when declaration order puts state second).
 */
export async function assertOnChainState(
  artifact: RunarArtifact,
  callTxid: string,
  outputIndex: number,
  expected: Record<string, unknown>,
): Promise<Record<string, unknown>> {
  const tx = await fetchTx(callTxid);
  if (outputIndex >= tx.outputs.length) {
    throw new Error(
      `assertOnChainState: outputIndex ${outputIndex} out of range (tx has ${tx.outputs.length} outs)`,
    );
  }
  const scriptHex = tx.outputs[outputIndex]!.lockingScript.toHex();
  const decoded = decodeStateFromScript(artifact, scriptHex);
  for (const [k, want] of Object.entries(expected)) {
    const got = decoded[k];
    if (typeof want === 'bigint') {
      const g = typeof got === 'bigint' ? got : BigInt(String(got));
      if (g !== want) {
        throw new Error(`on-chain state.${k}: got ${got}, want ${want}`);
      }
    } else if (got !== want && String(got) !== String(want)) {
      throw new Error(`on-chain state.${k}: got ${JSON.stringify(got)}, want ${JSON.stringify(want)}`);
    }
  }
  return decoded;
}

/**
 * Assert 1-byte ByteString state framing is `<0x01><byte>` (direct push),
 * never bare OP_1..OP_16 (0x51..0x60) as the length.
 */
export function assertByteString1BFraming(scriptHex: string, expectedTagHex: string): void {
  const opRet = findLastOpReturn(scriptHex);
  if (opRet < 0) throw new Error('no OP_RETURN in locking script');
  // After OP_RETURN (2 hex chars at opRet), first state field starts.
  const stateStart = opRet + 2;
  const framing = scriptHex.slice(stateStart, stateStart + 2).toLowerCase();
  const payload = scriptHex.slice(stateStart + 2, stateStart + 4).toLowerCase();
  // Must be direct push of length 1: opcode 0x01, not OP_1..OP_16 (0x51-0x60).
  // Direct push of length 1 is 0x01 — never OP_1..OP_16 (0x51..0x60) as length.
  if (framing !== '01') {
    throw new Error(
      `ByteString 1B framing: first state opcode 0x${framing} (want 0x01 direct push, ` +
        `not OP_N-as-length 0x51..0x60)`,
    );
  }
  if (payload !== expectedTagHex.toLowerCase()) {
    throw new Error(`ByteString 1B payload: got ${payload}, want ${expectedTagHex}`);
  }
}

export async function assertOnChainByteString1B(
  callOrDeployTxid: string,
  outputIndex: number,
  expectedTagHex: string,
): Promise<void> {
  const tx = await fetchTx(callOrDeployTxid);
  const scriptHex = tx.outputs[outputIndex]!.lockingScript.toHex();
  assertByteString1BFraming(scriptHex, expectedTagHex);
}
