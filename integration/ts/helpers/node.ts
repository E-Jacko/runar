/**
 * Bitcoin regtest node helpers — JSON-RPC communication, mining, wallet funding.
 */

import { RPCProvider } from 'runar-sdk';
import type { Transaction } from '@bsv/sdk';

export const RPC_URL = process.env.RPC_URL ?? 'http://localhost:18332';
export const RPC_USER = process.env.RPC_USER ?? 'bitcoin';
export const RPC_PASS = process.env.RPC_PASS ?? 'bitcoin';

/**
 * Wrap an RPCProvider's broadcast method to log the raw tx size in bytes
 * before delegating to the SDK implementation. Mutates the provider in
 * place; returns the same instance for chaining.
 */
function instrumentBroadcast(provider: RPCProvider): RPCProvider {
  const original = provider.broadcast.bind(provider);
  provider.broadcast = async (tx: Transaction): Promise<string> => {
    const hex = tx.toHex();
    const sizeBytes = Math.floor(hex.length / 2);
    process.stderr.write(`[runar-integration] tx broadcast: ${sizeBytes} bytes\n`);
    return original(tx);
  };
  return provider;
}

/** Create an RPCProvider using env-configured credentials. */
export function createProvider(): RPCProvider {
  return instrumentBroadcast(
    new RPCProvider(RPC_URL, RPC_USER, RPC_PASS, { autoMine: true, network: 'testnet' }),
  );
}

/** Create a provider that does NOT mine after each broadcast. Call mine(1) manually. */
export function createBatchProvider(): RPCProvider {
  return instrumentBroadcast(
    new RPCProvider(RPC_URL, RPC_USER, RPC_PASS, { autoMine: false, network: 'testnet' }),
  );
}

export async function rpcCall(method: string, ...params: unknown[]): Promise<unknown> {
  const body = JSON.stringify({
    jsonrpc: '1.0',
    id: 'runar',
    method,
    params,
  });

  const auth = Buffer.from(`${RPC_USER}:${RPC_PASS}`).toString('base64');
  const response = await fetch(RPC_URL, {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      Authorization: `Basic ${auth}`,
    },
    body,
    signal: AbortSignal.timeout(600_000),
  });

  const json = (await response.json()) as { result: unknown; error: unknown };
  if (json.error) {
    const err = json.error as { message?: string };
    throw new Error(`RPC ${method}: ${err.message ?? JSON.stringify(json.error)}`);
  }
  return json.result;
}

export async function mine(blocks: number): Promise<void> {
  try {
    await rpcCall('generate', blocks);
  } catch {
    const addr = (await rpcCall('getnewaddress')) as string;
    await rpcCall('generatetoaddress', blocks, addr);
  }
}

/**
 * Mine until `txid` has at least one confirmation, or fail loudly.
 *
 * A bare `mine(1)` is a RACE: the node must have accepted the tx into its
 * mempool AND selected it for the block template before that block is built.
 * Under a full suite (many tests broadcasting and mining against one node)
 * that ordering is not guaranteed, so the block can land without the tx and a
 * `confirmations > 0` assertion fails on timing rather than on consensus.
 *
 * Observed exactly that: `bip143-crosstier` failed with "expected 0 to be
 * greater than 0" inside `run-all.sh` while passing 4/4 in isolation.
 *
 * This keeps the assertion's strength — the tx must really enter a block — and
 * only removes the assumption that one block suffices.
 */
export async function mineUntilConfirmed(txid: string, maxBlocks = 5): Promise<number> {
  for (let i = 0; i < maxBlocks; i++) {
    await mine(1);
    const tx = (await rpcCall('getrawtransaction', txid, true)) as {
      confirmations?: number;
    };
    const confirmations = tx.confirmations ?? 0;
    if (confirmations > 0) return confirmations;
  }
  throw new Error(
    `tx ${txid} still unconfirmed after mining ${maxBlocks} blocks — ` +
      `it was accepted to the mempool but never selected into a block`,
  );
}

export async function getBlockCount(): Promise<number> {
  return (await rpcCall('getblockcount')) as number;
}

export async function isNodeAvailable(): Promise<boolean> {
  try {
    await getBlockCount();
    return true;
  } catch {
    return false;
  }
}

export async function sendToAddress(address: string, amount: number): Promise<string> {
  return (await rpcCall('sendtoaddress', address, amount)) as string;
}

export async function fundAddress(address: string, btcAmount: number): Promise<void> {
  await rpcCall('importaddress', address, '', false);
  await sendToAddress(address, btcAmount);
  await mine(1);
}
