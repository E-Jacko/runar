// ---------------------------------------------------------------------------
// runar-sdk/providers/mock.ts — Mock provider for testing
// ---------------------------------------------------------------------------

import { Spend, LockingScript, type Transaction } from '@bsv/sdk';
import type { Provider } from './provider.js';
import type { TransactionData, UTXO } from '../types.js';
import { InputLimits } from 'runar-ir-schema';
import { assertScriptHexUnderLimit } from '../errors.js';

/**
 * Deep-review finding C8 (part 2): offline validation of a transaction's
 * KNOWN inputs (script validity via @bsv/sdk's production `Spend`
 * interpreter, plus a fee-sanity check when every input is known) before
 * `MockProvider.broadcast()` acks it.
 *
 * Deliberately self-contained rather than imported from `contract.ts`'s
 * `dryRunContractInput` (same @bsv/sdk `Spend` shape, different call site):
 * that would create a `providers/mock.ts` <-> `contract.ts` dependency in
 * the wrong direction (providers are a leaf module). Keep both thin
 * wrappers in sync if `Spend`'s constructor shape ever changes.
 */
function validateBroadcastTx(
  tx: Transaction,
  knownOutpoints: ReadonlyMap<string, { script: string; satoshis: number }>,
): { valid: boolean; error?: string } {
  let allInputsKnown = true;
  let totalKnownIn = 0;

  for (let i = 0; i < tx.inputs.length; i++) {
    const input = tx.inputs[i]!;
    const known = knownOutpoints.get(`${input.sourceTXID}:${input.sourceOutputIndex}`);
    if (!known) {
      allInputsKnown = false;
      continue;
    }
    totalKnownIn += known.satoshis;

    const otherInputs = tx.inputs.filter((_, j) => j !== i);
    try {
      const spend = new Spend({
        sourceTXID: input.sourceTXID!,
        sourceOutputIndex: input.sourceOutputIndex,
        sourceSatoshis: known.satoshis,
        lockingScript: LockingScript.fromHex(known.script),
        transactionVersion: tx.version,
        otherInputs,
        outputs: tx.outputs,
        inputIndex: i,
        unlockingScript: input.unlockingScript!,
        inputSequence: input.sequence ?? 0xffffffff,
        lockTime: tx.lockTime,
      });
      if (!spend.validate()) {
        return { valid: false, error: `input ${i}: script evaluated to false` };
      }
    } catch (e) {
      return { valid: false, error: `input ${i}: ${e instanceof Error ? e.message : String(e)}` };
    }
  }

  if (allInputsKnown) {
    const totalOut = tx.outputs.reduce((sum, o) => sum + (o.satoshis ?? 0), 0);
    if (totalOut > totalKnownIn) {
      return {
        valid: false,
        error: `underfunded: outputs (${totalOut} sats) exceed known inputs (${totalKnownIn} sats)`,
      };
    }
  }

  return { valid: true };
}

/**
 * In-memory mock provider for unit tests and local development.
 *
 * Allows injecting transactions and UTXOs, and records broadcasts for
 * assertion in tests.
 */
export class MockProvider implements Provider {
  private readonly transactions: Map<string, TransactionData> = new Map();
  private readonly rawTransactions: Map<string, string> = new Map();
  private readonly utxos: Map<string, UTXO[]> = new Map();
  private readonly contractUtxos: Map<string, UTXO> = new Map();
  private readonly broadcastedTxs: string[] = [];
  private readonly broadcastedTxObjects: Transaction[] = [];
  private readonly network: 'mainnet' | 'testnet';
  private broadcastCount = 0;
  private feeRate = 100;
  /** Deep-review C8 (part 2): opt-in broadcast validation, off by default. */
  private validateBroadcasts = false;
  /** outpoint ("txid:vout") -> { script, satoshis } for every UTXO this
   * provider has been told about (via addUtxo/addContractUtxo/addTransaction)
   * or has itself produced via a prior broadcast(). Used by
   * `validateBroadcastTx` to check script validity / fee sanity for the
   * inputs it actually knows the value+script of. */
  private readonly knownOutpoints: Map<string, { script: string; satoshis: number }> = new Map();

  constructor(network: 'mainnet' | 'testnet' = 'testnet') {
    this.network = network;
  }

  // -------------------------------------------------------------------------
  // Test data injection
  // -------------------------------------------------------------------------

  addTransaction(tx: TransactionData): void {
    this.transactions.set(tx.txid, tx);
    if (tx.raw) {
      this.rawTransactions.set(tx.txid, tx.raw);
    }
    for (let i = 0; i < tx.outputs.length; i++) {
      const out = tx.outputs[i]!;
      this.knownOutpoints.set(`${tx.txid}:${i}`, { script: out.script, satoshis: out.satoshis });
    }
  }

  addUtxo(address: string, utxo: UTXO): void {
    const existing = this.utxos.get(address) ?? [];
    existing.push(utxo);
    this.utxos.set(address, existing);
    this.knownOutpoints.set(`${utxo.txid}:${utxo.outputIndex}`, { script: utxo.script, satoshis: utxo.satoshis });
  }

  addContractUtxo(scriptHash: string, utxo: UTXO): void {
    this.contractUtxos.set(scriptHash, utxo);
    this.knownOutpoints.set(`${utxo.txid}:${utxo.outputIndex}`, { script: utxo.script, satoshis: utxo.satoshis });
  }

  /**
   * Opt in to validating `broadcast()`ed transactions (deep-review C8 part
   * 2): checks script validity (via @bsv/sdk's `Spend`) for every input
   * whose UTXO this provider knows about, and — when ALL inputs are known —
   * rejects a tx whose outputs exceed its inputs. `broadcast()` throws
   * instead of returning a fake txid when validation fails.
   *
   * Default is OFF (unchanged legacy always-ack behaviour) so existing
   * tests that don't care about validity keep passing.
   */
  enableBroadcastValidation(enabled = true): void {
    this.validateBroadcasts = enabled;
  }

  /** Get all raw tx hexes that were broadcast through this provider. */
  getBroadcastedTxs(): readonly string[] {
    return this.broadcastedTxs;
  }

  /** Get all Transaction objects that were broadcast through this provider. */
  getBroadcastedTxObjects(): readonly Transaction[] {
    return this.broadcastedTxObjects;
  }

  // -------------------------------------------------------------------------
  // Provider implementation
  // -------------------------------------------------------------------------

  async getTransaction(txid: string): Promise<TransactionData> {
    const tx = this.transactions.get(txid);
    if (!tx) {
      throw new Error(`MockProvider: transaction ${txid} not found`);
    }
    return tx;
  }

  async broadcast(tx: Transaction): Promise<string> {
    if (this.validateBroadcasts) {
      const result = validateBroadcastTx(tx, this.knownOutpoints);
      if (!result.valid) {
        throw new Error(
          `MockProvider: refusing to broadcast invalid transaction (C8)${result.error ? `: ${result.error}` : ''}.`,
        );
      }
    }

    const rawTx = tx.toHex();
    this.broadcastedTxs.push(rawTx);
    this.broadcastedTxObjects.push(tx);
    this.broadcastCount++;

    // Generate a deterministic fake txid purely from the raw tx hex.
    // Same transaction → same txid (real Bitcoin semantics: txid = hash of tx bytes).
    const fakeTxid = sha256Hex(`mock-broadcast-${rawTx}`);

    // Auto-store raw hex for subsequent getRawTransaction lookups
    this.rawTransactions.set(fakeTxid, rawTx);

    // Register this tx's own outputs as known outpoints so a subsequent
    // chained call (spending the continuation this broadcast just created)
    // can also be validated.
    for (let i = 0; i < tx.outputs.length; i++) {
      const out = tx.outputs[i]!;
      this.knownOutpoints.set(`${fakeTxid}:${i}`, {
        script: out.lockingScript.toHex(),
        satoshis: out.satoshis ?? 0,
      });
    }

    return fakeTxid;
  }

  async getUtxos(address: string): Promise<UTXO[]> {
    const utxos = this.utxos.get(address) ?? [];
    // DoS-bound: reject pathological scripts from the provider layer BEFORE
    // they propagate into signature / broadcast paths.
    for (const u of utxos) {
      if (u.script) {
        assertScriptHexUnderLimit(
          u.script, InputLimits.MAX_SCRIPT_BYTES,
          `MockProvider.getUtxos(${address})`,
        );
      }
    }
    return utxos;
  }

  async getContractUtxo(scriptHash: string): Promise<UTXO | null> {
    const utxo = this.contractUtxos.get(scriptHash) ?? null;
    if (utxo && utxo.script) {
      assertScriptHexUnderLimit(
        utxo.script, InputLimits.MAX_SCRIPT_BYTES,
        `MockProvider.getContractUtxo(${scriptHash})`,
      );
    }
    return utxo;
  }

  getNetwork(): 'mainnet' | 'testnet' {
    return this.network;
  }

  async getFeeRate(): Promise<number> {
    return this.feeRate;
  }

  async getRawTransaction(txid: string): Promise<string> {
    const raw = this.rawTransactions.get(txid);
    if (raw) return raw;
    const tx = this.transactions.get(txid);
    if (!tx) {
      throw new Error(`MockProvider: transaction ${txid} not found`);
    }
    if (!tx.raw) {
      throw new Error(`MockProvider: transaction ${txid} has no raw hex`);
    }
    return tx.raw;
  }

  /** Set the fee rate returned by getFeeRate() (for testing). */
  setFeeRate(rate: number): void {
    this.feeRate = rate;
  }
}

// ---------------------------------------------------------------------------
// Minimal hex sha256 for deterministic fake txids (no external deps)
// ---------------------------------------------------------------------------

function sha256Hex(input: string): string {
  // Simple deterministic hash for mock purposes — not cryptographically
  // secure. Produces a 64-char hex string that looks like a txid.
  let h0 = 0x6a09e667;
  let h1 = 0xbb67ae85;
  let h2 = 0x3c6ef372;
  let h3 = 0xa54ff53a;
  for (let i = 0; i < input.length; i++) {
    const c = input.charCodeAt(i);
    h0 = Math.imul(h0 ^ c, 0x01000193) >>> 0;
    h1 = Math.imul(h1 ^ c, 0x01000193) >>> 0;
    h2 = Math.imul(h2 ^ c, 0x01000193) >>> 0;
    h3 = Math.imul(h3 ^ c, 0x01000193) >>> 0;
  }
  return [h0, h1, h2, h3, h0 ^ h2, h1 ^ h3, h0 ^ h1, h2 ^ h3]
    .map((n) => (n >>> 0).toString(16).padStart(8, '0'))
    .join('');
}
