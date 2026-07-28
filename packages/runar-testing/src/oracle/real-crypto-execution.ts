/**
 * Real-crypto execution oracle (post-mortem remediation #1).
 *
 * The plain differential-execution oracle (`differential-execution.ts`) runs
 * the compiled bytes on the in-process `ScriptVM` against a SYNTHETIC, fixed
 * transaction context (null outpoint, no outputs), so while its OP_CHECKSIG is
 * real (it is `@bsv/sdk`'s `Spend`), no witness it is handed carries a signature
 * over a real spending transaction, and it cannot exercise a state-continuation
 * preimage at all. (Historically it was worse: `ScriptVM` was a hand-rolled
 * interpreter whose `checkSigCallback` defaulted to `() => true`, i.e. every
 * signature check passed unconditionally.)
 * Every fixture needing a signature or a tx-context preimage was therefore
 * routed OUT into `crypto-exempt.json` / `harness-inapplicable.json` and got
 * NO real execution — the exact blind spot behind BUG-100 / #99 / #100 / #44
 * ("compiled to wrong bytes, all seven tiers agreed, nobody executed it with
 * real crypto").
 *
 * This module gives the oracle REAL secp256k1. It executes the compiled
 * fold-ON bytes through `@bsv/sdk`'s production `Spend` interpreter, which
 * computes the real BIP-143 sighash and runs real `OP_CHECKSIG` /
 * `OP_CHECKMULTISIG` / `OP_CODESEPARATOR`, and it synthesises real accept-path
 * witnesses (real key, real DER signature, real state-continuation preimage):
 *
 *   - {@link runStatelessSigned}: a stateless `SmartContract` whose spend
 *     verifies one or more `checkSig` / `checkMultiSig`. Builds the real
 *     single-input sighash, produces real DER signatures from the named test
 *     keys, and validates on `Spend`.
 *   - {@link runStatefulSpend}: a `StatefulSmartContract`. Drives a full
 *     deploy → call continuation spend through the SDK (`RunarContract`) with a
 *     real `LocalSigner`, then re-validates the built call tx on `Spend` — real
 *     auto-injected `checkPreimage` + `OP_CODESEPARATOR` + (optional) user
 *     `checkSig`, i.e. the exact BUG-100 on-chain state binding.
 *
 * A near-miss (wrong key, or a tampered continuation output) MUST make `Spend`
 * reject. Because the ANF interpreter models crypto with mocks it cannot model
 * a crypto rejection, so a crypto near-miss is asserted as a script-only
 * rejection (`cryptoNearMiss`); the accept path is additionally cross-checked
 * against the interpreter for source-vs-script agreement.
 */
import { compile } from 'runar-compiler';
import {
  PrivateKey,
  LockingScript,
  UnlockingScript,
  Spend,
  Transaction,
  Hash,
  TransactionSignature,
} from '@bsv/sdk';
import { RunarContract, MockProvider, LocalSigner, extractStateFromScript } from 'runar-sdk';
import type { RunarArtifact, ABIMethod, ABIParam } from 'runar-ir-schema';
import { TestContract } from '../test-contract.js';
import { TEST_KEYS } from '../test-keys.js';
import { encodeScriptNumber, hexToBytes, bytesToHex } from '../vm/utils.js';

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

/** Marker for a method arg that should be filled with a REAL signature. */
export interface SignMarker {
  /** Name of the test key that signs; `wrong` signs the correct sighash but
   *  with a key whose pubkey is NOT the committed one (crypto near-miss). */
  signWith: string;
}

export type StatelessArg = bigint | boolean | Uint8Array | SignMarker;

export interface RealExecResult {
  /** Did the compiled script verify on the real `@bsv/sdk` Spend engine? */
  vmAccepted: boolean;
  vmError?: string;
  /** Did the ANF interpreter (source semantics, mock crypto) accept?
   *  `undefined` when not evaluated. */
  interpreterAccepted?: boolean;
  interpreterError?: string;
  lockingHex?: string;
  unlockingHex?: string;
  /** For an ACCEPTED stateful spend: the continuation output's state decoded
   *  from the on-chain call tx (via `extractStateFromScript`), so the caller can
   *  check it against an INDEPENDENT hand-authored expectation. This is the only
   *  check of the state *value* — accept/reject alone cannot catch an ANF-level
   *  state-transition miscompile, which produces the same wrong state in both the
   *  SDK-built output and the covenant that validates it (audit #4). `undefined`
   *  when the spend was rejected/tampered or the contract has no state fields. */
  continuationState?: Record<string, unknown> | null;
  /** Did execution actually reach the real Spend engine (`spend.validate()` /
   *  `validateSpend()` was invoked)? `false` means a harness/SDK error occurred
   *  BEFORE the engine ran (e.g. `RunarContract.call()` threw pre-broadcast, a
   *  missing broadcast tx, a malformed unlocking script). A rejection with
   *  `reachedEngine === false` did NOT come from the on-chain script guard, so a
   *  near-miss that relies on the guard must assert `reachedEngine === true` —
   *  otherwise a reject that fails for an unrelated SDK reason silently passes
   *  and the guard it was meant to exercise stops being tested (audit #12). */
  reachedEngine?: boolean;
}

// ---------------------------------------------------------------------------
// Test-key registry
// ---------------------------------------------------------------------------

export function testKey(name: string): {
  privKey: string;
  pubKey: string;
  pubKeyHash: string;
} {
  const k = TEST_KEYS.find((k) => k.name === name);
  if (!k) throw new Error(`unknown test key '${name}' (see runar-testing/src/test-keys.ts)`);
  return { privKey: k.privKey, pubKey: k.pubKey, pubKeyHash: k.pubKeyHash };
}

function privateKeyOf(name: string): PrivateKey {
  return PrivateKey.fromHex(testKey(name).privKey);
}

// ---------------------------------------------------------------------------
// Argument encoding (compiled unlocking script) — mirrors script-execution.ts
// ---------------------------------------------------------------------------

function encodePushData(data: Uint8Array): Uint8Array {
  if (data.length === 0) return new Uint8Array([0x00]);
  if (data.length <= 75) {
    const r = new Uint8Array(1 + data.length);
    r[0] = data.length;
    r.set(data, 1);
    return r;
  }
  if (data.length <= 255) {
    const r = new Uint8Array(2 + data.length);
    r[0] = 0x4c;
    r[1] = data.length;
    r.set(data, 2);
    return r;
  }
  if (data.length <= 65535) {
    const r = new Uint8Array(3 + data.length);
    r[0] = 0x4d;
    r[1] = data.length & 0xff;
    r[2] = (data.length >> 8) & 0xff;
    r.set(data, 3);
    return r;
  }
  const r = new Uint8Array(5 + data.length);
  r[0] = 0x4e;
  r[1] = data.length & 0xff;
  r[2] = (data.length >> 8) & 0xff;
  r[3] = (data.length >> 16) & 0xff;
  r[4] = (data.length >> 24) & 0xff;
  r.set(data, 5);
  return r;
}

function encodeConcrete(arg: bigint | boolean | Uint8Array, param: ABIParam): Uint8Array {
  switch (param.type) {
    case 'bigint': {
      const n = typeof arg === 'bigint' ? arg : BigInt(arg as unknown as number);
      return encodePushData(encodeScriptNumber(n));
    }
    case 'boolean':
      return (arg as boolean) ? new Uint8Array([0x51]) : new Uint8Array([0x00]);
    default: {
      // ByteString / PubKey / Sig / Sha256 / Ripemd160 / Addr / SigHashPreimage
      const bytes = arg instanceof Uint8Array ? arg : hexToBytes(arg as unknown as string);
      return encodePushData(bytes);
    }
  }
}

function concat(arrays: Uint8Array[]): Uint8Array {
  let total = 0;
  for (const a of arrays) total += a.length;
  const out = new Uint8Array(total);
  let off = 0;
  for (const a of arrays) {
    out.set(a, off);
    off += a.length;
  }
  return out;
}

// ---------------------------------------------------------------------------
// Stateless signed execution
// ---------------------------------------------------------------------------

export interface StatelessSignedOptions {
  source: string;
  fileName: string;
  method: string;
  /** Positional args; a {@link SignMarker} is replaced with a real DER sig. */
  args: StatelessArg[];
  /** Baked constructor args (bigint | boolean | hex string). */
  constructorArgs: Record<string, bigint | boolean | string>;
  /** Run the ANF interpreter too (source-vs-script agreement). Default true. */
  checkInterpreter?: boolean;
}

function findPublicMethod(artifact: RunarArtifact, name: string): ABIMethod {
  const m = artifact.abi.methods.find((m) => m.name === name && m.isPublic);
  if (!m) throw new Error(`public method '${name}' not found in ${artifact.contractName}`);
  return m;
}

export function runStatelessSigned(opts: StatelessSignedOptions): RealExecResult {
  const compiled = compile(opts.source, {
    fileName: opts.fileName,
    constructorArgs: opts.constructorArgs,
    disableConstantFolding: false, // fold-ON deployed bytes
  });
  if (!compiled.success || !compiled.artifact || !compiled.scriptHex) {
    const errs = compiled.diagnostics
      .filter((d) => d.severity === 'error')
      .map((d) => d.message)
      .join('; ');
    throw new Error(`compile failed for ${opts.fileName}: ${errs}`);
  }
  const artifact = compiled.artifact;
  const lockingHex = compiled.scriptHex;
  const method = findPublicMethod(artifact, opts.method);
  if (opts.args.length !== method.params.length) {
    throw new Error(
      `arg count mismatch for ${opts.method}: ABI declares ${method.params.length}, got ${opts.args.length}`,
    );
  }

  const lockingScript = LockingScript.fromHex(lockingHex);

  // Build the real single-input BIP-143 sighash preimage (subscript = the full
  // locking script; stateless contracts carry no OP_CODESEPARATOR so the
  // subscript is the whole script). All checkSig / checkMultiSig ops in a
  // single-input spend sign this same digest.
  const scope = TransactionSignature.SIGHASH_ALL | TransactionSignature.SIGHASH_FORKID;
  const preimageBytes = TransactionSignature.formatBytes({
    sourceTXID: '00'.repeat(32),
    sourceOutputIndex: 0,
    sourceSatoshis: 100000,
    transactionVersion: 2,
    otherInputs: [],
    outputs: [],
    inputIndex: 0,
    subscript: lockingScript,
    inputSequence: 0xffffffff,
    lockTime: 0,
    scope,
  });
  // OP_CHECKSIG computes hash256(preimage) = sha256(sha256(preimage)); sign()
  // does one sha256 internally, so pre-hash once.
  const digest = Hash.sha256(Array.from(preimageBytes));

  function derSig(keyName: string): string {
    const sig = privateKeyOf(keyName).sign(digest);
    const txSig = new TransactionSignature(sig.r, sig.s, scope);
    return bytesToHex(new Uint8Array(txSig.toChecksigFormat()));
  }

  // Build unlocking pushes.
  const pushes: Uint8Array[] = [];
  for (let i = 0; i < opts.args.length; i++) {
    const param = method.params[i]!;
    const a = opts.args[i]!;
    if (typeof a === 'object' && !(a instanceof Uint8Array) && 'signWith' in a) {
      pushes.push(encodePushData(hexToBytes(derSig(a.signWith))));
    } else {
      pushes.push(encodeConcrete(a as bigint | boolean | Uint8Array, param));
    }
  }
  // Method selector for multi-public-method contracts.
  const publicMethods = artifact.abi.methods.filter((m) => m.isPublic);
  const publicIdx = publicMethods.findIndex((m) => m.name === opts.method);
  if (publicIdx !== -1 && publicMethods.length > 1) {
    pushes.push(encodePushData(encodeScriptNumber(BigInt(publicIdx))));
  }
  const unlockingHex = bytesToHex(concat(pushes));

  // Execute on the real @bsv/sdk Spend interpreter.
  let vmAccepted = false;
  let vmError: string | undefined;
  let reachedEngine = false;
  try {
    const spend = new Spend({
      sourceTXID: '00'.repeat(32),
      sourceOutputIndex: 0,
      sourceSatoshis: 100000,
      lockingScript,
      transactionVersion: 2,
      otherInputs: [],
      outputs: [],
      unlockingScript: UnlockingScript.fromHex(unlockingHex),
      inputIndex: 0,
      inputSequence: 0xffffffff,
      lockTime: 0,
    });
    // The engine is now running: a subsequent false/throw is a genuine script
    // rejection, not a harness error before the guard ran.
    reachedEngine = true;
    vmAccepted = spend.validate();
  } catch (e) {
    vmAccepted = false;
    vmError = e instanceof Error ? e.message : String(e);
  }

  // Source-semantics oracle. The ANF interpreter's `checkSig` performs REAL
  // ECDSA verification over a fixed TEST_MESSAGE (not a mock), so a Sig arg is
  // fed the named key's precomputed `testSig` (a real signature over that
  // message). (`checkMultiSig` is unimplemented in the interpreter — it always
  // returns false — so multisig fixtures must set `checkInterpreter: false`.)
  let interpreterAccepted: boolean | undefined;
  let interpreterError: string | undefined;
  if (opts.checkInterpreter !== false) {
    try {
      const tc = TestContract.fromSource(opts.source, opts.constructorArgs, opts.fileName);
      const named: Record<string, unknown> = {};
      method.params.forEach((p, i) => {
        const a = opts.args[i]!;
        if (typeof a === 'object' && !(a instanceof Uint8Array) && 'signWith' in a) {
          const k = TEST_KEYS.find((k) => k.name === a.signWith);
          named[p.name] = hexToBytes(k!.testSig); // real sig over TEST_MESSAGE
        } else {
          named[p.name] = a;
        }
      });
      const res = tc.call(opts.method, named);
      interpreterAccepted = res.success;
      if (!res.success) interpreterError = res.error;
    } catch (e) {
      interpreterAccepted = false;
      interpreterError = e instanceof Error ? e.message : String(e);
    }
  }

  return { vmAccepted, vmError, interpreterAccepted, interpreterError, lockingHex, unlockingHex, reachedEngine };
}

// ---------------------------------------------------------------------------
// Stateful continuation execution (BUG-100 class)
// ---------------------------------------------------------------------------

export interface StatefulSpendOptions {
  source: string;
  fileName: string;
  method: string;
  /** Method args; use `null` for a Sig param (SDK auto-signs input 0). */
  args: unknown[];
  /** Positional constructor args (bigint | boolean | hex string). */
  constructorArgs: (bigint | boolean | string)[];
  /** Test-key name that funds the deploy and signs the call. */
  signerKey: string;
  /** Satoshis for the continuation output — must match a method's explicit
   *  `addOutput(<sats>, ...)` / `addRawOutput(<sats>, ...)` amount so the
   *  on-chain checkPreimage output binding holds. */
  satoshis?: number;
  /** Optional nLockTime for the call tx (locktime / block-height introspection). */
  lockTime?: number;
  /** Near-miss: after building a valid call, tamper the continuation output so
   *  the on-chain checkPreimage binding must fail. */
  tamperOutput?: boolean;
}

function mutateLastByte(hex: string): string {
  if (hex.length < 2) return hex;
  const b = parseInt(hex.slice(-2), 16) ^ 0xff;
  return hex.slice(0, -2) + b.toString(16).padStart(2, '0');
}

/**
 * Validate `tx`'s input `inputIdx` against `sourceTx`'s output `sourceOutputIdx`
 * on the real Spend interpreter. Mirrors the harness in
 * runar-sdk/__tests__/issues-99-100-stateful-exec.test.ts. When `tamperOutput`
 * is set, the continuation output (index 0) is corrupted before validation so
 * the recomputed sighash no longer matches the on-stack preimage.
 */
function validateSpend(
  tx: Transaction,
  inputIdx: number,
  sourceTx: Transaction,
  sourceOutputIdx: number,
  tamperOutput: boolean,
): boolean {
  const input = tx.inputs[inputIdx]!;
  const sourceOutput = sourceTx.outputs[sourceOutputIdx]!;
  const outputs: { lockingScript: LockingScript; satoshis: number }[] = tx.outputs.map((o, i) => {
    const script =
      tamperOutput && i === 0
        ? LockingScript.fromHex(mutateLastByte(o.lockingScript.toHex()))
        : o.lockingScript;
    return { lockingScript: script, satoshis: o.satoshis ?? 0 };
  });
  const spend = new Spend({
    sourceTXID: input.sourceTXID!,
    sourceOutputIndex: input.sourceOutputIndex,
    sourceSatoshis: sourceOutput.satoshis!,
    lockingScript: sourceOutput.lockingScript,
    transactionVersion: tx.version,
    otherInputs: tx.inputs
      .filter((_: unknown, i: number) => i !== inputIdx)
      .map(
        (
          inp: { sourceOutputIndex: number; sourceTXID?: string; sequence?: number },
          idx: number,
        ) => ({
          inputIndex: idx >= inputIdx ? idx + 1 : idx,
          sourceOutputIndex: inp.sourceOutputIndex,
          sourceTXID: inp.sourceTXID!,
          sequence: inp.sequence,
          unlockingScript: undefined as never,
          sourceSatoshis: 0,
          lockingScript: LockingScript.fromHex(''),
        }),
      ),
    outputs,
    unlockingScript: input.unlockingScript!,
    inputIndex: inputIdx,
    inputSequence: input.sequence ?? 0xffffffff,
    lockTime: tx.lockTime,
  });
  return spend.validate();
}

export async function runStatefulSpend(opts: StatefulSpendOptions): Promise<RealExecResult> {
  const compiled = compile(opts.source, { fileName: opts.fileName });
  if (!compiled.artifact) {
    const errs = (compiled.diagnostics || [])
      .filter((d) => d.severity === 'error')
      .map((d) => d.message)
      .join('; ');
    throw new Error(`compile failed for ${opts.fileName}: ${errs}`);
  }
  const artifact = compiled.artifact;

  const key = testKey(opts.signerKey);
  const signer = new LocalSigner(key.privKey);
  const provider = new MockProvider();
  const address = await signer.getAddress();
  provider.addUtxo(address, {
    txid: key.privKey.slice(0, 64),
    outputIndex: 0,
    satoshis: 500_000,
    script: '76a914' + '00'.repeat(20) + '88ac',
  });

  const contract = new RunarContract(artifact, opts.constructorArgs);
  await contract.deploy(provider, signer, {});
  const deployTx = Transaction.fromHex(provider.getBroadcastedTxs()[0]!);

  let vmAccepted = false;
  let vmError: string | undefined;
  let continuationState: Record<string, unknown> | null | undefined;
  let reachedEngine = false;
  try {
    const callOpts: { locktime?: number; satoshis?: number } = {};
    if (opts.lockTime !== undefined) callOpts.locktime = opts.lockTime;
    if (opts.satoshis !== undefined) callOpts.satoshis = opts.satoshis;
    await contract.call(opts.method, opts.args, provider, signer, callOpts);
    const callTx = Transaction.fromHex(provider.getBroadcastedTxs()[1]!);
    // We have a broadcast call tx to validate: a subsequent reject is a genuine
    // script-guard rejection, not an SDK error before the guard ran (audit #12).
    reachedEngine = true;
    vmAccepted = validateSpend(callTx, 0, deployTx, 0, opts.tamperOutput === true);
    // Independent readback of the state VALUE: decode the continuation output's
    // state straight from the on-chain call tx bytes (byte layout only, NOT the
    // transition), so the caller can assert it equals a hand-authored expected
    // state. Only meaningful for a genuinely accepted (untampered) continuation.
    if (vmAccepted && !opts.tamperOutput) {
      const contOutput = callTx.outputs[0];
      if (contOutput) {
        continuationState = extractStateFromScript(artifact, contOutput.lockingScript.toHex());
      }
    }
  } catch (e) {
    vmAccepted = false;
    vmError = e instanceof Error ? e.message : String(e);
  }

  return { vmAccepted, vmError, continuationState, reachedEngine };
}
