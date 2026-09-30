/**
 * `this.addOutput(extractAmount(this.txPreimage), …)` is the natural way to
 * pin "the continuation carries exactly the satoshis it spends". It compiles
 * and verifies on-chain, but the SDK's ANF simulator grouped `extractAmount`
 * with `extractOutputHash` and returned 32 zero bytes for it — a placeholder
 * that makes sense for hashOutputs (a property of a transaction that does not
 * exist yet) and none for the input amount, which is the value of the UTXO
 * being spent and is in the SDK's hands before it builds anything.
 *
 * So `add_output` recorded a 0-satoshi state continuation, `prepareCall`
 * built exactly that, and the covenant's own hashOutputs check refused the
 * SDK's transaction:
 *
 *   {"dryRun":true}                  -> REFUSED: … The top stack element must be truthy …
 *   {"dryRun":true,"satoshis":10000} -> accepted; continuation carries 10000 sats
 *
 * The honest path failed closed for a reason the caller could not see in the
 * ABI, and only an explicit `CallOptions.satoshis` equal to the input value
 * rescued it. `extractAmount` now answers from `SimulationInputs.inputSatoshis`
 * in all three interpreter modes, and `RunarContract` supplies it from the
 * UTXO the preimage is signed over.
 */
import { describe, it, expect } from 'vitest';
import {
  LockingScript,
  OP,
  Script,
  Spend,
  Transaction,
  TransactionSignature,
  Utils,
} from '@bsv/sdk';
import { compile } from 'runar-compiler';
import type { ANFBinding, ANFProgram, RunarArtifact } from 'runar-ir-schema';
import { RunarContract } from '../contract.js';
import { MockProvider } from '../providers/mock.js';
import { LocalSigner } from '../signers/local.js';
import { buildP2PKHScript } from '../script-utils.js';
import { detachUnlockingScript } from '../spend-safety.js';
import type { UTXO } from '../types.js';
import {
  computeNewStateAndDataOutputs,
  executeOnChainAuthoritative,
  executeStrict,
  type SimulationInputs,
} from '../anf-interpreter.js';

const SIGNER_KEY = '0000000000000000000000000000000000000000000000000000000000000005';
const FUNDING_TXID = 'f'.repeat(64);

const source = `import { StatefulSmartContract, assert, extractAmount } from 'runar-lang';

class Carry extends StatefulSmartContract {
  count: bigint;

  constructor(count: bigint) {
    super(count);
    this.count = count;
  }

  public tick() {
    this.addOutput(extractAmount(this.txPreimage), this.count + 1n);
  }
}
`;

// The same pin, reached through a private helper — `extractAmount` is then
// evaluated inside `evalMethodCall`, which has its own bindings walk.
const viaHelper = `import { StatefulSmartContract, assert, extractAmount } from 'runar-lang';

class CarryViaHelper extends StatefulSmartContract {
  count: bigint;

  constructor(count: bigint) {
    super(count);
    this.count = count;
  }

  private spent(): bigint {
    return extractAmount(this.txPreimage);
  }

  public tick() {
    this.addOutput(this.spent(), this.count + 1n);
  }
}
`;

// `extractAmount` inside an `if` body: evaluated by the `if` arm's recursive
// `evalBindings` walk. The new state is `count + amount`, so the covenant's
// hashOutputs check also pins the simulated STATE, not only the output value.
const viaIf = `import { StatefulSmartContract, assert, extractAmount } from 'runar-lang';

class CarryIf extends StatefulSmartContract {
  count: bigint;

  constructor(count: bigint) {
    super(count);
    this.count = count;
  }

  public tick(big: boolean) {
    let next: bigint = 0n;
    if (big) {
      next = this.count + extractAmount(this.txPreimage);
    } else {
      next = this.count + 1n;
    }
    this.addOutput(extractAmount(this.txPreimage), next);
  }
}
`;

// `extractAmount` inside a bounded-loop body: evaluated by the `loop` arm's
// recursive walk, three times. The new state is `3 * amount`.
const viaLoop = `import { StatefulSmartContract, assert, extractAmount } from 'runar-lang';

class CarryLoop extends StatefulSmartContract {
  count: bigint;

  constructor(count: bigint) {
    super(count);
    this.count = count;
  }

  public tick() {
    let total: bigint = 0n;
    for (let i: bigint = 0n; i < 3n; i++) {
      total = total + extractAmount(this.txPreimage);
    }
    this.addOutput(extractAmount(this.txPreimage), total);
  }
}
`;

function compileSource(src: string, fileName: string): RunarArtifact {
  const result = compile(src, { fileName });
  if (!result.artifact) {
    throw new Error(`Compile failed: ${result.diagnostics.map((d) => d.message).join('; ')}`);
  }
  return result.artifact;
}

/** Every `call` binding's `func`, tagged with the nesting it sits in. */
function callSites(body: ANFBinding[], nesting: string[] = []): Array<{ func: string; nesting: string[] }> {
  const out: Array<{ func: string; nesting: string[] }> = [];
  for (const b of body) {
    const v = b.value;
    if (v.kind === 'call') out.push({ func: v.func, nesting });
    if (v.kind === 'if') {
      out.push(...callSites(v.then, [...nesting, 'if.then']));
      out.push(...callSites(v.else, [...nesting, 'if.else']));
    }
    if (v.kind === 'loop') out.push(...callSites(v.body, [...nesting, 'loop']));
  }
  return out;
}

/** A MockProvider that keeps the last transaction handed to `broadcast`, accepted or not. */
class CapturingProvider extends MockProvider {
  lastBroadcast: Transaction | undefined;
  override async broadcast(tx: Transaction): Promise<string> {
    this.lastBroadcast = tx;
    return super.broadcast(tx);
  }
}

async function deployed(artifact: RunarArtifact, satoshis: number) {
  const signer = new LocalSigner(SIGNER_KEY);
  const provider = new CapturingProvider();
  provider.addUtxo(await signer.getAddress(), {
    txid: FUNDING_TXID,
    outputIndex: 0,
    satoshis: 1_000_000,
    script: buildP2PKHScript(await signer.getPublicKey()),
  });
  const contract = new RunarContract(artifact, [0n]);
  await contract.deploy(provider, signer, { satoshis });
  return { contract, provider, signer };
}

/**
 * BIP-143 `hashOutputs` for a set of outputs, taken from the SDK's own
 * preimage serializer (the 32 bytes before nLocktime + sighash type) rather
 * than a second hand-rolled encoder.
 */
function hashOutputsOf(outputs: Transaction['outputs']): string {
  const preimage = TransactionSignature.format({
    sourceTXID: '00'.repeat(32),
    sourceOutputIndex: 0,
    sourceSatoshis: 0,
    transactionVersion: 1,
    otherInputs: [],
    outputs,
    inputIndex: 0,
    subscript: Script.fromHex(''),
    inputSequence: 0xffffffff,
    lockTime: 0,
    scope: 0x41,
  });
  return Utils.toHex(preimage.slice(preimage.length - 40, preimage.length - 8));
}

/**
 * Replay input 0 of `tx` against `utxo` with @bsv/sdk's `Spend`, one opcode at
 * a time, and capture the two operands of the covenant's final `OP_EQUAL` —
 * the hashOutputs the script rebuilt from the preimage's amount, and the
 * hashOutputs the preimage carries for the transaction actually built. Then
 * finish with `validate()` so the verdict is the interpreter's own.
 */
function replayContinuationCheck(tx: Transaction, utxo: UTXO): {
  operands: [string, string];
  verdict: 'accepted' | string;
} {
  const lockingScript = LockingScript.fromHex(utxo.script);
  const chunks = lockingScript.chunks;
  // The auto-injected continuation check ends the code part, just before the
  // OP_RETURN that introduces the state:
  //   … OP_HASH256 <preimage → hashOutputs> OP_EQUAL OP_NIP OP_NIP OP_RETURN <state>
  let returnIdx = -1;
  for (let i = chunks.length - 1; i >= 0; i--) {
    if (chunks[i]!.op === OP.OP_RETURN) { returnIdx = i; break; }
  }
  expect(returnIdx).toBeGreaterThan(3);
  const equalIdx = returnIdx - 3;
  expect(chunks[equalIdx]!.op).toBe(OP.OP_EQUAL);
  expect(chunks[equalIdx + 1]!.op).toBe(OP.OP_NIP);
  expect(chunks[equalIdx + 2]!.op).toBe(OP.OP_NIP);

  const input = tx.inputs[0]!;
  const spend = new Spend({
    sourceTXID: utxo.txid,
    sourceOutputIndex: utxo.outputIndex,
    sourceSatoshis: utxo.satoshis,
    lockingScript,
    transactionVersion: tx.version,
    otherInputs: tx.inputs.filter((_, j) => j !== 0),
    outputs: tx.outputs,
    inputIndex: 0,
    unlockingScript: detachUnlockingScript(input.unlockingScript!),
    inputSequence: input.sequence ?? 0xffffffff,
    lockTime: tx.lockTime,
  });

  let operands: [string, string] | undefined;
  // `step()` executes the opcode at `programCounter` and advances, so sample
  // the stack when the counter has reached the OP_EQUAL and not yet run it.
  while (!(spend.context === 'LockingScript' && spend.programCounter === equalIdx)) {
    if (!spend.step()) throw new Error('script ended before the continuation check');
  }
  const n = spend.stack.length;
  operands = [Utils.toHex(spend.stack[n - 1]!), Utils.toHex(spend.stack[n - 2]!)];

  let verdict: string;
  try {
    spend.validate();
    verdict = 'accepted';
  } catch (e) {
    verdict = e instanceof Error ? e.message : String(e);
  }
  return { operands, verdict };
}

describe('extractAmount in the ANF simulator', () => {
  const artifact = compileSource(source, 'Carry.runar.ts');
  const helperArtifact = compileSource(viaHelper, 'CarryViaHelper.runar.ts');
  const ifArtifact = compileSource(viaIf, 'CarryIf.runar.ts');
  const loopArtifact = compileSource(viaLoop, 'CarryLoop.runar.ts');

  it('answers with the supplied input amount', () => {
    const { outputs } = computeNewStateAndDataOutputs(
      artifact.anf!, 'tick', { count: 0n }, {}, [], { inputSatoshis: 12_345n },
    );
    expect(outputs).toEqual([{ kind: 'state', satoshis: 12_345n }]);
  });

  it('answers the same through a private helper', () => {
    const { outputs } = computeNewStateAndDataOutputs(
      helperArtifact.anf!, 'tick', { count: 0n }, {}, [], { inputSatoshis: 12_345n },
    );
    expect(outputs).toEqual([{ kind: 'state', satoshis: 12_345n }]);
  });

  it('answers the same inside an if body', () => {
    // Pin the shape: one call sits in the then-arm, so this really exercises
    // the `if` arm's recursive walk and not the top-level one.
    const sites = callSites(ifArtifact.anf!.methods.find((m) => m.name === 'tick')!.body)
      .filter((s) => s.func === 'extractAmount');
    expect(sites.map((s) => s.nesting)).toEqual([['if.then'], []]);

    const { state, outputs } = computeNewStateAndDataOutputs(
      ifArtifact.anf!, 'tick', { count: 5n }, { big: true }, [], { inputSatoshis: 12_345n },
    );
    expect(outputs).toEqual([{ kind: 'state', satoshis: 12_345n }]);
    expect(state.count).toBe(12_350n);
  });

  it('answers the same inside a bounded-loop body', () => {
    const sites = callSites(loopArtifact.anf!.methods.find((m) => m.name === 'tick')!.body)
      .filter((s) => s.func === 'extractAmount');
    expect(sites.map((s) => s.nesting)).toEqual([['loop'], []]);

    const { state, outputs } = computeNewStateAndDataOutputs(
      loopArtifact.anf!, 'tick', { count: 0n }, {}, [], { inputSatoshis: 12_345n },
    );
    expect(outputs).toEqual([{ kind: 'state', satoshis: 12_345n }]);
    expect(state.count).toBe(37_035n);
  });

  it('keeps the historical placeholder when nothing is known about the spend', () => {
    // Existing callers that pass no SimulationInputs see exactly what they
    // saw before: a 32-zero-byte value that `add_output` reads as 0n.
    const { outputs } = computeNewStateAndDataOutputs(
      artifact.anf!, 'tick', { count: 0n }, {},
    );
    expect(outputs).toEqual([{ kind: 'state', satoshis: 0n }]);
  });
});

describe('extractAmount evaluates identically in lenient, strict and on-chain authoritative mode', () => {
  // Hand-built ANF, and deliberately NOT compiler-shaped: every compiled
  // method that touches `txPreimage` carries an injected `check_preimage`
  // node (which this interpreter answers `undefined`) followed by an `assert`
  // on it, and the strict modes can never satisfy that off-chain — pinned in
  // the last test of this block — so no compiled artifact reaches the amount
  // logic in strict or on-chain mode. The node kinds used here (`load_param`,
  // `call`, `bin_op`, `assert`, `if`, `update_prop`, `method_call`) are the
  // compiler's own; only the injected scaffolding is absent. `preimage` and
  // `sighash` are arbitrary bytes: no node here reads either.
  //
  // gate(preimage, min):
  //   assert(extractAmount(preimage) >= min);
  //   if (extractAmount(preimage) > 5000) value = 2 else value = 1
  const gateAnf: ANFProgram = {
    contractName: 'AmountGuard',
    properties: [{ name: 'value', type: 'bigint', readonly: false }],
    methods: [{
      name: 'gate',
      params: [
        { name: 'preimage', type: 'SigHashPreimage' },
        { name: 'min', type: 'bigint' },
      ],
      body: [
        { name: 'pre', value: { kind: 'load_param', name: 'preimage' } },
        { name: 'minArg', value: { kind: 'load_param', name: 'min' } },
        { name: 'amount', value: { kind: 'call', func: 'extractAmount', args: ['pre'] } },
        { name: 'enough', value: { kind: 'bin_op', op: '>=', left: 'amount', right: 'minArg' } },
        { name: 'assertEnough', value: { kind: 'assert', value: 'enough' } },
        { name: 'threshold', value: { kind: 'load_const', value: 5000n } },
        { name: 'isBig', value: { kind: 'bin_op', op: '>', left: 'amount', right: 'threshold' } },
        {
          name: 'branch',
          value: {
            kind: 'if',
            cond: 'isBig',
            then: [
              { name: 'two', value: { kind: 'load_const', value: 2n } },
              { name: 'setBig', value: { kind: 'update_prop', name: 'value', value: 'two' } },
            ],
            else: [
              { name: 'one', value: { kind: 'load_const', value: 1n } },
              { name: 'setSmall', value: { kind: 'update_prop', name: 'value', value: 'one' } },
            ],
          },
        },
      ],
      isPublic: true,
    }],
  };
  // record(preimage): value = spent(preimage)   where   private spent(p) = extractAmount(p)
  // — the raw answer lands in state, so what each mode answered is observable.
  const viaHelperAnf: ANFProgram = {
    contractName: 'Record',
    properties: [{ name: 'value', type: 'bigint', readonly: false }],
    methods: [
      {
        name: 'spent',
        params: [{ name: 'p', type: 'SigHashPreimage' }],
        body: [
          { name: 'pre', value: { kind: 'load_param', name: 'p' } },
          { name: 'amt', value: { kind: 'call', func: 'extractAmount', args: ['pre'] } },
        ],
        isPublic: false,
      },
      {
        name: 'record',
        params: [{ name: 'preimage', type: 'SigHashPreimage' }],
        body: [
          { name: 'pre', value: { kind: 'load_param', name: 'preimage' } },
          // The compiler lowers `this.spent(...)` to exactly this pair.
          { name: 'self', value: { kind: 'load_const', value: '@this' } },
          { name: 'got', value: { kind: 'method_call', object: 'self', method: 'spent', args: ['pre'] } },
          { name: 'upd', value: { kind: 'update_prop', name: 'value', value: 'got' } },
        ],
        isPublic: true,
      },
    ],
  };
  const preimage = 'ab'.repeat(8);
  const sighash = '11'.repeat(32);

  function allThree(anf: ANFProgram, method: string, args: Record<string, unknown>, inputs?: SimulationInputs) {
    return {
      lenient: computeNewStateAndDataOutputs(anf, method, { value: 0n }, args, [], inputs),
      strict: executeStrict(anf, method, { value: 0n }, args, [], inputs),
      onChain: executeOnChainAuthoritative(anf, method, { value: 0n }, args, [], { sighash }, inputs),
    };
  }

  it('takes the same branch in all three modes (amount above the threshold)', () => {
    const r = allThree(gateAnf, 'gate', { preimage, min: 6_000n }, { inputSatoshis: 7_000n });
    expect(r.lenient.state).toEqual({ value: 2n });
    expect(r.strict).toEqual(r.lenient);
    expect(r.onChain).toEqual(r.lenient);
  });

  it('takes the same branch in all three modes (amount below the threshold)', () => {
    const r = allThree(gateAnf, 'gate', { preimage, min: 1_000n }, { inputSatoshis: 4_000n });
    expect(r.lenient.state).toEqual({ value: 1n });
    expect(r.strict).toEqual(r.lenient);
    expect(r.onChain).toEqual(r.lenient);
  });

  it('the strict modes refuse on the amount assert; lenient skips it and still branches on the same amount', () => {
    const args = { preimage, min: 6_000n };
    const inputs = { inputSatoshis: 4_000n };
    expect(() => executeStrict(gateAnf, 'gate', { value: 0n }, args, [], inputs))
      .toThrow(expect.objectContaining({ name: 'AssertionFailureError', bindingName: 'assertEnough' }));
    expect(() => executeOnChainAuthoritative(gateAnf, 'gate', { value: 0n }, args, [], { sighash }, inputs))
      .toThrow(expect.objectContaining({ name: 'AssertionFailureError', bindingName: 'assertEnough' }));
    const lenient = computeNewStateAndDataOutputs(gateAnf, 'gate', { value: 0n }, args, [], inputs);
    expect(lenient.state).toEqual({ value: 1n });
  });

  it('a private helper answers from the same inputs as its caller, in every mode', () => {
    const r = allThree(viaHelperAnf, 'record', { preimage }, { inputSatoshis: 12_345n });
    expect(r.lenient.state).toEqual({ value: 12_345n });
    expect(r.strict).toEqual(r.lenient);
    expect(r.onChain).toEqual(r.lenient);
  });

  it('with no SimulationInputs every mode answers exactly the placeholder it always did, helper included', () => {
    // What `main` answers: the 32-zero-byte string, unchanged by any mode.
    const r = allThree(viaHelperAnf, 'record', { preimage });
    expect(r.lenient.state).toEqual({ value: '00'.repeat(32) });
    expect(r.strict).toEqual(r.lenient);
    expect(r.onChain).toEqual(r.lenient);
  });

  it('a compiled artifact cannot reach the amount logic in the strict modes (why the ANF above is hand-built)', () => {
    // Every compiled method that touches txPreimage starts with an injected
    // check_preimage node and an assert on it; the interpreter answers the
    // node `undefined`, so the strict modes throw there — with or without
    // inputs — before any developer logic runs. Unchanged from main.
    const artifact = compileSource(source, 'Carry.runar.ts');
    const body = artifact.anf!.methods.find((m) => m.name === 'tick')!.body;
    const checkPreimage = body.find((b) => b.value.kind === 'check_preimage')!;
    const guard = body.find((b) => b.value.kind === 'assert' && b.value.value === checkPreimage.name)!;
    for (const inputs of [undefined, { inputSatoshis: 10_000n }]) {
      expect(() => executeStrict(artifact.anf!, 'tick', { count: 0n }, {}, [0n], inputs))
        .toThrow(expect.objectContaining({ name: 'AssertionFailureError', bindingName: guard.name }));
      expect(() => executeOnChainAuthoritative(artifact.anf!, 'tick', { count: 0n }, {}, [0n], { sighash }, inputs))
        .toThrow(expect.objectContaining({ name: 'AssertionFailureError', bindingName: guard.name }));
    }
  });
});

describe('RunarContract.call on an extractAmount-pinned continuation', () => {
  it('builds the continuation at the input value without CallOptions.satoshis, and the real Spend accepts it', async () => {
    const artifact = compileSource(source, 'Carry.runar.ts');
    const { contract, provider, signer } = await deployed(artifact, 10_000);

    // MockProvider validates every broadcast through @bsv/sdk's Spend.
    await contract.call('tick', [], provider, signer);

    const txs = provider.getBroadcastedTxs();
    const callTx = Transaction.fromHex(txs[txs.length - 1]!);
    expect(callTx.outputs[0]!.satoshis).toBe(10_000);
    expect(contract.getUtxo()!.satoshis).toBe(10_000);
    expect(contract.state.count).toBe(1n);
  });

  it('the same through a private helper', async () => {
    const artifact = compileSource(viaHelper, 'CarryViaHelper.runar.ts');
    const { contract, provider, signer } = await deployed(artifact, 7_777);
    await contract.call('tick', [], provider, signer);
    expect(contract.getUtxo()!.satoshis).toBe(7_777);
  });

  it('the same inside an if body, with the state the on-chain branch computes from the real amount', async () => {
    const artifact = compileSource(viaIf, 'CarryIf.runar.ts');
    const { contract, provider, signer } = await deployed(artifact, 7_777);
    // The covenant recomputes count' = count + amount from the REAL preimage
    // and pins it in hashOutputs, so a simulation that answered the
    // placeholder inside the if body would be refused here.
    await contract.call('tick', [true], provider, signer);
    expect(contract.getUtxo()!.satoshis).toBe(7_777);
    expect(contract.state.count).toBe(7_777n);
  });

  it('the same inside a bounded-loop body', async () => {
    const artifact = compileSource(viaLoop, 'CarryLoop.runar.ts');
    const { contract, provider, signer } = await deployed(artifact, 7_777);
    await contract.call('tick', [], provider, signer);
    expect(contract.getUtxo()!.satoshis).toBe(7_777);
    expect(contract.state.count).toBe(23_331n);
  });

  it('an explicit CallOptions.satoshis that contradicts the pin is refused by the covenant hashOutputs check, specifically', async () => {
    // The on-chain rule is unchanged: the script pins the continuation to
    // extractAmount(preimage). A caller who overrides the amount builds a
    // transaction the covenant rejects. This pins WHICH check rejects it:
    // the script's final OP_EQUAL compares the hashOutputs it rebuilt at the
    // preimage's amount (10 000) with the hashOutputs of the transaction that
    // was actually built (9 000), and they differ by exactly that output.
    const artifact = compileSource(source, 'Carry.runar.ts');
    const { contract, provider, signer } = await deployed(artifact, 10_000);
    const spent = { ...contract.getUtxo()! };

    await expect(
      contract.call('tick', [], provider, signer, { satoshis: 9_000 }),
    ).rejects.toThrow(/MockProvider: refusing to broadcast invalid transaction \(C8\): input 0: .*top stack element must be truthy/);

    const tx = provider.lastBroadcast!;
    expect(tx.outputs[0]!.satoshis).toBe(9_000);
    const asBuilt = hashOutputsOf(tx.outputs);
    const asPinned = hashOutputsOf(tx.outputs.map((o, i) => (i === 0 ? { ...o, satoshis: 10_000 } : o)));
    expect(asBuilt).not.toBe(asPinned);

    const { operands, verdict } = replayContinuationCheck(tx, spent);
    expect(operands).toContain(asBuilt);
    expect(operands).toContain(asPinned);
    expect(verdict).toMatch(/top stack element must be truthy/);
  });

  it.each([
    ['a fractional', 1.5],
    ['an undefined', undefined as unknown as number],
  ])('refuses to simulate from %s UTXO satoshi value, naming the method and the UTXO', async (_label, bad) => {
    const artifact = compileSource(source, 'Carry.runar.ts');
    const { contract, provider, signer } = await deployed(artifact, 10_000);
    const good = contract.getUtxo()!;
    const restored = RunarContract.fromUtxo(artifact, { ...good, satoshis: bad });
    await expect(restored.call('tick', [], provider, signer)).rejects.toThrow(
      `RunarContract.call('tick'): the contract UTXO ${good.txid}:${good.outputIndex} has a satoshi ` +
        `value that is not a non-negative safe integer (${String(bad)}).`,
    );
  });

  it('the accepted transaction passes the same check with equal operands', async () => {
    const artifact = compileSource(source, 'Carry.runar.ts');
    const { contract, provider, signer } = await deployed(artifact, 10_000);
    const spent = { ...contract.getUtxo()! };
    await contract.call('tick', [], provider, signer);

    const tx = provider.lastBroadcast!;
    const { operands, verdict } = replayContinuationCheck(tx, spent);
    expect(operands[0]).toBe(operands[1]);
    expect(operands[0]).toBe(hashOutputsOf(tx.outputs));
    expect(verdict).toBe('accepted');
  });
});
