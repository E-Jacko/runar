/**
 * Branch-merged local variables must survive the REAL Bitcoin Script
 * interpreter, and must carry the RIGHT value.
 *
 * Reported privately (Ben Palmer, 2026-08-03): a local initialised from a
 * stored state field and conditionally reassigned, then fed to the
 * `addOutput` continuation, compiles cleanly, passes the ANF-interpreter
 * tests, and is REJECTED by @bsv/sdk's `Spend` — a permanently unspendable
 * contract produced from idiomatic source.
 *
 * Root cause is in ANF lowering, not in the number encoding the report
 * guessed at: `lowerIfStatement` (04-anf-lower.ts) only rewires post-branch
 * references to the if's result when BOTH arms end by rebinding the SAME
 * single local. With two or more merged locals — or with the arms
 * reassigning DIFFERENT locals — every later reference still names the
 * pre-branch binding, which is the dead initial value. Stack lowering then
 * compounds it: `lowerIf`'s N>=2 reconcile only recognises results whose
 * names are declared contract PROPERTIES, so branch-merged locals fall
 * through to the single-slot `push(bindingName)` fallback and one stackMap
 * name is registered for N physical stack values. Every subsequent operand
 * lookup resolves one slot off — OP_NUM2BIN/OP_ADD land on a 33-byte pubkey.
 *
 * Two failure faces, one cause:
 *   - "non-minimally encoded script number"
 *   - "OP_NUM2BIN requires that the size expressed in the top stack item is
 *      large enough to hold the value expressed in the second-from-top"
 * and a third, quieter one: the arms leave correct-looking bytes but the
 * continuation commits the STALE pre-branch value. That last face is why
 * every case below asserts the resulting state, not just acceptance — an
 * ANF-level stale reference corrupts the off-chain interpreter and the
 * on-chain script IDENTICALLY, so they agree with each other on a wrong
 * answer and the VM is perfectly happy.
 */

import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract, MockProvider, LocalSigner } from 'runar-sdk';
import { PrivateKey } from '@bsv/sdk';
import type { RunarArtifact } from 'runar-ir-schema';

const PRIV = PrivateKey.fromString('b1'.repeat(32), 16);
const PKH = PRIV.toPublicKey().toHash('hex') as string;
const KEY = PRIV.toPublicKey().encode(true, 'hex') as string;
const OTHER_KEY = PrivateKey.fromString('c1'.repeat(32), 16)
  .toPublicKey().encode(true, 'hex') as string;
const ZERO_KEY = '00'.repeat(33);

function compileOrThrow(source: string, fileName: string): RunarArtifact {
  const r = compile(source, { fileName });
  if (!r.success || !r.artifact) {
    throw new Error(`compile failed: ${r.diagnostics.map((d) => d.message).join('; ')}`);
  }
  return r.artifact as RunarArtifact;
}

/**
 * Compile → deploy → call, with `MockProvider.enableBroadcastValidation()`
 * so every broadcast runs through the real `Spend` interpreter. Returns the
 * post-call state on success; throws on script rejection.
 */
async function deployAndCall(
  source: string,
  fileName: string,
  ctorArgs: unknown[],
  method: string,
  args: unknown[],
): Promise<Record<string, unknown>> {
  const artifact = compileOrThrow(source, fileName);
  const signer = new LocalSigner(PRIV.toString());
  const provider = new MockProvider();
  provider.enableBroadcastValidation();
  provider.addUtxo(await signer.getAddress(), {
    txid: 'ee'.repeat(32),
    outputIndex: 0,
    satoshis: 1_000_000,
    script: '76a914' + PKH + '88ac',
  });
  const contract = new RunarContract(artifact, ctorArgs);
  contract.connect(provider, signer);
  await contract.deploy({ satoshis: 1000 });
  await contract.call(method, args, { satoshis: 60_000 });
  return contract.state as Record<string, unknown>;
}

// ---------------------------------------------------------------------------
// Shapes. Each one is idiomatic "branch and merge a local" source.
// ---------------------------------------------------------------------------

const HEAD = `import { StatefulSmartContract, assert } from 'runar-lang';
import type { PubKey } from 'runar-lang';
`;

/** K=1 merged local, both arms reassign it. Already worked before the fix. */
const S1_ONE_LOCAL_BOTH_ARMS = `${HEAD}
export class S1 extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let na = this.a;
    if (this.a == 0n) { na = bidAmount; } else { na = bidAmount + 1n; }
    this.addOutput(bidAmount, this.closed, na, this.b);
  }
}
`;

/** K=1 merged local, if without else. Already worked before the fix. */
const S2_ONE_LOCAL_NO_ELSE = `${HEAD}
export class S2 extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let na = this.a;
    if (this.a == 0n) { na = bidAmount; }
    this.addOutput(bidAmount, this.closed, na, this.b);
  }
}
`;

/** K=2 merged locals, both arms reassign the SAME two. */
const S3_TWO_LOCALS_SAME_SET = `${HEAD}
export class S3 extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let na = this.a;
    let nb = this.b;
    if (this.a == 0n) { na = bidAmount; nb = 1n; } else { na = 1n; nb = bidAmount; }
    this.addOutput(bidAmount, this.closed, na, nb);
  }
}
`;

/** K=2 union, arms reassign DIFFERENT locals. */
const S4_TWO_LOCALS_ASYMMETRIC = `${HEAD}
export class S4 extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let na = this.a;
    let nb = this.b;
    if (this.a == 0n) { na = bidAmount; } else { nb = bidAmount; }
    this.addOutput(bidAmount, this.closed, na, nb);
  }
}
`;

/** K=2 merged locals, if without else. */
const S5_TWO_LOCALS_NO_ELSE = `${HEAD}
export class S5 extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let na = this.a;
    let nb = this.b;
    if (this.a == 0n) { na = bidAmount; nb = 7n; }
    this.addOutput(bidAmount, this.closed, na, nb);
  }
}
`;

/** K=3 merged locals, both arms reassign the same three. */
const S6_THREE_LOCALS_SAME_SET = `${HEAD}
export class S6 extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  c: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let na = this.a;
    let nb = this.b;
    let nc = this.c;
    if (this.a == 0n) { na = bidAmount; nb = 2n; nc = 3n; }
    else { na = 4n; nb = 5n; nc = bidAmount; }
    this.addOutput(bidAmount, this.closed, na, nb, nc);
  }
}
`;

/** K=2 merged locals of MIXED types (PubKey + bigint), same set both arms. */
const S7_MIXED_TYPES_SAME_SET = `${HEAD}
export class S7 extends StatefulSmartContract {
  closed: bigint = 0n;
  k: PubKey = "${ZERO_KEY}" as PubKey;
  amt: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidderKey: PubKey, bidAmount: bigint) {
    assert(this.closed == 0n);
    let nk = this.k;
    let namt = this.amt;
    if (this.amt == 0n) { nk = bidderKey; namt = bidAmount; }
    else { nk = bidderKey; namt = bidAmount + 1n; }
    this.addOutput(bidAmount, this.closed, nk, namt);
  }
}
`;

/** The filed reproducer: K=4 union, asymmetric arms, mixed types, and the
 *  merged locals also feed an arithmetic expression used as the output
 *  AMOUNT. */
const S8_FILED_REPRO = `${HEAD}
export class S8 extends StatefulSmartContract {
  closed: bigint = 0n;
  closeHeight: bigint = 0n;
  seat1Key: PubKey = "${ZERO_KEY}" as PubKey;
  seat1Amount: bigint = 0n;
  seat2Key: PubKey = "${ZERO_KEY}" as PubKey;
  seat2Amount: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidderKey: PubKey, bidAmount: bigint) {
    assert(this.closed == 0n);
    let n1k = this.seat1Key;
    let n1a = this.seat1Amount;
    let n2k = this.seat2Key;
    let n2a = this.seat2Amount;
    if (this.seat1Amount == 0n) {
      n1k = bidderKey; n1a = bidAmount;
    } else {
      n2k = bidderKey; n2a = bidAmount;
    }
    this.addOutput(n1a + n2a, this.closed, this.closeHeight, n1k, n1a, n2k, n2a);
  }
}
`;

/** Merged locals reassigned inside a NESTED conditional. */
const S9_NESTED = `${HEAD}
export class S9 extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bid(bidAmount: bigint) {
    assert(this.closed == 0n);
    let na = this.a;
    let nb = this.b;
    if (this.a == 0n) {
      if (bidAmount > 100n) { na = bidAmount; nb = 1n; } else { na = 1n; nb = bidAmount; }
    } else {
      na = 9n; nb = 9n;
    }
    this.addOutput(bidAmount, this.closed, na, nb);
  }
}
`;

describe('branch-merged locals — real Script VM + correct value', () => {
  it('S1: one merged local, both arms', async () => {
    const state = await deployAndCall(S1_ONE_LOCAL_BOTH_ARMS, 'S1.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.a).toBe(60_000n);
    expect(state.b).toBe(0n);
  });

  it('S2: one merged local, no else', async () => {
    const state = await deployAndCall(S2_ONE_LOCAL_NO_ELSE, 'S2.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.a).toBe(60_000n);
    expect(state.b).toBe(0n);
  });

  it('S3: two merged locals, same set in both arms', async () => {
    const state = await deployAndCall(S3_TWO_LOCALS_SAME_SET, 'S3.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.a).toBe(60_000n);
    expect(state.b).toBe(1n);
  });

  it('S4: two merged locals, arms reassign different ones', async () => {
    const state = await deployAndCall(S4_TWO_LOCALS_ASYMMETRIC, 'S4.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.a).toBe(60_000n);
    expect(state.b).toBe(0n);
  });

  it('S5: two merged locals, no else', async () => {
    const state = await deployAndCall(S5_TWO_LOCALS_NO_ELSE, 'S5.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.a).toBe(60_000n);
    expect(state.b).toBe(7n);
  });

  it('S6: three merged locals, same set in both arms', async () => {
    const state = await deployAndCall(S6_THREE_LOCALS_SAME_SET, 'S6.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.a).toBe(60_000n);
    expect(state.b).toBe(2n);
    expect(state.c).toBe(3n);
  });

  it('S7: two merged locals of mixed types', async () => {
    const state = await deployAndCall(S7_MIXED_TYPES_SAME_SET, 'S7.runar.ts', [0n], 'bid', [KEY, 60_000n]);
    expect(state.k).toBe(KEY);
    expect(state.amt).toBe(60_000n);
  });

  it('S8: the filed reproducer — four merged locals, asymmetric, mixed types', async () => {
    const state = await deployAndCall(S8_FILED_REPRO, 'S8.runar.ts', [0n], 'bid', [OTHER_KEY, 60_000n]);
    expect(state.seat1Key).toBe(OTHER_KEY);
    expect(state.seat1Amount).toBe(60_000n);
    expect(state.seat2Key).toBe(ZERO_KEY);
    expect(state.seat2Amount).toBe(0n);
  });

  it('S9: merged locals reassigned inside a nested conditional', async () => {
    const state = await deployAndCall(S9_NESTED, 'S9.runar.ts', [0n], 'bid', [60_000n]);
    expect(state.a).toBe(60_000n);
    expect(state.b).toBe(1n);
  });
});
