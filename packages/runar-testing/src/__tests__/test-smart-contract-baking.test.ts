/**
 * TestSmartContract.fromArtifact constructor-arg baking — previously the
 * wrapper stored `constructorArgs` but executed the RAW placeholder script,
 * so any contract whose readonly props are baked at deploy failed with
 * `OP_EQUALVERIFY failed` (comparing against an OP_0 placeholder).
 *
 * Now `constructorSlots` substitution is applied, mirroring runar-sdk's
 * `RunarContract.buildCodeScript`.
 */

import { describe, it, expect } from 'vitest';
import { createHash } from 'crypto';
import { compile } from 'runar-compiler';
import {
  TestSmartContract,
  expectScriptSuccess,
  expectScriptFailure,
} from '../helpers.js';

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/** Referenced readonly Sha256 — the exact shape that used to fail. */
const HASH_LOCK_SOURCE = `
class HashLock extends SmartContract {
  readonly hashValue: Sha256;

  constructor(hashValue: Sha256) {
    super(hashValue);
    this.hashValue = hashValue;
  }

  public unlock(preimage: ByteString) {
    assert(sha256(preimage) === this.hashValue);
  }
}
`;

/** Two constructor params: bigint + bytes. */
const TWO_ARG_SOURCE = `
class TwoArg extends SmartContract {
  readonly target: bigint;
  readonly tag: ByteString;

  constructor(target: bigint, tag: ByteString) {
    super(target, tag);
    this.target = target;
    this.tag = tag;
  }

  public check(x: bigint, t: ByteString) {
    assert(x === this.target);
    assert(t === this.tag);
  }
}
`;

const PREIMAGE_HEX = 'deadbeef';
const HASH_HEX = createHash('sha256')
  .update(Buffer.from(PREIMAGE_HEX, 'hex'))
  .digest('hex');

function compileUnbaked(source: string) {
  const result = compile(source);
  expect(result.success).toBe(true);
  expect(result.artifact!.constructorSlots!.length).toBeGreaterThanOrEqual(1);
  return result.artifact!;
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('TestSmartContract.fromArtifact bakes constructorArgs', () => {
  it('referenced readonly Sha256 passes a VM call with the baked value', () => {
    const artifact = compileUnbaked(HASH_LOCK_SOURCE);
    const contract = TestSmartContract.fromArtifact(artifact, [HASH_HEX]);

    // Previously: OP_EQUALVERIFY failed at PC~3 (placeholder OP_0 vs hash).
    expectScriptSuccess(contract.call('unlock', [PREIMAGE_HEX]));
  });

  it('wrong preimage still fails against the baked value', () => {
    const artifact = compileUnbaked(HASH_LOCK_SOURCE);
    const contract = TestSmartContract.fromArtifact(artifact, [HASH_HEX]);

    expectScriptFailure(contract.call('unlock', ['00112233']));
  });

  it('bakes multiple positional args (bigint + ByteString)', () => {
    const artifact = compileUnbaked(TWO_ARG_SOURCE);
    const contract = TestSmartContract.fromArtifact(artifact, [42n, 'cafe']);

    expectScriptSuccess(contract.call('check', [42n, 'cafe']));
    expectScriptFailure(contract.call('check', [43n, 'cafe']));
    expectScriptFailure(contract.call('check', [42n, 'beef']));
  });

  it('getLockingScriptHex returns the baked script (no OP_0 placeholder)', () => {
    const artifact = compileUnbaked(HASH_LOCK_SOURCE);
    const contract = TestSmartContract.fromArtifact(artifact, [HASH_HEX]);

    expect(contract.getLockingScriptHex()).toContain(HASH_HEX);
    expect(contract.getLockingScriptHex()).not.toBe(artifact.script);
  });

  it('throws when constructorSlots exist but args are missing', () => {
    const artifact = compileUnbaked(HASH_LOCK_SOURCE);
    expect(() => TestSmartContract.fromArtifact(artifact, [])).toThrow(
      /expects 1 constructor arg/,
    );
  });

  it('throws on arg count mismatch', () => {
    const artifact = compileUnbaked(TWO_ARG_SOURCE);
    expect(() =>
      TestSmartContract.fromArtifact(artifact, [42n]),
    ).toThrow(/expects 2 constructor arg/);
  });

  it('accepts non-empty args when the artifact has no constructorSlots', () => {
    // Compile with baked args — no slots remain; passing args again is fine
    // (matches the pre-fix calling convention).
    const result = compile(HASH_LOCK_SOURCE, {
      constructorArgs: { hashValue: HASH_HEX },
    });
    expect(result.success).toBe(true);
    const contract = TestSmartContract.fromArtifact(result.artifact!, [
      HASH_HEX,
    ]);
    expectScriptSuccess(contract.call('unlock', [PREIMAGE_HEX]));
  });
});

// ---------------------------------------------------------------------------
// codeSepIndexSlots baking — stateful contracts with variable-length state
// fields carry OP_0 placeholders for the adjusted codeSeparatorIndex. The
// original fix baked constructorSlots only, so the test script diverged
// from the deployed bytes for these artifacts (test↔deploy fidelity gap).
// ---------------------------------------------------------------------------

/** Stateful + varlen ByteString state field → artifact.codeSepIndexSlots. */
const VARLEN_STATE_SOURCE = `
class VarState extends StatefulSmartContract {
  owner: PubKey;
  memo: ByteString;

  readonly issuer: PubKey;
  readonly bound: bigint;

  constructor(owner: PubKey, memo: ByteString, issuer: PubKey, bound: bigint) {
    super(owner, memo, issuer, bound);
    this.owner = owner;
    this.memo = memo;
    this.issuer = issuer;
    this.bound = bound;
  }

  public update(sig: Sig, newMemo: ByteString, outputSatoshis: bigint) {
    assert(checkSig(sig, this.owner));
    assert(this.bound >= 1n);
    assert(outputSatoshis >= 1n);
    this.memo = newMemo;
    this.addOutput(outputSatoshis, this.owner, this.memo);
  }

  public reclaim(sig: Sig, outputSatoshis: bigint) {
    assert(checkSig(sig, this.issuer));
    assert(outputSatoshis >= 1n);
    this.addOutput(outputSatoshis, this.owner, this.memo);
  }
}
`;

const OWNER_PK = '02' + '11'.repeat(32);
const ISSUER_PK = '03' + 'ab'.repeat(32);
/** ctor args: [owner, memo, issuer, bound] */
const VARLEN_ARGS: unknown[] = [OWNER_PK, 'aabbcc', ISSUER_PK, 5n];

describe('TestSmartContract.fromArtifact bakes codeSepIndexSlots', () => {
  const result = compile(VARLEN_STATE_SOURCE, { fileName: 'VarState.runar.ts' });
  expect(result.success).toBe(true);
  const artifact = result.artifact!;

  it('fixture sanity: the artifact carries both slot kinds', () => {
    expect(artifact.codeSepIndexSlots!.length).toBeGreaterThanOrEqual(1);
    expect(artifact.constructorSlots!.length).toBeGreaterThanOrEqual(1);
    for (const cs of artifact.codeSepIndexSlots!) {
      expect(artifact.script.slice(cs.byteOffset * 2, cs.byteOffset * 2 + 2)).toBe('00');
    }
  });

  it('baked script is byte-identical to runar-sdk buildResolvedCodeHex (deploy parity)', async () => {
    // Cross-implementation oracle: the SDK's resolver is itself pinned
    // byte-identical to RunarContract.getCodePartHex by its own suite.
    const { buildResolvedCodeHex } = await import('runar-sdk');
    const contract = TestSmartContract.fromArtifact(artifact, VARLEN_ARGS);
    expect(contract.getLockingScriptHex().toLowerCase()).toBe(
      buildResolvedCodeHex(artifact, VARLEN_ARGS).toLowerCase(),
    );
  });

  it('substitutes every codeSepIndex placeholder (no OP_0 left at a slot)', () => {
    const contract = TestSmartContract.fromArtifact(artifact, VARLEN_ARGS);
    const baked = contract.getLockingScriptHex();
    expect(baked).not.toBe(artifact.script);
    // First codeSep slot precedes every constructor slot in this fixture, so
    // its byte offset is unshifted; its codeSepIndex (6) bakes as OP_6.
    const sortedSep = [...artifact.codeSepIndexSlots!].sort((a, b) => a.byteOffset - b.byteOffset);
    const sortedCtor = [...artifact.constructorSlots!].sort((a, b) => a.byteOffset - b.byteOffset);
    const first = sortedSep[0]!;
    if (first.byteOffset < sortedCtor[0]!.byteOffset && first.codeSepIndex <= 16) {
      expect(baked.slice(first.byteOffset * 2, first.byteOffset * 2 + 2)).toBe(
        (0x50 + first.codeSepIndex).toString(16),
      );
    }
  });

  it('bakes codeSepIndexSlots even when constructor args were baked at compile time', async () => {
    // Baked-args compile leaves no constructorSlots, but the codeSepIndex
    // placeholders are always emitted for the SDK to fill.
    const baked = compile(VARLEN_STATE_SOURCE, {
      fileName: 'VarState.runar.ts',
      constructorArgs: {
        owner: OWNER_PK,
        memo: 'aabbcc',
        issuer: ISSUER_PK,
        bound: 5n,
      },
    });
    expect(baked.success).toBe(true);
    const bakedArtifact = baked.artifact!;
    expect(bakedArtifact.constructorSlots ?? []).toHaveLength(0);
    expect(bakedArtifact.codeSepIndexSlots!.length).toBeGreaterThanOrEqual(1);

    const { buildResolvedCodeHex } = await import('runar-sdk');
    const contract = TestSmartContract.fromArtifact(bakedArtifact, []);
    expect(contract.getLockingScriptHex().toLowerCase()).toBe(
      buildResolvedCodeHex(bakedArtifact, []).toLowerCase(),
    );
    expect(contract.getLockingScriptHex()).not.toBe(bakedArtifact.script);
  });
});
