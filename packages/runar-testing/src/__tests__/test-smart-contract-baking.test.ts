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
