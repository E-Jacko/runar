/**
 * buildStatefulPreimage outpoint / prevouts overrides — multi-input
 * covenant tests need control over the spent outpoint and hashPrevouts
 * (contracts verifying companion inputs via extractHashPrevouts /
 * extractOutpoint). Previously both were hardcoded to a 36-zero-byte
 * dummy outpoint.
 */

import { describe, it, expect } from 'vitest';
import { createHash } from 'crypto';
import { compile } from 'runar-compiler';
import type { RunarArtifact } from 'runar-ir-schema';
import { buildStatefulPreimage } from '../mock-preimage.js';

// ---------------------------------------------------------------------------
// Fixture
// ---------------------------------------------------------------------------

const counterSource = `
import { StatefulSmartContract, assert } from 'runar-lang';

class Counter extends StatefulSmartContract {
  count: bigint;

  constructor(count: bigint) {
    super(count);
    this.count = count;
  }

  public increment() {
    this.count++;
  }
}
`;

let artifact: RunarArtifact;
{
  const result = compile(counterSource, { fileName: 'Counter.runar.ts' });
  if (!result.success || !result.artifact) {
    throw new Error(
      result.diagnostics.map((d) => d.message).join('\n') || 'compile failed',
    );
  }
  artifact = result.artifact;
}

function baseParams() {
  return {
    artifact,
    constructorArgs: { count: 0n },
    state: { count: 5n },
    newState: { count: 6n },
  };
}

function hash256hex(hex: string): string {
  const one = createHash('sha256').update(Buffer.from(hex, 'hex')).digest();
  return createHash('sha256').update(one).digest('hex');
}

const DUMMY_OUTPOINT = '00'.repeat(36);
const OUTPOINT_A = 'aa'.repeat(32) + '01000000';
const OUTPOINT_B = 'bb'.repeat(32) + '00000000';

/** Slice helpers over the BIP-143 preimage layout. */
function preimageHashPrevouts(preimageHex: string): string {
  return preimageHex.slice(8, 8 + 64); // after nVersion(4B)
}
function preimageOutpoint(preimageHex: string): string {
  return preimageHex.slice(8 + 64 + 64, 8 + 64 + 64 + 72); // after hashSequence
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('buildStatefulPreimage outpoint/prevouts overrides', () => {
  it('defaults are backward compatible (dummy outpoint, hashPrevouts = hash256(dummy))', () => {
    const result = buildStatefulPreimage(baseParams());
    expect(preimageOutpoint(result.preimageHex)).toBe(DUMMY_OUTPOINT);
    expect(preimageHashPrevouts(result.preimageHex)).toBe(
      hash256hex(DUMMY_OUTPOINT),
    );
  });

  it('outpoint override lands in the preimage and in hashPrevouts', () => {
    const result = buildStatefulPreimage({
      ...baseParams(),
      outpoint: OUTPOINT_A,
    });
    expect(preimageOutpoint(result.preimageHex)).toBe(OUTPOINT_A);
    expect(preimageHashPrevouts(result.preimageHex)).toBe(
      hash256hex(OUTPOINT_A),
    );
  });

  it('prevouts override: hashPrevouts = hash256(concat(prevouts)), outpoint defaults to first prevout', () => {
    const result = buildStatefulPreimage({
      ...baseParams(),
      prevouts: [OUTPOINT_A, OUTPOINT_B],
    });
    expect(preimageOutpoint(result.preimageHex)).toBe(OUTPOINT_A);
    expect(preimageHashPrevouts(result.preimageHex)).toBe(
      hash256hex(OUTPOINT_A + OUTPOINT_B),
    );
  });

  it('outpoint + prevouts: spent input can be the second prevout', () => {
    const result = buildStatefulPreimage({
      ...baseParams(),
      outpoint: OUTPOINT_B,
      prevouts: [OUTPOINT_A, OUTPOINT_B],
    });
    expect(preimageOutpoint(result.preimageHex)).toBe(OUTPOINT_B);
    expect(preimageHashPrevouts(result.preimageHex)).toBe(
      hash256hex(OUTPOINT_A + OUTPOINT_B),
    );
  });

  it('default call is byte-identical to the pre-override behaviour', () => {
    const legacy = buildStatefulPreimage(baseParams());
    const explicit = buildStatefulPreimage({
      ...baseParams(),
      outpoint: DUMMY_OUTPOINT,
      prevouts: [DUMMY_OUTPOINT],
    });
    expect(explicit.preimageHex).toBe(legacy.preimageHex);
    expect(explicit.signatureHex).toBe(legacy.signatureHex);
  });

  it('rejects malformed outpoint / prevouts', () => {
    expect(() =>
      buildStatefulPreimage({ ...baseParams(), outpoint: 'aa'.repeat(32) }),
    ).toThrow(/72 hex chars/);
    expect(() =>
      buildStatefulPreimage({
        ...baseParams(),
        prevouts: [OUTPOINT_A, 'zz'.repeat(36)],
      }),
    ).toThrow(/prevouts\[1\]/);
    expect(() =>
      buildStatefulPreimage({ ...baseParams(), prevouts: [] }),
    ).toThrow(/must not be empty/);
  });
});
