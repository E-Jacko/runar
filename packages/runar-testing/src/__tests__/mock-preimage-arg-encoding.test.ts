/**
 * Issue #122: mock-preimage constructor-arg encoding must be byte-identical
 * to the SDK's script-building path.
 *
 * The old local `encodeConstructorArg` encoded bigints as 8 raw bytes with no
 * push opcode, booleans as '01' instead of OP_1, and spliced hex strings raw
 * with no push prefix — so the code part it built (and hashed) never matched
 * the script the SDK actually deploys. Tests using it stayed internally
 * consistent (same wrong bytes on both sides of a comparison), which is
 * exactly why this pin against `RunarContract` exists.
 */

import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract } from 'runar-sdk';
import type { RunarArtifact } from 'runar-ir-schema';
import { buildLockingScript } from '../mock-preimage.js';

const source = `
import { SmartContract, assert, ByteString } from 'runar-lang';

class Pinned extends SmartContract {
  readonly a: bigint;
  readonly b: ByteString;
  readonly c: boolean;

  constructor(a: bigint, b: ByteString, c: boolean) {
    super(a, b, c);
    this.a = a;
    this.b = b;
    this.c = c;
  }

  public spend(x: bigint, y: ByteString) {
    assert(x === this.a && y === this.b && this.c);
  }
}
`;

function compileArtifact(): RunarArtifact {
  const result = compile(source);
  if (!result.success || !result.artifact) {
    throw new Error(`Compile failed: ${result.diagnostics.map((d) => d.message).join(', ')}`);
  }
  return result.artifact as RunarArtifact;
}

describe('mock-preimage constructor-arg encoding (issue #122)', () => {
  it('builds a code part byte-identical to RunarContract for bigint, ByteString, and boolean slots', () => {
    const artifact = compileArtifact();
    expect(artifact.constructorSlots?.length).toBe(3);

    // 42n exercises script-number push encoding (not OP_N), 'deadbeef'
    // exercises push-data prefixing, true exercises OP_1.
    const mockScript = buildLockingScript(
      artifact,
      { a: 42n, b: 'deadbeef', c: true },
      {},
    );
    const sdkScript = new RunarContract(artifact, [42n, 'deadbeef', true]).getLockingScript();

    expect(mockScript).toBe(sdkScript);
  });

  it('agrees with the SDK on OP_N-range and zero bigints', () => {
    const artifact = compileArtifact();

    for (const n of [0n, 1n, 16n, 17n]) {
      const mockScript = buildLockingScript(
        artifact,
        { a: n, b: '00', c: false },
        {},
      );
      const sdkScript = new RunarContract(artifact, [n, '00', false]).getLockingScript();
      expect(mockScript).toBe(sdkScript);
    }
  });
});
