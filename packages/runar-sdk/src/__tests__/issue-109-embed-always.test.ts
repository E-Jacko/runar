/**
 * End-to-end proof for GitHub issue #109 (TypeScript reference tier).
 *
 * A readonly field no method references is normally eliminated by the
 * compiler's DCE, so its deploy-time value exists nowhere in the on-chain
 * script and downstream recovery fails. A `/** @embedAlways *\/` directive
 * forces the field into the locking script (a constructor slot). This test
 * drives the full SDK path: compile -> splice real args into the deployed
 * locking script -> recover them with `extractConstructorArgs`, asserting
 * the annotated field's value survives and the un-annotated control does not.
 */
import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract } from '../contract.js';
import { extractConstructorArgs } from '../script-utils.js';
import type { RunarArtifact } from 'runar-ir-schema';

function source(directive: string): string {
  return `
import { SmartContract, assert, Addr, PubKey, Sig, ByteString, hash160, checkSig } from 'runar-lang';

class Meta extends SmartContract {
  readonly pubKeyHash: Addr;
  ${directive}
  readonly metadataId: ByteString;

  constructor(pubKeyHash: Addr, metadataId: ByteString) {
    super(pubKeyHash, metadataId);
    this.pubKeyHash = pubKeyHash;
    this.metadataId = metadataId;
  }

  public unlock(sig: Sig, pubKey: PubKey) {
    assert(hash160(pubKey) === this.pubKeyHash);
    assert(checkSig(sig, pubKey));
  }
}
`;
}

function compileArtifact(directive: string): RunarArtifact {
  const result = compile(source(directive), { fileName: 'Meta.runar.ts' });
  if (!result.artifact) {
    const errs = result.diagnostics
      .filter(d => d.severity === 'error')
      .map(d => d.message);
    throw new Error(`Compile failed: ${errs.join('; ')}`);
  }
  return result.artifact;
}

const PKH = 'ab'.repeat(20);
const METADATA = 'cafebabedeadbeef';

describe('#109 SDK — @embedAlways field is recoverable from the deployed script', () => {
  it('recovers the annotated metadataId value via extractConstructorArgs', () => {
    const artifact = compileArtifact('/** @embedAlways */');
    const contract = new RunarContract(artifact, [PKH, METADATA]);
    const scriptHex = contract.getLockingScript();

    const recovered = extractConstructorArgs(artifact, scriptHex);
    expect(recovered).toHaveProperty('metadataId');
    expect(recovered.metadataId).toBe(METADATA);
    expect(recovered.pubKeyHash).toBe(PKH);
  });

  it('un-annotated control: metadataId is eliminated (not recoverable)', () => {
    const artifact = compileArtifact('');
    const contract = new RunarContract(artifact, [PKH, METADATA]);
    const scriptHex = contract.getLockingScript();

    const recovered = extractConstructorArgs(artifact, scriptHex);
    expect(recovered).not.toHaveProperty('metadataId');
    expect(recovered.pubKeyHash).toBe(PKH);
  });
});
