/**
 * `requireBaked` compile option — kills the silent-elimination footgun.
 *
 * A readonly property no method references is dropped from the compiled
 * script entirely; its value then exists nowhere on-chain and cannot be
 * verified by any downstream contract. `requireBaked: ['prop']` turns that
 * silent elimination into a compile error, in both template mode (no
 * constructorArgs — SDK bakes at deploy) and baked mode (constructorArgs
 * provided at compile time).
 */

import { describe, it, expect } from 'vitest';
import { compile } from '../index.js';

const SOURCE = `
import { StatefulSmartContract, assert, checkSig } from 'runar-lang';
import type { PubKey, Sig, ByteString } from 'runar-lang';

class EacShaped extends StatefulSmartContract {
  owner: PubKey;
  quantityWh: bigint;

  readonly issuer: PubKey;
  readonly source: bigint;
  /** Never referenced — the compiler eliminates it. */
  readonly tokenId: ByteString;

  constructor(owner: PubKey, quantityWh: bigint, issuer: PubKey, source: bigint, tokenId: ByteString) {
    super(owner, quantityWh, issuer, source, tokenId);
    this.owner = owner;
    this.quantityWh = quantityWh;
    this.issuer = issuer;
    this.source = source;
    this.tokenId = tokenId;
  }

  public withdraw(sig: Sig, outputSatoshis: bigint) {
    assert(checkSig(sig, this.issuer));
    assert(this.source >= 1n);
    assert(outputSatoshis >= 1n);
    this.addOutput(outputSatoshis, this.owner, this.quantityWh);
  }
}
`;

const OWNER = '02' + '11'.repeat(32);
const ISSUER = '03' + 'ab'.repeat(32);

describe('requireBaked (template mode)', () => {
  it('passes for referenced readonly props (they become constructor slots)', () => {
    const result = compile(SOURCE, {
      fileName: 'EacShaped.runar.ts',
      requireBaked: ['issuer', 'source'],
    });
    expect(result.success, JSON.stringify(result.diagnostics)).toBe(true);
    const slotNames = result.artifact!.constructorSlots!.map(s => s.name);
    expect(slotNames).toContain('issuer');
    expect(slotNames).toContain('source');
  });

  it('FAILS for an eliminated (unreferenced) readonly prop — the iteration-003 footgun', () => {
    const result = compile(SOURCE, {
      fileName: 'EacShaped.runar.ts',
      requireBaked: ['tokenId'],
    });
    expect(result.success).toBe(false);
    expect(result.artifact).toBeUndefined();
    const msgs = result.diagnostics.map(d => d.message).join('\n');
    expect(msgs).toMatch(/tokenId.*not referenced by any method body/s);
    expect(msgs).toMatch(/ELIMINATES/);
  });

  it('FAILS for an unknown property name', () => {
    const result = compile(SOURCE, {
      fileName: 'EacShaped.runar.ts',
      requireBaked: ['isuer'], // typo
    });
    expect(result.success).toBe(false);
    expect(result.diagnostics.map(d => d.message).join('\n'))
      .toMatch(/'isuer' is not a property/);
  });

  it('FAILS for a mutable state field (state tail, not a code slot)', () => {
    const result = compile(SOURCE, {
      fileName: 'EacShaped.runar.ts',
      requireBaked: ['quantityWh'],
    });
    expect(result.success).toBe(false);
    expect(result.diagnostics.map(d => d.message).join('\n'))
      .toMatch(/'quantityWh' is mutable state/);
  });
});

describe('requireBaked (baked mode — constructorArgs at compile time)', () => {
  const constructorArgs = {
    owner: OWNER,
    quantityWh: 10n,
    issuer: ISSUER,
    source: 1n,
    tokenId: 'deadbeef',
  };

  it('passes for referenced props baked via constructorArgs', () => {
    const result = compile(SOURCE, {
      fileName: 'EacShaped.runar.ts',
      constructorArgs,
      requireBaked: ['issuer', 'source'],
    });
    expect(result.success, JSON.stringify(result.diagnostics)).toBe(true);
    // The baked issuer bytes are really in the script.
    expect(result.artifact!.script).toContain(ISSUER);
  });

  it('FAILS for an eliminated prop even when a value was supplied for it', () => {
    const result = compile(SOURCE, {
      fileName: 'EacShaped.runar.ts',
      constructorArgs,
      requireBaked: ['tokenId'],
    });
    expect(result.success).toBe(false);
    expect(result.diagnostics.map(d => d.message).join('\n'))
      .toMatch(/tokenId.*not referenced by any method body/s);
  });
});

describe('requireBaked is opt-in', () => {
  it('omitting the option changes nothing (eliminated prop still compiles)', () => {
    const result = compile(SOURCE, { fileName: 'EacShaped.runar.ts' });
    expect(result.success).toBe(true);
    expect(result.artifact!.constructorSlots!.find(s => s.name === 'tokenId')).toBeUndefined();
  });
});
