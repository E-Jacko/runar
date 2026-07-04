/**
 * resolveSlotLayout / computeTemplateHash / resolveStateLayout — the
 * value-dependent half of the artifact's verification descriptors.
 *
 * PARITY ORACLE: the EAC companion-input verification work derived every
 * constant by hand from compiled bytes — issuer offset via `indexOf` on the
 * code part, source offset via diffing two bakes, the template hash via a
 * 3-piece excise-and-concat. A mini version of that derivation is ported
 * here as the oracle: the descriptor APIs must reproduce EXACTLY the same
 * values, or they are useless as a replacement.
 */

import { describe, it, expect } from 'vitest';
import { createHash } from 'node:crypto';
import { compile } from 'runar-compiler';
import { RunarContract } from '../contract.js';
import {
  resolveSlotLayout,
  computeTemplateHash,
  buildResolvedCodeHex,
  resolveStateLayout,
} from '../slot-layout.js';
import { serializeState } from '../state.js';

// ---------------------------------------------------------------------------
// Contract under test: the EAC shape (stateful token, readonly PubKey issuer
// anchored via checkSig, readonly bigint source anchored via an assert)
// ---------------------------------------------------------------------------

const EAC_SHAPED_SOURCE = `
import { StatefulSmartContract, assert, checkSig } from 'runar-lang';
import type { PubKey, Sig, ByteString } from 'runar-lang';

class EacShaped extends StatefulSmartContract {
  owner: PubKey;
  quantityWh: bigint;
  status: bigint;

  readonly issuer: PubKey;
  readonly source: bigint;
  readonly tokenId: ByteString;

  constructor(
    owner: PubKey,
    quantityWh: bigint,
    status: bigint,
    issuer: PubKey,
    source: bigint,
    tokenId: ByteString,
  ) {
    super(owner, quantityWh, status, issuer, source, tokenId);
    this.owner = owner;
    this.quantityWh = quantityWh;
    this.status = status;
    this.issuer = issuer;
    this.source = source;
    this.tokenId = tokenId;
  }

  public retire(sig: Sig, outputSatoshis: bigint) {
    assert(checkSig(sig, this.owner));
    assert(this.status === 1n);
    assert(outputSatoshis >= 1n);
    this.addOutput(outputSatoshis, this.owner, this.quantityWh, 3n);
  }

  public withdraw(sig: Sig, outputSatoshis: bigint) {
    assert(checkSig(sig, this.issuer));
    assert(this.source >= 1n);
    assert(this.status === 1n);
    assert(outputSatoshis >= 1n);
    this.addOutput(outputSatoshis, this.owner, this.quantityWh, 4n);
  }
}
`;

const compiled = compile(EAC_SHAPED_SOURCE, { fileName: 'EacShaped.runar.ts' });
if (!compiled.artifact) {
  throw new Error('compile failed: ' + JSON.stringify(compiled.diagnostics));
}
const artifact = compiled.artifact;

const OWNER = '02' + '11'.repeat(32);
const ISSUER = '03' + 'ab'.repeat(32);

/** ctor args: [owner, quantityWh, status, issuer, source, tokenId] */
const argsWithSource = (source: bigint): unknown[] =>
  [OWNER, 10n, 1n, ISSUER, source, 'deadbeef'];
const ARGS = argsWithSource(1n);

const hash256hex = (hex: string): string => {
  const first = createHash('sha256').update(Buffer.from(hex, 'hex')).digest();
  return createHash('sha256').update(first).digest('hex');
};

const codePartHex = (args: unknown[]): string => {
  const c = new RunarContract(artifact, args);
  return (c as unknown as { getCodePartHex(): string }).getCodePartHex().toLowerCase();
};

// ---------------------------------------------------------------------------
// THE ORACLE: hand-derivation exactly as the companion-input verification
// tests do it today (indexOf + two-bake diff + 3-piece excise).
// ---------------------------------------------------------------------------

function oracleDerivation() {
  const code = codePartHex(ARGS);

  let idx = code.indexOf(ISSUER);
  while (idx >= 0 && idx % 2 !== 0) idx = code.indexOf(ISSUER, idx + 1);
  if (idx < 0) throw new Error('issuer pubkey not found in code part');
  const issuerOffset = idx / 2;

  // Diff two bakes that differ only in source (both 1..16 → single OP_N byte)
  const code2 = codePartHex(argsWithSource(2n));
  if (code.length !== code2.length) throw new Error('source bake changed code length');
  const diffs: number[] = [];
  for (let i = 0; i < code.length; i += 2) {
    if (code.slice(i, i + 2) !== code2.slice(i, i + 2)) diffs.push(i / 2);
  }
  if (diffs.length !== 1) throw new Error(`expected 1 differing byte, got ${diffs.length}`);
  const sourceOffset = diffs[0]!;
  if (code.slice(sourceOffset * 2, sourceOffset * 2 + 2) !== '51') {
    throw new Error('source slot is not baked as OP_N');
  }

  const codeLen = code.length / 2;
  const codePostLen = codeLen - sourceOffset - 1;
  const template =
    code.slice(0, issuerOffset * 2) +
    code.slice((issuerOffset + 33) * 2, sourceOffset * 2) +
    code.slice((sourceOffset + 1) * 2);
  return { code, issuerOffset, sourceOffset, codeLen, codePostLen, codeHash: hash256hex(template) };
}

const oracle = oracleDerivation();

// ---------------------------------------------------------------------------
// Parity: descriptor APIs must reproduce the oracle exactly
// ---------------------------------------------------------------------------

describe('resolveSlotLayout parity with the indexOf oracle', () => {
  const layout = resolveSlotLayout(artifact, ARGS);
  const issuer = layout.slots.find(s => s.name === 'issuer')!;
  const source = layout.slots.find(s => s.name === 'source')!;

  it('issuer slot: data-push, header 1, value at the oracle offset, 33 bytes', () => {
    expect(issuer.encoding).toBe('data-push');
    expect(issuer.pushHeaderBytes).toBe(1);
    expect(issuer.valueByteOffset).toBe(oracle.issuerOffset);
    expect(issuer.valueByteLength).toBe(33);
    expect(issuer.byteOffset).toBe(oracle.issuerOffset - 1); // the 0x21 push header
    expect(issuer.byteLength).toBe(34);
  });

  it('source slot: single OP_N opcode byte at the oracle offset', () => {
    expect(source.encoding).toBe('op-n');
    expect(source.pushHeaderBytes).toBe(0);
    expect(source.byteOffset).toBe(oracle.sourceOffset);
    expect(source.byteLength).toBe(1);
    expect(source.valueByteOffset).toBe(oracle.sourceOffset);
    expect(source.valueByteLength).toBe(1);
  });

  it('slot order and derived constants match (source after issuer + 33)', () => {
    expect(source.byteOffset).toBeGreaterThan(issuer.valueByteOffset + 33);
    expect(layout.codeByteLength).toBe(oracle.codeLen);
    // codePostLen exactly as the consuming covenant computes it
    expect(layout.codeByteLength - source.byteOffset - 1).toBe(oracle.codePostLen);
  });

  it('buildResolvedCodeHex is byte-identical to RunarContract.getCodePartHex()', () => {
    expect(buildResolvedCodeHex(artifact, ARGS).toLowerCase()).toBe(oracle.code);
  });

  it('extracted slot bytes are the baked values', () => {
    expect(oracle.code.slice(issuer.valueByteOffset * 2, (issuer.valueByteOffset + 33) * 2))
      .toBe(ISSUER);
    // OP_N rule: opcode byte = 0x50 + source
    expect(oracle.code.slice(source.byteOffset * 2, source.byteOffset * 2 + 2)).toBe('51');
  });
});

describe('computeTemplateHash parity', () => {
  it('reproduces the oracle template hash exactly', () => {
    expect(computeTemplateHash(artifact, ARGS)).toBe(oracle.codeHash);
  });

  it('is invariant across baked slot VALUES of the same width class', () => {
    // Different issuer + different 1..16 source → same excised template
    const otherArgs = ['02' + '22'.repeat(32), 999n, 3n, '02' + 'cd'.repeat(32), 7n, 'beef'];
    expect(computeTemplateHash(artifact, otherArgs)).toBe(oracle.codeHash);
  });

  it('differs when a scriptnum slot changes width class (>= 17 bakes as 2 bytes)', () => {
    // The push header (0x01) stays in the template, so the identity changes —
    // exactly the offset-shifting trap the OP_N (1..16) constraint avoids.
    expect(computeTemplateHash(artifact, argsWithSource(17n))).not.toBe(oracle.codeHash);
  });
});

describe('the OP_N / OP_0 / multi-byte encoding boundaries (iteration-010 trap)', () => {
  it('source = 16n is still a single OP_16 opcode', () => {
    const s = resolveSlotLayout(artifact, argsWithSource(16n)).slots.find(x => x.name === 'source')!;
    expect(s.encoding).toBe('op-n');
    expect(s.byteLength).toBe(1);
    const code = codePartHex(argsWithSource(16n));
    expect(code.slice(s.byteOffset * 2, s.byteOffset * 2 + 2)).toBe('60'); // OP_16
  });

  it('source = 17n becomes a 2-byte scriptnum push and shifts the code length', () => {
    const layout = resolveSlotLayout(artifact, argsWithSource(17n));
    const s = layout.slots.find(x => x.name === 'source')!;
    expect(s.encoding).toBe('scriptnum-push');
    expect(s.pushHeaderBytes).toBe(1);
    expect(s.valueByteLength).toBe(1);
    expect(s.byteLength).toBe(2);
    expect(layout.codeByteLength).toBe(oracle.codeLen + 1);
    // parity against the real bake
    const code = codePartHex(argsWithSource(17n));
    expect(code.length / 2).toBe(layout.codeByteLength);
    expect(code.slice(s.byteOffset * 2, (s.byteOffset + 2) * 2)).toBe('0111'); // push1 0x11
  });

  it('source = 0n bakes as OP_0 — flagged as the placeholder-lookalike it is', () => {
    const s = resolveSlotLayout(artifact, argsWithSource(0n)).slots.find(x => x.name === 'source')!;
    expect(s.encoding).toBe('op-0');
    expect(s.byteLength).toBe(1);
  });
});

describe('resolveStateLayout', () => {
  const layout = resolveStateLayout(artifact);

  it('lays out owner/quantityWh/status per serializeState', () => {
    expect(layout.fields.map(f => f.name)).toEqual(['owner', 'quantityWh', 'status']);
    expect(layout.fields[0]).toMatchObject({ encoding: 'raw', byteOffset: 0, byteLength: 33, tailOffset: -49 });
    expect(layout.fields[1]).toMatchObject({ encoding: 'num2bin-le8', byteOffset: 33, byteLength: 8, tailOffset: -16 });
    expect(layout.fields[2]).toMatchObject({ encoding: 'num2bin-le8', byteOffset: 41, byteLength: 8, tailOffset: -8 });
    expect(layout.totalByteLength).toBe(49);
  });

  it('offsets slice the REAL serialized state and locking script correctly', () => {
    const state = { owner: OWNER, quantityWh: 10n, status: 3n };
    const stateHex = serializeState(artifact.stateFields!, state);
    expect(stateHex.length / 2).toBe(layout.totalByteLength);

    const c = new RunarContract(artifact, ARGS);
    (c as unknown as { setState(s: Record<string, unknown>): void }).setState(state);
    const script = (c.getLockingScript() as string).toLowerCase();
    const scriptLen = script.length / 2;

    // tail offsets are from the END of the locking script
    const owner = layout.fields[0]!;
    expect(script.slice((scriptLen + owner.tailOffset!) * 2, (scriptLen + owner.tailOffset! + owner.byteLength!) * 2))
      .toBe(OWNER);
    const status = layout.fields[2]!;
    expect(script.slice((scriptLen + status.tailOffset!) * 2))
      .toBe('0300000000000000'); // 3n as NUM2BIN-8 LE
  });

  it('works on artifacts that predate the layout annotation (fallback path)', () => {
    const bare = {
      ...artifact,
      stateFields: artifact.stateFields!.map(f => ({ name: f.name, type: f.type, index: f.index })),
    };
    const fallback = resolveStateLayout(bare);
    expect(fallback.fields[1]).toMatchObject({ encoding: 'num2bin-le8', byteOffset: 33, tailOffset: -16 });
    expect(fallback.totalByteLength).toBe(49);
  });
});
