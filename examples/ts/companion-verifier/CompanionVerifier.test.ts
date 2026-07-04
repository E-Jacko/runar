/**
 * Verified Companion Inputs — cross-contract composition example.
 *
 * A CompanionVerifier covenant (input 0) verifies attributes of an
 * AttributedToken companion (input 1) by parsing the companion's parent
 * transaction in Script, bound to the spending tx via the BIP-143 preimage.
 *
 * The fixtures exercise the REAL compiled token: the companion locking
 * script inside each parent tx is produced by `RunarContract` from the
 * compiled AttributedToken artifact, and the verifier's layout constants
 * (slot offsets + excised-template hash) are derived mechanically from the
 * artifact's verification descriptors via `resolveSlotLayout` /
 * `computeTemplateHash` — no hand-counted byte offsets.
 */

import { describe, it, expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { createHash } from 'node:crypto';
import { TestContract, ALICE, BOB, CHARLIE, DAVE, EVE, signTestMessage } from 'runar-testing';
import { compile } from 'runar-compiler';
import { RunarContract, resolveSlotLayout, computeTemplateHash } from 'runar-sdk';

const __dirname = dirname(fileURLToPath(import.meta.url));
const tokenSource = readFileSync(join(__dirname, 'AttributedToken.runar.ts'), 'utf8');
const verifierSource = readFileSync(join(__dirname, 'CompanionVerifier.runar.ts'), 'utf8');

// ---------------------------------------------------------------------------
// Compile the token and derive the verifier's layout constants from the
// artifact's verification descriptors
// ---------------------------------------------------------------------------

const tokenCompile = compile(tokenSource, { fileName: 'AttributedToken.runar.ts' });
if (!tokenCompile.artifact) {
  throw new Error('AttributedToken compile failed: ' + JSON.stringify(tokenCompile.diagnostics));
}
const tokenArtifact = tokenCompile.artifact;

const ATTESTOR = CHARLIE.pubKey.toLowerCase(); // allowlisted attestor #1
const ATTESTOR2 = DAVE.pubKey.toLowerCase(); // allowlisted attestor #2
const ROGUE = EVE.pubKey.toLowerCase(); // NOT on the allowlist
const CATEGORY_A = 1n; // the required category enum
const CATEGORY_B = 2n; // a different (rejected) category

/** ctor args: [owner, amount, status, attestor, category, batchId] */
const tokenArgs = (attestor: string, amount = 10n, status = 1n, category = CATEGORY_A): unknown[] =>
  [BOB.pubKey, amount, status, attestor, category, 'deadbeef'];

// The descriptor-driven derivation: resolveSlotLayout returns the concrete
// byte offsets of the attestor (33-byte push) and category (single OP_N
// opcode) slots in the deployed code part; computeTemplateHash returns the
// hash256 of the code part with both slot VALUES excised. These replace the
// hand-rolled indexOf / two-bake-diff derivation entirely.
const layout = resolveSlotLayout(tokenArtifact, tokenArgs(ATTESTOR));
const attestorSlot = layout.slots.find((s) => s.name === 'attestor')!;
const categorySlot = layout.slots.find((s) => s.name === 'category')!;

const ATTESTOR_OFFSET = BigInt(attestorSlot.valueByteOffset);
const CATEGORY_OFFSET = BigInt(categorySlot.valueByteOffset);
const CODE_POST_LEN = BigInt(layout.codeByteLength) - CATEGORY_OFFSET - 1n;
const TEMPLATE_HASH = computeTemplateHash(tokenArtifact, tokenArgs(ATTESTOR));

/** Full locking script (code part + OP_RETURN state tail) of a token UTXO. */
function tokenFullScript(attestor: string, amount = 10n, status = 1n, category = CATEGORY_A): string {
  const c = new RunarContract(tokenArtifact, tokenArgs(attestor, amount, status, category));
  return (c.getLockingScript() as string).toLowerCase();
}

const TOKEN_SCRIPT = tokenFullScript(ATTESTOR);

// ---------------------------------------------------------------------------
// Parent-tx fixture builders (structurally real serialized transactions)
// ---------------------------------------------------------------------------

const hash256hex = (hex: string) => {
  const f = createHash('sha256').update(Buffer.from(hex, 'hex')).digest();
  return createHash('sha256').update(f).digest('hex');
};
const u32le = (n: number) => { const b = Buffer.alloc(4); b.writeUInt32LE(n); return b.toString('hex'); };
const u64le = (n: bigint) => { const b = Buffer.alloc(8); b.writeBigUInt64LE(n); return b.toString('hex'); };
const varint = (n: number) => {
  if (n < 0xfd) return Buffer.from([n]).toString('hex');
  const b = Buffer.alloc(2); b.writeUInt16LE(n);
  return 'fd' + b.toString('hex');
};

/** Build a structurally real parent tx: version | inputs | outputs | locktime. */
function buildParentTx(outputScript: string = TOKEN_SCRIPT, inputCount = 1): string {
  let tx = u32le(1) + varint(inputCount);
  for (let i = 0; i < inputCount; i++) {
    tx += (i + 11).toString(16).padStart(2, '0').repeat(32) + u32le(0) + varint(107) + 'ab'.repeat(107) + 'ffffffff';
  }
  tx += varint(1) + u64le(1000n) + varint(outputScript.length / 2) + outputScript + u32le(0);
  return tx;
}

const MY_OUTPOINT = 'cc'.repeat(32) + u32le(0);
const OWNER_SIG = signTestMessage(ALICE.privKey);
const SATS = 1000n;

function makeVerifier(overrides: Record<string, unknown> = {}) {
  return TestContract.fromSource(verifierSource, {
    owner: ALICE.pubKey,
    companionsVerified: 0n,
    attestorOffset: ATTESTOR_OFFSET,
    categoryOffset: CATEGORY_OFFSET,
    codePostLen: CODE_POST_LEN,
    expectedTemplateHash: TEMPLATE_HASH,
    allowedAttestor1: ATTESTOR,
    allowedAttestor2: ATTESTOR2,
    minAmount: 5n,
    requiredCategory: CATEGORY_A,
    ...overrides,
  }, 'CompanionVerifier.runar.ts');
}

/**
 * Drive one verifyCompanion call. The mock preimage is wired so that
 * hashPrevouts / outpoint / outputHash reflect a spending tx whose input 0
 * is this verifier and whose input 1 is output 0 of `parentTx`.
 */
function verify(
  verifier: ReturnType<typeof makeVerifier>,
  parentTx: string,
  opts: { tamperParent?: boolean; vout?: number; tamperPrevouts?: boolean } = {},
) {
  const companionOutpoint = hash256hex(parentTx) + u32le(opts.vout ?? 0);
  const allPrevouts = MY_OUTPOINT + companionOutpoint;
  const expectedOutputs = 'e803000000000000' + '19' + '76a914' + '22'.repeat(20) + '88ac';
  verifier.setMockPreimageBytes({
    hashPrevouts: Buffer.from(hash256hex(allPrevouts), 'hex'),
    outpoint: Buffer.from(MY_OUTPOINT, 'hex'),
    outputHash: Buffer.from(hash256hex(expectedOutputs), 'hex'),
  });
  // A single flipped nibble breaks hash256(parentTx) === outpoint txid.
  const suppliedParent = opts.tamperParent
    ? parentTx.slice(0, 9) + (parentTx[9] === '0' ? '1' : '0') + parentTx.slice(10)
    : parentTx;
  // Prevouts that do NOT hash to the preimage's hashPrevouts.
  const suppliedPrevouts = opts.tamperPrevouts
    ? 'ff'.repeat(allPrevouts.length / 2)
    : allPrevouts;
  return verifier.call('verifyCompanion', {
    sig: OWNER_SIG,
    allPrevouts: suppliedPrevouts,
    companionParentTx: suppliedParent,
    expectedOutputs,
  });
}

// ---------------------------------------------------------------------------
// AttributedToken — the companion token's own behavior
// ---------------------------------------------------------------------------

describe('AttributedToken', () => {
  function makeToken(amount = 100n) {
    return TestContract.fromSource(tokenSource, {
      owner: ALICE.pubKey,
      amount,
      status: 1n,
      attestor: ATTESTOR,
      category: CATEGORY_A,
      batchId: 'deadbeef',
    }, 'AttributedToken.runar.ts');
  }

  it('transfer moves the whole amount to the recipient', () => {
    const r = makeToken().call('transfer', { sig: OWNER_SIG, to: BOB.pubKey, outputSatoshis: SATS });
    expect(r.success).toBe(true);
    expect(r.outputs).toHaveLength(1);
    expect(r.outputs[0]!.owner).toBe(BOB.pubKey);
    expect(r.outputs[0]!.amount).toBe(100n);
  });

  it('split conserves amount across both children', () => {
    const r = makeToken().call('split', { sig: OWNER_SIG, to: BOB.pubKey, splitAmount: 30n, outputSatoshis: SATS });
    expect(r.success).toBe(true);
    expect(r.outputs).toHaveLength(2);
    expect(r.outputs[0]!.amount).toBe(30n);
    expect(r.outputs[1]!.amount).toBe(70n);
    expect(r.outputs[0]!.owner).toBe(BOB.pubKey);
    expect(r.outputs[1]!.owner).toBe(ALICE.pubKey);
  });

  it('split rejects taking the full amount (must leave a remainder)', () => {
    const r = makeToken().call('split', { sig: OWNER_SIG, to: BOB.pubKey, splitAmount: 100n, outputSatoshis: SATS });
    expect(r.success).toBe(false);
  });

  it('both attribute slots are baked as constructorSlots (the load-bearing rule)', () => {
    // `batchId` is readonly but unreferenced by any method — the compiler
    // eliminates it, so it is NOT verifiable on-chain. Only referenced
    // attributes become slots.
    expect(tokenArtifact.constructorSlots).toHaveLength(2);
    expect(attestorSlot.encoding).toBe('data-push');
    expect(attestorSlot.valueByteLength).toBe(33);
    expect(categorySlot.encoding).toBe('op-n');
    expect(categorySlot.byteLength).toBe(1);
  });
});

// ---------------------------------------------------------------------------
// CompanionVerifier — accept + adversarial battery
// ---------------------------------------------------------------------------

describe('CompanionVerifier', () => {
  describe('accepts', () => {
    it('a valid companion (allowlisted attestor, right category, active, amount ok)', () => {
      const r = verify(makeVerifier(), buildParentTx());
      expect(r.error).toBeUndefined();
      expect(r.success).toBe(true);
    });

    it('a companion whose parent has multiple inputs (bounded-walk profile)', () => {
      const r = verify(makeVerifier(), buildParentTx(TOKEN_SCRIPT, 2));
      expect(r.success).toBe(true);
    });

    it('a companion attested by the second allowlisted attestor', () => {
      const r = verify(makeVerifier(), buildParentTx(tokenFullScript(ATTESTOR2)));
      expect(r.success).toBe(true);
    });
  });

  describe('rejects (attribute predicate)', () => {
    it('a rogue attestor not on the allowlist', () => {
      const r = verify(makeVerifier(), buildParentTx(tokenFullScript(ROGUE)));
      expect(r.success).toBe(false);
    });

    it('a wrong category (attribute slot #2, OP_N extraction)', () => {
      const r = verify(makeVerifier(), buildParentTx(tokenFullScript(ATTESTOR, 10n, 1n, CATEGORY_B)));
      expect(r.success).toBe(false);
    });

    it('a companion below the minimum amount (state-region predicate)', () => {
      const r = verify(makeVerifier({ minAmount: 50n }), buildParentTx());
      expect(r.success).toBe(false);
    });

    it('a retired companion (status must be Active)', () => {
      const r = verify(makeVerifier(), buildParentTx(tokenFullScript(ATTESTOR, 10n, 3n)));
      expect(r.success).toBe(false);
    });
  });

  describe('rejects (counterfeits and tampering)', () => {
    it('a counterfeit script planting an allowlisted key at the attestor offset (template identity)', () => {
      // Same length class, allowlisted attestor bytes at the right offset —
      // but every other byte differs, so the excised-template hash mismatches.
      const fake =
        'ee'.repeat(Number(ATTESTOR_OFFSET)) + ATTESTOR + 'ee'.repeat(Number(CODE_POST_LEN) + 50);
      const r = verify(makeVerifier(), buildParentTx(fake));
      expect(r.success).toBe(false);
    });

    it('a tampered parent tx (one flipped nibble -> txid mismatch; parent binding)', () => {
      const r = verify(makeVerifier(), buildParentTx(), { tamperParent: true });
      expect(r.success).toBe(false);
    });

    it('allPrevouts that do not hash to the preimage hashPrevouts (prevouts binding)', () => {
      const r = verify(makeVerifier(), buildParentTx(), { tamperPrevouts: true });
      expect(r.success).toBe(false);
    });
  });

  describe('rejects (structural walk bounds)', () => {
    it('a companion outpoint pointing at vout 1 (positional convention)', () => {
      const r = verify(makeVerifier(), buildParentTx(), { vout: 1 });
      expect(r.success).toBe(false);
    });

    it('a parent tx with more than 3 inputs (walk bound)', () => {
      const r = verify(makeVerifier(), buildParentTx(TOKEN_SCRIPT, 4));
      expect(r.success).toBe(false);
    });

    it('a short (P2PKH-sized) output 0 script (varint marker must be 0xfd)', () => {
      const p2pkh = '76a914' + '33'.repeat(20) + '88ac';
      const r = verify(makeVerifier(), buildParentTx(p2pkh));
      expect(r.success).toBe(false);
    });
  });
});
