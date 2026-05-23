#!/usr/bin/env npx tsx
/**
 * Validate the cross-tier signed-envelope fixture against the TypeScript
 * reference implementation.
 *
 * `conformance/sdk-envelope/fixtures.json` is the frozen, hand-curated wire
 * fixture that all six non-TS SDKs validate against (canonicalJson +
 * signEnvelope/verifyEnvelope). This script is the TS tier's drift guard: it
 * LOADS the committed fixture — it never rewrites it, so the curated vectors
 * and their `_vector_id` / `_audit_ref` / `_notes` annotations are preserved —
 * and asserts that every TS-derived byte still matches:
 *   - canonicalJson(input) === expected   for every canonical_json_vector
 *     (including the RFC 8785 parity gates v18/v18b/v19/v20/v21).
 *   - canonicalJson is idempotent on valid_envelope.payload.
 *   - the valid_envelope signature verifies for its payload under the
 *     documented signer pubkey (canonicalJson + sha256 + ECDSA).
 *
 * If TS's canonicalJson or signing path drifts from the committed bytes, this
 * fails — which is what stops the six consumers from silently validating
 * against a stale fixture. The lone-surrogate rejection vectors and the
 * verifyEnvelope rejection vectors are intentionally NOT checked here: they
 * depend on per-tier rejection semantics / an injectable clock and are owned
 * by each tier's interop test.
 *
 * Run from repo root: `cd conformance && npx tsx sdk-envelope/validate-fixtures.ts`.
 * Exits non-zero on the first mismatch.
 */

import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { BigNumber, Hash, PrivateKey, PublicKey, Signature, Utils } from '@bsv/sdk';
import { verify as ecdsaVerifyRaw } from '@bsv/sdk/primitives/ECDSA';
// The SDK's wire `canonicalJson` (runar-sdk/src/envelope.ts) is a literal
// re-export of this `canonicalJsonStringify`, so importing the source here
// tests the identical function while avoiding a build of runar-ir-schema's
// dist — this guard stays install-only in CI.
import { canonicalJsonStringify as canonicalJson } from '../../packages/runar-ir-schema/src/canonical-json.js';

const __dirname = dirname(fileURLToPath(import.meta.url));
const ALICE_PUB_HEX = new PrivateKey(1n).toPublicKey().toDER('hex') as string;

function fail(msg: string): never {
  console.error(`FAIL: ${msg}`);
  process.exit(1);
}

function main(): void {
  const fixturePath = join(__dirname, 'fixtures.json');
  const fixture = JSON.parse(readFileSync(fixturePath, 'utf8'));

  // 1. Every canonical_json_vector must round-trip through the TS canonicalJson.
  const vectors = fixture.canonical_json_vectors as Array<{ input: unknown; expected: string; _vector_id?: string }>;
  if (!Array.isArray(vectors) || vectors.length === 0) fail('canonical_json_vectors missing or empty');
  for (const [i, v] of vectors.entries()) {
    const got = canonicalJson(v.input);
    if (got !== v.expected) {
      const id = v._vector_id ? ` (${v._vector_id})` : '';
      fail(`canonical_json_vectors[${i}]${id}: expected ${JSON.stringify(v.expected)}, got ${JSON.stringify(got)}`);
    }
  }

  // 2. The valid_envelope must verify against the TS reference.
  const env = fixture.valid_envelope as { payload: string; sig: string; pubkey: string };
  if (!env || typeof env.payload !== 'string' || typeof env.sig !== 'string' || typeof env.pubkey !== 'string') {
    fail('valid_envelope missing payload/sig/pubkey');
  }
  if (env.pubkey !== ALICE_PUB_HEX) {
    fail(`valid_envelope.pubkey ${env.pubkey} != documented signer ${ALICE_PUB_HEX}`);
  }
  // canonicalJson must be idempotent on the committed payload (drift guard).
  const reCanon = canonicalJson(JSON.parse(env.payload));
  if (reCanon !== env.payload) {
    fail(`canonicalJson not idempotent on valid_envelope.payload:\n  committed:  ${env.payload}\n  recomputed: ${reCanon}`);
  }
  // The committed signature must verify for sha256(payload) under the pubkey.
  const digest = Hash.sha256(Utils.toArray(env.payload, 'utf8'));
  let sigOk = false;
  try {
    sigOk = ecdsaVerifyRaw(
      new BigNumber(digest),
      Signature.fromDER(Utils.toArray(env.sig, 'hex')),
      PublicKey.fromDER(Utils.toArray(env.pubkey, 'hex')),
    );
  } catch (e) {
    fail(`valid_envelope signature failed to parse/verify: ${(e as Error).message}`);
  }
  if (!sigOk) {
    fail('valid_envelope.sig does not verify for its payload under the TS reference (canonicalJson/sha256/ECDSA drift)');
  }

  console.log(`OK: ${vectors.length} canonical-JSON vectors + valid envelope signature validate against the TS reference.`);
}

main();
