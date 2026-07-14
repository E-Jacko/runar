/**
 * FRI colinearity check — Plonky3-generated test vector validation.
 *
 * Validates the FRI folding relation:
 *   g(x²) = (f(x) + f(-x)) / 2 + alpha * (f(x) - f(-x)) / (2 * x)
 *
 * Uses Baby Bear base field + quartic extension (ext4, W=11).
 * The contract implements the full formula using:
 *   - bbFieldAdd/Sub for base field
 *   - bbFieldMul/Inv for base field
 *   - bbExt4Mul0..3 for ext4 × ext4 (alpha * diff)
 *
 * Uses the Rúnar interpreter (TestContract) — no regtest node needed.
 */

import { describe, it, expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { TestContract } from 'runar-testing';

const __dirname = dirname(fileURLToPath(import.meta.url));
const VECTORS_DIR = join(__dirname, 'vectors');

interface FRIVector {
  x: number;
  f_x: [number, number, number, number];
  f_neg_x: [number, number, number, number];
  alpha: [number, number, number, number];
  expected_g_x2: [number, number, number, number];
  expected: 'accept' | 'reject';
  description: string;
}

interface FRIVectorFile {
  field: string;
  prime: number;
  vectors: FRIVector[];
}

function loadVectors(filename: string): FRIVectorFile {
  return JSON.parse(readFileSync(join(VECTORS_DIR, filename), 'utf-8'));
}

// The contract implements the FRI colinearity check using Rúnar builtins.
// It computes g(x²) from the inputs and asserts it matches the expected value.
//
// Ext4 addition/subtraction = component-wise bbFieldAdd/Sub
// Ext4 × base scalar = component-wise bbFieldMul
// Ext4 × ext4 = bbExt4Mul0..3
const friSource = `
import {
  SmartContract, assert,
  bbFieldAdd, bbFieldSub, bbFieldMul, bbFieldInv,
  bbExt4Mul0, bbExt4Mul1, bbExt4Mul2, bbExt4Mul3
} from 'runar-lang';

class FRIColinearityCheck extends SmartContract {
  constructor() { super(); }

  public verify(
    x: bigint,
    fx0: bigint, fx1: bigint, fx2: bigint, fx3: bigint,
    fnx0: bigint, fnx1: bigint, fnx2: bigint, fnx3: bigint,
    a0: bigint, a1: bigint, a2: bigint, a3: bigint,
    eg0: bigint, eg1: bigint, eg2: bigint, eg3: bigint
  ) {
    // sum = f(x) + f(-x)  (ext4 add = component-wise)
    const s0 = bbFieldAdd(fx0, fnx0);
    const s1 = bbFieldAdd(fx1, fnx1);
    const s2 = bbFieldAdd(fx2, fnx2);
    const s3 = bbFieldAdd(fx3, fnx3);

    // half_sum = sum / 2 = sum * inv(2)
    const inv2 = bbFieldInv(2n);
    const hs0 = bbFieldMul(s0, inv2);
    const hs1 = bbFieldMul(s1, inv2);
    const hs2 = bbFieldMul(s2, inv2);
    const hs3 = bbFieldMul(s3, inv2);

    // diff = f(x) - f(-x)  (ext4 sub = component-wise)
    const d0 = bbFieldSub(fx0, fnx0);
    const d1 = bbFieldSub(fx1, fnx1);
    const d2 = bbFieldSub(fx2, fnx2);
    const d3 = bbFieldSub(fx3, fnx3);

    // alpha_diff = alpha * diff  (ext4 × ext4)
    const ad0 = bbExt4Mul0(a0, a1, a2, a3, d0, d1, d2, d3);
    const ad1 = bbExt4Mul1(a0, a1, a2, a3, d0, d1, d2, d3);
    const ad2 = bbExt4Mul2(a0, a1, a2, a3, d0, d1, d2, d3);
    const ad3 = bbExt4Mul3(a0, a1, a2, a3, d0, d1, d2, d3);

    // inv_2x = 1 / (2 * x)
    const inv2x = bbFieldInv(bbFieldMul(2n, x));

    // alpha_term = alpha_diff * inv(2x)  (ext4 × base scalar)
    const at0 = bbFieldMul(ad0, inv2x);
    const at1 = bbFieldMul(ad1, inv2x);
    const at2 = bbFieldMul(ad2, inv2x);
    const at3 = bbFieldMul(ad3, inv2x);

    // g(x²) = half_sum + alpha_term  (ext4 add)
    const g0 = bbFieldAdd(hs0, at0);
    const g1 = bbFieldAdd(hs1, at1);
    const g2 = bbFieldAdd(hs2, at2);
    const g3 = bbFieldAdd(hs3, at3);

    // Assert matches expected
    assert(g0 === eg0);
    assert(g1 === eg1);
    assert(g2 === eg2);
    assert(g3 === eg3);
  }
}
`;

describe('FRI Colinearity Vectors (Plonky3)', () => {
  const vf = loadVectors('fri_colinearity.json');
  const c = TestContract.fromSource(friSource, {});

  const accept = vf.vectors.filter((v) => v.expected === 'accept');
  const reject = vf.vectors.filter((v) => v.expected === 'reject');

  describe('accept', () => {
    it.each(accept.map((v, i) => [i, v.description, v] as const))(
      'vec[%d]: %s',
      (_i, _desc, vec) => {
        const r = c.call('verify', {
          x: BigInt(vec.x),
          fx0: BigInt(vec.f_x[0]), fx1: BigInt(vec.f_x[1]),
          fx2: BigInt(vec.f_x[2]), fx3: BigInt(vec.f_x[3]),
          fnx0: BigInt(vec.f_neg_x[0]), fnx1: BigInt(vec.f_neg_x[1]),
          fnx2: BigInt(vec.f_neg_x[2]), fnx3: BigInt(vec.f_neg_x[3]),
          a0: BigInt(vec.alpha[0]), a1: BigInt(vec.alpha[1]),
          a2: BigInt(vec.alpha[2]), a3: BigInt(vec.alpha[3]),
          eg0: BigInt(vec.expected_g_x2[0]), eg1: BigInt(vec.expected_g_x2[1]),
          eg2: BigInt(vec.expected_g_x2[2]), eg3: BigInt(vec.expected_g_x2[3]),
        });
        expect(r.success).toBe(true);
      },
    );
  });

  describe('reject', () => {
    it.each(reject.map((v, i) => [i, v.description, v] as const))(
      'vec[%d]: %s',
      (_i, _desc, vec) => {
        const r = c.call('verify', {
          x: BigInt(vec.x),
          fx0: BigInt(vec.f_x[0]), fx1: BigInt(vec.f_x[1]),
          fx2: BigInt(vec.f_x[2]), fx3: BigInt(vec.f_x[3]),
          fnx0: BigInt(vec.f_neg_x[0]), fnx1: BigInt(vec.f_neg_x[1]),
          fnx2: BigInt(vec.f_neg_x[2]), fnx3: BigInt(vec.f_neg_x[3]),
          a0: BigInt(vec.alpha[0]), a1: BigInt(vec.alpha[1]),
          a2: BigInt(vec.alpha[2]), a3: BigInt(vec.alpha[3]),
          eg0: BigInt(vec.expected_g_x2[0]), eg1: BigInt(vec.expected_g_x2[1]),
          eg2: BigInt(vec.expected_g_x2[2]), eg3: BigInt(vec.expected_g_x2[3]),
        });
        expect(r.success).toBe(false);
      },
    );
  });
});
