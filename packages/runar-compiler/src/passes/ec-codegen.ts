/**
 * EC codegen — secp256k1 elliptic curve operations for Bitcoin Script.
 *
 * Follows the slh-dsa-codegen.ts pattern: self-contained module imported by
 * 05-stack-lower.ts. Uses an ECTracker (similar to SLHTracker) for named
 * stack state tracking.
 *
 * Point representation: 64 bytes (x[32] || y[32], big-endian unsigned).
 *
 * Scalar multiplication uses homogeneous projective coordinates with the
 * Renes–Costello–Batina COMPLETE addition formulas (eprint 2015/1060,
 * Algorithms 8 and 9 specialised to a = 0). "Complete" means they have no
 * exceptional cases: they are correct when the two inputs are equal, when they
 * are inverses, and when either is the point at infinity. The point operand of
 * `ecMul` is contract input, so an incomplete formula is not merely a
 * correctness bug — it is an input the caller can choose to steer the
 * accumulator into a degenerate case. See ec-mul-scalars.test.ts.
 */

import type { StackOp } from '../ir/index.js';

// ===========================================================================
// Constants
// ===========================================================================

/** secp256k1 field prime p = 2^256 - 2^32 - 977 */
const FIELD_P = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2fn;
/** p - 2, used for Fermat's little theorem modular inverse */
const FIELD_P_MINUS_2 = FIELD_P - 2n;
/** secp256k1 curve order */
const CURVE_N = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141n;
/** secp256k1 generator x-coordinate */
const GEN_X = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798n;
/** secp256k1 generator y-coordinate */
const GEN_Y = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8n;

function bigintToBytes32(n: bigint): Uint8Array {
  const bytes = new Uint8Array(32);
  let v = n;
  for (let i = 31; i >= 0; i--) {
    bytes[i] = Number(v & 0xffn);
    v >>= 8n;
  }
  return bytes;
}

// ===========================================================================
// ECTracker — named stack state tracker (mirrors SLHTracker)
// ===========================================================================

export class ECTracker {
  nm: (string | null)[];
  _e: (op: StackOp) => void;

  constructor(init: (string | null)[], emit: (op: StackOp) => void) {
    this.nm = [...init];
    this._e = emit;
  }

  get depth(): number { return this.nm.length; }

  findDepth(name: string): number {
    for (let i = this.nm.length - 1; i >= 0; i--)
      if (this.nm[i] === name)
        return this.nm.length - 1 - i;
    throw new Error(`ECTracker: '${name}' not on stack [${this.nm.join(',')}]`);
  }

  pushBytes(n: string, v: Uint8Array): void { this._e({ op: 'push', value: v }); this.nm.push(n); }
  pushInt(n: string, v: bigint): void { this._e({ op: 'push', value: v }); this.nm.push(n); }
  dup(n: string): void { this._e({ op: 'dup' }); this.nm.push(n); }
  drop(): void { this._e({ op: 'drop' }); this.nm.pop(); }
  nip(): void {
    this._e({ op: 'nip' });
    const L = this.nm.length;
    if (L >= 2) this.nm.splice(L - 2, 1);
  }
  over(n: string): void { this._e({ op: 'over' }); this.nm.push(n); }
  swap(): void {
    this._e({ op: 'swap' });
    const L = this.nm.length;
    if (L >= 2) {
      const t = this.nm[L - 1];
      this.nm[L - 1] = this.nm[L - 2]!;
      this.nm[L - 2] = t!;
    }
  }
  rot(): void {
    this._e({ op: 'rot' });
    const L = this.nm.length;
    if (L >= 3) {
      const r = this.nm.splice(L - 3, 1)[0]!;
      this.nm.push(r);
    }
  }
  op(code: string): void { this._e({ op: 'opcode', code }); }
  roll(d: number): void {
    if (d === 0) return;
    if (d === 1) { this.swap(); return; }
    if (d === 2) { this.rot(); return; }
    this._e({ op: 'push', value: BigInt(d) });
    this.nm.push(null);
    this._e({ op: 'roll', depth: d });
    this.nm.pop();
    const idx = this.nm.length - 1 - d;
    const r = this.nm.splice(idx, 1)[0] ?? null;
    this.nm.push(r);
  }
  pick(d: number, n: string): void {
    if (d === 0) { this.dup(n); return; }
    if (d === 1) { this.over(n); return; }
    this._e({ op: 'push', value: BigInt(d) });
    this.nm.push(null);
    this._e({ op: 'pick', depth: d });
    this.nm.pop();
    this.nm.push(n);
  }
  toTop(name: string): void { this.roll(this.findDepth(name)); }
  copyToTop(name: string, n?: string): void { this.pick(this.findDepth(name), n ?? name); }
  toAlt(): void { this.op('OP_TOALTSTACK'); this.nm.pop(); }
  fromAlt(n: string): void { this.op('OP_FROMALTSTACK'); this.nm.push(n); }
  rename(n: string): void {
    if (this.nm.length > 0)
      this.nm[this.nm.length - 1] = n;
  }

  /** Emit raw opcodes tracking only net stack effect. */
  rawBlock(consume: string[], produce: string | null, fn: (e: (op: StackOp) => void) => void): void {
    for (let i = consume.length - 1; i >= 0; i--)
      this.nm.pop();
    fn(this._e);
    if (produce !== null)
      this.nm.push(produce);
  }

  /** Emit if/else with tracked stack effect. */
  emitIf(condName: string, thenFn: (e: (op: StackOp) => void) => void, elseFn: (e: (op: StackOp) => void) => void, resultName: string | null): void {
    this.toTop(condName);
    this.nm.pop(); // condition consumed
    const thenOps: StackOp[] = [];
    const elseOps: StackOp[] = [];
    thenFn((op) => thenOps.push(op));
    elseFn((op) => elseOps.push(op));
    this._e({ op: 'if', then: thenOps, else: elseOps });
    if (resultName !== null)
      this.nm.push(resultName);
  }
}

// ===========================================================================
// Field arithmetic helpers
// ===========================================================================

/** Push the field prime p onto the stack as a script number. */
function pushFieldP(t: ECTracker, name: string): void {
  // Push p directly as a BigInt — the emit pass encodes it as a proper
  // little-endian sign-magnitude script number push.
  t.pushInt(name, FIELD_P);
}

/**
 * fieldMod: reduce TOS mod p, ensure non-negative.
 * Expects 'aName' to be on the tracker stack.
 */
function fieldMod(t: ECTracker, aName: string, resultName: string): void {
  t.toTop(aName);
  pushFieldP(t, '_fmod_p');
  // (a % p + p) % p
  t.rawBlock([aName, '_fmod_p'], resultName, (e) => {
    e({ op: 'opcode', code: 'OP_2DUP' }); // a p a p
    e({ op: 'opcode', code: 'OP_MOD' });   // a p (a%p)
    e({ op: 'rot' });                       // p (a%p) a
    e({ op: 'drop' });                      // p (a%p)
    e({ op: 'over' });                      // p (a%p) p
    e({ op: 'opcode', code: 'OP_ADD' });    // p (a%p+p)
    e({ op: 'swap' });                      // (a%p+p) p
    e({ op: 'opcode', code: 'OP_MOD' });    // ((a%p+p)%p)
  });
}

/** fieldAdd: (a + b) mod p */
function fieldAdd(t: ECTracker, aName: string, bName: string, resultName: string): void {
  t.toTop(aName);
  t.toTop(bName);
  t.rawBlock([aName, bName], '_fadd_sum', (e) => {
    e({ op: 'opcode', code: 'OP_ADD' });
  });
  fieldMod(t, '_fadd_sum', resultName);
}

/** fieldSub: (a - b) mod p (non-negative) */
function fieldSub(t: ECTracker, aName: string, bName: string, resultName: string): void {
  t.toTop(aName);
  t.toTop(bName);
  t.rawBlock([aName, bName], '_fsub_diff', (e) => {
    e({ op: 'opcode', code: 'OP_SUB' });
  });
  fieldMod(t, '_fsub_diff', resultName);
}

/** fieldMul: (a * b) mod p */
function fieldMul(t: ECTracker, aName: string, bName: string, resultName: string): void {
  t.toTop(aName);
  t.toTop(bName);
  t.rawBlock([aName, bName], '_fmul_prod', (e) => {
    e({ op: 'opcode', code: 'OP_MUL' });
  });
  fieldMod(t, '_fmul_prod', resultName);
}

/** fieldMulConst: (a * c) mod p where c is a small constant. Uses OP_2MUL for c=2. */
function fieldMulConst(t: ECTracker, aName: string, c: bigint, resultName: string): void {
  t.toTop(aName);
  t.rawBlock([aName], '_fmc_prod', (e) => {
    if (c === 2n) {
      e({ op: 'opcode', code: 'OP_2MUL' });
    } else {
      e({ op: 'push', value: c });
      e({ op: 'opcode', code: 'OP_MUL' });
    }
  });
  fieldMod(t, '_fmc_prod', resultName);
}

/** fieldSqr: (a * a) mod p */
function fieldSqr(t: ECTracker, aName: string, resultName: string): void {
  t.copyToTop(aName, '_fsqr_copy');
  fieldMul(t, aName, '_fsqr_copy', resultName);
}

/**
 * fieldInv: a^(p-2) mod p via square-and-multiply.
 * Consumes aName from the tracker.
 */
function fieldInv(t: ECTracker, aName: string, resultName: string): void {
  // p-2 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2D
  // Bits 255..32: 224 bits, all 1 except bit 32 which is 0
  // Bits 31..0: 0xFFFFFC2D

  // Start: result = a (bit 255 = 1)
  t.copyToTop(aName, '_inv_r');
  // Bits 254 down to 33: all 1's (222 bits). Bit 32 is 0 (handled below).
  for (let i = 0; i < 222; i++) {
    fieldSqr(t, '_inv_r', '_inv_r2');
    t.rename('_inv_r');
    t.copyToTop(aName, '_inv_a');
    fieldMul(t, '_inv_r', '_inv_a', '_inv_m');
    t.rename('_inv_r');
  }
  // Bit 32 is 0: square only (no multiply)
  fieldSqr(t, '_inv_r', '_inv_r2');
  t.rename('_inv_r');
  // Bits 31 down to 0 of p-2
  const lowBits = Number(FIELD_P_MINUS_2 & 0xffffffffn);
  for (let i = 31; i >= 0; i--) {
    fieldSqr(t, '_inv_r', '_inv_r2');
    t.rename('_inv_r');
    if ((lowBits >> i) & 1) {
      t.copyToTop(aName, '_inv_a');
      fieldMul(t, '_inv_r', '_inv_a', '_inv_m');
      t.rename('_inv_r');
    }
  }
  // Clean up original input and rename result
  t.toTop(aName);
  t.drop();
  t.toTop('_inv_r');
  t.rename(resultName);
}

// ===========================================================================
// Point decompose / compose
// ===========================================================================

/**
 * Decompose 64-byte Point → (x_num, y_num) on stack.
 * Consumes pointName, produces xName and yName.
 */
function decomposePoint(t: ECTracker, pointName: string, xName: string, yName: string): void {
  t.toTop(pointName);
  // OP_SPLIT at 32 produces x_bytes (bottom) and y_bytes (top)
  t.rawBlock([pointName], null, (e) => {
    e({ op: 'push', value: 32n });
    e({ op: 'opcode', code: 'OP_SPLIT' });
  });
  // Manually track the two new items
  t.nm.push('_dp_xb');
  t.nm.push('_dp_yb');

  // Convert y_bytes (on top) to num
  // Reverse from BE to LE, append 0x00 sign byte to ensure unsigned, then BIN2NUM
  t.rawBlock(['_dp_yb'], yName, (e) => {
    emitReverse32(e);
    e({ op: 'push', value: new Uint8Array([0x00]) });
    e({ op: 'opcode', code: 'OP_CAT' });
    e({ op: 'opcode', code: 'OP_BIN2NUM' });
  });

  // Convert x_bytes to num
  t.toTop('_dp_xb');
  t.rawBlock(['_dp_xb'], xName, (e) => {
    emitReverse32(e);
    e({ op: 'push', value: new Uint8Array([0x00]) });
    e({ op: 'opcode', code: 'OP_CAT' });
    e({ op: 'opcode', code: 'OP_BIN2NUM' });
  });

  // Stack: [yName, xName] — swap to standard order [xName, yName]
  t.swap();
}

/**
 * Compose (x_num, y_num) → 64-byte Point.
 * Consumes xName and yName, produces resultName.
 */
function composePoint(t: ECTracker, xName: string, yName: string, resultName: string): void {
  // Convert x to 32-byte big-endian
  // Use NUM2BIN(33) to accommodate the sign byte, then drop the last byte
  t.toTop(xName);
  t.rawBlock([xName], '_cp_xb', (e) => {
    e({ op: 'push', value: 33n });
    e({ op: 'opcode', code: 'OP_NUM2BIN' });
    // Drop the sign byte (last byte) — split at 32, keep left
    e({ op: 'push', value: 32n });
    e({ op: 'opcode', code: 'OP_SPLIT' });
    e({ op: 'drop' });
    emitReverse32(e);
  });

  // Convert y to 32-byte big-endian
  t.toTop(yName);
  t.rawBlock([yName], '_cp_yb', (e) => {
    e({ op: 'push', value: 33n });
    e({ op: 'opcode', code: 'OP_NUM2BIN' });
    e({ op: 'push', value: 32n });
    e({ op: 'opcode', code: 'OP_SPLIT' });
    e({ op: 'drop' });
    emitReverse32(e);
  });

  // Cat: x_be || y_be (x is below y after the two toTop calls)
  t.toTop('_cp_xb');
  t.toTop('_cp_yb');
  t.rawBlock(['_cp_xb', '_cp_yb'], resultName, (e) => {
    e({ op: 'opcode', code: 'OP_CAT' });
  });
}

/**
 * Emit inline byte reversal for a 32-byte value on TOS.
 * After: reversed 32-byte value on TOS.
 */
function emitReverse32(e: (op: StackOp) => void): void {
  // Push empty accumulator, swap with data
  e({ op: 'opcode', code: 'OP_0' });
  e({ op: 'swap' });
  // 32 iterations: peel first byte, prepend to accumulator
  for (let i = 0; i < 32; i++) {
    // Stack: [accum, remaining]
    e({ op: 'push', value: 1n });
    e({ op: 'opcode', code: 'OP_SPLIT' });
    // Stack: [accum, byte0, rest]
    e({ op: 'rot' });
    // Stack: [byte0, rest, accum]
    e({ op: 'rot' });
    // Stack: [rest, accum, byte0]
    e({ op: 'swap' });
    // Stack: [rest, byte0, accum]
    e({ op: 'opcode', code: 'OP_CAT' });
    // Stack: [rest, byte0||accum]
    e({ op: 'swap' });
    // Stack: [byte0||accum, rest]
  }
  // Stack: [reversed, empty]
  e({ op: 'drop' });
}

// ===========================================================================
// Affine point addition (for ecAdd)
// ===========================================================================

/**
 * Affine point addition: expects px, py, qx, qy on tracker.
 * Produces rx, ry. Consumes all four inputs.
 */
function affineAdd(t: ECTracker): void {
  // The chord slope s = (qy - py) / (qx - px) is undefined when P == Q: the
  // denominator is zero and the correct slope is the TANGENT, 3px^2 / (2py).
  // Without this, ecAdd(P, P) silently produced a wrong point, so every
  // contract that doubled deployed an unspendable script — byte-identically
  // across all seven tiers, because they all shared the same omission.
  //
  // Both cases are the same shape, `s = num / den`, so only the NUMERATOR and
  // DENOMINATOR are selected; the single expensive fieldInv is still performed
  // exactly once. rx = s^2 - px - qx and ry = s*(px - rx) - py are already
  // correct for doubling (px == qx makes the first s^2 - 2px).
  //
  //   cond = (px == qx)                      1 when doubling, else 0
  //   num  = cond ? 3*px^2 : (qy - py)
  //   den  = cond ? 2*py   : (qx - px)
  //
  // selected as `b + cond*(a - b)` over the field, which needs no branch and
  // so keeps the emitted op sequence — and the tracker's static stack model —
  // identical on both paths.
  //
  // NOT handled: P == -Q (px == qx, py == -qy), whose true result is the point
  // at infinity. secp256k1 affine coordinates cannot represent it, so this
  // returns a garbage point exactly as it did before this fix. Callers that
  // can hit that case must guard it themselves.
  t.copyToTop('px', '_px_eq');
  t.copyToTop('qx', '_qx_eq');
  t.rawBlock(['_px_eq', '_qx_eq'], '_cond', (e) => {
    e({ op: 'opcode', code: 'OP_NUMEQUAL' });
  });

  // chord numerator / denominator
  t.copyToTop('qy', '_qy1');
  t.copyToTop('py', '_py1');
  fieldSub(t, '_qy1', '_py1', '_num_chord');
  t.copyToTop('qx', '_qx1');
  t.copyToTop('px', '_px1');
  fieldSub(t, '_qx1', '_px1', '_den_chord');

  // tangent numerator / denominator: 3*px^2 and 2*py
  t.copyToTop('px', '_px_t');
  fieldSqr(t, '_px_t', '_px_sq');
  fieldMulConst(t, '_px_sq', 3n, '_num_tan');
  t.copyToTop('py', '_py_t');
  fieldMulConst(t, '_py_t', 2n, '_den_tan');

  // num = num_chord + cond*(num_tan - num_chord)
  t.copyToTop('_num_chord', '_num_chord_c');
  fieldSub(t, '_num_tan', '_num_chord_c', '_num_diff');
  t.copyToTop('_cond', '_cond_n');
  fieldMul(t, '_num_diff', '_cond_n', '_num_sel');
  fieldAdd(t, '_num_chord', '_num_sel', '_s_num');

  // den = den_chord + cond*(den_tan - den_chord)
  t.copyToTop('_den_chord', '_den_chord_c');
  fieldSub(t, '_den_tan', '_den_chord_c', '_den_diff');
  t.toTop('_cond');
  t.rename('_cond_d');
  fieldMul(t, '_den_diff', '_cond_d', '_den_sel');
  fieldAdd(t, '_den_chord', '_den_sel', '_s_den');

  // s = s_num / s_den mod p
  fieldInv(t, '_s_den', '_s_den_inv');
  fieldMul(t, '_s_num', '_s_den_inv', '_s');

  // rx = s² - px - qx mod p
  t.copyToTop('_s', '_s_keep');
  fieldSqr(t, '_s', '_s2');
  t.copyToTop('px', '_px2');
  fieldSub(t, '_s2', '_px2', '_rx1');
  t.copyToTop('qx', '_qx2');
  fieldSub(t, '_rx1', '_qx2', 'rx');

  // ry = s * (px - rx) - py mod p
  t.copyToTop('px', '_px3');
  t.copyToTop('rx', '_rx2');
  fieldSub(t, '_px3', '_rx2', '_px_rx');
  fieldMul(t, '_s_keep', '_px_rx', '_s_px_rx');
  t.copyToTop('py', '_py2');
  fieldSub(t, '_s_px_rx', '_py2', 'ry');

  // Clean up original points
  t.toTop('px'); t.drop();
  t.toTop('py'); t.drop();
  t.toTop('qx'); t.drop();
  t.toTop('qy'); t.drop();
}

// ===========================================================================
// Projective point operations (for ecMul) — RCB complete formulas, a = 0
// ===========================================================================

/**
 * scalarMod: reduce TOS mod n (the curve ORDER, not the field prime), result
 * non-negative. Same shape as fieldMod but with a different modulus.
 *
 * This defines the scalar domain of ecMul over the whole of script-number
 * space: negative scalars and scalars >= n both reduce into [0, n-1], and
 * k = 0 / k = n give the point at infinity. Under the old ladder anything
 * outside [1, n-1] was undefined behaviour.
 */
function scalarModN(t: ECTracker, aName: string, resultName: string): void {
  t.toTop(aName);
  t.pushInt('_smod_n', CURVE_N);
  t.rawBlock([aName, '_smod_n'], resultName, (e) => {
    e({ op: 'opcode', code: 'OP_2DUP' });
    e({ op: 'opcode', code: 'OP_MOD' });
    e({ op: 'rot' });
    e({ op: 'drop' });
    e({ op: 'over' });
    e({ op: 'opcode', code: 'OP_ADD' });
    e({ op: 'swap' });
    e({ op: 'opcode', code: 'OP_MOD' });
  });
}

/**
 * Projective point doubling — RCB Algorithm 9 (a = 0), 6M + 2S + 1 m_3b.
 * Expects jx, jy, jz on the tracker; replaces them with the doubled point.
 *
 * Complete: doubling the point at infinity (0 : 1 : 0) yields (0 : 1 : 0).
 *
 * Deviations from the paper, both exact mod p and strictly cheaper here
 * (a multiply by a small constant costs one push + OP_MUL, an addition costs
 * a full reduce): line 2-4's `Z3 = 8*t0` is one mulConst rather than three
 * doublings, and line 11-12's `t2 = 3*t2` is one mulConst rather than two adds.
 */
function projectiveDouble(t: ECTracker): void {
  // Copies of the inputs that outlive their first consumer.
  t.copyToTop('jy', '_d_yz');       // t1 = Y*Z
  t.copyToTop('jy', '_d_xy');       // t1 = X*Y  (line 16)
  t.copyToTop('jz', '_d_zz_src');   // t2 = Z*Z

  fieldSqr(t, 'jy', '_d_t0');                       // t0 = Y^2
  t.copyToTop('_d_t0', '_d_t0a');
  fieldMulConst(t, '_d_t0a', 8n, '_d_Z3');          // Z3 = 8*t0
  fieldMul(t, '_d_yz', 'jz', '_d_t1');              // t1 = Y*Z
  fieldSqr(t, '_d_zz_src', '_d_zz');                // Z^2
  fieldMulConst(t, '_d_zz', 21n, '_d_t2');          // t2 = b3*Z^2   (b3 = 3*7)

  t.copyToTop('_d_t2', '_d_t2a');
  t.copyToTop('_d_Z3', '_d_Z3a');
  fieldMul(t, '_d_t2a', '_d_Z3a', '_d_X3');         // X3 = t2*Z3

  t.copyToTop('_d_t0', '_d_t0b');
  t.copyToTop('_d_t2', '_d_t2b');
  fieldAdd(t, '_d_t0b', '_d_t2b', '_d_Y3');         // Y3 = t0+t2

  fieldMul(t, '_d_t1', '_d_Z3', '_d_Z3n');          // Z3 = t1*Z3
  fieldMulConst(t, '_d_t2', 3n, '_d_t2c');          // t2 = 3*t2
  fieldSub(t, '_d_t0', '_d_t2c', '_d_t0n');         // t0 = t0-t2

  t.copyToTop('_d_t0n', '_d_t0na');
  fieldMul(t, '_d_t0na', '_d_Y3', '_d_Y3b');        // Y3 = t0*Y3
  fieldAdd(t, '_d_X3', '_d_Y3b', '_d_Y3c');         // Y3 = X3+Y3

  fieldMul(t, 'jx', '_d_xy', '_d_xyv');             // t1 = X*Y
  fieldMul(t, '_d_t0n', '_d_xyv', '_d_X3b');        // X3 = t0*t1
  fieldMulConst(t, '_d_X3b', 2n, '_d_X3c');         // X3 = X3+X3

  t.toTop('_d_X3c'); t.rename('jx');
  t.toTop('_d_Y3c'); t.rename('jy');
  t.toTop('_d_Z3n'); t.rename('jz');
}

/**
 * Projective → affine conversion. Consumes jx, jy, jz; produces rxName, ryName.
 *
 * fieldInv is Fermat exponentiation, so inv(0) = 0: the point at infinity
 * (Z = 0) converts to (0, 0), which is the all-zero Point blob. That is the
 * agreed encoding for infinity — it is not a curve point, so it cannot be
 * confused with a real result.
 */
function projectiveToAffine(t: ECTracker, rxName: string, ryName: string): void {
  fieldInv(t, 'jz', '_zinv');
  t.copyToTop('_zinv', '_zinv_b');
  fieldMul(t, 'jx', '_zinv', rxName);
  fieldMul(t, 'jy', '_zinv_b', ryName);
}

// ===========================================================================
// Projective mixed addition (P_projective + Q_affine)
// ===========================================================================

/**
 * Build complete mixed-add ops for use inside OP_IF — RCB Algorithm 8 (a = 0),
 * 11M + 2 m_3b. Adds the affine base point (ax, ay) into the accumulator.
 *
 * Complete: no exceptional cases. In particular
 *   - accumulator == Q          -> correctly doubles (this is the case that
 *                                  broke ecMul(P, 2n): the old Jacobian
 *                                  mixed-add computed H = R = 0 and returned
 *                                  the zero point, which then absorbed every
 *                                  remaining iteration)
 *   - accumulator == -Q         -> correctly yields the point at infinity
 *   - accumulator == infinity   -> correctly yields Q
 *
 * Uses an inner ECTracker cloned from the outer one, because the ops run
 * under OP_IF: the outer tracker's model must describe the stack for BOTH
 * branches, so this block has to be stack-shape neutral — same names, same
 * depths, with jx/jy/jz replaced in place.
 *
 * Stack layout: [..., ax, ay, _k, jx, jy, jz]
 * After:        [..., ax, ay, _k, jx', jy', jz']
 */
function buildProjectiveAddMixedInline(e: (op: StackOp) => void, t: ECTracker): void {
  const it = new ECTracker([...t.nm], e);

  // The affine base survives every iteration, so only ever consume copies.
  it.copyToTop('ax', '_m_x2a');   // t0 = X1*X2
  it.copyToTop('ax', '_m_x2b');   // X2+Y2
  it.copyToTop('ax', '_m_x2c');   // X2*Z1
  it.copyToTop('ay', '_m_y2a');   // t1 = Y1*Y2
  it.copyToTop('ay', '_m_y2b');   // X2+Y2
  it.copyToTop('ay', '_m_y2c');   // Y2*Z1
  it.copyToTop('jx', '_m_x1a');   // X1+Y1
  it.copyToTop('jx', '_m_x1b');   // Y3+X1
  it.copyToTop('jy', '_m_y1a');   // X1+Y1
  it.copyToTop('jy', '_m_y1b');   // t4+Y1
  it.copyToTop('jz', '_m_z1a');   // X2*Z1
  it.copyToTop('jz', '_m_z1b');   // b3*Z1

  fieldMul(it, 'jx', '_m_x2a', '_m_t0');            // t0 = X1*X2
  fieldMul(it, 'jy', '_m_y2a', '_m_t1');            // t1 = Y1*Y2
  fieldAdd(it, '_m_x2b', '_m_y2b', '_m_s1');        // X2+Y2
  fieldAdd(it, '_m_x1a', '_m_y1a', '_m_s2');        // X1+Y1
  fieldMul(it, '_m_s1', '_m_s2', '_m_t3');          // t3 = (X2+Y2)(X1+Y1)

  it.copyToTop('_m_t0', '_m_t0a');
  it.copyToTop('_m_t1', '_m_t1a');
  fieldAdd(it, '_m_t0a', '_m_t1a', '_m_s3');        // t4 = t0+t1
  fieldSub(it, '_m_t3', '_m_s3', '_m_t3b');         // t3 = t3-t4

  fieldMul(it, '_m_y2c', 'jz', '_m_t4');            // t4 = Y2*Z1
  fieldAdd(it, '_m_t4', '_m_y1b', '_m_t4b');        // t4 = t4+Y1
  fieldMul(it, '_m_x2c', '_m_z1a', '_m_Y3');        // Y3 = X2*Z1
  fieldAdd(it, '_m_Y3', '_m_x1b', '_m_Y3b');        // Y3 = Y3+X1

  fieldMulConst(it, '_m_t0', 3n, '_m_t0b');         // t0 = 3*t0
  fieldMulConst(it, '_m_z1b', 21n, '_m_t2');        // t2 = b3*Z1

  it.copyToTop('_m_t1', '_m_t1b');
  it.copyToTop('_m_t2', '_m_t2a');
  fieldAdd(it, '_m_t1b', '_m_t2a', '_m_Z3');        // Z3 = t1+t2
  fieldSub(it, '_m_t1', '_m_t2', '_m_t1c');         // t1 = t1-t2
  fieldMulConst(it, '_m_Y3b', 21n, '_m_Y3c');       // Y3 = b3*Y3

  it.copyToTop('_m_Y3c', '_m_Y3ca');
  it.copyToTop('_m_t4b', '_m_t4ba');
  fieldMul(it, '_m_t4ba', '_m_Y3ca', '_m_X3');      // X3 = t4*Y3

  it.copyToTop('_m_t3b', '_m_t3ba');
  it.copyToTop('_m_t1c', '_m_t1ca');
  fieldMul(it, '_m_t3ba', '_m_t1ca', '_m_t2b');     // t2 = t3*t1
  fieldSub(it, '_m_t2b', '_m_X3', '_m_X3b');        // X3 = t2-X3

  it.copyToTop('_m_t0b', '_m_t0ba');
  fieldMul(it, '_m_Y3c', '_m_t0ba', '_m_Y3d');      // Y3 = Y3*t0

  it.copyToTop('_m_Z3', '_m_Z3a');
  fieldMul(it, '_m_t1c', '_m_Z3a', '_m_t1d');       // t1 = t1*Z3
  fieldAdd(it, '_m_t1d', '_m_Y3d', '_m_Y3e');       // Y3 = t1+Y3

  fieldMul(it, '_m_t0b', '_m_t3b', '_m_t0c');       // t0 = t0*t3
  fieldMul(it, '_m_Z3', '_m_t4b', '_m_Z3b');        // Z3 = Z3*t4
  fieldAdd(it, '_m_Z3b', '_m_t0c', '_m_Z3c');       // Z3 = Z3+t0

  it.toTop('_m_X3b'); it.rename('jx');
  it.toTop('_m_Y3e'); it.rename('jy');
  it.toTop('_m_Z3c'); it.rename('jz');
}

// ===========================================================================
// Public entry points (called from stack lowerer)
// ===========================================================================

/**
 * ecAdd: add two points.
 * Stack in: [point_a, point_b] (b on top)
 * Stack out: [result_point]
 */
export function emitEcAdd(emit: (op: StackOp) => void): void {
  const t = new ECTracker(['_pa', '_pb'], emit);
  decomposePoint(t, '_pa', 'px', 'py');
  decomposePoint(t, '_pb', 'qx', 'qy');
  affineAdd(t);
  composePoint(t, 'rx', 'ry', '_result');
}

/**
 * ecMul: scalar multiplication P * k.
 * Stack in: [point, scalar] (scalar on top)
 * Stack out: [result_point]
 *
 * 256-iteration MSB-first double-and-add over homogeneous projective
 * coordinates, using the RCB COMPLETE formulas. The accumulator starts at the
 * point at infinity, so every one of the 256 bits is handled uniformly.
 *
 * The previous version ran 257 iterations over k+3n with an accumulator seeded
 * at P, to guarantee a set leading bit. That relied on the INCOMPLETE Jacobian
 * mixed-add never being handed two equal points — which it was, for k = 2, on
 * the final iteration, yielding an all-zero point. No choice of offset avoids
 * this: every candidate multiple of n merely relocates the collision onto
 * different small scalars. Completeness is the only fix that holds for an
 * operand the caller chooses.
 */
export function emitEcMul(emit: (op: StackOp) => void): void {
  const t = new ECTracker(['_pt', '_k'], emit);
  decomposePoint(t, '_pt', 'ax', 'ay');

  // Reduce the scalar into [0, n-1] so the 256-bit ladder covers the whole
  // domain: negative k and k >= n are now defined rather than undefined.
  scalarModN(t, '_k', '_k');

  // Accumulator := point at infinity (0 : 1 : 0). Legal input to both complete
  // formulas, which is exactly why no special leading-bit handling is needed.
  t.pushInt('jx', 0n);
  t.pushInt('jy', 1n);
  t.pushInt('jz', 0n);

  // 256 iterations: bits 255 down to 0
  for (let bit = 255; bit >= 0; bit--) {
    projectiveDouble(t);

    // Extract bit: (k >> bit) & 1, using OP_RSHIFTNUM / OP_2DIV
    t.copyToTop('_k', '_k_copy');
    if (bit === 1) {
      // Single-bit shift: OP_2DIV (no push needed)
      t.rawBlock(['_k_copy'], '_shifted', (e) => {
        e({ op: 'opcode', code: 'OP_2DIV' });
      });
    } else if (bit > 1) {
      // Multi-bit shift: push shift amount, OP_RSHIFTNUM
      t.pushInt('_shift', BigInt(bit));
      t.rawBlock(['_k_copy', '_shift'], '_shifted', (e) => {
        e({ op: 'opcode', code: 'OP_RSHIFTNUM' });
      });
    } else {
      t.rename('_shifted');
    }
    t.pushInt('_two', 2n);
    t.rawBlock(['_shifted', '_two'], '_bit', (e) => {
      e({ op: 'opcode', code: 'OP_MOD' });
    });

    // Move _bit to TOS and remove from tracker BEFORE generating add ops,
    // because OP_IF consumes _bit and the add ops run with _bit already gone.
    t.toTop('_bit');
    t.nm.pop(); // _bit consumed by IF
    const addOps: StackOp[] = [];
    const addEmit = (op: StackOp) => addOps.push(op);
    buildProjectiveAddMixedInline(addEmit, t);
    emit({ op: 'if', then: addOps, else: [] });
  }

  projectiveToAffine(t, '_rx', '_ry');

  // Clean up
  t.toTop('ax'); t.drop();
  t.toTop('ay'); t.drop();
  t.toTop('_k'); t.drop();

  composePoint(t, '_rx', '_ry', '_result');
}

/**
 * ecMulGen: scalar multiplication G * k.
 * Stack in: [scalar]
 * Stack out: [result_point]
 */
export function emitEcMulGen(emit: (op: StackOp) => void): void {
  // Push generator point as 64-byte blob, then delegate to ecMul
  const gPoint = new Uint8Array(64);
  gPoint.set(bigintToBytes32(GEN_X), 0);
  gPoint.set(bigintToBytes32(GEN_Y), 32);
  emit({ op: 'push', value: gPoint });
  emit({ op: 'swap' }); // [point, scalar]
  emitEcMul(emit);
}

/**
 * ecNegate: negate a point (x, p - y).
 * Stack in: [point]
 * Stack out: [negated_point]
 */
export function emitEcNegate(emit: (op: StackOp) => void): void {
  const t = new ECTracker(['_pt'], emit);
  decomposePoint(t, '_pt', '_nx', '_ny');
  pushFieldP(t, '_fp');
  fieldSub(t, '_fp', '_ny', '_neg_y');
  composePoint(t, '_nx', '_neg_y', '_result');
}

/**
 * ecOnCurve: check if point is on secp256k1 (y² ≡ x³ + 7 mod p).
 * Stack in: [point]
 * Stack out: [boolean]
 */
export function emitEcOnCurve(emit: (op: StackOp) => void): void {
  const t = new ECTracker(['_pt'], emit);
  decomposePoint(t, '_pt', '_x', '_y');

  // GAP-301: coordinate canonicity. `decomposePoint` BIN2NUMs each coordinate
  // as an unsigned value that may be ≥ p; the field arithmetic below would
  // silently reduce it mod p, so a non-canonical encoding of a valid point
  // would pass. Reject it: require x < p AND y < p (coordinates are unsigned,
  // so the 0 ≤ lower bound holds by construction). Combined with the curve
  // equation at the end via OP_BOOLAND so ecOnCurve still returns a boolean.
  t.copyToTop('_x', '_x_lt');
  pushFieldP(t, '_p_for_x');
  t.rawBlock(['_x_lt', '_p_for_x'], '_x_canon', (e) => {
    e({ op: 'opcode', code: 'OP_LESSTHAN' });
  });
  t.copyToTop('_y', '_y_lt');
  pushFieldP(t, '_p_for_y');
  t.rawBlock(['_y_lt', '_p_for_y'], '_y_canon', (e) => {
    e({ op: 'opcode', code: 'OP_LESSTHAN' });
  });
  t.toTop('_x_canon');
  t.toTop('_y_canon');
  t.rawBlock(['_x_canon', '_y_canon'], '_canon', (e) => {
    e({ op: 'opcode', code: 'OP_BOOLAND' });
  });

  // lhs = y²
  fieldSqr(t, '_y', '_y2');

  // rhs = x³ + 7
  t.copyToTop('_x', '_x_copy');
  fieldSqr(t, '_x', '_x2');
  fieldMul(t, '_x2', '_x_copy', '_x3');
  t.pushInt('_seven', 7n);
  fieldAdd(t, '_x3', '_seven', '_rhs');

  // Compare curve equation
  t.toTop('_y2');
  t.toTop('_rhs');
  t.rawBlock(['_y2', '_rhs'], '_curve_eq', (e) => {
    e({ op: 'opcode', code: 'OP_EQUAL' });
  });

  // on-curve = canonical AND curve-equation
  t.toTop('_canon');
  t.toTop('_curve_eq');
  t.rawBlock(['_canon', '_curve_eq'], '_result', (e) => {
    e({ op: 'opcode', code: 'OP_BOOLAND' });
  });
}

/**
 * ecModReduce: ((value % mod) + mod) % mod
 * Stack in: [value, mod]
 * Stack out: [result]
 */
export function emitEcModReduce(emit: (op: StackOp) => void): void {
  emit({ op: 'opcode', code: 'OP_2DUP' });
  emit({ op: 'opcode', code: 'OP_MOD' });
  emit({ op: 'rot' });
  emit({ op: 'drop' });
  emit({ op: 'over' });
  emit({ op: 'opcode', code: 'OP_ADD' });
  emit({ op: 'swap' });
  emit({ op: 'opcode', code: 'OP_MOD' });
}

/**
 * ecEncodeCompressed: point → 33-byte compressed pubkey.
 * Stack in: [point (64 bytes)]
 * Stack out: [compressed (33 bytes)]
 */
export function emitEcEncodeCompressed(emit: (op: StackOp) => void): void {
  // Split at 32: [x_bytes, y_bytes]
  emit({ op: 'push', value: 32n });
  emit({ op: 'opcode', code: 'OP_SPLIT' });
  // Get last byte of y for parity
  emit({ op: 'opcode', code: 'OP_SIZE' });
  emit({ op: 'push', value: 1n });
  emit({ op: 'opcode', code: 'OP_SUB' });
  emit({ op: 'opcode', code: 'OP_SPLIT' });
  // Stack: [x_bytes, y_prefix, last_byte]
  emit({ op: 'opcode', code: 'OP_BIN2NUM' });
  emit({ op: 'push', value: 2n });
  emit({ op: 'opcode', code: 'OP_MOD' });
  // Stack: [x_bytes, y_prefix, parity]
  emit({ op: 'swap' });
  emit({ op: 'drop' }); // drop y_prefix
  // Stack: [x_bytes, parity]
  emit({ op: 'if',
    then: [{ op: 'push', value: new Uint8Array([0x03]) }],
    else: [{ op: 'push', value: new Uint8Array([0x02]) }],
  });
  // Stack: [x_bytes, prefix_byte]
  emit({ op: 'swap' });
  emit({ op: 'opcode', code: 'OP_CAT' });
}

/**
 * ecMakePoint: (x: bigint, y: bigint) → Point.
 * Stack in: [x_num, y_num] (y on top)
 * Stack out: [point_bytes (64 bytes)]
 */
export function emitEcMakePoint(emit: (op: StackOp) => void): void {
  // Convert y to 32 bytes big-endian (NUM2BIN(33) to handle sign byte, then take first 32)
  emit({ op: 'push', value: 33n });
  emit({ op: 'opcode', code: 'OP_NUM2BIN' });
  emit({ op: 'push', value: 32n });
  emit({ op: 'opcode', code: 'OP_SPLIT' });
  emit({ op: 'drop' });
  emitReverse32(emit);
  // Stack: [x_num, y_be]
  emit({ op: 'swap' });
  // Stack: [y_be, x_num]
  emit({ op: 'push', value: 33n });
  emit({ op: 'opcode', code: 'OP_NUM2BIN' });
  emit({ op: 'push', value: 32n });
  emit({ op: 'opcode', code: 'OP_SPLIT' });
  emit({ op: 'drop' });
  emitReverse32(emit);
  // Stack: [y_be, x_be]
  emit({ op: 'swap' });
  // Stack: [x_be, y_be]
  emit({ op: 'opcode', code: 'OP_CAT' });
}

/**
 * ecPointX: extract x-coordinate from Point.
 * Stack in: [point (64 bytes)]
 * Stack out: [x as bigint]
 */
export function emitEcPointX(emit: (op: StackOp) => void): void {
  emit({ op: 'push', value: 32n });
  emit({ op: 'opcode', code: 'OP_SPLIT' });
  emit({ op: 'drop' });
  emitReverse32(emit);
  // Append 0x00 sign byte to ensure unsigned interpretation
  emit({ op: 'push', value: new Uint8Array([0x00]) });
  emit({ op: 'opcode', code: 'OP_CAT' });
  emit({ op: 'opcode', code: 'OP_BIN2NUM' });
}

/**
 * ecPointY: extract y-coordinate from Point.
 * Stack in: [point (64 bytes)]
 * Stack out: [y as bigint]
 */
export function emitEcPointY(emit: (op: StackOp) => void): void {
  emit({ op: 'push', value: 32n });
  emit({ op: 'opcode', code: 'OP_SPLIT' });
  emit({ op: 'swap' });
  emit({ op: 'drop' });
  emitReverse32(emit);
  // Append 0x00 sign byte to ensure unsigned interpretation
  emit({ op: 'push', value: new Uint8Array([0x00]) });
  emit({ op: 'opcode', code: 'OP_CAT' });
  emit({ op: 'opcode', code: 'OP_BIN2NUM' });
}
