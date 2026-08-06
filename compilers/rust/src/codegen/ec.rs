//! EC codegen — secp256k1 elliptic curve operations for Bitcoin Script.
//!
//! Port of packages/runar-compiler/src/passes/ec-codegen.ts.
//! All helpers are self-contained.
//!
//! Point representation: 64 bytes (x[32] || y[32], big-endian unsigned).
//! Internal arithmetic uses Jacobian coordinates for scalar multiplication.

use num_bigint::BigInt;
use super::stack::{PushValue, StackOp};

// ===========================================================================
// Constants
// ===========================================================================

/// Low 32 bits of (p - 2) = 0xFFFFFC2D.
const FIELD_P_MINUS_2_LOW32: u32 = 0xFFFF_FC2D;

/// secp256k1 curve ORDER n as a script number (little-endian sign-magnitude).
/// The MSB has bit 7 set, so a 0x00 sign byte keeps it positive.
const CURVE_N_SCRIPT_NUM: [u8; 33] = [
    0x41, 0x41, 0x36, 0xd0, 0x8c, 0x5e, 0xd2, 0xbf, 0x3b, 0xa0, 0x48, 0xaf,
    0xe6, 0xdc, 0xae, 0xba, 0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00,
];

/// secp256k1 generator x-coordinate (32 bytes, big-endian).
const GEN_X_BYTES: [u8; 32] = [
    0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0, 0x62, 0x95,
    0xce, 0x87, 0x0b, 0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9,
    0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8, 0x17, 0x98,
];

/// secp256k1 generator y-coordinate (32 bytes, big-endian).
const GEN_Y_BYTES: [u8; 32] = [
    0x48, 0x3a, 0xda, 0x77, 0x26, 0xa3, 0xc4, 0x65, 0x5d, 0xa4, 0xfb, 0xfc,
    0x0e, 0x11, 0x08, 0xa8, 0xfd, 0x17, 0xb4, 0x48, 0xa6, 0x85, 0x54, 0x19,
    0x9c, 0x47, 0xd0, 0x8f, 0xfb, 0x10, 0xd4, 0xb8,
];

/// Collect ops into a Vec via closure.
fn collect_ops(f: impl FnOnce(&mut dyn FnMut(StackOp))) -> Vec<StackOp> {
    let mut ops = Vec::new();
    f(&mut |op| ops.push(op));
    ops
}

// ===========================================================================
// ECTracker — named stack state tracker (mirrors SLHTracker)
// ===========================================================================

struct ECTracker<'a> {
    nm: Vec<String>,
    e: &'a mut dyn FnMut(StackOp),
}

#[allow(dead_code)]
impl<'a> ECTracker<'a> {
    fn new(init: &[&str], emit: &'a mut dyn FnMut(StackOp)) -> Self {
        ECTracker {
            nm: init.iter().map(|s| s.to_string()).collect(),
            e: emit,
        }
    }

    fn depth(&self) -> usize {
        self.nm.len()
    }

    fn find_depth(&self, name: &str) -> usize {
        for i in (0..self.nm.len()).rev() {
            if self.nm[i] == name {
                return self.nm.len() - 1 - i;
            }
        }
        panic!("ECTracker: '{}' not on stack {:?}", name, self.nm);
    }

    fn push_bytes(&mut self, n: &str, v: Vec<u8>) {
        (self.e)(StackOp::Push(PushValue::Bytes(v)));
        self.nm.push(n.to_string());
    }

    fn push_int(&mut self, n: &str, v: i128) {
        (self.e)(StackOp::Push(PushValue::Int(BigInt::from(v))));
        self.nm.push(n.to_string());
    }

    fn dup(&mut self, n: &str) {
        (self.e)(StackOp::Dup);
        self.nm.push(n.to_string());
    }

    fn drop(&mut self) {
        (self.e)(StackOp::Drop);
        if !self.nm.is_empty() {
            self.nm.pop();
        }
    }

    fn nip(&mut self) {
        (self.e)(StackOp::Nip);
        let len = self.nm.len();
        if len >= 2 {
            self.nm.remove(len - 2);
        }
    }

    fn over(&mut self, n: &str) {
        (self.e)(StackOp::Over);
        self.nm.push(n.to_string());
    }

    fn swap(&mut self) {
        (self.e)(StackOp::Swap);
        let len = self.nm.len();
        if len >= 2 {
            self.nm.swap(len - 1, len - 2);
        }
    }

    fn rot(&mut self) {
        (self.e)(StackOp::Rot);
        let len = self.nm.len();
        if len >= 3 {
            let r = self.nm.remove(len - 3);
            self.nm.push(r);
        }
    }

    fn op(&mut self, code: &str) {
        (self.e)(StackOp::Opcode(code.into()));
    }

    fn roll(&mut self, d: usize) {
        if d == 0 {
            return;
        }
        if d == 1 {
            self.swap();
            return;
        }
        if d == 2 {
            self.rot();
            return;
        }
        (self.e)(StackOp::Push(PushValue::Int(BigInt::from(d as i128))));
        self.nm.push(String::new());
        (self.e)(StackOp::Opcode("OP_ROLL".into()));
        self.nm.pop(); // pop the push
        let idx = self.nm.len() - 1 - d;
        let r = self.nm.remove(idx);
        self.nm.push(r);
    }

    fn pick(&mut self, d: usize, n: &str) {
        if d == 0 {
            self.dup(n);
            return;
        }
        if d == 1 {
            self.over(n);
            return;
        }
        (self.e)(StackOp::Push(PushValue::Int(BigInt::from(d as i128))));
        self.nm.push(String::new());
        (self.e)(StackOp::Opcode("OP_PICK".into()));
        self.nm.pop(); // pop the push
        self.nm.push(n.to_string());
    }

    fn to_top(&mut self, name: &str) {
        let d = self.find_depth(name);
        self.roll(d);
    }

    fn copy_to_top(&mut self, name: &str, n: &str) {
        let d = self.find_depth(name);
        self.pick(d, n);
    }

    fn to_alt(&mut self) {
        self.op("OP_TOALTSTACK");
        if !self.nm.is_empty() {
            self.nm.pop();
        }
    }

    fn from_alt(&mut self, n: &str) {
        self.op("OP_FROMALTSTACK");
        self.nm.push(n.to_string());
    }

    fn rename(&mut self, n: &str) {
        if let Some(last) = self.nm.last_mut() {
            *last = n.to_string();
        }
    }

    /// Emit raw opcodes; tracker only records net stack effect.
    fn raw_block(
        &mut self,
        consume: &[&str],
        produce: Option<&str>,
        f: impl FnOnce(&mut dyn FnMut(StackOp)),
    ) {
        for _ in consume {
            if !self.nm.is_empty() {
                self.nm.pop();
            }
        }
        f(self.e);
        if let Some(p) = produce {
            self.nm.push(p.to_string());
        }
    }

    /// Emit if/else with tracked stack effect.
    fn emit_if(
        &mut self,
        cond_name: &str,
        then_fn: impl FnOnce(&mut dyn FnMut(StackOp)),
        else_fn: impl FnOnce(&mut dyn FnMut(StackOp)),
        result_name: Option<&str>,
    ) {
        self.to_top(cond_name);
        self.nm.pop(); // condition consumed
        let then_ops = collect_ops(then_fn);
        let else_ops = collect_ops(else_fn);
        (self.e)(StackOp::If {
            then_ops,
            else_ops,
        });
        if let Some(rn) = result_name {
            self.nm.push(rn.to_string());
        }
    }
}

// ===========================================================================
// Field arithmetic helpers
// ===========================================================================

/// secp256k1 field prime p as a Bitcoin script number (little-endian sign-magnitude).
/// p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
/// Big-endian bytes [0..31]:
///   [ff]*27, fe, ff, ff, fc, 2f
/// Reversed to LE (byte 31 first):
///   2f, fc, ff, ff, fe, [ff]*27
/// MSB (0xff) has bit 7 set, so we append a 0x00 sign byte to keep it positive.
const FIELD_P_SCRIPT_NUM: [u8; 33] = [
    0x2f, 0xfc, 0xff, 0xff, 0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00,
];

/// Push the field prime p onto the stack as a script number.
fn push_field_p(t: &mut ECTracker, name: &str) {
    // Push p as pre-encoded script number bytes — equivalent to pushInt(FIELD_P)
    // in the TS implementation, but using bytes since FIELD_P exceeds i128.
    t.push_bytes(name, FIELD_P_SCRIPT_NUM.to_vec());
}

/// fieldMod: reduce TOS mod p, ensure non-negative.
/// Expects `a_name` to be on the tracker stack.
fn field_mod(t: &mut ECTracker, a_name: &str, result_name: &str) {
    t.to_top(a_name);
    push_field_p(t, "_fmod_p");
    // (a % p + p) % p
    t.raw_block(&[a_name, "_fmod_p"], Some(result_name), |e| {
        e(StackOp::Opcode("OP_2DUP".into())); // a p a p
        e(StackOp::Opcode("OP_MOD".into()));   // a p (a%p)
        e(StackOp::Rot);                        // p (a%p) a
        e(StackOp::Drop);                       // p (a%p)
        e(StackOp::Over);                       // p (a%p) p
        e(StackOp::Opcode("OP_ADD".into()));    // p (a%p+p)
        e(StackOp::Swap);                       // (a%p+p) p
        e(StackOp::Opcode("OP_MOD".into()));    // ((a%p+p)%p)
    });
}

/// fieldAdd: (a + b) mod p.
fn field_add(t: &mut ECTracker, a_name: &str, b_name: &str, result_name: &str) {
    t.to_top(a_name);
    t.to_top(b_name);
    t.raw_block(&[a_name, b_name], Some("_fadd_sum"), |e| {
        e(StackOp::Opcode("OP_ADD".into()));
    });
    field_mod(t, "_fadd_sum", result_name);
}

/// fieldSub: (a - b) mod p (non-negative).
fn field_sub(t: &mut ECTracker, a_name: &str, b_name: &str, result_name: &str) {
    t.to_top(a_name);
    t.to_top(b_name);
    t.raw_block(&[a_name, b_name], Some("_fsub_diff"), |e| {
        e(StackOp::Opcode("OP_SUB".into()));
    });
    field_mod(t, "_fsub_diff", result_name);
}

/// fieldMul: (a * b) mod p.
fn field_mul(t: &mut ECTracker, a_name: &str, b_name: &str, result_name: &str) {
    t.to_top(a_name);
    t.to_top(b_name);
    t.raw_block(&[a_name, b_name], Some("_fmul_prod"), |e| {
        e(StackOp::Opcode("OP_MUL".into()));
    });
    field_mod(t, "_fmul_prod", result_name);
}

/// fieldMulConst: (a * c) mod p where c is a small constant.
fn field_mul_const(t: &mut ECTracker, a_name: &str, c: i128, result_name: &str) {
    t.to_top(a_name);
    t.raw_block(&[a_name], Some("_fmc_prod"), |e| {
        if c == 2 {
            // Use OP_2MUL (single opcode, no push needed)
            e(StackOp::Opcode("OP_2MUL".into()));
        } else {
            e(StackOp::Push(PushValue::Int(BigInt::from(c))));
            e(StackOp::Opcode("OP_MUL".into()));
        }
    });
    field_mod(t, "_fmc_prod", result_name);
}

/// fieldSqr: (a * a) mod p.
fn field_sqr(t: &mut ECTracker, a_name: &str, result_name: &str) {
    t.copy_to_top(a_name, "_fsqr_copy");
    field_mul(t, a_name, "_fsqr_copy", result_name);
}

/// fieldInv: a^(p-2) mod p via square-and-multiply.
/// Consumes a_name from the tracker.
fn field_inv(t: &mut ECTracker, a_name: &str, result_name: &str) {
    // p-2 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2D
    // Bits 255..32: 224 bits, all 1 except bit 32 which is 0
    // Bits 31..0: 0xFFFFFC2D

    // Start: result = a (bit 255 = 1)
    t.copy_to_top(a_name, "_inv_r");
    // Bits 254 down to 33: all 1's (222 bits). Bit 32 is 0 (handled below).
    for _i in 0..222 {
        field_sqr(t, "_inv_r", "_inv_r2");
        t.rename("_inv_r");
        t.copy_to_top(a_name, "_inv_a");
        field_mul(t, "_inv_r", "_inv_a", "_inv_m");
        t.rename("_inv_r");
    }
    // Bit 32 is 0: square only (no multiply)
    field_sqr(t, "_inv_r", "_inv_r2");
    t.rename("_inv_r");
    // Bits 31 down to 0 of p-2
    let low_bits = FIELD_P_MINUS_2_LOW32;
    for i in (0..=31).rev() {
        field_sqr(t, "_inv_r", "_inv_r2");
        t.rename("_inv_r");
        if (low_bits >> i) & 1 != 0 {
            t.copy_to_top(a_name, "_inv_a");
            field_mul(t, "_inv_r", "_inv_a", "_inv_m");
            t.rename("_inv_r");
        }
    }
    // Clean up original input and rename result
    t.to_top(a_name);
    t.drop();
    t.to_top("_inv_r");
    t.rename(result_name);
}

// ===========================================================================
// Point decompose / compose
// ===========================================================================

/// Decompose 64-byte Point -> (x_num, y_num) on stack.
/// Consumes pointName, produces xName and yName.
fn decompose_point(t: &mut ECTracker, point_name: &str, x_name: &str, y_name: &str) {
    t.to_top(point_name);
    // OP_SPLIT at 32 produces x_bytes (bottom) and y_bytes (top)
    t.raw_block(&[point_name], None, |e| {
        e(StackOp::Push(PushValue::Int(BigInt::from(32))));
        e(StackOp::Opcode("OP_SPLIT".into()));
    });
    // Manually track the two new items
    t.nm.push("_dp_xb".to_string());
    t.nm.push("_dp_yb".to_string());

    // Convert y_bytes (on top) to num
    // Reverse from BE to LE, append 0x00 sign byte to ensure unsigned, then BIN2NUM
    t.raw_block(&["_dp_yb"], Some(y_name), |e| {
        emit_reverse_32(e);
        e(StackOp::Push(PushValue::Bytes(vec![0x00])));
        e(StackOp::Opcode("OP_CAT".into()));
        e(StackOp::Opcode("OP_BIN2NUM".into()));
    });

    // Convert x_bytes to num
    t.to_top("_dp_xb");
    t.raw_block(&["_dp_xb"], Some(x_name), |e| {
        emit_reverse_32(e);
        e(StackOp::Push(PushValue::Bytes(vec![0x00])));
        e(StackOp::Opcode("OP_CAT".into()));
        e(StackOp::Opcode("OP_BIN2NUM".into()));
    });

    // Stack: [yName, xName] — swap to standard order [xName, yName]
    t.swap();
}

/// Compose (x_num, y_num) -> 64-byte Point.
/// Consumes xName and yName, produces resultName.
fn compose_point(t: &mut ECTracker, x_name: &str, y_name: &str, result_name: &str) {
    // Convert x to 32-byte big-endian
    // Use NUM2BIN(33) to accommodate the sign byte, then drop the last byte
    t.to_top(x_name);
    t.raw_block(&[x_name], Some("_cp_xb"), |e| {
        e(StackOp::Push(PushValue::Int(BigInt::from(33))));
        e(StackOp::Opcode("OP_NUM2BIN".into()));
        // Drop the sign byte (last byte) — split at 32, keep left
        e(StackOp::Push(PushValue::Int(BigInt::from(32))));
        e(StackOp::Opcode("OP_SPLIT".into()));
        e(StackOp::Drop);
        emit_reverse_32(e);
    });

    // Convert y to 32-byte big-endian
    t.to_top(y_name);
    t.raw_block(&[y_name], Some("_cp_yb"), |e| {
        e(StackOp::Push(PushValue::Int(BigInt::from(33))));
        e(StackOp::Opcode("OP_NUM2BIN".into()));
        e(StackOp::Push(PushValue::Int(BigInt::from(32))));
        e(StackOp::Opcode("OP_SPLIT".into()));
        e(StackOp::Drop);
        emit_reverse_32(e);
    });

    // Cat: x_be || y_be (x is below y after the two to_top calls)
    t.to_top("_cp_xb");
    t.to_top("_cp_yb");
    t.raw_block(&["_cp_xb", "_cp_yb"], Some(result_name), |e| {
        e(StackOp::Opcode("OP_CAT".into()));
    });
}

/// Emit inline byte reversal for a 32-byte value on TOS.
/// After: reversed 32-byte value on TOS.
pub fn emit_reverse_32(e: &mut dyn FnMut(StackOp)) {
    // Push empty accumulator, swap with data
    e(StackOp::Opcode("OP_0".into()));
    e(StackOp::Swap);
    // 32 iterations: peel first byte, prepend to accumulator
    for _i in 0..32 {
        // Stack: [accum, remaining]
        e(StackOp::Push(PushValue::Int(BigInt::from(1))));
        e(StackOp::Opcode("OP_SPLIT".into()));
        // Stack: [accum, byte0, rest]
        e(StackOp::Rot);
        // Stack: [byte0, rest, accum]
        e(StackOp::Rot);
        // Stack: [rest, accum, byte0]
        e(StackOp::Swap);
        // Stack: [rest, byte0, accum]
        e(StackOp::Opcode("OP_CAT".into()));
        // Stack: [rest, byte0||accum]
        e(StackOp::Swap);
        // Stack: [byte0||accum, rest]
    }
    // Stack: [reversed, empty]
    e(StackOp::Drop);
}

// ===========================================================================
// Affine point addition (for ecAdd)
// ===========================================================================

/// Affine point addition: expects px, py, qx, qy on tracker.
/// Produces rx, ry. Consumes all four inputs.
fn affine_add(t: &mut ECTracker) {
    // The chord slope s = (qy - py) / (qx - px) is undefined when P == Q: the
    // denominator is zero and the correct slope is the TANGENT, 3px^2 / (2py).
    // Without this, ecAdd(P, P) silently produced a wrong point, so every
    // contract that doubled deployed an unspendable script.
    //
    // Both cases are `s = num / den`, so only the NUMERATOR and DENOMINATOR
    // are selected and the single expensive field_inv still runs exactly once.
    // rx and ry below are already correct for doubling.
    //
    //   cond = (px == qx)
    //   num  = cond ? 3*px^2 : (qy - py)
    //   den  = cond ? 2*py   : (qx - px)
    //
    // selected as `b + cond*(a - b)`, which needs no branch and keeps the
    // emitted op sequence identical on both paths.
    //
    // NOT handled: P == -Q, whose true result is the point at infinity, which
    // affine coordinates cannot represent.
    t.copy_to_top("px", "_px_eq");
    t.copy_to_top("qx", "_qx_eq");
    t.raw_block(&["_px_eq", "_qx_eq"], Some("_cond"), |e| {
        e(StackOp::Opcode("OP_NUMEQUAL".into()));
    });

    // chord numerator / denominator
    t.copy_to_top("qy", "_qy1");
    t.copy_to_top("py", "_py1");
    field_sub(t, "_qy1", "_py1", "_num_chord");
    t.copy_to_top("qx", "_qx1");
    t.copy_to_top("px", "_px1");
    field_sub(t, "_qx1", "_px1", "_den_chord");

    // tangent numerator / denominator: 3*px^2 and 2*py
    t.copy_to_top("px", "_px_t");
    field_sqr(t, "_px_t", "_px_sq");
    field_mul_const(t, "_px_sq", 3, "_num_tan");
    t.copy_to_top("py", "_py_t");
    field_mul_const(t, "_py_t", 2, "_den_tan");

    // num = num_chord + cond*(num_tan - num_chord)
    t.copy_to_top("_num_chord", "_num_chord_c");
    field_sub(t, "_num_tan", "_num_chord_c", "_num_diff");
    t.copy_to_top("_cond", "_cond_n");
    field_mul(t, "_num_diff", "_cond_n", "_num_sel");
    field_add(t, "_num_chord", "_num_sel", "_s_num");

    // den = den_chord + cond*(den_tan - den_chord)
    t.copy_to_top("_den_chord", "_den_chord_c");
    field_sub(t, "_den_tan", "_den_chord_c", "_den_diff");
    t.to_top("_cond");
    t.rename("_cond_d");
    field_mul(t, "_den_diff", "_cond_d", "_den_sel");
    field_add(t, "_den_chord", "_den_sel", "_s_den");

    // s = s_num / s_den mod p
    field_inv(t, "_s_den", "_s_den_inv");
    field_mul(t, "_s_num", "_s_den_inv", "_s");

    // rx = s^2 - px - qx mod p
    t.copy_to_top("_s", "_s_keep");
    field_sqr(t, "_s", "_s2");
    t.copy_to_top("px", "_px2");
    field_sub(t, "_s2", "_px2", "_rx1");
    t.copy_to_top("qx", "_qx2");
    field_sub(t, "_rx1", "_qx2", "rx");

    // ry = s * (px - rx) - py mod p
    t.copy_to_top("px", "_px3");
    t.copy_to_top("rx", "_rx2");
    field_sub(t, "_px3", "_rx2", "_px_rx");
    field_mul(t, "_s_keep", "_px_rx", "_s_px_rx");
    t.copy_to_top("py", "_py2");
    field_sub(t, "_s_px_rx", "_py2", "ry");

    // Clean up original points
    t.to_top("px"); t.drop();
    t.to_top("py"); t.drop();
    t.to_top("qx"); t.drop();
    t.to_top("qy"); t.drop();
}

// ===========================================================================
// Projective point operations (for ecMul) — RCB complete formulas, a = 0
// ===========================================================================

/// scalarModN: reduce TOS mod n (the curve ORDER, not the field prime),
/// result non-negative. Same shape as field_mod but with a different modulus.
///
/// This defines the scalar domain of ecMul over the whole of script-number
/// space: negative scalars and scalars >= n both reduce into [0, n-1], and
/// k = 0 / k = n give the point at infinity. Under the old ladder anything
/// outside [1, n-1] was undefined behaviour.
fn scalar_mod_n(t: &mut ECTracker, a_name: &str, result_name: &str) {
    t.to_top(a_name);
    t.push_bytes("_smod_n", CURVE_N_SCRIPT_NUM.to_vec());
    t.raw_block(&[a_name, "_smod_n"], Some(result_name), |e| {
        e(StackOp::Opcode("OP_2DUP".into()));
        e(StackOp::Opcode("OP_MOD".into()));
        e(StackOp::Rot);
        e(StackOp::Drop);
        e(StackOp::Over);
        e(StackOp::Opcode("OP_ADD".into()));
        e(StackOp::Swap);
        e(StackOp::Opcode("OP_MOD".into()));
    });
}

/// Projective point doubling — RCB Algorithm 9 (a = 0), 6M + 2S + 1 m_3b.
/// Expects jx, jy, jz on the tracker; replaces them with the doubled point.
///
/// Complete: doubling the point at infinity (0 : 1 : 0) yields (0 : 1 : 0).
///
/// Deviations from the paper, both exact mod p and strictly cheaper here
/// (a multiply by a small constant costs one push + OP_MUL, an addition costs
/// a full reduce): line 2-4's `Z3 = 8*t0` is one mul_const rather than three
/// doublings, and line 11-12's `t2 = 3*t2` is one mul_const rather than two adds.
fn projective_double(t: &mut ECTracker) {
    // Copies of the inputs that outlive their first consumer.
    t.copy_to_top("jy", "_d_yz");     // t1 = Y*Z
    t.copy_to_top("jy", "_d_xy");     // t1 = X*Y  (line 16)
    t.copy_to_top("jz", "_d_zz_src"); // t2 = Z*Z

    field_sqr(t, "jy", "_d_t0"); // t0 = Y^2
    t.copy_to_top("_d_t0", "_d_t0a");
    field_mul_const(t, "_d_t0a", 8, "_d_Z3"); // Z3 = 8*t0
    field_mul(t, "_d_yz", "jz", "_d_t1");     // t1 = Y*Z
    field_sqr(t, "_d_zz_src", "_d_zz");       // Z^2
    field_mul_const(t, "_d_zz", 21, "_d_t2"); // t2 = b3*Z^2  (b3 = 3*7)

    t.copy_to_top("_d_t2", "_d_t2a");
    t.copy_to_top("_d_Z3", "_d_Z3a");
    field_mul(t, "_d_t2a", "_d_Z3a", "_d_X3"); // X3 = t2*Z3

    t.copy_to_top("_d_t0", "_d_t0b");
    t.copy_to_top("_d_t2", "_d_t2b");
    field_add(t, "_d_t0b", "_d_t2b", "_d_Y3"); // Y3 = t0+t2

    field_mul(t, "_d_t1", "_d_Z3", "_d_Z3n");  // Z3 = t1*Z3
    field_mul_const(t, "_d_t2", 3, "_d_t2c");  // t2 = 3*t2
    field_sub(t, "_d_t0", "_d_t2c", "_d_t0n"); // t0 = t0-t2

    t.copy_to_top("_d_t0n", "_d_t0na");
    field_mul(t, "_d_t0na", "_d_Y3", "_d_Y3b"); // Y3 = t0*Y3
    field_add(t, "_d_X3", "_d_Y3b", "_d_Y3c");  // Y3 = X3+Y3

    field_mul(t, "jx", "_d_xy", "_d_xyv");      // t1 = X*Y
    field_mul(t, "_d_t0n", "_d_xyv", "_d_X3b"); // X3 = t0*t1
    field_mul_const(t, "_d_X3b", 2, "_d_X3c");  // X3 = X3+X3

    t.to_top("_d_X3c"); t.rename("jx");
    t.to_top("_d_Y3c"); t.rename("jy");
    t.to_top("_d_Z3n"); t.rename("jz");
}

/// Projective -> affine conversion. Consumes jx, jy, jz; produces rx_name, ry_name.
///
/// field_inv is Fermat exponentiation, so inv(0) = 0: the point at infinity
/// (Z = 0) converts to (0, 0), which is the all-zero Point blob. That is the
/// agreed encoding for infinity — it is not a curve point, so it cannot be
/// confused with a real result.
fn projective_to_affine(t: &mut ECTracker, rx_name: &str, ry_name: &str) {
    field_inv(t, "jz", "_zinv");
    t.copy_to_top("_zinv", "_zinv_b");
    field_mul(t, "jx", "_zinv", rx_name);
    field_mul(t, "jy", "_zinv_b", ry_name);
}

// ===========================================================================
// Projective mixed addition (P_projective + Q_affine)
// ===========================================================================

/// Build complete mixed-add ops for use inside OP_IF — RCB Algorithm 8 (a = 0),
/// 11M + 2 m_3b. Adds the affine base point (ax, ay) into the accumulator.
///
/// Complete: no exceptional cases. In particular
///   - accumulator == Q        -> correctly doubles (this is the case that broke
///     ecMul(P, 2n): the old Jacobian mixed-add computed H = R = 0 and returned
///     the zero point, which then absorbed every remaining iteration)
///   - accumulator == -Q       -> correctly yields the point at infinity
///   - accumulator == infinity -> correctly yields Q
///
/// Uses an inner ECTracker cloned from the outer one, because the ops run under
/// OP_IF: the outer tracker's model must describe the stack for BOTH branches,
/// so this block has to be stack-shape neutral — same names, same depths, with
/// jx/jy/jz replaced in place.
///
/// Stack layout: [..., ax, ay, _k, jx, jy, jz]
/// After:        [..., ax, ay, _k, jx', jy', jz']
fn build_projective_add_mixed_inline(e: &mut dyn FnMut(StackOp), t: &ECTracker) {
    let names: Vec<String> = t.nm.clone();
    let name_refs: Vec<&str> = names.iter().map(|s| s.as_str()).collect();
    let it = &mut ECTracker::new(&name_refs, e);

    // The affine base survives every iteration, so only ever consume copies.
    it.copy_to_top("ax", "_m_x2a"); // t0 = X1*X2
    it.copy_to_top("ax", "_m_x2b"); // X2+Y2
    it.copy_to_top("ax", "_m_x2c"); // X2*Z1
    it.copy_to_top("ay", "_m_y2a"); // t1 = Y1*Y2
    it.copy_to_top("ay", "_m_y2b"); // X2+Y2
    it.copy_to_top("ay", "_m_y2c"); // Y2*Z1
    it.copy_to_top("jx", "_m_x1a"); // X1+Y1
    it.copy_to_top("jx", "_m_x1b"); // Y3+X1
    it.copy_to_top("jy", "_m_y1a"); // X1+Y1
    it.copy_to_top("jy", "_m_y1b"); // t4+Y1
    it.copy_to_top("jz", "_m_z1a"); // X2*Z1
    it.copy_to_top("jz", "_m_z1b"); // b3*Z1

    field_mul(it, "jx", "_m_x2a", "_m_t0");     // t0 = X1*X2
    field_mul(it, "jy", "_m_y2a", "_m_t1");     // t1 = Y1*Y2
    field_add(it, "_m_x2b", "_m_y2b", "_m_s1"); // X2+Y2
    field_add(it, "_m_x1a", "_m_y1a", "_m_s2"); // X1+Y1
    field_mul(it, "_m_s1", "_m_s2", "_m_t3");   // t3 = (X2+Y2)(X1+Y1)

    it.copy_to_top("_m_t0", "_m_t0a");
    it.copy_to_top("_m_t1", "_m_t1a");
    field_add(it, "_m_t0a", "_m_t1a", "_m_s3"); // t4 = t0+t1
    field_sub(it, "_m_t3", "_m_s3", "_m_t3b");  // t3 = t3-t4

    field_mul(it, "_m_y2c", "jz", "_m_t4");     // t4 = Y2*Z1
    field_add(it, "_m_t4", "_m_y1b", "_m_t4b"); // t4 = t4+Y1
    field_mul(it, "_m_x2c", "_m_z1a", "_m_Y3"); // Y3 = X2*Z1
    field_add(it, "_m_Y3", "_m_x1b", "_m_Y3b"); // Y3 = Y3+X1

    field_mul_const(it, "_m_t0", 3, "_m_t0b");   // t0 = 3*t0
    field_mul_const(it, "_m_z1b", 21, "_m_t2");  // t2 = b3*Z1

    it.copy_to_top("_m_t1", "_m_t1b");
    it.copy_to_top("_m_t2", "_m_t2a");
    field_add(it, "_m_t1b", "_m_t2a", "_m_Z3");   // Z3 = t1+t2
    field_sub(it, "_m_t1", "_m_t2", "_m_t1c");    // t1 = t1-t2
    field_mul_const(it, "_m_Y3b", 21, "_m_Y3c");  // Y3 = b3*Y3

    it.copy_to_top("_m_Y3c", "_m_Y3ca");
    it.copy_to_top("_m_t4b", "_m_t4ba");
    field_mul(it, "_m_t4ba", "_m_Y3ca", "_m_X3"); // X3 = t4*Y3

    it.copy_to_top("_m_t3b", "_m_t3ba");
    it.copy_to_top("_m_t1c", "_m_t1ca");
    field_mul(it, "_m_t3ba", "_m_t1ca", "_m_t2b"); // t2 = t3*t1
    field_sub(it, "_m_t2b", "_m_X3", "_m_X3b");    // X3 = t2-X3

    it.copy_to_top("_m_t0b", "_m_t0ba");
    field_mul(it, "_m_Y3c", "_m_t0ba", "_m_Y3d"); // Y3 = Y3*t0

    it.copy_to_top("_m_Z3", "_m_Z3a");
    field_mul(it, "_m_t1c", "_m_Z3a", "_m_t1d");  // t1 = t1*Z3
    field_add(it, "_m_t1d", "_m_Y3d", "_m_Y3e");  // Y3 = t1+Y3

    field_mul(it, "_m_t0b", "_m_t3b", "_m_t0c"); // t0 = t0*t3
    field_mul(it, "_m_Z3", "_m_t4b", "_m_Z3b");  // Z3 = Z3*t4
    field_add(it, "_m_Z3b", "_m_t0c", "_m_Z3c"); // Z3 = Z3+t0

    it.to_top("_m_X3b"); it.rename("jx");
    it.to_top("_m_Y3e"); it.rename("jy");
    it.to_top("_m_Z3c"); it.rename("jz");
}

// ===========================================================================
// Public entry points (called from stack lowerer)
// ===========================================================================

/// ecAdd: add two points.
/// Stack in: [point_a, point_b] (b on top)
/// Stack out: [result_point]
pub fn emit_ec_add(emit: &mut dyn FnMut(StackOp)) {
    let mut t = ECTracker::new(&["_pa", "_pb"], emit);
    decompose_point(&mut t, "_pa", "px", "py");
    decompose_point(&mut t, "_pb", "qx", "qy");
    affine_add(&mut t);
    compose_point(&mut t, "rx", "ry", "_result");
}

/// ecMul: scalar multiplication P * k.
/// Stack in: [point, scalar] (scalar on top)
/// Stack out: [result_point]
///
/// Uses 256-iteration double-and-add with Jacobian coordinates.
pub fn emit_ec_mul(emit: &mut dyn FnMut(StackOp)) {
    let mut t = ECTracker::new(&["_pt", "_k"], emit);
    // Decompose to affine base point
    decompose_point(&mut t, "_pt", "ax", "ay");

    // Reduce the scalar into [0, n-1] so the 256-bit ladder covers the whole
    // domain: negative k and k >= n are now defined rather than undefined.
    scalar_mod_n(&mut t, "_k", "_k");

    // Accumulator := point at infinity (0 : 1 : 0). Legal input to both complete
    // formulas, which is exactly why no special leading-bit handling is needed.
    t.push_int("jx", 0);
    t.push_int("jy", 1);
    t.push_int("jz", 0);

    // 256 iterations: bits 255 down to 0
    for bit in (0..=255).rev() {
        // Double accumulator
        projective_double(&mut t);

        // Extract bit: (k >> bit) & 1, using OP_RSHIFTNUM / OP_2DIV
        t.copy_to_top("_k", "_k_copy");
        if bit == 1 {
            // Single-bit shift: OP_2DIV (no push needed)
            t.raw_block(&["_k_copy"], Some("_shifted"), |e| {
                e(StackOp::Opcode("OP_2DIV".into()));
            });
        } else if bit > 1 {
            // Multi-bit shift: push shift amount, OP_RSHIFTNUM
            t.push_int("_shift", bit as i128);
            t.raw_block(&["_k_copy", "_shift"], Some("_shifted"), |e| {
                e(StackOp::Opcode("OP_RSHIFTNUM".into()));
            });
        } else {
            t.rename("_shifted");
        }
        t.push_int("_two", 2);
        t.raw_block(&["_shifted", "_two"], Some("_bit"), |e| {
            e(StackOp::Opcode("OP_MOD".into()));
        });

        // Move _bit to TOS and remove from tracker BEFORE generating add ops,
        // because OP_IF consumes _bit and the add ops run with _bit already gone.
        t.to_top("_bit");
        t.nm.pop(); // _bit consumed by IF
        let add_ops = collect_ops(|add_emit| {
            build_projective_add_mixed_inline(add_emit, &t);
        });
        (t.e)(StackOp::If {
            then_ops: add_ops,
            else_ops: vec![],
        });
    }

    // Convert projective to affine
    projective_to_affine(&mut t, "_rx", "_ry");

    // Clean up base point and scalar
    t.to_top("ax"); t.drop();
    t.to_top("ay"); t.drop();
    t.to_top("_k"); t.drop();

    // Compose result
    compose_point(&mut t, "_rx", "_ry", "_result");
}

/// ecMulGen: scalar multiplication G * k.
/// Stack in: [scalar]
/// Stack out: [result_point]
pub fn emit_ec_mul_gen(emit: &mut dyn FnMut(StackOp)) {
    // Push generator point as 64-byte blob, then delegate to ecMul
    let mut g_point = Vec::with_capacity(64);
    g_point.extend_from_slice(&GEN_X_BYTES);
    g_point.extend_from_slice(&GEN_Y_BYTES);
    emit(StackOp::Push(PushValue::Bytes(g_point)));
    emit(StackOp::Swap); // [point, scalar]
    emit_ec_mul(emit);
}

/// ecNegate: negate a point (x, p - y).
/// Stack in: [point]
/// Stack out: [negated_point]
pub fn emit_ec_negate(emit: &mut dyn FnMut(StackOp)) {
    let mut t = ECTracker::new(&["_pt"], emit);
    decompose_point(&mut t, "_pt", "_nx", "_ny");
    push_field_p(&mut t, "_fp");
    field_sub(&mut t, "_fp", "_ny", "_neg_y");
    compose_point(&mut t, "_nx", "_neg_y", "_result");
}

/// ecOnCurve: check if point is on secp256k1 (y^2 = x^3 + 7 mod p).
/// Stack in: [point]
/// Stack out: [boolean]
pub fn emit_ec_on_curve(emit: &mut dyn FnMut(StackOp)) {
    let mut t = ECTracker::new(&["_pt"], emit);
    decompose_point(&mut t, "_pt", "_x", "_y");

    // GAP-301: coordinate canonicity. `decompose_point` BIN2NUMs each coordinate
    // as an unsigned value that may be >= p; the field arithmetic below would
    // silently reduce it mod p, so a non-canonical encoding of a valid point
    // would pass. Reject it: require x < p AND y < p (coordinates are unsigned,
    // so the 0 <= lower bound holds by construction). Combined with the curve
    // equation at the end via OP_BOOLAND so ecOnCurve still returns a boolean.
    t.copy_to_top("_x", "_x_lt");
    push_field_p(&mut t, "_p_for_x");
    t.raw_block(&["_x_lt", "_p_for_x"], Some("_x_canon"), |e| {
        e(StackOp::Opcode("OP_LESSTHAN".into()));
    });
    t.copy_to_top("_y", "_y_lt");
    push_field_p(&mut t, "_p_for_y");
    t.raw_block(&["_y_lt", "_p_for_y"], Some("_y_canon"), |e| {
        e(StackOp::Opcode("OP_LESSTHAN".into()));
    });
    t.to_top("_x_canon");
    t.to_top("_y_canon");
    t.raw_block(&["_x_canon", "_y_canon"], Some("_canon"), |e| {
        e(StackOp::Opcode("OP_BOOLAND".into()));
    });

    // lhs = y^2
    field_sqr(&mut t, "_y", "_y2");

    // rhs = x^3 + 7
    t.copy_to_top("_x", "_x_copy");
    field_sqr(&mut t, "_x", "_x2");
    field_mul(&mut t, "_x2", "_x_copy", "_x3");
    t.push_int("_seven", 7);
    field_add(&mut t, "_x3", "_seven", "_rhs");

    // Compare curve equation
    t.to_top("_y2");
    t.to_top("_rhs");
    t.raw_block(&["_y2", "_rhs"], Some("_curve_eq"), |e| {
        e(StackOp::Opcode("OP_EQUAL".into()));
    });

    // on-curve = canonical AND curve-equation
    t.to_top("_canon");
    t.to_top("_curve_eq");
    t.raw_block(&["_canon", "_curve_eq"], Some("_result"), |e| {
        e(StackOp::Opcode("OP_BOOLAND".into()));
    });
}

/// ecModReduce: ((value % mod) + mod) % mod
/// Stack in: [value, mod]
/// Stack out: [result]
pub fn emit_ec_mod_reduce(emit: &mut dyn FnMut(StackOp)) {
    emit(StackOp::Opcode("OP_2DUP".into()));
    emit(StackOp::Opcode("OP_MOD".into()));
    emit(StackOp::Rot);
    emit(StackOp::Drop);
    emit(StackOp::Over);
    emit(StackOp::Opcode("OP_ADD".into()));
    emit(StackOp::Swap);
    emit(StackOp::Opcode("OP_MOD".into()));
}

/// ecEncodeCompressed: point -> 33-byte compressed pubkey.
/// Stack in: [point (64 bytes)]
/// Stack out: [compressed (33 bytes)]
pub fn emit_ec_encode_compressed(emit: &mut dyn FnMut(StackOp)) {
    // Split at 32: [x_bytes, y_bytes]
    emit(StackOp::Push(PushValue::Int(BigInt::from(32))));
    emit(StackOp::Opcode("OP_SPLIT".into()));
    // Get last byte of y for parity
    emit(StackOp::Opcode("OP_SIZE".into()));
    emit(StackOp::Push(PushValue::Int(BigInt::from(1))));
    emit(StackOp::Opcode("OP_SUB".into()));
    emit(StackOp::Opcode("OP_SPLIT".into()));
    // Stack: [x_bytes, y_prefix, last_byte]
    emit(StackOp::Opcode("OP_BIN2NUM".into()));
    emit(StackOp::Push(PushValue::Int(BigInt::from(2))));
    emit(StackOp::Opcode("OP_MOD".into()));
    // Stack: [x_bytes, y_prefix, parity]
    emit(StackOp::Swap);
    emit(StackOp::Drop); // drop y_prefix
    // Stack: [x_bytes, parity]
    emit(StackOp::If {
        then_ops: vec![StackOp::Push(PushValue::Bytes(vec![0x03]))],
        else_ops: vec![StackOp::Push(PushValue::Bytes(vec![0x02]))],
    });
    // Stack: [x_bytes, prefix_byte]
    emit(StackOp::Swap);
    emit(StackOp::Opcode("OP_CAT".into()));
}

/// ecMakePoint: (x: bigint, y: bigint) -> Point.
/// Stack in: [x_num, y_num] (y on top)
/// Stack out: [point_bytes (64 bytes)]
pub fn emit_ec_make_point(emit: &mut dyn FnMut(StackOp)) {
    // Convert y to 32 bytes big-endian (NUM2BIN(33) to handle sign byte, then take first 32)
    emit(StackOp::Push(PushValue::Int(BigInt::from(33))));
    emit(StackOp::Opcode("OP_NUM2BIN".into()));
    emit(StackOp::Push(PushValue::Int(BigInt::from(32))));
    emit(StackOp::Opcode("OP_SPLIT".into()));
    emit(StackOp::Drop);
    emit_reverse_32(emit);
    // Stack: [x_num, y_be]
    emit(StackOp::Swap);
    // Stack: [y_be, x_num]
    emit(StackOp::Push(PushValue::Int(BigInt::from(33))));
    emit(StackOp::Opcode("OP_NUM2BIN".into()));
    emit(StackOp::Push(PushValue::Int(BigInt::from(32))));
    emit(StackOp::Opcode("OP_SPLIT".into()));
    emit(StackOp::Drop);
    emit_reverse_32(emit);
    // Stack: [y_be, x_be]
    emit(StackOp::Swap);
    // Stack: [x_be, y_be]
    emit(StackOp::Opcode("OP_CAT".into()));
}

/// ecPointX: extract x-coordinate from Point.
/// Stack in: [point (64 bytes)]
/// Stack out: [x as bigint]
pub fn emit_ec_point_x(emit: &mut dyn FnMut(StackOp)) {
    emit(StackOp::Push(PushValue::Int(BigInt::from(32))));
    emit(StackOp::Opcode("OP_SPLIT".into()));
    emit(StackOp::Drop);
    emit_reverse_32(emit);
    // Append 0x00 sign byte to ensure unsigned interpretation
    emit(StackOp::Push(PushValue::Bytes(vec![0x00])));
    emit(StackOp::Opcode("OP_CAT".into()));
    emit(StackOp::Opcode("OP_BIN2NUM".into()));
}

/// ecPointY: extract y-coordinate from Point.
/// Stack in: [point (64 bytes)]
/// Stack out: [y as bigint]
pub fn emit_ec_point_y(emit: &mut dyn FnMut(StackOp)) {
    emit(StackOp::Push(PushValue::Int(BigInt::from(32))));
    emit(StackOp::Opcode("OP_SPLIT".into()));
    emit(StackOp::Swap);
    emit(StackOp::Drop);
    emit_reverse_32(emit);
    // Append 0x00 sign byte to ensure unsigned interpretation
    emit(StackOp::Push(PushValue::Bytes(vec![0x00])));
    emit(StackOp::Opcode("OP_CAT".into()));
    emit(StackOp::Opcode("OP_BIN2NUM".into()));
}

