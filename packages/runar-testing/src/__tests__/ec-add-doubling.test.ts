import { describe, it, expect } from 'vitest';
import { emitEcAdd, emitEcMulGen, emitMethod } from 'runar-compiler';
import type { StackOp } from 'runar-ir-schema';
import { ScriptVM } from '../index.js';

/**
 * `ecAdd` must be able to DOUBLE a point.
 *
 * The affine chord formula `s = (qy - py) / (qx - px)` divides by zero when
 * P == Q, so a codegen carrying only that case computes a wrong result for
 * `ecAdd(P, P)`. Every contract that doubles then compiles cleanly, agrees
 * byte-for-byte across all seven tiers, and deploys an UNSPENDABLE script.
 *
 * Found by spending the `ec-unit` fixture (which calls `ecAdd(g, g)`) on a live
 * regtest node: rejected with "Script failed an OP_VERIFY operation".
 */

const GX  = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798n;
const GY  = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8n;
const G2X = 0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5n;
const G2Y = 0x1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52an;
const G3X = 0xf9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9n;
const G3Y = 0x388f7b0f632de8140fe337e62a37f3566500a99934c2231b6cb9fd7584b8e672n;
const G4X = 0xe493dbf1c10d80f3581e4904930b1404cc6c13900ee0758474fa94abe8c4cd13n;
const G4Y = 0x51ed993ea0d455b75642e2098ea51448d967ae33bfbdfe40cfe97bdc47739922n;

/** 64-byte point blob: x[32] || y[32], big-endian, as `Point` is defined. */
function point(x: bigint, y: bigint): Uint8Array {
  const hex = x.toString(16).padStart(64, '0') + y.toString(16).padStart(64, '0');
  return Uint8Array.from(Buffer.from(hex, 'hex'));
}

function run(ops: StackOp[]): { success: boolean; stack: Uint8Array[] } {
  const { scriptHex } = emitMethod({ name: 't', ops } as never) as { scriptHex: string };
  return new ScriptVM().executeHex(scriptHex) as never;
}

/** Top of stack after `ecAdd(a, b)`, hex-encoded. */
function ecAdd(a: Uint8Array, b: Uint8Array): string {
  const ops: StackOp[] = [
    { op: 'push', value: a } as StackOp,
    { op: 'push', value: b } as StackOp,
  ];
  emitEcAdd((o) => ops.push(o));
  const r = run(ops);
  return r.stack.length ? Buffer.from(r.stack[r.stack.length - 1]!).toString('hex') : '(empty)';
}

function hex(x: bigint, y: bigint): string {
  return Buffer.from(point(x, y)).toString('hex');
}

describe('emitEcAdd', () => {
  it('control: ecMulGen(3) yields 3G, pinning the blob format and constants', () => {
    const ops: StackOp[] = [{ op: 'push', value: 3n } as StackOp];
    emitEcMulGen((o) => ops.push(o));
    const r = run(ops);
    const got = Buffer.from(r.stack[r.stack.length - 1]!).toString('hex');
    expect(got).toBe(hex(G3X, G3Y));
  });

  it('adds two DISTINCT points: ecAdd(G, 2G) === 3G', () => {
    expect(ecAdd(point(GX, GY), point(G2X, G2Y))).toBe(hex(G3X, G3Y));
  });

  it('DOUBLES a point: ecAdd(G, G) === 2G', () => {
    expect(ecAdd(point(GX, GY), point(GX, GY))).toBe(hex(G2X, G2Y));
  });

  it('doubles a non-generator point: ecAdd(2G, 2G) === 4G', () => {
    expect(ecAdd(point(G2X, G2Y), point(G2X, G2Y))).toBe(hex(G4X, G4Y));
  });
});
