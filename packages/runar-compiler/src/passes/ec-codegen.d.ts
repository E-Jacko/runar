/**
 * EC codegen — secp256k1 elliptic curve operations for Bitcoin Script.
 *
 * Follows the slh-dsa-codegen.ts pattern: self-contained module imported by
 * 05-stack-lower.ts. Uses an ECTracker (similar to SLHTracker) for named
 * stack state tracking.
 *
 * Point representation: 64 bytes (x[32] || y[32], big-endian unsigned).
 * Internal arithmetic uses Jacobian coordinates for scalar multiplication.
 */
import type { StackOp } from '../ir/index.js';
export declare class ECTracker {
    nm: (string | null)[];
    _e: (op: StackOp) => void;
    constructor(init: (string | null)[], emit: (op: StackOp) => void);
    get depth(): number;
    findDepth(name: string): number;
    pushBytes(n: string, v: Uint8Array): void;
    pushInt(n: string, v: bigint): void;
    dup(n: string): void;
    drop(): void;
    nip(): void;
    over(n: string): void;
    swap(): void;
    rot(): void;
    op(code: string): void;
    roll(d: number): void;
    pick(d: number, n: string): void;
    toTop(name: string): void;
    copyToTop(name: string, n?: string): void;
    toAlt(): void;
    fromAlt(n: string): void;
    rename(n: string): void;
    /** Emit raw opcodes tracking only net stack effect. */
    rawBlock(consume: string[], produce: string | null, fn: (e: (op: StackOp) => void) => void): void;
    /** Emit if/else with tracked stack effect. */
    emitIf(condName: string, thenFn: (e: (op: StackOp) => void) => void, elseFn: (e: (op: StackOp) => void) => void, resultName: string | null): void;
}
/**
 * ecAdd: add two points.
 * Stack in: [point_a, point_b] (b on top)
 * Stack out: [result_point]
 */
export declare function emitEcAdd(emit: (op: StackOp) => void): void;
/**
 * ecMul: scalar multiplication P * k.
 * Stack in: [point, scalar] (scalar on top)
 * Stack out: [result_point]
 *
 * Uses 257-iteration MSB-first double-and-add with Jacobian coordinates.
 * Adds 3n to k so that bit 257 is always set: k+3n ∈ [3n, 4n-1], and
 * since 3n > 2^257, bit 257 is guaranteed to be 1 for all valid k.
 * This avoids the k+n overflow issue where bit 256 was only set for
 * large k, causing incorrect results for ~half of all scalar values.
 */
export declare function emitEcMul(emit: (op: StackOp) => void): void;
/**
 * ecMulGen: scalar multiplication G * k.
 * Stack in: [scalar]
 * Stack out: [result_point]
 */
export declare function emitEcMulGen(emit: (op: StackOp) => void): void;
/**
 * ecNegate: negate a point (x, p - y).
 * Stack in: [point]
 * Stack out: [negated_point]
 */
export declare function emitEcNegate(emit: (op: StackOp) => void): void;
/**
 * ecOnCurve: check if point is on secp256k1 (y² ≡ x³ + 7 mod p).
 * Stack in: [point]
 * Stack out: [boolean]
 */
export declare function emitEcOnCurve(emit: (op: StackOp) => void): void;
/**
 * ecModReduce: ((value % mod) + mod) % mod
 * Stack in: [value, mod]
 * Stack out: [result]
 */
export declare function emitEcModReduce(emit: (op: StackOp) => void): void;
/**
 * ecEncodeCompressed: point → 33-byte compressed pubkey.
 * Stack in: [point (64 bytes)]
 * Stack out: [compressed (33 bytes)]
 */
export declare function emitEcEncodeCompressed(emit: (op: StackOp) => void): void;
/**
 * ecMakePoint: (x: bigint, y: bigint) → Point.
 * Stack in: [x_num, y_num] (y on top)
 * Stack out: [point_bytes (64 bytes)]
 */
export declare function emitEcMakePoint(emit: (op: StackOp) => void): void;
/**
 * ecPointX: extract x-coordinate from Point.
 * Stack in: [point (64 bytes)]
 * Stack out: [x as bigint]
 */
export declare function emitEcPointX(emit: (op: StackOp) => void): void;
/**
 * ecPointY: extract y-coordinate from Point.
 * Stack in: [point (64 bytes)]
 * Stack out: [y as bigint]
 */
export declare function emitEcPointY(emit: (op: StackOp) => void): void;
//# sourceMappingURL=ec-codegen.d.ts.map