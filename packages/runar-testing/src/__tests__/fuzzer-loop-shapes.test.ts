/**
 * REACHABILITY gate for the exec-oracle generator's loop-body shapes.
 *
 * WHY THIS FILE EXISTS
 * --------------------
 * The 2026-08-06 fund-safety miscompile — a bounded loop that rebinds a
 * loop-carried local and READS IT AGAIN in the same iteration compiling to
 * `step*N` instead of `step*N*(N+1)/2`, byte-identically in all seven tiers —
 * survived three bug-hunting waves for a structural reason, not a lucky one:
 * `arbForLoop` pointed every generated body statement at the SAME accumulator,
 * so a foreign read of a reassigned local was outside the generator's
 * REACHABLE SPACE. No seed, no time budget and no number of runs could have
 * produced it.
 *
 * A probability argument is therefore not evidence here. Every assertion below
 * is made on the generated IR — the actual `ForStmt` bodies — with a FIXED
 * seed, in the style of `conformance/fuzzer/__tests__/spend-shapes.test.ts`:
 *
 *   1. `arbExecCaseWithLoopShape(shape)` pins the topology, so each shape is
 *      proved reachable directly rather than waited for.
 *   2. The composite `arbExecCase` is sampled at one fixed seed and every shape
 *      is shown to appear, with the sample index it first appears at.
 *   3. `ExecCase.loopShape` is a LABEL. Each case's shape is re-derived from
 *      its IR and must match the label, so a shape that claims a topology it
 *      does not emit fails here.
 */

import { describe, it, expect } from 'vitest';
import fc from 'fast-check';
import { compile } from 'runar-compiler';
import {
  EXEC_LOOP_SHAPES,
  arbExecCase,
  arbExecCaseWithLoopShape,
  loopShapeCarriers,
  renderTypeScript,
  type ExecCase,
  type ExecLoopShape,
} from '../fuzzer/index.js';
import type { ForStmt, Stmt, Expr } from '../fuzzer/contract-ir.js';

const SEED = 424242;
/** Cases drawn from the composite generator for the "is it reachable at all
 *  through the real arbitrary" gate. */
const COMPOSITE = fc.sample(arbExecCase, { numRuns: 120, seed: SEED });

// ---------------------------------------------------------------------------
// IR helpers — these read the generated STATEMENTS, never the shape label
// ---------------------------------------------------------------------------

function findLoop(body: Stmt[]): ForStmt | null {
  for (const s of body) if (s.kind === 'for') return s;
  return null;
}

function innerLoop(loop: ForStmt): ForStmt | null {
  for (const s of loop.body) if (s.kind === 'for') return s;
  return null;
}

/** Names of locals assigned by a statement list, in order. */
function assignTargets(body: Stmt[]): string[] {
  return body.filter((s): s is Extract<Stmt, { kind: 'assign' }> => s.kind === 'assign').map((s) => s.target);
}

/** Every `var_ref` name inside an expression. */
function refs(expr: Expr, out: string[] = []): string[] {
  switch (expr.kind) {
    case 'var_ref':
      out.push(expr.name);
      break;
    case 'binary':
      refs(expr.left, out);
      refs(expr.right, out);
      break;
    case 'unary':
      refs(expr.operand, out);
      break;
    case 'ternary':
      refs(expr.condition, out);
      refs(expr.consequent, out);
      refs(expr.alternate, out);
      break;
    case 'call':
      expr.args.forEach((a) => refs(a, out));
      break;
  }
  return out;
}

/**
 * Does statement `j` read a local that statement `i < j` REASSIGNED, where the
 * two statements target different locals? That is the confirmed-bug shape,
 * derived from the IR alone.
 */
function hasCrossRead(body: Stmt[]): boolean {
  const assignedSoFar = new Set<string>();
  for (const s of body) {
    if (s.kind !== 'assign' || s.isProperty) continue;
    // Reading `x` inside `x = x + 1` is the self-accumulation every loop does;
    // only a read of a DIFFERENT local that an earlier statement rebound counts.
    const foreign = refs(s.value).filter((n) => n !== s.target);
    if (foreign.some((n) => assignedSoFar.has(n))) return true;
    assignedSoFar.add(s.target);
  }
  return false;
}

/** Does a statement read `name` BEFORE any statement reassigns it? */
function readsBeforeReassign(body: Stmt[], name: string): boolean {
  for (const s of body) {
    if (s.kind !== 'assign') continue;
    if (s.target !== name && refs(s.value).includes(name)) return true;
    if (s.target === name) return false;
  }
  return false;
}

/** Locals declared mutable before the loop, in declaration order. */
function declaredCarriers(body: Stmt[]): string[] {
  return body
    .filter((s): s is Extract<Stmt, { kind: 'var_decl' }> => s.kind === 'var_decl' && s.mutable)
    .map((s) => s.name);
}

/** Re-derive the topology from the IR. Returns null when it matches nothing. */
function classify(c: ExecCase): ExecLoopShape | null {
  const body = c.contract.methods[0]!.body;
  const loop = findLoop(body);
  if (!loop) return null;
  const inner = innerLoop(loop);
  if (inner) {
    if (hasCrossRead(inner.body)) return 'nested-inner-cross-read';
    // The carried local is rebound only in the INNER body and read one scope
    // out, after the inner loop closes.
    const outerAssigns = loop.body.filter((s) => s.kind === 'assign');
    const innerTargets = assignTargets(inner.body);
    if (
      outerAssigns.length > 0 &&
      outerAssigns.every((s) => refs((s as Extract<Stmt, { kind: 'assign' }>).value).some((n) => innerTargets.includes(n)))
    ) {
      return 'nested-outer-read';
    }
    return null;
  }
  const targets = new Set(assignTargets(loop.body));
  if (targets.size === 1) return 'single-carrier';
  if (hasCrossRead(loop.body)) return 'k2-cross-read';
  if (readsBeforeReassign(loop.body, 'acc')) return 'k2-read-before-reassign';
  return 'k2-independent';
}

// ---------------------------------------------------------------------------

describe('exec-oracle loop shapes: reachability', () => {
  it('the composite generator reaches EVERY loop shape at a fixed seed', () => {
    const firstIndex = new Map<ExecLoopShape, number>();
    COMPOSITE.forEach((c, i) => {
      if (c.loopShape !== null && !firstIndex.has(c.loopShape)) firstIndex.set(c.loopShape, i);
    });
    const missing = EXEC_LOOP_SHAPES.filter((s) => !firstIndex.has(s));
    expect(
      missing,
      `seed ${SEED} / 120 samples reached: ${JSON.stringify(Object.fromEntries(firstIndex))}`,
    ).toEqual([]);
    // Fixed seed => fixed first-hit indices. Recorded so a change to the draw
    // order is visible in the diff rather than silently shifting the corpus.
    expect(Object.fromEntries(firstIndex)).toEqual({
      'nested-outer-read': 1,
      'k2-read-before-reassign': 3,
      'single-carrier': 6,
      'k2-cross-read': 10,
      'k2-independent': 11,
      'nested-inner-cross-read': 14,
    });
  });

  it('every generated case labels itself with the topology its IR actually has', () => {
    for (const c of COMPOSITE) {
      expect(classify(c), `${c.contract.name} mislabels its loop`).toBe(c.loopShape);
    }
  });

  it.each([...EXEC_LOOP_SHAPES])('%s is produced on demand and compiles', (shape) => {
    const cases = fc.sample(arbExecCaseWithLoopShape(shape), { numRuns: 8, seed: SEED });
    for (const c of cases) {
      expect(c.loopShape).toBe(shape);
      expect(classify(c)).toBe(shape);
      // Every carrier the shape declares is a mutable local declared BEFORE the
      // loop, so the loop genuinely carries it across iterations.
      const declared = declaredCarriers(c.contract.methods[0]!.body);
      expect(declared).toEqual(loopShapeCarriers(shape));
      const source = renderTypeScript(c.contract);
      const r = compile(source, { fileName: `${c.contract.name}.runar.ts` });
      expect(
        r.success,
        `${shape}: ${r.diagnostics.map((d) => d.message).join('; ')}\n${source}`,
      ).toBe(true);
    }
  });
});

// ---------------------------------------------------------------------------
// The individual shapes, asserted against the IR
// ---------------------------------------------------------------------------

describe('exec-oracle loop shapes: structure', () => {
  const sampleOf = (shape: ExecLoopShape): ExecCase[] =>
    fc.sample(arbExecCaseWithLoopShape(shape), { numRuns: 8, seed: SEED });

  it('k2-cross-read: >=2 carried locals, one rebound then READ by a later statement', () => {
    for (const c of sampleOf('k2-cross-read')) {
      const loop = findLoop(c.contract.methods[0]!.body)!;
      const targets = assignTargets(loop.body);
      expect(new Set(targets).size).toBeGreaterThanOrEqual(2);
      // The reported shape exactly: `acc` is rebound first, `wacc` then reads it.
      expect(targets).toEqual(['acc', 'wacc']);
      expect(refs((loop.body[1] as Extract<Stmt, { kind: 'assign' }>).value)).toContain('acc');
      expect(hasCrossRead(loop.body)).toBe(true);
    }
  });

  it('k2-read-before-reassign: the carried local is READ BEFORE it is rebound', () => {
    for (const c of sampleOf('k2-read-before-reassign')) {
      const loop = findLoop(c.contract.methods[0]!.body)!;
      expect(assignTargets(loop.body)).toEqual(['wacc', 'acc']);
      expect(readsBeforeReassign(loop.body, 'acc')).toBe(true);
      // ...and it is NOT the cross-read shape — the generator reaches both, so
      // a compiler fix written too wide turns exactly one of them red.
      expect(hasCrossRead(loop.body)).toBe(false);
    }
  });

  it('k2-independent: two carried locals, neither reading the other', () => {
    for (const c of sampleOf('k2-independent')) {
      const loop = findLoop(c.contract.methods[0]!.body)!;
      expect(new Set(assignTargets(loop.body))).toEqual(new Set(['acc', 'wacc']));
      expect(hasCrossRead(loop.body)).toBe(false);
      expect(readsBeforeReassign(loop.body, 'acc')).toBe(false);
    }
  });

  it('nested-inner-cross-read: the carried local is bound only inside the INNER body', () => {
    for (const c of sampleOf('nested-inner-cross-read')) {
      const outer = findLoop(c.contract.methods[0]!.body)!;
      const inner = innerLoop(outer)!;
      expect(inner).not.toBeNull();
      // Nothing is assigned at the outer level: at that scope `acc` and `wacc`
      // are bound only by the nested loop.
      expect(assignTargets(outer.body)).toEqual([]);
      expect(assignTargets(inner.body)).toEqual(['acc', 'wacc']);
      expect(hasCrossRead(inner.body)).toBe(true);
    }
  });

  it('nested-outer-read: bound in the INNER body, read one scope out', () => {
    for (const c of sampleOf('nested-outer-read')) {
      const outer = findLoop(c.contract.methods[0]!.body)!;
      const inner = innerLoop(outer)!;
      expect(assignTargets(inner.body)).toEqual(['acc']);
      expect(assignTargets(outer.body)).toEqual(['wacc']);
      const outerAssign = outer.body.find(
        (s): s is Extract<Stmt, { kind: 'assign' }> => s.kind === 'assign',
      )!;
      expect(refs(outerAssign.value)).toContain('acc');
    }
  });

  it('single-carrier: the historical shape is still reachable', () => {
    for (const c of sampleOf('single-carrier')) {
      const loop = findLoop(c.contract.methods[0]!.body)!;
      expect(new Set(assignTargets(loop.body))).toEqual(new Set(['acc']));
      expect(declaredCarriers(c.contract.methods[0]!.body)).toEqual(['acc']);
    }
  });

  it('a loop body never accumulates only literals (it would be constant-folded away)', () => {
    // Bounded loops are unrolled, so a body over literals and the loop counter
    // alone never reaches stack lowering — the shape would be in the corpus and
    // still never exercise the code under test.
    for (const shape of EXEC_LOOP_SHAPES) {
      for (const c of sampleOf(shape)) {
        const method = c.contract.methods[0]!;
        const runtime = new Set(method.params.filter((p) => p.type === 'bigint').map((p) => p.name));
        for (const p of c.contract.properties) if (p.type === 'bigint') runtime.add(p.name);
        expect(runtime.size, `${shape}: no runtime bigint in scope`).toBeGreaterThan(0);
        const loop = findLoop(method.body)!;
        const collect = (l: ForStmt): string[] =>
          l.body.flatMap((s) =>
            s.kind === 'for' ? collect(s) : s.kind === 'assign' ? refs(s.value) : [],
          );
        const propRefs = (l: ForStmt): string[] =>
          l.body.flatMap((s) =>
            s.kind === 'for'
              ? propRefs(s)
              : s.kind === 'assign'
                ? collectPropertyNames(s.value)
                : [],
          );
        const seen = [...collect(loop), ...propRefs(loop)];
        expect(
          seen.some((n) => runtime.has(n)),
          `${shape}: loop body has no runtime bigint reference`,
        ).toBe(true);
      }
    }
  });
});

function collectPropertyNames(expr: Expr, out: string[] = []): string[] {
  switch (expr.kind) {
    case 'property_ref':
      out.push(expr.name);
      break;
    case 'binary':
      collectPropertyNames(expr.left, out);
      collectPropertyNames(expr.right, out);
      break;
    case 'unary':
      collectPropertyNames(expr.operand, out);
      break;
    case 'ternary':
      collectPropertyNames(expr.condition, out);
      collectPropertyNames(expr.consequent, out);
      collectPropertyNames(expr.alternate, out);
      break;
    case 'call':
      expr.args.forEach((a) => collectPropertyNames(a, out));
      break;
  }
  return out;
}
