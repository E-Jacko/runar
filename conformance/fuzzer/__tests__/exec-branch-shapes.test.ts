/**
 * REACHABILITY gate for the exec-oracle generator's BRANCH shapes.
 *
 * WHY THIS FILE EXISTS
 * --------------------
 * `arbExecMethodBody` emitted ZERO `if` statements, so `--execute` and
 * `--tri-modal` — the only OTHER absolute oracles in the repo besides
 * `--spend-oracle` — had no randomized branch coverage at all. Every
 * branch-merge miscompilation the project has shipped was outside their
 * reachable space *by construction*: no seed, no run count and no time budget
 * could have produced one. That is a structural hole, not bad luck, and the
 * same one `packages/runar-testing/src/__tests__/fuzzer-loop-shapes.test.ts`
 * closed for loop bodies.
 *
 * A probability argument is therefore not evidence here. Every assertion below
 * reads the generated IR — the actual `IfStmt` nodes — at a FIXED seed:
 *
 *   1. `arbExecCaseWithBranchShape(shape)` pins the topology, so each shape is
 *      proved reachable directly rather than waited for.
 *   2. The composite `arbExecCase` is sampled at one fixed seed and every shape
 *      is shown to appear.
 *   3. `ExecCase.branchShape` is a LABEL. Each case's shape is re-derived from
 *      its IR and must match, so a shape that claims a topology it does not
 *      emit fails here.
 *   4. The terminal assert is shown to contain an ORDER-SENSITIVE comparison
 *      between two DISTINCT branch locals — see the "commutativity" test below
 *      for why that is the load-bearing part.
 */

import { describe, it, expect } from 'vitest';
import fc from 'fast-check';

import { compile } from '../../../packages/runar-compiler/src/index.js';
import {
  EXEC_BRANCH_SHAPES,
  arbExecCase,
  arbExecCaseWithBranchShape,
  branchShapeLocals,
  branchShapeMerged,
  renderTypeScript,
  type ExecBranchShape,
  type ExecCase,
} from '../../../packages/runar-testing/src/fuzzer/index.js';
import type { Expr, IfStmt, Stmt } from '../../../packages/runar-testing/src/fuzzer/contract-ir.js';

const SEED = 424242;
const COMPOSITE = fc.sample(arbExecCase, { numRuns: 200, seed: SEED });

/** Order-sensitive comparison ops — `===` / `!==` are deliberately excluded. */
const ORDER_OPS = new Set(['<', '>', '<=', '>=']);

// ---------------------------------------------------------------------------
// IR helpers — these read the generated STATEMENTS, never the shape label
// ---------------------------------------------------------------------------

function methodBody(c: ExecCase): Stmt[] {
  return c.contract.methods[0]!.body;
}

/** The FIRST top-level `if` in a body, or null. */
function topLevelIf(body: Stmt[]): IfStmt | null {
  for (const s of body) if (s.kind === 'if') return s;
  return null;
}

function innerIf(stmt: IfStmt): IfStmt | null {
  for (const s of stmt.then) if (s.kind === 'if') return s;
  return null;
}

/** Local names assigned by a statement list (non-recursive), in order. */
function assignTargets(body: Stmt[]): string[] {
  return body
    .filter((s): s is Extract<Stmt, { kind: 'assign' }> => s.kind === 'assign' && !s.isProperty)
    .map((s) => s.target);
}

/** Every local assigned ANYWHERE in a statement tree. */
function allAssigned(body: Stmt[], out: Set<string> = new Set()): Set<string> {
  for (const s of body) {
    if (s.kind === 'assign' && !s.isProperty) out.add(s.target);
    else if (s.kind === 'if') {
      allAssigned(s.then, out);
      if (s.else_) allAssigned(s.else_, out);
    } else if (s.kind === 'for') allAssigned(s.body, out);
  }
  return out;
}

/** Names declared by `let` in a statement list. */
function declaredLocals(body: Stmt[]): string[] {
  return body
    .filter((s): s is Extract<Stmt, { kind: 'var_decl' }> => s.kind === 'var_decl')
    .map((s) => s.name);
}

function terminalAssert(body: Stmt[]): Expr {
  const last = body[body.length - 1]!;
  expect(last.kind).toBe('assert');
  return (last as Extract<Stmt, { kind: 'assert' }>).condition;
}

/**
 * Does `expr` contain `a <order-op> b` where `a` and `b` are DISTINCT locals
 * from `locals`? A pure slot SWAP of two such locals inverts this comparison,
 * which is exactly what a commutative `a + b <cmp> rhs` clause cannot see.
 */
function hasOrderSensitivePair(expr: Expr, locals: Set<string>): boolean {
  if (expr.kind !== 'binary') return false;
  if (
    ORDER_OPS.has(expr.op) &&
    expr.left.kind === 'var_ref' &&
    expr.right.kind === 'var_ref' &&
    expr.left.name !== expr.right.name &&
    locals.has(expr.left.name) &&
    locals.has(expr.right.name)
  ) {
    return true;
  }
  return hasOrderSensitivePair(expr.left, locals) || hasOrderSensitivePair(expr.right, locals);
}

/** Re-derive the branch topology from the IR alone. */
function deriveShape(body: Stmt[]): ExecBranchShape | null {
  const outer = topLevelIf(body);
  if (outer === null) return null;
  const inner = innerIf(outer);
  if (inner !== null) {
    // Nested declared-results-in-arm: outer has NO else, inner has one.
    if (outer.else_ === undefined && inner.else_ !== undefined) return 'nested-arm-sibling';
    return null;
  }
  return outer.else_ === undefined ? 'flat-if' : 'if-else';
}

// ---------------------------------------------------------------------------

describe('exec-oracle branch-shape reachability', () => {
  it('the composite generator emits `if` statements at all (the hole this closes)', () => {
    const withBranch = COMPOSITE.filter((c) => topLevelIf(methodBody(c)) !== null);
    expect(withBranch.length).toBeGreaterThan(0);
    // ...and does NOT emit one every time: the no-branch corpus must survive.
    expect(withBranch.length).toBeLessThan(COMPOSITE.length);
  });

  it('every branch shape is reachable through the composite generator', () => {
    const seen = new Set(COMPOSITE.map((c) => c.branchShape).filter((s) => s !== null));
    expect([...EXEC_BRANCH_SHAPES].filter((s) => !seen.has(s))).toEqual([]);
  });

  it('the `branchShape` LABEL matches the topology re-derived from the IR', () => {
    for (const c of COMPOSITE) {
      expect(deriveShape(methodBody(c)), `case labelled ${c.branchShape}`).toBe(c.branchShape);
    }
  });

  for (const shape of EXEC_BRANCH_SHAPES) {
    it(`pins ${shape} and emits exactly that topology`, () => {
      const cases = fc.sample(arbExecCaseWithBranchShape(shape), { numRuns: 8, seed: SEED });
      expect(cases.length).toBe(8);
      for (const c of cases) {
        const body = methodBody(c);
        expect(c.branchShape).toBe(shape);
        expect(deriveShape(body)).toBe(shape);

        // All three branch-region locals are declared, in order.
        const decls = declaredLocals(body);
        for (const name of branchShapeLocals(shape)) expect(decls).toContain(name);

        // Only the shape's declared results are ever rebound — `msib` never is,
        // so it stays a LIVE UNTOUCHED value in the branch region on every path.
        const assigned = allAssigned(body);
        for (const m of branchShapeMerged(shape)) expect(assigned.has(m)).toBe(true);
        expect(assigned.has('msib')).toBe(false);
      }
    });
  }

  it('nested-arm-sibling leaves a LIVE UNTOUCHED sibling inside the outer arm', () => {
    const cases = fc.sample(arbExecCaseWithBranchShape('nested-arm-sibling'), {
      numRuns: 12,
      seed: SEED,
    });
    for (const c of cases) {
      const body = methodBody(c);
      const outer = topLevelIf(body)!;
      // Degree of freedom 2: the OUTER `if` has no else, so only ONE outer path
      // rearranges the region and the two paths leave equal depth, different
      // layout.
      expect(outer.else_).toBeUndefined();
      // The outer arm holds nothing but the inner `if`.
      expect(outer.then.length).toBe(1);

      const inner = innerIf(outer)!;
      // The inner `if` keeps a REAL else — the confirmed #149 inner `if` had
      // one, and the compiler repair must not be gated on its absence.
      expect(inner.else_).toBeDefined();
      // Degree of freedom 1: the inner arms declare results for a PREFIX only
      // (`m0`), so `m1` is inherited, live and untouched.
      expect(assignTargets(inner.then)).toEqual(['m0']);
      expect(assignTargets(inner.else_!)).toEqual(['m0']);
      expect(allAssigned(body).has('m1')).toBe(false);
    }
  });

  it('the terminal assert is ORDER-SENSITIVE between distinct merged locals', () => {
    // This is the load-bearing property. The pre-existing terminal clauses are
    // all COMMUTATIVE in the merged locals (`a + b <cmp> rhs`), so a pure slot
    // SWAP leaves the value unchanged and the verdict identical — the oracle
    // reports agreement on a script that read the wrong slots. Every
    // branch-carrying case must therefore also carry `a <order-op> b`.
    const branchCases = COMPOSITE.filter((c) => c.branchShape !== null);
    expect(branchCases.length).toBeGreaterThan(0);
    for (const c of branchCases) {
      const locals = new Set(branchShapeLocals(c.branchShape!));
      expect(
        hasOrderSensitivePair(terminalAssert(methodBody(c)), locals),
        `${c.contract.name} terminal assert has no order-sensitive local pair`,
      ).toBe(true);
    }
  });

  it('every branch-carrying generated contract compiles', () => {
    for (const c of COMPOSITE.filter((x) => x.branchShape !== null)) {
      const source = renderTypeScript(c.contract);
      const r = compile(source, { fileName: `${c.contract.name}.runar.ts` });
      expect(
        r.success,
        `${c.contract.name} (${c.branchShape}) failed: ${r.diagnostics
          .map((d: { message: string }) => d.message)
          .join('; ')}`,
      ).toBe(true);
    }
  });
});
