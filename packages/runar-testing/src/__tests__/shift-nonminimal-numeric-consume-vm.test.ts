/**
 * A shift whose RESULT is a non-minimal zero must not be silently accepted by
 * the ANF interpreter when the deployed script rejects it.
 *
 * `OP_LSHIFT` / `OP_RSHIFT` operate on the operand's stack BYTES and PRESERVE
 * its byte length (spec/opcodes.md:176, docs/language-reference.md:287). So
 * `1 >> 1` leaves the 1-byte array `[0x00]` — a NON-MINIMAL encoding of zero;
 * the minimal encoding of zero is the empty array. Every numeric consumer on
 * chain (`OP_NUMEQUAL`, the relational ops, the arithmetic ops) enforces
 * minimal encoding on its operands, so the deployed script ABORTS with
 * "non-minimally encoded script number".
 *
 * `interpreter.ts` already threads `scriptBytes` through `& | ^ << >>` (that
 * is the 2026-07 chained-shift fix). But the comparison and arithmetic cases
 * then compare `left.value === right.value` — the DECODED number — and drop
 * `scriptBytes` on the floor. The interpreter therefore re-minimises the shift
 * result and ACCEPTS a spend no node will accept.
 *
 * Direction matters. `conformance/fuzz-regressions/entries/
 * 2026-07-14-chained-shift-or-nonminimal` pins the case where the interpreter
 * wrongly REJECTED a spend the script accepts, and its note says it exists so
 * that a one-sided fix cannot pass. This file pins the MIRROR case, which that
 * entry does not reach: the interpreter wrongly ACCEPTS a spend the script
 * REJECTS. That is the funds-locking direction — a developer tests with
 * `TestContract`, sees green, deploys, and the UTXO is unspendable.
 */

import { describe, it, expect } from 'vitest';
import { runTriModalExecution } from '../oracle/tri-modal-execution.js';

const SRC = (expr: string) => `import { SmartContract, assert } from 'runar-lang';

export class S extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f() { assert(${expr}); }
}
`;

function run(expr: string, n: bigint, fold: boolean) {
  return runTriModalExecution({
    source: SRC(expr),
    fileName: 'S.runar.ts',
    method: 'f',
    args: [],
    constructorArgs: { n },
    disableConstantFolding: fold,
  });
}

describe('a shift result that is a non-minimal zero', () => {
  for (const fold of [true, false]) {
    const mode = fold ? 'fold-OFF' : 'fold-ON';

    // `1 >> 1` -> [0x00]; OP_NUMEQUAL rejects the non-minimal operand.
    it(`>> producing [0x00] agrees between interpreter and Spend (${mode})`, () => {
      const r = run('(this.n >> 1n) === 0n', 1n, fold);
      expect(r.interpreterAccepted).toBe(r.spendAccepted);
    });

    // `1 << 64` also leaves a length-preserved zero.
    it(`<< producing [0x00] agrees between interpreter and Spend (${mode})`, () => {
      const r = run('(this.n << 64n) === 0n', 1n, fold);
      expect(r.interpreterAccepted).toBe(r.spendAccepted);
    });

    // Controls — a shift whose result is MINIMAL must keep working, so the fix
    // cannot "succeed" by rejecting every shift.
    it(`>> producing a minimal non-zero still accepts (${mode})`, () => {
      const r = run('(this.n >> 1n) === 1n', 2n, fold);
      expect(r.interpreterAccepted).toBe(true);
      expect(r.spendAccepted).toBe(true);
    });

    it(`<< producing a minimal non-zero still accepts (${mode})`, () => {
      const r = run('(this.n << 1n) === 2n', 1n, fold);
      expect(r.interpreterAccepted).toBe(true);
      expect(r.spendAccepted).toBe(true);
    });

    // A genuinely false guard must still reject on both sides.
    it(`a false guard over a minimal shift rejects on both (${mode})`, () => {
      const r = run('(this.n >> 1n) === 0n', 2n, fold);
      expect(r.interpreterAccepted).toBe(false);
      expect(r.spendAccepted).toBe(false);
    });
  }
});

describe('a non-minimal shift result consumed by a UNARY op or numeric builtin', () => {
  // The binary-op gate does not see these: the value goes straight into
  // OP_NOT / OP_ABS / a bool coercion without passing through `+ - * / %` or a
  // comparison. On chain those opcodes decode with fRequireMinimal=true too.
  for (const fold of [true, false]) {
    const mode = fold ? 'fold-OFF' : 'fold-ON';

    it(`bool() of a non-minimal shift agrees with Spend (${mode})`, () => {
      const r = run('bool(this.n >> 1n) === false', 1n, fold);
      expect(r.interpreterAccepted).toBe(r.spendAccepted);
    });

    it(`! of a non-minimal shift agrees with Spend (${mode})`, () => {
      const r = run('!bool(this.n >> 1n)', 1n, fold);
      expect(r.interpreterAccepted).toBe(r.spendAccepted);
    });

    it(`abs() of a non-minimal shift agrees with Spend (${mode})`, () => {
      const r = run('abs(this.n >> 1n) === 0n', 1n, fold);
      expect(r.interpreterAccepted).toBe(r.spendAccepted);
    });

    // Control: the same builtins over a MINIMAL shift result must still work.
    it(`abs() of a minimal shift result still accepts (${mode})`, () => {
      const r = run('abs(this.n >> 1n) === 1n', 2n, fold);
      expect(r.interpreterAccepted).toBe(true);
      expect(r.spendAccepted).toBe(true);
    });
  }
});
