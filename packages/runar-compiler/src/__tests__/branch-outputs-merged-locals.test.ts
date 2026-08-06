/**
 * A conditional that declares outputs and does ANYTHING ELSE the parent scope
 * can still observe is an unsupported shape and must be a HARD COMPILE ERROR in
 * every tier.
 *
 * Background: an `if` expression carries exactly ONE value. When a branch
 * contains an output intrinsic that value is already spoken for — it is the
 * output concat the continuation hash consumes (04-anf-lower's
 * `appendBranchOutputConcat`). Anything else the arm leaves behind breaks one of
 * two invariants nothing downstream enforces:
 *
 *   INV-A  the parent registers the if-expression's value as the branch's
 *          contribution to the continuation hash, so "the branch's output
 *          bytes" really means "whatever the arm's LAST binding is". A binding
 *          after the output silently replaces the serialized output with an
 *          unrelated value, and `drainBranchPrivateResidue` then physically
 *          drops the real output.
 *   INV-B  an arm that emits an output AND leaves any other nameable slot — a
 *          second merged local, a property write, a rebound local still read
 *          after the `if` — leaves 2+ results against the ONE stackMap name
 *          `lowerIf` registers, desyncing the parent stack from there on.
 *
 * Before the 2026-08-05 fixes the compiler emitted anyway, so the locking script
 * was permanently unspendable (OP_NUM2BIN / OP_NUMEQUALVERIFY / OP_ADD landing
 * on the wrong slot) — or, quieter, the continuation committed a bare script
 * number where a serialized output belonged, and the off-chain interpreter
 * agreed with it. Refusing at compile time is the fix. The real-Script-VM proof
 * of each shape lives in
 * packages/runar-testing/src/__tests__/branch-output-terminal-value-vm.test.ts.
 *
 * This file is the negative pin, plus the positive controls that stop the
 * predicate from being widened: R6/R7/R8 are legal and MUST keep compiling.
 * Reverting any clause to a silent emit must turn it red. Ported to all seven
 * tiers:
 *   compilers/go/compiler/branch_outputs_merged_locals_test.go
 *   compilers/rust/tests/branch_outputs_merged_locals_tests.rs
 *   compilers/python/tests/test_branch_outputs_merged_locals.py
 *   compilers/zig/src/tests/branch_outputs_merged_locals.zig
 *   compilers/ruby/test/test_branch_outputs_merged_locals.rb
 *   compilers/java/src/test/java/runar/compiler/passes/BranchOutputsMergedLocalsTest.java
 */

import { describe, it, expect } from 'vitest';
import { compile } from '../index.js';

// ---------------------------------------------------------------------------
// Sources. Kept byte-identical across all seven tiers.
// ---------------------------------------------------------------------------

/**
 * REJECTED: `if` with an output intrinsic in each arm, and two locals (`na`,
 * `nb`) merged ASYMMETRICALLY across the branch — the then-arm reassigns `na`,
 * the else-arm reassigns `nb`.
 */
const OUTPUTS_AND_MERGED_LOCALS = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsAndMergedLocals extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let na = this.a;
    let nb = this.b;
    if (this.a === 0n) {
      na = bidAmount;
      this.addOutput(bidAmount, this.closed, na, nb);
    } else {
      nb = bidAmount;
      this.addOutput(bidAmount, this.closed, na, nb);
    }
  }
}
`;

/**
 * REJECTED (INV-A): each arm emits its output and THEN rebinds a local, so the
 * arm's terminal binding — the one the parent registers as the branch's output
 * bytes — is a bare script number, and the real serialized output is dropped by
 * the residue drain.
 */
const OUTPUTS_THEN_REBIND = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsThenRebind extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let na = this.a;
    if (this.a === 0n) {
      this.addOutput(bidAmount, this.closed, bidAmount, this.b);
      na = bidAmount;
    } else {
      this.addOutput(bidAmount, this.closed, this.a, this.b);
      na = this.a;
    }
    assert(na > 0n);
  }
}
`;

/**
 * REJECTED (INV-A, local DEAD after the `if`): identical to OUTPUTS_THEN_REBIND
 * minus the post-`if` read. Pins that INV-A is independent of liveness, which is
 * why the predicate cannot be liveness-only.
 */
const OUTPUTS_THEN_REBIND_DEAD = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsThenRebindDead extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let na = this.a;
    if (this.a === 0n) {
      this.addOutput(bidAmount, this.closed, bidAmount, this.b);
      na = bidAmount;
    } else {
      this.addOutput(bidAmount, this.closed, this.a, this.b);
      na = this.a;
    }
  }
}
`;

/**
 * REJECTED (INV-A, ZERO merged locals): each arm emits a data output and THEN
 * writes a property. `lowerUpdateProp` renames the physical top to the property
 * name, so the receipt bytes are no longer on top and the drain deletes them —
 * stack lowering used to abort with an internal "value not found on stack".
 */
const OUTPUTS_THEN_PROP_WRITE = `import { StatefulSmartContract, assert } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class OutputsThenPropWrite extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public pay(payload: ByteString): void {
    assert(this.closed === 0n);
    if (this.a === 0n) {
      this.addDataOutput(0n, payload);
      this.b = 1n;
    } else {
      this.addDataOutput(0n, payload);
      this.b = 2n;
    }
    this.a = this.a + 1n;
  }
}
`;

/**
 * REJECTED (INV-B, ZERO merged locals): the property write comes BEFORE the
 * output, so each arm DOES end with its output intrinsic and the ANF-shape
 * invariant holds — and it is still unrepresentable. The property slot survives
 * `drainBranchPrivateResidue` (property names are pre-`if` names), so the arm
 * leaves two results against one registered stackMap name. This is the case
 * that rules out "arm ends with its output" as a sufficient predicate.
 */
const PROP_WRITE_THEN_OUTPUTS = `import { StatefulSmartContract, assert } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class PropWriteThenOutputs extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public pay(payload: ByteString): void {
    assert(this.closed === 0n);
    if (this.a === 0n) {
      this.b = 1n;
      this.addDataOutput(0n, payload);
    } else {
      this.b = 2n;
      this.addDataOutput(0n, payload);
    }
    this.a = this.a + 1n;
  }
}
`;

/**
 * REJECTED (INV-B, K=1): each arm rebinds one local BEFORE its output, and the
 * local is READ after the `if`. Being live puts it in `outerProtectedRefs`, so
 * `add_output` picks instead of rolling it and the arm ends two deep against one
 * registered stackMap name.
 */
const OUTPUTS_WITH_LIVE_REBIND = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsWithLiveRebind extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let na = this.a;
    if (this.a === 0n) {
      na = bidAmount;
      this.addOutput(bidAmount, this.closed, na, this.b);
    } else {
      na = bidAmount + 1n;
      this.addOutput(bidAmount, this.closed, na, this.b);
    }
    assert(na === bidAmount);
  }
}
`;

/**
 * ACCEPTED control: the same two asymmetrically merged locals, with the
 * `addOutput` moved after the `if` — the documented workaround, and the shape
 * the guard must NOT fire on.
 */
const OUTPUTS_AFTER_MERGED_LOCALS = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsAfterMergedLocals extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let na = this.a;
    let nb = this.b;
    if (this.a === 0n) {
      na = bidAmount;
    } else {
      nb = bidAmount;
    }
    this.addOutput(bidAmount, this.closed, na, nb);
  }
}
`;

/**
 * ACCEPTED control: OUTPUTS_WITH_LIVE_REBIND with the local DEAD after the
 * `if`, so `add_output` consumes the arm's own copy on last use and the arm
 * leaves exactly one result. Pins which K=1 sub-shape is genuinely safe, so the
 * predicate cannot be widened to "any rebound local".
 */
const OUTPUTS_WITH_DEAD_REBIND = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsWithDeadRebind extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let na = this.a;
    if (this.a === 0n) {
      na = bidAmount;
      this.addOutput(bidAmount, this.closed, na, this.b);
    } else {
      na = bidAmount + 1n;
      this.addOutput(bidAmount, this.closed, na, this.b);
    }
  }
}
`;

/**
 * ACCEPTED control / baseline: each arm emits its output and touches nothing
 * else. The whole point of the guard is that THIS still compiles — if it ever
 * stops, the predicate has been written far too wide.
 */
const OUTPUTS_ONLY = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsOnly extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    if (this.a === 0n) {
      this.addOutput(bidAmount, this.closed, bidAmount, this.b);
    } else {
      this.addOutput(bidAmount, this.closed, this.a, this.b);
    }
  }
}
`;

/**
 * ACCEPTED control: a pre-`if` local IS live across the `if`, but it is not one
 * the arms bind. Pins that the liveness clause is about names the ARM rebinds,
 * not about post-`if` liveness generally.
 */
const OUTPUTS_WITH_UNRELATED_LIVE_LOCAL = `import { StatefulSmartContract, assert } from 'runar-lang';

class OutputsWithUnrelatedLiveLocal extends StatefulSmartContract {
  closed: bigint = 0n;
  a: bigint = 0n;
  b: bigint = 0n;

  constructor(seed: bigint) {
    super(seed);
    this.closed = seed;
  }

  public bid(bidAmount: bigint): void {
    assert(this.closed === 0n);
    let guard = this.closed;
    let na = this.a;
    if (this.a === 0n) {
      na = bidAmount;
      this.addOutput(bidAmount, this.closed, na, this.b);
    } else {
      na = bidAmount + 1n;
      this.addOutput(bidAmount, this.closed, na, this.b);
    }
    assert(guard === 0n);
  }
}
`;

/** The joined error-severity diagnostics ('' when the source compiled). */
function compileErrors(source: string, fileName: string): string {
  const result = compile(source, { fileName });
  const errors = result.diagnostics.filter((d) => d.severity === 'error');
  if (errors.length > 0) {
    expect(result.success).toBe(false);
    expect(result.artifact).toBeUndefined();
  }
  return errors.map((d) => d.message).join('\n');
}

describe('conditional that declares outputs and does anything else', () => {
  const rejected: Array<[string, string, string, string]> = [
    // [case, source, fileName, reason clause the diagnostic must name]
    ['merges >=2 locals', OUTPUTS_AND_MERGED_LOCALS, 'OutputsAndMergedLocals.runar.ts',
      'merges 2 local variables (na, nb)'],
    ['rebinds a local after its output (INV-A)', OUTPUTS_THEN_REBIND, 'OutputsThenRebind.runar.ts',
      'continues past its output in the then-branch'],
    ['rebinds a dead local after its output (INV-A)', OUTPUTS_THEN_REBIND_DEAD, 'OutputsThenRebindDead.runar.ts',
      'continues past its output in the then-branch'],
    ['writes a property after its output (INV-A)', OUTPUTS_THEN_PROP_WRITE, 'OutputsThenPropWrite.runar.ts',
      'continues past its output in the then-branch'],
    ['writes a property before its output (INV-B)', PROP_WRITE_THEN_OUTPUTS, 'PropWriteThenOutputs.runar.ts',
      'assigns contract properties (b) inside the branch'],
    ['rebinds a local read after the if (INV-B)', OUTPUTS_WITH_LIVE_REBIND, 'OutputsWithLiveRebind.runar.ts',
      'reassigns local variables read after it (na)'],
  ];

  for (const [label, source, fileName, reason] of rejected) {
    it(`is rejected at compile time: ${label}`, () => {
      const msg = compileErrors(source, fileName);
      expect(msg).not.toBe('');
      expect(msg).toContain('Cannot compile conditional that both declares outputs and');
      expect(msg).toContain(reason);
      // Only the workaround that actually works is advertised. The rejected
      // sources already give each branch its own complete addOutput, so the old
      // "or give each branch its own complete addOutput" advice was a dead end.
      expect(msg).toContain(
        'Move the addOutput/addRawOutput/addDataOutput call after the if-statement');
      expect(msg).not.toContain('give each branch its own complete addOutput');
    });
  }

  const accepted: Array<[string, string, string]> = [
    ['the addOutput moves after the if', OUTPUTS_AFTER_MERGED_LOCALS, 'OutputsAfterMergedLocals.runar.ts'],
    ['the rebound local is dead after the if', OUTPUTS_WITH_DEAD_REBIND, 'OutputsWithDeadRebind.runar.ts'],
    ['each arm emits its output and nothing else', OUTPUTS_ONLY, 'OutputsOnly.runar.ts'],
    ['a live local across the if is not one the arms bind', OUTPUTS_WITH_UNRELATED_LIVE_LOCAL,
      'OutputsWithUnrelatedLiveLocal.runar.ts'],
  ];

  for (const [label, source, fileName] of accepted) {
    it(`does not fire when ${label}`, () => {
      expect(compileErrors(source, fileName)).toBe('');
      const result = compile(source, { fileName });
      expect(result.success).toBe(true);
      expect(result.artifact?.script).toBeTruthy();
    });
  }
});
