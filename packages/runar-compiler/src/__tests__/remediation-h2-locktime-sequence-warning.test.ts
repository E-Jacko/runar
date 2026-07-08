import { describe, it, expect } from 'vitest';
import { parse } from '../passes/01-parse.js';
import { validate } from '../passes/02-validate.js';
import type { ValidationResult } from '../passes/02-validate.js';
import type { ContractNode } from '../ir/index.js';

// ---------------------------------------------------------------------------
// H2 (#131): locktime soundness warning.
//
// A method that reads extractLocktime(preimage) only enforces a timelock if
// the covenant ALSO asserts the spending tx is non-final
// (extractSequence(preimage) < 0xffffffff). Without that, a hand-built
// all-final-sequence transaction bypasses the locktime gate. The compiler
// should emit an advisory WARNING (non-fatal) when a public method reads
// extractLocktime but does not (transitively) assert a sequence-finality
// guard.
// ---------------------------------------------------------------------------

const WARNING_NEEDLE = 'does not assert extractSequence';

function parseContract(source: string): ContractNode {
  const result = parse(source);
  if (!result.contract) {
    throw new Error(`Parse failed: ${result.errors.map(e => e.message).join(', ')}`);
  }
  return result.contract;
}

function validateSource(source: string): ValidationResult {
  return validate(parseContract(source));
}

function hasLocktimeWarning(result: ValidationResult): boolean {
  return result.warnings.some(w => w.message.includes(WARNING_NEEDLE));
}

describe('H2 (#131): extractLocktime without extractSequence guard', () => {
  it('warns when a method reads extractLocktime but has no sequence guard', () => {
    const source = `
      class TimeLock extends StatefulSmartContract {
        count: bigint;
        readonly deadline: bigint;
        constructor(count: bigint, deadline: bigint) {
          super(count, deadline);
          this.count = count;
          this.deadline = deadline;
        }
        public unlock() {
          assert(extractLocktime(this.txPreimage) >= this.deadline);
          this.count++;
        }
      }
    `;
    const result = validateSource(source);
    expect(hasLocktimeWarning(result)).toBe(true);
    // The warning names the method and points at the fix.
    const w = result.warnings.find(x => x.message.includes(WARNING_NEEDLE))!;
    expect(w.severity).toBe('warning');
    expect(w.message).toContain('unlock');
    expect(w.message).toContain('0xffffffff');
  });

  it('does NOT warn when the method also asserts extractSequence < final', () => {
    const source = `
      class TimeLock extends StatefulSmartContract {
        count: bigint;
        readonly deadline: bigint;
        constructor(count: bigint, deadline: bigint) {
          super(count, deadline);
          this.count = count;
          this.deadline = deadline;
        }
        public unlock() {
          assert(extractSequence(this.txPreimage) < 0xffffffffn);
          assert(extractLocktime(this.txPreimage) >= this.deadline);
          this.count++;
        }
      }
    `;
    const result = validateSource(source);
    expect(hasLocktimeWarning(result)).toBe(false);
  });

  it('does NOT warn for a method that never reads extractLocktime', () => {
    const source = `
      class Counter extends StatefulSmartContract {
        count: bigint;
        constructor(count: bigint) {
          super(count);
          this.count = count;
        }
        public increment() {
          this.count++;
        }
      }
    `;
    const result = validateSource(source);
    expect(hasLocktimeWarning(result)).toBe(false);
  });

  it('sees a sequence guard supplied transitively through a private helper', () => {
    const source = `
      class TimeLock extends StatefulSmartContract {
        count: bigint;
        readonly deadline: bigint;
        constructor(count: bigint, deadline: bigint) {
          super(count, deadline);
          this.count = count;
          this.deadline = deadline;
        }
        private requireNonFinal() {
          assert(extractSequence(this.txPreimage) < 0xffffffffn);
        }
        public unlock() {
          this.requireNonFinal();
          assert(extractLocktime(this.txPreimage) >= this.deadline);
          this.count++;
        }
      }
    `;
    const result = validateSource(source);
    expect(hasLocktimeWarning(result)).toBe(false);
  });

  it('warns when the locktime read is in a private helper but no sequence guard exists', () => {
    const source = `
      class TimeLock extends StatefulSmartContract {
        count: bigint;
        readonly deadline: bigint;
        constructor(count: bigint, deadline: bigint) {
          super(count, deadline);
          this.count = count;
          this.deadline = deadline;
        }
        private checkDeadline() {
          assert(extractLocktime(this.txPreimage) >= this.deadline);
        }
        public unlock() {
          this.checkDeadline();
          this.count++;
        }
      }
    `;
    const result = validateSource(source);
    expect(hasLocktimeWarning(result)).toBe(true);
  });
});
