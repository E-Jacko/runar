// ---------------------------------------------------------------------------
// Audit C3 — property initializers are restricted to literal values.
//
// CLAUDE.md ("Property initializers"): "Properties can have `= value` defaults
// (literal values only: BigIntLiteral, BoolLiteral, ByteStringLiteral)."
//
// `ts`, `go` and `java` enforced this; `rust`, `zig`, `python` and `ruby` did
// not — they compiled e.g. `p: bigint = 1n + 2n;` and emitted a deployable
// locking script for a program the language does not define.
//
// The cross-tier diagnostic contract is the substring
// "initializer must be a literal value".
//
// Mirrored in the peer tiers:
//   compilers/go/frontend/validator_test.go
//   compilers/rust/src/frontend/validator.rs      (#[cfg(test)] mod tests)
//   compilers/python/tests/test_validator.py
//   compilers/zig/src/passes/validate.zig         (inline test blocks)
//   compilers/ruby/test/test_validator.rb
//   compilers/java/src/test/java/runar/compiler/passes/ValidateTest.java
// ---------------------------------------------------------------------------

import { describe, it, expect } from 'vitest';
import { parse } from '../passes/01-parse.js';
import { validate } from '../passes/02-validate.js';
import type { ValidationResult } from '../passes/02-validate.js';
import type { ContractNode } from '../ir/index.js';

function parseContract(source: string, fileName?: string): ContractNode {
  const result = parse(source, fileName);
  if (!result.contract) {
    throw new Error(`Parse failed: ${result.errors.map(e => e.message).join(', ')}`);
  }
  return result.contract;
}

function validateSource(source: string, fileName?: string): ValidationResult {
  return validate(parseContract(source, fileName));
}

function hasError(result: ValidationResult, substring: string): boolean {
  return result.errors.some(e => e.message.includes(substring));
}

/** The common cross-tier diagnostic substring. */
const NON_LITERAL_INIT = 'initializer must be a literal value';

describe('C3: property initializer must be a literal', () => {
  it('rejects an arithmetic property initializer', () => {
    const source = `
class Bad extends StatefulSmartContract {
  count: bigint = 1n + 2n;
  readonly owner: Addr;

  constructor(owner: Addr) {
    super(owner);
    this.owner = owner;
  }

  public bump() {
    this.count = this.count + 1n;
  }
}
`;
    const result = validateSource(source);
    expect(hasError(result, NON_LITERAL_INIT)).toBe(true);
  });

  it('rejects a call-expression property initializer', () => {
    const source = `
class Bad2 extends StatefulSmartContract {
  count: bigint = abs(-3n);
  readonly owner: Addr;

  constructor(owner: Addr) {
    super(owner);
    this.owner = owner;
  }

  public bump() {
    this.count = this.count + 1n;
  }
}
`;
    const result = validateSource(source);
    expect(hasError(result, NON_LITERAL_INIT)).toBe(true);
  });

  it('accepts bigint / boolean / bytestring / negative-bigint literals', () => {
    const source = `
class Good extends StatefulSmartContract {
  count: bigint = 7n;
  flag: boolean = true;
  tag: ByteString = 'deadbeef';
  offset: bigint = -3n;
  readonly owner: Addr;

  constructor(owner: Addr) {
    super(owner);
    this.owner = owner;
  }

  public bump() {
    this.count = this.count + 1n;
  }
}
`;
    const result = validateSource(source);
    expect(result.errors).toEqual([]);
  });
});
