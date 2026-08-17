// ---------------------------------------------------------------------------
// Audit C2 — `readonly` property assignment must be rejected outside the
// constructor.
//
// spec/semantics.md:247   <this.p = e, env, sigma> ==> ERROR: cannot assign to
//                         readonly property
// spec/grammar.md:94      readonly properties "cannot be reassigned"
//
// Before this rule existed, a contract that reassigned its readonly owner
// before checking it compiled to `76a97ca9788777` — hash160(pk) compared
// against hash160(pk), true for ANY pubkey, i.e. anyone can spend.
//
// The constructor MUST still be allowed to assign readonly properties.
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
const READONLY_WRITE = 'assign to readonly property';

describe('C2: readonly property assignment', () => {
  it('rejects the owner-hijack contract that reassigns its readonly owner', () => {
    // Compiles to 76a97ca9788777 without the rule: hash160(pk) == hash160(pk).
    const source = `
class Hijack extends SmartContract {
  readonly ownerHash: Addr;

  constructor(ownerHash: Addr) {
    super(ownerHash);
    this.ownerHash = ownerHash;
  }

  public unlock(attackerPk: PubKey) {
    this.ownerHash = hash160(attackerPk);
    assert(hash160(attackerPk) == this.ownerHash);
  }
}
`;
    const result = validateSource(source);
    expect(hasError(result, READONLY_WRITE)).toBe(true);
  });

  it('reports the offending property name', () => {
    const source = `
class Hijack extends SmartContract {
  readonly ownerHash: Addr;

  constructor(ownerHash: Addr) {
    super(ownerHash);
    this.ownerHash = ownerHash;
  }

  public unlock(attackerPk: PubKey) {
    this.ownerHash = hash160(attackerPk);
    assert(true);
  }
}
`;
    const result = validateSource(source);
    expect(result.errors.some(e => e.message.includes("'ownerHash'"))).toBe(true);
  });

  it('rejects a readonly write in a StatefulSmartContract method', () => {
    const source = `
class Vault extends StatefulSmartContract {
  readonly owner: Addr;
  count: bigint;

  constructor(owner: Addr, count: bigint) {
    super(owner, count);
    this.owner = owner;
    this.count = count;
  }

  public bump(newOwner: Addr) {
    this.owner = newOwner;
    this.count = this.count + 1n;
  }
}
`;
    const result = validateSource(source);
    expect(hasError(result, READONLY_WRITE)).toBe(true);
  });

  it('rejects a readonly write nested inside an if branch', () => {
    const source = `
class Nested extends StatefulSmartContract {
  readonly owner: Addr;
  count: bigint;

  constructor(owner: Addr, count: bigint) {
    super(owner, count);
    this.owner = owner;
    this.count = count;
  }

  public bump(newOwner: Addr, flag: boolean) {
    if (flag) {
      this.owner = newOwner;
    } else {
      this.count = this.count + 1n;
    }
  }
}
`;
    const result = validateSource(source);
    expect(hasError(result, READONLY_WRITE)).toBe(true);
  });

  it('rejects a readonly write in a private helper method', () => {
    const source = `
class Helper extends StatefulSmartContract {
  readonly owner: Addr;
  count: bigint;

  constructor(owner: Addr, count: bigint) {
    super(owner, count);
    this.owner = owner;
    this.count = count;
  }

  private steal(newOwner: Addr): void {
    this.owner = newOwner;
  }

  public bump(newOwner: Addr) {
    this.steal(newOwner);
    this.count = this.count + 1n;
  }
}
`;
    const result = validateSource(source);
    expect(hasError(result, READONLY_WRITE)).toBe(true);
  });

  it('rejects increment/decrement of a readonly property', () => {
    const source = `
class Bump extends StatefulSmartContract {
  readonly limit: bigint;
  count: bigint;

  constructor(limit: bigint, count: bigint) {
    super(limit, count);
    this.limit = limit;
    this.count = count;
  }

  public go() {
    this.limit++;
    this.count = this.count + 1n;
  }
}
`;
    const result = validateSource(source);
    expect(hasError(result, READONLY_WRITE)).toBe(true);
  });

  it('rejects the Python-surface hijack contract too', () => {
    const source = `
from runar import SmartContract, assert_, hash160, Readonly, ByteString, PubKey

class Hijack(SmartContract):
    owner_hash: Readonly[ByteString]

    def __init__(self, owner_hash: ByteString):
        super().__init__(owner_hash)
        self.owner_hash = owner_hash

    @public
    def unlock(self, attacker_pk: PubKey):
        self.owner_hash = hash160(attacker_pk)
        assert_(hash160(attacker_pk) == self.owner_hash)
`;
    const result = validateSource(source, 'Hijack.runar.py');
    expect(hasError(result, READONLY_WRITE)).toBe(true);
  });

  // -------------------------------------------------------------------------
  // The constructor must keep working — every contract assigns its readonly
  // properties there.
  // -------------------------------------------------------------------------

  it('accepts readonly assignment in the constructor', () => {
    const source = `
class P2PKH extends SmartContract {
  readonly pubKeyHash: Addr;

  constructor(pubKeyHash: Addr) {
    super(pubKeyHash);
    this.pubKeyHash = pubKeyHash;
  }

  public unlock(sig: Sig, pk: PubKey) {
    assert(hash160(pk) == this.pubKeyHash);
    assert(checkSig(sig, pk));
  }
}
`;
    const result = validateSource(source);
    expect(result.errors).toEqual([]);
  });

  it('accepts mutable state mutation in a StatefulSmartContract method', () => {
    const source = `
class Counter extends StatefulSmartContract {
  readonly owner: Addr;
  count: bigint;

  constructor(owner: Addr, count: bigint) {
    super(owner, count);
    this.owner = owner;
    this.count = count;
  }

  public increment() {
    this.count = this.count + 1n;
  }
}
`;
    const result = validateSource(source);
    expect(result.errors).toEqual([]);
  });

  it('accepts reading a readonly property in a method', () => {
    const source = `
class Reader extends StatefulSmartContract {
  readonly limit: bigint;
  count: bigint;

  constructor(limit: bigint, count: bigint) {
    super(limit, count);
    this.limit = limit;
    this.count = count;
  }

  public increment() {
    assert(this.count < this.limit);
    this.count = this.count + 1n;
  }
}
`;
    const result = validateSource(source);
    expect(result.errors).toEqual([]);
  });

  it('accepts a local variable that shadows a readonly property name', () => {
    const source = `
class Shadow extends StatefulSmartContract {
  readonly limit: bigint;
  count: bigint;

  constructor(limit: bigint, count: bigint) {
    super(limit, count);
    this.limit = limit;
    this.count = count;
  }

  public increment() {
    let limit: bigint = 5n;
    limit = 6n;
    assert(this.count < limit);
    this.count = this.count + 1n;
  }
}
`;
    const result = validateSource(source);
    expect(result.errors).toEqual([]);
  });
});
