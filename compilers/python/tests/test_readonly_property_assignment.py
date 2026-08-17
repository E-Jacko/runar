"""Audit C2 -- ``readonly`` property assignment must be rejected outside the constructor.

``spec/semantics.md:247``::

    <this.p = e, env, sigma> ==> ERROR: cannot assign to readonly property

Without the rule a contract that reassigns its readonly owner before checking
it compiles to ``76a97ca9788777`` -- hash160(pk) compared against hash160(pk),
true for ANY pubkey, i.e. anyone can spend.

The constructor MUST still be allowed to assign readonly properties.

Mirrors ``packages/runar-compiler/src/__tests__/readonly-property-assignment.test.ts``.
"""

from __future__ import annotations

from runar_compiler.frontend.parser_dispatch import parse_source
from runar_compiler.frontend.validator import ValidationResult, validate

# The cross-tier diagnostic substring.
READONLY_WRITE = "assign to readonly property"


def validate_source(source: str, file_name: str = "Test.runar.ts") -> ValidationResult:
    result = parse_source(source, file_name)
    assert result.contract is not None, f"parse failed: {result.errors}"
    return validate(result.contract)


def has_error(result: ValidationResult, needle: str) -> bool:
    return any(needle in d.message for d in result.errors)


def test_rejects_owner_hijack_contract():
    source = """
import { SmartContract, Addr, PubKey } from 'runar-lang';

class Hijack extends SmartContract {
  readonly ownerHash: Addr;

  constructor(ownerHash: Addr) {
    super(ownerHash);
    this.ownerHash = ownerHash;
  }

  public unlock(attackerPk: PubKey) {
    this.ownerHash = hash160(attackerPk);
    assert(hash160(attackerPk) === this.ownerHash);
  }
}
"""
    result = validate_source(source)
    assert has_error(result, READONLY_WRITE), (
        f"expected a readonly-write error, got: {result.error_strings()}"
    )
    assert has_error(result, "'ownerHash'"), (
        f"expected the offending property name, got: {result.error_strings()}"
    )


def test_rejects_readonly_write_in_stateful_method():
    source = """
import { StatefulSmartContract, Addr } from 'runar-lang';

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
"""
    result = validate_source(source)
    assert has_error(result, READONLY_WRITE), (
        f"expected a readonly-write error, got: {result.error_strings()}"
    )


def test_rejects_readonly_write_nested_in_if():
    source = """
import { StatefulSmartContract, Addr } from 'runar-lang';

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
"""
    result = validate_source(source)
    assert has_error(result, READONLY_WRITE), (
        f"expected a readonly-write error, got: {result.error_strings()}"
    )


def test_rejects_readonly_write_in_private_helper():
    source = """
import { StatefulSmartContract, Addr } from 'runar-lang';

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
"""
    result = validate_source(source)
    assert has_error(result, READONLY_WRITE), (
        f"expected a readonly-write error, got: {result.error_strings()}"
    )


def test_rejects_increment_of_readonly_property():
    source = """
import { StatefulSmartContract } from 'runar-lang';

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
"""
    result = validate_source(source)
    assert has_error(result, READONLY_WRITE), (
        f"expected a readonly-write error, got: {result.error_strings()}"
    )


def test_rejects_python_surface_hijack_contract():
    source = """
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
"""
    result = validate_source(source, "Hijack.runar.py")
    assert has_error(result, READONLY_WRITE), (
        f"expected a readonly-write error, got: {result.error_strings()}"
    )


# ---------------------------------------------------------------------------
# The constructor must keep working -- every contract assigns its readonly
# properties there.
# ---------------------------------------------------------------------------


def test_accepts_readonly_assignment_in_constructor():
    source = """
import { SmartContract, Addr, PubKey, Sig } from 'runar-lang';

class P2PKH extends SmartContract {
  readonly pubKeyHash: Addr;

  constructor(pubKeyHash: Addr) {
    super(pubKeyHash);
    this.pubKeyHash = pubKeyHash;
  }

  public unlock(sig: Sig, pubKey: PubKey) {
    assert(hash160(pubKey) === this.pubKeyHash);
    assert(checkSig(sig, pubKey));
  }
}
"""
    result = validate_source(source)
    assert result.errors == [], f"expected no errors, got: {result.error_strings()}"


def test_accepts_mutable_state_mutation():
    source = """
import { StatefulSmartContract, Addr } from 'runar-lang';

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
"""
    result = validate_source(source)
    assert result.errors == [], f"expected no errors, got: {result.error_strings()}"


def test_accepts_local_shadowing_a_readonly_property_name():
    source = """
import { StatefulSmartContract } from 'runar-lang';

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
"""
    result = validate_source(source)
    assert result.errors == [], f"expected no errors, got: {result.error_strings()}"
