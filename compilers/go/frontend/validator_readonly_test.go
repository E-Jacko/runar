package frontend

import (
	"strings"
	"testing"
)

// ---------------------------------------------------------------------------
// Audit C2 — `readonly` property assignment must be rejected outside the
// constructor.
//
// spec/semantics.md:247   <this.p = e, env, sigma> ==> ERROR: cannot assign to
//                         readonly property
//
// Mirrors packages/runar-compiler/src/__tests__/readonly-property-assignment.test.ts
// ---------------------------------------------------------------------------

// readonlyWriteMsg is the cross-tier diagnostic substring.
const readonlyWriteMsg = "assign to readonly property"

func hasErrorContaining(errs []string, needle string) bool {
	for _, e := range errs {
		if strings.Contains(e, needle) {
			return true
		}
	}
	return false
}

func TestValidate_ReadonlyWrite_HijackContractRejected(t *testing.T) {
	// Compiles to 76a97ca9788777 without the rule: hash160(pk) == hash160(pk),
	// true for ANY pubkey.
	source := `
import { SmartContract, assert, PubKey, Addr, hash160 } from 'runar-lang';

class Hijack extends SmartContract {
  readonly ownerHash: Addr;

  constructor(ownerHash: Addr) {
    super(ownerHash);
    this.ownerHash = ownerHash;
  }

  public unlock(attackerPk: PubKey): void {
    this.ownerHash = hash160(attackerPk);
    assert(hash160(attackerPk) === this.ownerHash);
  }
}
`
	contract := mustParseTS(t, source)
	result := Validate(contract)

	if !hasErrorContaining(result.ErrorStrings(), readonlyWriteMsg) {
		t.Errorf("expected a readonly-write error, got: %s", strings.Join(result.ErrorStrings(), "; "))
	}
	if !hasErrorContaining(result.ErrorStrings(), "'ownerHash'") {
		t.Errorf("expected the offending property name in the diagnostic, got: %s", strings.Join(result.ErrorStrings(), "; "))
	}
}

func TestValidate_ReadonlyWrite_StatefulMethodRejected(t *testing.T) {
	source := `
import { StatefulSmartContract, Addr } from 'runar-lang';

class Vault extends StatefulSmartContract {
  readonly owner: Addr;
  count: bigint;

  constructor(owner: Addr, count: bigint) {
    super(owner, count);
    this.owner = owner;
    this.count = count;
  }

  public bump(newOwner: Addr): void {
    this.owner = newOwner;
    this.count = this.count + 1n;
  }
}
`
	contract := mustParseTS(t, source)
	result := Validate(contract)

	if !hasErrorContaining(result.ErrorStrings(), readonlyWriteMsg) {
		t.Errorf("expected a readonly-write error, got: %s", strings.Join(result.ErrorStrings(), "; "))
	}
}

func TestValidate_ReadonlyWrite_NestedInIfRejected(t *testing.T) {
	source := `
import { StatefulSmartContract, Addr } from 'runar-lang';

class Nested extends StatefulSmartContract {
  readonly owner: Addr;
  count: bigint;

  constructor(owner: Addr, count: bigint) {
    super(owner, count);
    this.owner = owner;
    this.count = count;
  }

  public bump(newOwner: Addr, flag: boolean): void {
    if (flag) {
      this.owner = newOwner;
    } else {
      this.count = this.count + 1n;
    }
  }
}
`
	contract := mustParseTS(t, source)
	result := Validate(contract)

	if !hasErrorContaining(result.ErrorStrings(), readonlyWriteMsg) {
		t.Errorf("expected a readonly-write error, got: %s", strings.Join(result.ErrorStrings(), "; "))
	}
}

func TestValidate_ReadonlyWrite_PrivateHelperRejected(t *testing.T) {
	source := `
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

  public bump(newOwner: Addr): void {
    this.steal(newOwner);
    this.count = this.count + 1n;
  }
}
`
	contract := mustParseTS(t, source)
	result := Validate(contract)

	if !hasErrorContaining(result.ErrorStrings(), readonlyWriteMsg) {
		t.Errorf("expected a readonly-write error, got: %s", strings.Join(result.ErrorStrings(), "; "))
	}
}

func TestValidate_ReadonlyWrite_IncrementRejected(t *testing.T) {
	source := `
import { StatefulSmartContract } from 'runar-lang';

class Bump extends StatefulSmartContract {
  readonly limit: bigint;
  count: bigint;

  constructor(limit: bigint, count: bigint) {
    super(limit, count);
    this.limit = limit;
    this.count = count;
  }

  public go(): void {
    this.limit++;
    this.count = this.count + 1n;
  }
}
`
	contract := mustParseTS(t, source)
	result := Validate(contract)

	if !hasErrorContaining(result.ErrorStrings(), readonlyWriteMsg) {
		t.Errorf("expected a readonly-write error, got: %s", strings.Join(result.ErrorStrings(), "; "))
	}
}

func TestValidate_ReadonlyWrite_PythonSurfaceRejected(t *testing.T) {
	source := `
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
`
	parsed := ParseSource([]byte(source), "Hijack.runar.py")
	if parsed.Contract == nil {
		t.Fatalf("parse returned nil contract: %s", strings.Join(parsed.ErrorStrings(), "; "))
	}
	result := Validate(parsed.Contract)

	if !hasErrorContaining(result.ErrorStrings(), readonlyWriteMsg) {
		t.Errorf("expected a readonly-write error, got: %s", strings.Join(result.ErrorStrings(), "; "))
	}
}

// ---------------------------------------------------------------------------
// The constructor must keep working — every contract assigns its readonly
// properties there.
// ---------------------------------------------------------------------------

func TestValidate_ReadonlyWrite_ConstructorAssignmentAccepted(t *testing.T) {
	source := `
import { SmartContract, assert, PubKey, Sig, Addr, hash160, checkSig } from 'runar-lang';

class P2PKH extends SmartContract {
  readonly pubKeyHash: Addr;

  constructor(pubKeyHash: Addr) {
    super(pubKeyHash);
    this.pubKeyHash = pubKeyHash;
  }

  public unlock(sig: Sig, pubKey: PubKey): void {
    assert(hash160(pubKey) === this.pubKeyHash);
    assert(checkSig(sig, pubKey));
  }
}
`
	contract := mustParseTS(t, source)
	result := Validate(contract)

	if len(result.Errors) > 0 {
		t.Errorf("expected no validation errors, got: %s", strings.Join(result.ErrorStrings(), "; "))
	}
}

func TestValidate_ReadonlyWrite_MutableStateAccepted(t *testing.T) {
	source := `
import { StatefulSmartContract, Addr } from 'runar-lang';

class Counter extends StatefulSmartContract {
  readonly owner: Addr;
  count: bigint;

  constructor(owner: Addr, count: bigint) {
    super(owner, count);
    this.owner = owner;
    this.count = count;
  }

  public increment(): void {
    this.count = this.count + 1n;
  }
}
`
	contract := mustParseTS(t, source)
	result := Validate(contract)

	if len(result.Errors) > 0 {
		t.Errorf("expected no validation errors, got: %s", strings.Join(result.ErrorStrings(), "; "))
	}
}

func TestValidate_ReadonlyWrite_LocalShadowAccepted(t *testing.T) {
	source := `
import { StatefulSmartContract, assert } from 'runar-lang';

class Shadow extends StatefulSmartContract {
  readonly limit: bigint;
  count: bigint;

  constructor(limit: bigint, count: bigint) {
    super(limit, count);
    this.limit = limit;
    this.count = count;
  }

  public increment(): void {
    let limit: bigint = 5n;
    limit = 6n;
    assert(this.count < limit);
    this.count = this.count + 1n;
  }
}
`
	contract := mustParseTS(t, source)
	result := Validate(contract)

	if len(result.Errors) > 0 {
		t.Errorf("expected no validation errors, got: %s", strings.Join(result.ErrorStrings(), "; "))
	}
}
