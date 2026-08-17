package frontend

import (
	"strings"
	"testing"
)

// ---------------------------------------------------------------------------
// Audit C3 — property initializers are restricted to literal values.
//
// Mirrors packages/runar-compiler/src/__tests__/property-initializer-literal.test.ts
// ---------------------------------------------------------------------------

// nonLiteralInitMsg is the cross-tier diagnostic substring.
const nonLiteralInitMsg = "initializer must be a literal value"

func TestValidate_NonLiteralInitializer_ArithmeticRejected(t *testing.T) {
	source := `
import { StatefulSmartContract, Addr } from 'runar-lang';

class Bad extends StatefulSmartContract {
  count: bigint = 1n + 2n;
  readonly owner: Addr;

  constructor(owner: Addr) {
    super(owner);
    this.owner = owner;
  }

  public bump(): void {
    this.count = this.count + 1n;
  }
}
`
	contract := mustParseTS(t, source)
	result := Validate(contract)

	if !hasErrorContaining(result.ErrorStrings(), nonLiteralInitMsg) {
		t.Errorf("expected a non-literal-initializer error, got: %s", strings.Join(result.ErrorStrings(), "; "))
	}
}

func TestValidate_NonLiteralInitializer_CallRejected(t *testing.T) {
	source := `
import { StatefulSmartContract, Addr, abs } from 'runar-lang';

class Bad2 extends StatefulSmartContract {
  count: bigint = abs(-3n);
  readonly owner: Addr;

  constructor(owner: Addr) {
    super(owner);
    this.owner = owner;
  }

  public bump(): void {
    this.count = this.count + 1n;
  }
}
`
	contract := mustParseTS(t, source)
	result := Validate(contract)

	if !hasErrorContaining(result.ErrorStrings(), nonLiteralInitMsg) {
		t.Errorf("expected a non-literal-initializer error, got: %s", strings.Join(result.ErrorStrings(), "; "))
	}
}

func TestValidate_LiteralInitializers_Accepted(t *testing.T) {
	source := `
import { StatefulSmartContract, Addr, ByteString } from 'runar-lang';

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

  public bump(): void {
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
