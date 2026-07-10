package frontend

import (
	"strings"
	"testing"
)

// The @sighash (#123) and @embedAlways (#109) comment directives are now
// implemented on the TypeScript (.runar.ts) surface parser, matching the TS
// reference compiler. The eight non-TS surface parsers do NOT read comments,
// so the ParseSource dispatch fails closed on those formats rather than
// silently drop a security-critical directive. These tests pin both halves of
// that policy.

func TestParseSource_TSSurface_CompilesSighashDirective(t *testing.T) {
	src := []byte(`class Counter extends StatefulSmartContract {
		n: bigint;
		constructor(n: bigint) { super(n); this.n = n; }
		/** @sighash SINGLE|FORKID */
		public bump(): void { this.addOutput(1000n, this.n); }
	}`)
	res := ParseSource(src, "Counter.runar.ts")
	if len(res.Errors) != 0 {
		t.Fatalf("expected @sighash on .runar.ts to parse cleanly, got: %v", res.ErrorStrings())
	}
	if res.Contract == nil {
		t.Fatal("no contract parsed")
	}
	m := res.Contract.Methods[0]
	if m.SighashType == nil || *m.SighashType != 0x43 {
		t.Fatalf("expected bump SighashType 0x43, got %v", m.SighashType)
	}
}

func TestParseSource_TSSurface_CompilesEmbedAlwaysDirective(t *testing.T) {
	src := []byte(`class Counter extends SmartContract {
		/** @embedAlways */
		readonly x: bigint;
		constructor(x: bigint) { super(x); this.x = x; }
		public unlock(): void {}
	}`)
	res := ParseSource(src, "Counter.runar.ts")
	if len(res.Errors) != 0 {
		t.Fatalf("expected @embedAlways on .runar.ts to parse cleanly, got: %v", res.ErrorStrings())
	}
	if res.Contract == nil || len(res.Contract.Properties) == 0 {
		t.Fatal("no property parsed")
	}
	if !res.Contract.Properties[0].EmbedAlways {
		t.Fatal("expected EmbedAlways to be set on x")
	}
}

func TestParseSource_NonTSSurface_RejectsSighashDirective(t *testing.T) {
	// A .runar.sol surface parser ignores comments, so the guard must fire.
	src := []byte(`contract Counter {
		// @sighash SINGLE|FORKID
		function unlock() public {}
	}`)
	res := ParseSource(src, "Counter.runar.sol")
	joined := strings.Join(res.ErrorStrings(), "\n")
	if !strings.Contains(joined, "@sighash") || !strings.Contains(joined, "#123") {
		t.Fatalf("expected @sighash/#123 fail-closed error on .runar.sol, got: %s", joined)
	}
}

func TestParseSource_NonTSSurface_RejectsEmbedAlwaysDirective(t *testing.T) {
	src := []byte(`contract Counter {
		// @embedAlways
		x: uint;
	}`)
	res := ParseSource(src, "Counter.runar.sol")
	joined := strings.Join(res.ErrorStrings(), "\n")
	if !strings.Contains(joined, "@embedAlways") || !strings.Contains(joined, "#109") {
		t.Fatalf("expected @embedAlways/#109 fail-closed error on .runar.sol, got: %s", joined)
	}
}

func TestParseSource_AllowsSourceWithoutDirectives(t *testing.T) {
	// A field named "sighashType" must NOT trip the word-boundary guard.
	src := []byte(`class Counter extends SmartContract {
		public readonly sighashType: bigint;
		constructor(sighashType: bigint) { super(sighashType); this.sighashType = sighashType; }
		public unlock() {}
	}`)
	res := ParseSource(src, "Counter.runar.ts")
	for _, d := range res.Errors {
		if strings.Contains(d.Message, "not supported") {
			t.Fatalf("directive guard tripped on a non-directive identifier: %s", d.Message)
		}
	}
}
