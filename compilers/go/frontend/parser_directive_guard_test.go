package frontend

import (
	"strings"
	"testing"
)

// The @sighash (#123) and @embedAlways (#109) comment directives are
// implemented only in the TypeScript compiler. The Go compiler must fail
// closed rather than silently drop them (see ParseSource directive guard).

func TestParseSource_RejectsSighashDirective(t *testing.T) {
	src := []byte(`class Counter extends SmartContract {
		public readonly x: bigint;
		constructor(x: bigint) { super(); this.x = x; }
		/** @sighash SINGLE|FORKID */
		public unlock() {}
	}`)
	res := ParseSource(src, "Counter.runar.ts")
	if len(res.Errors) == 0 {
		t.Fatal("expected an error diagnostic for @sighash directive, got none")
	}
	joined := strings.Join(res.ErrorStrings(), "\n")
	if !strings.Contains(joined, "@sighash") || !strings.Contains(joined, "#123") {
		t.Fatalf("expected @sighash/#123 fail-closed error, got: %s", joined)
	}
}

func TestParseSource_RejectsEmbedAlwaysDirective(t *testing.T) {
	src := []byte(`class Counter extends SmartContract {
		/** @embedAlways */
		public readonly x: bigint;
		constructor(x: bigint) { super(); this.x = x; }
		public unlock() {}
	}`)
	res := ParseSource(src, "Counter.runar.ts")
	if len(res.Errors) == 0 {
		t.Fatal("expected an error diagnostic for @embedAlways directive, got none")
	}
	joined := strings.Join(res.ErrorStrings(), "\n")
	if !strings.Contains(joined, "@embedAlways") || !strings.Contains(joined, "#109") {
		t.Fatalf("expected @embedAlways/#109 fail-closed error, got: %s", joined)
	}
}

func TestParseSource_AllowsSourceWithoutDirectives(t *testing.T) {
	// A field named "sighashType" must NOT trip the word-boundary guard.
	src := []byte(`class Counter extends SmartContract {
		public readonly sighashType: bigint;
		constructor(sighashType: bigint) { super(); this.sighashType = sighashType; }
		public unlock() {}
	}`)
	res := ParseSource(src, "Counter.runar.ts")
	for _, d := range res.Errors {
		if strings.Contains(d.Message, "not yet supported") {
			t.Fatalf("directive guard tripped on a non-directive identifier: %s", d.Message)
		}
	}
}
