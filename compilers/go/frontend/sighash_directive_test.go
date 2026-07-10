package frontend

import (
	"strings"
	"testing"
)

// #123 @sighash flag grammar — faithful port of the TS sighash-directive.test.ts.

func TestParseSighashFlags_CommonCombos(t *testing.T) {
	cases := map[string]int{
		"ALL|FORKID":              0x41,
		"SINGLE|FORKID":           0x43,
		"NONE|FORKID":             0x42,
		"ALL|ANYONECANPAY|FORKID": 0xc1,
	}
	for flags, want := range cases {
		r := parseSighashFlags(flags)
		if !r.ok() || r.value != want {
			t.Fatalf("parseSighashFlags(%q) = %+v, want value 0x%x", flags, r, want)
		}
	}
}

func TestParseSighashFlags_OrderAndWhitespace(t *testing.T) {
	r := parseSighashFlags(" FORKID | SINGLE ")
	if !r.ok() || r.value != 0x43 {
		t.Fatalf("got %+v, want 0x43", r)
	}
}

func TestParseSighashFlags_Default(t *testing.T) {
	if SighashDefault != 0x41 {
		t.Fatalf("SighashDefault = 0x%x, want 0x41", SighashDefault)
	}
	if r := parseSighashFlags("ALL|FORKID"); !r.ok() || r.value != SighashDefault {
		t.Fatalf("ALL|FORKID = %+v, want SighashDefault", r)
	}
}

func TestParseSighashFlags_UnknownFlag(t *testing.T) {
	r := parseSighashFlags("ALL|FORKD")
	if r.ok() || !strings.Contains(r.err, `unknown flag "FORKD"`) {
		t.Fatalf("got %+v, want unknown-flag error", r)
	}
}

func TestParseSighashFlags_RejectsAllNoneOnNames(t *testing.T) {
	r := parseSighashFlags("ALL|NONE|FORKID")
	if r.ok() || !strings.Contains(r.err, "cannot combine base types") {
		t.Fatalf("got %+v, want cannot-combine error", r)
	}
}

func TestParseSighashFlags_RejectsTwoBaseTypes(t *testing.T) {
	if r := parseSighashFlags("SINGLE|ALL"); r.ok() {
		t.Fatalf("SINGLE|ALL should be rejected, got %+v", r)
	}
}

func TestParseSighashFlags_RejectsNoBaseType(t *testing.T) {
	r := parseSighashFlags("FORKID|ANYONECANPAY")
	if r.ok() || !strings.Contains(r.err, "exactly one base type") {
		t.Fatalf("got %+v, want exactly-one-base-type error", r)
	}
}

func TestParseSighashFlags_RejectsDuplicate(t *testing.T) {
	r := parseSighashFlags("SINGLE|SINGLE|FORKID")
	if r.ok() || !strings.Contains(r.err, "duplicate flag") {
		t.Fatalf("got %+v, want duplicate-flag error", r)
	}
}

func TestParseSighashFlags_RejectsEmpty(t *testing.T) {
	if parseSighashFlags("").ok() {
		t.Fatal("empty flags should be rejected")
	}
	if parseSighashFlags("   ").ok() {
		t.Fatal("whitespace-only flags should be rejected")
	}
}

// F2: FORKID is mandatory on BSV (deploy-to-brick otherwise).
func TestParseSighashFlags_RequiresForkID(t *testing.T) {
	for _, flags := range []string{"SINGLE", "ALL", "NONE", "ALL|ANYONECANPAY"} {
		r := parseSighashFlags(flags)
		if r.ok() || !strings.Contains(r.err, "FORKID is mandatory on BSV") {
			t.Fatalf("parseSighashFlags(%q) = %+v, want FORKID-mandatory error", flags, r)
		}
	}
}

func TestParseSighashFlags_AcceptsWithForkID(t *testing.T) {
	if r := parseSighashFlags("SINGLE|FORKID"); !r.ok() || r.value != 0x43 {
		t.Fatalf("SINGLE|FORKID = %+v", r)
	}
	if r := parseSighashFlags("ALL|ANYONECANPAY|FORKID"); !r.ok() || r.value != 0xc1 {
		t.Fatalf("ALL|ANYONECANPAY|FORKID = %+v", r)
	}
}

func TestExtractSighashDirective(t *testing.T) {
	r, present := extractSighashDirective("/** @sighash SINGLE|FORKID */")
	if !present || !r.ok() || r.value != 0x43 {
		t.Fatalf("JSDoc extract = %+v present=%v", r, present)
	}
	r, present = extractSighashDirective("// @sighash NONE|FORKID")
	if !present || !r.ok() || r.value != 0x42 {
		t.Fatalf("line-comment extract = %+v present=%v", r, present)
	}
	if _, present := extractSighashDirective("/** no directive here */"); present {
		t.Fatal("no-directive text should report absent")
	}
}

func TestDescribeSighash(t *testing.T) {
	cases := map[int]string{
		0x41: "ALL|FORKID",
		0x43: "SINGLE|FORKID",
		0xc1: "ALL|ANYONECANPAY|FORKID",
		0x42: "NONE|FORKID",
	}
	for v, want := range cases {
		if got := describeSighash(v); got != want {
			t.Fatalf("describeSighash(0x%x) = %q, want %q", v, got, want)
		}
	}
}
