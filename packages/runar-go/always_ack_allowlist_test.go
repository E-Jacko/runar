package runar

import (
	"encoding/json"
	"os"
	"regexp"
	"sort"
	"strings"
	"testing"
)

// Testing-gap remediation Phase A5 (Go tier): machine-checked gate on the
// always-ack MockProvider escape hatches (NewAlwaysAckMockProvider,
// DisableBroadcastValidation, EnableBroadcastValidation(false)).
//
// A _test.go file may only use one of those escape hatches if it has a
// matching entry in always_ack_allowlist.json. The gate is enforced in BOTH
// directions: it fails on unlisted always-ack usage (someone quietly
// re-disabling the fund-safety net) AND on stale entries (a file that no
// longer needs always-ack, or that was deleted) — so the list can only shrink.
//
// Mirrors packages/runar-sdk/src/__tests__/always-ack-allowlist.test.ts.

var alwaysAckPattern = regexp.MustCompile(
	`NewAlwaysAckMockProvider|DisableBroadcastValidation|EnableBroadcastValidation\(\s*false\s*\)`)

var validAllowlistCategories = map[string]bool{
	"structure-only": true,
	"negative-api":   true,
	"fixture-shape":  true,
	"pending-a3":     true,
}

type alwaysAckAllowlistEntry struct {
	File     string `json:"file"`
	Reason   string `json:"reason"`
	Category string `json:"category"`
}

type alwaysAckAllowlist struct {
	Comment string                    `json:"$comment"`
	Entries []alwaysAckAllowlistEntry `json:"entries"`
}

func readAlwaysAckAllowlist(t *testing.T) alwaysAckAllowlist {
	t.Helper()
	raw, err := os.ReadFile("always_ack_allowlist.json")
	if err != nil {
		t.Fatalf("read always_ack_allowlist.json: %v", err)
	}
	var al alwaysAckAllowlist
	if err := json.Unmarshal(raw, &al); err != nil {
		t.Fatalf("parse always_ack_allowlist.json: %v", err)
	}
	return al
}

// filesUsingAlwaysAck returns every *_test.go in this package that calls an
// always-ack escape hatch. This audit file itself is excluded: it names the
// hatches in a regexp, not at a call site.
func filesUsingAlwaysAck(t *testing.T) map[string]bool {
	t.Helper()
	entries, err := os.ReadDir(".")
	if err != nil {
		t.Fatalf("readdir: %v", err)
	}
	found := map[string]bool{}
	for _, e := range entries {
		name := e.Name()
		if e.IsDir() || !strings.HasSuffix(name, "_test.go") || name == "always_ack_allowlist_test.go" {
			continue
		}
		body, err := os.ReadFile(name)
		if err != nil {
			t.Fatalf("read %s: %v", name, err)
		}
		if alwaysAckPattern.Match(body) {
			found[name] = true
		}
	}
	return found
}

func TestAlwaysAckAllowlist_EntriesAreWellFormed(t *testing.T) {
	for _, e := range readAlwaysAckAllowlist(t).Entries {
		if strings.TrimSpace(e.File) == "" {
			t.Errorf("allowlist entry with empty file: %+v", e)
		}
		if strings.TrimSpace(e.Reason) == "" {
			t.Errorf("allowlist entry %q has no reason", e.File)
		}
		if !validAllowlistCategories[e.Category] {
			t.Errorf("allowlist entry %q has invalid category %q (want structure-only|negative-api|fixture-shape|pending-a3)",
				e.File, e.Category)
		}
	}
}

func TestAlwaysAckAllowlist_EveryEntryNamesAnExistingFile(t *testing.T) {
	for _, e := range readAlwaysAckAllowlist(t).Entries {
		if _, err := os.Stat(e.File); err != nil {
			t.Errorf("always_ack_allowlist.json names %q, which does not exist; remove the entry", e.File)
		}
	}
}

func TestAlwaysAckAllowlist_NoStaleEntries(t *testing.T) {
	usage := filesUsingAlwaysAck(t)
	for _, e := range readAlwaysAckAllowlist(t).Entries {
		if _, err := os.Stat(e.File); err != nil {
			continue // covered by the existence test
		}
		if !usage[e.File] {
			t.Errorf("always_ack_allowlist.json has a STALE entry for %q — the file no longer uses "+
				"NewAlwaysAckMockProvider / DisableBroadcastValidation / EnableBroadcastValidation(false). "+
				"Remove it: the allowlist must only shrink.", e.File)
		}
	}
}

func TestAlwaysAckAllowlist_NoUngovernedOptOut(t *testing.T) {
	listed := map[string]bool{}
	for _, e := range readAlwaysAckAllowlist(t).Entries {
		listed[e.File] = true
	}
	var unlisted []string
	for f := range filesUsingAlwaysAck(t) {
		if !listed[f] {
			unlisted = append(unlisted, f)
		}
	}
	sort.Strings(unlisted)
	if len(unlisted) > 0 {
		t.Fatalf("Unlisted always-ack MockProvider usage:\n  - %s\n"+
			"Add an entry to always_ack_allowlist.json with a file, reason and category "+
			"(structure-only|negative-api|fixture-shape|pending-a3), or fix the test to run "+
			"under the default validating provider instead.",
			strings.Join(unlisted, "\n  - "))
	}
}
