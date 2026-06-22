// Command canonicalise is the Go-tier CLI shim for the cross-tier
// canonicalJson (RFC 8785 / JCS) differential fuzzer
// (conformance/fuzzer/canonical-json-differential.ts).
//
// Protocol (single-shot, stdin → stdout):
//
//	Request on stdin is a single JSON object, one of:
//	  {"mode":"json","value":<any JSON>}
//	      Parse `value` with Go's encoding/json (UseNumber, to preserve the
//	      int-vs-float distinction), run CanonicalJSON, print the canonical
//	      bytes to stdout and exit 0.
//	  {"mode":"utf16","key":"<string>","units":[<int>,...]}
//	      Build the object {key: <string built from UTF-16 code units>} where
//	      lone surrogates are emitted as their WTF-8 3-byte pattern (mirrors
//	      packages/runar-go/sdk_envelope_interop_test.go), run CanonicalJSON.
//
//	On a typed canonicalJson rejection (lone surrogate, non-finite number,
//	etc.) the shim prints "RUNAR_CANON_ERR:<message>" to stdout and exits 3.
//	On any other failure it exits 1. This lets the differential driver treat
//	"all tiers reject identically" as a non-divergence.
package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"os"

	runar "github.com/icellan/runar/packages/runar-go"
)

func main() {
	raw, err := io.ReadAll(os.Stdin)
	if err != nil {
		fmt.Fprintf(os.Stderr, "read stdin: %v\n", err)
		os.Exit(1)
	}

	// First pass: pull out mode/key/units and the raw `value` bytes.
	var envelope struct {
		Mode  string          `json:"mode"`
		Value json.RawMessage `json:"value"`
		Key   string          `json:"key"`
		Units []int64         `json:"units"`
	}
	if err := json.Unmarshal(raw, &envelope); err != nil {
		fmt.Fprintf(os.Stderr, "parse request: %v\n", err)
		os.Exit(1)
	}

	var input any
	switch envelope.Mode {
	case "json":
		dec := json.NewDecoder(bytes.NewReader(envelope.Value))
		dec.UseNumber()
		var v any
		if err := dec.Decode(&v); err != nil {
			fmt.Fprintf(os.Stderr, "parse value: %v\n", err)
			os.Exit(1)
		}
		input = normalize(v)
	case "utf16":
		input = map[string]any{envelope.Key: utf16UnitsToString(envelope.Units)}
	default:
		fmt.Fprintf(os.Stderr, "unknown mode %q\n", envelope.Mode)
		os.Exit(1)
	}

	out, err := runar.CanonicalJSON(input)
	if err != nil {
		// Typed canonicalJson rejection — report on stdout with a stable
		// prefix so the differential driver can compare rejection-vs-accept
		// across tiers.
		fmt.Printf("RUNAR_CANON_ERR:%s", err.Error())
		os.Exit(3)
	}
	fmt.Print(out)
}

// normalize converts json.Number leaves into int64 (when exact) or float64 so
// CanonicalJSON sees stable per-leaf types matching the JS source value.
// Mirrors normalizeJSON in sdk_envelope_interop_test.go.
func normalize(v any) any {
	switch x := v.(type) {
	case json.Number:
		if i, err := x.Int64(); err == nil {
			return i
		}
		f, _ := x.Float64()
		return f
	case map[string]any:
		out := make(map[string]any, len(x))
		for k, e := range x {
			out[k] = normalize(e)
		}
		return out
	case []any:
		out := make([]any, len(x))
		for i, e := range x {
			out[i] = normalize(e)
		}
		return out
	}
	return v
}

// utf16UnitsToString builds a Go string from UTF-16 code units. Surrogate
// pairs are decoded to their astral rune; lone surrogates are emitted as the
// WTF-8 3-byte pattern of the surrogate value itself so CanonicalJSON's
// escaper observes the lone surrogate (rather than a replacement char). This
// matches the construction in sdk_envelope_interop_test.go.
func utf16UnitsToString(units []int64) string {
	var b []byte
	for i := 0; i < len(units); i++ {
		u := units[i]
		if u >= 0xD800 && u <= 0xDBFF && i+1 < len(units) {
			lo := units[i+1]
			if lo >= 0xDC00 && lo <= 0xDFFF {
				r := 0x10000 + ((u - 0xD800) << 10) + (lo - 0xDC00)
				b = appendRuneUTF8(b, r)
				i++
				continue
			}
		}
		if u < 0x80 {
			b = append(b, byte(u))
		} else if u < 0x800 {
			b = append(b, byte(0xC0|(u>>6)), byte(0x80|(u&0x3F)))
		} else {
			// BMP (including lone surrogates): emit 3-byte form.
			b = append(b, byte(0xE0|(u>>12)), byte(0x80|((u>>6)&0x3F)), byte(0x80|(u&0x3F)))
		}
	}
	return string(b)
}

func appendRuneUTF8(b []byte, r int64) []byte {
	switch {
	case r < 0x80:
		return append(b, byte(r))
	case r < 0x800:
		return append(b, byte(0xC0|(r>>6)), byte(0x80|(r&0x3F)))
	case r < 0x10000:
		return append(b, byte(0xE0|(r>>12)), byte(0x80|((r>>6)&0x3F)), byte(0x80|(r&0x3F)))
	default:
		return append(b, byte(0xF0|(r>>18)), byte(0x80|((r>>12)&0x3F)), byte(0x80|((r>>6)&0x3F)), byte(0x80|(r&0x3F)))
	}
}
