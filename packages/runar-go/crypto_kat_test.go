package runar

// Independent OFFICIAL crypto known-answer tests.
//
// Unlike runtime_vectors_test.go (whose vectors are cross-SDK goldens the
// tiers agree on), the vectors here are copied verbatim from external
// authorities — the BLAKE3 team's own reference test file and RFC 6979 —
// and are NOT re-derived from any Runar tier. They exist to catch the
// BUG-101 failure mode, where a primitive was "validated" only against
// self-produced goldens that were themselves wrong.
//
// Sources are recorded in the `_source` field of each vendored JSON:
//   conformance/runtime-vectors/blake3-official-kat.json  (BLAKE3-team/BLAKE3)
//   conformance/runtime-vectors/ecdsa-rfc6979.json        (RFC 6979 A.2.5/A.2.6)

import (
	"crypto/elliptic"
	"encoding/hex"
	"encoding/json"
	"math/big"
	"os"
	"path/filepath"
	"runtime"
	"testing"
)

// runtimeVectorsDir walks up from this test file until it finds the
// conformance/runtime-vectors directory, so the test runs regardless of the
// working directory `go test` is invoked from.
func runtimeVectorsDir(t *testing.T) string {
	t.Helper()
	_, thisFile, _, ok := runtime.Caller(0)
	if !ok {
		t.Fatal("runtime.Caller failed")
	}
	dir := filepath.Dir(thisFile)
	for {
		candidate := filepath.Join(dir, "conformance", "runtime-vectors")
		if info, err := os.Stat(candidate); err == nil && info.IsDir() {
			return candidate
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			t.Fatalf("could not locate conformance/runtime-vectors walking up from %s", filepath.Dir(thisFile))
		}
		dir = parent
	}
}

func readVendoredKAT(t *testing.T, name string, dst interface{}) {
	t.Helper()
	path := filepath.Join(runtimeVectorsDir(t), name)
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", name, err)
	}
	if err := json.Unmarshal(data, dst); err != nil {
		t.Fatalf("parse %s: %v", name, err)
	}
}

// ---------------------------------------------------------------------------
// BLAKE3 — official reference vectors (BLAKE3-team/BLAKE3 test_vectors.json)
// ---------------------------------------------------------------------------

type blake3OfficialVector struct {
	InputLen int    `json:"input_len"`
	Input    string `json:"input"`
	Expected string `json:"expected"`
}

type blake3OfficialKAT struct {
	Vectors []blake3OfficialVector `json:"blake3_hash_official"`
}

func TestOfficialKAT_Blake3Hash(t *testing.T) {
	var kat blake3OfficialKAT
	readVendoredKAT(t, "blake3-official-kat.json", &kat)
	if len(kat.Vectors) == 0 {
		t.Fatal("blake3-official-kat.json carries no vectors")
	}
	for _, v := range kat.Vectors {
		v := v
		t.Run(v.Expected[:8], func(t *testing.T) {
			input, err := hex.DecodeString(v.Input)
			if err != nil {
				t.Fatalf("bad input hex: %v", err)
			}
			if len(input) != v.InputLen {
				t.Fatalf("input_len=%d but decoded %d bytes", v.InputLen, len(input))
			}
			got := hex.EncodeToString([]byte(Blake3Hash(ByteString(input))))
			if got != v.Expected {
				t.Errorf("Blake3Hash(len=%d) = %s; official BLAKE3 KAT wants %s", v.InputLen, got, v.Expected)
			}
		})
	}
}

// ---------------------------------------------------------------------------
// ECDSA P-256 / P-384 — RFC 6979 deterministic-ECDSA vectors
// ---------------------------------------------------------------------------

type ecdsaVector struct {
	Name         string `json:"name"`
	Curve        string `json:"curve"`
	Hash         string `json:"hash"`
	MessageASCII string `json:"message_ascii"`
	MessageHex   string `json:"message_hex"`
	Qx           string `json:"qx"`
	Qy           string `json:"qy"`
	R            string `json:"r"`
	S            string `json:"s"`
	Source       string `json:"source"`
}

type ecdsaKAT struct {
	Vectors []ecdsaVector `json:"ecdsa_rfc6979"`
}

// buildCompressedPubkey reconstructs the SEC1 compressed public key from the
// RFC's (Qx, Qy) — done here (not vendored precomputed) so the JSON stays a
// faithful copy of the RFC.
func buildCompressedPubkey(t *testing.T, curve elliptic.Curve, qxHex, qyHex string) []byte {
	t.Helper()
	qxb, err := hex.DecodeString(qxHex)
	if err != nil {
		t.Fatalf("bad qx hex: %v", err)
	}
	qyb, err := hex.DecodeString(qyHex)
	if err != nil {
		t.Fatalf("bad qy hex: %v", err)
	}
	x := new(big.Int).SetBytes(qxb)
	y := new(big.Int).SetBytes(qyb)
	if !curve.IsOnCurve(x, y) {
		t.Fatalf("RFC public key (Qx,Qy) is not on %s — vendored vector is corrupt", curve.Params().Name)
	}
	return elliptic.MarshalCompressed(curve, x, y)
}

// buildRawSig assembles the r[width]||s[width] raw signature the verifier expects.
func buildRawSig(t *testing.T, rHex, sHex string, width int) []byte {
	t.Helper()
	r, ok := new(big.Int).SetString(rHex, 16)
	if !ok {
		t.Fatalf("bad r hex: %s", rHex)
	}
	s, ok := new(big.Int).SetString(sHex, 16)
	if !ok {
		t.Fatalf("bad s hex: %s", sHex)
	}
	sig := make([]byte, 2*width)
	r.FillBytes(sig[:width])
	s.FillBytes(sig[width:])
	return sig
}

func TestOfficialKAT_ECDSA_RFC6979(t *testing.T) {
	var kat ecdsaKAT
	readVendoredKAT(t, "ecdsa-rfc6979.json", &kat)
	if len(kat.Vectors) == 0 {
		t.Fatal("ecdsa-rfc6979.json carries no vectors")
	}
	for _, v := range kat.Vectors {
		v := v
		t.Run(v.Name, func(t *testing.T) {
			var curve elliptic.Curve
			var width int
			var verify func(msg, sig, pk ByteString) bool
			switch v.Curve {
			case "P-256":
				curve, width, verify = elliptic.P256(), 32, VerifyECDSAP256
			case "P-384":
				curve, width, verify = elliptic.P384(), 48, VerifyECDSAP384
			default:
				t.Fatalf("unknown curve %q", v.Curve)
			}

			pubkey := buildCompressedPubkey(t, curve, v.Qx, v.Qy)
			sig := buildRawSig(t, v.R, v.S, width)
			msg := []byte(v.MessageASCII)

			// The published (r,s) MUST verify.
			if !verify(ByteString(msg), ByteString(sig), ByteString(pubkey)) {
				t.Fatalf("VerifyECDSA%s rejected the OFFICIAL %s signature (%s) — native impl disagrees with the RFC", v.Curve, v.Curve, v.Source)
			}

			// A 1-bit-flipped signature MUST be rejected.
			tampered := make([]byte, len(sig))
			copy(tampered, sig)
			tampered[len(tampered)-1] ^= 0x01
			if verify(ByteString(msg), ByteString(tampered), ByteString(pubkey)) {
				t.Errorf("VerifyECDSA%s accepted a 1-bit-tampered signature — must reject", v.Curve)
			}

			// A different message MUST be rejected.
			if verify(ByteString("wrong message"), ByteString(sig), ByteString(pubkey)) {
				t.Errorf("VerifyECDSA%s accepted the signature against the wrong message — must reject", v.Curve)
			}
		})
	}
}

// ---------------------------------------------------------------------------
// SLH-DSA (FIPS 205) — NIST ACVP known-answer vector
// ---------------------------------------------------------------------------

type slhDsaVector struct {
	Name          string `json:"name"`
	ParamSet      string `json:"param_set"`
	Pk            string `json:"pk"`
	Message       string `json:"message"`
	Signature     string `json:"signature"`
	ExpectedValid bool   `json:"expected_valid"`
}

type slhDsaKAT struct {
	Vectors []slhDsaVector `json:"slh_dsa_acvp"`
}

// slhParamsByName maps an ACVP parameterSet string to the native SLHParams.
func slhParamsByName(name string) (SLHParams, bool) {
	switch name {
	case "SLH-DSA-SHA2-128s":
		return SLH_SHA2_128s, true
	case "SLH-DSA-SHA2-128f":
		return SLH_SHA2_128f, true
	case "SLH-DSA-SHA2-192s":
		return SLH_SHA2_192s, true
	case "SLH-DSA-SHA2-192f":
		return SLH_SHA2_192f, true
	case "SLH-DSA-SHA2-256s":
		return SLH_SHA2_256s, true
	case "SLH-DSA-SHA2-256f":
		return SLH_SHA2_256f, true
	default:
		return SLHParams{}, false
	}
}

func TestOfficialKAT_SLHDSA_ACVP(t *testing.T) {
	var kat slhDsaKAT
	readVendoredKAT(t, "slh-dsa-acvp-kat.json", &kat)
	if len(kat.Vectors) == 0 {
		t.Fatal("slh-dsa-acvp-kat.json carries no vectors")
	}
	for _, v := range kat.Vectors {
		v := v
		t.Run(v.Name, func(t *testing.T) {
			params, ok := slhParamsByName(v.ParamSet)
			if !ok {
				t.Fatalf("unknown SLH-DSA param set %q", v.ParamSet)
			}
			pk, err := hex.DecodeString(v.Pk)
			if err != nil {
				t.Fatalf("bad pk hex: %v", err)
			}
			msg, err := hex.DecodeString(v.Message)
			if err != nil {
				t.Fatalf("bad message hex: %v", err)
			}
			sig, err := hex.DecodeString(v.Signature)
			if err != nil {
				t.Fatalf("bad signature hex: %v", err)
			}

			// The NIST-published signature is EXPECTED TO FAIL verification
			// today — this is a self-clearing xfail pinned to issue #137, NOT
			// a skip. CONFIRMED CONFORMANCE BUG (BUG-101 class): the native
			// SLH-DSA round-trips its OWN signatures (see
			// TestSLHDSA_SelfConsistency) but is NOT FIPS-205 conformant, so
			// it currently rejects this authoritative NIST ACVP signature.
			// The vector is copied verbatim from NIST (see
			// slh-dsa-acvp-kat.json _source) — the impl is at fault, NOT the
			// vector. At least one deviation is confirmed: slhHmsg's MGF1
			// seed omits the R||PK.seed prefix that FIPS-205 §11.2 mandates
			// (added to mitigate multi-target long-message 2nd-preimage
			// attacks); a patch experiment shows further verify-path
			// deviations remain beyond it, so a full FIPS-205 audit is
			// required (tracked in #137).
			//
			// When #137 is fixed and SLHVerify starts ACCEPTING the standard
			// vector, THIS ASSERTION FLIPS TO A FAILURE — that is the point:
			// it forces whoever fixes #137 to replace the block below with
			// `if !SLHVerify(...) { t.Fatalf(...) }` and delete this xfail
			// comment, instead of the bug rotting silently behind a skip.
			if SLHVerify(params, msg, sig, pk) {
				t.Fatalf("SLHVerify ACCEPTED the official NIST ACVP %s signature — issue #137 appears FIXED. Flip this xfail to require acceptance and delete the xfail comment.", v.ParamSet)
			}

			// A genuinely tampered signature MUST be rejected regardless of
			// #137 — that property holds whether or not the impl is
			// FIPS-205 conformant, so it runs unconditionally (it used to be
			// dead code behind the t.Skipf this xfail replaces).
			tampered := make([]byte, len(sig))
			copy(tampered, sig)
			tampered[len(tampered)-1] ^= 0x01
			if SLHVerify(params, msg, tampered, pk) {
				t.Errorf("SLHVerify accepted a 1-bit-tampered %s signature — must reject", v.ParamSet)
			}
		})
	}
}

// TestSLHDSA_SelfConsistency proves the native SLH-DSA impl round-trips its
// OWN signatures. If this passes but TestOfficialKAT_SLHDSA_ACVP fails, the
// divergence is localised to a FIPS-205 standard deviation (the exact BUG-101
// class: self-consistent but wrong vs. the published standard) rather than a
// harness error. Uses the fast 128f variant to keep signing quick.
func TestSLHDSA_SelfConsistency(t *testing.T) {
	if testing.Short() {
		t.Skip("skipping SLH-DSA self-consistency in -short mode")
	}
	params := SLH_SHA2_128f
	seed := make([]byte, 3*params.N)
	for i := range seed {
		seed[i] = byte(i)
	}
	kp := SLHKeygen(params, seed)
	msg := []byte("runar slh-dsa self-consistency probe")
	sig := SLHSign(params, msg, kp.SK)
	if !SLHVerify(params, msg, sig, kp.PK) {
		t.Fatal("SLHVerify rejected a signature produced by SLHSign — impl is not even self-consistent")
	}
	bad := make([]byte, len(sig))
	copy(bad, sig)
	bad[0] ^= 0x01
	if SLHVerify(params, msg, bad, kp.PK) {
		t.Error("SLHVerify accepted a tampered self-produced signature")
	}
}
