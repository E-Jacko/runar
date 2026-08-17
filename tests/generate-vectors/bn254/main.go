// Generates BN254 field arithmetic, G1 curve, and pairing test vectors using
// gnark-crypto as the reference implementation. These vectors validate Rúnar's
// compiled Bitcoin Script BN254 operations.
//
// Output: JSON files in ../../vectors/ for field ops, G1 ops, and pairings.
package main

import (
	"encoding/json"
	"fmt"
	"log"
	"math/big"
	"math/rand"
	"os"
	"path/filepath"

	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fp"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

// ---------------------------------------------------------------------------
// JSON types
// ---------------------------------------------------------------------------

type FpVectorFile struct {
	Field   string     `json:"field"`
	Prime   string     `json:"prime"`
	Vectors []FpVector `json:"vectors"`
}

type FpVector struct {
	Op          string  `json:"op"`
	A           string  `json:"a"`
	B           *string `json:"b,omitempty"`
	Expected    string  `json:"expected"`
	Description string  `json:"description"`
}

type G1VectorFile struct {
	Field   string     `json:"field"`
	Curve   string     `json:"curve"`
	Vectors []G1Vector `json:"vectors"`
}

type G1Vector struct {
	Op          string  `json:"op"`
	Ax          string  `json:"ax"`
	Ay          string  `json:"ay"`
	Bx          *string `json:"bx,omitempty"`
	By          *string `json:"by,omitempty"`
	Scalar      *string `json:"scalar,omitempty"`
	ExpectedX   string  `json:"expected_x"`
	ExpectedY   string  `json:"expected_y"`
	Description string  `json:"description"`
}

type PairingVectorFile struct {
	Field   string          `json:"field"`
	Vectors []PairingVector `json:"vectors"`
}

type PairingVector struct {
	Op       string   `json:"op"`
	G1Points []string `json:"g1_points"`
	G2Points []string `json:"g2_points"`
	// Group tags an equivalence class that MUST share one expected_gt. For a
	// single pairing the class key is the scalar product a*b mod r, because
	// e(a*G1, b*G2) = e(G1, G2)^(a*b) depends on nothing else. Two vectors in
	// one group with different expected_gt means the pairing that produced them
	// is not bilinear — an invariant a verifier can check WITHOUT owning a
	// second pairing implementation. Empty for vectors that stand alone.
	Group       string   `json:"group,omitempty"`
	ExpectedGT  []string `json:"expected_gt"`
	IsOne       bool     `json:"is_one"`
	Description string   `json:"description"`
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

// fpToHex returns a 64-char zero-padded hex string (32 bytes big-endian).
func fpToHex(f *fp.Element) string {
	b := f.Bytes()
	return fmt.Sprintf("%064x", new(big.Int).SetBytes(b[:]))
}

// fpFromU64 creates an fp.Element from a uint64.
func fpFromU64(v uint64) fp.Element {
	var f fp.Element
	f.SetUint64(v)
	return f
}

// fpFromBig creates an fp.Element from a *big.Int.
func fpFromBig(v *big.Int) fp.Element {
	var f fp.Element
	f.SetBigInt(v)
	return f
}

// g1ToHex returns (x_hex, y_hex) for an affine G1 point.
func g1ToHex(p *bn254.G1Affine) (string, string) {
	xb := p.X.Bytes()
	yb := p.Y.Bytes()
	return fmt.Sprintf("%064x", new(big.Int).SetBytes(xb[:])),
		fmt.Sprintf("%064x", new(big.Int).SetBytes(yb[:]))
}

// strPtr returns a pointer to a string (for optional JSON fields).
func strPtr(s string) *string { return &s }

var fpP *big.Int

func init() {
	fpP, _ = new(big.Int).SetString("21888242871839275222246405745257275088696311157297823662689037894645226208583", 10)
}

// ---------------------------------------------------------------------------
// Field arithmetic vector generators
// ---------------------------------------------------------------------------

func generateFpAddVectors() []FpVector {
	var vecs []FpVector
	rng := rand.New(rand.NewSource(42))

	add := func(a, b fp.Element, desc string) {
		var r fp.Element
		r.Add(&a, &b)
		bh := fpToHex(&b)
		vecs = append(vecs, FpVector{Op: "add", A: fpToHex(&a), B: &bh, Expected: fpToHex(&r), Description: desc})
	}

	// Edge cases
	add(fpFromU64(0), fpFromU64(0), "0 + 0 = 0")
	add(fpFromU64(1), fpFromU64(0), "1 + 0 = 1")
	add(fpFromU64(0), fpFromU64(1), "0 + 1 = 1")
	pMinus1 := fpFromBig(new(big.Int).Sub(fpP, big.NewInt(1)))
	add(pMinus1, fpFromU64(1), "(p-1) + 1 = 0")
	add(pMinus1, pMinus1, "(p-1) + (p-1) = p-2")

	// Small values
	for i := uint64(1); i <= 10; i++ {
		for j := uint64(1); j <= 10; j++ {
			add(fpFromU64(i), fpFromU64(j), fmt.Sprintf("%d + %d", i, j))
		}
	}

	// Random values
	for i := 0; i < 50; i++ {
		var a, b fp.Element
		a.SetUint64(rng.Uint64())
		b.SetUint64(rng.Uint64())
		add(a, b, fmt.Sprintf("random #%d", i))
	}

	return vecs
}

func generateFpSubVectors() []FpVector {
	var vecs []FpVector
	rng := rand.New(rand.NewSource(43))

	sub := func(a, b fp.Element, desc string) {
		var r fp.Element
		r.Sub(&a, &b)
		bh := fpToHex(&b)
		vecs = append(vecs, FpVector{Op: "sub", A: fpToHex(&a), B: &bh, Expected: fpToHex(&r), Description: desc})
	}

	sub(fpFromU64(0), fpFromU64(0), "0 - 0 = 0")
	sub(fpFromU64(1), fpFromU64(0), "1 - 0 = 1")
	sub(fpFromU64(0), fpFromU64(1), "0 - 1 = p-1")
	pMinus1 := fpFromBig(new(big.Int).Sub(fpP, big.NewInt(1)))
	sub(fpFromU64(1), pMinus1, "1 - (p-1) = 2")
	sub(pMinus1, pMinus1, "(p-1) - (p-1) = 0")

	for i := uint64(0); i <= 10; i++ {
		for j := uint64(0); j <= 10; j++ {
			sub(fpFromU64(i), fpFromU64(j), fmt.Sprintf("%d - %d", i, j))
		}
	}

	for i := 0; i < 50; i++ {
		var a, b fp.Element
		a.SetUint64(rng.Uint64())
		b.SetUint64(rng.Uint64())
		sub(a, b, fmt.Sprintf("random #%d", i))
	}

	return vecs
}

func generateFpMulVectors() []FpVector {
	var vecs []FpVector
	rng := rand.New(rand.NewSource(44))

	mul := func(a, b fp.Element, desc string) {
		var r fp.Element
		r.Mul(&a, &b)
		bh := fpToHex(&b)
		vecs = append(vecs, FpVector{Op: "mul", A: fpToHex(&a), B: &bh, Expected: fpToHex(&r), Description: desc})
	}

	mul(fpFromU64(0), fpFromU64(0), "0 * 0 = 0")
	mul(fpFromU64(1), fpFromU64(0), "1 * 0 = 0")
	mul(fpFromU64(1), fpFromU64(1), "1 * 1 = 1")
	pMinus1 := fpFromBig(new(big.Int).Sub(fpP, big.NewInt(1)))
	mul(pMinus1, pMinus1, "(-1) * (-1) = 1")
	mul(pMinus1, fpFromU64(2), "(-1) * 2 = p-2")

	for i := uint64(1); i <= 12; i++ {
		for j := uint64(1); j <= 12; j++ {
			mul(fpFromU64(i), fpFromU64(j), fmt.Sprintf("%d * %d", i, j))
		}
	}

	for i := 0; i < 50; i++ {
		var a, b fp.Element
		a.SetUint64(rng.Uint64())
		b.SetUint64(rng.Uint64())
		mul(a, b, fmt.Sprintf("random #%d", i))
	}

	return vecs
}

func generateFpInvVectors() []FpVector {
	var vecs []FpVector
	rng := rand.New(rand.NewSource(45))

	inv := func(a fp.Element, desc string) {
		var r fp.Element
		r.Inverse(&a)
		vecs = append(vecs, FpVector{Op: "inv", A: fpToHex(&a), Expected: fpToHex(&r), Description: desc})
	}

	inv(fpFromU64(1), "inv(1) = 1")
	inv(fpFromU64(2), "inv(2)")
	pMinus1 := fpFromBig(new(big.Int).Sub(fpP, big.NewInt(1)))
	inv(pMinus1, "inv(p-1) = p-1")

	for i := uint64(1); i <= 50; i++ {
		inv(fpFromU64(i), fmt.Sprintf("inv(%d)", i))
	}

	for i := 0; i < 30; i++ {
		var a fp.Element
		a.SetUint64(rng.Uint64() | 1) // ensure non-zero
		inv(a, fmt.Sprintf("random inv #%d", i))
	}

	return vecs
}

// ---------------------------------------------------------------------------
// G1 curve operation vector generators
// ---------------------------------------------------------------------------

func generateG1AddVectors() []G1Vector {
	var vecs []G1Vector

	// Generator
	_, _, g1Gen, _ := bn254.Generators()

	// Compute small multiples: 1G, 2G, ..., 10G
	points := make([]bn254.G1Affine, 11)
	// points[0] is zero-value (point at infinity)
	points[1].Set(&g1Gen)
	for i := 2; i <= 10; i++ {
		points[i].Add(&points[i-1], &g1Gen)
	}

	// Addition tests: iG + jG = (i+j)G
	for i := 1; i <= 5; i++ {
		for j := 1; j <= 5; j++ {
			var sum bn254.G1Affine
			sum.Add(&points[i], &points[j])
			ax, ay := g1ToHex(&points[i])
			bx, by := g1ToHex(&points[j])
			ex, ey := g1ToHex(&sum)
			vecs = append(vecs, G1Vector{
				Op: "add", Ax: ax, Ay: ay, Bx: strPtr(bx), By: strPtr(by),
				ExpectedX: ex, ExpectedY: ey,
				Description: fmt.Sprintf("%dG + %dG = %dG", i, j, i+j),
			})
		}
	}

	// P + (-P) = infinity — skip since infinity isn't a normal affine point

	return vecs
}

func generateG1ScalarMulVectors() []G1Vector {
	var vecs []G1Vector

	_, _, g1Gen, _ := bn254.Generators()

	// Small scalars
	for i := int64(1); i <= 10; i++ {
		var result bn254.G1Affine
		var s big.Int
		s.SetInt64(i)
		result.ScalarMultiplication(&g1Gen, &s)
		ex, ey := g1ToHex(&result)
		gx, gy := g1ToHex(&g1Gen)
		sc := fmt.Sprintf("%064x", &s)
		vecs = append(vecs, G1Vector{
			Op: "scalar_mul", Ax: gx, Ay: gy, Scalar: strPtr(sc),
			ExpectedX: ex, ExpectedY: ey,
			Description: fmt.Sprintf("%d * G", i),
		})
	}

	// Powers of 2
	for k := uint(1); k <= 10; k++ {
		var result bn254.G1Affine
		s := new(big.Int).Lsh(big.NewInt(1), k)
		result.ScalarMultiplication(&g1Gen, s)
		ex, ey := g1ToHex(&result)
		gx, gy := g1ToHex(&g1Gen)
		sc := fmt.Sprintf("%064x", s)
		vecs = append(vecs, G1Vector{
			Op: "scalar_mul", Ax: gx, Ay: gy, Scalar: strPtr(sc),
			ExpectedX: ex, ExpectedY: ey,
			Description: fmt.Sprintf("2^%d * G", k),
		})
	}

	// Random scalars
	rng := rand.New(rand.NewSource(46))
	for i := 0; i < 5; i++ {
		var result bn254.G1Affine
		var s fr.Element
		s.SetUint64(rng.Uint64())
		var sBig big.Int
		s.BigInt(&sBig)
		result.ScalarMultiplication(&g1Gen, &sBig)
		ex, ey := g1ToHex(&result)
		gx, gy := g1ToHex(&g1Gen)
		sc := fmt.Sprintf("%064x", &sBig)
		vecs = append(vecs, G1Vector{
			Op: "scalar_mul", Ax: gx, Ay: gy, Scalar: strPtr(sc),
			ExpectedX: ex, ExpectedY: ey,
			Description: fmt.Sprintf("random scalar #%d * G", i),
		})
	}

	return vecs
}

// ---------------------------------------------------------------------------
// Pairing vector generators
// ---------------------------------------------------------------------------

// pair is bn254.Pair with the error promoted to a panic — every call site here
// passes points that are on-curve and in the correct subgroup by construction,
// so an error is a generator bug, not a vector.
func pair(g1s []bn254.G1Affine, g2s []bn254.G2Affine) bn254.GT {
	gt, err := bn254.Pair(g1s, g2s)
	if err != nil {
		panic(fmt.Sprintf("pairing failed: %v", err))
	}
	return gt
}

func mulG1(p bn254.G1Affine, k *big.Int) bn254.G1Affine {
	var out bn254.G1Affine
	out.ScalarMultiplication(&p, k)
	return out
}

func mulG2(p bn254.G2Affine, k *big.Int) bn254.G2Affine {
	var out bn254.G2Affine
	out.ScalarMultiplication(&p, k)
	return out
}

// generatePairingVectors produces the BN254 pairing corpus.
//
// The pairing is the single most security-critical operation in the Groth16
// path and it has no official upstream KAT in this repo, so the corpus is built
// so that a verifier can falsify a wrong implementation using ALGEBRA over the
// recorded values alone, without owning a second pairing:
//
//   - bilinearity — e(a*G1, b*G2) depends only on a*b mod r, so every vector
//     carrying the same `group` key must carry byte-identical expected_gt.
//     Three spellings of each product (a on G1, a on G2, and the split a/b) are
//     emitted, so a pairing that is not bilinear cannot produce a consistent file.
//   - degeneracy — pairings that must equal the Fp12 identity carry is_one=true.
//   - non-degeneracy — negative controls that must NOT be the identity carry
//     is_one=false, so "return 1 always" is falsified too.
//
// conformance/scripts/check-bn254-pairing-invariants.mjs enforces all of this
// over the checked-in file.
func generatePairingVectors() []PairingVector {
	var vecs []PairingVector

	_, _, g1Gen, g2Gen := bn254.Generators()
	r := fr.Modulus()

	single := func(a, b *big.Int, group, desc string) {
		p1 := mulG1(g1Gen, a)
		p2 := mulG2(g2Gen, b)
		gt := pair([]bn254.G1Affine{p1}, []bn254.G2Affine{p2})
		var one bn254.GT
		one.SetOne()
		vecs = append(vecs, PairingVector{
			Op:          "single_pairing",
			G1Points:    g1AffineToHexSlice(p1),
			G2Points:    g2AffineToHexSlice(p2),
			Group:       group,
			ExpectedGT:  gtToHexSlice(&gt),
			IsOne:       gt.Equal(&one),
			Description: desc,
		})
	}

	// --- bilinearity classes -------------------------------------------------
	// For each product k, emit e(k*G1, G2), e(G1, k*G2) and every non-trivial
	// factorisation a*b = k. All of them MUST share one expected_gt.
	type factorisation struct{ a, b int64 }
	classes := []struct {
		k       int64
		factors []factorisation
	}{
		{1, nil},
		{2, nil},
		{6, []factorisation{{2, 3}, {3, 2}}},
		{35, []factorisation{{5, 7}, {7, 5}}},
		{42, []factorisation{{6, 7}, {7, 6}, {2, 21}, {21, 2}}},
		{1728, []factorisation{{12, 144}, {144, 12}}},
	}
	for _, c := range classes {
		k := big.NewInt(c.k)
		group := fmt.Sprintf("bilinear:k=%d", c.k)
		single(k, big.NewInt(1), group, fmt.Sprintf("e(%d*G1, G2) — bilinearity class k=%d", c.k, c.k))
		single(big.NewInt(1), k, group, fmt.Sprintf("e(G1, %d*G2) — same class, scalar moved to G2", c.k))
		for _, f := range c.factors {
			single(big.NewInt(f.a), big.NewInt(f.b),
				group,
				fmt.Sprintf("e(%d*G1, %d*G2) — same class, %d*%d = %d", f.a, f.b, f.a, f.b, c.k))
		}
	}

	// A large scalar and its reduction mod r land in the same class: the pairing
	// output depends on a*b mod r, not on the integer.
	{
		big1 := new(big.Int).Add(r, big.NewInt(2)) // r + 2 == 2 (mod r)
		single(big1, big.NewInt(1), "bilinear:k=2",
			"e((r+2)*G1, G2) — scalar reduces mod r into class k=2")
	}

	// --- degeneracy: results that MUST be the Fp12 identity -------------------
	// e(O, G2) and e(G1, O). gnark represents the point at infinity as the zero
	// value of the affine type.
	{
		var infG1 bn254.G1Affine
		var infG2 bn254.G2Affine
		gt := pair([]bn254.G1Affine{infG1}, []bn254.G2Affine{g2Gen})
		vecs = append(vecs, PairingVector{
			Op:          "single_pairing",
			G1Points:    g1AffineToHexSlice(infG1),
			G2Points:    g2AffineToHexSlice(g2Gen),
			ExpectedGT:  gtToHexSlice(&gt),
			IsOne:       true,
			Description: "e(O, G2) = 1 — G1 argument is the point at infinity",
		})
		gt2 := pair([]bn254.G1Affine{g1Gen}, []bn254.G2Affine{infG2})
		vecs = append(vecs, PairingVector{
			Op:          "single_pairing",
			G1Points:    g1AffineToHexSlice(g1Gen),
			G2Points:    g2AffineToHexSlice(infG2),
			ExpectedGT:  gtToHexSlice(&gt2),
			IsOne:       true,
			Description: "e(G1, O) = 1 — G2 argument is the point at infinity",
		})
	}

	// --- product pairings: the Groth16 check shape ----------------------------
	// e(a*G1, G2) * e(-G1, a*G2) = 1 for several a. This is the two-term form of
	// the Groth16 verification equation.
	for _, av := range []int64{1, 2, 42, 65537} {
		a := big.NewInt(av)
		aG1 := mulG1(g1Gen, a)
		aG2 := mulG2(g2Gen, a)
		var negG1 bn254.G1Affine
		negG1.Neg(&g1Gen)
		gt := pair(
			[]bn254.G1Affine{aG1, negG1},
			[]bn254.G2Affine{g2Gen, aG2},
		)
		vecs = append(vecs, PairingVector{
			Op:          "product_pairing",
			G1Points:    append(g1AffineToHexSlice(aG1), g1AffineToHexSlice(negG1)...),
			G2Points:    append(g2AffineToHexSlice(g2Gen), g2AffineToHexSlice(aG2)...),
			ExpectedGT:  gtToHexSlice(&gt),
			IsOne:       true,
			Description: fmt.Sprintf("e(%d*G1, G2) * e(-G1, %d*G2) = 1 (Groth16-style product)", av, av),
		})
	}

	// The full FOUR-term Groth16 shape:
	//   e(A, B) * e(-alpha, beta) * e(-C, delta) * e(-vk_x, gamma) = 1
	// built so the exponents sum to zero mod r:
	//   A = a*G1, B = b*G2 with a*b = alpha*beta + c*delta + x*gamma.
	{
		alpha, beta := big.NewInt(11), big.NewInt(13)
		c, delta := big.NewInt(17), big.NewInt(19)
		x, gamma := big.NewInt(23), big.NewInt(29)
		sum := new(big.Int).Mul(alpha, beta)
		sum.Add(sum, new(big.Int).Mul(c, delta))
		sum.Add(sum, new(big.Int).Mul(x, gamma))
		sum.Mod(sum, r) // == a*b with b = 1

		aG1 := mulG1(g1Gen, sum)
		bG2 := g2Gen
		negAlpha := mulG1(g1Gen, new(big.Int).Sub(r, new(big.Int).Mod(alpha, r)))
		betaG2 := mulG2(g2Gen, beta)
		negC := mulG1(g1Gen, new(big.Int).Sub(r, new(big.Int).Mod(c, r)))
		deltaG2 := mulG2(g2Gen, delta)
		negVkx := mulG1(g1Gen, new(big.Int).Sub(r, new(big.Int).Mod(x, r)))
		gammaG2 := mulG2(g2Gen, gamma)

		g1s := []bn254.G1Affine{aG1, negAlpha, negC, negVkx}
		g2s := []bn254.G2Affine{bG2, betaG2, deltaG2, gammaG2}
		gt := pair(g1s, g2s)
		var g1hex, g2hex []string
		for i := range g1s {
			g1hex = append(g1hex, g1AffineToHexSlice(g1s[i])...)
			g2hex = append(g2hex, g2AffineToHexSlice(g2s[i])...)
		}
		vecs = append(vecs, PairingVector{
			Op:          "product_pairing",
			G1Points:    g1hex,
			G2Points:    g2hex,
			ExpectedGT:  gtToHexSlice(&gt),
			IsOne:       true,
			Description: "e(A,B) * e(-alpha,beta) * e(-C,delta) * e(-vk_x,gamma) = 1 — the four-term Groth16 verification shape",
		})

		// NEGATIVE CONTROL: perturb one exponent by 1 and the product must stop
		// being the identity. Without this a verifier that returns 1 for every
		// input satisfies every is_one=true vector above.
		badA := mulG1(g1Gen, new(big.Int).Add(sum, big.NewInt(1)))
		badG1s := []bn254.G1Affine{badA, negAlpha, negC, negVkx}
		badGT := pair(badG1s, g2s)
		var badG1hex, badG2hex []string
		for i := range badG1s {
			badG1hex = append(badG1hex, g1AffineToHexSlice(badG1s[i])...)
			badG2hex = append(badG2hex, g2AffineToHexSlice(g2s[i])...)
		}
		vecs = append(vecs, PairingVector{
			Op:          "product_pairing",
			G1Points:    badG1hex,
			G2Points:    badG2hex,
			ExpectedGT:  gtToHexSlice(&badGT),
			IsOne:       false,
			Description: "NEGATIVE CONTROL: the same four-term product with A off by one generator — must NOT be 1",
		})
	}

	// More negative controls: single pairings that must not be the identity.
	for _, av := range []int64{1, 2, 3} {
		a := big.NewInt(av)
		aG1 := mulG1(g1Gen, a)
		var negG1 bn254.G1Affine
		negG1.Neg(&g1Gen)
		bad := big.NewInt(av + 1)
		badG2 := mulG2(g2Gen, bad)
		gt := pair(
			[]bn254.G1Affine{aG1, negG1},
			[]bn254.G2Affine{g2Gen, badG2},
		)
		vecs = append(vecs, PairingVector{
			Op:          "product_pairing",
			G1Points:    append(g1AffineToHexSlice(aG1), g1AffineToHexSlice(negG1)...),
			G2Points:    append(g2AffineToHexSlice(g2Gen), g2AffineToHexSlice(badG2)...),
			ExpectedGT:  gtToHexSlice(&gt),
			IsOne:       false,
			Description: fmt.Sprintf("NEGATIVE CONTROL: e(%d*G1, G2) * e(-G1, %d*G2) != 1 (exponents %d and %d disagree)", av, av+1, av, av+1),
		})
	}

	return vecs
}

func g1AffineToHexSlice(p bn254.G1Affine) []string {
	x, y := g1ToHex(&p)
	return []string{x, y}
}

func g2AffineToHexSlice(p bn254.G2Affine) []string {
	// G2 point has Fp2 coordinates: X = (X.A0, X.A1), Y = (Y.A0, Y.A1)
	xa0 := p.X.A0.Bytes()
	xa1 := p.X.A1.Bytes()
	ya0 := p.Y.A0.Bytes()
	ya1 := p.Y.A1.Bytes()
	return []string{
		fmt.Sprintf("%064x", new(big.Int).SetBytes(xa0[:])),
		fmt.Sprintf("%064x", new(big.Int).SetBytes(xa1[:])),
		fmt.Sprintf("%064x", new(big.Int).SetBytes(ya0[:])),
		fmt.Sprintf("%064x", new(big.Int).SetBytes(ya1[:])),
	}
}

func gtToHexSlice(gt *bn254.GT) []string {
	// GT is Fp12 = Fp6[w]/(w^2 - v), Fp6 = Fp2[v]/(v^3 - xi)
	// Marshal as 12 Fp elements in gnark-crypto's canonical order
	b := gt.Marshal()
	result := make([]string, 12)
	for i := 0; i < 12; i++ {
		elem := new(big.Int).SetBytes(b[i*32 : (i+1)*32])
		result[i] = fmt.Sprintf("%064x", elem)
	}
	return result
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

func main() {
	vectorsDir := filepath.Join("..", "..", "vectors")
	if err := os.MkdirAll(vectorsDir, 0o755); err != nil {
		log.Fatalf("create vectors dir: %v", err)
	}

	// Field arithmetic vectors
	for _, tc := range []struct {
		name string
		gen  func() []FpVector
	}{
		{"bn254_fp_add", generateFpAddVectors},
		{"bn254_fp_sub", generateFpSubVectors},
		{"bn254_fp_mul", generateFpMulVectors},
		{"bn254_fp_inv", generateFpInvVectors},
	} {
		vecs := tc.gen()
		file := FpVectorFile{
			Field:   "bn254_fp",
			Prime:   fpP.String(),
			Vectors: vecs,
		}
		data, err := json.MarshalIndent(file, "", "  ")
		if err != nil {
			log.Fatalf("json marshal %s: %v", tc.name, err)
		}
		path := filepath.Join(vectorsDir, tc.name+".json")
		if err := os.WriteFile(path, data, 0o644); err != nil {
			log.Fatalf("write %s: %v", path, err)
		}
		fmt.Printf("Generated %d vectors in %s\n", len(vecs), tc.name)
	}

	// G1 vectors
	addVecs := generateG1AddVectors()
	smVecs := generateG1ScalarMulVectors()
	allG1 := append(addVecs, smVecs...)
	g1File := G1VectorFile{
		Field:   "bn254",
		Curve:   "y^2 = x^3 + 3",
		Vectors: allG1,
	}
	g1Data, err := json.MarshalIndent(g1File, "", "  ")
	if err != nil {
		log.Fatalf("json marshal g1: %v", err)
	}
	if err := os.WriteFile(filepath.Join(vectorsDir, "bn254_g1.json"), g1Data, 0o644); err != nil {
		log.Fatalf("write g1: %v", err)
	}
	fmt.Printf("Generated %d G1 vectors\n", len(allG1))

	// Pairing vectors
	pairingVecs := generatePairingVectors()
	pFile := PairingVectorFile{
		Field:   "bn254",
		Vectors: pairingVecs,
	}
	pData, err := json.MarshalIndent(pFile, "", "  ")
	if err != nil {
		log.Fatalf("json marshal pairing: %v", err)
	}
	if err := os.WriteFile(filepath.Join(vectorsDir, "bn254_pairing.json"), pData, 0o644); err != nil {
		log.Fatalf("write pairing: %v", err)
	}
	fmt.Printf("Generated %d pairing vectors\n", len(pairingVecs))

	fmt.Println("\nAll BN254 test vectors written.")
}
