# EC degenerate cases — semantics and the commit-pairing constraint (2026-08)

Durable record for the three degenerate inputs the secp256k1 / P-256 / P-384
codegen has to answer for, and for a **bisect hazard** that is invisible in any
single commit.

## ⚠ `03f50d48` and `f16790a9` MUST NEVER BE SEPARATED

`03f50d48` gave the scalar ladder an add-or-double select at its **last step
only**. The proof that one step suffices is an interval argument: after step `i`
the accumulator holds `c_i·P` with `c_i = (k + 3n) >> i`, and the degenerate
cases are `c_i ≡ 0, 1, 2 (mod n)`. Enumerating them by interval arithmetic
shows only `i = 0` qualifies.

**That enumeration is conditioned on `k ∈ [0, n−1]`.** The reduce that makes it
true — `k mod n` before the `+3n` — landed in the NEXT commit, `f16790a9`.

So `03f50d48` on its own is **unsound**: with an unbounded scalar, `c_i` is free
to hit `0, 1, 2 (mod n)` at steps other than `i = 0`, where there is no select
and the Jacobian mixed-add silently returns the point at infinity (`Z3 = 0`,
which `fieldInv`-as-Fermat turns into the all-zero point). The scalar is
normally an unlock argument, i.e. attacker-chosen.

Consequences:

- never `git bisect` a range that lands between these two commits and trust the
  result of an EC test;
- never cherry-pick or revert one without the other;
- any change to the `+3n` offset, the iteration count, or the reduce invalidates
  the interval argument and must redo it.

This warning is duplicated in the `buildJacobianAddOrDoubleInline` comment of
all seven tiers' EC codegen modules, because that is where someone will be
standing when they consider changing it.

## The three degenerate inputs and their answers

The affine `x‖y` encoding cannot represent the point at infinity `O`. Rather
than fail, the codegen encodes `O` as the **all-zero blob** and relies on
`ecOnCurve` / `pNNNOnCurve` to reject it (`0² ≠ 0³ + b` on all three curves).

| Input | Result | Where |
|---|---|---|
| `ecMul(P, 0n)`, `ecMulGen(0n)`, any `k ≡ 0 (mod n)` | all-zero point | ladder: `Z3 = 0` |
| `ecAdd(P, ecNegate(P))`, any `P.x == Q.x` with `P.y != Q.y` | all-zero point | `affineAdd` `notinf` mask |
| `ecAdd(P, P)` | `2P` (tangent) | `affineAdd` `cond` select |

The second row is the 2026-08 change. Selecting the tangent on `px == qx`
**alone** — as `03f50d48` did — answered `P + (−P)` with `2P`: on-curve,
plausible, and wrong. That is strictly worse than the behaviour it replaced,
because the pre-`03f50d48` chord path divided by zero and produced an *off*-curve
blob, so the idiom the codegen documents —

```ts
const r = p384Add(a, b);
assert(p384OnCurve(r));
```

— used to reject `p384Add(G, p384Negate(G))` and, after `03f50d48`, accepted it.

### Why all-zero and not "reject"

Three reasons, in order of weight:

1. **The optimizer already answers all-zero.** `ec-mulgen-linear` in
   `optimizer/ec-rules.json` rewrites `ecAdd(ecMulGen(k1), ecMulGen(k2))` into
   `ecMulGen(k1 + k2)`. For `k1 + k2 ≡ 0 (mod n)` the rewritten spelling is
   `ecMulGen(0)` → all-zero. Rejecting in `ecAdd` would make the same source
   produce two different behaviours depending on whether the optimizer fired.
2. It matches `ecMul(P, 0n)`, so `O` has ONE encoding across the whole surface.
3. `ecAdd` is a pure value-producing expression with no failure channel; adding
   one turns attacker-chosen input into a liveness failure. Same argument
   `f16790a9` used for reducing the scalar instead of rejecting it.

Measured cost: **+21 script bytes** per `ecAdd` / `p256Add` / `p384Add`
(+0.083% / +0.106% / +0.045%).

## `decompressPubKey` and the ladder's precondition

The ladder's exception analysis holds for points **on** the curve, where
cofactor 1 pins `ord(P) = n`. `decompressPubKey` (the P-256 / P-384 ECDSA
verifier's only pubkey entry point) computed `y = (x³ − 3x + b)^((p+1)/4)` and
never checked `y² == x³ − 3x + b`, nor `x < p`. For an `x` whose RHS is a
quadratic non-residue the recovered point is off-curve — it lies on the twist,
whose order is composite — and went straight into `cEmitMul`.

It now emits `valid = (x < p) AND (y² == x³ − 3x + b)`, ANDed into the verifier's
boolean result. A flag rather than an `OP_VERIFY`, for reason 3 above.

**Severity, honestly stated:** this is defence in depth, not a demonstrated
bypass. Every input that trips the guard also fails the final
`(R.x mod n) == r` comparison, and making that comparison succeed with an
attacker-chosen off-curve `Q` is equivalent to forging ECDSA. No pre-fix `true`
is constructible, which is why the regression test for it is a pin rather than a
red-then-green proof.

## Found on the way in: five off-chain mocks disagreed with the script

Adding `assert(!ecOnCurve(ecAdd(g, neg)))` to the `ec-unit` fixture made the
Python example test fail — and the reason was not the compiler. Five of the
seven **off-chain runtime mocks** special-cased the all-zero blob as
"point at infinity, therefore on the curve":

| tier | before | after |
|---|---|---|
| TS (`runar-lang`) | `false` ✓ | unchanged |
| Go (`runar-go`) | `false` ✓ | unchanged |
| Rust (`runar-rs`) | `true` ✗ | `false` |
| Python (`runar-py`) | `true` ✗ | `false` |
| Zig (`runar-zig`) | `true` ✗ | `false` |
| Ruby (`runar-rb`) | `true` ✗ | `false` |
| Java (`runar-java`) | `true` ✗ | `false` |

Projectively `O` *is* on the curve, so the convention is defensible in the
abstract — but `ecOnCurve` is defined here by what the emitted script does, and
the script computes `x < p AND y < p AND y² == x³ + 7`, which is `false` for
`(0, 0)`. The mock therefore answered the opposite of the chain.

Direction of harm: a contract author writes the documented guard
`assert(ecOnCurve(r))`, it passes in unit tests against the mock when `r = O`,
and the deployed script rejects — an unspendable output discovered only after
funding. `O` is reachable from `ecMul(P, 0n)`, and, as of this change, from
`ecAdd(P, −P)` as well, so this stopped being theoretical.

The Zig and Rust suites each carried a test asserting the wrong answer
(`ecOnCurve(identity)` / `ec_on_curve_accepts_identity`); both were inverted
with a comment explaining why.

## Where these are gated

| Property | Test |
|---|---|
| `ecAdd(P, −P)` = all-zero, script AND interpreter, 3 curves | `packages/runar-testing/src/__tests__/ec-degenerate-add.test.ts` |
| scalar domain (`k ≥ n`, `k < 0`, `k ≡ 0`), 3 curves | `packages/runar-testing/src/__tests__/ec-scalar-domain.test.ts` |
| `ec-mulgen-linear` ↔ scalar reduce dependency | same file, `ec-mulgen-linear depends on the scalar reduce` |
| coordinate canonicity, x half AND y half, 3 curves | `packages/runar-testing/src/__tests__/ec-on-curve-canonicity.test.ts` |
| `verifyECDSA_P256/P384` accept + decompression guards | `packages/runar-testing/src/__tests__/p256-p384-ecdsa-verify.test.ts` |
| all seven tiers, real Spend engine | `conformance/witnesses/real-crypto/{ec-unit,p256-primitives,p384-primitives}.json` |

## Correction to an earlier claim

An earlier comment in `ec-on-curve-canonicity.test.ts` said the **y** half of the
canonicity guard had "no constructible witness", on the grounds that a curve
point with `y < 2^(8·w) − p` is a `2^-32` / `2^-224` / `2^-256` event. That is
only true of *random search*. Fix `y` and the curve equation is a cubic in `x`,
whose roots come out of `gcd(X^p − X, f)` over `F_p` in milliseconds. A small-`y`
witness now exists for **all three curves** and is computed in the test rather
than assumed away.
