# GAP-008 spec ambiguities filed by Rust porter

Filed against `spec/script-analyzer-format.md` v1.0 (2026-05-27) during
the Rust port of the analyzer. Goldens at
`conformance/analyzer/*/expected-analyzer-report.json` are taken as the
ground truth where they conflict with the spec text.

## max-stack-depth-seed-zero (§8.3 — Summary)

Spec §8.3 reads:

> `maxStackDepth = max(p.stackDepthAtEnd over all paths, defaulting to 0 if no paths)`
> [...]
> Note this means `maxStackDepth` can be negative when all paths end with
> a depth below zero (consumer of unlocking-script items).

The canonical goldens disagree. Every fixture whose paths' `stackDepthAtEnd`
values are all negative reports `maxStackDepth: 0`, not the (negative)
max-over-paths value:

| fixture            | per-path stackDepthAtEnd      | maxStackDepth in golden |
|--------------------|-------------------------------|-------------------------|
| basic-p2pkh        | [-1]                          | 0                       |
| escrow             | [-1, -1]                      | 0                       |
| covenant-vault     | [-2]                          | 0                       |
| stateful-counter   | [-2, -2, -4, -3, ..., all<0]  | 0                       |
| if-else            | [0, 0]                        | 0                       |

The observable rule (and the one the Rust port implements) is therefore:

```
maxStackDepth = max(0, max_over_paths(stackDepthAtEnd))
```

i.e. the reducer seeds with `0`, so a negative max-over-paths is clamped
to `0`. This matches Schnorr-ZKP (`maxStackDepth: 1023`) and the empty
case (`0` when no paths).

Recommendation: clarify §8.3 to match the goldens — either replace the
"can be negative" note with the seed-0 rule, or regenerate the goldens
to drop the seed. The 6 in-flight ports must agree, so the Rust port
matches the goldens.

## right-shift-mask-on-bit-extraction (§7.2 — choices vector build)

Spec §7.2 reads:

> The choices array for path index `combo` (0..N-1) is built as:
> ```
> for b in [0 .. numBranches):
>   choices[b] = ((combo >> b) & 1) == 1
> ```

In Rust (and most non-JS languages), shifting a 32-bit integer by `b >= 32`
is either UB (Rust integer overflow check) or yields `0` after a saturating
clamp. In JS, however, `combo >> b` masks `b` to 5 bits — so `combo >> 32`
equals `combo >> 0`, and the bit pattern recurs every 32 positions.

The §5.1 paragraph already calls out the JS-shift quirk for *left* shifts
on `1 << numBranches`. The same quirk applies to the *right* shift in the
choices loop. The schnorr-zkp golden makes this concrete: with
numBranches = 514, combo = 1, the trues land at b ∈ {0, 32, 64, ..., 512}
(17 entries). A direct port that gives `0` for `combo >> 32` produces only
1 true (at b = 0) and the description / branchChoices diverge.

The Rust port implements:

```rust
let shift = (b as u32) & 31;
let bit = (combo >> shift) & 1;
choices.push(bit == 1);
```

Recommendation: add an explicit note to §7.2 mirroring the §5.1 note —
"replicate JS 32-bit right-shift semantics: `choices[b] = ((combo >> (b & 31)) & 1) == 1`".
