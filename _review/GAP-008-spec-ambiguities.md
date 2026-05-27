# GAP-008 spec ambiguities (Go port)

## maxStackDepth seed value

Spec §8.3 says:

```
maxStackDepth = max(p.stackDepthAtEnd over all paths, defaulting to 0
                    if no paths)
```

And note: "If `paths` is empty, `maxStackDepth = 0`. Note this means
`maxStackDepth` can be negative when all paths end with a depth below
zero".

But the 8 canonical goldens contradict this:

- `basic-p2pkh`: single path, `stackDepthAtEnd: -1`, `maxStackDepth: 0`.
- `covenant-vault`: single path, `stackDepthAtEnd: -2`, `maxStackDepth: 0`.
- `stateful-counter`: paths range -2..-4, `maxStackDepth: 0`.
- `auction`, `escrow`, `if-else`: same pattern.

These all match `max(0, max(stackDepthAtEnd over paths))` —
i.e. the reduction is **seeded with 0** rather than allowed to go
negative. (TS idiom: `paths.reduce((m,p) => Math.max(m, p.stackDepthAtEnd), 0)`.)

The reference example in §3.6 shows `stackDepthAtEnd: -2` /
`maxStackDepth: -2` which is incompatible with the actual goldens.

**Resolution chosen:** match the goldens — seed the max with 0. The
note in §14 about "negative depths" still applies to per-path
`stackDepthAtEnd`. The Go port emits `max(0, max-over-paths)`.

## choices vector consumption during traversal

Spec §7.4: "at each IF/NOTIF (in source order), take the next decision".

This wording suggested to me that the choices vector is consumed by
source-order position (i.e. when an outer IF is false and its body is
skipped, the choices for the nested IFs in that body would still be
"used up" before we move on to IFs in the ELSE body). I implemented
that first.

The canonical goldens (stateful-counter id=2 in particular) contradict
this. The actual semantics:

- The `description` is built **mechanically from the full choices
  vector in source order** (so `IF[true] at 115` may appear in the
  description even if IF#115 is in a skipped body and was never
  dynamically encountered).
- The **execution traversal consumes choices in dynamic-encounter
  order**: skipped bodies do not advance `choiceIdx`. So `choices[1]`
  is consumed at *whichever* IF/NOTIF the linear walk hits second,
  regardless of which IF that is in source order.

This is internally inconsistent (the description and the execution
disagree on which choice belongs to which IF) but it's what the
reference produces and what the goldens encode.

**Resolution chosen:** match the goldens — keep description
source-order-mechanical, but advance `choiceIdx` only on dynamically
encountered IFs.

## PATHS_TRUNCATED finding emission order

Spec §11.1 says ties within the same (severity, offset) bucket are
broken by "the order they were appended in §11's orchestration:
pathFindings (in appearance order: structural, then per-path, then
branch-depth) → ...". This suggested PATHS_TRUNCATED (which is a
per-path-enumeration finding) might come after per-path findings.

The ec-demo golden has PATHS_TRUNCATED ordered **before** all per-path
UNCONDITIONALLY_SUCCEEDS / NO_SIG_CHECK findings (all share severity
warning + no offset).

**Resolution chosen:** treat PATHS_TRUNCATED as a structural finding
emitted at enumeration time, before any per-path finding is appended.

## Stale or unused TS-reference fields

Spec §7.2 mentions `reachable: true` is always true in the current
version and "reserved for future dead-branch detection". Implemented as
hardcoded `true` per spec.
---

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
