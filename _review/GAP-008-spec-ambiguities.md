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
