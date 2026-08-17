# Rúnar v1 audit — Claude Code — STATE (session 2 final)

Worktree: /Users/siggioskarsson/gitcheckout/runar-claude (detached @ **52de4384**)
Session 1 (2026-08-10) audited a17037d6 -> CC-001..CC-012. Session 2 (2026-08-16)
audited 52de4384 -> CC-013..CC-016. `git diff --stat a17037d6 52de4384` touches
only `runar-verification/**`, so session-1 findings were still on-HEAD; each was
re-verified rather than re-derived. `fix/v1-audit-remediation` is NOT merged.

## Phase: COMPLETE — deliverables written

- `findings.jsonl` — **16** findings: 3x S0, 1x S1, 1x S2, 11x S3 (all valid JSON)
- `REPORT.md` — session 2 first, then session 1 verbatim; H1-H5 verdicts,
  S0/S1 ordered by fix cost, unsoftened "could not verify" for both sessions
- `repro/` — CC-013 generator patch + repro contract + finding.json, the four
  mutation harnesses (mut-gen/mut-gate/mut-run/mut-go/mut-escalate), result JSON
- `logs/` — 00..70 (session 1), 80..A0 (session 2); raw output for every claim

## Session-2 obligations: all five closed except as noted
| session-1 gap | outcome |
|---|---|
| `lake build` / real Lean checking | **DONE** — exit 0, 64 jobs, zero `sorry`; TCB gate: axioms=71 exactly |
| `integration:all:run` (Docker) | **DONE** — exit 0, all **7** tiers passed on a real regtest node |
| `--spend-oracle` never run | **DONE** — produced CC-013 + the CC-014 S0 |
| mutation >=200 mutants | **DONE** — TS 621, Go 246. Rust/Zig/Ruby/Python/Java: still zero |
| 7-tier `--anf` / `--ir --stateful` at scale | **NOT DONE** — still open |

## Results
- **CC-014 (S0, new)** stateful `addOutput` + branch-merged local + live untouched
  sibling + outer `if` with no else -> `interp=true, spend=false`, funds locked.
  `OP_NUM2BIN` crossed-operand signature at PC 605. 4/4 fresh seeds.
- **CC-013 (S3, new)** spend-oracle: stock **0 failures / 11,750 spend inputs**;
  needs TWO degrees of freedom (sibling local AND outer-if-without-else). Sibling
  alone = 0 failures / 8,830 inputs — this CORRECTS session 1's inferred claim.
- **CC-015 (S3, new)** TS mutation 578 scored (37 vacuous fold mutants excluded),
  183 survive (68.3%); 25/25 escalated survivors caught by NO gate.
- **CC-016 (S3, new)** `05-stack-lower.ts:2212-2218` terminal-assert cleanup path
  executes **0 times** across all 71 fixtures — verified by instrumentation.
- Session-1 CC-001/002/003/005/007/009/010/011 all re-verified STILL OPEN.
  CC-002 is broader than recorded (4 bypass args under the deployed fold-ON default).
- Go mutation: 246/246 caught (100%), genuine `hex-diff`. TS restricted to the same
  ops+regions: 56.6%, with 55 of 109 survivors inside `lowerIf`. Interpretation is
  flagged INFERRED in REPORT.md; no tier-quality conclusion drawn.

## Two harness bugs of my own, found and corrected (documented in REPORT.md)
1. Go copy at `$ROOT/.mut-go-wN` escapes `go.work` -> every mutant `build-fail` ->
   fake 100%. Tell: a perfect score right after TS scored ~36% survival.
   Fixed to in-place serial + pristine restore.
2. TS gate runs fold-OFF, so `constant-fold.ts` mutants never execute -> fake
   37/37 survival. Excluded from the score.

## Tree state
`git status --porcelain` -> `?? audits/v1-review/` **only**. Generator patch
reverted (original at `repro/spend-shapes.ts.orig`), all mutation workers removed,
`compilers/go` and `packages/runar-compiler/src` restored, instrumentation probe
deleted. Nothing committed.

## If resuming
Highest-value remaining, in order: (1) 7-tier `--anf` / `--ir --stateful` at scale;
(2) full `pnpm run lean:verify` (per-module build + goldenLoad/roundtrip/pipelineGolden);
(3) Rust mutation + re-run TS/Go under one identical operator set and sampling
strategy; (4) equivalent-mutant triage of the 183 TS survivors; (5) the gate
perturbations neither session did (fold-ON allowlist, script-size-baseline,
decompiler fingerprints/templates, sdk-envelope, sdk-bip143).
