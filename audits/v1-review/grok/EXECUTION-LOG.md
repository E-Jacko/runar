# Execution log (deep pass)

Commands run on monorepo at HEAD `52de4384` (same as worktree).

## NestedAdopt #149 (real Spend via MockProvider)

File: `audits/v1-review/grok/_probe_nested_adopt.test.ts` (audit-only; not product source)

```
npx vitest run audits/v1-review/grok/_probe_nested_adopt.test.ts
```

| Case | fold-OFF | fold-ON |
|---|---|---|
| inner then `go(3,1,1)` expect p=55 | **PASS** | **PASS** |
| inner else `go(3,1,0)` expect p=65 | **FAIL** — Spend rejects: "top stack element must be truthy after script evaluation" PC:710 | **FAIL** same |
| outer skip `go(3,0,0)` expect p=15 | **PASS** | **PASS** |

Result: **2 failed | 4 passed**. Open S0 confirmed by execution, not only docs.

Side observation: successful paths log `Failed to fetch transaction after broadcast: MockProvider: transaction … not found` — `broadcast()` never inserts into `this.transactions` used by `getTransaction()`.

## Nested loop regression (control: fix still live)

```
npx vitest run packages/runar-testing/src/__tests__/nested-loop-carried-local-vm.test.ts -t "N22: 2x2"
```

**PASS** — plan §9.1 item 6 ("nested loops open") is **stale**; fix is in tree (`flattenNestedLoopBodies`).

## Skip audit

```
python3 scripts/audit-test-skips.py
```
OK — 134 sites / 66 rows.

## Not run

Lean/lake, full fuzzer, full 7-tier matrix, differential.sh --strict.
