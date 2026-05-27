# GAP-008 — Bitcoin Script Analyzer port: follow-ups

These items were discovered while porting the analyzer from TS to six other
tiers. They do NOT block the GAP-008 work (the spec faithfully reproduces TS
reference behavior, including quirks, so the cross-tier goldens stay
byte-identical), but they SHOULD be addressed in dedicated follow-up issues.

## 1. `PATHS_TRUNCATED` message arithmetic — 32-bit shift overflow

**Location:** `packages/runar-testing/src/analyzer/path-analyzer.ts` line ~283:

```ts
const requestedCombinations = 1 << numBranches;
```

For `numBranches >= 32`, this produces nonsense values because JS bitwise
left-shift masks the shift count to 5 bits (`numBranches & 31`). The
PATHS_TRUNCATED message then claims e.g. `2^785 = 131072 paths`, which is
visibly wrong to any reader.

**Observed in:** `ec-demo` golden (`numBranches = 785`, "requested" = 131072).

**Suggested fix:** use a saturating computation:
```ts
const requestedCombinations = numBranches >= 53
  ? Number.MAX_SAFE_INTEGER
  : 2 ** numBranches;
```
and reword the message to e.g. `Script has 785 branch points (more than 2^53 paths); ...`. **Cross-tier:** if this fix lands, ALL 7 analyzer tiers must apply the same fix and the goldens must be regenerated in a single commit.

## 2. `MAX_PATHS = 256` may be too small

In the TS reference, the cap is 256. `ec-demo` enumerates exactly 256 of
its >> 2^53 spending paths — almost certainly hiding analysis-relevant
behavior. The conformance gate is byte-identical output, so this cap is
locked in by goldens; but the cap could reasonably be raised to e.g. 4096
once the goldens are regenerated. Stack-Overflow risk: each path's
description string grows with `numBranches`, so for `numBranches >= 32`
the per-path description is ~30 KB — bumping `MAX_PATHS` to 4096 would
inflate goldens roughly linearly.

## 3. `LARGE_SCRIPT` threshold (500_000 bytes)

The threshold is hardcoded and chosen for traditional Bitcoin. For BSV
(which Rúnar targets) scripts up to several MB are routinely deployed;
500 KB is no longer a meaningful red flag. Consider raising to e.g. 4 MB
or removing the finding entirely. (None of the 8 canonical fixtures
exercises this finding — `ec-demo` and `schnorr-zkp` are larger than
500 KB but the analyzer treats hex-string length as bytes, which is
off by a factor of 2 — see follow-up 4.)

## 4. `scriptSizeBytes` is computed as `normalizedHex.length / 2`

This is correct. However the path-description and many other fields use
the *opcode offset* in script bytes, while the `LARGE_SCRIPT` threshold
compares against the same `scriptSizeBytes`. The threshold of 500_000
bytes is in **script bytes** (not hex characters), so the comparison is
correct. Noting here only to flag that any future change to the threshold
semantics should be cross-tier-coordinated.

## 5. `sortFindings` second key is `offset ?? Infinity`

This is well-defined in JS but each tier needs to map `Infinity` to its
language's sort key. The spec explicitly states "offset-less findings
sort to the end within their severity bucket"; per-tier implementers
should use either:
- a large sentinel int (e.g. `Int.MAX`) AND check for it correctly,
- or a key-extractor that returns `Option<int>` with `None > Some(n)`.

Not a bug; just a pitfall called out so non-TS tiers don't all
reimplement it differently.

## 6. `UNREACHABLE_AFTER_RETURN` only fires in the linear-fallback path

The path-analyzer's per-path linear analysis also walks opcodes and
emits `UNREACHABLE_AFTER_RETURN`, but only for opcodes that appear
in the *per-path* collected list, after an `OP_RETURN`. None of the 8
fixtures have an `OP_RETURN` followed by more opcodes inside a single
branch, so this case is untested in the conformance goldens.

## 7. `CHECKSIG_RESULT_DROPPED` is intentionally scoped to direct OP_DROP

Other patterns like `OP_CHECKSIG OP_TOALTSTACK OP_DROP` or `OP_CHECKSIG
OP_NIP` are not flagged. This is a deliberate scope limit (low
false-positive rate) but worth documenting. None of the fixtures
exercise the finding.

## 8. Synthetic `RAW_SPAN` opcode (id = -1) unused by the 8 fixtures

`collapseRawScriptSpans` is fully implemented and tier-tested but none
of the 8 canonical fixtures pass `rawScriptSpans`. Tier ports must
still implement and unit-test the collapse algorithm, but cross-tier
byte parity for this feature is not verified by the conformance suite.
Worth adding a 9th tiny fixture that exercises raw_script (e.g.
`asm-raw-script`) once the 7th tier ports land.
