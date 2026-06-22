# canonicalJson — RFC 8785 / JCS Cross-Tier Parity

**Status:** canonicalJson is byte-identical across all 7 SDK tiers
(TS, Go, Rust, Python, Zig, Ruby, Java). Every previously-catalogued
cross-tier divergence (D1, D3, D4, D5, D6) is **RESOLVED in code**. The
single remaining open item (D2) is a framing refinement that is not
reachable on the v1 wire schema; see §3.

This document is the single source of truth for the cross-tier
canonicalJson parity story. It supersedes the divergence catalogues
previously inlined in `audits/phase13-prep.md` §2/§5/§8 and in the
`_notes` of `conformance/sdk-envelope/fixtures.json`.

`canonicalJson` is the RFC 8785 / JCS serializer used to hash payloads
before signing in the signed-envelope wire protocol. Two
implementations that produce different bytes for the same JSON value
silently break every cross-tier signature, so byte-identity is a hard
wire-protocol invariant (see `CLAUDE.md` — "Seven SDKs Must Stay in
Sync").

The TS reference is `packages/runar-ir-schema/src/canonical-json.ts`
(`canonicalJsonStringify`), re-exported as the SDK's wire `canonicalJson`
in `packages/runar-sdk/src/envelope.ts`.

---

## 1. Resolved divergences

Each divergence below was a real cross-tier byte mismatch in an earlier
revision. All are now fixed; the file:line of each fix is cited so the
claim is checkable.

### D1 — RESOLVED: Zig object-key sort was byte-wise, not UTF-16 code-unit

RFC 8785 sorts object keys by UTF-16 code-unit value (the ES default
`Array.prototype.sort()` order), **not** UTF-8 byte order. The two
orders disagree whenever an astral-plane (supplementary) character is
compared against a BMP character ≥ U+E000: under UTF-16 the astral key
sorts first (its high surrogate 0xD83D < 0xE000), under UTF-8 the BMP
key sorts first (0xF0… > 0xEE…).

Fix — Zig transcodes each key to UTF-16LE and sorts by code unit:
- `packages/runar-zig/src/sdk_envelope.zig:81-96` — keys transcoded via
  `std.unicode.utf8ToUtf16LeAlloc`, then sorted by `utf16Less`.
- `packages/runar-zig/src/sdk_envelope.zig:279-285` — `utf16Less`
  (code-unit lexicographic compare).

Peer tiers (all UTF-16 code-unit order):
- TS — `packages/runar-ir-schema/src/canonical-json.ts:234`
  (`Object.keys(obj).sort()`; ES default sort is UTF-16 code-unit order).
- Go — `packages/runar-go/sdk_envelope.go:101-102, 260-264`
  (`utf16Less` over `utf16.Encode`).
- Rust — `packages/runar-rs/src/sdk/envelope.rs:80-83`
  (`k.encode_utf16().collect()` as the sort key).
- Python — `packages/runar-py/runar/sdk/envelope.py:72-84`
  (`key=lambda k: k.encode("utf-16-be")`).
- Ruby — `packages/runar-rb/lib/runar/sdk/envelope.rb:72`
  (`sort_by { |k| k.encode('UTF-16BE').bytes }`).
- Java — `packages/runar-java/src/main/java/runar/lang/sdk/Envelope.java:96-97`
  (Java strings are UTF-16; default `String.compareTo` is code-unit order).

Gated by fixture vectors `v18-empty-key-vs-astral` and
`v18b-astral-vs-bmp-private-use` in
`conformance/sdk-envelope/fixtures.json`.

### D3 — RESOLVED: Zig emitted duplicate object keys instead of rejecting

RFC 8785 §3.2.3 requires that duplicate keys be rejected. Zig's
`Value.Object` is a slice of key/value pairs (it does not dedupe like a
map), so duplicates could previously be emitted verbatim.

Fix — `packages/runar-zig/src/sdk_envelope.zig:97-105`: after the
UTF-16 sort, an adjacency check compares each key's code-unit sequence
to its predecessor and returns `error.DuplicateObjectKey` on a match.

The other tiers receive their input as a native map/dict/object (TS
`object`, Go `map`, Rust `serde_json::Map`, Python `dict`, Ruby `Hash`,
Java `Map`) where duplicate string keys cannot coexist, so D3 is
structurally impossible for them. Regression-tested in Zig at
`packages/runar-zig/src/sdk_envelope.zig:666` ("canonicalJson rejects
duplicate object keys (audit D3)").

### D4 — RESOLVED: Ruby falsy-value rewrite

Ruby's old `value[k] || value[k.to_sym]` lookup silently rewrote any
falsy value (`false`, `0`) by falling through to the symbol key (or
`nil`). Fixed by replacing the `||` fallthrough with an explicit
`key?` presence check in `packages/runar-rb/lib/runar/sdk/envelope.rb`.
Gated by fixture vector `v19-boolean-false-preserved`. (D4 was already
recorded as fixed in prior docs; listed here for completeness.)

### D5 — RESOLVED: cross-tier float formatter divergence

Floats must serialize per ECMA-262 §6.1.6.1.13 (`Number::toString`),
which JS `JSON.stringify` produces natively. The non-TS tiers' stdlib
formatters diverged: e.g. `1e21` rendered as `1.0e+21` (Ruby), `1.0E21`
(Java), or `{e}`-format (Zig), and `1e-300` carried a spurious `.0`.

Fix — every non-TS tier now has a dedicated `*Ecma262Double` formatter
that re-derives the shortest digit string and decimal exponent and
re-emits per the spec rules:
- TS — native (`JSON.stringify` / `String(x)` is the reference).
- Go — `packages/runar-go/sdk_envelope.go:162` (`appendEcma262Double`).
- Rust — `packages/runar-rs/src/sdk/envelope.rs:117`
  (`format_ecma262_double`).
- Python — `packages/runar-py/runar/sdk/envelope.py:47-58`
  (`_canonical_append` float branch; `repr()` shortest-roundtrip with
  integer-valued fast path).
- Zig — `packages/runar-zig/src/sdk_envelope.zig:174`
  (`appendEcma262Double`).
- Ruby — `packages/runar-rb/lib/runar/sdk/envelope.rb:155`
  (`format_ecma262_double`).
- Java — `packages/runar-java/src/main/java/runar/lang/sdk/Envelope.java:165`
  (`formatEcma262Double`).

All seven now emit `1e+21` and `1e-300`. Gated by fixture vectors
`v20-float-1e21-scientific` (`1e+21`) and
`v21-float-1e-300-no-trailing-dotzero` (`1e-300`).

### D6 — RESOLVED: lone-surrogate input is rejected everywhere

A lone surrogate (e.g. U+D800 with no low-surrogate partner) is invalid
Unicode per RFC 8785 §3.2.2.2 and must be rejected — not silently
emitted, U+FFFD-replaced, or passed through.

Fix — every tier rejects:
- TS — `packages/runar-ir-schema/src/canonical-json.ts:177-190`
  (walks UTF-16 code units; throws a `lone-surrogate` `CanonicalJsonError`
  for an unpaired high or low surrogate).
- Go — `packages/runar-go/sdk_envelope.go:281-303` (walks bytes; rejects
  the WTF-8 3-byte surrogate pattern `0xED, 0xA0..0xBF, 0x80..0xBF`
  before Go's UTF-8 decoder can fold it to U+FFFD).
- Python — `packages/runar-py/runar/sdk/envelope.py:104-110` (rejects
  code points in 0xD800..0xDFFF).
- Zig — `packages/runar-zig/src/sdk_envelope.zig:159-161` (returns
  `error.LoneSurrogate` for the 3-byte surrogate UTF-8 form).
- Ruby — `packages/runar-rb/lib/runar/sdk/envelope.rb:124-130` (raises
  for code points in U+D800..U+DFFF).
- Java — `packages/runar-java/src/main/java/runar/lang/sdk/Envelope.java:118-137`
  (`Character.isHighSurrogate`/`isLowSurrogate` pairing check).
- Rust — a lone surrogate is **unrepresentable** in Rust's `&str`/`String`
  (which are guaranteed well-formed UTF-8), so the divergence is rejected
  at the type-system boundary before canonicalJson runs.

Gated by fixture rejection vector `v22-lone-surrogate-rejected` and the
Go interop test
`packages/runar-go/sdk_envelope_interop_test.go`
(`TestEnvelopeInterop_CanonicalJSONRejectionVectors`), which feeds the
fixture's `input_value_utf16_units` to each tier's canonicalJson and
asserts rejection.

---

## 2. Open item (not reachable on the v1 wire schema)

### D2 — Zig string-escape walks bytes, not codepoints

`appendJsonString` in `packages/runar-zig/src/sdk_envelope.zig:118-166`
escapes strings on a byte walk. It now validates UTF-8 well-formedness
and rejects the surrogate range (so it is no longer the lone-surrogate
vector — that is covered under D6), but the broader codepoint-oriented
escape framing is tracked separately. This is **not** a present
cross-tier byte divergence on any input the v1 wire schema can carry
(§3), so it is not v1-blocking.

---

## 3. v1 wire-schema restriction (why the divergences are also latent)

Independently of the code fixes above, the divergence *triggers* cannot
arise on the v1 signed-envelope wire schema. The envelope payload keys
in production today are `kind`, `n`, `nonce`, `expiresAt` (see
`conformance/sdk-envelope/fixtures.json` → `valid_envelope`), and the
wire restriction is:

- **Keys:** ASCII only ⇒ UTF-16 vs UTF-8 sort order coincide (D1 cannot
  fire); no duplicate keys cross the wire (D3 cannot fire).
- **Values:** integers, booleans, and ASCII strings only ⇒ no
  floating-point values (D5 cannot fire) and no non-ASCII / surrogate
  code points (D6 / D2 cannot fire).

So the divergences are doubly closed: **fixed in code** (§1) *and*
**latent** on the v1 schema. The code fixes mean they would remain
byte-identical even if the schema later admitted non-ASCII keys,
floats, or full-Unicode string values.

---

## 4. Remaining hardening (tracked separately)

- **Property-based / differential fuzzing of canonicalJson across all 7
  tiers** — randomized JSON values (including astral keys, float edge
  cases, and surrogate inputs) round-tripped for byte-identity / matched
  rejection. Tracked as a separate v1-readiness item (GAP-002 fuzzer);
  the curated fixture vectors v18–v22 + the signing vectors are the
  current regression gate in the interim.
- **D2 codepoint-escape framing** in Zig `appendJsonString` (§2).
