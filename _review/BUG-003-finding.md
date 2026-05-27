# BUG-003 finding — multisig-2of3 contract is structurally insecure across all 7 tiers

## TL;DR

The compiled locking script emitted for `MultiSig2of3` does **not** verify
signatures at all. **Any input is accepted, including all-empty signatures and
all-garbage bytes.** The bug is in the Rúnar compiler's stack-lowering for
`array_literal` / `checkMultiSig`, not in any one frontend, so it is identical
across all 7 compiler tiers (the conformance fixture
`conformance/tests/multisig/expected-script.hex` enshrines the broken layout).

I am stopping per the task instructions (real ordering bug discovered) and not
adding the 9 adversarial test ports until the bug is triaged.

## Worktree / branch

- worktree: `/Users/siggioskarsson/gitcheckout/runar/.claude/worktrees/agent-a51157ccc878a8b30`
- branch: `worktree-agent-a51157ccc878a8b30` (based on `origin/main` @ `6218ecf4`)

## Evidence — what the locking script actually does

Compile the TS reference contract with constructor args
`pk1=02aa..aa, pk2=02bb..bb, pk3=02cc..cc`. The resulting `scriptAsm` is:

```
<02aa..aa> <02bb..bb> <02cc..cc> OP_ROT OP_ROT OP_ROT OP_0 OP_ROT OP_2 OP_3 OP_ROLL OP_3 OP_CHECKMULTISIG
```

Step the script through `ScriptVM` (`packages/runar-testing/src/vm/script-vm.ts`)
with an unlocking script `<sig1> <sig2>` and a `checkSigCallback` that returns
`false` for everything. The trace, just before `OP_CHECKMULTISIG`:

```
step 13: OP_3   stack (bot→top) =
  [ sig1, sig2, pk1, '' (empty), pk2, 0x02, pk3, 0x03 ]
step 14: OP_CHECKMULTISIG   stack = [ sig1, sig2, 0x01 ]
```

`OP_CHECKMULTISIG` pops top-down per BSV interpreter semantics
(`packages/runar-testing/src/vm/script-vm.ts:1427`):

1. pop `0x03` → **nKeys = 3**
2. pop 3 pubkeys: `pk3, 0x02, pk2`
3. pop `''` (empty bytes) → **nSigs = 0** ← the number `2` is not in this slot!
4. pop **0** sigs (loop body skipped)
5. pop dummy: `pk1`
6. signature loop is vacuously valid → push `OP_TRUE` (`0x01`)

The verify loop runs **zero times**. `checkSigCallback` is never invoked
(I confirmed this with a callback that logs on every call — no log lines).
The original `sig1, sig2` from the unlocking script are still sitting at the
bottom of the stack untouched. The script terminates with `0x01` on top → success.

### Attack: garbage and empty sigs both pass

```ts
// always-false checkSigCallback, unlocking = <0xdeadad..> <0xdeadad..>
vm.executeHex(unlocking + scriptHex).success === true   // ← should be false

// always-false checkSigCallback, unlocking = OP_0 OP_0  (two empty sigs)
vm2.executeHex(unlocking + scriptHex).success === true  // ← should be false
```

Both assertions hold today. The contract is structurally `OP_TRUE`.

## Root cause

`packages/runar-compiler/src/passes/05-stack-lower.ts:1628-1672`
(`lowerCheckMultiSig`) treats each *array-literal binding* (`sigsRef`,
`pksRef`) as a **single** stack slot when calling `bringToTop`, but the
array-literal lowering (`lowerArrayLiteral`,
`packages/runar-compiler/src/passes/05-stack-lower.ts:1594-1616`) physically
leaves **N elements** on the stack and only records the count in
`arrayLengths`. The stack-map abstraction is one-slot-wide but the runtime
layout is N-slots-wide. Result:

- The `OP_0` dummy is pushed *between* the sigs array and the pubkeys array
  instead of *below* the sigs array.
- The `nSigs` count is pushed at the wrong depth.
- The whole layout collapses into the trace above where pubkeys and counts
  interleave with phantom empty slots, and `OP_CHECKMULTISIG` reads
  `nSigs = empty-bytes-as-number = 0`.

The peephole optimizer (`packages/runar-compiler/src/optimizer/peephole.ts`)
does not rescue this.

## Cross-tier scope

The checked-in conformance hex
`conformance/tests/multisig/expected-script.hex` is byte-identical to what
the TS compiler emits today (`...00 7b 52 53 7a 53 ae` tail). Per project
policy and `conformance/runner/runner.ts`, every tier (Go, Rust, Python,
Zig, Ruby, Java) must produce this exact hex; therefore **every tier
inherits the same broken script**. The bug is in the shared lowering
algorithm, not in any one frontend.

The `examples/{move,sol}/multisig-2of3/` contracts also lower through the
same TS compiler stack-lowering, so they are equally vulnerable.

## Why the existing tests don't catch this

- `examples/ts/multisig-2of3/MultiSig2of3.test.ts` only asserts
  `typeof result.success === 'boolean'` — a tautology — and the TS
  interpreter (`packages/runar-testing/src/interpreter/interpreter.ts:712`)
  hard-codes `checkMultiSig → false` *and* throws on `array_literal`
  evaluation (`interpreter.ts:431`), so the interpreter path never actually
  exercises the codegen.
- The conformance suite checks hex/IR byte-equality, not script semantics.
- No tier runs the locking script through its `ScriptVM` against
  ECDSA-real or callback-mocked signatures.

So the bug has been latent.

## Recommended fix (not in scope for this task)

`lowerCheckMultiSig` must consume the **N physical elements** named by the
sigs and pubkeys array-literal bindings, in correct interleaved order, so
the final stack layout (top → bottom) is:

```
nPKs, pk_n, …, pk_1, nSigs, sig_m, …, sig_1, OP_0(dummy)
```

Concretely: instead of `bringToTop(sigsRef, …)`, the lowering needs an
N-wide variant that handles array bindings, or `lowerArrayLiteral` needs to
register the *bottom-of-array* depth so `lowerCheckMultiSig` can splice
counts and the dummy at the right places. The conformance golden hex must
be regenerated and all 7 tiers re-verified.

After the fix, the 9 adversarial test ports (the original BUG-003 ask)
should be added — they will then actually exercise meaningful semantics.

## Files cited

- `/Users/siggioskarsson/gitcheckout/runar/.claude/worktrees/agent-a51157ccc878a8b30/examples/ts/multisig-2of3/MultiSig2of3.runar.ts`
- `/Users/siggioskarsson/gitcheckout/runar/.claude/worktrees/agent-a51157ccc878a8b30/examples/ts/multisig-2of3/MultiSig2of3.test.ts`
- `/Users/siggioskarsson/gitcheckout/runar/.claude/worktrees/agent-a51157ccc878a8b30/packages/runar-compiler/src/passes/05-stack-lower.ts` — `lowerCheckMultiSig` (line 1628), `lowerArrayLiteral` (line 1594), `bringToTop` (line 828)
- `/Users/siggioskarsson/gitcheckout/runar/.claude/worktrees/agent-a51157ccc878a8b30/packages/runar-testing/src/vm/script-vm.ts` — `executeCheckMultiSig` (line 1427)
- `/Users/siggioskarsson/gitcheckout/runar/.claude/worktrees/agent-a51157ccc878a8b30/packages/runar-testing/src/interpreter/interpreter.ts` — interpreter `checkMultiSig` stub (line 712)
- `/Users/siggioskarsson/gitcheckout/runar/.claude/worktrees/agent-a51157ccc878a8b30/conformance/tests/multisig/expected-script.hex` — cross-tier golden enshrining the broken layout
