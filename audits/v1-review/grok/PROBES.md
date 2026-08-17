# PROBES — construct combinations not named by fixture inventory

Each probe is a small Rúnar contract (TS surface). Run through: all 7 compiler tiers
(hex + Stack IR), fold-OFF and fold-ON, ANF interpreter, ScriptVM/Spend where applicable,
and `--spend-oracle` style independent post-state when stateful.

**Convention:** `Expected disagreement` = where I expect tiers or oracles to diverge,
or script to disagree with source. `Pass blamed` = pipeline stage most likely responsible.

Fixtures already cover many single constructs; risk is **unnamed combinations**.

---

## P01 — Nested declared-results with live sibling (#149 reduction)

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P01 extends StatefulSmartContract {
  p: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.p = seed; }
  public go(x: bigint, c1: bigint, c2: bigint) {
    let a: bigint = 1n;
    let y: bigint = x + 2n;
    if (c1 > 0n) {
      if (c2 > 0n) { a = 5n; } else { a = 6n; }
    }
    assert(a + y > 0n);
    this.p = a * 10n + y;
  }
}
// Call: go(3,1,0) expect p=65; go(3,1,1) expect p=55; go(3,0,0) expect p=15
```

| Field | Value |
|---|---|
| Tiers expected to disagree | none — all may agree on **wrong** (shared design) |
| Predicted failure | Spend reject or wrong `p` on `go(3,1,0)` |
| Pass | `05-stack-lower` `lowerIf` adopt/reconcile |
| Oracle | real Spend + independent expectedState |

---

## P02 — Triple nest, only middle merges

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P02 extends StatefulSmartContract {
  p: bigint = 0n;
  constructor(s: bigint) { super(s); this.p = s; }
  public go(a: bigint, b: bigint, c: bigint) {
    let x: bigint = 1n;
    let y: bigint = 2n;
    let z: bigint = 3n;
    if (a > 0n) {
      if (b > 0n) {
        if (c > 0n) { x = 9n; } else { y = 8n; }
      } else { z = 7n; }
    }
    assert(x + y + z > 0n);
    this.p = x * 100n + y * 10n + z;
  }
}
```

| Tiers / prediction | all tiers same wrong layout possible |
| Pass | stack-lower multi-level reconcile |
| Expected | wrong `p` or unspendable on some path triples |

---

## P03 — Asymmetric rebind + property update in one arm only

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P03 extends StatefulSmartContract {
  a: bigint = 0n; b: bigint = 0n;
  constructor(a: bigint, b: bigint) { super(a, b); this.a = a; this.b = b; }
  public step(flag: bigint) {
    let x: bigint = this.a;
    let y: bigint = this.b;
    if (flag > 0n) { x = x + 1n; this.a = x; } else { y = y + 1n; }
    assert(x + y > 0n);
    this.b = y;
  }
}
```

| Pass | 04-anf-lower merge + update_prop in arm |
| Risk | stale `a` or `b` in continuation |

---

## P04 — if merges 2 locals AND addRawOutput in then only

```typescript
import { StatefulSmartContract, assert, toByteString } from 'runar-lang';
export class P04 extends StatefulSmartContract {
  a: bigint = 0n; b: bigint = 0n;
  constructor(a: bigint, b: bigint) { super(a, b); this.a = a; this.b = b; }
  public go(flag: bigint, sats: bigint) {
    let x: bigint = this.a; let y: bigint = this.b;
    if (flag > 0n) {
      x = x + 1n; y = y + 2n;
      this.addRawOutput(sats, toByteString('76a914') /* probe: use valid short script in harness */);
    } else { x = x + 3n; }
    this.a = x; this.b = y;
  }
}
```

| Pass | anf-lower: outputs + multi-merge interaction (may hard-fail compile — pin diagnostic) |
| Risk | if compile succeeds, unspendable or wrong state |

---

## P05 — Early return inside then with live outer local

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P05 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f(flag: bigint): bigint {
    let acc: bigint = this.n;
    if (flag > 0n) {
      acc = acc + 1n;
      return acc;
    }
    acc = acc + 2n;
    return acc;
  }
}
```

| Pass | 04-anf-lower return + 05 cleanup counts |
| Risk | wrong return / stack residue; tiers differ on cleanup |

---

## P06 — Early return after multi-local merge

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P06 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f(flag: bigint): bigint {
    let a: bigint = 1n; let b: bigint = 2n;
    if (flag > 0n) { a = 3n; b = 4n; } else { a = 5n; }
    return a + b;
  }
}
```

| Pass | merge results + return materialization (`@ref:`) |
| Risk | return loads pre-merge binding |

---

## P07 — Loop then merge locals (order inverted vs fixtures)

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P07 extends StatefulSmartContract {
  a: bigint = 0n; b: bigint = 0n;
  constructor(a: bigint, b: bigint) { super(a, b); this.a = a; this.b = b; }
  public go(flag: bigint) {
    let x: bigint = this.a; let y: bigint = this.b;
    for (let i: bigint = 0n; i < 3n; i++) { x = x + 1n; }
    if (flag > 0n) { y = y + x; } else { y = y - 1n; }
    this.a = x; this.b = y;
  }
}
```

| Pass | loop lower + subsequent lowerIf |
| Risk | loop-carried slot map wrong at join |

---

## P08 — Nested loop, outer local read after inner rebind

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P08 extends StatefulSmartContract {
  s: bigint = 0n;
  constructor(s: bigint) { super(s); this.s = s; }
  public go() {
    let outer: bigint = this.s;
    let acc: bigint = 0n;
    for (let i: bigint = 0n; i < 2n; i++) {
      for (let j: bigint = 0n; j < 2n; j++) {
        acc = acc + outer;
        outer = outer + 1n;
      }
    }
    this.s = acc + outer;
  }
}
```

| Pass | loop outer-ref liveness (Lean multi-result work adjacent) |
| Risk | stale outer |

---

## P09 — Four mutable fields, conditional write to subset

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P09 extends StatefulSmartContract {
  a: bigint = 0n; b: bigint = 0n; c: bigint = 0n; d: bigint = 0n;
  constructor(a: bigint, b: bigint, c: bigint, d: bigint) {
    super(a, b, c, d); this.a = a; this.b = b; this.c = c; this.d = d;
  }
  public go(flag: bigint) {
    if (flag > 0n) { this.a = this.a + 1n; this.c = this.c + 1n; }
    else { this.b = this.b + 1n; }
    assert(this.a + this.b + this.c + this.d >= 0n);
  }
}
```

| Pass | state continuation framing / field order |
| Risk | wrong fields in OP_RETURN state section |

---

## P10 — 1-byte OP_N ByteString state + branch merge locals

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P10 extends StatefulSmartContract {
  tag: bytes = b''; // harness: ByteString 0x05
  n: bigint = 0n;
  constructor(tag: bytes, n: bigint) { super(tag, n); this.tag = tag; this.n = n; }
  public go(flag: bigint) {
    let x: bigint = this.n; let y: bigint = 1n;
    if (flag > 0n) { x = x + 1n; y = 2n; } else { y = 3n; }
    this.n = x + y;
  }
}
```

| Pass | SDK state wire + compiler multi-merge (Palmer-1×Palmer-2) |
| Risk | framing or merge alone green; combination fails |

---

## P11 — Empty ByteString state after conditional

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P11 extends StatefulSmartContract {
  blob: bytes = b'';
  constructor(blob: bytes) { super(blob); this.blob = blob; }
  public go(flag: bigint) {
    if (flag > 0n) { this.blob = b''; } // empty
    assert(true);
  }
}
```

| Pass | state codec empty push |
| Risk | length misread |

---

## P12 — Negative bigint state edges through merge

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P12 extends StatefulSmartContract {
  v: bigint = 0n;
  constructor(v: bigint) { super(v); this.v = v; }
  public go(flag: bigint) {
    let x: bigint = this.v;
    if (flag > 0n) { x = -1n; } else { x = -256n; }
    this.v = x;
  }
}
// Deploy with v=-128; call both flags
```

| Pass | scriptnum encoding + merge |
| Risk | non-minimal / sign byte |

---

## P13 — OP_SPLIT at 0 and at len (via slice builtins if exposed)

```typescript
import { SmartContract, assert, slice, len } from 'runar-lang';
export class P13 extends SmartContract {
  readonly bs: bytes;
  constructor(bs: bytes) { super(bs); this.bs = bs; }
  public f(at: bigint) {
    // Adjust names to actual Rúnar byte APIs available in lang
    const left = slice(this.bs, 0n, at);
    const right = slice(this.bs, at, len(this.bs));
    assert(len(left) + len(right) === len(this.bs));
  }
}
// at=0, at=len, at=middle
```

| Pass | byte ops codegen |
| Risk | empty half / off-by-one; pre-Genesis refs refuse |

---

## P14 — num2bin undersized destination

```typescript
import { SmartContract, assert, num2bin } from 'runar-lang';
export class P14 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f() {
    // size too small for n — must fail assert path or reject compile
    const b = num2bin(this.n, 1n);
    assert(len(b) === 1n);
  }
}
```

| Pass | math_byte / OP_NUM2BIN |
| Risk | soft accept with truncated value |

---

## P15 — bin2num of non-minimal encoding (if injectable)

```typescript
import { SmartContract, assert, bin2num } from 'runar-lang';
export class P15 extends SmartContract {
  readonly bs: bytes;
  constructor(bs: bytes) { super(bs); this.bs = bs; }
  public f() {
    const n = bin2num(this.bs);
    assert(n === 1n);
  }
}
// constructor: non-minimal 0x0100... vs minimal 0x01
```

| Pass | OP_BIN2NUM + MINIMALDATA interaction |
| Risk | accept non-minimal or reject valid |

---

## P16 — Division / mod with negative operands

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P16 extends SmartContract {
  readonly a: bigint; readonly b: bigint;
  constructor(a: bigint, b: bigint) { super(a, b); this.a = a; this.b = b; }
  public f() {
    assert((this.a / this.b) === -3n); // pick operands per Script rules
    assert((this.a % this.b) === -1n);
  }
}
```

| Pass | bin_op lowering vs Script div semantics |
| Risk | host fold vs Script sign of remainder |

---

## P17 — safediv / safemod zero divisor

```typescript
import { SmartContract, assert, safediv, safemod } from 'runar-lang';
export class P17 extends SmartContract {
  readonly a: bigint;
  constructor(a: bigint) { super(a); this.a = a; }
  public f() {
    assert(safediv(this.a, 0n) === 0n);
    assert(safemod(this.a, 0n) === 0n);
  }
}
```

| Pass | builtin codegen |
| Risk | abort vs defined zero |

---

## P18 — Shift amount ≥ width

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P18 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f() {
    assert((this.n << 64n) === 0n || true); // pin Script LSHIFT behavior
    assert((1n << 31n) > 0n);
  }
}
```

| Pass | OP_LSHIFT |
| Risk | host BigInt vs Script; external ref skips |

---

## P19 — Non-minimal true into assert / if

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P19 extends SmartContract {
  readonly bs: bytes;
  constructor(bs: bytes) { super(bs); this.bs = bs; }
  public f() {
    // if language allows ByteString as condition after bin2num
    const n = bin2num(this.bs);
    if (n) { assert(true); } else { assert(false); }
  }
}
// bs = 0x0100 (non-minimal 1)
```

| Pass | OP_IF truthiness / MINIMALDATA |
| Risk | accept path that Script rejects |

---

## P20 — if-without-else multi-temp then early return

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P20 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f(flag: bigint): bigint {
    let a: bigint = 0n; let b: bigint = 0n; let c: bigint = 0n;
    if (flag > 0n) { a = 1n; b = 2n; c = 3n; }
    return a + b + c + this.n;
  }
}
```

| Pass | if-without-else pad + return |
| Related | K=1 empty-pad regression cousin |

---

## P21 — Method private helper with branch merge inlined

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P21 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  private step(flag: bigint): bigint {
    let x: bigint = this.n; let y: bigint = 1n;
    if (flag > 0n) { x = x + 1n; y = y + 1n; } else { y = y + 2n; }
    return x + y;
  }
  public f(flag: bigint) { assert(this.step(flag) > 0n); }
}
```

| Pass | method_call inline + merge |
| Risk | inline drops merge block |

---

## P22 — Multi-method selector + per-method merge

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P22 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public m1(flag: bigint) {
    let a: bigint = 1n; let b: bigint = 2n;
    if (flag > 0n) { a = 3n; b = 4n; }
    assert(a + b === 7n || a + b === 3n);
  }
  public m2(flag: bigint) {
    let a: bigint = 1n;
    if (flag > 0n) { a = 9n; }
    assert(a > 0n);
  }
}
```

| Pass | dispatch + per-branch body stack |
| Risk | method 1 vs 2 cleanup confusion |

---

## P23 — Fixed array expand then branch (03b × merge)

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P23 extends StatefulSmartContract {
  cells: bigint[] = [0n, 0n, 0n]; // or FixedArray syntax as supported
  constructor(c0: bigint, c1: bigint, c2: bigint) {
    super(c0, c1, c2);
    this.cells = [c0, c1, c2];
  }
  public go(i: bigint, flag: bigint) {
    let x: bigint = this.cells[0]; // expand to scalars
    let y: bigint = this.cells[1];
    if (flag > 0n) { x = x + 1n; y = y + 1n; }
    // write back via supported index assign
  }
}
```

| Pass | **03b-expand-fixed-arrays** + merge |
| Risk | tier divergence on expand then join |

---

## P24 — Property initializer + merge + state write

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P24 extends StatefulSmartContract {
  a: bigint = 7n;
  b: bigint = 8n;
  constructor() { super(); }
  public go(flag: bigint) {
    let x: bigint = this.a; let y: bigint = this.b;
    if (flag > 0n) { x = 1n; y = 2n; } else { x = 3n; y = 4n; }
    this.a = x; this.b = y;
  }
}
```

| Pass | initialValue ANF + merge |
| Risk | initializer dropped or double-counted |

---

## P25 — checkSig path with empty sig in else (NULLFAIL cousin)

```typescript
import { SmartContract, assert, checkSig, Sig, PubKey } from 'runar-lang';
export class P25 extends SmartContract {
  readonly pk: PubKey;
  constructor(pk: PubKey) { super(pk); this.pk = pk; }
  public unlock(sig: Sig, flag: bigint) {
    if (flag > 0n) { assert(checkSig(sig, this.pk)); }
    else { assert(true); }
  }
}
```

| Pass | OR-CHECKSIG / EMPTY_SIG discipline |
| Risk | NULLFAIL on unused sig branch |

---

## P26 — addOutput multi-field after only-then writes

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P26 extends StatefulSmartContract {
  a: bigint = 0n; b: bigint = 0n; c: bigint = 0n;
  constructor(a: bigint, b: bigint, c: bigint) {
    super(a, b, c); this.a = a; this.b = b; this.c = c;
  }
  public go(flag: bigint, sats: bigint) {
    if (flag > 0n) { this.a = this.a + 1n; }
    this.addOutput(sats, this.a, this.b, this.c);
  }
}
```

| Pass | continuation field order with partial write |
| Risk | b/c stale or order swapped |

---

## P27 — Interleaved addDataOutput + state update

```typescript
import { StatefulSmartContract, assert, toByteString } from 'runar-lang';
export class P27 extends StatefulSmartContract {
  n: bigint = 0n;
  constructor(n: bigint) { super(n); this.n = n; }
  public go(flag: bigint) {
    if (flag > 0n) {
      this.addDataOutput(0n, toByteString('dead'));
      this.n = this.n + 1n;
    } else {
      this.n = this.n + 2n;
    }
  }
}
```

| Pass | data output + state epilogue ordering |
| Risk | output index / hashOutputs mismatch |

---

## P28 — Boolean merge through if into numeric assert

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P28 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f(flag: boolean) {
    let ok: boolean = false;
    let x: bigint = 0n;
    if (flag) { ok = true; x = this.n; } else { ok = false; x = 0n; }
    assert(ok === (x === this.n));
  }
}
```

| Pass | multi-type merge results |
| Risk | bool as OP_IF non-minimal |

---

## P29 — K=3 merge, only one local live after if

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P29 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f(flag: bigint) {
    let a: bigint = 1n; let b: bigint = 2n; let c: bigint = 3n;
    if (flag > 0n) { a = 4n; b = 5n; c = 6n; } else { a = 7n; b = 8n; c = 9n; }
    assert(a > 0n); // b,c dead after
  }
}
```

| Pass | DCE × merge × last-use |
| Risk | DCE drops live merge temp; stack desync |

---

## P30 — Dead code after assert(false) else with merge in then

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P30 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f(flag: bigint) {
    let a: bigint = 0n; let b: bigint = 0n;
    if (flag > 0n) { a = 1n; b = 2n; } else { assert(false); }
    assert(a + b === 3n);
  }
}
```

| Pass | terminal assert-false else + merge |
| Related | assert-false-guard fixture family |

---

## P31 — Constant-fold boundary: 2^31, 2^32, 2^63

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P31 extends SmartContract {
  public f() {
    const a: bigint = 2147483647n;
    const b: bigint = 2147483648n;
    const c: bigint = 4294967296n;
    assert(a + 1n === b);
    assert(b + b === c);
  }
}
```

| Pass | constant-fold host vs Script / fold-ON |
| Risk | tier fold divergence (fold-ON allowlist) |

---

## P32 — Deep nested pure if (no state) stack depth

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P32 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f() {
    let x: bigint = this.n;
    if (x > 0n) {
      if (x > 1n) {
        if (x > 2n) {
          if (x > 3n) { x = x - 1n; } else { x = x + 1n; }
        } else { x = x + 2n; }
      } else { x = x + 3n; }
    } else { x = 0n; }
    assert(x >= 0n);
  }
}
```

| Pass | recursive lowerIf depth accounting |
| Risk | maxStackDepth wrong; cleanup |

---

## P33 — Readonly property read in both arms + after

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P33 extends SmartContract {
  readonly pk: bytes;
  constructor(pk: bytes) { super(pk); this.pk = pk; }
  public f(flag: bigint) {
    let h: bigint = 0n;
    if (flag > 0n) { h = len(this.pk); } else { h = len(this.pk) + 1n; }
    assert(h === len(this.pk) || h === len(this.pk) + 1n);
  }
}
```

| Pass | pick vs roll of readonly across merge |
| Related | branched-readonly-len |

---

## P34 — Loop body contains if merge

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P34 extends StatefulSmartContract {
  s: bigint = 0n;
  constructor(s: bigint) { super(s); this.s = s; }
  public go() {
    let a: bigint = 0n; let b: bigint = 1n;
    for (let i: bigint = 0n; i < 3n; i++) {
      if (i > 1n) { a = a + 1n; b = b + 1n; } else { a = a + 2n; }
    }
    this.s = a + b;
  }
}
```

| Pass | loop + inner multi-merge |
| Risk | per-iteration stack map leak |

---

## P35 — Python/Go/Rust surface: init() pattern vs TS initializer

Same contract as P24 expressed in `.runar.go` / `.runar.rs` / `.runar.py` with
private `init()` / snake_case. **Parser matrix probe.**

| Pass | frontend AST parity |
| Risk | missing initializer → ctor slot mismatch |

---

## P36 — Invalid program: Math.floor must reject all tiers

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P36 extends SmartContract {
  public f(n: bigint) { assert(Math.floor(Number(n)) > 0); }
}
```

| Expected | **all 7 reject** at typecheck/validate |
| Risk | one tier emits script for undefined program |

---

## P37 — Invalid: mutate readonly property

```typescript
import { SmartContract } from 'runar-lang';
export class P37 extends SmartContract {
  readonly n: bigint;
  constructor(n: bigint) { super(n); this.n = n; }
  public f() { this.n = 1n; }
}
```

| Expected | all 7 reject |
| Pass | validate/typecheck |

---

## P38 — Malformed --ir unknown ANF kind

Hand-crafted IR JSON with `"kind":"not_a_real_kind"`.

| Expected | all loaders throw UnknownANFKind |
| Risk | silent drop of binding |

---

## P39 — Hostile canonicalJson: duplicate keys via raw parse

Feed each SDK the UTF-8 `{"b":1,"a":2,"a":3}` (if parse path allows) and compare
`canonicalJson` outputs / throws.

| Expected | identical reject or identical last-wins policy |
| Risk | signature verify divergence |

---

## P40 — Envelope reason matrix expansion

For each `VerifyEnvelopeReason`, one known-bad envelope on all 7 SDKs; assert
**same reason enum**, not only false.

| Risk | one tier returns generic bad-sig for expired |

---

## P41 — #149 with fold-ON only

Same as P01 with default compiler fold enabled; pin state bytes.

| Risk | fold masks or changes arm materialization |

---

## P42 — Merge locals then hash256 state commitment path

Stateful counter: merge 2 locals, write state, rely on auto hashOutputs.

| Pass | stateful epilogue + merge |
| Risk | quiet wrong state accepted by covenant |

---

## P43 — max stack: many temps in both arms unequal count

```typescript
import { SmartContract, assert } from 'runar-lang';
export class P43 extends SmartContract {
  public f(flag: bigint) {
    let a: bigint = 0n;
    if (flag > 0n) {
      const t1 = 1n; const t2 = 2n; const t3 = 3n; const t4 = 4n;
      a = t1 + t2 + t3 + t4;
    } else {
      a = 1n;
    }
    assert(a > 0n);
  }
}
```

| Pass | branch residue drain |
| Risk | unequal arm depths after drain |

---

## P44 — ByteString OP_N 0x81 (OP_1NEGATE range) as state

| Related | Palmer-2 value class |
| Pin | deployed locking hex state section across 7 SDKs |

---

## P45 — Nested if where outer merges property, inner merges locals

```typescript
import { StatefulSmartContract, assert } from 'runar-lang';
export class P45 extends StatefulSmartContract {
  p: bigint = 0n;
  constructor(p: bigint) { super(p); this.p = p; }
  public go(c1: bigint, c2: bigint) {
    let a: bigint = 1n; let b: bigint = 2n;
    if (c1 > 0n) {
      if (c2 > 0n) { a = 3n; b = 4n; } else { a = 5n; b = 6n; }
      this.p = a + b;
    } else {
      this.p = 0n;
    }
  }
}
```

| Pass | property reconcile + local merge nesting |
| Risk | property restriction regressions post-Palmer |

---

## P46 — Loop start/step non-default if language allows

If surface supports non-0 start / non-1 step, probe both; else skip as N/A.

| Related | #121 loop start/step golden re-stamp |

---

## P47 — EC: P == -Q affine add → infinity (if not already fixture-only)

Contract calling `ecAdd(P, neg(P))` expects infinity encoding.

| Risk | non-Go tiers / fold / peephole ec-rules |

---

## P48 — SHA256 compress partial block then finalize

| Related | sha256-compress/finalize fixtures without witnesses |
| Risk | golden-only codegen error |

---

## P49 — Determinism soak template

Compile P01 50× under `GOMAXPROCS=1` and default; assert hex equality per tier.

| Finding class | GK-021 |

---

## P50 — Spend-oracle required-shape: inherited sibling

Generator-shaped source matching P01 with k=2 fields, only field0 rebound in
inner if, field1 (`y`) live across outer — **must** be a spend-shapes family.

| Closes | GK-027 |

---

## Execution notes for the fix session

1. Prefer `MockProvider.enableBroadcastValidation()` (or default-on) + independent expectedState.
2. Do not use ANF interpreter post-state as the sole oracle for stateful probes.
3. Record any tier that accepts P36/P37 as **S1** language-surface bugs.
4. P01/P02/P45 are highest EV; they target the open S0 class.
5. Probes use sketch API names (`bytes`, `slice`, `num2bin`) — adapt to exact `runar-lang` exports before compile.
