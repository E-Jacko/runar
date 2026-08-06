// ---------------------------------------------------------------------------
// conformance/sdk-vertical/vertical-pins.test.ts
// ---------------------------------------------------------------------------
//
// The compiler-side half of the vertical gate — everything that needs no SDK
// toolchain, so it runs in the ordinary vitest suite. The seven-tier half is
// the CLI runner (`npm run sdk-vertical` from conformance/), because it needs
// go / cargo / zig / gradle.
//
// Two kinds of test here:
//
//   GREEN  every checked-in case still derives to its pinned goldens, and
//          every artifact's self-claims survive an independent opcode walk.
//
//   RED    four deliberate corruptions, each proving a specific pin fires.
//          A pin that has never been shown to fail is a pin that has never
//          been tested — the same reasoning `conformance/witnesses` applies
//          to coverage claims. The corruptions are applied to in-memory
//          copies; nothing on disk is modified.
// ---------------------------------------------------------------------------

import { existsSync, readFileSync, readdirSync } from 'fs';
import { dirname, join } from 'path';
import { fileURLToPath } from 'url';
import { describe, expect, it } from 'vitest';

import { RunarContract } from '../../packages/runar-sdk/src/index.js';
import { hexToBytes, runStatefulSpend, runStatelessSigned, testKey } from '../../packages/runar-testing/src/index.js';

import { MATRIX } from './matrix.js';
import { checkDeployedAgainstDerivation, deriveVertical, type RefArtifact } from './reference/derive.js';
import { argValue, encodePushData, encodeScriptNumber, type TypedArg } from './reference/encode.js';
import { findCodeSeparators, walkScript } from './reference/script.js';
import { checkArtifacts, diffArtifact } from './generate.js';

const HERE = dirname(fileURLToPath(import.meta.url));
const CASES_DIR = join(HERE, 'cases');
const CONTRACTS_DIR = join(HERE, 'contracts');

interface CaseInput {
  artifact: RefArtifact;
  constructorArgs: TypedArg[];
}

const CASES = readdirSync(CASES_DIR, { withFileTypes: true })
  .filter((d) => d.isDirectory() && existsSync(join(CASES_DIR, d.name, 'input.json')))
  .map((d) => d.name)
  .sort();

function loadCase(name: string): CaseInput {
  return JSON.parse(readFileSync(join(CASES_DIR, name, 'input.json'), 'utf-8')) as CaseInput;
}

function clone<T>(v: T): T {
  return JSON.parse(JSON.stringify(v)) as T;
}

function codes(violations: Array<{ code: string }>): string[] {
  return violations.map((v) => v.code);
}

// ---------------------------------------------------------------------------
// GREEN — the pinned matrix
// ---------------------------------------------------------------------------

describe('sdk-vertical: matrix is populated', () => {
  it('has cases', () => {
    expect(CASES.length).toBeGreaterThan(0);
  });

  // A row with no case dir would silently never run; a case dir with no
  // MATRIX row is a stale golden nothing generates or reviews anymore.
  // "non-empty" alone (the previous assertion) cannot catch either (plan P2).
  it('cases/ on disk is EXACTLY the set of names in MATRIX — not merely non-empty', () => {
    const matrixNames = [...new Set(MATRIX.map((r) => r.name))].sort();
    expect(CASES).toEqual(matrixNames);
  });
});

describe.each(CASES)('sdk-vertical: %s', (name) => {
  const input = loadCase(name);
  const derived = deriveVertical(input.artifact, input.constructorArgs);

  it('artifact self-claims survive an independent opcode walk, and the splice resolves', () => {
    expect(derived.violations).toEqual([]);
  });

  it('independently-derived code part equals the checked-in golden', () => {
    const golden = readFileSync(join(CASES_DIR, name, 'expected-code-part.hex'), 'utf-8').trim();
    expect(derived.codePartHex).toBe(golden);
  });

  it('independently-derived layout equals the checked-in golden', () => {
    const golden = JSON.parse(readFileSync(join(CASES_DIR, name, 'expected-vertical.json'), 'utf-8'));
    expect(derived.slots).toEqual(golden.slots);
    expect(derived.templateCodeSeparators).toEqual(golden.templateCodeSeparators);
    expect(derived.deployedCodeSeparators).toEqual(golden.deployedCodeSeparators);
    expect(derived.codeSepSlotValues).toEqual(golden.codeSepSlotValues);
    expect(derived.codePartByteLength).toBe(golden.codePartByteLength);
  });

  it('the pinned locking-script golden begins with the derived code part', () => {
    const locking = readFileSync(join(CASES_DIR, name, 'expected-locking.hex'), 'utf-8').trim();
    expect(locking.startsWith(derived.codePartHex)).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// RED-PROOF 1 — an off-by-one constructorSlots offset
// ---------------------------------------------------------------------------

describe('RED-PROOF 1: constructorSlots byteOffset shifted by one', () => {
  it('fails the vertical pin', () => {
    const input = clone(loadCase('bytes-multi-4'));
    expect(deriveVertical(input.artifact, input.constructorArgs).violations).toEqual([]);

    input.artifact.constructorSlots![0]!.byteOffset += 1;
    const v = deriveVertical(input.artifact, input.constructorArgs).violations;

    expect(v.length).toBeGreaterThan(0);
    expect(codes(v).some((c) => c.startsWith('T2-') || c.startsWith('T3-'))).toBe(true);
  });

  it('an off-by-one onto a NEIGHBOURING, ALREADY-CLAIMED OP_0 fails via T4 — but this is a coincidence of THIS template, not a general catch (see P1-5 executed rows below)', () => {
    // SlotMatrix's template has adjacent OP_0 placeholders at 6 and 7, so
    // shifting the slot at 6 to 7 lands on a byte that IS 0x00 AND is already
    // claimed by another slot — that second fact is what actually fires here
    // (T4-duplicate-slot-offset), not the opcode walk by itself. T2/T3 do not
    // fire: offset 7 is a perfectly genuine 1-byte OP_0 opcode boundary.
    //
    // For an UNCLAIMED OP_0 — a compiler bug that points a slot's byteOffset
    // at some OTHER stray, genuine OP_0 elsewhere in the script that no other
    // slot claims — T2/T3/T4 all pass (it is still a valid, singly-claimed
    // opcode boundary), and D2 ALSO passes: `deriveVertical` trusts the
    // artifact's declared offset and splices there, so a splice at a
    // self-consistently WRONG offset produces a self-consistently "correct"
    // derivation. Nothing byte-level distinguishes "the compiler declared the
    // right slot" from "the compiler declared a plausible-looking wrong one"
    // — only running the result can: see the P1-5 EXECUTED ROWS below, which
    // spend the compiled script through a real `@bsv/sdk` `Spend` and prove a
    // mis-spliced witness/flag is rejected on-chain.
    const input = clone(loadCase('bytes-multi-4'));
    const slots = input.artifact.constructorSlots!;
    const tagSlot = slots.find((s) => s.byteOffset === 6)!;
    expect(input.artifact.script.slice(7 * 2, 7 * 2 + 2)).toBe('00'); // the decoy really is OP_0
    tagSlot.byteOffset = 7;

    const v = deriveVertical(input.artifact, input.constructorArgs).violations;
    expect(v.length).toBeGreaterThan(0);
    expect(codes(v)).toContain('T4-duplicate-slot-offset');
  });
});

// ---------------------------------------------------------------------------
// RED-PROOF 2 — a co-changed encoder/decoder pair (the PALMER-2 shape)
// ---------------------------------------------------------------------------

describe('RED-PROOF 2: 1-byte ByteString constructor arg mis-encoded in the OP_N range', () => {
  // The bug that shipped in 2026-08 was not "one SDK got it wrong". It was a
  // serializer and its own parser changing together, so every round-trip test
  // stayed green while the bytes on chain became unreadable. Reproduce that
  // shape: a hypothetical SDK whose push encoder collapses a 1-byte 0x00 to
  // OP_0, and whose extractor reads OP_0 back as 0x00.
  const brokenEncodePushData = (hex: string): string => {
    if (hex.length === 2 && parseInt(hex, 16) === 0x00) return '00'; // WRONG: OP_0
    return encodePushData(hex);
  };
  // A realistic extractor — it handles the single-opcode push encodings the
  // way every tier's does — carrying exactly ONE fault, the exact inverse of
  // the encoder's. That inverse-pair symmetry is the whole failure mode.
  const brokenExtract = (encoded: string): string => {
    const b0 = parseInt(encoded.slice(0, 2), 16);
    if (b0 === 0x00) return '00'; // WRONG: OP_0 pushes the EMPTY item
    if (b0 === 0x4f) return '81'; // OP_1NEGATE
    if (b0 >= 0x51 && b0 <= 0x60) return (b0 - 0x50).toString(16).padStart(2, '0'); // OP_N
    return encoded.slice(2, 2 + b0 * 2);
  };

  it('a round-trip test does NOT catch it — the co-changed pair agrees with itself', () => {
    for (const value of ['00', '05', '81', 'deadbeef']) {
      expect(brokenExtract(brokenEncodePushData(value))).toBe(value);
    }
  });

  it('the vertical pin DOES catch it: the slot pushes the empty item, not 0x00', () => {
    // The ORIGINAL version of this test spliced ONLY brokenEncodePushData('00')
    // over the template's first byte and left the rest of the template
    // untouched. brokenEncodePushData('00') returns '00' — byte-IDENTICAL to
    // the placeholder it replaces — so nothing was actually spliced: the
    // "brokenLocking" produced was the untouched 13-byte template, compared
    // against an 81-byte code part. `startsWith` is trivially false for ANY
    // 13-byte prefix of an 81-byte string, broken encoder or not — the
    // assertion passed for a reason that had nothing to do with the bug. That
    // is RED-PROOF 2 finding its OWN gap: a red-proof that can't be shown to
    // fail for the right reason has never actually been tested.
    //
    // The fix: splice EVERY constructor slot the broken way (only the 'data'
    // slots are even reachable by this bug — bump/scriptnum/bool slots are a
    // different code path in every real SDK), descending byte offset so
    // earlier offsets stay valid — exactly `deriveVertical`'s own splice
    // order, reproduced independently here rather than imported, so this
    // proof does not depend on the correctness of the code it is red-proofing.
    const input = clone(loadCase('bytes-zero'));
    const good = deriveVertical(input.artifact, input.constructorArgs);
    expect(good.violations).toEqual([]);

    const brokenSubs = (input.artifact.constructorSlots ?? []).map((slot) => {
      const arg = input.constructorArgs[slot.paramIndex]!;
      const encoding = slot.valueEncoding ?? 'data';
      let encodedHex: string;
      if (encoding === 'data') {
        encodedHex = brokenEncodePushData(argValue(arg) as string);
      } else if (encoding === 'scriptnum') {
        encodedHex = encodeScriptNumber(argValue(arg) as bigint);
      } else {
        encodedHex = (argValue(arg) as boolean) ? '51' : '00';
      }
      return { templateByteOffset: slot.byteOffset, encodedHex, name: slot.name ?? String(slot.paramIndex) };
    });
    let brokenCode = input.artifact.script;
    for (const s of [...brokenSubs].sort((a, b) => b.templateByteOffset - a.templateByteOffset)) {
      const at = s.templateByteOffset * 2;
      brokenCode = brokenCode.slice(0, at) + s.encodedHex + brokenCode.slice(at + 2);
    }

    // bytes-zero's SlotMatrix template has exactly ONE data slot whose value
    // is a corruptible 1-byte 0x00 ('tag', referenced twice at the SAME arg
    // value — see matrix.ts) — count is a scriptnum slot and owner is a
    // 33-byte PubKey, neither reachable by this encoder bug. Both `tag`
    // occurrences collapse from the correct 2-byte '0100' to the broken
    // 1-byte '00', so the broken code part is exactly 2 bytes shorter.
    expect(brokenCode).not.toBe(good.codePartHex);
    expect(brokenCode.length / 2).toBe(good.codePartByteLength - 2);

    // The pin compares the tier's bytes to the independent derivation.
    expect(brokenCode.startsWith(good.codePartHex)).toBe(false);

    // The semantic layer names the fault, per corrupted slot, without any
    // golden at all — checkDeployedAgainstDerivation walks the broken script
    // and asks what each of the GOOD derivation's slots actually pushes there.
    const violations = checkDeployedAgainstDerivation(good, brokenCode);
    const tagFault = violations.find((v) => v.code === 'D2-slot-pushes-wrong-value' && v.message.includes(`'tag'`));
    expect(tagFault, JSON.stringify(violations)).toBeDefined();
    expect(tagFault!.message).toContain('pushes 0x<empty>'); // OP_0 pushes the EMPTY item
    expect(tagFault!.message).toContain('deploy-time value is 0x00');

    // And directly, at the slot's own byte offset: OP_0 (empty push), not the
    // direct push '0100' the deploy-time value 0x00 requires.
    const op = walkScript(brokenCode)[0]!;
    expect(op.pushedHex).toBe(''); // OP_0 pushes the EMPTY item
    expect(op.pushedHex).not.toBe('00'); // ...but 0x00 was the deploy-time value
  });

  it('the correct encoding is pinned in the goldens for every OP_N-range class', () => {
    // 0x01..0x10 and 0x81 collapse to a single opcode; 0x00 must NOT.
    const expectations: Array<[string, string]> = [
      ['bytes-zero', '0100'],
      ['bytes-op-n-low', '51'],
      ['bytes-op-n-mid', '55'],
      ['bytes-op-n-high', '60'],
      ['bytes-op1negate', '4f'],
      ['bytes-outside-low', '0111'],
      ['bytes-empty', '00'],
    ];
    for (const [caseName, encoded] of expectations) {
      const golden = readFileSync(join(CASES_DIR, caseName, 'expected-code-part.hex'), 'utf-8').trim();
      expect(golden.slice(0, encoded.length), `${caseName} slot bytes`).toBe(encoded);
    }
  });
});

// ---------------------------------------------------------------------------
// RED-PROOF 3 — codeSeparatorIndex shifted, script untouched
// ---------------------------------------------------------------------------

describe('RED-PROOF 3: codeSeparatorIndex/Indices shifted by one, script unchanged', () => {
  it('fails the vertical pin', () => {
    const input = clone(loadCase('codesep-tag-op-n'));
    expect(deriveVertical(input.artifact, input.constructorArgs).violations).toEqual([]);

    input.artifact.codeSeparatorIndices = input.artifact.codeSeparatorIndices!.map((i) => i + 1);
    input.artifact.codeSeparatorIndex = input.artifact.codeSeparatorIndex! + 1;

    const v = deriveVertical(input.artifact, input.constructorArgs).violations;
    expect(codes(v)).toContain('T5-codesep-indices-mismatch');
    expect(codes(v)).toContain('T6-codesep-index-mismatch');
  });

  it('also fails when only the codeSepIndexSlot target is shifted', () => {
    const input = clone(loadCase('codesep-tag-op-n'));
    input.artifact.codeSepIndexSlots![0]!.codeSepIndex += 1;
    const v = deriveVertical(input.artifact, input.constructorArgs).violations;
    expect(codes(v)).toContain('T7-codesep-slot-target-missing');
  });
});

// ---------------------------------------------------------------------------
// RED-PROOF 4 — the script's OP_CODESEPARATOR moves, artifact untouched
// ---------------------------------------------------------------------------

describe('RED-PROOF 4: OP_CODESEPARATOR relocated in the script, artifact unchanged', () => {
  it('fails the vertical pin', () => {
    const input = clone(loadCase('codesep-tag-op-n'));
    const script = input.artifact.script;
    const seps = findCodeSeparators(script);
    expect(seps[0]).toBe(6);

    // Swap the OP_CODESEPARATOR at byte 6 with the 1-byte opcode before it, so
    // the script still decodes cleanly but the separator now sits at byte 5.
    // CodeSepMatrix has THREE public methods (bump/reseal/close), each with
    // its own OP_CODESEPARATOR — only the first (bump's) moves; reseal's and
    // close's (seps[1], seps[2]) sit well after byte 7 and are untouched by a
    // same-length swap at bytes 5-6.
    const at = (i: number) => script.slice(i * 2, i * 2 + 2);
    const swapped = script.slice(0, 5 * 2) + at(6) + at(5) + script.slice(7 * 2);
    expect(findCodeSeparators(swapped)).toEqual([5, seps[1], seps[2]]);
    input.artifact.script = swapped;

    const v = deriveVertical(input.artifact, input.constructorArgs).violations;
    expect(codes(v)).toContain('T5-codesep-indices-mismatch');
  });

  it('a 0xab byte inside PUSH DATA is not mistaken for a separator', () => {
    // bytes-ab-trap bakes a 1-byte 0xab constructor arg; codesep-tag-ab-trap
    // bakes three. A naive `script.indexOf('ab')` scan reports those as
    // separators. The walk must not. CodeSepMatrix has three public methods
    // (bump/reseal/close), each auto-injecting its own OP_CODESEPARATOR.
    const trap = loadCase('codesep-tag-ab-trap');
    const derived = deriveVertical(trap.artifact, trap.constructorArgs);
    expect(derived.violations).toEqual([]);
    expect(derived.deployedCodeSeparators.length).toBe(3);

    const naive: number[] = [];
    for (let i = 0; i + 1 < derived.codePartHex.length; i += 2) {
      if (derived.codePartHex.slice(i, i + 2) === 'ab') naive.push(i / 2);
    }
    expect(naive.length).toBeGreaterThan(derived.deployedCodeSeparators.length);
  });
});

// ---------------------------------------------------------------------------
// P0-1: codeSepIndexSlots must exercise a SHIFTED, MULTI-BYTE bake — the
// matrix must not regress to "every row bakes the same constant".
// ---------------------------------------------------------------------------
//
// Before `reseal` was added to CodeSepMatrix.runar.ts, the artifact's ONLY
// codeSepIndexSlot targeted `bump`'s own OP_CODESEPARATOR, which always sits
// at template offset 6 — before EVERY constructor slot — so its baked value
// was `6 + 0 = 6` on every single row, regardless of `tag`. `reseal` (added
// after `bump`, before `close`) gives every codesep-tag-* case a SECOND
// codeSepIndexSlot whose own separator sits AFTER the `tag` ctor slot, so its
// baked value moves with `tag`'s encoded length — the first time any row
// bakes a shifted, multi-byte codesep index.
// ---------------------------------------------------------------------------

describe('P0-1: codeSepIndexSlots exercise a shifted, multi-byte bake (not a constant)', () => {
  const codesepCases = CASES.filter((c) => c.startsWith('codesep-'));
  const allValues = codesepCases.flatMap((name) => {
    const input = loadCase(name);
    const derived = deriveVertical(input.artifact, input.constructorArgs);
    expect(derived.violations).toEqual([]);
    return derived.codeSepSlotValues;
  });

  it('has codesep cases to check', () => {
    expect(codesepCases.length).toBeGreaterThan(0);
  });

  it('at least one codeSepIndexSlot targets a separator AFTER the first ctor slot', () => {
    const input = loadCase(codesepCases[0]!);
    const firstCtorOffset = Math.min(...input.artifact.constructorSlots!.map((s) => s.byteOffset));
    const lateTargets = (input.artifact.codeSepIndexSlots ?? []).filter((s) => s.codeSepIndex > firstCtorOffset);
    expect(lateTargets.length).toBeGreaterThan(0);
  });

  it('at least two rows bake DIFFERENT values for the SAME codeSepIndexSlot target', () => {
    const byTemplateOffset = new Map<number, Set<number>>();
    for (const v of allValues) {
      const set = byTemplateOffset.get(v.templateByteOffset) ?? new Set<number>();
      set.add(v.expectedBakedValue);
      byTemplateOffset.set(v.templateByteOffset, set);
    }
    const distinctCounts = [...byTemplateOffset.values()].map((s) => s.size);
    expect(Math.max(...distinctCounts)).toBeGreaterThanOrEqual(2);
  });

  it('at least one baked value requires a multi-byte scriptnum push (> 16)', () => {
    expect(allValues.some((v) => v.expectedBakedValue > 16)).toBe(true);
  });

  it('at least one row bakes a value DIFFERENT from its own templateCodeSepIndex — proving the shift-accumulation loop in collectSubstitutions/derive.ts:312-316 is live, not dead code', () => {
    expect(allValues.some((v) => v.expectedBakedValue !== v.templateCodeSepIndex)).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// Extra defect: an encode failure must surface as a violation, not a crash.
// ---------------------------------------------------------------------------

describe('extra defect: a slot whose valueEncoding disagrees with its ABI arg type reports D0-encode-failed instead of throwing', () => {
  it('does not throw, and the derivation still returns something usable', () => {
    const input = clone(loadCase('bigint-0'));
    // count's slot declares valueEncoding 'scriptnum'; feed it a ByteString arg.
    input.constructorArgs[0] = { type: 'ByteString', value: 'ab' };

    let result: ReturnType<typeof deriveVertical> | undefined;
    expect(() => {
      result = deriveVertical(input.artifact, input.constructorArgs);
    }).not.toThrow();

    expect(codes(result!.violations)).toContain('D0-encode-failed');
    expect(result!.contractName).toBe(input.artifact.contractName);
  });

  it('previously escaped uncaught: generate.ts would have crashed instead of printing "[FAIL] refusing to write a golden"', () => {
    // Same fixture, exercised the way generate.ts's per-row loop calls it:
    // catch nothing extra, just call deriveVertical and inspect violations.
    const input = clone(loadCase('bool-true'));
    input.constructorArgs[0] = { type: 'bigint', value: '1' }; // flag slot declares 'bool'
    const violations = deriveVertical(input.artifact, input.constructorArgs).violations;
    expect(codes(violations)).toContain('D0-encode-failed');
  });
});

describe('extra defect: T8 checks slot.type and slot.valueEncoding against the ABI, not just slot.name', () => {
  // bigint-0's SlotMatrix constructorSlots are, in order: tag(0), count(1),
  // tag(2), owner(3), owner(4) — index 1 is the 'count' (bigint) slot.
  it('T8-slot-type-mismatch when a constructor slot declares the wrong type', () => {
    const input = clone(loadCase('bigint-0'));
    expect(deriveVertical(input.artifact, input.constructorArgs).violations).toEqual([]);
    const countSlot = input.artifact.constructorSlots![1]!;
    expect(countSlot.name).toBe('count');
    countSlot.type = 'ByteString'; // count is really 'bigint'
    const v = deriveVertical(input.artifact, input.constructorArgs).violations;
    expect(codes(v)).toContain('T8-slot-type-mismatch');
  });

  it('T8-slot-encoding-mismatch when valueEncoding disagrees with what the ABI type implies', () => {
    const input = clone(loadCase('bigint-0'));
    const countSlot = input.artifact.constructorSlots![1]!;
    expect(countSlot.name).toBe('count');
    countSlot.valueEncoding = 'data'; // count is bigint -> must be 'scriptnum'
    const v = deriveVertical(input.artifact, input.constructorArgs).violations;
    expect(codes(v)).toContain('T8-slot-encoding-mismatch');
  });
});

// ---------------------------------------------------------------------------
// P1-4 D3 red-proof — fixedValueByteLength / fixedPushHeaderBytes mismatches.
// Every checked-in row uses the SAME 33-byte pubkey, so these branches have
// never fired on any real input.
// ---------------------------------------------------------------------------

describe('P1-4 D3 red-proof: fixedValueByteLength / fixedPushHeaderBytes, never exercised by any matrix row', () => {
  it('every matrix row uses the SAME 33-byte pubkey for every PubKey slot', () => {
    const pubkeyValues = new Set(
      MATRIX.flatMap((r) => r.constructorArgs.filter((a) => a.type === 'PubKey').map((a) => a.value)),
    );
    expect(pubkeyValues.size).toBe(1);
    expect([...pubkeyValues][0]!.length).toBe(33 * 2);
  });

  it('D3-fixed-length-mismatch fires for a 32-byte value against a slot declaring fixedValueByteLength 33', () => {
    const input = clone(loadCase('bigint-0')); // SlotMatrix: owner is PubKey, fixedValueByteLength: 33
    const ownerArg = input.constructorArgs[2]!;
    expect(ownerArg.type).toBe('PubKey');
    ownerArg.value = 'aa'.repeat(32); // one byte short of the declared 33
    const v = deriveVertical(input.artifact, input.constructorArgs).violations;
    expect(codes(v)).toContain('D3-fixed-length-mismatch');
  });

  it('D3-fixed-header-mismatch fires for a 76-byte value against a slot declaring fixedPushHeaderBytes 1', () => {
    const input = clone(loadCase('bigint-0'));
    const ownerArg = input.constructorArgs[2]!;
    expect(ownerArg.type).toBe('PubKey');
    ownerArg.value = 'aa'.repeat(76); // needs OP_PUSHDATA1 (2-byte header); slot declares 1
    const v = deriveVertical(input.artifact, input.constructorArgs).violations;
    expect(codes(v)).toContain('D3-fixed-header-mismatch');
  });
});

// ---------------------------------------------------------------------------
// P0-2 — signing-subscript pins for TypeScript (X1 static, X2 executed).
// ---------------------------------------------------------------------------
//
// packages/runar-sdk/src/contract.ts has TWO implementations of the same
// arithmetic: `_resolvedCodeSepSlotValues` (what gets BAKED into the script —
// what the rest of this suite pins) and `adjustCodeSepOffset` (what computes
// the BIP-143 scriptCode TRIM POINT, reached from `getSubscriptForSigning`).
// Both gate on `this._codeScript !== null`, which is null on the ordinary
// deploy path, so `adjustCodeSepOffset` is what actually runs there — and
// nothing before this called it. An off-by-one in it alone: every D5 pin
// stays green, the signature is one byte short.
// ---------------------------------------------------------------------------

describe('P0-2 X1: RunarContract.getSubscriptForSigning trims the DEPLOYED code part at the exact offset the independent derivation computes', () => {
  const codesepCases = CASES.filter((c) => c.startsWith('codesep-'));

  it('has codesep cases to check', () => {
    expect(codesepCases.length).toBeGreaterThan(0);
  });

  describe.each(codesepCases)('%s', (name) => {
    it('getCodePartHex() agrees with the independent derivation first — or the trim point means nothing', () => {
      const input = loadCase(name);
      const derived = deriveVertical(input.artifact, input.constructorArgs);
      expect(derived.violations).toEqual([]);

      const args = input.constructorArgs.map(argValue);
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      const contract = new RunarContract(input.artifact as any, args);
      expect(contract.getCodePartHex()).toBe(derived.codePartHex);
    });

    it('getSubscriptForSigning trims at the SAME offset the independent derivation says OP_CODESEPARATOR lands, for every method', () => {
      const input = loadCase(name);
      const derived = deriveVertical(input.artifact, input.constructorArgs);
      expect(derived.violations).toEqual([]);

      const args = input.constructorArgs.map(argValue);
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      const contract = new RunarContract(input.artifact as any, args);
      const deployed = derived.codePartHex;

      expect(derived.deployedCodeSeparators.length).toBeGreaterThan(0);
      for (let m = 0; m < derived.deployedCodeSeparators.length; m++) {
        const sepOffset = derived.deployedCodeSeparators[m]!;
        const want = deployed.slice((sepOffset + 1) * 2);
        expect(contract.getSubscriptForSigning(deployed, m), `${name} method ${m}`).toBe(want);
      }
    });
  });
});

describe('P0-2 X2: a real deploy -> call continuation spend of CodeSepMatrix.reseal (the shifted, multi-byte codesep bake) validates on @bsv/sdk Spend', () => {
  const source = readFileSync(join(CONTRACTS_DIR, 'CodeSepMatrix.runar.ts'), 'utf-8');

  it(
    'accepts a correct spend, and the continuation state carries the new note',
    async () => {
      const key = testKey('alice');
      const r = await runStatefulSpend({
        source,
        fileName: 'CodeSepMatrix.runar.ts',
        method: 'reseal',
        args: ['deadbeef'],
        // tag = '00' -> the +1-byte shift class (codesep-tag-zero), exercised
        // here as a REAL signed spend, not just a static derivation.
        constructorArgs: ['48656c6c6f', '00', key.pubKey],
        signerKey: 'alice',
      });
      expect(r.vmAccepted, r.vmError).toBe(true);
      expect(r.continuationState).toEqual({ note: 'deadbeef' });
    },
    20000,
  );

  it(
    'a tampered continuation output is rejected by the real engine (the reject half — without it an always-true harness would pass silently)',
    async () => {
      const key = testKey('alice');
      const r = await runStatefulSpend({
        source,
        fileName: 'CodeSepMatrix.runar.ts',
        method: 'reseal',
        args: ['deadbeef'],
        constructorArgs: ['48656c6c6f', '00', key.pubKey],
        signerKey: 'alice',
        tamperOutput: true,
      });
      expect(r.vmAccepted).toBe(false);
      expect(r.reachedEngine).toBe(true);
    },
    20000,
  );
});

// ---------------------------------------------------------------------------
// P0-3 — generate.ts --check: recompile and diff against the checked-in
// goldens, without writing anything.
// ---------------------------------------------------------------------------

describe('P0-3 diffArtifact red-proof: a one-byte script mutation is named by exact offset, in memory, no compiler needed', () => {
  it('names the differing byte offset and both values', () => {
    const golden = { script: '00' + '11'.repeat(10), other: 'x' };
    const actual = { script: 'ff' + '11'.repeat(10), other: 'x' };
    const issues = diffArtifact('unit-test', golden, actual);
    expect(issues).toHaveLength(1);
    expect(issues[0]).toContain("'script' differs");
    expect(issues[0]).toContain('offset 0');
    expect(issues[0]).toContain('expected 0x00');
    expect(issues[0]).toContain('actual 0xff');
  });

  it('is key-order independent (no false positive on an object with reordered keys)', () => {
    const golden = { a: 1, b: { x: 1, y: 2 } };
    const actual = { b: { y: 2, x: 1 }, a: 1 };
    expect(diffArtifact('unit-test', golden, actual)).toEqual([]);
  });

  it('finds the offset in a byte further into the script, not just byte 0', () => {
    const golden = { script: '11'.repeat(5) + '00' + '11'.repeat(5) };
    const actual = { script: '11'.repeat(5) + 'ff' + '11'.repeat(5) };
    const issues = diffArtifact('unit-test', golden, actual);
    expect(issues[0]).toContain('offset 5');
  });
});

describe('P0-3 integration: a fresh recompile of contracts/*.runar.ts matches the checked-in goldens', () => {
  it(
    'checkArtifacts() reports zero issues (spawns the compiler for SlotMatrix/SlotBool/CodeSepMatrix)',
    () => {
      const result = checkArtifacts();
      expect(result.issues, result.issues.join('\n')).toEqual([]);
      expect(result.ok).toBe(true);
    },
    60000,
  );
});

// ---------------------------------------------------------------------------
// P1-5 — executed rows: the "unclaimed OP_0" gap is only closed by actually
// spending the compiled script through a real Bitcoin Script interpreter.
// ---------------------------------------------------------------------------

describe('P1-5 executed rows: SlotMatrix.unlock — real signature, accept and reject', () => {
  const source = readFileSync(join(CONTRACTS_DIR, 'SlotMatrix.runar.ts'), 'utf-8');
  const key = testKey('alice');

  it('accepts with witness/n matching the baked tag/count', () => {
    const r = runStatelessSigned({
      source,
      fileName: 'SlotMatrix.runar.ts',
      method: 'unlock',
      args: [{ signWith: 'alice' }, hexToBytes('05'), 7n],
      constructorArgs: { count: 7n, tag: '05', owner: key.pubKey },
    });
    expect(r.vmAccepted, r.vmError).toBe(true);
  });

  it('rejects a witness that does NOT match the baked tag — the general "unclaimed OP_0" case no static pin above can catch', () => {
    const r = runStatelessSigned({
      source,
      fileName: 'SlotMatrix.runar.ts',
      method: 'unlock',
      args: [{ signWith: 'alice' }, hexToBytes('06'), 7n],
      constructorArgs: { count: 7n, tag: '05', owner: key.pubKey },
    });
    expect(r.vmAccepted).toBe(false);
    expect(r.reachedEngine).toBe(true);
  });
});

describe('P1-5 executed rows: SlotBool.unlock — real signature, both flag values, accept and reject', () => {
  const source = readFileSync(join(CONTRACTS_DIR, 'SlotBool.runar.ts'), 'utf-8');
  const key = testKey('bob');

  it('flag=true, expected=true -> accepts', () => {
    const r = runStatelessSigned({
      source,
      fileName: 'SlotBool.runar.ts',
      method: 'unlock',
      args: [{ signWith: 'bob' }, true],
      constructorArgs: { flag: true, owner: key.pubKey },
    });
    expect(r.vmAccepted, r.vmError).toBe(true);
  });

  it('flag=true, expected=false -> rejects', () => {
    const r = runStatelessSigned({
      source,
      fileName: 'SlotBool.runar.ts',
      method: 'unlock',
      args: [{ signWith: 'bob' }, false],
      constructorArgs: { flag: true, owner: key.pubKey },
    });
    expect(r.vmAccepted).toBe(false);
    expect(r.reachedEngine).toBe(true);
  });

  it('flag=false, expected=false -> accepts (byte-identical to the untouched OP_0 placeholder — the class this fixture exists for)', () => {
    const r = runStatelessSigned({
      source,
      fileName: 'SlotBool.runar.ts',
      method: 'unlock',
      args: [{ signWith: 'bob' }, false],
      constructorArgs: { flag: false, owner: key.pubKey },
    });
    expect(r.vmAccepted, r.vmError).toBe(true);
  });

  it('flag=false, expected=true -> rejects', () => {
    const r = runStatelessSigned({
      source,
      fileName: 'SlotBool.runar.ts',
      method: 'unlock',
      args: [{ signWith: 'bob' }, true],
      constructorArgs: { flag: false, owner: key.pubKey },
    });
    expect(r.vmAccepted).toBe(false);
    expect(r.reachedEngine).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// P2 — mechanical enforcement of the reference/** import boundary. The whole
// vertical-pin design rests on reference/** being independent of the code it
// checks; before this, only a prose comment guarded that.
// ---------------------------------------------------------------------------

describe('P2: reference/** imports nothing from packages/**, runar-*, or @bsv/*', () => {
  const REFERENCE_DIR = join(HERE, 'reference');
  const files = readdirSync(REFERENCE_DIR).filter((f) => f.endsWith('.ts'));

  it('has files to check', () => {
    expect(files.length).toBeGreaterThan(0);
  });

  for (const file of files) {
    it(file, () => {
      const src = readFileSync(join(REFERENCE_DIR, file), 'utf-8');
      const importLines = src.match(/^import[^;]+;/gm) ?? [];
      for (const line of importLines) {
        expect(line, `${file}: ${line}`).not.toMatch(/from\s+['"](packages\/|runar-|@bsv\/)/);
      }
    });
  }
});
