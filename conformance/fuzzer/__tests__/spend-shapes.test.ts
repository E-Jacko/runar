import { describe, it, expect } from 'vitest';
import { compile } from '../../../packages/runar-compiler/src/index.js';
import {
  REQUIRED_CASE_COUNT,
  REQUIRED_TAGS,
  encodeStateSectionHex,
  generateShapes,
  type GeneratedShape,
} from '../spend-shapes.js';

/**
 * Phase E2 acceptance (testing-gap remediation plan §3 "E2. Shape injection
 * into generators"): a SEEDED run must demonstrably hit each injected shape.
 *
 * Every assertion here is on the generated SOURCE / shape record — never on a
 * probability, and never on "the fuzzer found nothing so the shape must be
 * covered". `generateShapes` draws its primary construct family round-robin, so
 * these are exact, deterministic expectations rather than statistical ones.
 */

const SEED = 424242;
/** One case per family: `generateShapes` draws `FAMILIES[i % FAMILIES.length]`,
 *  so anything short of this never reaches the tail families. */
const CORPUS = generateShapes({ seed: SEED, count: REQUIRED_CASE_COUNT });

/** All shapes whose rendered source declares `n` merged locals. */
function withLocalCount(shapes: GeneratedShape[], n: number): GeneratedShape[] {
  return shapes.filter((s) => (s.source.match(/^\s+let l\d+:/gm) ?? []).length === n);
}

describe('spend-oracle shape generator (Phase E2)', () => {
  it('is deterministic: the same seed produces byte-identical sources', () => {
    const again = generateShapes({ seed: SEED, count: REQUIRED_CASE_COUNT });
    expect(again.map((s) => s.source)).toEqual(CORPUS.map((s) => s.source));
    expect(again.map((s) => s.id)).toEqual(CORPUS.map((s) => s.id));
    expect(again.map((s) => JSON.stringify(s.expectedState, bigintReplacer))).toEqual(
      CORPUS.map((s) => JSON.stringify(s.expectedState, bigintReplacer)),
    );
  });

  it('reaches every required construct tag in one case per family', () => {
    const seen = new Set(CORPUS.flatMap((s) => s.tags));
    const missing = REQUIRED_TAGS.filter((t) => !seen.has(t));
    expect(missing).toEqual([]);
  });

  // -------------------------------------------------------------------------
  // (a) multi-local branch merges — the PALMER-1 shape family
  // -------------------------------------------------------------------------

  it('(a) emits k=1, k=2 and k>=3 merged locals', () => {
    expect(withLocalCount(CORPUS, 1).length).toBeGreaterThan(0);
    expect(withLocalCount(CORPUS, 2).length).toBeGreaterThan(0);
    expect(CORPUS.filter((s) => withLocalCount([s], 3).length + withLocalCount([s], 4).length > 0).length)
      .toBeGreaterThan(0);
  });

  it('(a) emits an ASYMMETRIC merge: the arms rebind DIFFERENT locals', () => {
    const asym = CORPUS.filter((s) => s.tags.includes('merge-asymmetric'));
    expect(asym.length).toBeGreaterThan(0);
    for (const s of asym) {
      const { thenBody, elseBody } = armBodies(s.source);
      expect(elseBody, `${s.id} must have both arms`).not.toBeNull();
      const thenTargets = assignTargets(thenBody!);
      const elseTargets = assignTargets(elseBody!);
      // Disjoint and both non-empty: this is exactly the reported shape.
      expect(thenTargets.length).toBeGreaterThan(0);
      expect(elseTargets.length).toBeGreaterThan(0);
      expect(thenTargets.filter((t) => elseTargets.includes(t))).toEqual([]);
    }
  });

  it('(a) emits a BOTH-ARMS-REBIND merge (same locals in both arms)', () => {
    const both = CORPUS.filter((s) => s.tags.includes('merge-both-arms'));
    expect(both.length).toBeGreaterThan(0);
    for (const s of both) {
      const { thenBody, elseBody } = armBodies(s.source);
      expect(elseBody).not.toBeNull();
      expect(assignTargets(thenBody!).sort()).toEqual(assignTargets(elseBody!).sort());
    }
  });

  it('(a) emits an if-WITHOUT-else merge', () => {
    const noElse = CORPUS.filter((s) => s.tags.includes('merge-no-else'));
    expect(noElse.length).toBeGreaterThan(0);
    for (const s of noElse) expect(s.source).not.toContain('} else {');
  });

  it('(a) emits a NESTED-if merge', () => {
    const nested = CORPUS.filter((s) => s.tags.includes('merge-nested-if'));
    expect(nested.length).toBeGreaterThan(0);
    for (const s of nested) {
      expect(s.source).toContain('if (p0 > 0n) {');
      expect(s.source).toContain('if (p0 > 2000n) {');
    }
  });

  // -------------------------------------------------------------------------
  // (b) 1-byte OP_N-range ByteString state + negative bigint state
  // -------------------------------------------------------------------------

  it('(b) puts a 1-byte OP_N-range ByteString (0x01..0x10 / 0x81) in STATE', () => {
    const hits = CORPUS.filter((s) =>
      [...s.fields, ...Object.entries(s.expectedState ?? {}).map(([name, value]) => ({
        name,
        type: s.fields.find((f) => f.name === name)!.type,
        value,
      }))].some(
        (m) =>
          m.type === 'ByteString' &&
          typeof m.value === 'string' &&
          m.value.length === 2 &&
          (parseInt(m.value, 16) <= 0x10 && parseInt(m.value, 16) >= 0x01 || m.value === '81'),
      ),
    );
    expect(hits.length).toBeGreaterThan(0);
    // And the independent codec frames it as <len><data>, NEVER as OP_N — the
    // exact byte difference PALMER-2 introduced.
    expect(encodeStateSectionHex([{ name: 'x', type: 'ByteString', value: '05' }], { x: '05' })).toBe('0105');
    expect(encodeStateSectionHex([{ name: 'x', type: 'ByteString', value: '81' }], { x: '81' })).toBe('0181');
    expect(encodeStateSectionHex([{ name: 'x', type: 'ByteString', value: '10' }], { x: '10' })).toBe('0110');
  });

  it('(b) covers 0x00, empty and 1-byte-outside-range ByteString state', () => {
    const values = CORPUS.flatMap((s) =>
      s.fields.filter((f) => f.type === 'ByteString').map((f) => f.value as string),
    ).concat(
      CORPUS.flatMap((s) =>
        Object.entries(s.expectedState ?? {})
          .filter(([name]) => s.fields.find((f) => f.name === name)?.type === 'ByteString')
          .map(([, v]) => v as string),
      ),
    );
    expect(values).toContain('');
    expect(values).toContain('00');
    expect(values.some((v) => v.length === 2 && parseInt(v, 16) > 0x10 && v !== '81')).toBe(true);
    expect(values.some((v) => v.length > 2)).toBe(true);
    // `0x00` must frame as `0100`, never OP_0; empty frames as a zero-length push.
    expect(encodeStateSectionHex([{ name: 'x', type: 'ByteString', value: '00' }], { x: '00' })).toBe('0100');
    expect(encodeStateSectionHex([{ name: 'x', type: 'ByteString', value: '' }], { x: '' })).toBe('00');
  });

  it('(b) puts NEGATIVE bigint values in STATE (no golden anywhere does)', () => {
    const negatives = CORPUS.flatMap((s) => [
      ...s.fields.filter((f) => f.type === 'bigint').map((f) => f.value as bigint),
      ...Object.entries(s.expectedState ?? {})
        .filter(([name]) => s.fields.find((f) => f.name === name)?.type === 'bigint')
        .map(([, v]) => v as bigint),
    ]).filter((v) => v < 0n);
    expect(negatives.length).toBeGreaterThan(0);
    expect(negatives).toContain(-1n);
    // -1 is 8-byte LE sign-magnitude: 01 00 00 00 00 00 00 80.
    expect(encodeStateSectionHex([{ name: 'x', type: 'bigint', value: -1n }], { x: -1n })).toBe(
      '0100000000000080',
    );
  });

  // -------------------------------------------------------------------------
  // (c) multi-slot constructor-arg shapes
  // -------------------------------------------------------------------------

  it('(c) emits several constructorSlots of mixed types', () => {
    const multi = CORPUS.filter((s) => s.tags.includes('ctor-slots-multi'));
    expect(multi.length).toBeGreaterThan(0);
    const mixed = multi.filter((s) => new Set(s.slots.map((x) => x.type)).size >= 2);
    expect(mixed.length).toBeGreaterThan(0);
    // Every slot is REFERENCED (unreferenced readonly props are eliminated by
    // the compiler and would never become a slot at all).
    for (const s of multi) {
      for (const slot of s.slots) expect(s.source).toContain(`this.${slot.name}`);
    }
  });

  it('(c) emits a case where an earlier slot SHIFTS later slot offsets', () => {
    expect(CORPUS.filter((s) => s.tags.includes('ctor-slots-shifting-offsets')).length).toBeGreaterThan(0);

    // The dedicated family is deterministic: slots are [PubKey, bigint 70000,
    // ByteString deadbeef], so slot 0's deployed value is a 34-byte push while
    // its TEMPLATE placeholder is a single OP_0 byte.
    const s = CORPUS.find((x) => x.family === 'ctor-slots-shifting')!;
    expect(s.slots.map((m) => m.type)).toEqual(['PubKey', 'bigint', 'ByteString']);

    const template = compile(s.source, { fileName: s.fileName });
    expect(template.success, template.diagnostics.map((d: { message: string }) => d.message).join('; ')).toBe(true);
    expect((template.artifact!.constructorSlots ?? []).length).toBe(3);

    // Bake the same source with the concrete constructor args. Slot 0's value
    // is a 34-byte PubKey push where the template holds a single OP_0
    // placeholder byte, so the baked script is at least 33 bytes longer — i.e.
    // slots 1 and 2 CANNOT keep their template offsets at deploy time. That
    // value-dependent shift is what this shape exists to exercise.
    const ctor: Record<string, bigint | boolean | string> = {};
    s.slots.forEach((m) => {
      ctor[m.name] = m.value as bigint | boolean | string;
    });
    s.fields.forEach((m) => {
      ctor[m.name] = m.value as bigint | boolean | string;
    });
    const baked = compile(s.source, { fileName: s.fileName, constructorArgs: ctor });
    expect(baked.success, baked.diagnostics.map((d: { message: string }) => d.message).join('; ')).toBe(true);
    const grew = (baked.artifact!.script.length - template.artifact!.script.length) / 2;
    expect(grew).toBeGreaterThanOrEqual(33);
  });

  // -------------------------------------------------------------------------
  // (d) loop-carried locals fed to addOutput — the ledger's
  //     `loop-carried-locals-k2`. Same "one stack carrier asked to hold N live
  //     values" family as the branch merges above, in loop form.
  // -------------------------------------------------------------------------

  const loopShapes = (): GeneratedShape[] => CORPUS.filter((s) => s.family.startsWith('loop-'));

  it('(d) emits a loop whose carried locals are fed to addOutput', () => {
    const loops = loopShapes();
    expect(loops.length).toBeGreaterThan(0);
    for (const s of loops) {
      expect(s.source, `${s.id}`).toMatch(/for \(let i: bigint = 0n; i < \d+n; i\+\+\) \{/);
      // Every carried local reaches the state continuation.
      expect(s.source).toContain(
        `this.addOutput(1000n, ${s.fields.map((_f, fi) => `l${fi}`).join(', ')});`,
      );
      // The loop, not an `if`, decides the post-state.
      expect(s.source).not.toContain('if (p0 > 0n) {');
    }
  });

  it('(d) emits the CROSS-READ shape: a carried local rebound then read again', () => {
    const cross = loopShapes().filter((s) => s.tags.includes('loop-cross-read'));
    expect(cross.length).toBeGreaterThan(0);
    for (const s of cross) {
      const body = loopBodyLines(s.source);
      // Exactly the confirmed shape: `l0` is rebound, `l1` then reads it.
      expect(body).toContain('l0 = l0 + p0;');
      expect(body).toContain('l1 = l1 + l0;');
      expect(body.indexOf('l0 = l0 + p0;')).toBeLessThan(body.indexOf('l1 = l1 + l0;'));
    }
    // ...including the ONE-iteration case: value-identical to the source, so
    // only a real spend sees the residual shadowed slot.
    const oneIter = cross.filter((s) => /i < 1n;/.test(s.source));
    expect(oneIter.length).toBeGreaterThan(0);
  });

  it('(d) emits the READ-BEFORE-REASSIGN control, distinguishable from the cross-read', () => {
    const before = loopShapes().filter((s) => s.tags.includes('loop-read-before-reassign'));
    expect(before.length).toBeGreaterThan(0);
    for (const s of before) {
      const body = loopBodyLines(s.source);
      expect(body.indexOf('l1 = l1 + l0;')).toBeLessThan(body.indexOf('l0 = l0 + p0;'));
    }
  });

  it('(d) emits NESTED loops with a carried local bound only in the inner body', () => {
    const nested = loopShapes().filter((s) => s.tags.includes('loop-nested'));
    expect(nested.length).toBeGreaterThan(0);
    for (const s of nested) {
      expect(s.source).toMatch(/for \(let j: bigint = 0n; j < \d+n; j\+\+\) \{/);
    }
    // Both nested forms: the cross-read INSIDE the inner body, and the carried
    // local rebound only in the inner body and read one scope OUT.
    expect(nested.some((s) => s.family === 'loop-k2-nested-cross-read')).toBe(true);
    expect(nested.some((s) => s.family === 'loop-k2-nested-outer-read')).toBe(true);
  });

  it("(d) the post-state model is the loop's arithmetic, computed here", () => {
    // Spot-check the model against the source by hand, the way the rest of this
    // file works: never read back out of the compiler or the SDK.
    const s = CORPUS.find((x) => x.family === 'loop-k2-cross-read')!;
    const step = s.methodArgs[0] as bigint;
    const iters = Number(/i < (\d+)n;/.exec(s.source)![1]);
    let l0 = s.fields[0]!.value as bigint;
    let l1 = s.fields[1]!.value as bigint;
    for (let i = 0; i < iters; i++) {
      l0 = l0 + step;
      l1 = l1 + l0;
    }
    expect(s.expectedState).toEqual({ f0: l0, f1: l1 });
    // And it is NOT the value the miscompile produced (`l1` accumulating the
    // PRE-loop `l0`), whenever the two differ at all.
    let bad = s.fields[1]!.value as bigint;
    let pre = s.fields[0]!.value as bigint;
    for (let i = 0; i < iters; i++) {
      const before = pre;
      pre = pre + step;
      bad = bad + before;
    }
    if (bad !== l1) expect(s.expectedState!.f1).not.toBe(bad);
  });

  // -------------------------------------------------------------------------
  // Sanity: every generated shape is a valid Rúnar contract
  // -------------------------------------------------------------------------

  it('every generated shape compiles', () => {
    for (const s of CORPUS) {
      const r = compile(s.source, { fileName: s.fileName });
      expect(r.success, `${s.id} failed to compile: ${r.diagnostics.map((d: { message: string }) => d.message).join('; ')}`).toBe(true);
    }
  });

  // -------------------------------------------------------------------------
  // Phase E4 — metamorphic variants
  // -------------------------------------------------------------------------

  it('(E4) produces a renamed-locals variant that still compiles and renames every local', () => {
    for (const s of CORPUS) {
      expect(s.variants.renameLocals).not.toBe(s.source);
      expect(s.variants.renameLocals).not.toMatch(/\bl\d+\b/);
      const r = compile(s.variants.renameLocals, { fileName: s.fileName });
      expect(r.success, `${s.id} rename-locals variant failed to compile`).toBe(true);
    }
  });

  it('(E4) produces a swapped-arms variant for the pure if/else shapes', () => {
    const swappable = CORPUS.filter((s) => s.variants.swapArms !== null);
    expect(swappable.length).toBeGreaterThan(0);
    for (const s of swappable) {
      expect(s.variants.swapArms).toContain('if (p0 <= 0n) {');
      const r = compile(s.variants.swapArms!, { fileName: s.fileName });
      expect(r.success, `${s.id} swap-arms variant failed to compile`).toBe(true);
    }
    // The no-else / nested forms have no pure arm pair, so they correctly
    // decline the transform rather than emitting a semantically different one.
    for (const s of CORPUS.filter((x) => x.tags.includes('merge-no-else') || x.tags.includes('merge-nested-if'))) {
      expect(s.variants.swapArms).toBeNull();
    }
  });
});

// ---------------------------------------------------------------------------
// Source helpers — these read the RENDERED SOURCE, not the generator's records,
// so a shape that claims a tag it does not actually emit fails the test.
// ---------------------------------------------------------------------------

function bigintReplacer(_k: string, v: unknown): unknown {
  return typeof v === 'bigint' ? `${v}n` : v;
}

/** Split `if (...) { A } else { B }` into its two arm bodies. */
function armBodies(source: string): { thenBody: string | null; elseBody: string | null } {
  const m = /if \([^)]*\) \{\n([\s\S]*?)\n\s*\}(?: else \{\n([\s\S]*?)\n\s*\})?/.exec(source);
  if (!m) return { thenBody: null, elseBody: null };
  return { thenBody: m[1] ?? null, elseBody: m[2] ?? null };
}

/** Local names assigned inside an arm body, e.g. `['l0', 'l2']`. */
function assignTargets(body: string): string[] {
  return [...body.matchAll(/^\s*(l\d+) = /gm)].map((m) => m[1]!);
}

/** Assignment statements inside a loop family's loop, trimmed, in order. */
function loopBodyLines(source: string): string[] {
  return source
    .split('\n')
    .map((l) => l.trim())
    .filter((l) => /^l\d+ = /.test(l));
}
