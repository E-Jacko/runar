/**
 * A MUTABLE bigint property initialised to a magnitude the 8-byte
 * sign-magnitude state word cannot hold must be a compile error.
 *
 * ===========================================================================
 * `num2bin-le8` gives a bigint state field 63 magnitude bits (bytes 0..6 plus
 * the low 7 bits of byte 7) and one sign bit (0x80 of byte 7). The compiler
 * stamped `encoding: "num2bin-le8"` on the field and recorded the initializer
 * verbatim, so a contract declaring `count: bigint = 2n ** 63n` compiled,
 * deployed, and could never be spent: the SDK wrote the low 8 bytes of the
 * value into the state section while the covenant rebuilds the continuation
 * with the compiler's own OP_NUM2BIN 8, which cannot produce those bytes from
 * that number.
 *
 * This is the half of the bound that is knowable at compile time. The runtime
 * half — values that only exist when the contract is called — is guarded in
 * the SDK serializer: packages/runar-sdk/src/__tests__/state-bigint-magnitude-guard.test.ts
 * ===========================================================================
 *
 * READONLY properties are deliberately NOT guarded: they are baked into the
 * locking script as script-number pushes, never into the `num2bin-le8` state
 * section, and BSV script numbers are arbitrary-precision after Genesis. A
 * guard there would reject working contracts.
 */

import { describe, it, expect } from 'vitest';
import { compile } from '../index.js';

/** 2^63 — one past the largest magnitude the 63 magnitude bits can hold. */
const TWO_63 = 9_223_372_036_854_775_808n;
/** 2^63 - 1 — the largest magnitude that DOES fit. */
const MAX_MAGNITUDE = TWO_63 - 1n;

function statefulWithInit(init: string): string {
  return `import { StatefulSmartContract } from 'runar-lang';

export class BigInit extends StatefulSmartContract {
  count: bigint = ${init};
  constructor() { super(); }

  public bump() {
    this.count = this.count + 1n;
  }
}
`;
}

function readonlyWithInit(init: string): string {
  return `import { SmartContract, assert } from 'runar-lang';

export class BigConst extends SmartContract {
  readonly limit: bigint = ${init};
  constructor() { super(); }

  public check(x: bigint): void {
    assert(x < this.limit);
  }
}
`;
}

function diagnostics(source: string, fileName: string): string {
  const r = compile(source, { fileName });
  return r.diagnostics.map((d) => d.message).join(' | ');
}

describe('state bigint magnitude bound (compile time)', () => {
  it('rejects a mutable bigint property initialised to 2^63', () => {
    const r = compile(statefulWithInit(`${TWO_63}n`), {
      fileName: 'BigInit.runar.ts',
    });
    expect(r.success).toBe(false);
    expect(diagnostics(statefulWithInit(`${TWO_63}n`), 'BigInit.runar.ts')).toMatch(
      /does not fit/i,
    );
  });

  it('rejects -(2^63) too — the sign bit is not magnitude', () => {
    const r = compile(statefulWithInit(`-${TWO_63}n`), {
      fileName: 'BigInit.runar.ts',
    });
    expect(r.success).toBe(false);
  });

  it('rejects a magnitude well above the word (2^64)', () => {
    const r = compile(statefulWithInit('18446744073709551616n'), {
      fileName: 'BigInit.runar.ts',
    });
    expect(r.success).toBe(false);
  });

  it('names the property and the value it refused', () => {
    const msg = diagnostics(statefulWithInit(`${TWO_63}n`), 'BigInit.runar.ts');
    expect(msg).toMatch(/count/);
    expect(msg).toContain(String(TWO_63));
  });

  // -------------------------------------------------------------------------
  // Accepting controls
  // -------------------------------------------------------------------------

  it('accepts 2^63 - 1, the largest magnitude that fits', () => {
    const r = compile(statefulWithInit(`${MAX_MAGNITUDE}n`), {
      fileName: 'BigInit.runar.ts',
    });
    expect(r.success).toBe(true);
    expect(r.artifact!.stateFields![0]!.initialValue).toBe(MAX_MAGNITUDE);
  });

  it('accepts -(2^63 - 1)', () => {
    const r = compile(statefulWithInit(`-${MAX_MAGNITUDE}n`), {
      fileName: 'BigInit.runar.ts',
    });
    expect(r.success).toBe(true);
    expect(r.artifact!.stateFields![0]!.initialValue).toBe(-MAX_MAGNITUDE);
  });

  it('accepts the small initialisers shipped contracts use', () => {
    for (const init of ['0n', '1n', '-1n', '1000000n']) {
      const r = compile(statefulWithInit(init), { fileName: 'BigInit.runar.ts' });
      expect(r.success, `initialiser ${init} should compile`).toBe(true);
    }
  });

  it('leaves a READONLY bigint above 2^63 alone — it is a script push, not state', () => {
    const r = compile(readonlyWithInit('18446744073709551616n'), {
      fileName: 'BigConst.runar.ts',
    });
    expect(r.success).toBe(true);
  });
});
