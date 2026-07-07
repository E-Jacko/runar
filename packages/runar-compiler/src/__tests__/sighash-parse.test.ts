import { describe, it, expect } from 'vitest';
import { parse } from '../passes/01-parse.js';

function methodByName(src: string, name: string) {
  const r = parse(src, 'X.runar.ts');
  expect(r.errors.filter((e) => e.severity === 'error')).toEqual([]);
  return r.contract!.methods.find((m) => m.name === name)!;
}

describe('#123 @sighash directive parsing (TS surface)', () => {
  it('sets sighashType from a JSDoc directive on a public method', () => {
    const src = `
      class C extends StatefulSmartContract {
        n: bigint;
        constructor(n: bigint) { super(n); this.n = n; }
        /** @sighash SINGLE|FORKID */
        public bump(): void { this.n = this.n + 1n; }
      }`;
    expect(methodByName(src, 'bump').sighashType).toBe(0x43);
  });

  it('leaves sighashType undefined when there is no directive (default 0x41)', () => {
    const src = `
      class C extends StatefulSmartContract {
        n: bigint;
        constructor(n: bigint) { super(n); this.n = n; }
        public bump(): void { this.n = this.n + 1n; }
      }`;
    expect(methodByName(src, 'bump').sighashType).toBeUndefined();
  });

  it('accepts a // line-comment directive', () => {
    const src = `
      class C extends StatefulSmartContract {
        n: bigint;
        constructor(n: bigint) { super(n); this.n = n; }
        // @sighash NONE|FORKID
        public wipe(): void { this.n = 0n; }
      }`;
    expect(methodByName(src, 'wipe').sighashType).toBe(0x42);
  });

  it('reports an error for a bad flag combo', () => {
    const src = `
      class C extends StatefulSmartContract {
        n: bigint;
        constructor(n: bigint) { super(n); this.n = n; }
        /** @sighash ALL|NONE|FORKID */
        public bump(): void { this.n = this.n + 1n; }
      }`;
    const r = parse(src, 'X.runar.ts');
    expect(r.errors.some((e) => /cannot combine base types/.test(e.message))).toBe(true);
  });

  it('reports an error for @sighash on a private method', () => {
    const src = `
      class C extends StatefulSmartContract {
        n: bigint;
        constructor(n: bigint) { super(n); this.n = n; }
        /** @sighash SINGLE|FORKID */
        private helper(): bigint { return 1n; }
        public bump(): void { this.n = this.n + 1n; }
      }`;
    const r = parse(src, 'X.runar.ts');
    expect(r.errors.some((e) => /non-public method/.test(e.message))).toBe(true);
  });
});
