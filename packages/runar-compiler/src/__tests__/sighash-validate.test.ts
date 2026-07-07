import { describe, it, expect } from 'vitest';
import { compile } from '../index.js';

function errorsOf(src: string, fileName = 'X.runar.ts'): string[] {
  const r = compile(src, { fileName });
  return (r.diagnostics ?? []).filter((d) => d.severity === 'error').map((d) => d.message);
}
function compiles(src: string, fileName = 'X.runar.ts'): boolean {
  const r = compile(src, { fileName });
  return !!r.artifact && (r.diagnostics ?? []).filter((d) => d.severity === 'error').length === 0;
}

// ---------------------------------------------------------------------------
// Negative: one rejection per validation rule
// ---------------------------------------------------------------------------

describe('#123 field-usage validation — ANYONECANPAY', () => {
  const GUARD = (directive: string) => `
    class Guard extends SmartContract {
      readonly expected: ByteString;
      constructor(expected: ByteString) { super(expected); this.expected = expected; }
      ${directive}
      public spend(pre: SigHashPreimage): void {
        assert(checkPreimage(pre));
        assert(extractHashPrevouts(pre) === this.expected);
      }
    }`;

  it('rejects extractHashPrevouts under ANYONECANPAY', () => {
    const errs = errorsOf(GUARD('/** @sighash ALL|ANYONECANPAY|FORKID */'));
    expect(errs.some((e) => /hashPrevouts.*zeroed under ANYONECANPAY/.test(e))).toBe(true);
  });

  it('rejects extractPrevOutputScript (companion-input) under ANYONECANPAY', () => {
    const src = `
      class Co extends StatefulSmartContract {
        readonly h0: ByteString;
        n: bigint;
        constructor(h0: ByteString, n: bigint) { super(h0, n); this.h0 = h0; this.n = n; }
        /** @sighash ALL|ANYONECANPAY|FORKID */
        public coSpend(): void {
          const s = extractPrevOutputScript(1n, this.h0);
          assert(len(s) > 0n);
        }
      }`;
    expect(errorsOf(src).some((e) => /companion input|prevout script/.test(e))).toBe(true);
  });

  it('ACCEPTS the same extractHashPrevouts read under the ALL default', () => {
    expect(compiles(GUARD(''))).toBe(true);
    expect(compiles(GUARD('/** @sighash ALL|FORKID */'))).toBe(true);
  });
});

describe('#123 field-usage validation — NONE', () => {
  it('rejects a state continuation under NONE', () => {
    const src = `
      class Counter extends StatefulSmartContract {
        n: bigint;
        constructor(n: bigint) { super(n); this.n = n; }
        /** @sighash NONE|FORKID */
        public bump(): void { this.n = this.n + 1n; }
      }`;
    expect(errorsOf(src).some((e) => /NONE commits to NO outputs|continuation/.test(e))).toBe(true);
  });

  it('ACCEPTS the same mutation under the ALL default', () => {
    const src = `
      class Counter extends StatefulSmartContract {
        n: bigint;
        constructor(n: bigint) { super(n); this.n = n; }
        public bump(): void { this.n = this.n + 1n; }
      }`;
    expect(compiles(src)).toBe(true);
  });
});

describe('#123 field-usage validation — SINGLE', () => {
  it('rejects a multi-output (non-same-index) continuation under SINGLE', () => {
    const src = `
      class Multi extends StatefulSmartContract {
        count: bigint;
        constructor(count: bigint) { super(count); this.count = count; }
        /** @sighash SINGLE|FORKID */
        public split(): void {
          this.addOutput(1000n, this.count);
          this.addOutput(2000n, this.count);
        }
      }`;
    expect(errorsOf(src).some((e) => /SINGLE commits ONLY to the output at this input/.test(e))).toBe(true);
  });

  it('ACCEPTS a single-output continuation under SINGLE', () => {
    const src = `
      class Counter extends StatefulSmartContract {
        n: bigint;
        constructor(n: bigint) { super(n); this.n = n; }
        /** @sighash SINGLE|FORKID */
        public bump(): void { this.n = this.n + 1n; }
      }`;
    expect(compiles(src)).toBe(true);
  });

  it('ACCEPTS the same multi-output method under the ALL default', () => {
    const src = `
      class Multi extends StatefulSmartContract {
        count: bigint;
        constructor(count: bigint) { super(count); this.count = count; }
        public split(): void {
          this.addOutput(1000n, this.count);
          this.addOutput(2000n, this.count);
        }
      }`;
    expect(compiles(src)).toBe(true);
  });
});
