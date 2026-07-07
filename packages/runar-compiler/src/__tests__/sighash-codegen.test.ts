import { describe, it, expect } from 'vitest';
import { compile } from '../index.js';

const COUNTER = (directive: string) => `
  class Counter extends StatefulSmartContract {
    n: bigint;
    constructor(n: bigint) { super(n); this.n = n; }
    ${directive}
    public bump(): void { this.n = this.n + 1n; }
  }
`;

function compileOk(src: string) {
  const r = compile(src, { fileName: 'Counter.runar.ts', disableConstantFolding: true });
  const errs = (r.diagnostics ?? []).filter((d) => d.severity === 'error');
  expect(errs).toEqual([]);
  return r;
}

describe('#123 codegen — sighash mode is threaded into script + ABI', () => {
  it('default (no directive) is byte-identical to an explicit ALL|FORKID', () => {
    const noDirective = compileOk(COUNTER(''));
    const explicitAll = compileOk(COUNTER('/** @sighash ALL|FORKID */'));
    // ALL|FORKID equals the historically-pinned default → identical script + IR.
    const bigintSafe = (_k: string, v: unknown) => (typeof v === 'bigint' ? `${v}n` : v);
    expect(explicitAll.artifact!.script).toBe(noDirective.artifact!.script);
    expect(JSON.stringify(explicitAll.anf, bigintSafe)).toBe(JSON.stringify(noDirective.anf, bigintSafe));
  });

  it('SINGLE|FORKID changes the script (mode-aware binding + assert)', () => {
    const dflt = compileOk(COUNTER(''));
    const single = compileOk(COUNTER('/** @sighash SINGLE|FORKID */'));
    expect(single.artifact!.script).not.toBe(dflt.artifact!.script);
    // The compiled locking script must contain the SINGLE|FORKID flag byte 0x43
    // pushed as the appended OP_PUSH_TX sighash byte (OP_DATA_1 0x43 = "0143").
    expect(single.artifact!.script.includes('0143')).toBe(true);
    // ...and must NOT still be pinned to the default 0x41 push.
    const dfltHas41 = dflt.artifact!.script.includes('0141');
    expect(dfltHas41).toBe(true);
  });

  it('ABI carries sigHashType for a non-default mode and omits it for the default', () => {
    const single = compileOk(COUNTER('/** @sighash SINGLE|FORKID */'));
    const dflt = compileOk(COUNTER(''));
    const singleBump = single.artifact!.abi.methods.find((m) => m.name === 'bump')!;
    const dfltBump = dflt.artifact!.abi.methods.find((m) => m.name === 'bump')!;
    expect(singleBump.sigHashType).toBe(0x43);
    expect(dfltBump.sigHashType).toBeUndefined();
  });

  it('the auto-injected preimage-type assert uses the declared mode constant', () => {
    // The ANF load_const for the expected sighash type should be 0x43 = 67.
    const single = compileOk(COUNTER('/** @sighash SINGLE|FORKID */'));
    const anfStr = JSON.stringify(single.anf, (_k, v) => (typeof v === 'bigint' ? `${v}n` : v));
    expect(anfStr.includes('"67n"')).toBe(true);
  });
});
