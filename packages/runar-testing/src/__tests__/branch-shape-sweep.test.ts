/**
 * Exhaustive arm-shape sweep for the `if` node's multi-result contract.
 *
 * This is the evidence base the multi-result branch node was designed against,
 * kept as a regression gate. Two grids:
 *
 *  1. STATELESS (source-vs-script differential oracle: the AST-walking
 *     interpreter vs the compiled bytes on `@bsv/sdk`'s `Spend`). Five then-arm
 *     styles x five else-arm styles x both spender branches x both fold modes,
 *     in three merge arities (K=1 with else, K=1 without else, K=2). The arm
 *     styles are chosen so the two arms disagree on the VERDICT for the same
 *     input, which is what makes the merged local's slot observable.
 *
 *     At the commit before the node landed this grid produced **20
 *     divergences**, every one a GUARD BYPASS (`interpreter=false vm=true` —
 *     the compiled script accepting a spend the source rejects, the direction
 *     that loses funds). All 20 are one shape: one arm rebinds its local IN
 *     PLACE (net stack depth 0) while the other pushes a fresh slot (net +1),
 *     so `lowerIf`'s phase-3 balance padded the shorter arm with an EMPTY push
 *     and the parent registered THAT as the merged value. The fuzzer's
 *     `--execute` finding #8 (seed 1, contract 28) is one cell of this grid;
 *     see conformance/fuzz-regressions/entries/2026-08-06-branch-k1-empty-pad-guard-bypass.
 *
 *  2. STATEFUL (deploy -> call -> `Spend`, behind
 *     `MockProvider.enableBroadcastValidation()`, against a post-state
 *     hand-derived from the source). Property writes need a
 *     `StatefulSmartContract`, so the shapes that mix locals and properties —
 *     and the ones where the two arms disagree on property ORDER or on which
 *     property SET they write — live here. Before the node, six of these were
 *     broken: `MIX-else-D`, `MIX-else-A`, `P2-else-reorder` and
 *     `P-else-diffsets` were REFUSED at compile time by the containment
 *     invariant (legal Rúnar the compiler would not accept), while
 *     `MIX-else-E`, `K1-else-nonethen`, `K1-else-inplfresh`,
 *     `K1-else-freshinpl` and `MIX-else-propelse` compiled to scripts `Spend`
 *     rejects outright — permanently locked UTXOs.
 *
 * Every expectation below is derived from the source with x = 10, never from
 * compiler output.
 */

import { describe, it, expect } from 'vitest';
import { runDifferentialExecution } from '../oracle/index.js';
import { compile } from 'runar-compiler';
import { RunarContract, MockProvider, LocalSigner } from 'runar-sdk';
import { PrivateKey } from '@bsv/sdk';

const PRIV = PrivateKey.fromString('b1'.repeat(32), 16);
const PKH = PRIV.toPublicKey().toHash('hex') as string;

function stateless(body: string): string {
  return `import { SmartContract, assert, abs } from 'runar-lang';
class S extends SmartContract {
  readonly p13: bigint;
  constructor(p13: bigint) { super(p13); this.p13 = p13; }
  public go(flag: boolean, y: bigint): void {
${body}
  }
}
`;
}
const armVariants: Record<string, string> = {
  inplace: 'm = abs(m);', fresh: 'm = 43n;', fromParam: 'm = y;', selfplus: 'm = m + 1n;', none: '',
};
function contract(body: string, outputs: string): string {
  return `import { StatefulSmartContract } from 'runar-lang';
export class T extends StatefulSmartContract {
  p: bigint = 0n; a: bigint = 0n; b: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.p = seed; }
  public go(x: bigint, flag: bigint) {
${body}
    this.addOutput(1000n, ${outputs});
  }
}
`;
}
async function spend(source: string, fold: boolean, flag: bigint) {
  const r = compile(source, { fileName: 'T.runar.ts', disableConstantFolding: fold });
  if (!r.success || !r.artifact) throw new Error('COMPILE: ' + r.diagnostics.map(d => d.message).join('; '));
  const signer = new LocalSigner(PRIV.toString());
  const provider = new MockProvider();
  provider.enableBroadcastValidation();
  provider.addUtxo(await signer.getAddress(), { txid: 'ee'.repeat(32), outputIndex: 0, satoshis: 1_000_000, script: '76a914' + PKH + '88ac' });
  const c = new RunarContract(r.artifact as never, [0n]);
  c.connect(provider, signer);
  await c.deploy({ satoshis: 1000 });
  await c.call('go', [10n, flag], { satoshis: 1000 });
  return c.state as Record<string, unknown>;
}
const findings: string[] = [];
const SHAPES: Record<string, [string, string, string, string]> = {
  'MIX-else-D':      ['    let na: bigint = 1n;\n    if (flag > 0n) { this.p = x + 100n; na = x + 1n; } else { na = x + 2n; }', 'this.p, na, this.b', 'p=110,a=11,b=0', 'p=0,a=12,b=0'],
  'MIX-else-E':      ['    let na: bigint = 7n;\n    if (flag > 0n) { this.p = na * 2n; na = 5n; } else { na = x; }\n    this.p = 32n + this.p;', 'this.p, na, this.b', 'p=46,a=5,b=0', 'p=32,a=10,b=0'],
  'MIX-else-A':      ['    let na: bigint = 1n;\n    let nb: bigint = 2n;\n    if (flag > 0n) { this.p = x + 100n; na = x + 1n; } else { nb = x + 2n; }', 'this.p, na, nb', 'p=110,a=11,b=2', 'p=0,a=1,b=12'],
  'MIX-noelse':      ['    let na: bigint = 1n;\n    if (flag > 0n) { this.p = x + 100n; na = x + 1n; }', 'this.p, na, this.b', 'p=110,a=11,b=0', 'p=0,a=1,b=0'],
  'P2-noelse':       ['    if (flag > 0n) { this.a = x + 1n; this.b = x + 2n; }', 'this.p, this.a, this.b', 'p=0,a=11,b=12', 'p=0,a=0,b=0'],
  'P2-else':         ['    if (flag > 0n) { this.a = x + 1n; this.b = x + 2n; } else { this.a = 5n; this.b = 6n; }', 'this.p, this.a, this.b', 'p=0,a=11,b=12', 'p=0,a=5,b=6'],
  'P1-else':         ['    if (flag > 0n) { this.a = x + 1n; } else { this.a = 5n; }', 'this.p, this.a, this.b', 'p=0,a=11,b=0', 'p=0,a=5,b=0'],
  'P2-else-reorder': ['    if (flag > 0n) { this.a = 1n; this.b = 2n; } else { this.b = 3n; this.a = 4n; }', 'this.p, this.a, this.b', 'p=0,a=1,b=2', 'p=0,a=4,b=3'],
  'P-else-diffsets': ['    if (flag > 0n) { this.a = 1n; this.b = 2n; } else { this.a = 5n; }', 'this.p, this.a, this.b', 'p=0,a=1,b=2', 'p=0,a=5,b=0'],
  'P-else-disjoint': ['    if (flag > 0n) { this.a = 1n; } else { this.b = 2n; }', 'this.p, this.a, this.b', 'p=0,a=1,b=0', 'p=0,a=0,b=2'],
  'K1-else-nonethen':['    let na: bigint = 3n;\n    if (flag > 0n) { } else { na = x; }', 'this.p, na, this.b', 'p=0,a=3,b=0', 'p=0,a=10,b=0'],
  'K1-else-inplfresh':['    let na: bigint = 3n;\n    if (flag > 0n) { na = na + 1n; } else { na = 9n; }', 'this.p, na, this.b', 'p=0,a=4,b=0', 'p=0,a=9,b=0'],
  'K1-else-freshinpl':['    let na: bigint = 3n;\n    if (flag > 0n) { na = 9n; } else { na = na + 1n; }', 'this.p, na, this.b', 'p=0,a=9,b=0', 'p=0,a=4,b=0'],
  'MIX-else-propelse':['    let na: bigint = 1n;\n    if (flag > 0n) { na = x + 1n; } else { this.p = 7n; }', 'this.p, na, this.b', 'p=0,a=11,b=0', 'p=7,a=1,b=0'],
  'K2-else':         ['    let na: bigint = 1n;\n    let nb: bigint = 2n;\n    if (flag > 0n) { na = x + 1n; } else { nb = x + 2n; }', 'this.p, na, nb', 'p=0,a=11,b=2', 'p=0,a=1,b=12'],
  'K3-else':         ['    let na: bigint = 1n;\n    let nb: bigint = 2n;\n    let nc: bigint = 3n;\n    if (flag > 0n) { na = 4n; nb = 5n; } else { nc = 6n; }', 'na, nb, nc', 'p=4,a=5,b=3', 'p=1,a=2,b=6'],
  'P2-read-after':   ['    if (flag > 0n) { this.a = x + 1n; this.b = x + 2n; }\n    this.a = this.a + 100n;', 'this.p, this.a, this.b', 'p=0,a=111,b=12', 'p=0,a=100,b=0'],
  'dispatch-chain':  ['    if (x == 10n) { this.a = 1n; } else if (x == 11n) { this.a = 2n; } else { this.b = 3n; }', 'this.p, this.a, this.b', 'p=0,a=1,b=0', 'p=0,a=1,b=0'],
};

describe('branch arm-shape sweep', () => {
  it('stateless K1/K2 sweep', () => {
    const keys = Object.keys(armVariants);
    for (const ta of keys) for (const ea of keys) for (const flag of [true, false]) for (const fold of [true, false]) {
      for (const [label, body] of [
        [`K1 ${ta}/${ea}`, `    let m: bigint = abs(this.p13);\n    if (flag) { ${armVariants[ta]} } else { ${armVariants[ea]} }\n    assert(m < 3204n);\n    assert(y > -100000n);\n`],
        [`K1-noelse ${ta}`, `    let m: bigint = abs(this.p13);\n    if (flag) { ${armVariants[ta]} }\n    assert(m < 3204n);\n    assert(y > -100000n);\n`],
        [`K2 ${ta}/${ea}`, `    let m: bigint = abs(this.p13);\n    let n: bigint = 2n;\n    if (flag) { ${armVariants[ta]} n = m + 3n; } else { ${armVariants[ea]} n = 9n; }\n    assert(m < 3204n);\n    assert(n < 100n);\n    assert(y > -100000n);\n`],
      ] as Array<[string, string]>) {
        try {
          const r = runDifferentialExecution({ source: stateless(body), fileName: 'S.runar.ts', method: 'go', args: [flag, 7n], constructorArgs: { p13: 18025n }, disableConstantFolding: fold });
          if (!r.agrees) findings.push(`DIVERGE ${label} flag=${flag} fold=${fold}: interp=${r.interpreterAccepted} vm=${r.vmAccepted}`);
        } catch (e) { findings.push(`ERR ${label} flag=${flag} fold=${fold}: ${(e as Error).message.slice(0,90)}`); }
      }
    }
    expect(findings.join('\n')).toBe('');
  });

  it('stateful shape sweep', async () => {
    const f2: string[] = [];
    for (const [name, [body, outs, e1, e0]] of Object.entries(SHAPES)) {
      for (const fold of [true, false]) {
        for (const [flag, want] of [[1n, e1], [0n, e0]] as Array<[bigint, string]>) {
          try {
            const st = await spend(contract(body, outs), fold, flag);
            const got = `p=${st.p},a=${st.a},b=${st.b}`;
            if (got !== want) f2.push(`${name} fold=${fold} flag=${flag}: want ${want} got ${got}`);
          } catch (e) { f2.push(`${name} fold=${fold} flag=${flag}: FAIL ${(e as Error).message.slice(0,100)}`); }
        }
      }
    }
    expect(f2.join('\n')).toBe('');
  });
});
