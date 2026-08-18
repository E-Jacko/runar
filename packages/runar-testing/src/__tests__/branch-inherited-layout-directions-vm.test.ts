/**
 * The two surfaces of the inherited-arm layout defect that the pinned #149
 * reduction (`nested-declared-results-arm-layout-vm.test.ts`) does NOT cover.
 *
 * That reduction pins exactly one direction: a stateless-shaped `assert` whose
 * else path fails `OP_VERIFY`, i.e. LOCKED funds. The three-way v1 audit found
 * two more surfaces of the same root cause, and a fix validated only against
 * the recorded reduction can leave either of them live:
 *
 *   A. WRONGLY-SPENDABLE (the mirror direction). Where the recorded case makes
 *      a true guard evaluate false, the same rotation makes a FALSE guard
 *      evaluate true. The contract's only spending condition is bypassed —
 *      an authorization failure, not an availability failure.
 *
 *   B. STATEFUL `addOutput` continuation. The merged local is read positionally
 *      alongside a live UNTOUCHED sibling by `this.addOutput(...)`, so the
 *      rotation crosses the two values inside the state continuation and the
 *      covenant fails inside its own `OP_NUM2BIN`.
 *
 * Both require the same two degrees of freedom as the recorded case: the inner
 * `if` must leave a live sibling it did NOT rebind in the region it inherited
 * from the enclosing arm, AND the outer `if` must have no `else`, so only one
 * outer path rearranges that region.
 */

import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract, MockProvider, LocalSigner } from 'runar-sdk';
import { PrivateKey } from '@bsv/sdk';
import { runTriModalExecution } from '../oracle/tri-modal-execution.js';

const PRIV = PrivateKey.fromString('b1'.repeat(32), 16);
const PKH = PRIV.toPublicKey().toHash('hex') as string;

// ---------------------------------------------------------------------------
// A. Wrongly-SPENDABLE: the guard is bypassed, not just locked.
// ---------------------------------------------------------------------------

const BYPASS_SRC = `import { SmartContract, assert } from 'runar-lang';

export class Bypass extends SmartContract {
  readonly q: bigint;
  constructor(q: bigint) { super(q); this.q = q; }

  public run5(param2: bigint): void {
    let br0: bigint = param2;
    const sib0: bigint = param2;
    if (param2 > -8n) {
      if (param2 <= 0n) { br0 = 0n; } else { br0 = 1n; }
    }
    assert(br0 < sib0);
  }
}
`;

describe('inherited-arm layout — wrongly-spendable direction', () => {
  // For each of these the SOURCE rejects: param2 <= 0 sets br0 = 0, and
  // sib0 == param2, so `br0 < sib0` is `0 < param2` which is false for every
  // param2 <= 0. The deployed script must reject too.
  for (const fold of [true, false]) {
    const mode = fold ? 'fold-OFF' : 'fold-ON';
    for (const v of [0n, -1n, -2n]) {
      it(`param2=${v} rejected by script as well as source (${mode})`, () => {
        const r = runTriModalExecution({
          source: BYPASS_SRC,
          fileName: 'Bypass.runar.ts',
          method: 'run5',
          args: [v],
          constructorArgs: { q: 1n },
          disableConstantFolding: fold,
        });
        expect(r.interpreterAccepted).toBe(false);
        // The defect makes the deployed script accept a spend the contract's
        // own guard rejects: anyone can spend the UTXO.
        expect(r.spendAccepted).toBe(false);
      });
    }

    // Control: a value the source genuinely accepts must stay spendable, so a
    // fix cannot "succeed" by rejecting everything.
    it(`param2=5 accepted by source and by script (${mode})`, () => {
      const r = runTriModalExecution({
        source: BYPASS_SRC,
        fileName: 'Bypass.runar.ts',
        method: 'run5',
        args: [5n],
        constructorArgs: { q: 1n },
        disableConstantFolding: fold,
      });
      expect(r.interpreterAccepted).toBe(true);
      expect(r.spendAccepted).toBe(true);
    });
  }
});

// ---------------------------------------------------------------------------
// B. Stateful `addOutput` continuation with a live untouched sibling.
// ---------------------------------------------------------------------------

const ADDOUTPUT_SRC = `import { StatefulSmartContract, assert } from 'runar-lang';
import type { PubKey } from 'runar-lang';

export class SibOut extends StatefulSmartContract {
  f0: bigint;
  f1: PubKey;

  constructor(f0: bigint, f1: PubKey) {
    super(f0, f1);
    this.f0 = f0;
    this.f1 = f1;
  }

  public step(p0: bigint) {
    assert(p0 >= 1n);
    let l0: bigint = this.f0;
    let l1: PubKey = this.f1;
    if (p0 > 0n) {
      if (p0 > 2000n) { l0 = 127n; } else { l0 = 17n; }
    }
    this.addOutput(1000n, l0, l1);
  }
}
`;

const PUB = '02' + 'a1'.repeat(32);

async function runStateful(fold: boolean, p0: bigint): Promise<Record<string, unknown>> {
  const r = compile(ADDOUTPUT_SRC, {
    fileName: 'SibOut.runar.ts',
    disableConstantFolding: fold,
  });
  if (!r.success || !r.artifact) {
    throw new Error('compile failed: ' + r.diagnostics
      .filter((d) => d.severity !== 'warning').map((d) => d.message).join('; '));
  }
  const signer = new LocalSigner(PRIV.toString());
  const provider = new MockProvider();
  provider.enableBroadcastValidation();
  provider.addUtxo(await signer.getAddress(), {
    txid: 'ee'.repeat(32),
    outputIndex: 0,
    satoshis: 1_000_000,
    script: '76a914' + PKH + '88ac',
  });
  const c = new RunarContract(r.artifact as never, [-128n, PUB]);
  c.connect(provider, signer);
  await c.deploy({ satoshis: 5000 });
  await c.call('step', [p0], { satoshis: 1000 });
  return c.state as Record<string, unknown>;
}

describe('inherited-arm layout — stateful addOutput with a live untouched sibling', () => {
  for (const fold of [true, false]) {
    const mode = fold ? 'fold-OFF' : 'fold-ON';

    // p0 = 1065: outer taken, inner ELSE arm -> l0 = 17; l1 untouched.
    it(`inner else-arm: continuation commits l0=17 and keeps the sibling (${mode})`, async () => {
      const st = await runStateful(fold, 1065n);
      expect(st.f0).toBe(17n);
      expect(st.f1).toBe(PUB);
    });

    // p0 = 3000: outer taken, inner THEN arm -> l0 = 127.
    it(`inner then-arm: continuation commits l0=127 and keeps the sibling (${mode})`, async () => {
      const st = await runStateful(fold, 3000n);
      expect(st.f0).toBe(127n);
      expect(st.f1).toBe(PUB);
    });
  }
});
