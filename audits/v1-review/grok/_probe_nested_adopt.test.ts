import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract, MockProvider, LocalSigner } from 'runar-sdk';
import { PrivateKey } from '@bsv/sdk';

const PRIV = PrivateKey.fromString('b1'.repeat(32), 16);
const PKH = PRIV.toPublicKey().toHash('hex') as string;

const SRC = `import { StatefulSmartContract, assert } from 'runar-lang';

export class NestedAdopt extends StatefulSmartContract {
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
`;

async function run(fold: boolean, args: bigint[]) {
  const r = compile(SRC, {
    fileName: 'NestedAdopt.runar.ts',
    disableConstantFolding: fold,
  });
  if (!r.success || !r.artifact) {
    throw new Error('compile failed: ' + r.diagnostics.filter((d: any) => d.severity !== 'warning').map((d: any) => d.message).join('; '));
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
  const c = new RunarContract(r.artifact as never, [0n]);
  c.connect(provider, signer);
  await c.deploy({ satoshis: 1000 });
  await c.call('go', args, { satoshis: 1000 });
  return c.state as Record<string, unknown>;
}

describe('AUDIT PROBE NestedAdopt #149', () => {
  for (const fold of [true, false]) {
    const mode = fold ? 'fold-OFF' : 'fold-ON';
    it(`inner then (${mode})`, async () => {
      expect((await run(fold, [3n, 1n, 1n])).p).toBe(55n);
    });
    it(`inner else (${mode}) — THE DEFECT`, async () => {
      expect((await run(fold, [3n, 1n, 0n])).p).toBe(65n);
    });
    it(`outer skip (${mode})`, async () => {
      expect((await run(fold, [3n, 0n, 0n])).p).toBe(15n);
    });
  }
});
