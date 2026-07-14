/**
 * Phase 5: Script size and resource measurement for FRI building blocks.
 *
 * Compiles minimal contracts for each operation and measures the resulting
 * Bitcoin Script size (in bytes). Results feed into BSVM's Gate 0 evaluation.
 */

import { describe, it } from 'vitest';
import { compile } from 'runar-compiler';

function scriptBytes(source: string, fileName: string): number {
  const result = compile(source, { fileName });
  if (!result.artifact) {
    throw new Error(`Compile failed: ${JSON.stringify(result.errors)}`);
  }
  return result.artifact.script.length / 2; // hex → bytes
}

function scriptAsm(source: string, fileName: string): string {
  const result = compile(source, { fileName });
  if (!result.artifact) {
    throw new Error(`Compile failed: ${JSON.stringify(result.errors)}`);
  }
  return result.artifact.asm;
}

// Contracts that isolate each operation
const contracts: Record<string, { source: string; fileName: string }> = {
  'Baby Bear add': {
    fileName: 'BBAdd.runar.ts',
    source: `
import { SmartContract, assert, bbFieldAdd } from 'runar-lang';
class BBAdd extends SmartContract {
  readonly expected: bigint;
  constructor(expected: bigint) { super(expected); this.expected = expected; }
  public verify(a: bigint, b: bigint) {
    assert(bbFieldAdd(a, b) === this.expected);
  }
}`,
  },
  'Baby Bear sub': {
    fileName: 'BBSub.runar.ts',
    source: `
import { SmartContract, assert, bbFieldSub } from 'runar-lang';
class BBSub extends SmartContract {
  readonly expected: bigint;
  constructor(expected: bigint) { super(expected); this.expected = expected; }
  public verify(a: bigint, b: bigint) {
    assert(bbFieldSub(a, b) === this.expected);
  }
}`,
  },
  'Baby Bear mul': {
    fileName: 'BBMul.runar.ts',
    source: `
import { SmartContract, assert, bbFieldMul } from 'runar-lang';
class BBMul extends SmartContract {
  readonly expected: bigint;
  constructor(expected: bigint) { super(expected); this.expected = expected; }
  public verify(a: bigint, b: bigint) {
    assert(bbFieldMul(a, b) === this.expected);
  }
}`,
  },
  'Baby Bear inv': {
    fileName: 'BBInv.runar.ts',
    source: `
import { SmartContract, assert, bbFieldInv } from 'runar-lang';
class BBInv extends SmartContract {
  readonly expected: bigint;
  constructor(expected: bigint) { super(expected); this.expected = expected; }
  public verify(a: bigint) {
    assert(bbFieldInv(a) === this.expected);
  }
}`,
  },
  'Ext4 mul (single component)': {
    fileName: 'Ext4Mul.runar.ts',
    source: `
import { SmartContract, assert, bbExt4Mul0 } from 'runar-lang';
class Ext4Mul extends SmartContract {
  readonly expected: bigint;
  constructor(expected: bigint) { super(expected); this.expected = expected; }
  public verify(a0: bigint, a1: bigint, a2: bigint, a3: bigint, b0: bigint, b1: bigint, b2: bigint, b3: bigint) {
    assert(bbExt4Mul0(a0, a1, a2, a3, b0, b1, b2, b3) === this.expected);
  }
}`,
  },
  'Ext4 mul (all 4 components)': {
    fileName: 'Ext4MulFull.runar.ts',
    source: `
import { SmartContract, assert, bbExt4Mul0, bbExt4Mul1, bbExt4Mul2, bbExt4Mul3 } from 'runar-lang';
class Ext4MulFull extends SmartContract {
  constructor() { super(); }
  public verify(a0: bigint, a1: bigint, a2: bigint, a3: bigint, b0: bigint, b1: bigint, b2: bigint, b3: bigint, e0: bigint, e1: bigint, e2: bigint, e3: bigint) {
    assert(bbExt4Mul0(a0, a1, a2, a3, b0, b1, b2, b3) === e0);
    assert(bbExt4Mul1(a0, a1, a2, a3, b0, b1, b2, b3) === e1);
    assert(bbExt4Mul2(a0, a1, a2, a3, b0, b1, b2, b3) === e2);
    assert(bbExt4Mul3(a0, a1, a2, a3, b0, b1, b2, b3) === e3);
  }
}`,
  },
  'Ext4 inv (single component)': {
    fileName: 'Ext4Inv.runar.ts',
    source: `
import { SmartContract, assert, bbExt4Inv0 } from 'runar-lang';
class Ext4Inv extends SmartContract {
  readonly expected: bigint;
  constructor(expected: bigint) { super(expected); this.expected = expected; }
  public verify(a0: bigint, a1: bigint, a2: bigint, a3: bigint) {
    assert(bbExt4Inv0(a0, a1, a2, a3) === this.expected);
  }
}`,
  },
  'Ext4 inv (all 4 components)': {
    fileName: 'Ext4InvFull.runar.ts',
    source: `
import { SmartContract, assert, bbExt4Inv0, bbExt4Inv1, bbExt4Inv2, bbExt4Inv3 } from 'runar-lang';
class Ext4InvFull extends SmartContract {
  constructor() { super(); }
  public verify(a0: bigint, a1: bigint, a2: bigint, a3: bigint, e0: bigint, e1: bigint, e2: bigint, e3: bigint) {
    assert(bbExt4Inv0(a0, a1, a2, a3) === e0);
    assert(bbExt4Inv1(a0, a1, a2, a3) === e1);
    assert(bbExt4Inv2(a0, a1, a2, a3) === e2);
    assert(bbExt4Inv3(a0, a1, a2, a3) === e3);
  }
}`,
  },
  'FRI colinearity check': {
    fileName: 'FRICheck.runar.ts',
    source: `
import {
  SmartContract, assert,
  bbFieldAdd, bbFieldSub, bbFieldMul, bbFieldInv,
  bbExt4Mul0, bbExt4Mul1, bbExt4Mul2, bbExt4Mul3
} from 'runar-lang';

class FRICheck extends SmartContract {
  constructor() { super(); }
  public verify(
    x: bigint,
    fx0: bigint, fx1: bigint, fx2: bigint, fx3: bigint,
    fnx0: bigint, fnx1: bigint, fnx2: bigint, fnx3: bigint,
    a0: bigint, a1: bigint, a2: bigint, a3: bigint,
    eg0: bigint, eg1: bigint, eg2: bigint, eg3: bigint
  ) {
    const s0 = bbFieldAdd(fx0, fnx0);
    const s1 = bbFieldAdd(fx1, fnx1);
    const s2 = bbFieldAdd(fx2, fnx2);
    const s3 = bbFieldAdd(fx3, fnx3);
    const inv2 = bbFieldInv(2n);
    const hs0 = bbFieldMul(s0, inv2);
    const hs1 = bbFieldMul(s1, inv2);
    const hs2 = bbFieldMul(s2, inv2);
    const hs3 = bbFieldMul(s3, inv2);
    const d0 = bbFieldSub(fx0, fnx0);
    const d1 = bbFieldSub(fx1, fnx1);
    const d2 = bbFieldSub(fx2, fnx2);
    const d3 = bbFieldSub(fx3, fnx3);
    const ad0 = bbExt4Mul0(a0, a1, a2, a3, d0, d1, d2, d3);
    const ad1 = bbExt4Mul1(a0, a1, a2, a3, d0, d1, d2, d3);
    const ad2 = bbExt4Mul2(a0, a1, a2, a3, d0, d1, d2, d3);
    const ad3 = bbExt4Mul3(a0, a1, a2, a3, d0, d1, d2, d3);
    const inv2x = bbFieldInv(bbFieldMul(2n, x));
    const at0 = bbFieldMul(ad0, inv2x);
    const at1 = bbFieldMul(ad1, inv2x);
    const at2 = bbFieldMul(ad2, inv2x);
    const at3 = bbFieldMul(ad3, inv2x);
    const g0 = bbFieldAdd(hs0, at0);
    const g1 = bbFieldAdd(hs1, at1);
    const g2 = bbFieldAdd(hs2, at2);
    const g3 = bbFieldAdd(hs3, at3);
    assert(g0 === eg0);
    assert(g1 === eg1);
    assert(g2 === eg2);
    assert(g3 === eg3);
  }
}`,
  },
};

// Merkle proof contracts at various depths
for (const depth of [4, 10, 20]) {
  contracts[`Merkle proof (depth ${depth})`] = {
    fileName: `Merkle${depth}.runar.ts`,
    source: `
import { SmartContract, assert, merkleRootSha256 } from 'runar-lang';
import type { ByteString } from 'runar-lang';
class Merkle${depth} extends SmartContract {
  readonly expectedRoot: ByteString;
  constructor(expectedRoot: ByteString) { super(expectedRoot); this.expectedRoot = expectedRoot; }
  public verify(leaf: ByteString, proof: ByteString, index: bigint) {
    const root = merkleRootSha256(leaf, proof, index, ${depth}n);
    assert(root === this.expectedRoot);
  }
}`,
  };
}

describe('Phase 5: Script Size Measurement', () => {
  const results: { name: string; bytes: number; display: string }[] = [];

  for (const [name, { source, fileName }] of Object.entries(contracts)) {
    it(`compiles: ${name}`, () => {
      const bytes = scriptBytes(source, fileName);
      const display =
        bytes < 1024
          ? `${bytes} bytes`
          : `${(bytes / 1024).toFixed(1)} KB`;
      results.push({ name, bytes, display });
      console.log(`  ${name}: ${display}`);
    });
  }

  it('summary table', () => {
    console.log('\n=== Script Size Measurements ===');
    console.log('| Operation | Script Size |');
    console.log('|---|---|');
    for (const r of results) {
      console.log(`| ${r.name} | ${r.display} |`);
    }
    console.log('================================\n');
  });
});
