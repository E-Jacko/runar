/**
 * Unit smoke tests for the real-crypto execution oracle (post-mortem
 * remediation #1). The exhaustive per-fixture coverage lives in
 * conformance/witnesses/real-crypto-execution.test.ts; these guard the
 * exported API surface (`runStatelessSigned` / `runStatefulSpend`) and the two
 * core mechanisms: a real single-input ECDSA checkSig, and a real stateful
 * deploy→call continuation with a tampered-output near-miss.
 */
import { describe, it, expect } from 'vitest';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { runStatelessSigned, runStatefulSpend, testKey } from '../oracle/index.js';

const CONFORMANCE = resolve(__dirname, '../../../../conformance/tests');

function readContract(name: string): { source: string; fileName: string } {
  const manifest = JSON.parse(
    readFileSync(resolve(CONFORMANCE, name, 'source.json'), 'utf8'),
  ) as { sources: Record<string, string> };
  const rel = manifest.sources['.runar.ts'];
  if (!rel) throw new Error(`${name}: source.json has no '.runar.ts' entry`);
  return { source: readFileSync(resolve(CONFORMANCE, name, rel), 'utf8'), fileName: rel.split('/').pop()! };
}

const hexBytes = (hex: string): Uint8Array => Uint8Array.from(Buffer.from(hex, 'hex'));

describe('runStatelessSigned — real ECDSA checkSig', () => {
  const { source, fileName } = readContract('basic-p2pkh');
  const alice = testKey('alice');

  it('accepts a real signature from the committed key and the interpreter agrees', () => {
    const r = runStatelessSigned({
      source,
      fileName,
      method: 'unlock',
      args: [{ signWith: 'alice' }, hexBytes(alice.pubKey)],
      constructorArgs: { pubKeyHash: alice.pubKeyHash },
    });
    expect(r.vmAccepted, r.vmError).toBe(true);
    expect(r.interpreterAccepted).toBe(true);
  });

  it('rejects the wrong committed key on the real Spend engine', () => {
    const bob = testKey('bob');
    const r = runStatelessSigned({
      source,
      fileName,
      method: 'unlock',
      args: [{ signWith: 'bob' }, hexBytes(bob.pubKey)],
      constructorArgs: { pubKeyHash: alice.pubKeyHash },
    });
    expect(r.vmAccepted).toBe(false);
  });
});

describe('runStatefulSpend — real checkPreimage continuation', () => {
  const { source, fileName } = readContract('stateful-counter');

  it('accepts a valid deploy→increment continuation on the real Spend engine', async () => {
    const r = await runStatefulSpend({
      source,
      fileName,
      method: 'increment',
      args: [],
      constructorArgs: [5n],
      signerKey: 'alice',
    });
    expect(r.vmAccepted, r.vmError).toBe(true);
  });

  it('rejects when the enforced continuation output is tampered (BUG-100 binding)', async () => {
    const r = await runStatefulSpend({
      source,
      fileName,
      method: 'increment',
      args: [],
      constructorArgs: [5n],
      signerKey: 'alice',
      tamperOutput: true,
    });
    expect(r.vmAccepted).toBe(false);
  });
});
