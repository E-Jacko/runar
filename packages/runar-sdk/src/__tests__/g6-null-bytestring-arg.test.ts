/**
 * Deep-review finding G6 (TypeScript tier): a `null` argument for a ByteString
 * parameter used to be resolved TYPE-blind — every null ByteString received the
 * `allPrevouts` outpoint stub. A caller who passed `null` for an ordinary
 * ByteString param (e.g. `memo`) therefore got real serialized outpoint bytes
 * spliced into their own parameter: the transaction builds and broadcasts, then
 * fails at script execution with an opaque error.
 *
 * The fix is a NAME gate, not a blanket throw. A blanket throw (as the review
 * originally prescribed) would break the documented `allPrevouts` auto-compute
 * convention that the token-ft integration tests rely on across tiers. So:
 * `allPrevouts` keeps auto-resolving, every other ByteString param fails loudly
 * at build time naming the offender, and `Sig`/`PubKey`/`SigHashPreimage` keep
 * their own auto-resolution rules.
 *
 * Mirrors the peer-tier tests added for the same finding:
 * `packages/runar-go/sdk_null_bytestring_arg_test.go`,
 * `packages/runar-rs/tests/null_bytestring_arg.rs`,
 * `packages/runar-py/tests/test_null_bytestring_arg.py`,
 * `packages/runar-rb/spec/sdk/null_bytestring_arg_spec.rb`,
 * `packages/runar-zig/src/sdk_null_bytestring_arg_test.zig`,
 * `packages/runar-java/.../NullByteStringArgTest.java`.
 */
import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract } from '../contract.js';
import { MockProvider } from '../providers/mock.js';
import { LocalSigner } from '../signers/local.js';
import type { RunarArtifact } from 'runar-ir-schema';

const SIGNER_KEY = '0000000000000000000000000000000000000000000000000000000000000007';

function compileSource(source: string, fileName: string): RunarArtifact {
  const result = compile(source, { fileName });
  if (!result.artifact) {
    const errors = (result.diagnostics || [])
      .filter((d: { severity: string }) => d.severity === 'error')
      .map((d: { message: string }) => d.message);
    throw new Error(`Compile failed: ${errors.join('; ')}`);
  }
  return result.artifact;
}

// A stateful contract with an ORDINARY ByteString param (`memo`) — not the
// `allPrevouts` convention name.
const MEMO_SRC = `
  import { StatefulSmartContract, ByteString, assert, len } from 'runar-lang';

  class MemoBump extends StatefulSmartContract {
    counter: bigint;
    constructor(counter: bigint) { super(counter); this.counter = counter; }
    public bump(memo: ByteString): void {
      assert(len(memo) >= 0n);
      this.counter = this.counter + 1n;
    }
  }
`;

async function deploy(src: string, fileName: string, ctorArgs: unknown[]) {
  const artifact = compileSource(src, fileName);
  const provider = new MockProvider();
  const signer = new LocalSigner(SIGNER_KEY);
  const address = await signer.getAddress();
  provider.addUtxo(address, {
    txid: SIGNER_KEY.slice(0, 64),
    outputIndex: 0,
    satoshis: 500_000,
    script: '76a914' + '00'.repeat(20) + '88ac',
  });
  const contract = new RunarContract(artifact, ctorArgs);
  contract.connect(provider, signer);
  await contract.deploy(provider, signer, {});
  return { contract, provider, signer };
}

describe('G6 — null for a non-auto-resolved ByteString param must fail loudly', () => {
  it('rejects a null `memo` instead of silently splicing outpoint bytes into it', async () => {
    const { contract } = await deploy(MEMO_SRC, 'MemoBump.runar.ts', [0n]);
    // Pre-fix this silently resolved to `00`.repeat(36 * nInputs) — the
    // allPrevouts stub — and later to REAL outpoint bytes, corrupting `memo`.
    await expect(contract.prepareCall('bump', [null])).rejects.toThrow(/memo/);
  });

  it("names the parameter and points at the 'allPrevouts' convention", async () => {
    const { contract } = await deploy(MEMO_SRC, 'MemoBump.runar.ts', [0n]);
    await expect(contract.prepareCall('bump', [null])).rejects.toThrow(/allPrevouts/);
  });

  it('an explicit empty ByteString is still accepted (the documented escape hatch)', async () => {
    const { contract } = await deploy(MEMO_SRC, 'MemoBump.runar.ts', [0n]);
    const prepared = await contract.prepareCall('bump', ['']);
    expect(prepared).toBeTruthy();
  });
});
