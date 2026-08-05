/**
 * The SDK's state-section serializer and the compiler's on-chain state
 * framing must be the same encoding.
 *
 * Reported privately (Ben Palmer, 2026-08-03) as "variable-length ByteString
 * state fields break the continuation output check". The actual trigger is
 * narrower: a ByteString state value of EXACTLY ONE byte whose value is in
 * {0x01..0x10, 0x81}. Multi-byte values, empty values, and 1-byte values
 * outside that set were always fine.
 *
 * Cause: #110 (4573b424 / bd7ec284) taught all seven SDKs' state serializers
 * the SCRIPT_VERIFY_MINIMALDATA rule — a 1-byte push in the OP_N range must
 * use OP_1..OP_16 / OP_1NEGATE. That rule is correct for UNLOCKING-script
 * pushes (`encodeArg`), which the interpreter executes. The state section is
 * not executed: it is raw data after OP_RETURN in the locking script, framed
 * as <len><data> by the compiler's on-chain writer (`emitPushDataEncode`,
 * 05-stack-lower.ts) and parsed as <len><data> by the on-chain reader. #110
 * changed only the seven SDKs, never the seven compilers, so from that
 * commit on the two sides disagreed:
 *
 *   value "05" -> SDK "55" (OP_5)   vs   on-chain "0105"
 *
 * Two faces, both fund-loss:
 *   - WRITE: the continuation the script rebuilds differs from the outputs
 *     the SDK actually serialised, so hashOutputs never matches;
 *   - READ: a contract DEPLOYED with such a value can't be spent at all —
 *     the on-chain reader takes 0x55 as a length-85 push and dies in
 *     OP_SPLIT on the first call.
 *
 * The fix restores <len><data> in the state serializer of all seven SDKs
 * (the pre-#110 encoding, which matched). `encodeArg` keeps the MINIMALDATA
 * rule — unlocking-script pushes really are executed.
 */

import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { RunarContract, MockProvider, LocalSigner, serializeState, deserializeState } from 'runar-sdk';
import { PrivateKey } from '@bsv/sdk';
import type { RunarArtifact, StateField } from 'runar-ir-schema';

const PRIV = PrivateKey.fromString('b1'.repeat(32), 16);
const PKH = PRIV.toPublicKey().toHash('hex') as string;

function compileOrThrow(source: string, fileName: string): RunarArtifact {
  const r = compile(source, { fileName });
  if (!r.success || !r.artifact) {
    throw new Error(`compile failed: ${r.diagnostics.map((d) => d.message).join('; ')}`);
  }
  return r.artifact as RunarArtifact;
}

async function deployAndCall(
  source: string,
  fileName: string,
  method: string,
  args: unknown[],
): Promise<Record<string, unknown>> {
  const artifact = compileOrThrow(source, fileName);
  const signer = new LocalSigner(PRIV.toString());
  const provider = new MockProvider();
  provider.enableBroadcastValidation();
  provider.addUtxo(await signer.getAddress(), {
    txid: 'ee'.repeat(32),
    outputIndex: 0,
    satoshis: 1_000_000,
    script: '76a914' + PKH + '88ac',
  });
  const contract = new RunarContract(artifact, [0n]);
  contract.connect(provider, signer);
  await contract.deploy({ satoshis: 1000 });
  await contract.call(method, args, { satoshis: 60_000 });
  return contract.state as Record<string, unknown>;
}

/** Carries a caller-supplied ByteString through the continuation. */
const CARRIER = `import { StatefulSmartContract, assert } from 'runar-lang';
import type { ByteString } from 'runar-lang';

export class Carrier extends StatefulSmartContract {
  closed: bigint = 0n;
  handle: ByteString = "" as ByteString;
  tail: bigint = 0n;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public put(h: ByteString, amount: bigint) {
    assert(this.closed == 0n);
    this.addOutput(amount, this.closed, h, this.tail);
  }
}
`;

/** Deployed with a 1-byte OP_N-range initial state value already in place. */
const PRESET = `import { StatefulSmartContract, assert } from 'runar-lang';
import type { ByteString } from 'runar-lang';

export class Preset extends StatefulSmartContract {
  closed: bigint = 0n;
  handle: ByteString = "05" as ByteString;
  constructor(seed: bigint) { super(seed); this.closed = seed; }
  public bump(amount: bigint) {
    assert(this.closed == 0n);
    this.addOutput(amount, this.closed, this.handle);
  }
}
`;

// Every 1-byte value the MINIMALDATA short-circuit touched, plus controls
// either side of it and multi-byte / empty cases.
const HANDLES = [
  '', '00', '01', '02', '05', '10', '11', '20', '7f', '80', '81', '82', 'ff',
  '0102', '0500', 'aabbcc', 'de'.repeat(40),
];

describe('state-section framing — SDK serializer vs on-chain reader/writer', () => {
  describe('write path: value survives the continuation on the real Script VM', () => {
    for (const handle of HANDLES) {
      const label = handle === '' ? '(empty)' : handle.length > 16 ? `${handle.slice(0, 8)}… (${handle.length / 2}B)` : handle;
      it(`handle=${label}`, async () => {
        const state = await deployAndCall(CARRIER, 'Carrier.runar.ts', 'put', [handle, 60_000n]);
        expect(state.handle).toBe(handle);
        expect(state.tail).toBe(0n);
      });
    }
  });

  it('read path: a contract deployed with a 1-byte OP_N-range value is spendable', async () => {
    const state = await deployAndCall(PRESET, 'Preset.runar.ts', 'bump', [60_000n]);
    expect(state.handle).toBe('05');
  });

  describe('unit: serializeState frames ByteString as <len><data>, like the on-chain writer', () => {
    const fields: StateField[] = [{ name: 'b', type: 'ByteString', index: 0 }];

    it('1-byte values in the OP_N range are NOT collapsed to OP_1..OP_16', () => {
      for (let n = 1; n <= 16; n++) {
        const hex = n.toString(16).padStart(2, '0');
        expect(serializeState(fields, { b: hex })).toBe('01' + hex);
      }
    });

    it('0x81 is not collapsed to OP_1NEGATE', () => {
      expect(serializeState(fields, { b: '81' })).toBe('0181');
    });

    it('0x00 keeps the direct push (unchanged by this fix)', () => {
      expect(serializeState(fields, { b: '00' })).toBe('0100');
    });

    it('empty stays a zero-length push', () => {
      expect(serializeState(fields, { b: '' })).toBe('00');
    });

    it('values outside the OP_N range and multi-byte values are unchanged', () => {
      expect(serializeState(fields, { b: '11' })).toBe('0111');
      expect(serializeState(fields, { b: '0011' })).toBe('020011');
    });

    it('round-trips through deserializeState for every 1-byte value', () => {
      for (let byte = 0; byte <= 0xff; byte++) {
        const hex = byte.toString(16).padStart(2, '0');
        const blob = serializeState(fields, { b: hex });
        expect(deserializeState(fields, blob)).toEqual({ b: hex });
      }
    });
  });
});
