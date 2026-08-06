// round-trip only — absolute pin: packages/runar-sdk/src/__tests__/encode-push-data-minimaldata.test.ts
//
// Every case below is extractConstructorArgs(splice(encodeArg(x))) === x --
// encode and restore sharing the same implementation's assumptions. The
// literal expected bytes for encodeArg itself (the encoder this file only
// exercises indirectly) live in encode-push-data-minimaldata.test.ts.
/**
 * S1 — single-byte MINIMALDATA ByteString constructor-arg roundtrip.
 *
 * `encodeArg` (contract.ts, splicing a ctor arg into the code template via
 * `buildCodeScript`) and `extractConstructorArgs` / `interpretScriptElement`
 * (script-utils.ts, restoring a ctor arg from a deployed script) must be
 * inverses. Before the fix:
 *   - `encodeArg('00')` produced OP_0 ('00'), a 0-length push — wrong, since
 *     the compiler's `encodePushBytesHex` emits the direct push `01 00` for a
 *     1-byte zero payload (OP_0 pushes `[]`, not `[0x00]`).
 *   - Even with the encode side fixed, a ByteString ctor arg encoded via
 *     OP_1..OP_16 / OP_1NEGATE (payloads 0x01..0x10, 0x81) restored as ''
 *     because `interpretScriptElement`'s default (non-numeric) branch just
 *     forwarded `dataHex`, which `readScriptElement` leaves empty for those
 *     opcodes (they carry no separate data bytes — the opcode IS the value).
 *
 * Mirrors the artifact-construction style of constructor-slots.test.ts and
 * script-utils.test.ts (hand-built minimal artifacts, no compiler dependency).
 */
import { describe, it, expect } from 'vitest';
import { RunarContract } from '../contract.js';
import { extractConstructorArgs } from '../script-utils.js';
import type { RunarArtifact } from 'runar-ir-schema';

function makeArtifact(byteOffset: number, prefix: string, suffix: string): RunarArtifact {
  return {
    version: 'runar-v0.1.0',
    compilerVersion: '0.1.0',
    contractName: 'CtorByteString',
    asm: '',
    buildTimestamp: '2026-03-02T00:00:00.000Z',
    script: prefix + '00' + suffix,
    abi: {
      constructor: { params: [{ name: 'b', type: 'ByteString' }] },
      methods: [{ name: 'noop', params: [], isPublic: true }],
    },
    constructorSlots: [{ paramIndex: 0, byteOffset }],
  };
}

describe('S1 — single-byte ByteString ctor-arg MINIMALDATA roundtrip', () => {
  const cases: Array<{ label: string; hex: string }> = [
    { label: '0x00 (OP_0)', hex: '00' },
    { label: '0x01 (OP_1)', hex: '01' },
    { label: '0x05 (OP_5, mid OP_1..OP_16 range)', hex: '05' },
    { label: '0x10 (OP_16)', hex: '10' },
    { label: '0x81 (OP_1NEGATE)', hex: '81' },
    { label: 'multi-byte value', hex: 'aabbccdd' },
  ];

  for (const tc of cases) {
    it(`splices then restores ${tc.label}`, () => {
      // Template: OP_DUP <ctor slot placeholder> OP_DROP
      const artifact = makeArtifact(1, 'ab', '7c');
      const contract = new RunarContract(artifact, [tc.hex]);
      const lockingScript = contract.getLockingScript();

      const restored = extractConstructorArgs(artifact, lockingScript);
      expect(restored.b).toBe(tc.hex);
    });
  }
});
