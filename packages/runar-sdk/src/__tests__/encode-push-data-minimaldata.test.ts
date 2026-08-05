import { describe, it, expect } from 'vitest';
import { serializeState } from '../state.js';
import { encodeArg } from '../contract.js';
import type { StateField } from 'runar-ir-schema';

// ---------------------------------------------------------------------------
// MINIMALDATA-correct single-byte push encoding — for EXECUTED pushes only.
//
// BSV consensus + relay policy (SCRIPT_VERIFY_MINIMALDATA) require that a
// 1-byte data push whose payload is in {0x01..=0x10, 0x81} MUST use the
// corresponding minimal opcode (OP_1..OP_16 / OP_1NEGATE) rather than the
// direct push "01 NN". That applies to the contract-level arg encoder
// (encodePushData/encodeArg in contract.ts), which builds UNLOCKING scripts:
// the interpreter executes those pushes, and a non-minimal one is rejected at
// the relay layer with `non-mandatory-script-verify-flag (Data push larger
// than necessary)`. Byte-identical with the other six SDKs.
//
// It does NOT apply to the state serializer. #110 applied it there too, in all
// seven SDKs and none of the seven compilers, which silently desynchronised
// the state section from the compiler's on-chain codec and made any contract
// with a 1-byte OP_N-range ByteString state field permanently unspendable.
// The state section is raw data after OP_RETURN — never executed, therefore
// never MINIMALDATA-checked — and is framed `<len><data>` on both sides. See
// packages/runar-testing/src/__tests__/state-push-framing-vm.test.ts, which
// pins that against the real Script VM.
//
// 0x00 is deliberately EXCLUDED from the minimal set (C9 / S1): OP_0 pushes
// the EMPTY byte array, not a 1-byte 0x00, so the minimal encoding of a 1-byte
// 0x00 payload is the direct push "01 00" — exactly what the compiler's
// `encodePushBytesHex` (packages/runar-compiler/src/passes/push-encoding.ts)
// emits. The SDK previously special-cased 0x00 -> OP_0, which is not the
// inverse of any decoder (a real OP_0 decodes to the empty string, not "00")
// and diverges from the compiler's own byte-for-byte encoding.
// ---------------------------------------------------------------------------

// A single ByteString state field routes through the default (push-data)
// branch, so the whole serialized hex equals the framing of its value.
const byteStringField: StateField[] = [{ name: 'b', type: 'ByteString', index: 0 }];

describe('state serializer (serializeState) — <len><data>, NOT MINIMALDATA', () => {
  it('0x05 -> 0105 (direct push; OP_5 would not match the on-chain reader)', () => {
    expect(serializeState(byteStringField, { b: '05' })).toBe('0105');
  });
  it('0x00 -> 0100 (direct push, NOT OP_0 -- OP_0 pushes [], not [0x00])', () => {
    expect(serializeState(byteStringField, { b: '00' })).toBe('0100');
  });
  it('0x81 -> 0181 (direct push, not OP_1NEGATE)', () => {
    expect(serializeState(byteStringField, { b: '81' })).toBe('0181');
  });
  it('0x01..0x10 stay direct pushes', () => {
    for (let n = 1; n <= 16; n++) {
      const hex = n.toString(16).padStart(2, '0');
      expect(serializeState(byteStringField, { b: hex })).toBe('01' + hex);
    }
  });
  it('single byte outside range still direct-pushes (0x11 -> 0111)', () => {
    expect(serializeState(byteStringField, { b: '11' })).toBe('0111');
  });
  it('two-byte payload still direct-pushes (0x0011 -> 020011)', () => {
    expect(serializeState(byteStringField, { b: '0011' })).toBe('020011');
  });
});

describe('MINIMALDATA single-byte push — contract arg encoder (encodeArg)', () => {
  it('0x05 -> 55 (OP_5)', () => {
    expect(encodeArg('05')).toBe('55');
  });
  it('0x00 -> 0100 (direct push, NOT OP_0 -- OP_0 pushes [], not [0x00])', () => {
    expect(encodeArg('00')).toBe('0100');
  });
  it('0x81 -> 4f (OP_1NEGATE)', () => {
    expect(encodeArg('81')).toBe('4f');
  });
  it('single byte outside range still direct-pushes (0x11 -> 0111)', () => {
    expect(encodeArg('11')).toBe('0111');
  });
  it('two-byte payload still direct-pushes (0xdeadbeef -> 04deadbeef)', () => {
    expect(encodeArg('deadbeef')).toBe('04deadbeef');
  });
});
