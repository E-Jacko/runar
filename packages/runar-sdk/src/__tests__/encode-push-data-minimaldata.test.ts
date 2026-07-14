import { describe, it, expect } from 'vitest';
import { serializeState } from '../state.js';
import { encodeArg } from '../contract.js';
import type { StateField } from 'runar-ir-schema';

// ---------------------------------------------------------------------------
// MINIMALDATA-correct single-byte push encoding.
//
// BSV consensus + relay policy (SCRIPT_VERIFY_MINIMALDATA) require that a
// 1-byte data push whose payload is in {0x00, 0x01..=0x10, 0x81} MUST use the
// corresponding minimal opcode (OP_0 / OP_1..OP_16 / OP_1NEGATE) rather than
// the direct push "01 NN". Both the state serializer (encodePushDataState in
// state.ts) and the contract-level arg encoder (encodePushData in contract.ts)
// must honor this so a 1-byte ByteString value does not emit a relay-rejected
// non-minimal direct push. Byte-identical with the other six SDKs.
// ---------------------------------------------------------------------------

// A single ByteString state field routes through the default (push-data)
// branch, so the whole serialized hex equals the push encoding of its value.
const byteStringField: StateField[] = [{ name: 'b', type: 'ByteString', index: 0 }];

describe('MINIMALDATA single-byte push — state serializer (serializeState)', () => {
  it('0x05 -> 55 (OP_5)', () => {
    expect(serializeState(byteStringField, { b: '05' })).toBe('55');
  });
  it('0x00 -> 00 (OP_0)', () => {
    expect(serializeState(byteStringField, { b: '00' })).toBe('00');
  });
  it('0x81 -> 4f (OP_1NEGATE)', () => {
    expect(serializeState(byteStringField, { b: '81' })).toBe('4f');
  });
  it('0x01..0x10 -> OP_1..OP_16', () => {
    for (let n = 1; n <= 16; n++) {
      const hex = n.toString(16).padStart(2, '0');
      const expected = (0x50 + n).toString(16);
      expect(serializeState(byteStringField, { b: hex })).toBe(expected);
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
  it('0x00 -> 00 (OP_0)', () => {
    expect(encodeArg('00')).toBe('00');
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
