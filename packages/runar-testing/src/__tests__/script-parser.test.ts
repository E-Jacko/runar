import { describe, it, expect } from 'vitest';
import { parseScript, isPushOpcode, isCheckSigOpcode } from '../analyzer/script-parser.js';

describe('parseScript', () => {
  it('parses P2PKH script: OP_DUP OP_HASH160 OP_0 OP_EQUALVERIFY OP_CHECKSIG', () => {
    // 76 a9 00 88 ac
    const ops = parseScript('76a90088ac');
    expect(ops).toHaveLength(5);

    expect(ops[0]!.name).toBe('OP_DUP');
    expect(ops[0]!.offset).toBe(0);
    expect(ops[0]!.opcode).toBe(0x76);

    expect(ops[1]!.name).toBe('OP_HASH160');
    expect(ops[1]!.offset).toBe(1);

    expect(ops[2]!.name).toBe('OP_0');
    expect(ops[2]!.offset).toBe(2);
    expect(isPushOpcode(ops[2]!)).toBe(true);

    expect(ops[3]!.name).toBe('OP_EQUALVERIFY');
    expect(ops[3]!.offset).toBe(3);

    expect(ops[4]!.name).toBe('OP_CHECKSIG');
    expect(ops[4]!.offset).toBe(4);
    expect(isCheckSigOpcode(ops[4]!)).toBe(true);
  });

  it('parses direct push (1-75 bytes)', () => {
    // Push 3 bytes: 0x03 followed by 3 data bytes
    const ops = parseScript('03aabbcc');
    expect(ops).toHaveLength(1);
    expect(ops[0]!.name).toBe('PUSH_3');
    expect(ops[0]!.data).toEqual(new Uint8Array([0xaa, 0xbb, 0xcc]));
    expect(ops[0]!.pushEncoding).toBe('direct');
    expect(ops[0]!.dataLength).toBe(3);
    expect(ops[0]!.size).toBe(4); // 1 opcode + 3 data
    expect(isPushOpcode(ops[0]!)).toBe(true);
  });

  it('parses OP_PUSHDATA1', () => {
    // OP_PUSHDATA1 (0x4c) + length byte (0x02) + 2 bytes data
    const ops = parseScript('4c02ff00');
    expect(ops).toHaveLength(1);
    expect(ops[0]!.name).toBe('OP_PUSHDATA1');
    expect(ops[0]!.data).toEqual(new Uint8Array([0xff, 0x00]));
    expect(ops[0]!.pushEncoding).toBe('pushdata1');
    expect(ops[0]!.dataLength).toBe(2);
    expect(ops[0]!.size).toBe(4); // 1 opcode + 1 length + 2 data
  });

  it('parses OP_PUSHDATA2', () => {
    // OP_PUSHDATA2 (0x4d) + 2-byte LE length (0x0300) + 3 bytes data
    const ops = parseScript('4d0300aabbcc');
    expect(ops).toHaveLength(1);
    expect(ops[0]!.name).toBe('OP_PUSHDATA2');
    expect(ops[0]!.data).toEqual(new Uint8Array([0xaa, 0xbb, 0xcc]));
    expect(ops[0]!.pushEncoding).toBe('pushdata2');
    expect(ops[0]!.dataLength).toBe(3);
  });

  it('parses OP_1 through OP_16', () => {
    // OP_1 = 0x51, OP_2 = 0x52, ..., OP_16 = 0x60
    const ops = parseScript('5152535460');
    expect(ops).toHaveLength(5);
    expect(ops[0]!.name).toBe('OP_1');
    expect(ops[0]!.pushEncoding).toBe('opN');
    expect(ops[1]!.name).toBe('OP_2');
    expect(ops[2]!.name).toBe('OP_3');
    expect(ops[3]!.name).toBe('OP_4');
    expect(ops[4]!.name).toBe('OP_16');
  });

  it('parses OP_1NEGATE', () => {
    const ops = parseScript('4f');
    expect(ops).toHaveLength(1);
    expect(ops[0]!.name).toBe('OP_1NEGATE');
    expect(ops[0]!.pushEncoding).toBe('opN');
  });

  it('parses empty script', () => {
    const ops = parseScript('');
    expect(ops).toHaveLength(0);
  });

  it('handles truncated direct push gracefully', () => {
    // Push 5 bytes, but only 2 bytes of data follow
    const ops = parseScript('05aabb');
    expect(ops).toHaveLength(1);
    expect(ops[0]!.name).toBe('PUSH_5');
    expect(ops[0]!.data).toEqual(new Uint8Array([0xaa, 0xbb]));
    expect(ops[0]!.size).toBe(3); // 1 opcode + 2 available data
  });

  it('handles truncated OP_PUSHDATA1 gracefully', () => {
    // OP_PUSHDATA1 with no length byte
    const ops = parseScript('4c');
    expect(ops).toHaveLength(1);
    expect(ops[0]!.name).toBe('OP_PUSHDATA1');
  });

  it('parses arithmetic opcodes', () => {
    // OP_ADD OP_SUB OP_MUL OP_DIV OP_MOD
    const ops = parseScript('9394959697');
    expect(ops.map((o) => o.name)).toEqual([
      'OP_ADD', 'OP_SUB', 'OP_MUL', 'OP_DIV', 'OP_MOD',
    ]);
  });

  it('parses flow control opcodes', () => {
    // OP_IF OP_ELSE OP_ENDIF OP_VERIFY OP_RETURN
    const ops = parseScript('6367686a69');
    expect(ops.map((o) => o.name)).toEqual([
      'OP_IF', 'OP_ELSE', 'OP_ENDIF', 'OP_RETURN', 'OP_VERIFY',
    ]);
  });

  it('tracks offsets correctly through mixed opcodes', () => {
    // OP_DUP(76) PUSH_2(02 aabb) OP_ADD(93)
    const ops = parseScript('7602aabb93');
    expect(ops).toHaveLength(3);
    expect(ops[0]!.offset).toBe(0); // OP_DUP
    expect(ops[1]!.offset).toBe(1); // PUSH_2
    expect(ops[1]!.size).toBe(3);   // 1 + 2
    expect(ops[2]!.offset).toBe(4); // OP_ADD
  });

  it('identifies checkSig opcodes', () => {
    // OP_CHECKSIG(ac), OP_CHECKSIGVERIFY(ad), OP_CHECKMULTISIG(ae), OP_CHECKMULTISIGVERIFY(af)
    const ops = parseScript('acadaeaf');
    expect(ops.every((op) => isCheckSigOpcode(op))).toBe(true);
  });

  it('non-sig opcodes are not checkSig', () => {
    const ops = parseScript('769376'); // DUP ADD DUP
    expect(ops.every((op) => !isCheckSigOpcode(op))).toBe(true);
  });
});
