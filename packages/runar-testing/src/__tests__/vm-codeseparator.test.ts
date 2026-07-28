/**
 * OP_CODESEPARATOR (0xab) — previously the ScriptVM threw
 * "Unknown or disabled opcode: 0xab", so compiled STATEFUL Rúnar contracts
 * (which all carry a codeSeparator-trimmed scriptCode) could not be
 * replayed in the in-house VM at all.
 *
 * Post-Genesis BSV semantics: during execution OP_CODESEPARATOR marks the
 * position after itself as the scriptCode start for subsequent signature
 * ops. The VM now wraps the upstream @bsv/sdk `Spend` engine, so the trimmed
 * scriptCode is exercised by REAL secp256k1 verification, not a mock: the
 * signature below is only valid if the sighash was computed over the
 * post-separator subscript.
 */

import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { PrivateKey, Script, TransactionSignature, Hash } from '@bsv/sdk';
import { ScriptVM } from '../vm/index.js';
import { Opcode } from '../vm/opcodes.js';
import { TEST_KEYS } from '../test-keys.js';
import { hexToBytes } from '../vm/utils.js';

describe('ScriptVM OP_CODESEPARATOR', () => {
  it('executes a script containing 0xab instead of throwing', () => {
    // OP_1 OP_CODESEPARATOR OP_1 OP_ADD  =>  2
    const vm = new ScriptVM();
    const result = vm.executeHex('51ab5193');

    expect(result.error).toBeUndefined();
    expect(result.success).toBe(true);
  });

  it('tracks lastCodeSeparator as the offset after the separator', () => {
    const vm = new ScriptVM();
    expect(vm.lastCodeSeparator).toBe(-1);

    // bytes: 0x51 @0, 0xab @1, 0x51 @2, 0x93 @3
    const result = vm.executeHex('51ab5193');
    expect(result.success).toBe(true);
    expect(vm.lastCodeSeparator).toBe(2);
  });

  it('updates lastCodeSeparator on each executed separator', () => {
    // OP_1 0xab OP_1 0xab OP_ADD => last separator at offset 3, start = 4
    const vm = new ScriptVM();
    const result = vm.executeHex('51ab51ab93');
    expect(result.success).toBe(true);
    expect(vm.lastCodeSeparator).toBe(4);
  });

  it('does not track a separator inside a non-executing branch', () => {
    // OP_0 OP_IF 0xab OP_ENDIF OP_1
    const vm = new ScriptVM();
    const result = vm.executeHex('0063ab6851');
    expect(result.success).toBe(true);
    expect(vm.lastCodeSeparator).toBe(-1);
  });

  it('trims the scriptCode for a REAL OP_CHECKSIG (stateful scriptCode shape)', () => {
    // Locking: 0xab OP_CHECKSIG. The separator is chunk 0, so the scriptCode
    // the engine signs over is chunks[1..] = [OP_CHECKSIG] alone.
    const locking = new Uint8Array([Opcode.OP_CODESEPARATOR, Opcode.OP_CHECKSIG]);
    const key = TEST_KEYS[0]!;
    const scope = TransactionSignature.SIGHASH_ALL | TransactionSignature.SIGHASH_FORKID;
    const preimage = TransactionSignature.formatBytes({
      sourceTXID: '00'.repeat(32),
      sourceOutputIndex: 0,
      sourceSatoshis: 100000,
      transactionVersion: 1,
      otherInputs: [],
      outputs: [],
      inputIndex: 0,
      subscript: Script.fromHex('ac'), // post-separator subscript
      inputSequence: 0xffffffff,
      lockTime: 0,
      scope,
    });
    const digest = Hash.sha256(Array.from(preimage));
    const raw = PrivateKey.fromHex(key.privKey).sign(digest);
    const sig = new TransactionSignature(raw.r, raw.s, scope).toChecksigFormat();
    const pubkey = hexToBytes(key.pubKey);

    const unlocking = new Uint8Array([sig.length, ...sig, pubkey.length, ...pubkey]);
    const vm = new ScriptVM();
    const result = vm.execute(unlocking, locking);
    expect(result.error).toBeUndefined();
    expect(result.success).toBe(true);
  });

  it('REJECTS a garbage signature — checksig is real, not a fail-open mock', () => {
    // The pre-wrapper VM defaulted `checkSigCallback` to `() => true`, so this
    // exact script "succeeded" with 0xaa as the signature and 0xbb as the
    // pubkey. The upstream engine rejects it.
    const vm = new ScriptVM();
    const unlocking = new Uint8Array([0x01, 0xaa, 0x01, 0xbb]); // push 0xaa, push 0xbb
    const locking = new Uint8Array([Opcode.OP_CODESEPARATOR, Opcode.OP_CHECKSIG]);
    const result = vm.execute(unlocking, locking);
    expect(result.success).toBe(false);
    expect(result.error).toBeDefined();
  });

  it('step mode steps over OP_CODESEPARATOR without error', () => {
    const vm = new ScriptVM();
    vm.loadHex('', '51ab5193');

    const opcodes: string[] = [];
    let step = vm.step();
    while (step !== null) {
      expect(step.error).toBeUndefined();
      opcodes.push(step.opcode);
      step = vm.step();
    }

    expect(opcodes).toContain('OP_CODESEPARATOR');
    expect(vm.isComplete).toBe(true);
    expect(vm.isSuccess).toBe(true);
    expect(vm.lastCodeSeparator).toBe(2);
  });

  it('a compiled stateful contract script no longer dies at 0xab', () => {
    const source = `
import { StatefulSmartContract, assert } from 'runar-lang';

class Counter extends StatefulSmartContract {
  count: bigint;

  constructor(count: bigint) {
    super(count);
    this.count = count;
  }

  public increment() {
    this.count++;
  }
}
`;
    const result = compile(source, { fileName: 'Counter.runar.ts' });
    expect(result.success).toBe(true);
    expect(result.scriptHex).toContain('ab');

    // Without valid preimage args the script fails on its own asserts —
    // but it must no longer fail with "Unknown or disabled opcode: 0xab".
    const vm = new ScriptVM();
    const vmResult = vm.executeHex(result.scriptHex!);
    expect(vmResult.error ?? '').not.toMatch(/unknown or disabled opcode: 0xab/i);
  });
});
