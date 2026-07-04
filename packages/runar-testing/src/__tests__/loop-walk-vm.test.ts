/**
 * Runtime proof for the unrolled-loop outer-ref fix: a method param
 * referenced inside AND after a for-loop must compile to a Script that
 * actually executes correctly in the VM (previously the post-loop
 * reference was a silent OP_0/empty push — the interpreter passed while
 * the Script failed with "OP_SPLIT: position N out of range [0, 0]").
 *
 * The repro is the multi-input tx walk pattern (V003): walk up to 3
 * inputs of a serialized tx, advancing a running offset, then read the
 * byte at the final offset.
 */

import { describe, it, expect } from 'vitest';
import { compile } from 'runar-compiler';
import { TestSmartContract, expectScriptSuccess, expectScriptFailure } from '../helpers.js';

const LOOP_WALK_SOURCE = `
import { SmartContract, assert, substr, cat, bin2num } from 'runar-lang';
import type { ByteString } from 'runar-lang';

class LoopWalk extends SmartContract {
  readonly pad00: ByteString = "00" as ByteString;

  constructor() {
    super();
  }

  public walk(data: ByteString) {
    let off = 5n;
    for (let i = 0n; i < 3n; i++) {
      if (i < bin2num(cat(substr(data, 4n, 1n), this.pad00))) {
        const sl = bin2num(cat(substr(data, off + 36n, 1n), this.pad00));
        assert(sl < 253n);
        off = off + 36n + 1n + sl + 4n;
      }
    }
    const tail = bin2num(cat(substr(data, off, 1n), this.pad00));
    assert(tail === 7n);
  }
}
`;

// Serialized-input helpers: outpoint(36) + scriptLen(1) + script + sequence(4)
const input = (fill: string, scriptLen: number) =>
  fill.repeat(36) + scriptLen.toString(16).padStart(2, '0') + 'ab'.repeat(scriptLen) + 'ffffffff';

/** version(4) + inputCount(1) + inputs + tail byte */
const txData = (inputs: string[], tail: string) =>
  '00'.repeat(4) +
  inputs.length.toString(16).padStart(2, '0') +
  inputs.join('') +
  tail;

describe('compiled loop-walk executes correctly in the VM', () => {
  const result = compile(LOOP_WALK_SOURCE, { fileName: 'LoopWalk.runar.ts' });
  expect(result.success).toBe(true);
  const contract = TestSmartContract.fromArtifact(result.artifact!, []);

  it('walks 1 input', () => {
    expectScriptSuccess(contract.call('walk', [txData([input('11', 2)], '07')]));
  });

  it('walks 2 inputs (variable script lengths)', () => {
    expectScriptSuccess(
      contract.call('walk', [txData([input('11', 2), input('22', 1)], '07')]),
    );
  });

  it('walks 3 inputs', () => {
    expectScriptSuccess(
      contract.call('walk', [
        txData([input('11', 2), input('22', 1), input('33', 3)], '07'),
      ]),
    );
  });

  it('fails when the byte at the walked offset is wrong', () => {
    expectScriptFailure(
      contract.call('walk', [txData([input('11', 2), input('22', 1)], '09')]),
    );
  });
});
