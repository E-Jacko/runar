/**
 * Deep-review finding C10: `RunarContract.fromUtxo` calls
 * `extractStateFromScript(artifact, utxo.script)` and only overwrites
 * `contract._state` `if (state)`. `extractStateFromScript` returns `null`
 * when the script has NO recognisable state section at all (no OP_RETURN
 * found) — i.e. state extraction failed ENTIRELY, not merely "this one
 * field has no on-chain slot" (that's issue #119's deliberate zero-fill of
 * unslotted CONSTRUCTOR args in `restoreConstructorArgs`, a distinct and
 * intentional code path this fix does not touch).
 *
 * Before this fix, a null extraction silently left `contract._state` at
 * whatever the constructor-initial defaults were (computed from
 * `restoreConstructorArgs`'s placeholder-`0n`-filled constructor args) —
 * presenting stale/deploy-time-looking values as if they were live
 * on-chain state, with no signal to the caller that reconnection failed.
 *
 * Fix: throw instead of silently falling back.
 */
import { describe, it, expect } from 'vitest';
import { RunarContract } from '../contract.js';
import { serializeState } from '../state.js';
import type { RunarArtifact, StateField } from 'runar-ir-schema';

function makeArtifact(
  overrides: Partial<RunarArtifact> & Pick<RunarArtifact, 'script' | 'abi'>,
): RunarArtifact {
  return {
    version: 'runar-v0.1.0',
    compilerVersion: '0.1.0',
    contractName: 'Test',
    asm: '',
    buildTimestamp: '2026-03-02T00:00:00.000Z',
    ...overrides,
  };
}

const FAKE_TXID = 'aa'.repeat(32);

describe('C10 — fromUtxo must not silently keep constructor-initial state when extraction fails', () => {
  it('throws when the UTXO script has no OP_RETURN state section at all', () => {
    const stateFields: StateField[] = [
      { name: 'count', type: 'bigint', index: 0 },
    ];
    const codeHex = '76a988ac';

    const artifact = makeArtifact({
      script: codeHex,
      abi: {
        constructor: { params: [{ name: 'count', type: 'bigint' }] },
        methods: [],
      },
      stateFields,
    });

    // No '6a' + state suffix at all — extractStateFromScript returns null.
    expect(() =>
      RunarContract.fromUtxo(artifact, {
        txid: FAKE_TXID,
        outputIndex: 0,
        satoshis: 10_000,
        script: codeHex,
      }),
    ).toThrow(/state/i);
  });

  it('sanity: still works (no throw) when the script DOES carry a valid state section', () => {
    const stateFields: StateField[] = [
      { name: 'count', type: 'bigint', index: 0 },
    ];
    const codeHex = '76a988ac';
    const stateHex = serializeState(stateFields, { count: 42n });
    const fullScript = codeHex + '6a' + stateHex;

    const artifact = makeArtifact({
      script: codeHex,
      abi: {
        constructor: { params: [{ name: 'count', type: 'bigint' }] },
        methods: [],
      },
      stateFields,
    });

    const contract = RunarContract.fromUtxo(artifact, {
      txid: FAKE_TXID,
      outputIndex: 0,
      satoshis: 10_000,
      script: fullScript,
    });
    expect(contract.state.count).toBe(42n);
  });
});
