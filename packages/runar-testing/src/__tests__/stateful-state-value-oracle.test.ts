import { describe, it, expect } from 'vitest';
import { runStatefulSpend } from '../oracle/real-crypto-execution.js';

// A stateful contract's on-chain state machine is only correct if the
// continuation output carries the state the SOURCE intends. accept/reject on the
// real Spend engine cannot see this: an ANF-level state-transition miscompile
// produces the SAME wrong state in both the SDK-built continuation output and
// the covenant that validates it, so Spend still ACCEPTS (audit finding #4).
// runStatefulSpend now decodes the continuation output's state from the on-chain
// call tx (byte layout only, via extractStateFromScript — not by re-running the
// transition) so it can be checked against an INDEPENDENT hand-authored value.

const CORRECT = `
import { StatefulSmartContract } from 'runar-lang';
export class Counter extends StatefulSmartContract {
  count: bigint;
  constructor(count: bigint) { super(count); this.count = count; }
  public increment() { this.count = this.count + 1n; }
}
`;

// Stand-in for a state-transition miscompile: count + 2 instead of count + 1.
// Self-consistent (the SDK-built output and the covenant both derive from this
// same source), so the real Spend engine ACCEPTS it — exactly the blind spot.
const WRONG = `
import { StatefulSmartContract } from 'runar-lang';
export class Counter extends StatefulSmartContract {
  count: bigint;
  constructor(count: bigint) { super(count); this.count = count; }
  public increment() { this.count = this.count + 2n; }
}
`;

describe('stateful continuation-state value oracle (audit #4)', () => {
  it('a correct transition is accepted AND carries the expected state', async () => {
    const r = await runStatefulSpend({
      source: CORRECT,
      fileName: 'Counter.runar.ts',
      method: 'increment',
      args: [],
      constructorArgs: [0n],
      signerKey: 'alice',
    });
    expect(r.vmAccepted, r.vmError).toBe(true);
    expect(r.continuationState).toEqual({ count: 1n });
  });

  it('a wrong transition is ACCEPTED by Spend but CAUGHT by the state-value check', async () => {
    const r = await runStatefulSpend({
      source: WRONG,
      fileName: 'Counter.runar.ts',
      method: 'increment',
      args: [],
      constructorArgs: [0n],
      signerKey: 'alice',
    });
    // accept/reject is blind — the wrong-but-self-consistent transition passes.
    expect(r.vmAccepted, r.vmError).toBe(true);
    // The independent state readback exposes it: on-chain state is count + 2, not
    // the intended count + 1. A harness checking only vmAccepted would ship this
    // contract's broken state machine — the audit #4 gap this oracle closes.
    expect(r.continuationState).toEqual({ count: 2n });
    expect(r.continuationState).not.toEqual({ count: 1n });
  });
});
