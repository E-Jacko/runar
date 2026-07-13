import { describe, it, expect } from 'vitest';
import { runStatefulSpend } from '../oracle/real-crypto-execution.js';

// A near-miss reject only tests the on-chain script guard if the rejection
// actually comes FROM the guard. The old harness converted every exception —
// including an SDK/harness error thrown BEFORE the script engine ran — into
// vmAccepted=false, which a reject spec accepts as a "correct rejection". So a
// reject that fails for an unrelated SDK reason silently passes and the guard it
// was meant to exercise stops being tested (audit #12). `reachedEngine`
// distinguishes the two.

const COUNTER = `
import { StatefulSmartContract, assert } from 'runar-lang';
export class Counter extends StatefulSmartContract {
  count: bigint;
  constructor(count: bigint) { super(count); this.count = count; }
  public decrement() { assert(this.count > 0n); this.count = this.count - 1n; }
}
`;

describe('reject must reach the script engine (audit #12)', () => {
  it('a genuine tampered-output near-miss rejects ON THE ENGINE', async () => {
    const r = await runStatefulSpend({
      source: COUNTER,
      fileName: 'Counter.runar.ts',
      method: 'decrement',
      args: [],
      constructorArgs: [5n],
      signerKey: 'alice',
      tamperOutput: true,
    });
    expect(r.vmAccepted).toBe(false); // the covenant binding fails
    expect(r.reachedEngine).toBe(true); // ...and it failed at the guard, as intended
  });

  it('an SDK-side failure rejects BEFORE the engine — caught by reachedEngine', async () => {
    // A reject spend whose args differ from the accept spend (here an arg-count
    // mismatch — the audit's "per-spend args differ -> SDK-side throw" scenario)
    // makes RunarContract.call throw before any tx is broadcast. vmAccepted=false
    // looks like a "correct rejection" to the old harness, but the script guard
    // was never exercised.
    const r = await runStatefulSpend({
      source: COUNTER,
      fileName: 'Counter.runar.ts',
      method: 'decrement',
      args: [99n], // decrement() takes 0 args -> SDK throws pre-broadcast
      constructorArgs: [5n],
      signerKey: 'alice',
    });
    expect(r.vmAccepted).toBe(false); // looks rejected...
    expect(r.reachedEngine).toBe(false); // ...but never reached the script engine
    // A reject spec that relied only on vmAccepted would pass here even though
    // the on-chain guard was never tested — exactly the audit #12 blind spot.
  });
});
