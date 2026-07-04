/**
 * constructorArgs shape validation — `compile(opts.constructorArgs)` must
 * reject inputs that would silently bake nothing and emit placeholder
 * scripts that fail opaquely at runtime:
 *
 *  (a) positional arrays (natural guess, but keys match no property names)
 *  (b) keys that don't match any contract property (typos)
 *  (c) referenced readonly properties left unbaked after applying the args
 */

import { describe, it, expect } from 'vitest';
import { compile } from '../index.js';

// ---------------------------------------------------------------------------
// Contract sources
// ---------------------------------------------------------------------------

const HASH_LOCK_SOURCE = `
class HashLock extends SmartContract {
  readonly hashValue: Sha256;

  constructor(hashValue: Sha256) {
    super(hashValue);
    this.hashValue = hashValue;
  }

  public unlock(preimage: ByteString) {
    assert(sha256(preimage) === this.hashValue);
  }
}
`;

const TWO_PROP_SOURCE = `
class TwoProp extends SmartContract {
  readonly target: bigint;
  readonly unused: bigint;

  constructor(target: bigint, unused: bigint) {
    super(target, unused);
    this.target = target;
    this.unused = unused;
  }

  public check(x: bigint) {
    assert(x === this.target);
  }
}
`;

const HASH = 'aa'.repeat(32);

function errorMessages(result: ReturnType<typeof compile>): string {
  return result.diagnostics
    .filter((d) => d.severity === 'error')
    .map((d) => d.message)
    .join('\n');
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('constructorArgs validation', () => {
  it('rejects a positional array with a diagnostic error', () => {
    const result = compile(HASH_LOCK_SOURCE, {
      // Positional array — the shape RunarContract/TestSmartContract take,
      // but NOT what compile() takes. Previously baked nothing silently.
      constructorArgs: [HASH] as unknown as Record<string, string>,
    });

    expect(result.success).toBe(false);
    expect(errorMessages(result)).toMatch(/positional array/i);
  });

  it('rejects keys that match no contract property', () => {
    const result = compile(HASH_LOCK_SOURCE, {
      constructorArgs: { hashVal: HASH }, // typo: hashValue
    });

    expect(result.success).toBe(false);
    const msgs = errorMessages(result);
    expect(msgs).toContain("'hashVal'");
    expect(msgs).toContain('hashValue');
  });

  it('rejects when a referenced readonly property remains unbaked', () => {
    const result = compile(TWO_PROP_SOURCE, {
      // 'target' is referenced by check() but not provided.
      constructorArgs: { unused: 1n },
    });

    expect(result.success).toBe(false);
    expect(errorMessages(result)).toMatch(/'target'.*placeholder/s);
  });

  it('accepts an unreferenced readonly property left unbaked', () => {
    // 'unused' is never referenced by a method — DCE eliminates it, so
    // leaving it unbaked is fine.
    const result = compile(TWO_PROP_SOURCE, {
      constructorArgs: { target: 42n },
    });

    expect(result.success).toBe(true);
    expect(result.scriptHex).toBeDefined();
  });

  it('accepts a complete named record (baked script, no slots)', () => {
    const result = compile(HASH_LOCK_SOURCE, {
      constructorArgs: { hashValue: HASH },
    });

    expect(result.success).toBe(true);
    expect(result.artifact!.script).toContain(HASH);
    const slots = result.artifact!.constructorSlots;
    expect(slots === undefined || slots.length === 0).toBe(true);
  });

  it('still compiles placeholder artifacts when no constructorArgs given', () => {
    const result = compile(HASH_LOCK_SOURCE);
    expect(result.success).toBe(true);
    expect(result.artifact!.constructorSlots!.length).toBeGreaterThanOrEqual(1);
  });
});
