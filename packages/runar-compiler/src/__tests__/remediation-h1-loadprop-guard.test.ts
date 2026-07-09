import { describe, it, expect } from 'vitest';
import { lowerToStack } from '../passes/05-stack-lower.js';
import type { ANFProgram } from '../ir/index.js';

// ---------------------------------------------------------------------------
// H1 (#119 tail): lowerLoadProp must NOT silently coerce an unknown property
// onto constructor slot 0.
//
// A `load_prop` binding whose name is not a declared constructor-param property
// used to fall through to `paramIndex >= 0 ? paramIndex : 0`, emitting the
// placeholder for constructor slot 0 — an UNRELATED argument's deploy-time
// bytes — with no diagnostic. That is a silent-wrong-code path: the produced
// locking script splices the wrong value at that position.
//
// The hardened behaviour is a HARD ERROR with a clear diagnostic and the
// binding's source location, instead of the silent placeholder.
// ---------------------------------------------------------------------------

/**
 * Minimal ANF program with a real readonly constructor-param property `pk`
 * (constructor slot 0) plus a public method that loads a property `ghost`
 * that is NOT declared on the contract. `ghost` therefore reaches the
 * placeholder fallback with `paramIndex === -1`.
 */
function programWithUnknownLoadProp(): ANFProgram {
  return {
    contractName: 'Ghost',
    properties: [
      { name: 'pk', type: 'PubKey', readonly: true },
    ],
    methods: [
      {
        name: 'spend',
        params: [],
        isPublic: true,
        body: [
          {
            name: 't0',
            value: { kind: 'load_prop', name: 'ghost' },
            sourceLoc: { file: 'Ghost.runar.ts', line: 7, column: 4 },
          },
          { name: 't1', value: { kind: 'assert', value: 't0' } },
        ],
      },
    ],
  };
}

describe('H1 (#119 tail): lowerLoadProp placeholder guard', () => {
  it('throws on a load_prop for a property with no constructor slot (paramIndex === -1)', () => {
    expect(() => lowerToStack(programWithUnknownLoadProp())).toThrow(
      /ghost/,
    );
  });

  it('includes the offending property name and source location in the diagnostic', () => {
    let message = '';
    try {
      lowerToStack(programWithUnknownLoadProp());
    } catch (err) {
      message = (err as Error).message;
    }
    expect(message).toContain('ghost');
    expect(message).toContain('Ghost.runar.ts');
    expect(message).toContain('7');
  });

  it('still lowers a real constructor-param property to a placeholder without error', () => {
    const program: ANFProgram = {
      contractName: 'Ok',
      properties: [{ name: 'pk', type: 'PubKey', readonly: true }],
      methods: [
        {
          name: 'spend',
          params: [],
          isPublic: true,
          body: [
            { name: 't0', value: { kind: 'load_prop', name: 'pk' } },
            { name: 't1', value: { kind: 'assert', value: 't0' } },
          ],
        },
      ],
    };
    expect(() => lowerToStack(program)).not.toThrow();
  });
});
