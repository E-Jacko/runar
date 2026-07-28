import fc from 'fast-check';
import { describe, it } from 'vitest';
import { arbExecCase, renderTypeScript, type ExecCase } from '../fuzzer/index.js';
import { runTriModalExecution } from '../oracle/index.js';

/**
 * Property-mode smoke test for the tri-modal execution-oracle generator
 * (issue #124). Every generated case must:
 *   (a) compile (a compile throw fails the property), and
 *   (b) produce ACCEPT/REJECT agreement across the ANF interpreter, `ScriptVM`
 *       (the @bsv/sdk Spend engine stepped opcode by opcode), and a strict
 *       full-consensus `Spend.validate()`.
 * fast-check shrinks any counterexample to a minimal (contract, inputs) repro.
 */
describe('arbExecCase — tri-modal agreement (loops + byte-ops + post-loop reads)', () => {
  it('all three engines agree over 300 generated cases (fixed seed)', () => {
    fc.assert(
      fc.property(arbExecCase, (c: ExecCase) => {
        const source = renderTypeScript(c.contract);
        const fileName = `${c.contract.name}.runar.ts`;
        const r = runTriModalExecution({
          source,
          fileName,
          method: c.method,
          args: c.args,
          constructorArgs: c.constructorArgs,
        });
        return r.agrees;
      }),
      { numRuns: 300, seed: 424242 },
    );
  });
});
