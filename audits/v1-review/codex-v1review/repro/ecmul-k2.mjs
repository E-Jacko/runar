import { emitEcMulGen, emitMethod } from '../../../../packages/runar-compiler/dist/index.js';
import { ScriptVM } from '../../../../packages/runar-testing/dist/index.js';

const G2 =
  'c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5' +
  '1ae168fea63dc339a3c58419466ceaeef7f632653266d0e1236431a950cfe52a';

const ops = [{ op: 'push', value: 2n }];
emitEcMulGen((op) => ops.push(op));
const { scriptHex } = emitMethod({ name: 'ecmul-k2-repro', ops });
const result = new ScriptVM().executeHex(scriptHex);
const actual = result.stack.length
  ? Buffer.from(result.stack.at(-1)).toString('hex')
  : '(empty)';

console.log(JSON.stringify({ success: result.success, expected: G2, actual }, null, 2));
if (actual !== G2) process.exit(1);
