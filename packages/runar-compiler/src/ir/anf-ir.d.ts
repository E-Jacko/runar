/**
 * ANF IR -- A-Normal Form intermediate representation (Pass 4 output).
 *
 * Every compound expression is decomposed into a flat sequence of
 * let-bindings whose right-hand sides are *simple* values: constants,
 * variable references, a single primitive operation, or a branch/loop.
 */
export interface ANFProgram {
    contractName: string;
    properties: ANFProperty[];
    methods: ANFMethod[];
}
export interface ANFProperty {
    name: string;
    type: string;
    readonly: boolean;
    initialValue?: string | bigint | boolean;
}
export interface ANFMethod {
    name: string;
    params: ANFParam[];
    body: ANFBinding[];
    isPublic: boolean;
}
export interface ANFParam {
    name: string;
    type: string;
}
/**
 * A single let-binding: `let <name> = <value>`
 *
 * Names follow the pattern `t0`, `t1`, ... and are scoped per method.
 */
export interface ANFBinding {
    name: string;
    value: ANFValue;
    /** Debug-only: source location of the originating AST node. Not part of conformance. */
    sourceLoc?: {
        file: string;
        line: number;
        column: number;
    };
}
export interface LoadParam {
    kind: 'load_param';
    name: string;
}
export interface LoadProp {
    kind: 'load_prop';
    name: string;
}
export interface LoadConst {
    kind: 'load_const';
    value: string | bigint | boolean;
}
export interface BinOp {
    kind: 'bin_op';
    op: string;
    left: string;
    right: string;
    result_type?: string;
}
export interface UnaryOp {
    kind: 'unary_op';
    op: string;
    operand: string;
    result_type?: string;
}
export interface Call {
    kind: 'call';
    func: string;
    args: string[];
}
export interface MethodCall {
    kind: 'method_call';
    object: string;
    method: string;
    args: string[];
}
export interface If {
    kind: 'if';
    cond: string;
    then: ANFBinding[];
    else: ANFBinding[];
}
export interface Loop {
    kind: 'loop';
    count: number;
    body: ANFBinding[];
    iterVar: string;
    start: bigint;
    step: 1 | -1;
}
export interface Assert {
    kind: 'assert';
    value: string;
    isAutoInjectedStateCheck?: boolean;
}
export interface UpdateProp {
    kind: 'update_prop';
    name: string;
    value: string;
}
export interface GetStateScript {
    kind: 'get_state_script';
}
export interface CheckPreimage {
    kind: 'check_preimage';
    preimage: string;
    /**
     * Issue #123: BIP-143 sighash flag the on-chain OP_PUSH_TX binding appends to
     * the derived signature (so the node re-derives the tx sighash under this
     * flag). Absent = default `ALL|FORKID` (0x41), byte-identical to the pinned
     * cross-tier binding blob. Only set for a method that declares a non-default
     * `@sighash` mode, keeping golden ANF unchanged for every existing contract.
     */
    sighashFlag?: number;
}
export interface DeserializeState {
    kind: 'deserialize_state';
    preimage: string;
}
export interface AddOutput {
    kind: 'add_output';
    satoshis: string;
    stateValues: string[];
    preimage: string;
}
export interface AddRawOutput {
    kind: 'add_raw_output';
    satoshis: string;
    scriptBytes: string;
}
/**
 * AddDataOutput — records an additional transaction output that is NOT a
 * state continuation. The output is included in the auto-computed
 * continuation hash (hashOutputs) in declaration order, after state
 * outputs and before the change output. The emit shape is identical to
 * `add_raw_output`: amount(8LE) + varint(scriptLen) + scriptBytes.
 *
 * Distinguished from `add_raw_output` only at the continuation-hash
 * composition stage: `add_data_output` refs are concatenated AFTER all
 * `add_output` (state) refs and BEFORE the change output.
 */
export interface AddDataOutput {
    kind: 'add_data_output';
    satoshis: string;
    scriptBytes: string;
}
export interface ArrayLiteral {
    kind: 'array_literal';
    elements: string[];
}
/**
 * RawScript — an opaque opcode-byte span with declared stack arity.
 *
 * Bytes are emitted verbatim during stack lowering and Bitcoin Script emit;
 * no re-encoding takes place. The compiler treats this node as a hard
 * barrier: the EC algebraic optimizer, the peephole optimizer, and the
 * static analyzer all leave it untouched, and dead-code elimination
 * treats it as side-effecting.
 *
 * Used by the `asm({...})` surface syntax and by the decompiler when a
 * span of bytes can't be lifted to higher-level Rúnar source. Keeping
 * the IR byte-canonical (not mnemonic-based) makes cross-compiler
 * conformance trivial.
 */
export interface RawScript {
    kind: 'raw_script';
    bytes: string;
    in_arity: number;
    out_arity: number;
}
export type ANFValue = LoadParam | LoadProp | LoadConst | BinOp | UnaryOp | Call | MethodCall | If | Loop | Assert | UpdateProp | GetStateScript | CheckPreimage | DeserializeState | AddOutput | AddRawOutput | AddDataOutput | ArrayLiteral | RawScript;
//# sourceMappingURL=anf-ir.d.ts.map