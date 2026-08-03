/**
 * Pass 6: Emit — converts Stack IR to Bitcoin Script bytes (hex string).
 *
 * Walks the StackOp list and encodes each operation as one or more Bitcoin
 * Script opcodes, producing both a hex-encoded script and a human-readable
 * ASM representation.
 */
import type { StackProgram, StackMethod } from '../ir/index.js';
import type { SourceMapping } from '../ir/index.js';
export declare const OPCODES: Record<string, number>;
export interface ConstructorSlot {
    paramIndex: number;
    byteOffset: number;
}
export interface CodeSepIndexSlot {
    /** Byte offset of the OP_0 placeholder in the template script */
    byteOffset: number;
    /** The template-relative codeSeparatorIndex value this placeholder represents */
    codeSepIndex: number;
}
/**
 * Byte range produced by a `raw_script` ANF node. The bytes are emitted
 * verbatim by `emitRawBytes`; the static analyzer reads these spans so it
 * can skip the contents (which are opaque, peephole-barrier-protected,
 * and not guaranteed to form a well-formed opcode stream).
 */
export interface RawScriptSpan {
    offset: number;
    length: number;
    inArity: number;
    outArity: number;
}
export interface EmitResult {
    /** Hex-encoded Bitcoin Script */
    scriptHex: string;
    /** Human-readable ASM representation */
    scriptAsm: string;
    /** Source mappings (opcode index → source location) */
    sourceMap: SourceMapping[];
    /** Byte offsets of constructor parameter placeholders */
    constructorSlots: ConstructorSlot[];
    /** Byte offsets of codeSepIndex placeholders in the script (OP_0 placeholders
     *  that the SDK must replace with the adjusted codeSeparatorIndex). */
    codeSepIndexSlots: CodeSepIndexSlot[];
    /** Byte offset of OP_CODESEPARATOR in the script (undefined if not present).
     *  For multi-method contracts, this is the LAST separator's offset. */
    codeSeparatorIndex?: number;
    /** Per-method OP_CODESEPARATOR byte offsets, in method emission order.
     *  Index 0 = first public method, index 1 = second, etc. */
    codeSeparatorIndices?: number[];
    /** Byte ranges produced by raw_script ANF nodes (opaque to the analyzer). */
    rawScriptSpans?: RawScriptSpan[];
}
/**
 * Emit a StackProgram as Bitcoin Script hex and ASM.
 *
 * For contracts with multiple public methods, the emitter generates a
 * method dispatch preamble that checks a function selector (the first
 * argument pushed by the spending transaction) and branches to the
 * corresponding method body.
 */
export declare function emit(program: StackProgram): EmitResult;
/**
 * Emit a single method's ops and return the result.
 * Useful for testing individual methods.
 */
export declare function emitMethod(method: StackMethod): EmitResult;
//# sourceMappingURL=06-emit.d.ts.map