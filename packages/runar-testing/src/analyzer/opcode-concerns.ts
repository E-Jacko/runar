/**
 * Opcode-level concern checks.
 *
 * Flags OP_CODESEPARATOR usage, inefficient push-data encoding, and
 * excessively large scripts.
 */

import type { ParsedOpcode } from './script-parser.js';
import type { AnalysisFinding } from './types.js';

/** OP_CODESEPARATOR byte value (0xab). */
const OP_CODESEPARATOR = 0xab;

/** Maximum script size before we flag it (500 KB). */
const LARGE_SCRIPT_THRESHOLD = 500_000;

/**
 * Check for opcode-level concerns in the parsed script.
 */
export function analyzeOpcodeConcerns(
  opcodes: ParsedOpcode[],
  scriptSizeBytes: number,
): AnalysisFinding[] {
  const findings: AnalysisFinding[] = [];

  // Check script size
  if (scriptSizeBytes > LARGE_SCRIPT_THRESHOLD) {
    findings.push({
      severity: 'info',
      code: 'LARGE_SCRIPT',
      message: `Script is ${scriptSizeBytes} bytes (${(scriptSizeBytes / 1024).toFixed(1)} KB) — consider if this is intentional`,
    });
  }

  for (const op of opcodes) {
    // Flag OP_CODESEPARATOR
    if (op.opcode === OP_CODESEPARATOR) {
      findings.push({
        severity: 'info',
        code: 'CODESEPARATOR_PRESENT',
        message: 'OP_CODESEPARATOR found — expected for stateful contracts, unusual otherwise',
        offset: op.offset,
        opcode: 'OP_CODESEPARATOR',
      });
    }

    // Check for inefficient push-data encoding
    if (op.pushEncoding && op.dataLength !== undefined) {
      const dataLen = op.dataLength;

      if (op.pushEncoding === 'pushdata1' && dataLen <= 75) {
        // OP_PUSHDATA1 used for data that fits in a direct push (0x01-0x4b)
        findings.push({
          severity: 'info',
          code: 'INEFFICIENT_PUSH',
          message: `OP_PUSHDATA1 used for ${dataLen}-byte data — direct push (opcode 0x${dataLen.toString(16).padStart(2, '0')}) would be more efficient`,
          offset: op.offset,
          opcode: 'OP_PUSHDATA1',
        });
      } else if (op.pushEncoding === 'pushdata2' && dataLen <= 255) {
        // OP_PUSHDATA2 used for data that fits in OP_PUSHDATA1
        findings.push({
          severity: 'info',
          code: 'INEFFICIENT_PUSH',
          message: `OP_PUSHDATA2 used for ${dataLen}-byte data — OP_PUSHDATA1 would be more efficient`,
          offset: op.offset,
          opcode: 'OP_PUSHDATA2',
        });
      } else if (op.pushEncoding === 'pushdata4' && dataLen <= 65535) {
        // OP_PUSHDATA4 used for data that fits in OP_PUSHDATA2
        findings.push({
          severity: 'info',
          code: 'INEFFICIENT_PUSH',
          message: `OP_PUSHDATA4 used for ${dataLen}-byte data — OP_PUSHDATA2 would be more efficient`,
          offset: op.offset,
          opcode: 'OP_PUSHDATA4',
        });
      }
    }
  }

  return findings;
}
