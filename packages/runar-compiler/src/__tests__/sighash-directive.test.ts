import { describe, it, expect } from 'vitest';
import {
  parseSighashFlags,
  extractSighashDirective,
  describeSighash,
  SIGHASH_DEFAULT,
} from '../passes/sighash-directive.js';

describe('#123 @sighash flag grammar', () => {
  it('parses the common single-base combos', () => {
    expect(parseSighashFlags('ALL|FORKID')).toEqual({ value: 0x41 });
    expect(parseSighashFlags('SINGLE|FORKID')).toEqual({ value: 0x43 });
    expect(parseSighashFlags('NONE|FORKID')).toEqual({ value: 0x42 });
    expect(parseSighashFlags('ALL|ANYONECANPAY|FORKID')).toEqual({ value: 0xc1 });
  });

  it('is order-independent and tolerant of whitespace', () => {
    expect(parseSighashFlags(' FORKID | SINGLE ')).toEqual({ value: 0x43 });
  });

  it('default constant is ALL|FORKID', () => {
    expect(SIGHASH_DEFAULT).toBe(0x41);
    expect(parseSighashFlags('ALL|FORKID')).toEqual({ value: SIGHASH_DEFAULT });
  });

  it('rejects unknown flag names', () => {
    const r = parseSighashFlags('ALL|FORKD');
    expect('error' in r && r.error).toMatch(/unknown flag "FORKD"/);
  });

  it('rejects the nonsensical ALL|NONE combo on NAMES (not the aliased 0x03 value)', () => {
    const r = parseSighashFlags('ALL|NONE|FORKID');
    expect('error' in r && r.error).toMatch(/cannot combine base types/);
  });

  it('rejects SINGLE|ALL (two base types)', () => {
    const r = parseSighashFlags('SINGLE|ALL');
    expect('error' in r).toBe(true);
  });

  it('rejects a directive with no base type', () => {
    const r = parseSighashFlags('FORKID|ANYONECANPAY');
    expect('error' in r && r.error).toMatch(/exactly one base type/);
  });

  it('rejects duplicate flags', () => {
    const r = parseSighashFlags('SINGLE|SINGLE|FORKID');
    expect('error' in r && r.error).toMatch(/duplicate flag/);
  });

  it('rejects empty flag lists', () => {
    expect('error' in parseSighashFlags('')).toBe(true);
    expect('error' in parseSighashFlags('   ')).toBe(true);
  });

  // F2 (P2, leaning P1): FORKID is mandatory on BSV — the whole OP_PUSH_TX /
  // BIP-143 preimage machinery is FORKID-only, so a FORKID-less flag set
  // deploys a covenant whose derived signature can never verify (deploy-to-brick).
  it('rejects a base type without FORKID (deploy-to-brick)', () => {
    for (const flags of ['SINGLE', 'ALL', 'NONE', 'ALL|ANYONECANPAY']) {
      const r = parseSighashFlags(flags);
      expect('error' in r && r.error).toMatch(/FORKID is mandatory on BSV/);
    }
  });

  it('accepts the same flag sets once FORKID is added', () => {
    expect(parseSighashFlags('SINGLE|FORKID')).toEqual({ value: 0x43 });
    expect(parseSighashFlags('ALL|ANYONECANPAY|FORKID')).toEqual({ value: 0xc1 });
  });

  it('extracts from JSDoc block text', () => {
    expect(extractSighashDirective('/** @sighash SINGLE|FORKID */')).toEqual({ value: 0x43 });
    expect(extractSighashDirective('// @sighash NONE|FORKID')).toEqual({ value: 0x42 });
    expect(extractSighashDirective('/** no directive here */')).toBeNull();
  });

  it('describeSighash round-trips', () => {
    expect(describeSighash(0x41)).toBe('ALL|FORKID');
    expect(describeSighash(0x43)).toBe('SINGLE|FORKID');
    expect(describeSighash(0xc1)).toBe('ALL|ANYONECANPAY|FORKID');
    expect(describeSighash(0x42)).toBe('NONE|FORKID');
  });
});
