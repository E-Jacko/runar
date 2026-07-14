#!/usr/bin/env ruby
# frozen_string_literal: true

# Ruby-tier CLI shim for the cross-tier canonicalJson (RFC 8785 / JCS)
# differential fuzzer (conformance/fuzzer/canonical-json-differential.ts).
#
# Protocol (single-shot, stdin -> stdout), mirrors the Go / Rust / Python /
# Zig shims:
#
#   {"mode":"json","value":<any JSON>}
#       Parse `value` with JSON.parse (Integer and Float are distinct Ruby
#       types, preserving the int-vs-float distinction the interop spec
#       relies on), run Runar::SDK::Envelope.canonical_json, print bytes,
#       exit 0.
#   {"mode":"utf16","key":"<string>","units":[<int>,...]}
#       Build {key => <string from UTF-16 units>} where lone surrogates are
#       emitted as their 3-byte WTF-8 form, so canonical_json's UTF-8 /
#       lone-surrogate guard rejects them.
#
#   On a typed rejection the shim prints "RUNAR_CANON_ERR:<message>" to
#   stdout and exits 3; any other failure exits 1.

$LOAD_PATH.unshift(File.expand_path('../lib', __dir__))

require 'json'
require 'runar/sdk'

def utf16_units_to_string(units)
  bytes = []
  i = 0
  n = units.length
  while i < n
    u = units[i]
    if u >= 0xD800 && u <= 0xDBFF && i + 1 < n && units[i + 1] >= 0xDC00 && units[i + 1] <= 0xDFFF
      cp = 0x10000 + ((u - 0xD800) << 10) + (units[i + 1] - 0xDC00)
      bytes.concat(codepoint_to_utf8(cp))
      i += 2
      next
    end
    bytes.concat(codepoint_to_utf8(u))
    i += 1
  end
  # Force UTF-8 so canonical_json's valid_encoding? / surrogate guard fires.
  bytes.pack('C*').force_encoding('UTF-8')
end

def codepoint_to_utf8(cp)
  if cp < 0x80
    [cp]
  elsif cp < 0x800
    [0xC0 | (cp >> 6), 0x80 | (cp & 0x3F)]
  elsif cp < 0x10000
    [0xE0 | (cp >> 12), 0x80 | ((cp >> 6) & 0x3F), 0x80 | (cp & 0x3F)]
  else
    [0xF0 | (cp >> 18), 0x80 | ((cp >> 12) & 0x3F), 0x80 | ((cp >> 6) & 0x3F), 0x80 | (cp & 0x3F)]
  end
end

raw = $stdin.read
begin
  req = JSON.parse(raw)
rescue StandardError => e
  warn "parse request: #{e}"
  exit 1
end

case req['mode']
when 'json'
  value = req['value']
when 'utf16'
  value = { req['key'].to_s => utf16_units_to_string(req['units'] || []) }
else
  warn "unknown mode #{req['mode'].inspect}"
  exit 1
end

begin
  out = Runar::SDK::Envelope.canonical_json(value)
rescue ArgumentError, TypeError, KeyError => e
  $stdout.write("RUNAR_CANON_ERR:#{e.message}")
  exit 3
end
$stdout.write(out)
