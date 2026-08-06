# frozen_string_literal: true

require 'spec_helper'
require 'json'

# Testing-gap remediation Phase A5 (Ruby tier): machine-checked gate on the
# always-ack MockProvider escape hatches (MockProvider.always_ack,
# disable_broadcast_validation, enable_broadcast_validation(false)).
#
# A spec file may only use one of those escape hatches if it has a matching
# entry in always_ack_allowlist.json. Enforced in BOTH directions: it fails on
# unlisted always-ack usage (someone quietly re-disabling the fund-safety net)
# AND on stale entries (a file that no longer needs always-ack, or that was
# deleted) — so the list can only shrink.
#
# Mirrors packages/runar-sdk/src/__tests__/always-ack-allowlist.test.ts,
# packages/runar-go/always_ack_allowlist_test.go and
# packages/runar-rs/tests/always_ack_allowlist.rs.
# rubocop:disable RSpec/DescribeClass
RSpec.describe 'always-ack MockProvider allowlist (Phase A5)' do
  # rubocop:enable RSpec/DescribeClass

  PACKAGE_ROOT = File.expand_path('../..', __dir__)
  ALLOWLIST_PATH = File.join(PACKAGE_ROOT, 'always_ack_allowlist.json')
  SELF_REL = 'spec/sdk/always_ack_allowlist_spec.rb'
  VALID_CATEGORIES = %w[structure-only negative-api fixture-shape pending-a3].freeze

  # Call-site patterns only. The DEFINITIONS in lib/runar/sdk/provider.rb are
  # outside the scanned tree (spec/ only), so the provider is never
  # self-referentially allowlisted.
  ALWAYS_ACK_PATTERN = /
    MockProvider\.always_ack |
    disable_broadcast_validation |
    enable_broadcast_validation\(\s*false\s*\)
  /x

  let(:allowlist) { JSON.parse(File.read(ALLOWLIST_PATH))['entries'] }

  let(:actual_usage) do
    Dir.glob(File.join(PACKAGE_ROOT, 'spec', '**', '*_spec.rb')).filter_map do |path|
      rel = path.delete_prefix("#{PACKAGE_ROOT}/")
      next if rel == SELF_REL

      rel if File.read(path).match?(ALWAYS_ACK_PATTERN)
    end.sort
  end

  it 'has a well-formed entry for every listed file' do
    allowlist.each do |e|
      expect(e['file'].to_s.strip).not_to be_empty
      expect(e['reason'].to_s.strip).not_to be_empty, "allowlist entry #{e['file']} has no reason"
      expect(VALID_CATEGORIES).to include(e['category']),
                                  "allowlist entry #{e['file']} has invalid category #{e['category'].inspect}"
    end
  end

  it 'names only files that exist' do
    missing = allowlist.reject { |e| File.exist?(File.join(PACKAGE_ROOT, e['file'])) }
    expect(missing.map { |e| e['file'] }).to eq([]),
                                             'always_ack_allowlist.json names files that no longer exist; remove them'
  end

  it 'carries no stale entries' do
    stale = allowlist.select { |e| File.exist?(File.join(PACKAGE_ROOT, e['file'])) }
                     .map { |e| e['file'] }
                     .reject { |f| actual_usage.include?(f) }
    expect(stale).to eq([]),
                     'always_ack_allowlist.json has entries for files that no longer use an ' \
                     'always-ack escape hatch — remove them (the allowlist must only shrink)'
  end

  it 'governs every always-ack usage in spec/' do
    listed = allowlist.map { |e| e['file'] }
    unlisted = actual_usage - listed
    expect(unlisted).to eq([]),
                        "Unlisted always-ack MockProvider usage:\n  - #{unlisted.join("\n  - ")}\n" \
                        'Add an entry to always_ack_allowlist.json with a file, reason and ' \
                        "category (#{VALID_CATEGORIES.join(' | ')}), or fix the spec to run " \
                        'under the default validating provider instead.'
  end
end
