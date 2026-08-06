# frozen_string_literal: true

require 'spec_helper'
require 'openssl'

# The message digest these helpers commit to is a WIRE-PROTOCOL fact, not a
# style choice: `Runar::NistECDSA.pNNN_sign` exists to produce signatures that
# the compiled `verifyECDSA_PNNN` Bitcoin Script verifier will accept, and that
# verifier hashes with `OP_SHA256` on BOTH curves.
#
# P-384 normally pairs with SHA-384, and this module used to follow that
# convention -- so it signed SHA-384(msg) while the deployed script verified
# SHA-256(msg). Because `p384_verify` hashed the same wrong way, the Ruby
# example suite agreed with itself and passed; only the chain disagreed. Every
# P-384 signature the Ruby SDK produced was unspendable.
#
# SHA-384 is not available on-chain at all: it is SHA-512-based and 64-bit word
# arithmetic is not expressible in Bitcoin Script (issue #137). So the fix is
# the signer, not the verifier.
#
# These specs pin the digest against a hand-built OpenSSL verification that
# names the digest explicitly, rather than against `pNNN_verify` -- which would
# just reproduce whatever the signer did.
RSpec.describe Runar::NistECDSA do
  # Verify a raw r||s signature against an explicitly-named digest, without
  # going through this module's own verify path.
  def openssl_verify_raw(curve, msg_hex, sig_hex, pk_hex, digest, coord_len)
    group = OpenSSL::PKey::EC::Group.new(curve)
    point = OpenSSL::PKey::EC::Point.new(group, OpenSSL::BN.new(pk_hex, 16))
    asn1 = OpenSSL::ASN1::Sequence([
      OpenSSL::ASN1::Sequence([
        OpenSSL::ASN1::ObjectId('id-ecPublicKey'),
        OpenSSL::ASN1::ObjectId(curve)
      ]),
      OpenSSL::ASN1::BitString(point.to_octet_string(:uncompressed))
    ])
    key = OpenSSL::PKey::EC.new(asn1.to_der)

    sig = [sig_hex].pack('H*')
    r = OpenSSL::BN.new(sig[0, coord_len].unpack1('H*'), 16)
    s = OpenSSL::BN.new(sig[coord_len, coord_len].unpack1('H*'), 16)
    der = OpenSSL::ASN1::Sequence([OpenSSL::ASN1::Integer(r),
                                   OpenSSL::ASN1::Integer(s)]).to_der

    key.verify(digest.new, der, [msg_hex].pack('H*'))
  end

  let(:msg_hex) { '52c3ad6172206d657373616765' } # "Runar message"

  describe 'P-256' do
    let(:kp) { described_class.p256_keygen }
    let(:sig) { described_class.p256_sign(msg_hex, kp[:sk]) }

    it 'signs the SHA-256 digest the on-chain verifier commits to' do
      expect(openssl_verify_raw('prime256v1', msg_hex, sig, kp[:pk_compressed],
                                OpenSSL::Digest::SHA256, 32)).to be(true)
    end

    it 'produces a 64-byte raw r||s signature' do
      expect(sig.length).to eq(128)
    end
  end

  describe 'P-384' do
    let(:kp) { described_class.p384_keygen }
    let(:sig) { described_class.p384_sign(msg_hex, kp[:sk]) }

    it 'signs the SHA-256 digest the on-chain verifier commits to, NOT SHA-384' do
      expect(openssl_verify_raw('secp384r1', msg_hex, sig, kp[:pk_compressed],
                                OpenSSL::Digest::SHA256, 48)).to be(true)
    end

    it 'does not sign a SHA-384 digest' do
      expect(openssl_verify_raw('secp384r1', msg_hex, sig, kp[:pk_compressed],
                                OpenSSL::Digest::SHA384, 48)).to be(false)
    end

    it 'produces a 96-byte raw r||s signature' do
      expect(sig.length).to eq(192)
    end

    it 'round-trips through its own verifier' do
      expect(described_class.p384_verify(msg_hex, sig, kp[:pk_compressed])).to be(true)
    end
  end
end
