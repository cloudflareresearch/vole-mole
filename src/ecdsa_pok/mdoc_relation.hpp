// EXPERIMENTAL: a zero-knowledge proof of an mdoc (ISO/IEC 18013-5) presentation, the VOLEitH
// counterpart of Longfellow's mdoc proof (version 7 of its circuits). Not part of the public API.
//
// Statement. Public: the issuer's public key, the session transcript, the document type, the time
// "now" (20 bytes, YYYY-MM-DDTHH:MM:SSZ), and 1 to MAX_ATTRIBUTES disclosed attributes (element
// identifier and CBOR-encoded value). The prover shows that it knows an MSO, an issuer signature
// on it, and a device signature, such that:
//
//   (a) the issuer's ECDSA-P256-SHA256 signature on the COSE Sig_structure of the MSO (as
//       COSE_PREFIX, a 2-byte length, and the tagged MSO, in at most MAX_BLOCKS SHA-256 blocks)
//       is valid under the issuer's key;
//   (b) the MSO has validFrom <= now <= validUntil, a device key Q, and valueDigests, and for each
//       attribute, the SHA-256 of an IssuerSignedItemBytes with that identifier and value (in the
//       weak sense of Longfellow's circuit: as patterns at secret offsets; see mdoc_binary.hpp);
//   (c) the device signature on the DeviceAuthentication of the transcript and document type (with
//       empty DeviceNameSpaces) is valid under Q.
//
// Both signatures are hidden entirely, as in Longfellow: the verifier learns nothing about Q, R, or
// s of either signature.
//
// Proof. A binary VOLEitH proof (mdoc_binary.hpp) shows (b), that e = SHA-256 of the
// Sig_structure, and that X = x(R), Q's coordinates, and X' = x(R') are less than p. A VOLEitH
// proof over F_p and F_n (mdoc_arith.hpp) shows the issuer's signature equation for e (as
// relation.hpp, with X = x(R)) and the device's for the public e' = SHA-256 of the device's
// Sig_structure (as hk_relation.hpp, with X' = x(R') and Q committed). They're linked as in
// relation.hpp (e and X, by Z_n, Z_p, Y_1, Y_2), and with a second link challenge, as in
// hk_relation.hpp (X', by Z_n', Z_p', and u1', u2' by Y_1', Y_2') and rr_relation.hpp (Q, by Z_q).
// The incomplete additions of the device's scalar multiplication are as in hk_arith.hpp: a prover
// that makes one exceptional either knows the device's private key (and so can sign) or hit a
// collision that offsets_are_sound() rules out.

#ifndef VOLE_MOLE_ECDSA_POK_MDOC_RELATION_HPP
#define VOLE_MOLE_ECDSA_POK_MDOC_RELATION_HPP

#include "vole_mole/ecdsa_pok.hpp"
#include "vole_mole/random.hpp"

#include "dst.hpp"
#include "ecdsa_pok/arith.hpp"
#include "ecdsa_pok/bin_ops.hpp"
#include "ecdsa_pok/cbor.hpp"
#include "ecdsa_pok/hk_relation.hpp"
#include "ecdsa_pok/link.hpp"
#include "ecdsa_pok/mdoc_arith.hpp"
#include "ecdsa_pok/mdoc_binary.hpp"
#include "ecdsa_pok/relation.hpp"
#include "ecdsa_pok/rr_relation.hpp" // bin_prg_of
#include "ecdsa_pok/sha256_circuit.hpp"
#include "p256/curve.hpp"
#include "p256/field.hpp"
#include "sha256/sha256.hpp"
#include "voleith.hpp"
#include "voleith_p256/voleith.hpp"

#include "hash.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <functional>
#include <optional>
#include <span>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

namespace vole_mole::ecdsa_pok::detail::mdoc {

namespace vp = vole_mole::voleith_p256;

struct Attribute {
    std::string id;             // elementIdentifier
    std::vector<uint8_t> value; // the CBOR encoding of elementValue
};

// The verifier's request: the whole statement.
struct Request {
    PublicKey issuer_pk;             // SEC1 uncompressed
    std::vector<uint8_t> transcript; // SessionTranscript, CBOR encoded
    std::string doc_type;
    std::array<uint8_t, DATE_BYTES> now;
    std::vector<Attribute> attributes;
};

template <size_t NA, Vole V, BinPrg PRG> struct Scheme {
    using Bin = BinRelation<NA, V == Vole::small, PRG>;
    using VP = std::conditional_t<V == Vole::small, vp::Small,
                                  std::conditional_t<V == Vole::medium, vp::Medium, vp::Fast>>;
    using Arith = vp::Layout<ArithRelation, VP>;

    static constexpr size_t BIN_BYTES = vole_mole::detail::PROOF_BYTES<Bin>;
    static constexpr size_t ARITH_BYTES = Arith::PROOF_BYTES;
    static constexpr size_t OFF_BIN = 0;
    static constexpr size_t OFF_ARITH = OFF_BIN + BIN_BYTES;
    static constexpr size_t OFF_Z = OFF_ARITH + ARITH_BYTES; // the link values (LinkValue)
    static constexpr size_t OFF_Y = OFF_Z + NUM_Z * Z_BYTES; // the issuer's Y_i, then the device's
    static constexpr size_t PROOF_BYTES = OFF_Y + 2 * NUM_Y_CHECKS * Y_BYTES;
};

// CBOR headers.
inline void cbor_header(std::vector<uint8_t>& out, uint8_t major, size_t n) {
    const auto m = static_cast<uint8_t>(major << 5);
    if (n < 24) {
        out.push_back(static_cast<uint8_t>(m | n));
    } else if (n < 256) {
        out.push_back(m | 24);
        out.push_back(static_cast<uint8_t>(n));
    } else if (n < 65536) {
        out.push_back(m | 25);
        out.push_back(static_cast<uint8_t>(n >> 8));
        out.push_back(static_cast<uint8_t>(n));
    } else {
        out.push_back(m | 26);
        for (int i = 3; i >= 0; --i) {
            out.push_back(static_cast<uint8_t>(n >> (8 * i)));
        }
    }
}
inline void append(std::vector<uint8_t>& out, std::span<const uint8_t> b) {
    out.insert(out.end(), b.begin(), b.end());
}
inline void append(std::vector<uint8_t>& out, const std::string& s) {
    out.insert(out.end(), s.begin(), s.end());
}

// The COSE Sig_structure that the device signs: ["Signature1", {1: -7}, h'', payload] with the
// detached payload DeviceAuthenticationBytes = #6.24(bstr .cbor ["DeviceAuthentication",
// SessionTranscript, DocType, #6.24(bstr .cbor {})]), as Longfellow's compute_transcript_hash.
inline std::vector<uint8_t> device_sig_structure(std::span<const uint8_t> transcript,
                                                 const std::string& doc_type) {
    std::vector<uint8_t> da = {0x84};
    cbor_header(da, 3, 20);
    append(da, std::string("DeviceAuthentication"));
    append(da, transcript);
    cbor_header(da, 3, doc_type.size());
    append(da, doc_type);
    append(da, std::array<uint8_t, 4>{0xD8, 0x18, 0x41, 0xA0});
    std::vector<uint8_t> dab = {0xD8, 0x18};
    cbor_header(dab, 2, da.size());
    append(dab, da);
    std::vector<uint8_t> out = {0x84, 0x6A, 'S', 'i',  'g',  'n',  'a',  't', 'u',
                                'r',  'e',  '1', 0x43, 0xA1, 0x01, 0x26, 0x40};
    cbor_header(out, 2, dab.size());
    append(out, dab);
    return out;
}

// The patterns of an attribute (see mdoc_binary.hpp).
inline std::vector<uint8_t> id_pattern(const Attribute& a) {
    std::vector<uint8_t> out(ELEMENT_ID.begin(), ELEMENT_ID.end());
    cbor_header(out, 3, a.id.size());
    append(out, a.id);
    return out;
}
inline std::vector<uint8_t> value_pattern(const Attribute& a) {
    std::vector<uint8_t> out(ELEMENT_VALUE.begin(), ELEMENT_VALUE.end());
    append(out, a.value);
    return out;
}

// The public values, from the request.
struct Public {
    Digest mu;
    Tables issuer_tables;
    Fn device_e; // SHA-256 of the device's Sig_structure, reduced modulo n
    BinPublic bin;
};

inline Digest statement_digest(const Request& req, Vole vole, BinPrg prg) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_MDOC_STATEMENT_DST);
    h.update_byte(std::to_underlying(vole));
    h.update_byte(std::to_underlying(prg));
    h.update(req.issuer_pk);
    auto part = [&](std::span<const uint8_t> b) {
        const uint64_t v = b.size();
        for (size_t i = 0; i < 8; ++i) {
            h.update_byte(static_cast<uint8_t>(v >> (8 * i)));
        }
        h.update(b);
    };
    auto str = [&](const std::string& s) {
        part(std::span(reinterpret_cast<const uint8_t*>(s.data()), s.size()));
    };
    part(req.transcript);
    str(req.doc_type);
    h.update(req.now);
    part(std::array<uint8_t, 1>{static_cast<uint8_t>(req.attributes.size())});
    for (const auto& a : req.attributes) {
        str(a.id);
        part(a.value);
    }
    Digest out;
    h.finalize(out);
    return out;
}

// The public values: nothing if the request is malformed, or in the degenerate cases of the
// issuer's tables (which happen with negligible probability).
inline std::optional<Public> make_public(const Request& req, Vole vole, BinPrg prg) {
    if (req.attributes.empty() || req.attributes.size() > MAX_ATTRIBUTES) {
        return std::nullopt;
    }
    const auto qi = p256::decode_point(req.issuer_pk);
    if (!qi) {
        return std::nullopt;
    }
    Public out;
    out.mu = statement_digest(req, vole, prg);
    out.device_e = Fn::reduce_32(sha256::hash(device_sig_structure(req.transcript, req.doc_type)));
    try {
        out.issuer_tables = detail::make_tables(*qi);
    } catch (const std::runtime_error&) {
        return std::nullopt;
    }
    out.bin.now = req.now;
    for (const auto& a : req.attributes) {
        out.bin.ei.push_back(id_pattern(a));
        out.bin.ev.push_back(value_pattern(a));
    }
    return out;
}

// What the prover finds in the DeviceResponse.
struct Parsed {
    std::vector<uint8_t> sig_structure; // the issuer's signed message
    p256::Signature issuer_sig, device_sig;
    Affine q; // the device key
    std::array<uint8_t, DATE_BYTES> valid_from, valid_until;
    std::vector<ItemValues> items;
    std::vector<size_t> windows;
};

inline p256::Signature to_sig(std::span<const uint8_t> b) {
    if (b.size() != 64) {
        throw std::invalid_argument("mdoc: invalid signature");
    }
    p256::Signature s;
    std::copy_n(b.begin(), 32, s.r.begin());
    std::copy_n(b.begin() + 32, 32, s.s.begin());
    return s;
}

inline size_t find(std::span<const uint8_t> hay, std::span<const uint8_t> needle) {
    const auto it = std::ranges::search(hay, needle);
    if (it.empty()) {
        throw std::invalid_argument("mdoc: pattern not found in the MSO");
    }
    return static_cast<size_t>(it.begin() - hay.begin());
}

// The item's fields (see ItemValues), from its IssuerSignedItemBytes.
inline ItemValues parse_item(std::span<const uint8_t> tagged) {
    if (tagged.size() < 56 || tagged.size() > ITEM_MAX_LEN || tagged[0] != 0xD8 ||
        tagged[1] != 0x18 || tagged[2] != 0x58 || tagged[4] != 0xA4) {
        throw std::invalid_argument("mdoc: unsupported IssuerSignedItemBytes");
    }
    const auto item = cbor::decode(tagged.subspan(4));
    if (!item) {
        throw std::invalid_argument("mdoc: invalid IssuerSignedItem");
    }
    ItemValues v{};
    const auto padded = sha256::pad(tagged);
    std::ranges::copy(padded, v.buf.begin());
    const auto traces = sha256_traces(padded);
    v.traces = {traces[0], traces[1]};
    v.len = tagged.size();
    const auto in = tagged.subspan(4);
    for (size_t j = 0; j < 4; ++j) {
        const auto& key = item->children[2 * j];
        const auto& val = item->children[2 * j + 1];
        v.slot_pos[j] = 4 + key.start;
        v.slot_len[j] = val.end - key.start;
        size_t f = 4;
        if (key.is_text(in, "digestID")) {
            f = F_DIGEST_ID;
            const uint8_t hb = in[val.start];
            const uint8_t ai = hb & 31;
            if ((hb >> 5) != 0 || ai > 26 || (ai > 24 && ai != 25 && ai != 26)) {
                throw std::invalid_argument("mdoc: unsupported digestID");
            }
            v.id_class = ai < 24 ? 0 : ai - 23;
        } else if (key.is_text(in, "random")) {
            f = F_RANDOM;
            const uint8_t hb = in[val.start];
            if ((hb >> 5) != 2 || (hb & 31) > 24) {
                throw std::invalid_argument("mdoc: unsupported random");
            }
            v.rnd_long = (hb & 31) == 24;
            v.rnd_n = static_cast<uint8_t>(val.arg);
            v.rnd_len = v.slot_len[j];
        } else if (key.is_text(in, "elementIdentifier")) {
            f = F_ID;
        } else if (key.is_text(in, "elementValue")) {
            f = F_VALUE;
        } else {
            throw std::invalid_argument("mdoc: unexpected key in IssuerSignedItem");
        }
        v.slot_of[f] = j;
    }
    return v;
}

// Find the witness in a DeviceResponse. Throws std::invalid_argument if it isn't found or the mdoc
// isn't supported.
inline Parsed parse(std::span<const uint8_t> resp, const Request& req) {
    // (Some DeviceResponses in Longfellow's tests have trailing zeros.)
    const auto root = cbor::decode(resp, true);
    if (!root) {
        throw std::invalid_argument("mdoc: invalid DeviceResponse");
    }
    const cbor::Item* docs = root->get(resp, "documents");
    const cbor::Item* doc = docs ? docs->at(0) : nullptr;
    const cbor::Item* is = doc ? doc->get(resp, "issuerSigned") : nullptr;
    const cbor::Item* ia = is ? is->get(resp, "issuerAuth") : nullptr;
    const cbor::Item* ns = is ? is->get(resp, "nameSpaces") : nullptr;
    const cbor::Item* ds = doc ? doc->get(resp, "deviceSigned") : nullptr;
    const cbor::Item* da = ds ? ds->get(resp, "deviceAuth") : nullptr;
    const cbor::Item* dsig = da ? da->get(resp, "deviceSignature") : nullptr;
    if (!ia || !ia->at(2) || !ia->at(3) || !ns || !dsig || !dsig->at(3) ||
        ia->at(2)->major != cbor::Major::bytes || ns->major != cbor::Major::map) {
        throw std::invalid_argument("mdoc: missing fields in DeviceResponse");
    }
    Parsed out;
    out.issuer_sig = to_sig(ia->at(3)->content(resp));
    out.device_sig = to_sig(dsig->at(3)->content(resp));

    // The issuer's signed message.
    const auto tagged_mso = ia->at(2)->content(resp);
    if (tagged_mso.size() < 256 || tagged_mso.size() > 65535) {
        throw std::invalid_argument("mdoc: unsupported MSO length");
    }
    out.sig_structure.assign(COSE_PREFIX.begin(), COSE_PREFIX.end());
    out.sig_structure.push_back(static_cast<uint8_t>(tagged_mso.size() >> 8));
    out.sig_structure.push_back(static_cast<uint8_t>(tagged_mso.size()));
    append(out.sig_structure, tagged_mso);
    if (sha256::num_blocks(out.sig_structure.size()) > MAX_BLOCKS) {
        throw std::invalid_argument("mdoc: MSO too long");
    }

    // The MSO.
    const auto tmso = cbor::decode(tagged_mso);
    if (!tmso || tmso->major != cbor::Major::tag || tmso->arg != 24 ||
        tmso->children[0].major != cbor::Major::bytes) {
        throw std::invalid_argument("mdoc: invalid MSO");
    }
    const auto mso_bytes = tmso->children[0].content(tagged_mso);
    const auto mso = cbor::decode(mso_bytes);
    if (!mso) {
        throw std::invalid_argument("mdoc: invalid MSO");
    }
    const cbor::Item* dki = mso->get(mso_bytes, "deviceKeyInfo");
    const cbor::Item* dk = dki ? dki->get(mso_bytes, "deviceKey") : nullptr;
    const cbor::Item* dkx = dk ? dk->get_int(-2) : nullptr;
    const cbor::Item* dky = dk ? dk->get_int(-3) : nullptr;
    const cbor::Item* vi = mso->get(mso_bytes, "validityInfo");
    const cbor::Item* vf = vi ? vi->get(mso_bytes, "validFrom") : nullptr;
    const cbor::Item* vu = vi ? vi->get(mso_bytes, "validUntil") : nullptr;
    if (!dkx || !dky || !vf || !vu || dkx->end - dkx->body != 32 || dky->end - dky->body != 32 ||
        vf->major != cbor::Major::tag || vu->major != cbor::Major::tag ||
        vf->children[0].end - vf->children[0].body != DATE_BYTES ||
        vu->children[0].end - vu->children[0].body != DATE_BYTES) {
        throw std::invalid_argument("mdoc: unsupported MSO");
    }
    std::ranges::copy(vf->children[0].content(mso_bytes), out.valid_from.begin());
    std::ranges::copy(vu->children[0].content(mso_bytes), out.valid_until.begin());
    std::array<uint8_t, PUBLIC_KEY_BYTES> pk{0x04};
    std::ranges::copy(dkx->content(mso_bytes), pk.begin() + 1);
    std::ranges::copy(dky->content(mso_bytes), pk.begin() + 33);
    const auto q = p256::decode_point(pk);
    if (!q) {
        throw std::invalid_argument("mdoc: invalid device key");
    }
    out.q = *q;

    // The windows.
    const std::span<const uint8_t> sig = out.sig_structure;
    auto concat = [](std::initializer_list<std::span<const uint8_t>> parts) {
        std::vector<uint8_t> v;
        for (const auto p : parts) {
            append(v, p);
        }
        return v;
    };
    out.windows.push_back(find(sig, concat({VALID_FROM, out.valid_from})));
    out.windows.push_back(find(sig, concat({VALID_UNTIL, out.valid_until})));
    out.windows.push_back(find(
        sig, concat({DEVICE_KEY, dkx->content(mso_bytes), DEVICE_KEY_Y, dky->content(mso_bytes)})));
    out.windows.push_back(find(sig, VALUE_DIGESTS));

    // The attributes.
    for (const auto& a : req.attributes) {
        std::optional<ItemValues> found;
        std::vector<uint8_t> tagged;
        for (size_t i = 1; i < ns->children.size() && !found; i += 2) {
            for (const auto& it : ns->children[i].children) {
                if (it.major != cbor::Major::tag || it.arg != 24 ||
                    it.children[0].major != cbor::Major::bytes) {
                    continue;
                }
                const auto inner = it.children[0].content(resp);
                const auto item = cbor::decode(inner);
                if (!item) {
                    continue;
                }
                const cbor::Item* ei = item->get(inner, "elementIdentifier");
                const cbor::Item* ev = item->get(inner, "elementValue");
                if (!ei || !ev || !ei->is_text(inner, a.id) ||
                    !std::ranges::equal(inner.subspan(ev->start, ev->end - ev->start), a.value)) {
                    continue;
                }
                const auto bytes = resp.subspan(it.start, it.end - it.start);
                tagged.assign(bytes.begin(), bytes.end());
                found = parse_item(bytes);
                break;
            }
        }
        if (!found) {
            throw std::invalid_argument("mdoc: attribute not found");
        }
        const auto digest = sha256::hash(tagged);
        out.windows.push_back(find(sig, concat({DIGEST, digest})));
        out.items.push_back(*found);
    }
    return out;
}

// The prover's witness.
struct Witness {
    detail::Witness issuer;
    hk::Witness device;
    Fp rho_q; // the mask of Z_q, reduced modulo p
    MdocValues bin;
};

// Compute the witness. Throws std::invalid_argument if a signature is invalid, and
// std::runtime_error in the degenerate cases of the scalar multiplications (which happen with
// negligible probability).
inline Witness make_witness(const Request& req, const Parsed& m, const Public& pub,
                            std::span<const uint8_t, 32> seed) {
    const auto qi = p256::decode_point(req.issuer_pk);
    if (!qi) {
        throw std::invalid_argument("mdoc: invalid issuer key");
    }
    std::array<uint8_t, 32> s1, s2;
    std::array<uint8_t, Z_BYTES> rho_q{};
    {
        faest::hash_state h;
        h.init(faest::secpar::s128);
        h.update(vole_mole::detail::ECDSA_MDOC_SEED_DST);
        h.update(seed);
        h.update_byte(2);
        Keccak_HashFinal(&h.ctx, nullptr);
        squeeze_bits(h.ctx, s1, 256);
        squeeze_bits(h.ctx, s2, 256);
        squeeze_bits(h.ctx, rho_q, rr::RHO_BITS);
    }
    Witness w{
        detail::make_witness(*qi, pub.issuer_tables, m.sig_structure, m.issuer_sig, s1),
        hk::make_witness(m.q, device_sig_structure(req.transcript, req.doc_type), m.device_sig, s2),
        reduce_le<Fp>(rho_q),
        {}};
    MdocValues& b = w.bin;
    b.sig.fill(0);
    const auto padded = sha256::pad(m.sig_structure);
    std::ranges::copy(padded, b.sig.begin());
    b.traces = sha256_traces(b.sig);
    b.last = padded.size() / 64 - 1;
    b.valid_from = m.valid_from;
    b.valid_until = m.valid_until;
    b.windows = m.windows;
    b.x = w.issuer.bin.x;
    store_limbs_le(b.qx.data(), m.q.x.canonical());
    store_limbs_le(b.qy.data(), m.q.y.canonical());
    b.xd = w.device.bin.x;
    b.items = m.items;
    b.rho_n = w.issuer.bin.rho_n;
    b.rho_p = w.issuer.bin.rho_p;
    b.rho_q = rho_q;
    b.rho_dn = w.device.bin.rho_n;
    b.rho_dp = w.device.bin.rho_p;
    return w;
}

// The link challenges, from the commitments of both proofs: the issuer's, and the device's.
template <typename Bin>
std::pair<LinkChallenge, LinkChallenge>
link_challenges(const Digest& mu, const vp::Digest& arith_chal2, std::span<const uint8_t> bin_chal1,
                std::span<const uint8_t, vole_mole::detail::PROOF_BYTES<Bin>> bin) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_MDOC_LINK_DST);
    h.update(mu);
    h.update(arith_chal2);
    h.update(bin_chal1);
    vole_mole::detail::hash_witness_prefix_commitment<Bin>(h, bin);
    Digest d;
    h.finalize(d);
    faest::hash_state h2;
    h2.init(faest::secpar::s128);
    h2.update(vole_mole::detail::ECDSA_MDOC_LINK_DST);
    h2.update(d);
    h2.update_byte(1);
    Digest d2;
    h2.finalize(d2);
    return {derive_link_challenge(d), derive_link_challenge(d2)};
}

inline Digest arith_binder(const LinkChallenge& chal, const LinkChallenge& dchal,
                           std::span<const uint8_t> link_values) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_MDOC_BINDER_DST);
    h.update(chal.digest);
    h.update(dchal.digest);
    h.update(link_values);
    Digest d;
    h.finalize(d);
    return d;
}

using YValues = std::array<p256::Limbs, 2 * NUM_Y_CHECKS>; // the issuer's, then the device's

inline ArithInstance arith_instance(const Public& pub, const LinkChallenge& chal,
                                    const LinkChallenge& dchal, LinkValues& z, const YValues& y) {
    auto zc = [&](size_t i) { return std::span<const uint8_t, Z_BYTES>(z_at(z, i)); };
    std::array<p256::Limbs, NUM_Y_CHECKS> yi, yd;
    std::copy_n(y.begin(), NUM_Y_CHECKS, yi.begin());
    std::copy_n(y.begin() + NUM_Y_CHECKS, NUM_Y_CHECKS, yd.begin());
    return {detail::arith_instance(&pub.issuer_tables, chal, zc(Z_N), zc(Z_P), yi),
            hk::arith_instance(pub.device_e, dchal, zc(Z_DN), zc(Z_DP), yd),
            LinkChallenge::weight<Fp>(dchal.xn_pos), LinkChallenge::weight<Fp>(dchal.xp_pos),
            reduce_le<Fp>(zc(Z_Q))};
}

// For tests: modifies the binary witness prefix, given the circuit's wires.
using Tamper = std::function<void(std::span<uint8_t>, const MdocWires<PlainOps>&)>;

// Prove with the witness. If `tamper` is given, it may modify the binary witness, and the witness
// isn't checked (for tests of cheating provers).
template <size_t NA, Vole V, BinPrg PRG>
void prove_with_witness(std::span<uint8_t, Scheme<NA, V, PRG>::PROOF_BYTES> proof,
                        const Public& pub, const Witness& wit, std::span<const uint8_t, 32> seed,
                        const Tamper* tamper = nullptr) {
    using S = Scheme<NA, V, PRG>;
    using Bin = typename S::Bin;
    using VP = typename S::VP;
    const auto bin = proof.template subspan<S::OFF_BIN, S::BIN_BYTES>();
    const auto ar = proof.template subspan<S::OFF_ARITH, S::ARITH_BYTES>();

    vp::ProveSeed rho_arith;
    vole_mole::detail::ProveSeed<Bin> rho_bin;
    {
        faest::hash_state h;
        h.init(faest::secpar::s128);
        h.update(vole_mole::detail::ECDSA_MDOC_SEED_DST);
        h.update(seed);
        h.update_byte(1);
        std::array<uint8_t, sizeof(rho_arith) + sizeof(rho_bin)> b;
        h.finalize(b);
        std::memcpy(rho_arith.data(), b.data(), rho_arith.size());
        std::memcpy(rho_bin.data(), b.data() + rho_arith.size(), rho_bin.size());
    }

    // Commit to the witness over F_p and F_n.
    std::vector<Fp> wp = wit.issuer.wp;
    wp.insert(wp.end(), wit.device.wp.begin(), wit.device.wp.end());
    wp.push_back(wit.rho_q);
    std::vector<Fn> wn = wit.issuer.wn;
    wn.insert(wn.end(), wit.device.wn.begin(), wit.device.wn.end());
    auto arith_state = vp::prove_commit<ArithRelation, VP>(ar, pub.mu, std::span<const Fp, LP>(wp),
                                                           std::span<const Fn, LN>(wn), rho_arith);

    // The binary witness prefix, and its commitment.
    std::vector<uint8_t> bin_witness(Bin::RELATION_WITNESS_BITS / 8, 0);
    PlainOps ops{bin_witness};
    const auto wires = prefix_circuit<Bin::SH.sha_log>(ops, pub.bin, &wit.bin);
    if (tamper) {
        (*tamper)(std::span<uint8_t>(bin_witness).first(Bin::WITNESS_PREFIX_BYTES), wires);
    } else if (ops.failed != 0) {
        throw std::logic_error("mdoc: the binary witness doesn't satisfy the circuit");
    }
    auto pending = vole_mole::detail::voleith_vole_gen<Bin>(
        bin, nullptr,
        std::span<const uint8_t, Bin::WITNESS_PREFIX_BYTES>(bin_witness.data(),
                                                            Bin::WITNESS_PREFIX_BYTES),
        rho_bin, pub.mu);

    // The link challenges and values.
    const auto [chal, dchal] = link_challenges<Bin>(pub.mu, arith_state.chal2, pending.chal1, bin);
    ops.next = 8 * Bin::WITNESS_PREFIX_BYTES;
    LinkValues z{};
    link_circuit<Bin::SH.link_log>(ops, wires, chal, dchal, z, true);
    std::ranges::copy(z, proof.begin() + S::OFF_Z);
    YValues y;
    const auto yi = detail::y_values(wit.issuer, chal);
    const auto yd = hk::y_values(wit.device, dchal);
    std::ranges::copy(yi, y.begin());
    std::ranges::copy(yd, y.begin() + NUM_Y_CHECKS);
    for (size_t i = 0; i < 2 * NUM_Y_CHECKS; ++i) {
        store_limbs_le(proof.data() + S::OFF_Y + i * Y_BYTES, y[i]);
    }

    // Finish the binary proof.
    typename Bin::instance bin_inst{&pub.mu, &pub.bin, &chal, &dchal, z};
    vole_mole::detail::voleith_prove_commit<Bin>(
        bin, bin_inst,
        std::span<const uint8_t, vole_mole::detail::WITNESS_SUFFIX_BYTES<Bin>>(
            bin_witness.data() + Bin::WITNESS_PREFIX_BYTES,
            vole_mole::detail::WITNESS_SUFFIX_BYTES<Bin>),
        std::move(pending));

    // Finish the proof over F_p and F_n.
    const ArithInstance ar_inst = mdoc::arith_instance(pub, chal, dchal, z, y);
    const Digest binder = arith_binder(chal, dchal, proof.subspan(S::OFF_Z));
    vp::prove_finish<ArithRelation, VP>(ar, arith_state, ar_inst, binder);
}

template <size_t NA, Vole V, BinPrg PRG>
bool verify_proof(std::span<const uint8_t, Scheme<NA, V, PRG>::PROOF_BYTES> proof,
                  const Public& pub) {
    using S = Scheme<NA, V, PRG>;
    using Bin = typename S::Bin;
    using VP = typename S::VP;
    const auto bin = proof.template subspan<S::OFF_BIN, S::BIN_BYTES>();
    const auto ar = proof.template subspan<S::OFF_ARITH, S::ARITH_BYTES>();
    LinkValues z;
    std::copy_n(proof.begin() + S::OFF_Z, z.size(), z.begin());

    // The link values must be in range.
    auto top_zero = [](std::span<const uint8_t> z, size_t cols) {
        for (size_t i = cols; i < 8 * Z_BYTES; ++i) {
            if (get_bit(z, i)) {
                return false;
            }
        }
        return true;
    };
    for (size_t i = 0; i < NUM_Z; ++i) {
        if (!top_zero(z_at(z, i), Z_COLS[i])) {
            return false;
        }
    }
    YValues y;
    for (size_t i = 0; i < 2 * NUM_Y_CHECKS; ++i) {
        y[i] = load_limbs_le(proof.data() + S::OFF_Y + i * Y_BYTES);
        if (!y_in_range(y[i])) {
            return false;
        }
    }

    auto pending = vole_mole::detail::voleith_vole_reconstruct<Bin>(bin, nullptr, pub.mu);
    if (!pending) {
        return false;
    }
    const auto arith_state = vp::verify_commit<ArithRelation, VP>(ar, pub.mu);
    if (!arith_state) {
        return false;
    }
    const auto [chal, dchal] =
        link_challenges<Bin>(pub.mu, arith_state->chal2, pending->chal1, bin);

    typename Bin::instance bin_inst{&pub.mu, &pub.bin, &chal, &dchal, z};
    if (!vole_mole::detail::voleith_verify_commit<Bin>(bin, bin_inst, std::move(*pending))) {
        return false;
    }

    const ArithInstance ar_inst = mdoc::arith_instance(pub, chal, dchal, z, y);
    const Digest binder = arith_binder(chal, dchal, proof.subspan(S::OFF_Z));
    return vp::verify_finish<ArithRelation, VP>(ar, *arith_state, ar_inst, binder);
}

// Dispatch on the number of attributes and the parameters. The MQ PRG isn't supported: its key
// length estimates stop well below the binary witness's million bits.
template <typename F> auto dispatch(size_t na, Params params, F&& f) {
    auto by_prg = [&]<size_t NA, Vole V>() {
        switch (params.prg) {
        case WitnessPrg::none:
            return f.template operator()<NA, V, BinPrg::none>();
        case WitnessPrg::local:
            return f.template operator()<NA, V, BinPrg::local>();
        case WitnessPrg::mq:
            break;
        }
        throw std::invalid_argument("mdoc: unsupported witness PRG");
    };
    auto by_vole = [&]<size_t NA>() {
        switch (params.vole) {
        case Vole::fast:
            return by_prg.template operator()<NA, Vole::fast>();
        case Vole::medium:
            return by_prg.template operator()<NA, Vole::medium>();
        case Vole::small:
            return by_prg.template operator()<NA, Vole::small>();
        }
        throw std::invalid_argument("mdoc: invalid VOLEitH parameters");
    };
    switch (na) {
    case 1:
        return by_vole.template operator()<1>();
    case 2:
        return by_vole.template operator()<2>();
    case 3:
        return by_vole.template operator()<3>();
    case 4:
        return by_vole.template operator()<4>();
    default:
        throw std::invalid_argument("mdoc: unsupported number of attributes");
    }
}

inline size_t proof_bytes(size_t na, Params params = {}) {
    return dispatch(na, params, []<size_t NA, Vole V, BinPrg PRG>() {
        return Scheme<NA, V, PRG>::PROOF_BYTES;
    });
}

// Prove the presentation of `resp` (a DeviceResponse) for `req`. Throws std::invalid_argument if
// the DeviceResponse doesn't satisfy the request or isn't supported, and std::runtime_error in
// negligible-probability failures.
inline std::vector<uint8_t> prove(std::span<const uint8_t> resp, const Request& req,
                                  Params params = {}) {
    const Parsed m = parse(resp, req);
    const auto qi = p256::decode_point(req.issuer_pk);
    if (!qi || !p256::ecdsa_verify(*qi, m.sig_structure, m.issuer_sig)) {
        throw std::invalid_argument("mdoc: invalid issuer signature");
    }
    const auto dmsg = device_sig_structure(req.transcript, req.doc_type);
    if (!p256::ecdsa_verify(m.q, dmsg, m.device_sig)) {
        throw std::invalid_argument("mdoc: invalid device signature");
    }
    if (!(m.valid_from <= req.now && req.now <= m.valid_until)) {
        throw std::invalid_argument("mdoc: not valid now");
    }
    const auto pub = make_public(req, params.vole, rr::bin_prg_of(params.prg));
    if (!pub) {
        throw std::runtime_error("mdoc: degenerate issuer key");
    }
    constexpr int ATTEMPTS = 8;
    for (int attempt = 1;; ++attempt) {
        const auto seed = random_bytes<32>();
        try {
            const Witness wit = make_witness(req, m, *pub, seed);
            return dispatch(req.attributes.size(), params, [&]<size_t NA, Vole V, BinPrg PRG>() {
                std::vector<uint8_t> proof(Scheme<NA, V, PRG>::PROOF_BYTES);
                prove_with_witness<NA, V, PRG>(
                    std::span<uint8_t, Scheme<NA, V, PRG>::PROOF_BYTES>(proof), *pub, wit, seed);
                return proof;
            });
        } catch (const std::runtime_error&) {
            if (attempt == ATTEMPTS) {
                throw;
            }
        }
    }
}

inline bool verify(const Request& req, std::span<const uint8_t> proof, Params params = {}) {
    if (req.attributes.empty() || req.attributes.size() > MAX_ATTRIBUTES ||
        params.prg == WitnessPrg::mq ||
        proof.size() != mdoc::proof_bytes(req.attributes.size(), params)) {
        return false;
    }
    const auto pub = make_public(req, params.vole, rr::bin_prg_of(params.prg));
    if (!pub) {
        return false;
    }
    return dispatch(req.attributes.size(), params, [&]<size_t NA, Vole V, BinPrg PRG>() {
        return verify_proof<NA, V, PRG>(
            std::span<const uint8_t, Scheme<NA, V, PRG>::PROOF_BYTES>(proof.data(), proof.size()),
            *pub);
    });
}

} // namespace vole_mole::ecdsa_pok::detail::mdoc

#endif
