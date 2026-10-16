// EXPERIMENTAL: a zero-knowledge proof of knowledge of a public key Q and an ECDSA-P256-SHA256
// signature (r, s) on a public message under Q, which reveals R, the signature's nonce point. As in
// hk_relation.hpp, this is the device signature of an mdoc, as a step toward an mdoc proof; Q is
// committed as bits in the binary proof, for linking to the rest of a statement. On its own, the
// statement is trivial (anyone can make a key and sign).
//
// Statement. Public: the message m, a context string, and R. Secret: Q and s. The prover shows that
// (r, s) with r = x(R) mod n is a valid signature on m under Q, i.e., s R = e G + r Q (then
// verification computes (e G + r Q) / s = R). If s = 0 (mod n), then Q = -(e / r) G, so the prover
// knows Q's secret key and can sign anyway.
//
// Revealing R. R = k G for the signer's nonce k, which is uniform (or pseudorandom, with RFC 6979)
// and independent of the secret key, so R is independent of Q. Given R and e, every Q' is
// consistent with some s' (s' R = e G + r Q' has a solution since R generates the group), so R
// reveals nothing about Q as long as s is hidden. This is the "efficient ECDSA" approach of
// Personae Labs' spartan-ecdsa: Q = s T + U for the public T = r^-1 R and U = -(e / r) G.
//
// Proof. Q = s T + U over F_p, with a comb on T (rr_arith.hpp), and Q as bits in the binary proof
// (rr_binary.hpp), linked by Z_p. Nothing is needed over F_n.

#ifndef VOLE_MOLE_ECDSA_POK_RR_RELATION_HPP
#define VOLE_MOLE_ECDSA_POK_RR_RELATION_HPP

#include "vole_mole/ecdsa_pok.hpp"
#include "vole_mole/random.hpp"

#include "dst.hpp"
#include "ecdsa_pok/bin_ops.hpp"
#include "ecdsa_pok/link.hpp"
#include "ecdsa_pok/relation.hpp" // limbs helpers, squeeze_bits
#include "ecdsa_pok/rr_arith.hpp"
#include "ecdsa_pok/rr_binary.hpp"
#include "p256/curve.hpp"
#include "p256/field.hpp"
#include "sha256/sha256.hpp"
#include "voleith.hpp"
#include "voleith_p256/voleith.hpp"

#include "hash.hpp" // from faest-arch-opt

extern "C" {
#include "KeccakHash.h" // from xkcp
}

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <span>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <vector>

namespace vole_mole::ecdsa_pok::detail::rr {

namespace vp = vole_mole::voleith_p256;

constexpr size_t R_BYTES = 64; // x || y, big endian

template <Vole V, BinPrg PRG> struct Scheme {
    using Bin = BinRelation<V == Vole::small, PRG>;
    using VP = std::conditional_t<V == Vole::small, vp::Small,
                                  std::conditional_t<V == Vole::medium, vp::Medium, vp::Fast>>;
    using Arith = vp::Layout<RrArithRelation, VP>;

    static constexpr size_t BIN_BYTES = vole_mole::detail::PROOF_BYTES<Bin>;
    static constexpr size_t ARITH_BYTES = Arith::PROOF_BYTES;
    static constexpr size_t OFF_R = 0;
    static constexpr size_t OFF_BIN = OFF_R + R_BYTES;
    static constexpr size_t OFF_ARITH = OFF_BIN + BIN_BYTES;
    static constexpr size_t OFF_ZP = OFF_ARITH + ARITH_BYTES;
    static constexpr size_t PROOF_BYTES = OFF_ZP + Z_BYTES;
};

// The public values derived from the statement and R.
struct Public {
    Digest mu;
    Tables tables;
};

inline Digest statement_digest(std::span<const uint8_t> msg, std::span<const uint8_t> ctx,
                               std::span<const uint8_t, R_BYTES> r, Vole vole, BinPrg prg) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_RR_STATEMENT_DST);
    h.update_byte(std::to_underlying(vole));
    h.update_byte(std::to_underlying(prg));
    for (const auto part : {msg, ctx}) {
        const uint64_t v = part.size();
        for (size_t i = 0; i < 8; ++i) {
            h.update_byte(static_cast<uint8_t>(v >> (8 * i)));
        }
        h.update(part);
    }
    h.update(r);
    Digest out;
    h.finalize(out);
    return out;
}

inline std::array<uint8_t, R_BYTES> encode_r(const Affine& r) {
    std::array<uint8_t, R_BYTES> out;
    const auto x = r.x.to_bytes(), y = r.y.to_bytes();
    std::ranges::copy(x, out.begin());
    std::ranges::copy(y, out.begin() + 32);
    return out;
}

// The public values for R (encoded): nothing if R isn't a point on the curve, if r = x(R) mod n is
// zero, or in the degenerate cases of the tables (which happen with negligible probability).
inline std::optional<Public> make_public(std::span<const uint8_t> msg, std::span<const uint8_t> ctx,
                                         std::span<const uint8_t, R_BYTES> rb, Vole vole,
                                         BinPrg prg) {
    const auto x = Fp::from_bytes(rb.subspan<0, 32>());
    const auto y = Fp::from_bytes(rb.subspan<32, 32>());
    if (!x || !y) {
        return std::nullopt;
    }
    const Affine rp{*x, *y, false};
    if (!rp.on_curve()) {
        return std::nullopt;
    }
    const Fn r = Fn::reduce_32(rp.x.to_bytes());
    if (r.is_zero()) {
        return std::nullopt;
    }
    const Fn e = Fn::reduce_32(sha256::hash(msg));
    const Fn r_inv = r.inv();
    const Affine t = p256::scalar_mul(rp, r_inv.canonical()).to_affine();
    const Affine u = p256::scalar_mul(p256::GENERATOR, (-(e * r_inv)).canonical()).to_affine();
    Public out;
    out.mu = statement_digest(msg, ctx, rb, vole, prg);
    // The offsets, hashed to the curve from the statement (including R).
    std::array<Affine, 2> h;
    for (size_t i = 0; i < 2; ++i) {
        std::vector<uint8_t> label(vole_mole::detail::ECDSA_RR_OFFSET_DST.begin(),
                                   vole_mole::detail::ECDSA_RR_OFFSET_DST.end());
        label.insert(label.end(), out.mu.begin(), out.mu.end());
        label.push_back(static_cast<uint8_t>(i));
        h[i] = p256::hash_to_point(label);
    }
    // T != O since r != 0; U = O iff e = 0 (mod n), which happens with negligible probability.
    if (t.inf || u.inf) {
        return std::nullopt;
    }
    try {
        out.tables = make_tables(t, u, h[0], h[1]);
    } catch (const std::runtime_error&) {
        return std::nullopt;
    }
    return out;
}

template <typename Bin>
LinkChallenge link_challenge(const Digest& mu, const vp::Digest& arith_chal2,
                             std::span<const uint8_t> bin_chal1,
                             std::span<const uint8_t, vole_mole::detail::PROOF_BYTES<Bin>> bin) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_RR_LINK_DST);
    h.update(mu);
    h.update(arith_chal2);
    h.update(bin_chal1);
    vole_mole::detail::hash_witness_prefix_commitment<Bin>(h, bin);
    Digest d;
    h.finalize(d);
    return derive_link_challenge(d);
}

inline Digest arith_binder(const LinkChallenge& chal, std::span<const uint8_t> zp) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_RR_BINDER_DST);
    h.update(chal.digest);
    h.update(zp);
    Digest d;
    h.finalize(d);
    return d;
}

inline ArithInstance arith_instance(const Tables* tables, const LinkChallenge& chal,
                                    std::span<const uint8_t, Z_BYTES> zp) {
    return {tables, LinkChallenge::weight<Fp>(chal.xn_pos), LinkChallenge::weight<Fp>(chal.xp_pos),
            reduce_le<Fp>(zp)};
}

struct Witness {
    std::vector<Fp> wp;
    PrefixValues bin;
};

// The nonce point R of a valid signature: (e G + r Q) / s.
inline Affine nonce_point(const Affine& q, std::span<const uint8_t> msg,
                          const p256::Signature& sig) {
    const Fn r = *Fn::from_bytes(sig.r);
    const Fn s = *Fn::from_bytes(sig.s);
    const Fn e = Fn::reduce_32(sha256::hash(msg));
    const Fn w = s.inv();
    return p256::scalar_mul(p256::GENERATOR, (e * w).canonical())
        .add(p256::scalar_mul(q, (r * w).canonical()))
        .to_affine();
}

// Compute the witness for a valid signature, given the public values for its R. Throws
// std::runtime_error in the degenerate cases of the comb (which happen with negligible
// probability).
inline Witness make_witness(const Affine& q, const p256::Signature& sig, const Public& pub,
                            std::span<const uint8_t, 32> seed) {
    const Tables& tab = pub.tables;
    const p256::Limbs s = Fn::from_bytes(sig.s)->canonical();
    Witness wit;
    wit.wp.assign(LP, Fp::zero());
    auto digit = [&](size_t k) {
        return static_cast<size_t>((s[(4 * k) / 64] >> ((4 * k) % 64)) & 0xf);
    };
    auto add = [](Fp& ax, Fp& ay, const Affine& t) {
        if (t.x == ax) {
            throw std::runtime_error("ecdsa_pok: degenerate addition");
        }
        const Fp lambda = (t.y - ay) * (t.x - ax).inv();
        const Fp nx = lambda.square() - ax - t.x;
        ay = lambda * (ax - nx) - ay;
        ax = nx;
        return lambda;
    };
    Fp ax = tab.h0.x, ay = tab.h0.y;
    for (size_t k = 0; k < NUM_DIGITS; ++k) {
        wit.wp[WP_S + k] = Fp::from_u64(digit(k));
    }
    for (size_t j = 0; j < COMB_STEPS; ++j) {
        wit.wp[WP_LAMBDA + j] = add(ax, ay, tab.at(j, digit(2 * j), digit(2 * j + 1)));
    }
    wit.wp[WP_LAMBDA + COMB_STEPS] = add(ax, ay, tab.pstar);
    if (!(ax == q.x && ay == q.y)) {
        throw std::logic_error("ecdsa_pok: s T + U != Q");
    }

    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_RR_SEED_DST);
    h.update(seed);
    Keccak_HashFinal(&h.ctx, nullptr);
    squeeze_bits(h.ctx, wit.bin.rho, RHO_BITS);
    wit.wp[WP_RHO] = reduce_le<Fp>(wit.bin.rho);
    store_limbs_le(wit.bin.x.data(), q.x.canonical());
    store_limbs_le(wit.bin.y.data(), q.y.canonical());
    return wit;
}

template <Vole V, BinPrg PRG>
void prove_with_witness(std::span<uint8_t, Scheme<V, PRG>::PROOF_BYTES> proof,
                        std::span<const uint8_t, R_BYTES> r, const Public& pub, const Witness& wit,
                        std::span<const uint8_t, 32> seed) {
    using S = Scheme<V, PRG>;
    using Bin = typename S::Bin;
    using VP = typename S::VP;
    std::ranges::copy(r, proof.begin() + S::OFF_R);
    const auto bin = proof.template subspan<S::OFF_BIN, S::BIN_BYTES>();
    const auto ar = proof.template subspan<S::OFF_ARITH, S::ARITH_BYTES>();
    const auto zp = proof.template subspan<S::OFF_ZP, Z_BYTES>();

    vp::ProveSeed rho_arith;
    vole_mole::detail::ProveSeed<Bin> rho_bin;
    {
        faest::hash_state h;
        h.init(faest::secpar::s128);
        h.update(vole_mole::detail::ECDSA_RR_SEED_DST);
        h.update(seed);
        h.update_byte(1);
        std::array<uint8_t, sizeof(rho_arith) + sizeof(rho_bin)> b;
        h.finalize(b);
        std::memcpy(rho_arith.data(), b.data(), rho_arith.size());
        std::memcpy(rho_bin.data(), b.data() + rho_arith.size(), rho_bin.size());
    }

    auto arith_state = vp::prove_commit<RrArithRelation, VP>(
        ar, pub.mu, std::span<const Fp, LP>(wit.wp), std::span<const Fn, LN>(), rho_arith);

    std::vector<uint8_t> bin_witness(Bin::RELATION_WITNESS_BITS / 8, 0);
    PlainOps ops{bin_witness};
    const auto wires = prefix_circuit<Bin::SH.small_log>(ops, &wit.bin);
    auto pending = vole_mole::detail::voleith_vole_gen<Bin>(
        bin, nullptr,
        std::span<const uint8_t, Bin::WITNESS_PREFIX_BYTES>(bin_witness.data(),
                                                            Bin::WITNESS_PREFIX_BYTES),
        rho_bin, pub.mu);

    const LinkChallenge chal =
        rr::link_challenge<Bin>(pub.mu, arith_state.chal2, pending.chal1, bin);
    ops.next = 8 * Bin::WITNESS_PREFIX_BYTES;
    link_circuit<Bin::SH.link_log>(ops, wires, chal, zp, true);

    typename Bin::instance bin_inst{&pub.mu, &chal, {}};
    std::ranges::copy(zp, bin_inst.zp.begin());
    vole_mole::detail::voleith_prove_commit<Bin>(
        bin, bin_inst,
        std::span<const uint8_t, vole_mole::detail::WITNESS_SUFFIX_BYTES<Bin>>(
            bin_witness.data() + Bin::WITNESS_PREFIX_BYTES,
            vole_mole::detail::WITNESS_SUFFIX_BYTES<Bin>),
        std::move(pending));

    const ArithInstance ar_inst = rr::arith_instance(&pub.tables, chal, zp);
    const Digest binder = rr::arith_binder(chal, zp);
    vp::prove_finish<RrArithRelation, VP>(ar, arith_state, ar_inst, binder);
}

template <Vole V, BinPrg PRG>
bool verify_proof(std::span<const uint8_t, Scheme<V, PRG>::PROOF_BYTES> proof, const Public& pub) {
    using S = Scheme<V, PRG>;
    using Bin = typename S::Bin;
    using VP = typename S::VP;
    const auto bin = proof.template subspan<S::OFF_BIN, S::BIN_BYTES>();
    const auto ar = proof.template subspan<S::OFF_ARITH, S::ARITH_BYTES>();
    const auto zp = proof.template subspan<S::OFF_ZP, Z_BYTES>();
    for (size_t i = Z_COLS; i < 8 * Z_BYTES; ++i) {
        if (get_bit(zp, i)) {
            return false;
        }
    }
    auto pending = vole_mole::detail::voleith_vole_reconstruct<Bin>(bin, nullptr, pub.mu);
    if (!pending) {
        return false;
    }
    const auto arith_state = vp::verify_commit<RrArithRelation, VP>(ar, pub.mu);
    if (!arith_state) {
        return false;
    }
    const LinkChallenge chal =
        rr::link_challenge<Bin>(pub.mu, arith_state->chal2, pending->chal1, bin);
    typename Bin::instance bin_inst{&pub.mu, &chal, {}};
    std::ranges::copy(zp, bin_inst.zp.begin());
    if (!vole_mole::detail::voleith_verify_commit<Bin>(bin, bin_inst, std::move(*pending))) {
        return false;
    }
    const ArithInstance ar_inst = rr::arith_instance(&pub.tables, chal, zp);
    const Digest binder = rr::arith_binder(chal, zp);
    return vp::verify_finish<RrArithRelation, VP>(ar, *arith_state, ar_inst, binder);
}

template <typename F> auto dispatch(Params params, F&& f) {
    auto by_prg = [&]<Vole V>() {
        switch (params.prg) {
        case WitnessPrg::none:
            return f.template operator()<V, BinPrg::none>();
        case WitnessPrg::local:
            return f.template operator()<V, BinPrg::local>();
        case WitnessPrg::mq:
            return f.template operator()<V, BinPrg::mq>();
        }
        throw std::invalid_argument("ecdsa_pok: invalid witness PRG");
    };
    switch (params.vole) {
    case Vole::fast:
        return by_prg.template operator()<Vole::fast>();
    case Vole::medium:
        return by_prg.template operator()<Vole::medium>();
    case Vole::small:
        return by_prg.template operator()<Vole::small>();
    }
    throw std::invalid_argument("ecdsa_pok: invalid VOLEitH parameters");
}

inline size_t proof_bytes(Params params = {}) {
    return dispatch(params, []<Vole V, BinPrg PRG>() { return Scheme<V, PRG>::PROOF_BYTES; });
}

constexpr BinPrg bin_prg_of(WitnessPrg prg) { return static_cast<BinPrg>(std::to_underlying(prg)); }

// Prove knowledge of a public key pk and a signature sig on msg under it, for context ctx,
// revealing sig's R. Throws as ecdsa_pok::prove.
inline std::vector<uint8_t> prove(const PublicKey& pk, std::span<const uint8_t> msg,
                                  const Signature& sig, std::span<const uint8_t> ctx,
                                  Params params = {}) {
    const auto q = p256::decode_point(pk);
    if (!q) {
        throw std::invalid_argument("ecdsa_pok: invalid public key");
    }
    p256::Signature s;
    std::copy_n(sig.begin(), 32, s.r.begin());
    std::copy_n(sig.begin() + 32, 32, s.s.begin());
    if (!p256::ecdsa_verify(*q, msg, s)) {
        throw std::invalid_argument("ecdsa_pok: invalid signature");
    }
    const auto rb = encode_r(nonce_point(*q, msg, s));
    const auto pub = make_public(msg, ctx, rb, params.vole, bin_prg_of(params.prg));
    if (!pub) {
        throw std::runtime_error("ecdsa_pok: degenerate signature");
    }
    constexpr int ATTEMPTS = 8;
    for (int attempt = 1;; ++attempt) {
        const auto seed = random_bytes<32>();
        try {
            const Witness wit = make_witness(*q, s, *pub, seed);
            return dispatch(params, [&]<Vole V, BinPrg PRG>() {
                std::vector<uint8_t> proof(Scheme<V, PRG>::PROOF_BYTES);
                prove_with_witness<V, PRG>(std::span<uint8_t, Scheme<V, PRG>::PROOF_BYTES>(proof),
                                           rb, *pub, wit, seed);
                return proof;
            });
        } catch (const std::runtime_error&) {
            if (attempt == ATTEMPTS) {
                throw;
            }
        }
    }
}

inline bool verify(std::span<const uint8_t> msg, std::span<const uint8_t> ctx,
                   std::span<const uint8_t> proof, Params params = {}) {
    if (proof.size() != proof_bytes(params)) {
        return false;
    }
    const auto pub =
        make_public(msg, ctx, proof.subspan<0, R_BYTES>(), params.vole, bin_prg_of(params.prg));
    if (!pub) {
        return false;
    }
    return dispatch(params, [&]<Vole V, BinPrg PRG>() {
        return verify_proof<V, PRG>(
            std::span<const uint8_t, Scheme<V, PRG>::PROOF_BYTES>(proof.data(), proof.size()),
            *pub);
    });
}

} // namespace vole_mole::ecdsa_pok::detail::rr

#endif
