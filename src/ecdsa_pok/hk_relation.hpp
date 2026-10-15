// EXPERIMENTAL: a zero-knowledge proof of knowledge of a public key and an ECDSA-P256-SHA256
// signature on a public message. This is the device signature of an mdoc (ISO/IEC 18013-5), whose
// key is hidden in the issuer-signed MSO; it's a step toward an mdoc proof. On its own, the
// statement is trivial (anyone can make a key and sign), so this is for measuring the cost of a
// variable-base scalar multiplication, not for use. A real proof would link Q to the rest of the
// statement, e.g., to the bits of the MSO in the binary proof.
//
// Statement. Public: the message m and a context string. Secret: the public key Q and the
// signature (r, s). The prover shows ECDSA.Verify(Q, m, (r, s)) = 1.
//
// As in relation.hpp, a valid signature exists iff there are integers u1, u2 in [0, 2^256), a
// point R and X = x(R) in [0, p) with
//
//   (a) R = u1 G + u2 Q (as an affine point),
//   (b) u1 X = u2 e and u2 X != 0 (mod n), for e = SHA-256(m) (public).
//
// (a) is proven over F_p, now with Q committed (hk_arith.hpp); (b) over F_n; and X < p in the
// binary proof (hk_binary.hpp). X is linked between the three as in relation.hpp (without e),
// and u1, u2 between F_p and F_n with the Y_i checks. The soundness and zero-knowledge arguments
// of the links are those of relation.hpp; see hk_arith.hpp for the incomplete additions.

#ifndef VOLE_MOLE_ECDSA_POK_HK_RELATION_HPP
#define VOLE_MOLE_ECDSA_POK_HK_RELATION_HPP

#include "vole_mole/ecdsa_pok.hpp"
#include "vole_mole/random.hpp"

#include "dst.hpp"
#include "ecdsa_pok/bin_ops.hpp"
#include "ecdsa_pok/hk_arith.hpp"
#include "ecdsa_pok/hk_binary.hpp"
#include "ecdsa_pok/link.hpp"
#include "ecdsa_pok/relation.hpp" // limbs helpers, squeeze_bits, Y_BYTES
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
#include <span>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <vector>

namespace vole_mole::ecdsa_pok::detail::hk {

namespace vp = vole_mole::voleith_p256;

template <Vole V, BinPrg PRG> struct Scheme {
    using Bin = BinRelation<V == Vole::small, PRG>;
    using VP = std::conditional_t<V == Vole::small, vp::Small,
                                  std::conditional_t<V == Vole::medium, vp::Medium, vp::Fast>>;
    using Arith = vp::Layout<HkArithRelation, VP>;

    static constexpr size_t BIN_BYTES = vole_mole::detail::PROOF_BYTES<Bin>;
    static constexpr size_t ARITH_BYTES = Arith::PROOF_BYTES;
    static constexpr size_t OFF_BIN = 0;
    static constexpr size_t OFF_ARITH = OFF_BIN + BIN_BYTES;
    static constexpr size_t OFF_ZN = OFF_ARITH + ARITH_BYTES;
    static constexpr size_t OFF_ZP = OFF_ZN + Z_BYTES;
    static constexpr size_t OFF_Y = OFF_ZP + Z_BYTES;
    static constexpr size_t PROOF_BYTES = OFF_Y + NUM_Y_CHECKS * Y_BYTES;
};

inline Digest statement_digest(std::span<const uint8_t> msg, std::span<const uint8_t> ctx,
                               Vole vole, BinPrg prg) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_HK_STATEMENT_DST);
    h.update_byte(std::to_underlying(vole));
    h.update_byte(std::to_underlying(prg));
    for (const auto part : {msg, ctx}) {
        const uint64_t v = part.size();
        for (size_t i = 0; i < 8; ++i) {
            h.update_byte(static_cast<uint8_t>(v >> (8 * i)));
        }
        h.update(part);
    }
    Digest out;
    h.finalize(out);
    return out;
}

template <typename Bin>
LinkChallenge link_challenge(const Digest& mu, const vp::Digest& arith_chal2,
                             std::span<const uint8_t> bin_chal1,
                             std::span<const uint8_t, vole_mole::detail::PROOF_BYTES<Bin>> bin) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_HK_LINK_DST);
    h.update(mu);
    h.update(arith_chal2);
    h.update(bin_chal1);
    vole_mole::detail::hash_witness_prefix_commitment<Bin>(h, bin);
    Digest d;
    h.finalize(d);
    return derive_link_challenge(d);
}

inline Digest arith_binder(const LinkChallenge& chal, std::span<const uint8_t> link_values) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_HK_BINDER_DST);
    h.update(chal.digest);
    h.update(link_values);
    Digest d;
    h.finalize(d);
    return d;
}

inline ArithInstance arith_instance(const Fn& e, const LinkChallenge& chal,
                                    std::span<const uint8_t, Z_BYTES> zn,
                                    std::span<const uint8_t, Z_BYTES> zp,
                                    const std::array<p256::Limbs, NUM_Y_CHECKS>& y) {
    ArithInstance x;
    x.e = e;
    x.c2 = LinkChallenge::weight<Fn>(chal.xn_pos);
    x.c3 = LinkChallenge::weight<Fp>(chal.xp_pos);
    x.zn = reduce_le<Fn>(zn);
    x.zp = reduce_le<Fp>(zp);
    for (size_t i = 0; i < NUM_Y_CHECKS; ++i) {
        for (size_t l = 0; l < 2 * NUM_LIMBS; ++l) {
            x.gamma_p[i][l] = Fp::from_u64(chal.gamma[i][l]);
            x.gamma_n[i][l] = Fn::from_u64(chal.gamma[i][l]);
        }
        x.y_p[i] = Fp::from_canonical(y[i]);
        p256::Limbs d{};
        x.y_n[i] = Fn::from_canonical(p256::detail::limbs_sub(d, y[i], Fn::M) == 0 ? d : y[i]);
    }
    return x;
}

// The prover's witness.
struct Witness {
    std::vector<Fp> wp;
    std::vector<Fn> wn;
    PrefixValues bin;
    std::array<p256::Limbs, 2> u; // u1, u2
    std::array<p256::Limbs, NUM_Y_CHECKS> sigma;
};

// Compute the witness. Throws std::invalid_argument if the signature is invalid, and
// std::runtime_error in the degenerate cases of the additions (which happen with negligible
// probability for an honest key).
inline Witness make_witness(const Affine& q, std::span<const uint8_t> msg,
                            const p256::Signature& sig, std::span<const uint8_t, 32> seed) {
    if (!p256::ecdsa_verify(q, msg, sig)) {
        throw std::invalid_argument("ecdsa_pok: invalid signature");
    }
    const Offsets& off = offsets();
    const Tables& tab = comb_tables();
    const Fn r = *Fn::from_bytes(sig.r);
    const Fn s = *Fn::from_bytes(sig.s);
    const Fn e = Fn::reduce_32(sha256::hash(msg));
    const Fn w = s.inv();
    const p256::Limbs u1 = (e * w).canonical(), u2 = (r * w).canonical();

    Witness wit;
    wit.u = {u1, u2};
    wit.wp.assign(LP, Fp::zero());
    wit.wn.assign(LN, Fn::zero());
    auto digit = [](const p256::Limbs& u, size_t k) {
        return static_cast<size_t>((u[(4 * k) / 64] >> ((4 * k) % 64)) & 0xf);
    };
    const Fp three = Fp::from_u64(3);
    auto add = [](Fp& ax, Fp& ay, const Fp& tx, const Fp& ty) {
        if (tx == ax) {
            throw std::runtime_error("ecdsa_pok: degenerate addition");
        }
        const Fp lambda = (ty - ay) * (tx - ax).inv();
        const Fp nx = lambda.square() - ax - tx;
        ay = lambda * (ax - nx) - ay;
        ax = nx;
        return lambda;
    };
    auto dbl = [&](Fp& ax, Fp& ay) {
        if (ay.is_zero()) {
            throw std::runtime_error("ecdsa_pok: degenerate doubling");
        }
        const Fp lambda = (ax.square() * three - three) * (ay + ay).inv();
        const Fp nx = lambda.square() - ax - ax;
        ay = lambda * (ax - nx) - ay;
        ax = nx;
        return lambda;
    };

    wit.wp[WP_Q] = q.x;
    wit.wp[WP_Q + 1] = q.y;
    std::array<Affine, RADIX> table;
    table[0] = off.h1;
    for (size_t b = 1; b < RADIX; ++b) {
        Fp ax = table[b - 1].x, ay = table[b - 1].y;
        wit.wp[WP_TABLE + b - 1] = add(ax, ay, q.x, q.y);
        table[b] = {ax, ay, false};
    }

    Fp ax = off.h0.x, ay = off.h0.y;
    size_t si = WP_LADDER;
    for (size_t wi = 0; wi < NUM_WINDOWS; ++wi) {
        if (wi > 0) {
            for (size_t i = 0; i < DIGIT_BITS; ++i) {
                wit.wp[si++] = dbl(ax, ay);
            }
        }
        const size_t k = NUM_WINDOWS - 1 - wi;
        const size_t d = digit(u2, k);
        wit.wp[WP_B + k] = Fp::from_u64(d);
        wit.wp[si++] = add(ax, ay, table[d].x, table[d].y);
    }
    for (size_t k = 0; k < NUM_DIGITS; ++k) {
        wit.wp[WP_A + k] = Fp::from_u64(digit(u1, k));
    }
    for (size_t j = 0; j < COMB_STEPS; ++j) {
        const Affine& t = tab.at(j, digit(u1, 2 * j), digit(u1, 2 * j + 1));
        wit.wp[WP_COMB + j] = add(ax, ay, t.x, t.y);
    }
    wit.wp[WP_FINAL] = add(ax, ay, off.pstar.x, off.pstar.y);
    if (!(Fn::reduce_32(ax.to_bytes()) == r)) {
        throw std::logic_error("ecdsa_pok: x(R) != r");
    }

    // The masks.
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_HK_SEED_DST);
    h.update(seed);
    Keccak_HashFinal(&h.ctx, nullptr);
    squeeze_bits(h.ctx, wit.bin.rho_n, RHO_BITS);
    squeeze_bits(h.ctx, wit.bin.rho_p, RHO_BITS);
    for (auto& sg : wit.sigma) {
        std::array<uint8_t, 32> b;
        squeeze_bits(h.ctx, b, 255);
        sg = load_limbs_le(b.data());
    }

    wit.wp[WP_RHO] = reduce_le<Fp>(wit.bin.rho_p);
    for (size_t i = 0; i < NUM_Y_CHECKS; ++i) {
        wit.wp[WP_SIGMA + i] = Fp::from_canonical(wit.sigma[i]);
        wit.wn[WN_SIGMA + i] = Fn::from_canonical(wit.sigma[i]);
    }
    for (size_t l = 0; l < NUM_LIMBS; ++l) {
        wit.wn[WN_U1 + l] = Fn::from_u64(u1[l]);
        wit.wn[WN_U2 + l] = Fn::from_u64(u2[l]);
    }
    const Fn xn = Fn::reduce_32(ax.to_bytes());
    wit.wn[WN_X] = xn;
    wit.wn[WN_INV] = (Fn::from_canonical(u2) * xn).inv();
    wit.wn[WN_RHO] = reduce_le<Fn>(wit.bin.rho_n);
    store_limbs_le(wit.bin.x.data(), ax.canonical());
    return wit;
}

inline std::array<p256::Limbs, NUM_Y_CHECKS> y_values(const Witness& wit,
                                                      const LinkChallenge& chal) {
    std::array<p256::Limbs, NUM_Y_CHECKS> out;
    for (size_t i = 0; i < NUM_Y_CHECKS; ++i) {
        Fp acc = Fp::from_canonical(wit.sigma[i]);
        for (size_t s = 0; s < 2; ++s) {
            for (size_t l = 0; l < NUM_LIMBS; ++l) {
                acc += Fp::from_u64(chal.gamma[i][NUM_LIMBS * s + l]) * Fp::from_u64(wit.u[s][l]);
            }
        }
        out[i] = acc.canonical();
    }
    return out;
}

template <Vole V, BinPrg PRG>
void prove_with_witness(std::span<uint8_t, Scheme<V, PRG>::PROOF_BYTES> proof, const Digest& mu,
                        const Fn& e, const Witness& wit, std::span<const uint8_t, 32> seed) {
    using S = Scheme<V, PRG>;
    using Bin = typename S::Bin;
    using VP = typename S::VP;
    const auto bin = proof.template subspan<S::OFF_BIN, S::BIN_BYTES>();
    const auto ar = proof.template subspan<S::OFF_ARITH, S::ARITH_BYTES>();
    const auto zn = proof.template subspan<S::OFF_ZN, Z_BYTES>();
    const auto zp = proof.template subspan<S::OFF_ZP, Z_BYTES>();

    vp::ProveSeed rho_arith;
    vole_mole::detail::ProveSeed<Bin> rho_bin;
    {
        faest::hash_state h;
        h.init(faest::secpar::s128);
        h.update(vole_mole::detail::ECDSA_HK_SEED_DST);
        h.update(seed);
        h.update_byte(1);
        std::array<uint8_t, sizeof(rho_arith) + sizeof(rho_bin)> b;
        h.finalize(b);
        std::memcpy(rho_arith.data(), b.data(), rho_arith.size());
        std::memcpy(rho_bin.data(), b.data() + rho_arith.size(), rho_bin.size());
    }

    auto arith_state = vp::prove_commit<HkArithRelation, VP>(
        ar, mu, std::span<const Fp, LP>(wit.wp), std::span<const Fn, LN>(wit.wn), rho_arith);

    std::vector<uint8_t> bin_witness(Bin::RELATION_WITNESS_BITS / 8, 0);
    PlainOps ops{bin_witness};
    const auto wires = prefix_circuit<Bin::SH.sha_log>(ops, &wit.bin);
    auto pending = vole_mole::detail::voleith_vole_gen<Bin>(
        bin, nullptr,
        std::span<const uint8_t, Bin::WITNESS_PREFIX_BYTES>(bin_witness.data(),
                                                            Bin::WITNESS_PREFIX_BYTES),
        rho_bin, mu);

    const LinkChallenge chal = hk::link_challenge<Bin>(mu, arith_state.chal2, pending.chal1, bin);
    ops.next = 8 * Bin::WITNESS_PREFIX_BYTES;
    link_circuit<Bin::SH.link_log>(ops, wires, chal, zn, zp, true);
    const auto y = hk::y_values(wit, chal);
    for (size_t i = 0; i < NUM_Y_CHECKS; ++i) {
        store_limbs_le(proof.data() + S::OFF_Y + i * Y_BYTES, y[i]);
    }

    typename Bin::instance bin_inst{&mu, &chal, {}, {}};
    std::ranges::copy(zn, bin_inst.zn.begin());
    std::ranges::copy(zp, bin_inst.zp.begin());
    vole_mole::detail::voleith_prove_commit<Bin>(
        bin, bin_inst,
        std::span<const uint8_t, vole_mole::detail::WITNESS_SUFFIX_BYTES<Bin>>(
            bin_witness.data() + Bin::WITNESS_PREFIX_BYTES,
            vole_mole::detail::WITNESS_SUFFIX_BYTES<Bin>),
        std::move(pending));

    const ArithInstance ar_inst = hk::arith_instance(e, chal, zn, zp, y);
    const Digest binder = hk::arith_binder(chal, proof.subspan(S::OFF_ZN));
    vp::prove_finish<HkArithRelation, VP>(ar, arith_state, ar_inst, binder);
}

template <Vole V, BinPrg PRG>
bool verify_proof(std::span<const uint8_t, Scheme<V, PRG>::PROOF_BYTES> proof, const Digest& mu,
                  const Fn& e) {
    using S = Scheme<V, PRG>;
    using Bin = typename S::Bin;
    using VP = typename S::VP;
    const auto bin = proof.template subspan<S::OFF_BIN, S::BIN_BYTES>();
    const auto ar = proof.template subspan<S::OFF_ARITH, S::ARITH_BYTES>();
    const auto zn = proof.template subspan<S::OFF_ZN, Z_BYTES>();
    const auto zp = proof.template subspan<S::OFF_ZP, Z_BYTES>();

    for (const auto z : {zn, zp}) {
        for (size_t i = Z_COLS; i < 8 * Z_BYTES; ++i) {
            if (get_bit(z, i)) {
                return false;
            }
        }
    }
    std::array<p256::Limbs, NUM_Y_CHECKS> y;
    for (size_t i = 0; i < NUM_Y_CHECKS; ++i) {
        y[i] = load_limbs_le(proof.data() + S::OFF_Y + i * Y_BYTES);
        if (!y_in_range(y[i])) {
            return false;
        }
    }

    auto pending = vole_mole::detail::voleith_vole_reconstruct<Bin>(bin, nullptr, mu);
    if (!pending) {
        return false;
    }
    const auto arith_state = vp::verify_commit<HkArithRelation, VP>(ar, mu);
    if (!arith_state) {
        return false;
    }
    const LinkChallenge chal = hk::link_challenge<Bin>(mu, arith_state->chal2, pending->chal1, bin);

    typename Bin::instance bin_inst{&mu, &chal, {}, {}};
    std::ranges::copy(zn, bin_inst.zn.begin());
    std::ranges::copy(zp, bin_inst.zp.begin());
    if (!vole_mole::detail::voleith_verify_commit<Bin>(bin, bin_inst, std::move(*pending))) {
        return false;
    }

    const ArithInstance ar_inst = hk::arith_instance(e, chal, zn, zp, y);
    const Digest binder = hk::arith_binder(chal, proof.subspan(S::OFF_ZN));
    return vp::verify_finish<HkArithRelation, VP>(ar, *arith_state, ar_inst, binder);
}

// Call f.template operator()<V, PRG>() for the parameters.
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

// Prove knowledge of a public key pk and a signature sig on msg under it, for context ctx. Throws
// as ecdsa_pok::prove.
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
    const BinPrg prg = static_cast<BinPrg>(std::to_underlying(params.prg));
    const Digest mu = statement_digest(msg, ctx, params.vole, prg);
    const Fn e = Fn::reduce_32(sha256::hash(msg));
    constexpr int ATTEMPTS = 8;
    for (int attempt = 1;; ++attempt) {
        const auto seed = random_bytes<32>();
        try {
            const Witness wit = make_witness(*q, msg, s, seed);
            return dispatch(params, [&]<Vole V, BinPrg PRG>() {
                std::vector<uint8_t> proof(Scheme<V, PRG>::PROOF_BYTES);
                prove_with_witness<V, PRG>(std::span<uint8_t, Scheme<V, PRG>::PROOF_BYTES>(proof),
                                           mu, e, wit, seed);
                return proof;
            });
        } catch (const std::runtime_error&) {
            if (attempt == ATTEMPTS) {
                throw;
            }
        }
    }
}

// Verify a proof of knowledge of a public key and a signature on msg under it, for context ctx.
inline bool verify(std::span<const uint8_t> msg, std::span<const uint8_t> ctx,
                   std::span<const uint8_t> proof, Params params = {}) {
    if (proof.size() != proof_bytes(params)) {
        return false;
    }
    const BinPrg prg = static_cast<BinPrg>(std::to_underlying(params.prg));
    const Digest mu = statement_digest(msg, ctx, params.vole, prg);
    const Fn e = Fn::reduce_32(sha256::hash(msg));
    return dispatch(params, [&]<Vole V, BinPrg PRG>() {
        return verify_proof<V, PRG>(
            std::span<const uint8_t, Scheme<V, PRG>::PROOF_BYTES>(proof.data(), proof.size()), mu,
            e);
    });
}

} // namespace vole_mole::ecdsa_pok::detail::hk

#endif
