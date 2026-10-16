// A zero-knowledge proof of knowledge of an ECDSA-P256-SHA256 signature on a hidden message.
//
// Statement. Public: the public key Q, the message length, and a context string. Secret: the
// message m and the signature (r, s). The prover shows that ECDSA.Verify(Q, m, (r, s)) = 1, i.e.,
// with e = SHA-256(m) (an integer), r, s in [1, n), u1 = e/s, u2 = r/s mod n, and
// R = u1 G + u2 Q != O, that x(R) = r mod n.
//
// Reformulation. A valid signature exists iff there are integers u1, u2 in [0, 2^256), a point R
// and X = x(R) in [0, p) such that
//
//   (a) R = u1 G + u2 Q (as an affine point, so R != O),
//   (b) u1 X = u2 e (mod n), and u2 X != 0 (mod n),
//   (c) e = SHA-256(m).
//
// Given a signature, (a)-(c) hold for u1 = e/s, u2 = r/s, and R, X as in verification: then
// u1 X = e r / s = u2 e, and u2 X = r^2 / s != 0. Conversely, given (a)-(c), let r = X mod n and
// s = X / u2 mod n; both are nonzero, r/s = u2 and e/s = e u2 / X = u1, so verification computes R
// and accepts. The verifier never needs r and s themselves, and there's no inversion modulo n.
//
// Proof. Each part of the statement is proven where it's cheap:
//
//   - (c), on bits, in FAEST's binary VOLEitH (binary.hpp): the SHA-256 compressions, X < p, and
//     X as 256 committed bits. By default, the binary witness is derived from a short key with
//     the local PRG (see "Derived witnesses" in voleith.hpp), so each of its bits costs one bit of
//     proof rather than tau;
//   - (a), over F_p, in a VOLEitH over the fields of P-256 (voleith_p256/), with a fixed-base comb
//     on the digits of u1, u2 (arith.hpp);
//   - (b), over F_n, in the same VOLEitH.
//
// Values shared between the proofs are linked by random linear combinations, revealed with masks:
//
//   - e (bits) and X (bits) to F_n: Z_n = c_1 e + c_2 X + rho_n. The binary proof shows this over
//     the integers (by column compression), for the committed bits of e, X, and rho_n; the proof
//     over F_n shows Z_n = c_1 e' + c_2 X' + rho_n' (mod n) for its committed e', X', rho_n'. Z_n
//     is public.
//   - X (bits) to F_p: likewise, Z_p = c_3 X + rho_p, where the proof over F_p uses its expression
//     for x(R).
//   - u1, u2 (digits over F_p) to F_n (limbs): Y_i = sum_l gamma_{i,l} L_l + sigma_i, for the
//   64-bit
//     limbs L_l of u1 and u2 (two checks, i = 1, 2).
//
// The link challenge (the c_i and gamma_{i,l}) is derived from the commitments to the binary
// witness prefix and to the whole witness over F_p and F_n, so all the masks and linked values are
// fixed before it. The carries of the binary link sums depend on the c_i, so they're committed
// afterwards (in the second step of the binary proof).
//
// Soundness of the links. For the binary to F_n link, subtracting the two equations gives
// c_1 (e - e') + c_2 (X - X') = rho_n' - rho_n (mod n), where the right-hand side is fixed before
// the challenge. Each c_i is a sum of 31 distinct powers 2^j, j < 256 (link.hpp); there are
// C(256, 31) > 2^132 such sums, each residue modulo n arises from at most two of them, so if
// e != e' or X != X' (mod n), then the equation holds with probability less than 2^-131. Likewise
// for F_p. For the F_p to F_n link, the limbs are exact integers over F_p (combinations of digits
// in [0, 16), checked by their range constraints), so sum_l gamma_l L_l < 2^131. The verifier
// checks Y_i < 2^255 + 2^132; since 2^255 + 2^132 + 2^131 < p, the equation over F_p determines
// the integer Y_i - sum_l gamma_l L_l, which is then fixed before the challenge. Subtracting the
// equation over F_n, sum_l gamma_l (L_l - L_l') is fixed modulo n, which happens with probability
// at most 2^-64 for each check if some L_l != L_l' (mod n), with 64-bit gamma_l. Two checks give
// 2^-128.
//
// Zero knowledge of the links. rho_n is uniform in [0, 2^641) and c_1 e + c_2 X < 2^513, so Z_n is
// within statistical distance 2^-128 of a value independent of e and X; likewise for Z_p. sigma_i
// is uniform in [0, 2^255) and the sums less than 2^131, so Y_i is within 2^-124.
//
// Then, given (c) on bits, X < p, e' = e and X' = X mod n, x(R) = X mod p (so X is the canonical
// x(R)), and the limbs of u1, u2 over F_n are the digits' integers modulo n, (a) and (b) hold.

#ifndef VOLE_MOLE_ECDSA_POK_RELATION_HPP
#define VOLE_MOLE_ECDSA_POK_RELATION_HPP

#include "vole_mole/ecdsa_pok.hpp"

#include "dst.hpp"
#include "ecdsa_pok/arith.hpp"
#include "ecdsa_pok/bin_ops.hpp"
#include "ecdsa_pok/binary.hpp"
#include "ecdsa_pok/link.hpp"
#include "ecdsa_pok/sha256_circuit.hpp"
#include "p256/curve.hpp"
#include "p256/field.hpp"
#include "sha256/sha256.hpp"
#include "voleith.hpp"
#include "voleith_p256/voleith.hpp"

#include "hash.hpp"       // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt

#include <algorithm>
#include <type_traits>
#include <utility>

extern "C" {
#include "KeccakHash.h" // from xkcp
}

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <span>
#include <stdexcept>
#include <vector>

namespace vole_mole::ecdsa_pok::detail {

namespace vp = vole_mole::voleith_p256;

constexpr size_t Y_BYTES = 32;

template <size_t NB, Vole V, BinPrg PRG> struct Scheme {
    using Bin = BinRelation<NB, V == Vole::small, PRG>;
    using VP = std::conditional_t<V == Vole::small, vp::Small,
                                  std::conditional_t<V == Vole::medium, vp::Medium, vp::Fast>>;
    // With the local PRG, the F_p witness is derived too (with the MQ PRG, it isn't: the local PRG
    // over F_p is an experimental assumption).
    using AR = WithDerivedWitness<ArithRelation, PRG == BinPrg::local>;
    using Arith = vp::Layout<AR, VP>;

    static constexpr size_t BIN_BYTES = vole_mole::detail::PROOF_BYTES<Bin>;
    static constexpr size_t ARITH_BYTES = Arith::PROOF_BYTES;
    static constexpr size_t OFF_BIN = 0;
    static constexpr size_t OFF_ARITH = OFF_BIN + BIN_BYTES;
    static constexpr size_t OFF_ZN = OFF_ARITH + ARITH_BYTES;
    static constexpr size_t OFF_ZP = OFF_ZN + Z_BYTES;
    static constexpr size_t OFF_Y = OFF_ZP + Z_BYTES;
    static constexpr size_t PROOF_BYTES = OFF_Y + NUM_Y_CHECKS * Y_BYTES;
};

inline Digest statement_digest(const p256::PublicKeyBytes& pk, size_t msg_len,
                               std::span<const uint8_t> ctx, Vole vole, BinPrg prg) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_POK_STATEMENT_DST);
    h.update_byte(std::to_underlying(vole));
    h.update_byte(std::to_underlying(prg));
    h.update(pk);
    for (const uint64_t v : {uint64_t{msg_len}, uint64_t{ctx.size()}}) {
        for (size_t i = 0; i < 8; ++i) {
            h.update_byte(static_cast<uint8_t>(v >> (8 * i)));
        }
    }
    h.update(ctx);
    Digest out;
    h.finalize(out);
    return out;
}

// The link challenge, from the commitments of both proofs.
template <typename Bin>
LinkChallenge link_challenge(const Digest& mu, const vp::Digest& arith_chal2,
                             std::span<const uint8_t> bin_chal1,
                             std::span<const uint8_t, vole_mole::detail::PROOF_BYTES<Bin>> bin) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_POK_LINK_DST);
    h.update(mu);
    h.update(arith_chal2);
    h.update(bin_chal1);
    // The commitment to the binary witness prefix: its correction, or, if it's derived, the
    // correction of the key and the prefix of e.
    vole_mole::detail::hash_witness_prefix_commitment<Bin>(h, bin);
    Digest d;
    h.finalize(d);
    return derive_link_challenge(d);
}

// The binder of the QuickSilver challenges over F_p and F_n.
inline Digest arith_binder(const LinkChallenge& chal, std::span<const uint8_t> link_values) {
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_POK_BINDER_DST);
    h.update(chal.digest);
    h.update(link_values);
    Digest d;
    h.finalize(d);
    return d;
}

inline ArithInstance arith_instance(const Tables* tables, const LinkChallenge& chal,
                                    std::span<const uint8_t, Z_BYTES> zn,
                                    std::span<const uint8_t, Z_BYTES> zp,
                                    const std::array<p256::Limbs, NUM_Y_CHECKS>& y) {
    ArithInstance x;
    x.tables = tables;
    x.c1 = LinkChallenge::weight<Fn>(chal.e_pos);
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
        // y < 2^256 < 2 n
        p256::Limbs d{};
        x.y_n[i] = Fn::from_canonical(p256::detail::limbs_sub(d, y[i], Fn::M) == 0 ? d : y[i]);
    }
    return x;
}

inline void store_limbs_le(uint8_t* out, const p256::Limbs& x) {
    for (size_t i = 0; i < 32; ++i) {
        out[i] = static_cast<uint8_t>(x[i / 8] >> (8 * (i % 8)));
    }
}
inline p256::Limbs load_limbs_le(const uint8_t* in) {
    p256::Limbs x{};
    for (size_t i = 0; i < 32; ++i) {
        x[i / 8] |= uint64_t{in[i]} << (8 * (i % 8));
    }
    return x;
}

// The prover's witness.
struct Witness {
    std::vector<Fp> wp;           // ArithRelation's F_p witness
    std::vector<Fn> wn;           // F_n witness
    PrefixValues bin;             // the binary witness prefix's values
    std::array<p256::Limbs, 2> u; // u1, u2 (integers of the digits)
    std::array<p256::Limbs, NUM_Y_CHECKS> sigma;
};

// A uniform integer below 2^bits from a SHAKE stream.
inline void squeeze_bits(Keccak_HashInstance& ctx, std::span<uint8_t> out, size_t bits) {
    Keccak_HashSqueeze(&ctx, out.data(), 8 * out.size());
    for (size_t i = bits; i < 8 * out.size(); ++i) {
        set_bit(out, i, false);
    }
}

// Compute the witness from the message and signature. The prover's masks are derived from seed.
// Throws std::invalid_argument if the signature is invalid, and std::runtime_error in the
// degenerate cases of the comb (which happen with negligible probability).
inline Witness make_witness(const Affine& q, const Tables& tables, std::span<const uint8_t> msg,
                            const p256::Signature& sig, std::span<const uint8_t, 32> seed) {
    if (!p256::ecdsa_verify(q, msg, sig)) {
        throw std::invalid_argument("ecdsa_pok: invalid signature");
    }
    const Fn r = *Fn::from_bytes(sig.r);
    const Fn s = *Fn::from_bytes(sig.s);
    const auto e_bytes = sha256::hash(msg);
    const Fn e = Fn::reduce_32(e_bytes);
    const Fn w = s.inv();
    const p256::Limbs u1 = (e * w).canonical(), u2 = (r * w).canonical();

    Witness wit;
    wit.u = {u1, u2};
    wit.wp.assign(LP, Fp::zero());
    wit.wn.assign(LN, Fn::zero());
    auto digit = [](const p256::Limbs& u, size_t k) {
        return static_cast<size_t>((u[(4 * k) / 64] >> ((4 * k) % 64)) & 0xf);
    };

    // The comb.
    std::vector<p256::ChainStep> steps;
    steps.reserve(NUM_STEPS);
    for (size_t k = 0; k < NUM_STEPS; ++k) {
        steps.push_back(
            {false, k < NUM_DIGITS ? tables.at(k, digit(u1, k), digit(u2, k)) : tables.pstar});
        if (k < NUM_DIGITS) {
            wit.wp[WP_A + k] = Fp::from_u64(digit(u1, k));
            wit.wp[WP_B + k] = Fp::from_u64(digit(u2, k));
        }
    }
    const p256::Chain chain = p256::slope_chain(tables.h0, steps);
    std::copy(chain.slopes.begin(), chain.slopes.end(), wit.wp.begin() + WP_LAMBDA);
    const Fp ax = chain.points.back().x;
    const p256::Limbs x_limbs = ax.canonical();
    if (!(Fn::reduce_32(ax.to_bytes()) == r)) {
        throw std::logic_error("ecdsa_pok: x(R) != r");
    }

    // The masks.
    faest::hash_state h;
    h.init(faest::secpar::s128);
    h.update(vole_mole::detail::ECDSA_POK_SEED_DST);
    h.update(seed);
    Keccak_HashFinal(&h.ctx, nullptr);
    squeeze_bits(h.ctx, wit.bin.rho_n, RHO_N_BITS);
    squeeze_bits(h.ctx, wit.bin.rho_p, RHO_P_BITS);
    for (auto& sg : wit.sigma) {
        std::array<uint8_t, 32> b;
        squeeze_bits(h.ctx, b, 255);
        sg = load_limbs_le(b.data());
    }

    wit.wp[WP_RHO] = reduce_le<Fp>(wit.bin.rho_p);
    for (size_t i = 0; i < NUM_Y_CHECKS; ++i) {
        wit.wp[WP_SIGMA + i] = Fp::from_canonical(wit.sigma[i]); // < 2^255 < p
        wit.wn[WN_SIGMA + i] = Fn::from_canonical(wit.sigma[i]); // < 2^255 < n
    }
    for (size_t l = 0; l < NUM_LIMBS; ++l) {
        wit.wn[WN_U1 + l] = Fn::from_u64(u1[l]);
        wit.wn[WN_U2 + l] = Fn::from_u64(u2[l]);
    }
    const Fn xn = Fn::reduce_32(ax.to_bytes());
    wit.wn[WN_E] = e;
    wit.wn[WN_X] = xn;
    wit.wn[WN_INV] = (Fn::from_canonical(u2) * xn).inv();
    wit.wn[WN_RHO] = reduce_le<Fn>(wit.bin.rho_n);

    wit.bin.padded = sha256::pad(msg);
    store_limbs_le(wit.bin.x.data(), x_limbs);
    return wit;
}

// Y_i = sum_l gamma_{i,l} L_l + sigma_i.
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
        out[i] = acc.canonical(); // < p, so this is the integer
    }
    return out;
}

template <size_t NB, Vole V, BinPrg PRG>
void prove_with_witness(std::span<uint8_t, Scheme<NB, V, PRG>::PROOF_BYTES> proof, const Digest& mu,
                        size_t msg_len, const Tables& tables, const Witness& wit,
                        std::span<const uint8_t, 32> seed) {
    using S = Scheme<NB, V, PRG>;
    using Bin = typename S::Bin;
    using VP = typename S::VP;
    const auto bin = proof.template subspan<S::OFF_BIN, S::BIN_BYTES>();
    const auto ar = proof.template subspan<S::OFF_ARITH, S::ARITH_BYTES>();
    const auto zn = proof.template subspan<S::OFF_ZN, Z_BYTES>();
    const auto zp = proof.template subspan<S::OFF_ZP, Z_BYTES>();

    // Per-proof randomness.
    vp::ProveSeed rho_arith;
    vole_mole::detail::ProveSeed<Bin> rho_bin;
    {
        faest::hash_state h;
        h.init(faest::secpar::s128);
        h.update(vole_mole::detail::ECDSA_POK_SEED_DST);
        h.update(seed);
        h.update_byte(1);
        std::array<uint8_t, sizeof(rho_arith) + sizeof(rho_bin)> b;
        h.finalize(b);
        std::memcpy(rho_arith.data(), b.data(), rho_arith.size());
        std::memcpy(rho_bin.data(), b.data() + rho_arith.size(), rho_bin.size());
    }

    // Commit to the witness over F_p and F_n.
    auto arith_state = vp::prove_commit<typename S::AR, VP>(
        ar, mu, std::span<const Fp, LP>(wit.wp), std::span<const Fn, LN>(wit.wn), rho_arith);

    // The binary witness prefix, and its commitment.
    std::vector<uint8_t> bin_witness(Bin::RELATION_WITNESS_BITS / 8, 0);
    PlainOps ops{bin_witness};
    const auto wires = prefix_circuit<Bin::SH.small_log>(ops, msg_len, &wit.bin);
    auto pending = vole_mole::detail::voleith_vole_gen<Bin>(
        bin, nullptr,
        std::span<const uint8_t, Bin::WITNESS_PREFIX_BYTES>(bin_witness.data(),
                                                            Bin::WITNESS_PREFIX_BYTES),
        rho_bin, mu);

    // The link challenge and values.
    const LinkChallenge chal = link_challenge<Bin>(mu, arith_state.chal2, pending.chal1, bin);
    ops.next = 8 * Bin::WITNESS_PREFIX_BYTES;
    link_circuit<Bin::SH.link_log>(ops, wires, chal, zn, zp, true);
    const auto y = y_values(wit, chal);
    for (size_t i = 0; i < NUM_Y_CHECKS; ++i) {
        store_limbs_le(proof.data() + S::OFF_Y + i * Y_BYTES, y[i]);
    }

    // Finish the binary proof.
    const Statement stmt{mu, msg_len};
    typename Bin::instance bin_inst{&stmt, &chal, {}, {}};
    std::ranges::copy(zn, bin_inst.zn.begin());
    std::ranges::copy(zp, bin_inst.zp.begin());
    vole_mole::detail::voleith_prove_commit<Bin>(
        bin, bin_inst,
        std::span<const uint8_t, vole_mole::detail::WITNESS_SUFFIX_BYTES<Bin>>(
            bin_witness.data() + Bin::WITNESS_PREFIX_BYTES,
            vole_mole::detail::WITNESS_SUFFIX_BYTES<Bin>),
        std::move(pending));

    // Finish the proof over F_p and F_n.
    const ArithInstance ar_inst = arith_instance(&tables, chal, zn, zp, y);
    const Digest binder = arith_binder(chal, proof.subspan(S::OFF_ZN));
    vp::prove_finish<typename S::AR, VP>(ar, arith_state, ar_inst, binder);
}

template <size_t NB, Vole V, BinPrg PRG>
bool verify_proof(std::span<const uint8_t, Scheme<NB, V, PRG>::PROOF_BYTES> proof, const Digest& mu,
                  size_t msg_len, const Tables& tables) {
    using S = Scheme<NB, V, PRG>;
    using Bin = typename S::Bin;
    using VP = typename S::VP;
    const auto bin = proof.template subspan<S::OFF_BIN, S::BIN_BYTES>();
    const auto ar = proof.template subspan<S::OFF_ARITH, S::ARITH_BYTES>();
    const auto zn = proof.template subspan<S::OFF_ZN, Z_BYTES>();
    const auto zp = proof.template subspan<S::OFF_ZP, Z_BYTES>();

    // The link values must be in range.
    for (size_t i = ZN_COLS; i < 8 * Z_BYTES; ++i) {
        if (get_bit(zn, i)) {
            return false;
        }
    }
    for (size_t i = ZP_COLS; i < 8 * Z_BYTES; ++i) {
        if (get_bit(zp, i)) {
            return false;
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
    const auto arith_state = vp::verify_commit<typename S::AR, VP>(ar, mu);
    if (!arith_state) {
        return false;
    }
    const LinkChallenge chal = link_challenge<Bin>(mu, arith_state->chal2, pending->chal1, bin);

    const Statement stmt{mu, msg_len};
    typename Bin::instance bin_inst{&stmt, &chal, {}, {}};
    std::ranges::copy(zn, bin_inst.zn.begin());
    std::ranges::copy(zp, bin_inst.zp.begin());
    if (!vole_mole::detail::voleith_verify_commit<Bin>(bin, bin_inst, std::move(*pending))) {
        return false;
    }

    const ArithInstance ar_inst = arith_instance(&tables, chal, zn, zp, y);
    const Digest binder = arith_binder(chal, proof.subspan(S::OFF_ZN));
    return vp::verify_finish<typename S::AR, VP>(ar, *arith_state, ar_inst, binder);
}

} // namespace vole_mole::ecdsa_pok::detail

#endif
