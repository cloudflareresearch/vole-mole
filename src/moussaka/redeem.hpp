// QuickSilver constraints for the redemption proof:
//
//   Instance: P[0], ..., P[N-1] (Anchor Set) where N <= MAX_ANCHORS, nf (nullifier), ctx_iss
//             (issuance context), ctx_red (redemption context)
//   Witness:  r (opening), s (UOV preimage), b (selector)
//   Constraints:
//     - Q(s) = Com(nf, ctx_iss, ctx_red, r), where Q = sum_u b[u] * P[u]
//     - sum(b[0..u+1]) * b[u+1] = 0 for u in [N-1] (parity constraints)
//     - sum(b) = 1 (weight constraint)
//
// Arithmetization: The commitment is evaluated as described in keccak/segmented.hpp, which adds
// 800 constraints of degree at most 9 for each of the two committed intermediate states. Rather
// than constraining each of the 8 * M bits of the output of the last segment, we combine each byte
// of the output (degree 8) into an element of the GF(256) subfield of GF(2^128), so that the M
// components of Q(s) can be compared directly. Rather than comparing each of the M components, we
// compare a random linear combination l of them, with coefficients in GF(2^128) derived from the
// QuickSilver challenge (see uov::detail::Combination). l(Q(s)) is computed as
// sum_u b[u] * l(P[u](s)): each l(P[u](s)) has degree 2 (see uov/circuit.hpp), so l(Q(s)) has
// degree 3, and the single output constraint has degree 8.
//
// The selector b is a vector of MAX_ANCHORS bits. Each bit is constrained to be a bit, or to be
// zero if it's beyond the end of the Anchor Set. Since every b[u] is a bit, the parity constraints
// (degree 2) and the weight constraint (degree 1) imply that exactly one bit is set: if b[v] = 1,
// then the parity constraint for v - 1 implies that an even number of bits below v are set; if v is
// the second-lowest set bit, then this is a contradiction. The witness layout is as follows:
//
//     0 ..  16   r
//    16 .. 135   s
//   135 .. 235   s5, the state after 5 rounds of the commitment
//   235 .. 335   s9, the state after 9 rounds of the commitment
//   335 .. 343   b, with b[u] at bit u % 8 of byte 335 + u / 8
//
// Every bit of r, s, and the intermediate states is constrained to be a bit, adding 2680
// constraints of degree 2.
//
// We use the VOLE-in-the-Head parameters of FAEST-EM-128f v3. Optionally, the witness is derived
// from a short key with the witness PRG RedeemWitnessPrg (see "Derived witnesses" in voleith.hpp).
// Then the witness bits are committed values of degree 2, so all of the degrees above double.
// (The bit constraints on the witness are then redundant, as the bits of the key are constrained
// to be bits, but they're cheap.)

#ifndef VOLE_MOLE_MOUSSAKA_REDEEM_HPP
#define VOLE_MOLE_MOUSSAKA_REDEEM_HPP

#include "vole_mole/moussaka.hpp"
#include "vole_mole/uov.hpp"

#include "ct.hpp"
#include "dst.hpp"
#include "keccak/segmented.hpp"
#include "moussaka/commit.hpp"
#include "qs_bit.hpp"
#include "uov/circuit.hpp"
#include "uov/public_key.hpp"
#include "voleith.hpp"
#include "witness_prg.hpp"

#include "constants.hpp"   // from faest-arch-opt
#include "hash.hpp"        // from faest-arch-opt
#include "parameters.hpp"  // from faest-arch-opt
#include "polynomials.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <type_traits>

namespace vole_mole::moussaka::detail {

constexpr size_t REDEEM_QS_DEGREE =
    std::max(keccak::detail::QS_DEGREE, size_t{3}); // Q(s) has degree 3
static_assert(REDEEM_QS_DEGREE - 1 + 4 <= 32, "faest-arch-opt supports at most 32 masks");

using AnchorSpan = std::span<const AnchorRef>;

// Witness layout.
constexpr size_t REDEEM_WIT_OFF_R = 0;
constexpr size_t REDEEM_WIT_OFF_S = REDEEM_WIT_OFF_R + R_BYTES;
constexpr size_t REDEEM_WIT_OFF_STATES = REDEEM_WIT_OFF_S + uov::N;
constexpr size_t REDEEM_WIT_OFF_B = REDEEM_WIT_OFF_STATES + keccak::detail::COMMITTED_STATES_BYTES;
static_assert(MAX_ANCHORS % 8 == 0 && MAX_ANCHORS > 0);
constexpr size_t SELECTOR_BYTES = MAX_ANCHORS / 8;
constexpr size_t REDEEM_WITNESS_BYTES = REDEEM_WIT_OFF_B + SELECTOR_BYTES;
constexpr size_t REDEEM_WITNESS_BITS = 8 * REDEEM_WITNESS_BYTES;

// The witness index of the bit b[u] of the selector.
constexpr size_t selector_bit(size_t u) { return 8 * REDEEM_WIT_OFF_B + u; }

// Map of the index of each byte of the input of Com to its index in the witness.
// Only the opening is secret.
constexpr keccak::detail::InputMap REDEEM_COM_TO_WIT = [] {
    keccak::detail::InputMap map;
    map.fill(-1);
    for (size_t i = 0; i < R_BYTES; ++i) {
        map[COM_OFF_R + i] = static_cast<int>(REDEEM_WIT_OFF_R + i);
    }
    return map;
}();
static_assert(keccak::detail::input_map_is_valid(REDEEM_COM_TO_WIT, REDEEM_WIT_OFF_R,
                                                 REDEEM_WIT_OFF_R + R_BYTES),
              "REDEEM_COM_TO_WIT is malformed");

constexpr size_t REDEEM_NUM_CONSTRAINTS =
    8 * REDEEM_WIT_OFF_B // bit constraints for r, s, and the intermediate states
    + MAX_ANCHORS        // each selector bit is a bit (or zero if beyond the Anchor Set)
    + (MAX_ANCHORS - 1)  // parity constraints
    + 1                  // weight constraint
    + keccak::detail::NUM_SEGMENT_CONSTRAINTS // segment ends in a committed state
    + 1; // Q(s) = commitment (a random linear combination of the M components)

// Compute the full witness, including the intermediate Keccak states and the selector for the
// Anchor at index i.
inline std::array<uint8_t, REDEEM_WITNESS_BYTES>
encode_redeem_witness(const Nullifier& nf, const Context& ctx_iss, const Context& ctx_red,
                      const Opening& r, const uov::Preimage& s, size_t i) {
    std::array<uint8_t, REDEEM_WITNESS_BYTES> w{};
    std::ranges::copy(r, w.begin() + REDEEM_WIT_OFF_R);
    std::ranges::copy(s, w.begin() + REDEEM_WIT_OFF_S);
    keccak::detail::encode_committed_states(
        std::span(w).subspan<REDEEM_WIT_OFF_STATES, keccak::detail::COMMITTED_STATES_BYTES>(),
        encode_com_state(nf, ctx_iss, ctx_red, r));
    // Write every selector bit so that the memory access pattern doesn't depend on i.
    for (size_t u = 0; u < MAX_ANCHORS; ++u) {
        const size_t b = selector_bit(u);
        w[b / 8] |= static_cast<uint8_t>(vole_mole::detail::ct_eq_mask(u, i) & (1u << (b % 8)));
    }
    return w;
}

// The VOLEitH parameter set for RedeemRelation.
constexpr faest::owf OWF_MOUSSAKA_REDEEM =
    static_cast<faest::owf>((0x52u << 8) | 0b10'0000 /* owf_flag_witness_bits_check */);
static_assert(faest::is_owf_with_witness_bits_check(OWF_MOUSSAKA_REDEEM));
static_assert(!faest::is_owf_with_aes_ecb(OWF_MOUSSAKA_REDEEM));
static_assert(!faest::is_owf_with_aes_em(OWF_MOUSSAKA_REDEEM));

// Commit to the witness directly rather than deriving it from a short key with a PRG (see
// "Derived witnesses" in voleith.hpp and witness_prg.hpp). MqPrg<2> makes the proof much smaller,
// at the cost of proving and verification time; it then deviates from the draft, and
// REDEEM_PROOF_BYTES must be updated.
using RedeemWitnessPrg = vole_mole::detail::NoPrg;

} // namespace vole_mole::moussaka::detail

// Must be declared outside of our namespace, since it specializes a template of faest-arch-opt.
template <>
struct faest::OWF_CONSTANTS<faest::secpar::s128, vole_mole::moussaka::detail::OWF_MOUSSAKA_REDEEM>
    : vole_mole::detail::RelationConstants<vole_mole::moussaka::detail::REDEEM_WITNESS_BITS,
                                           vole_mole::moussaka::detail::REDEEM_QS_DEGREE,
                                           vole_mole::moussaka::detail::RedeemWitnessPrg> {};

namespace vole_mole::moussaka::detail {

// Same as faest::v3::faest_em_128_f, except for the OWF.
using RedeemParams =
    faest::parameter_set<faest::secpar::s128, /* TAU */ 17, OWF_MOUSSAKA_REDEEM,
                         faest::prg::aes_ctr, faest::prg::aes_ctr, faest::leaf_hash::aes_ctr,
                         /* W_GRIND */ 8, {faest::bavc::one_tree, /* T_OPEN */ 105},
                         /* CRT_VOLE_MASKS */ true, /* HASH_INPUTS_V3 */ true>;

namespace check {
using EM128F = faest::v3::faest_em_128_f;
static_assert(std::is_same_v<RedeemParams::bavc_t, EM128F::bavc_t>);
static_assert(RedeemParams::tau_v == EM128F::tau_v);
static_assert(RedeemParams::delta_bits_v == EM128F::delta_bits_v);
static_assert(RedeemParams::vole_prg_v == EM128F::vole_prg_v);
static_assert(RedeemParams::leaf_hash_v == EM128F::leaf_hash_v);
static_assert(RedeemParams::use_crt_vole_masks == EM128F::use_crt_vole_masks);
static_assert(RedeemParams::use_v3_hash_inputs == EM128F::use_v3_hash_inputs);
static_assert(RedeemParams::use_grinding == EM128F::use_grinding);
} // namespace check

struct RedeemRelation {
    using params = RedeemParams;

    struct instance {
        AnchorSpan anchors;
        Nullifier nf;
        Context ctx_iss;
        Context ctx_red;
        ChallengeDigest challenge_digest;
    };

    static constexpr size_t NUM_CONSTRAINTS = REDEEM_NUM_CONSTRAINTS;

    static constexpr size_t WITNESS_PREFIX_BYTES = REDEEM_WITNESS_BYTES;

    static constexpr std::span<const uint8_t> DST = MOUSSAKA_REDEEM_PROOF_DST;

    // The public map of the witness PRG, if the witness is derived.
    static constexpr std::span<const uint8_t> WITNESS_PRG_DST = MOUSSAKA_REDEEM_PRG_DST;

    static void hash_instance(faest::hash_state& hasher, const instance& x) {
        static_assert(MAX_ANCHORS <= UINT32_MAX);
        const auto update_u32 = [&hasher](size_t v) {
            const auto u = static_cast<uint32_t>(v);
            const std::array<uint8_t, 4> bytes = {
                static_cast<uint8_t>(u), static_cast<uint8_t>(u >> 8),
                static_cast<uint8_t>(u >> 16), static_cast<uint8_t>(u >> 24)};
            hasher.update(bytes);
        };
        update_u32(MAX_ANCHORS);
        update_u32(x.anchors.size());
        for (const uov::PublicKey& pk : x.anchors) {
            hasher.update(uov::detail::PublicKeyAccess::digest(pk));
        }
        hasher.update(x.nf);
        hasher.update(x.ctx_iss);
        hasher.update(x.ctx_red);
        hasher.update(x.challenge_digest);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES> chal2) {
        static_assert(QS::max_degree == REDEEM_QS_DEGREE);
        using faest::poly1;
        using vole_mole::detail::qs_add_bit_constraint;
        using vole_mole::detail::qs_mul;
        using vole_mole::detail::qs_to_gfsecpar;
        using qs_bit = vole_mole::detail::qs_bit<QS, 1>;
        using qs_1 = keccak::detail::qs_val<QS, 1>;
        using qs_2 = keccak::detail::qs_val<QS, 2>;
        using qs_3 = keccak::detail::qs_val<QS, 3>;
        using qs_out = keccak::detail::qs_val<QS, keccak::detail::OUTPUT_DEGREE>;
        static_assert(3 <= keccak::detail::OUTPUT_DEGREE);
        const size_t n = x.anchors.size();

        // Add bit constraints: Every bit of r, s, and the intermediate states is a bit.
        for (size_t i = 0; i < 8 * REDEEM_WIT_OFF_B; ++i) {
            qs_add_bit_constraint(qs, qs->get_witness_bit(i));
        }

        // Add selector constraints: b[u] is a bit for u in [N] and 0 otherwise; ...
        std::array<qs_bit, MAX_ANCHORS> b;
        for (size_t u = 0; u < MAX_ANCHORS; ++u) {
            b[u] = qs->get_witness_bit(selector_bit(u));
            if (u < n) {
                qs_add_bit_constraint(qs, b[u]);
            } else {
                qs->add_constraint(qs_to_gfsecpar(b[u]));
            }
        }

        // ... sum(b[0..u+1]) * b[u+1] = 0 for each u in [MAX_ANCHORS - 1]; ...
        qs_bit prefix = b[0];
        for (size_t u = 0; u + 1 < MAX_ANCHORS; ++u) {
            qs->add_constraint(qs_to_gfsecpar(qs_mul<QS, 1, 1>(prefix, b[u + 1])));
            prefix += b[u + 1];
        }

        // ... and sum(b) = 1.
        qs->add_constraint(qs_to_gfsecpar(prefix + poly1(1)));

        // Add segment constraints: All but the last segment end in the expected intermediate state.
        const auto out = keccak::detail::qs_keccak(
            qs,
            keccak::detail::qs_input(qs, encode_com_state(x.nf, x.ctx_iss, x.ctx_red, {}),
                                     REDEEM_COM_TO_WIT),
            REDEEM_WIT_OFF_STATES);

        // Compute l(Q(s)) = sum_u b[u] * l(P[u](s)), where l is the random linear combination of
        // the M components.
        const uov::detail::Combination<QS> l(chal2, MOUSSAKA_REDEEM_COMBINE_DST);
        std::array<qs_1, uov::N> s;
        for (size_t i = 0; i < uov::N; ++i) {
            s[i] = qs->load_witness_8_bits_and_combine(8 * (REDEEM_WIT_OFF_S + i));
        }
        qs_3 lq(poly1(0), qs);
        for (size_t u = 0; u < n; ++u) {
            const qs_2 lp = uov::detail::qs_eval_combined_public_map<QS>(x.anchors[u].get(), s, l);
            lq += qs_mul<QS, 1, 2>(b[u], lp);
        }

        // Add output constraint: The last segment ends in Q(s), i.e., l(Q(s)) = l(out). Each byte
        // of the output is combined into an element of GF(256).
        qs_out lout(poly1(0), qs);
        for (size_t k = 0; k < uov::M; ++k) {
            lout += l.coeff(k) * keccak::detail::qs_byte(out, k);
        }
        qs->add_constraint(lout + keccak::detail::qs_lift<keccak::detail::OUTPUT_DEGREE>(lq));
    }
};

static_assert(WITNESS_BYTES<RedeemRelation> == REDEEM_WITNESS_BYTES);

static_assert(REDEEM_PROOF_BYTES == PROOF_BYTES<RedeemRelation>,
              "REDEEM_PROOF_BYTES is out of sync with faest-arch-opt");

using RedeemProof = std::span<uint8_t, REDEEM_PROOF_BYTES>;
using ConstRedeemProof = std::span<const uint8_t, REDEEM_PROOF_BYTES>;

// Compute the redemption proof for the given Anchor Set. The caller must ensure that the witness
// satisfies the instance.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if grinding fails (which
// happens with negligible probability).
inline void prove_redeem_request(RedeemProof pf_red, AnchorSpan anchors, size_t i,
                                 const Nullifier& nf, const Context& ctx_iss,
                                 const Context& ctx_red, const ChallengeDigest& challenge_digest,
                                 const Opening& r, const uov::Preimage& s,
                                 const ProveSeed<RedeemRelation>& rho) {
    const auto witness = encode_redeem_witness(nf, ctx_iss, ctx_red, r, s, i);
    voleith_prove<RedeemRelation>(pf_red, witness,
                                  {anchors, nf, ctx_iss, ctx_red, challenge_digest}, rho);
}

// Verify the redemption proof (steps 2-3 of FinalizeRedeem).
inline bool verify_redeem_proof(ConstRedeemProof pf_red, AnchorSpan anchors, const Nullifier& nf,
                                const Context& ctx_iss, const Context& ctx_red,
                                const ChallengeDigest& challenge_digest) {
    return voleith_verify<RedeemRelation>(pf_red,
                                          {anchors, nf, ctx_iss, ctx_red, challenge_digest});
}

} // namespace vole_mole::moussaka::detail

#endif
