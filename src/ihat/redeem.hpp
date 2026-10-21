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
// We use the VOLE-in-the-Head parameters of FAEST-EM-128f v3.

#ifndef VOLE_MOLE_IHAT_REDEEM_HPP
#define VOLE_MOLE_IHAT_REDEEM_HPP

#include "vole_mole/ihat.hpp"
#include "vole_mole/uov.hpp"

#include "dst.hpp"
#include "ihat/circuit.hpp"
#include "ihat/commit.hpp"
#include "keccak/segmented.hpp"
#include "voleith.hpp"

#include "hash.hpp"       // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

namespace vole_mole::ihat::detail {

constexpr size_t REDEEM_QS_DEGREE =
    std::max(keccak::detail::QS_DEGREE, size_t{3}); // Q(s) has degree 3
static_assert(REDEEM_QS_DEGREE - 1 + 4 <= 32, "faest-arch-opt supports at most 32 masks");

// Witness layout.
constexpr size_t REDEEM_WIT_OFF_R = 0;
constexpr size_t REDEEM_WIT_OFF_S = REDEEM_WIT_OFF_R + R_BYTES;
constexpr size_t REDEEM_WIT_OFF_STATES = REDEEM_WIT_OFF_S + uov::N;
constexpr size_t REDEEM_WIT_OFF_B = REDEEM_WIT_OFF_STATES + keccak::detail::COMMITTED_STATES_BYTES;
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
    8 * REDEEM_WIT_OFF_B       // bit constraints for r, s, and the intermediate states
    + SELECTOR_NUM_CONSTRAINTS // selector constraints
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
    encode_selector(std::span(w).subspan<REDEEM_WIT_OFF_B, SELECTOR_BYTES>(), i);
    return w;
}

// The VOLEitH parameter set for RedeemRelation.
constexpr faest::owf OWF_IHAT_REDEEM =
    static_cast<faest::owf>((0x52u << 8) | 0b10'0000 /* owf_flag_witness_bits_check */);
static_assert(faest::is_owf_with_witness_bits_check(OWF_IHAT_REDEEM));
static_assert(!faest::is_owf_with_aes_ecb(OWF_IHAT_REDEEM));
static_assert(!faest::is_owf_with_aes_em(OWF_IHAT_REDEEM));

} // namespace vole_mole::ihat::detail

// Must be declared outside of our namespace, since it specializes a template of faest-arch-opt.
template <>
struct faest::OWF_CONSTANTS<faest::secpar::s128, vole_mole::ihat::detail::OWF_IHAT_REDEEM> {
    constexpr static size_t WITNESS_BITS = vole_mole::ihat::detail::REDEEM_WITNESS_BITS;
    constexpr static size_t QS_DEGREE = vole_mole::ihat::detail::REDEEM_QS_DEGREE;
    // The witness starts with the opening of the commitment, which the Client never reveals.
    constexpr static bool REUSE_CRT_WITNESS = true;
    constexpr static bool valid = true;
};

namespace vole_mole::ihat::detail {

using RedeemParams = VoleithParams<OWF_IHAT_REDEEM>;
static_assert(is_em128f_variant<RedeemParams>());
static_assert(REDEEM_WIT_OFF_R == 0 && R_BYTES >= RedeemParams::secpar_bytes);

struct RedeemRelation {
    using params = RedeemParams;

    using instance = RedeemInstance;

    static constexpr size_t NUM_CONSTRAINTS = REDEEM_NUM_CONSTRAINTS;

    static constexpr size_t WITNESS_PREFIX_BYTES = REDEEM_WITNESS_BYTES;

    static constexpr std::span<const uint8_t> DST = IHAT_REDEEM_PROOF_DST;

    static void hash_instance(faest::hash_state& hasher, const instance& x) {
        hash_redeem_instance(hasher, x);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES> chal2) {
        static_assert(QS::max_degree == REDEEM_QS_DEGREE);

        // Add bit constraints: Every bit of r, s, and the intermediate states is a bit.
        qs_add_bit_constraints(qs, 8 * REDEEM_WIT_OFF_B);

        // Add selector constraints.
        const auto b = qs_add_selector_constraints(qs, x.anchors.size(), REDEEM_WIT_OFF_B);

        // Add segment constraints: All but the last segment end in the expected intermediate state.
        const auto out = keccak::detail::qs_keccak(
            qs,
            keccak::detail::qs_input(qs, encode_com_state(x.nf, x.ctx_iss, x.ctx_red, {}),
                                     REDEEM_COM_TO_WIT),
            REDEEM_WIT_OFF_STATES);

        // Add output constraint: The last segment ends in Q(s).
        qs_add_signature_constraint(qs, x.anchors, b, REDEEM_WIT_OFF_S, out, chal2,
                                    IHAT_REDEEM_COMBINE_DST);
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

} // namespace vole_mole::ihat::detail

#endif
