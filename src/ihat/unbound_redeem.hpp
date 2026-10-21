// QuickSilver constraints for the redemption proof of an unbound token:
//
//   Instance: P[0], ..., P[N-1] (Anchor Set) where N <= MAX_ANCHORS, nf (nullifier), ctx_iss
//             (issuance context), ctx_red (redemption context)
//   Witness:  r (opening), nf_key (nullifier key), s (UOV preimage), b (selector)
//   Constraints:
//     - Q(s) = UnboundCom(nf_key, ctx_iss, r), where Q = sum_u b[u] * P[u]
//     - nf = Derive(nf_key, ctx_red)
//     - sum(b[0..u+1]) * b[u+1] = 0 for u in [N-1] (parity constraints)
//     - sum(b) = 1 (weight constraint)
//
// Arithmetization is the same as for a standard redemption proof, except that the nullifier is
// derived from the nullifier key. The witness layout is as follows:
//
//     0 ..  16   r
//    16 ..  32   nf_key
//    32 .. 151   s
//   151 .. 351   s5, s9 of UnboundCom
//   351 .. 551   s5, s9 of Derive
//   551 .. 559   b, with b[u] at bit u % 8 of byte 551 + u / 8

#ifndef VOLE_MOLE_IHAT_UNBOUND_REDEEM_HPP
#define VOLE_MOLE_IHAT_UNBOUND_REDEEM_HPP

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

constexpr size_t UNBOUND_REDEEM_QS_DEGREE =
    std::max(keccak::detail::QS_DEGREE, size_t{3}); // Q(s) has degree 3
static_assert(UNBOUND_REDEEM_QS_DEGREE - 1 + 4 <= 32, "faest-arch-opt supports at most 32 masks");

// Witness layout.
constexpr size_t UNBOUND_REDEEM_WIT_OFF_R = 0;
constexpr size_t UNBOUND_REDEEM_WIT_OFF_NF_KEY = UNBOUND_REDEEM_WIT_OFF_R + R_BYTES;
constexpr size_t UNBOUND_REDEEM_WIT_OFF_S = UNBOUND_REDEEM_WIT_OFF_NF_KEY + NF_KEY_BYTES;
constexpr size_t UNBOUND_REDEEM_WIT_OFF_COM_STATES = UNBOUND_REDEEM_WIT_OFF_S + uov::N;
constexpr size_t UNBOUND_REDEEM_WIT_OFF_DERIVE_STATES =
    UNBOUND_REDEEM_WIT_OFF_COM_STATES + keccak::detail::COMMITTED_STATES_BYTES;
constexpr size_t UNBOUND_REDEEM_WIT_OFF_B =
    UNBOUND_REDEEM_WIT_OFF_DERIVE_STATES + keccak::detail::COMMITTED_STATES_BYTES;
constexpr size_t UNBOUND_REDEEM_WITNESS_BYTES = UNBOUND_REDEEM_WIT_OFF_B + SELECTOR_BYTES;
constexpr size_t UNBOUND_REDEEM_WITNESS_BITS = 8 * UNBOUND_REDEEM_WITNESS_BYTES;

// The witness index of the bit b[u] of the selector.
constexpr size_t unbound_selector_bit(size_t u) { return 8 * UNBOUND_REDEEM_WIT_OFF_B + u; }

// Map of the index of each byte of the input of UnboundCom to its index in the witness.
constexpr keccak::detail::InputMap UNBOUND_REDEEM_COM_TO_WIT = [] {
    keccak::detail::InputMap map;
    map.fill(-1);
    for (size_t i = 0; i < R_BYTES; ++i) {
        map[UNBOUND_COM_OFF_R + i] = static_cast<int>(UNBOUND_REDEEM_WIT_OFF_R + i);
    }
    for (size_t i = 0; i < NF_KEY_BYTES; ++i) {
        map[UNBOUND_COM_OFF_NF_KEY + i] = static_cast<int>(UNBOUND_REDEEM_WIT_OFF_NF_KEY + i);
    }
    return map;
}();
static_assert(keccak::detail::input_map_is_valid(UNBOUND_REDEEM_COM_TO_WIT,
                                                 UNBOUND_REDEEM_WIT_OFF_R,
                                                 UNBOUND_REDEEM_WIT_OFF_S),
              "UNBOUND_REDEEM_COM_TO_WIT is malformed");

// Map of the index of each byte of the input of Derive to its index in the witness.
constexpr keccak::detail::InputMap UNBOUND_REDEEM_DERIVE_TO_WIT = [] {
    keccak::detail::InputMap map;
    map.fill(-1);
    for (size_t i = 0; i < NF_KEY_BYTES; ++i) {
        map[DERIVE_OFF_NF_KEY + i] = static_cast<int>(UNBOUND_REDEEM_WIT_OFF_NF_KEY + i);
    }
    return map;
}();
static_assert(keccak::detail::input_map_is_valid(UNBOUND_REDEEM_DERIVE_TO_WIT,
                                                 UNBOUND_REDEEM_WIT_OFF_NF_KEY,
                                                 UNBOUND_REDEEM_WIT_OFF_S),
              "UNBOUND_REDEEM_DERIVE_TO_WIT is malformed");

constexpr size_t UNBOUND_REDEEM_NUM_CONSTRAINTS =
    8 * UNBOUND_REDEEM_WIT_OFF_B // bit constraints for r, nf_key, s, and the intermediate states
    + SELECTOR_NUM_CONSTRAINTS   // selector constraints
    + 2 * keccak::detail::NUM_SEGMENT_CONSTRAINTS // segments end in a committed state
    + 8 * NF_BYTES                                // Derive ends in nf
    + 1; // Q(s) = commitment (a random linear combination of the M components)

// Compute the full witness, including the intermediate Keccak states and the selector for the
// Anchor at index i.
inline std::array<uint8_t, UNBOUND_REDEEM_WITNESS_BYTES>
encode_unbound_redeem_witness(const NfKey& nf_key, const Context& ctx_iss, const Context& ctx_red,
                              const Opening& r, const uov::Preimage& s, size_t i) {
    using keccak::detail::COMMITTED_STATES_BYTES;
    using keccak::detail::encode_committed_states;
    std::array<uint8_t, UNBOUND_REDEEM_WITNESS_BYTES> w{};
    std::ranges::copy(r, w.begin() + UNBOUND_REDEEM_WIT_OFF_R);
    std::ranges::copy(nf_key, w.begin() + UNBOUND_REDEEM_WIT_OFF_NF_KEY);
    std::ranges::copy(s, w.begin() + UNBOUND_REDEEM_WIT_OFF_S);
    encode_committed_states(
        std::span(w).subspan<UNBOUND_REDEEM_WIT_OFF_COM_STATES, COMMITTED_STATES_BYTES>(),
        encode_unbound_com_state(nf_key, ctx_iss, r));
    encode_committed_states(
        std::span(w).subspan<UNBOUND_REDEEM_WIT_OFF_DERIVE_STATES, COMMITTED_STATES_BYTES>(),
        encode_derive_state(nf_key, ctx_red));
    encode_selector(std::span(w).subspan<UNBOUND_REDEEM_WIT_OFF_B, SELECTOR_BYTES>(), i);
    return w;
}

// The VOLEitH parameter set for UnboundRedeemRelation.
constexpr faest::owf OWF_UNBOUND_IHAT_REDEEM =
    static_cast<faest::owf>((0x72u << 8) | 0b10'0000 /* owf_flag_witness_bits_check */);
static_assert(faest::is_owf_with_witness_bits_check(OWF_UNBOUND_IHAT_REDEEM));
static_assert(!faest::is_owf_with_aes_ecb(OWF_UNBOUND_IHAT_REDEEM));
static_assert(!faest::is_owf_with_aes_em(OWF_UNBOUND_IHAT_REDEEM));

} // namespace vole_mole::ihat::detail

template <>
struct faest::OWF_CONSTANTS<faest::secpar::s128, vole_mole::ihat::detail::OWF_UNBOUND_IHAT_REDEEM> {
    constexpr static size_t WITNESS_BITS = vole_mole::ihat::detail::UNBOUND_REDEEM_WITNESS_BITS;
    constexpr static size_t QS_DEGREE = vole_mole::ihat::detail::UNBOUND_REDEEM_QS_DEGREE;
    // The witness starts with the opening of the commitment, which the Client never reveals.
    constexpr static bool REUSE_CRT_WITNESS = true;
    constexpr static bool valid = true;
};

namespace vole_mole::ihat::detail {

using UnboundRedeemParams = VoleithParams<OWF_UNBOUND_IHAT_REDEEM>;
static_assert(is_em128f_variant<UnboundRedeemParams>());
static_assert(UNBOUND_REDEEM_WIT_OFF_R == 0 && R_BYTES >= UnboundRedeemParams::secpar_bytes);

struct UnboundRedeemRelation {
    using params = UnboundRedeemParams;

    using instance = RedeemInstance;

    static constexpr size_t NUM_CONSTRAINTS = UNBOUND_REDEEM_NUM_CONSTRAINTS;

    static constexpr size_t WITNESS_PREFIX_BYTES = UNBOUND_REDEEM_WITNESS_BYTES;

    static constexpr std::span<const uint8_t> DST = UNBOUND_IHAT_REDEEM_PROOF_DST;

    static void hash_instance(faest::hash_state& hasher, const instance& x) {
        hash_redeem_instance(hasher, x);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES> chal2) {
        static_assert(QS::max_degree == UNBOUND_REDEEM_QS_DEGREE);

        // Add bit constraints: Every bit of r, nf_key, s, and the intermediate states is a bit.
        qs_add_bit_constraints(qs, 8 * UNBOUND_REDEEM_WIT_OFF_B);

        // Add selector constraints.
        const auto b = qs_add_selector_constraints(qs, x.anchors.size(), UNBOUND_REDEEM_WIT_OFF_B);

        // Add segment constraints for UnboundCom and Derive: All but the last segment of each end
        // in the expected intermediate state.
        const auto com_out = keccak::detail::qs_keccak(
            qs,
            keccak::detail::qs_input(qs, encode_unbound_com_state({}, x.ctx_iss, {}),
                                     UNBOUND_REDEEM_COM_TO_WIT),
            UNBOUND_REDEEM_WIT_OFF_COM_STATES);
        const auto derive_out = keccak::detail::qs_keccak(
            qs,
            keccak::detail::qs_input(qs, encode_derive_state({}, x.ctx_red),
                                     UNBOUND_REDEEM_DERIVE_TO_WIT),
            UNBOUND_REDEEM_WIT_OFF_DERIVE_STATES, 8 * NF_BYTES);

        // Add output constraints: Derive ends in nf. (Only the bits of nf are computed in the last
        // round.)
        qs_add_output_constraints(qs, derive_out, x.nf);

        // Add output constraint: UnboundCom ends in Q(s).
        qs_add_signature_constraint(qs, x.anchors, b, UNBOUND_REDEEM_WIT_OFF_S, com_out, chal2,
                                    UNBOUND_IHAT_REDEEM_COMBINE_DST);
    }
};

static_assert(WITNESS_BYTES<UnboundRedeemRelation> == UNBOUND_REDEEM_WITNESS_BYTES);

static_assert(UNBOUND_REDEEM_PROOF_BYTES == PROOF_BYTES<UnboundRedeemRelation>,
              "UNBOUND_REDEEM_PROOF_BYTES is out of sync with faest-arch-opt");

using UnboundRedeemProof = std::span<uint8_t, UNBOUND_REDEEM_PROOF_BYTES>;
using ConstUnboundRedeemProof = std::span<const uint8_t, UNBOUND_REDEEM_PROOF_BYTES>;

// Compute the redemption proof for the given Anchor Set. The caller must ensure that the witness
// satisfies the instance.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if grinding fails (which
// happens with negligible probability).
inline void prove_unbound_redeem_request(UnboundRedeemProof pf_red, AnchorSpan anchors, size_t i,
                                         const Nullifier& nf, const Context& ctx_iss,
                                         const Context& ctx_red,
                                         const ChallengeDigest& challenge_digest,
                                         const NfKey& nf_key, const Opening& r,
                                         const uov::Preimage& s,
                                         const ProveSeed<UnboundRedeemRelation>& rho) {
    const auto witness = encode_unbound_redeem_witness(nf_key, ctx_iss, ctx_red, r, s, i);
    voleith_prove<UnboundRedeemRelation>(pf_red, witness,
                                         {anchors, nf, ctx_iss, ctx_red, challenge_digest}, rho);
}

// Verify the redemption proof.
inline bool verify_unbound_redeem_proof(ConstUnboundRedeemProof pf_red, AnchorSpan anchors,
                                        const Nullifier& nf, const Context& ctx_iss,
                                        const Context& ctx_red,
                                        const ChallengeDigest& challenge_digest) {
    return voleith_verify<UnboundRedeemRelation>(pf_red,
                                                 {anchors, nf, ctx_iss, ctx_red, challenge_digest});
}

} // namespace vole_mole::ihat::detail

#endif
