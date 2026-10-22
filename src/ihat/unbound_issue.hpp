// QuickSilver constraints for the issuance proof of an unbound token:
//
//   Instance: t (commitment), ctx_iss (issuance context)
//   Witness:  nf_key (nullifier key), r (opening)
//   Constraint: t = UnboundCom(nf_key, ctx_iss, r)
//
// Arithmetization is the same as for standard issuance proofs, except that the redemption context
// and nullifier are replaced by the nullifier key. The witness layout is as follows:
//
//     0 ..  16   r
//    16 ..  32   nf_key
//    32 .. 132   s5, the state after 5 rounds
//   132 .. 232   s9, the state after 9 rounds

#ifndef VOLE_MOLE_IHAT_UNBOUND_ISSUE_HPP
#define VOLE_MOLE_IHAT_UNBOUND_ISSUE_HPP

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

constexpr size_t UNBOUND_ISSUE_QS_DEGREE =
    std::max(keccak::detail::QS_DEGREE, size_t{2}); // bit constraints: 2
static_assert(UNBOUND_ISSUE_QS_DEGREE - 1 + 4 <= 32, "faest-arch-opt supports at most 32 masks");

// Witness layout.
constexpr size_t UNBOUND_ISSUE_WIT_OFF_R = 0;
constexpr size_t UNBOUND_ISSUE_WIT_OFF_NF_KEY = UNBOUND_ISSUE_WIT_OFF_R + R_BYTES;
constexpr size_t UNBOUND_ISSUE_WIT_OFF_STATES = UNBOUND_ISSUE_WIT_OFF_NF_KEY + NF_KEY_BYTES;
constexpr size_t UNBOUND_ISSUE_WITNESS_BYTES =
    UNBOUND_ISSUE_WIT_OFF_STATES + keccak::detail::COMMITTED_STATES_BYTES;
constexpr size_t UNBOUND_ISSUE_WITNESS_BITS = 8 * UNBOUND_ISSUE_WITNESS_BYTES;

// Map of the index of each byte of the input of UnboundCom to its index in the witness. The opening
// and nullifier key are secret.
constexpr keccak::detail::InputMap UNBOUND_COM_TO_WIT = [] {
    keccak::detail::InputMap map;
    map.fill(-1);
    for (size_t i = 0; i < R_BYTES; ++i) {
        map[UNBOUND_COM_OFF_R + i] = static_cast<int>(UNBOUND_ISSUE_WIT_OFF_R + i);
    }
    for (size_t i = 0; i < NF_KEY_BYTES; ++i) {
        map[UNBOUND_COM_OFF_NF_KEY + i] = static_cast<int>(UNBOUND_ISSUE_WIT_OFF_NF_KEY + i);
    }
    return map;
}();
static_assert(keccak::detail::input_map_is_valid(UNBOUND_COM_TO_WIT, 0,
                                                 UNBOUND_ISSUE_WIT_OFF_STATES),
              "UNBOUND_COM_TO_WIT is malformed");

constexpr size_t UNBOUND_ISSUE_NUM_CONSTRAINTS =
    UNBOUND_ISSUE_WITNESS_BITS                // bit constraints
    + keccak::detail::NUM_SEGMENT_CONSTRAINTS // segment ends in a committed state
    + 8 * uov::M;                             // last segment ends in the commitment

// Compute the full witness, including the intermediate Keccak states.
inline std::array<uint8_t, UNBOUND_ISSUE_WITNESS_BYTES>
encode_unbound_issue_witness(const NfKey& nf_key, const Context& ctx_iss, const Opening& r) {
    std::array<uint8_t, UNBOUND_ISSUE_WITNESS_BYTES> w{};
    std::ranges::copy(r, w.begin() + UNBOUND_ISSUE_WIT_OFF_R);
    std::ranges::copy(nf_key, w.begin() + UNBOUND_ISSUE_WIT_OFF_NF_KEY);
    keccak::detail::encode_committed_states(
        std::span(w)
            .subspan<UNBOUND_ISSUE_WIT_OFF_STATES, keccak::detail::COMMITTED_STATES_BYTES>(),
        encode_unbound_com_state(nf_key, ctx_iss, r));
    return w;
}

constexpr faest::owf OWF_UNBOUND_IHAT_ISSUE =
    static_cast<faest::owf>((0x6du << 8) | 0b10'0000 /* owf_flag_witness_bits_check */);
static_assert(faest::is_owf_with_witness_bits_check(OWF_UNBOUND_IHAT_ISSUE));
static_assert(!faest::is_owf_with_aes_ecb(OWF_UNBOUND_IHAT_ISSUE));
static_assert(!faest::is_owf_with_aes_em(OWF_UNBOUND_IHAT_ISSUE));

} // namespace vole_mole::ihat::detail

// Must be declared outside of our namespace, since it specializes a template of faest-arch-opt.
template <>
struct faest::OWF_CONSTANTS<faest::secpar::s128, vole_mole::ihat::detail::OWF_UNBOUND_IHAT_ISSUE> {
    constexpr static size_t WITNESS_BITS = vole_mole::ihat::detail::UNBOUND_ISSUE_WITNESS_BITS;
    constexpr static size_t QS_DEGREE = vole_mole::ihat::detail::UNBOUND_ISSUE_QS_DEGREE;
    // The witness starts with the opening of the commitment, which the Client never reveals.
    constexpr static bool REUSE_CRT_WITNESS = true;
    constexpr static bool valid = true;
};

namespace vole_mole::ihat::detail {

using UnboundIssueParams = VoleithParams<OWF_UNBOUND_IHAT_ISSUE>;
static_assert(is_em128f_variant<UnboundIssueParams>());
static_assert(UNBOUND_ISSUE_WIT_OFF_R == 0 && R_BYTES >= UnboundIssueParams::secpar_bytes);

struct UnboundIssueRelation {
    using params = UnboundIssueParams;

    struct instance {
        Commitment t;
        Context ctx_iss;
    };

    static constexpr size_t NUM_CONSTRAINTS = UNBOUND_ISSUE_NUM_CONSTRAINTS;

    static constexpr size_t WITNESS_PREFIX_BYTES = UNBOUND_ISSUE_WITNESS_BYTES;

    static constexpr std::span<const uint8_t> DST = UNBOUND_IHAT_ISSUE_PROOF_DST;

    static void hash_instance(faest::hash_state& hasher, const instance& x) {
        hasher.update(x.t);
        hasher.update(x.ctx_iss);
    }

    template <typename QS>
    static void
    constraints(QS* qs, const instance& x,
                std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES> /* chal2 */) {
        static_assert(QS::max_degree == UNBOUND_ISSUE_QS_DEGREE);

        // Add bit constraints: Every witness bit is a bit.
        qs_add_bit_constraints(qs, UNBOUND_ISSUE_WITNESS_BITS);

        // Add segment constraints: All but the last segment end in the expected intermediate state.
        const auto out = keccak::detail::qs_keccak(
            qs,
            keccak::detail::qs_input(qs, encode_unbound_com_state({}, x.ctx_iss, {}),
                                     UNBOUND_COM_TO_WIT),
            UNBOUND_ISSUE_WIT_OFF_STATES, 8 * uov::M);

        // Add output constraint: The last segment ends in the commitment. (Only the bits of t are
        // computed in the last round.)
        qs_add_output_constraints(qs, out, x.t);
    }
};

// The public header hard-codes the proof size, so check it against faest-arch-opt's.
static_assert(UNBOUND_ISSUE_PROOF_BYTES == PROOF_BYTES<UnboundIssueRelation>,
              "UNBOUND_ISSUE_PROOF_BYTES is out of sync with faest-arch-opt");

using UnboundIssueProof = std::span<uint8_t, UNBOUND_ISSUE_PROOF_BYTES>;
using ConstUnboundIssueProof = std::span<const uint8_t, UNBOUND_ISSUE_PROOF_BYTES>;

// Compute the issuance proof pf_iss that t = UnboundCom(nf_key, ctx_iss, r), where t and ctx_iss
// are public. rho is randomness for the VOLEitH prover.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if grinding fails (which
// happens with negligible probability).
inline void prove_unbound_issue_request(UnboundIssueProof pf_iss, const Commitment& t,
                                        const NfKey& nf_key, const Context& ctx_iss,
                                        const Opening& r,
                                        const ProveSeed<UnboundIssueRelation>& rho) {
    const auto witness = encode_unbound_issue_witness(nf_key, ctx_iss, r);
    voleith_prove<UnboundIssueRelation>(pf_iss, witness, {t, ctx_iss}, rho);
}

// Verify the issuance proof pf_iss that t commits to ctx_iss.
inline bool verify_unbound_issue_proof(ConstUnboundIssueProof pf_iss, const Commitment& t,
                                       const Context& ctx_iss) {
    return voleith_verify<UnboundIssueRelation>(pf_iss, {t, ctx_iss});
}

} // namespace vole_mole::ihat::detail

#endif
