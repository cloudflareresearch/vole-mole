// QuickSilver constraints for the issuance proof:
//
//   Instance: c (commitment), T_init (initial credit), ctx_iss (issuance context)
//   Witness:  nf (nullifier), r (opening)
//   Constraint: c = Com(nf, ctx_iss, T_init, r)
//
// Arithmetization: The commitment is evaluated as described in keccak/segmented.hpp, which adds
// 800 constraints of degree at most 9 for each of the two committed intermediate states. The
// output of the last segment is c, of which we only know 256 of 800 bits, so we only compute these
// bits in the last round and add one constraint (of degree 8) per bit of c. The witness layout is
// as follows:
//
//     0 ..  16   r
//    16 ..  40   nf
//    40 .. 140   s5, the state after 5 rounds
//   140 .. 240   s9, the state after 9 rounds
//
// Soundness of the proof requires proving each witness bit is in fact a bit; this adds an
// additional 1920 constraints of degree 2.
//
// We use the VOLE-in-the-Head parameters of FAEST-EM-128f v3.

#ifndef VOLE_MOLE_RATATOUILLE_ISSUE_HPP
#define VOLE_MOLE_RATATOUILLE_ISSUE_HPP

#include "vole_mole/ratatouille.hpp"

#include "dst.hpp"
#include "keccak/segmented.hpp"
#include "qs_bit.hpp"
#include "ratatouille/commit.hpp"
#include "voleith.hpp"

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

namespace vole_mole::ratatouille::detail {

constexpr size_t ISSUE_QS_DEGREE =
    std::max(keccak::detail::QS_DEGREE, size_t{2}); // bit constraints: 2
// The CRT VOLE commitment needs ISSUE_QS_DEGREE - 1 masks for QuickSilver and 4 for the VOLE check.
// faest-arch-opt supports at most 32 masks.
static_assert(ISSUE_QS_DEGREE - 1 + 4 <= 32, "faest-arch-opt supports at most 32 masks");

// Witness layout.
constexpr size_t ISSUE_WIT_OFF_R = 0;
constexpr size_t ISSUE_WIT_OFF_NF = ISSUE_WIT_OFF_R + R_BYTES;
constexpr size_t ISSUE_WIT_OFF_STATES = ISSUE_WIT_OFF_NF + NF_BYTES;
constexpr size_t ISSUE_WITNESS_BYTES =
    ISSUE_WIT_OFF_STATES + keccak::detail::COMMITTED_STATES_BYTES;
constexpr size_t ISSUE_WITNESS_BITS = 8 * ISSUE_WITNESS_BYTES;

// Map of the index of each byte of the input of Com to its index in the witness.
// The opening and nullifier are secret.
constexpr keccak::detail::InputMap ISSUE_COM_TO_WIT = [] {
    keccak::detail::InputMap map;
    map.fill(-1);
    for (size_t i = 0; i < R_BYTES; ++i) {
        map[COM_OFF_R + i] = static_cast<int>(ISSUE_WIT_OFF_R + i);
    }
    for (size_t i = 0; i < NF_BYTES; ++i) {
        map[COM_OFF_NF + i] = static_cast<int>(ISSUE_WIT_OFF_NF + i);
    }
    return map;
}();
static_assert(keccak::detail::input_map_is_valid(ISSUE_COM_TO_WIT, 0, ISSUE_WIT_OFF_STATES),
              "ISSUE_COM_TO_WIT is malformed");

constexpr size_t ISSUE_NUM_CONSTRAINTS =
    ISSUE_WITNESS_BITS                        // bit constraints
    + keccak::detail::NUM_SEGMENT_CONSTRAINTS // segment ends in a committed state
    + 8 * COMMITMENT_BYTES;                   // last segment ends in the commitment

// Compute the full witness, including the intermediate Keccak states.
inline std::array<uint8_t, ISSUE_WITNESS_BYTES> encode_issue_witness(const Nullifier& nf,
                                                                     const Context& ctx_iss,
                                                                     Credits t_init,
                                                                     const Opening& r) {
    std::array<uint8_t, ISSUE_WITNESS_BYTES> w{};
    std::ranges::copy(r, w.begin() + ISSUE_WIT_OFF_R);
    std::ranges::copy(nf, w.begin() + ISSUE_WIT_OFF_NF);
    keccak::detail::encode_committed_states(
        std::span(w).subspan<ISSUE_WIT_OFF_STATES, keccak::detail::COMMITTED_STATES_BYTES>(),
        encode_com_state(nf, ctx_iss, t_init, r));
    return w;
}

// The VOLEitH parameter set for IssueRelation.
constexpr faest::owf OWF_RATATOUILLE_ISSUE =
    static_cast<faest::owf>((0x49u << 8) | 0b10'0000 /* owf_flag_witness_bits_check */);
static_assert(faest::is_owf_with_witness_bits_check(OWF_RATATOUILLE_ISSUE));
static_assert(!faest::is_owf_with_aes_ecb(OWF_RATATOUILLE_ISSUE));
static_assert(!faest::is_owf_with_aes_em(OWF_RATATOUILLE_ISSUE));

} // namespace vole_mole::ratatouille::detail

// Must be declared outside of our namespace, since it specializes a template of faest-arch-opt.
template <>
struct faest::OWF_CONSTANTS<faest::secpar::s128,
                            vole_mole::ratatouille::detail::OWF_RATATOUILLE_ISSUE> {
    constexpr static size_t WITNESS_BITS = vole_mole::ratatouille::detail::ISSUE_WITNESS_BITS;
    constexpr static size_t QS_DEGREE = vole_mole::ratatouille::detail::ISSUE_QS_DEGREE;
    constexpr static bool valid = true;
};

namespace vole_mole::ratatouille::detail {

// Same as faest::v3::faest_em_128_f, except for the OWF.
using IssueParams =
    faest::parameter_set<faest::secpar::s128, /* TAU */ 17, OWF_RATATOUILLE_ISSUE,
                         faest::prg::aes_ctr, faest::prg::aes_ctr, faest::leaf_hash::aes_ctr,
                         /* W_GRIND */ 8, {faest::bavc::one_tree, /* T_OPEN */ 105},
                         /* CRT_VOLE_MASKS */ true, /* HASH_INPUTS_V3 */ true>;

namespace check {
using EM128F = faest::v3::faest_em_128_f;
static_assert(std::is_same_v<IssueParams::bavc_t, EM128F::bavc_t>);
static_assert(IssueParams::tau_v == EM128F::tau_v);
static_assert(IssueParams::delta_bits_v == EM128F::delta_bits_v);
static_assert(IssueParams::vole_prg_v == EM128F::vole_prg_v);
static_assert(IssueParams::leaf_hash_v == EM128F::leaf_hash_v);
static_assert(IssueParams::use_crt_vole_masks == EM128F::use_crt_vole_masks);
static_assert(IssueParams::use_v3_hash_inputs == EM128F::use_v3_hash_inputs);
static_assert(IssueParams::use_grinding == EM128F::use_grinding);
} // namespace check

struct IssueRelation {
    using params = IssueParams;

    struct instance {
        Commitment c;
        Credits t_init;
        Context ctx_iss;
    };

    static constexpr size_t NUM_CONSTRAINTS = ISSUE_NUM_CONSTRAINTS;

    static constexpr size_t WITNESS_PREFIX_BYTES = ISSUE_WITNESS_BYTES;

    static constexpr std::span<const uint8_t> DST = RATATOUILLE_ISSUE_PROOF_DST;

    static void hash_instance(faest::hash_state& hasher, const instance& x) {
        hasher.update(x.c);
        hasher.update(encode_credits(x.t_init));
        hasher.update(x.ctx_iss);
    }

    template <typename QS>
    static void
    constraints(QS* qs, const instance& x,
                std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES> /* chal2 */) {
        static_assert(QS::max_degree == ISSUE_QS_DEGREE);
        using faest::poly1;

        // Add bit constraints: Every witness bit is a bit.
        for (size_t i = 0; i < ISSUE_WITNESS_BITS; ++i) {
            qs_add_bit_constraint(qs, qs->get_witness_bit(i));
        }

        // Add segment constraints: All but the last segment end in the expected intermediate state.
        const auto out = keccak::detail::qs_keccak(
            qs,
            keccak::detail::qs_input(qs, encode_com_state({}, x.ctx_iss, x.t_init, {}),
                                     ISSUE_COM_TO_WIT),
            ISSUE_WIT_OFF_STATES, 8 * COMMITMENT_BYTES);

        // Add output constraint: The last segment ends in the commitment. (Only the bits of c are
        // computed in the last round.)
        for (size_t i = 0; i < 8 * COMMITMENT_BYTES; ++i) {
            qs->add_constraint(qs_to_gfsecpar(out[i] + poly1((x.c[i / 8] >> (i % 8)) & 1)));
        }
    }
};

static_assert(WITNESS_BYTES<IssueRelation> == ISSUE_WITNESS_BYTES);

// The public header hard-codes the proof size, so check it against faest-arch-opt's.
static_assert(ISSUE_PROOF_BYTES == PROOF_BYTES<IssueRelation>,
              "ISSUE_PROOF_BYTES is out of sync with faest-arch-opt");

using IssueProof = std::span<uint8_t, ISSUE_PROOF_BYTES>;
using ConstIssueProof = std::span<const uint8_t, ISSUE_PROOF_BYTES>;

// Compute the issuance proof pf_iss that c = Com(nf, ctx_iss, t_init, r), where c, t_init, and
// ctx_iss are public. rho is randomness for the VOLEitH prover.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if grinding fails (which
// happens with negligible probability).
inline void prove_issue_request(IssueProof pf_iss, const Commitment& c, const Nullifier& nf,
                                Credits t_init, const Context& ctx_iss, const Opening& r,
                                const ProveSeed<IssueRelation>& rho) {
    const auto witness = encode_issue_witness(nf, ctx_iss, t_init, r);
    voleith_prove<IssueRelation>(pf_iss, witness, {c, t_init, ctx_iss}, rho);
}

// Verify the issuance proof pf_iss that c commits to t_init and ctx_iss.
inline bool verify_issue_proof(ConstIssueProof pf_iss, const Commitment& c, Credits t_init,
                               const Context& ctx_iss) {
    return voleith_verify<IssueRelation>(pf_iss, {c, t_init, ctx_iss});
}

} // namespace vole_mole::ratatouille::detail

#endif
