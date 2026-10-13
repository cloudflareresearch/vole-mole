// QuickSilver constraints for the PomFRIT redemption proof (<https://ia.cr/2026/109>, Algorithm 2):
//
//   Instance: h (UOV target), P (UOV public key)
//   Witness:  r (target mask), s (UOV preimage)
//   Constraint: P(s) = h + r
//
// Arithmetization: We evaluate P directly on the committed GF(256) elements of s. Rather than
// checking each of the M components, we check a random linear combination l of them, with
// coefficients in GF(2^128) derived from the QuickSilver challenge (<https://ia.cr/2026/109>,
// Section 8; see uov::detail::Combination). Since P is a quadratic map, this constraint has degree
// 2. We also need to confirm that each bit of witness is a bit, which adds 8 * (M + N) = 1312
// constraints of degree 2.
//
// We use the VOLE-in-the-Head parameters of FAEST-EM-128f v3.

#ifndef VOLE_MOLE_POMFRIT_REDEEM_HPP
#define VOLE_MOLE_POMFRIT_REDEEM_HPP

#include "vole_mole/uov.hpp"

#include "dst.hpp"
#include "qs_bit.hpp"
#include "uov/circuit.hpp"
#include "uov/public_key.hpp"
#include "voleith.hpp"
#include "witness_prg.hpp"

#include "constants.hpp"   // from faest-arch-opt
#include "faest_sig.hpp"   // from faest-arch-opt
#include "hash.hpp"        // from faest-arch-opt
#include "parameters.hpp"  // from faest-arch-opt
#include "polynomials.hpp" // from faest-arch-opt

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <type_traits>

namespace vole_mole::pomfrit::detail {

// Witness layout.
constexpr size_t WIT_OFF_R = 0;
constexpr size_t WIT_OFF_S = WIT_OFF_R + uov::M;
constexpr size_t REDEEM_WITNESS_BYTES = WIT_OFF_S + uov::N;
constexpr size_t REDEEM_WITNESS_BITS = 8 * REDEEM_WITNESS_BYTES;

constexpr size_t REDEEM_QS_DEGREE = 2;

constexpr size_t REDEEM_NUM_CONSTRAINTS = REDEEM_WITNESS_BITS // bit constraints
                                          + 1; // P(s) = h + r (random linear combination)

// The VOLEitH parameter set for RedeemRelation.
constexpr faest::owf OWF_REDEEM =
    static_cast<faest::owf>((0x50u << 8) | 0b10'0000 /* owf_flag_witness_bits_check */);
static_assert(faest::is_owf_with_witness_bits_check(OWF_REDEEM));
static_assert(!faest::is_owf_with_aes_ecb(OWF_REDEEM));
static_assert(!faest::is_owf_with_aes_em(OWF_REDEEM));

// Commit to the witness directly rather than deriving it from a short key with a PRG (see
// "Derived witnesses" in voleith.hpp and witness_prg.hpp).
using RedeemWitnessPrg = vole_mole::detail::NoPrg;

} // namespace vole_mole::pomfrit::detail

template <>
struct faest::OWF_CONSTANTS<faest::secpar::s128, vole_mole::pomfrit::detail::OWF_REDEEM>
    : vole_mole::detail::RelationConstants<vole_mole::pomfrit::detail::REDEEM_WITNESS_BITS,
                                           vole_mole::pomfrit::detail::REDEEM_QS_DEGREE,
                                           vole_mole::pomfrit::detail::RedeemWitnessPrg> {};

namespace vole_mole::pomfrit::detail {

using namespace vole_mole::detail;

// Same as faest::v3::faest_em_128_f.
using RedeemParams =
    faest::parameter_set<faest::secpar::s128, /* TAU */ 17, OWF_REDEEM, faest::prg::aes_ctr,
                         faest::prg::aes_ctr, faest::leaf_hash::aes_ctr, /* W_GRIND */ 8,
                         {faest::bavc::one_tree, /* T_OPEN */ 105},
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
        const uov::PublicKey* pk;
        uov::Target h;
    };

    static constexpr size_t NUM_CONSTRAINTS = REDEEM_NUM_CONSTRAINTS;

    // The witness prefix (r) is the target mask, which is generated before the proof. However, the
    // signature (s) is not determined until after the first step of proof generation.
    static constexpr size_t WITNESS_PREFIX_BYTES = uov::M;
    static_assert(WIT_OFF_R == 0 && WIT_OFF_S == WITNESS_PREFIX_BYTES);

    static constexpr std::span<const uint8_t> DST = POMFRIT_PROOF_DST;

    // The public map of the witness PRG, if the witness is derived.
    static constexpr std::span<const uint8_t> WITNESS_PRG_DST = POMFRIT_PRG_DST;

    static void hash_instance(faest::hash_state& hasher, const instance& x) {
        hasher.update(uov::detail::PublicKeyAccess::digest(*x.pk));
        hasher.update(x.h);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES> chal2) {
        static_assert(QS::max_degree == REDEEM_QS_DEGREE);
        using qs_1 = uov::detail::qs_val<QS, 1>;
        using qs_2 = uov::detail::qs_val<QS, 2>;

        // Add bit constraints: Every witness bit is a bit.
        for (size_t i = 0; i < REDEEM_WITNESS_BITS; ++i) {
            qs_add_bit_constraint(qs, qs->get_witness_bit(i));
        }

        // Evaluate l(P(s)), where l is the random linear combination of the M components.
        const uov::detail::Combination<QS> l(chal2, POMFRIT_COMBINE_DST);
        std::array<qs_1, uov::N> s;
        for (size_t i = 0; i < uov::N; ++i) {
            s[i] = qs->load_witness_8_bits_and_combine(8 * (WIT_OFF_S + i));
        }
        const qs_2 lp = uov::detail::qs_eval_combined_public_map<QS>(*x.pk, s, l);

        // Add output constraint: l(P(s) + h + r) = 0.
        qs_1 lr = qs_1(faest::poly1(0), qs);
        faest::poly_secpar<QS::secpar_v> lh = faest::poly_secpar<QS::secpar_v>::set_zero();
        for (size_t k = 0; k < uov::M; ++k) {
            const qs_1 r_k = qs->load_witness_8_bits_and_combine(8 * (WIT_OFF_R + k));
            lr += l.coeff(k) * r_k;
            lh += (l.coeff(k) * uov::detail::embed<QS>(x.h[k]))
                      .template reduce_to<faest::secpar_to_bits(QS::secpar_v)>();
        }
        qs->add_constraint(lp + qs_2(lr + lh));
    }
};

static_assert(WITNESS_BYTES<RedeemRelation> == REDEEM_WITNESS_BYTES);

using ProofView = faest::faest_signature<RedeemParams>;

} // namespace vole_mole::pomfrit::detail

#endif
