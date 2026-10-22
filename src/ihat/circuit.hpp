// Building blocks for VOLE-IHAT proofs.

#ifndef VOLE_MOLE_IHAT_CIRCUIT_HPP
#define VOLE_MOLE_IHAT_CIRCUIT_HPP

#include "vole_mole/ihat.hpp"
#include "vole_mole/uov.hpp"

#include "ct.hpp"
#include "keccak/segmented.hpp"
#include "qs_bit.hpp"
#include "uov/circuit.hpp"
#include "uov/public_key.hpp"

#include "hash.hpp"        // from faest-arch-opt
#include "parameters.hpp"  // from faest-arch-opt
#include "polynomials.hpp" // from faest-arch-opt
#include "vector_com.hpp"  // from faest-arch-opt; NOLINT(misc-include-cleaner)

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <type_traits>

namespace vole_mole::ihat::detail {

// The VOLEitH parameter set of a VOLE-IHAT relation, registered with faest-arch-opt as the "one-way
// function" OWF. Same as faest::v3::faest_em_128_f, except for the OWF.
template <faest::owf OWF>
using VoleithParams =
    faest::parameter_set<faest::secpar::s128, /* TAU */ 17, OWF, faest::prg::aes_ctr,
                         faest::prg::aes_ctr, faest::leaf_hash::aes_ctr, /* W_GRIND */ 8,
                         {faest::bavc::one_tree, /* T_OPEN */ 105},
                         /* CRT_VOLE_MASKS */ true, /* HASH_INPUTS_V3 */ true>;

// Whether parameter set P matches faest::v3::faest_em_128_f (except for the OWF) and derives the
// CRT VOLE masks from the witness, which must start with a uniform secret of at least secpar_bytes
// bytes.
template <typename P> constexpr bool is_em128f_variant() {
    using EM128F = faest::v3::faest_em_128_f;
    return std::is_same_v<typename P::bavc_t, EM128F::bavc_t> && P::tau_v == EM128F::tau_v &&
           P::delta_bits_v == EM128F::delta_bits_v && P::vole_prg_v == EM128F::vole_prg_v &&
           P::leaf_hash_v == EM128F::leaf_hash_v &&
           P::use_crt_vole_masks == EM128F::use_crt_vole_masks &&
           P::use_v3_hash_inputs == EM128F::use_v3_hash_inputs &&
           P::use_grinding == EM128F::use_grinding && P::CONSTS::REUSE_CRT_WITNESS &&
           P::CONSTS::CRT_LABEL_ROW_OFFSET == 0;
}

// Add bit constraints: Each of the first `num_bits` witness bits is a bit.
template <typename QS> void qs_add_bit_constraints(QS* qs, size_t num_bits) {
    for (size_t i = 0; i < num_bits; ++i) {
        vole_mole::detail::qs_add_bit_constraint(qs, qs->get_witness_bit(i));
    }
}

// Add output constraints: The first 8 * bytes.size() bits of the Keccak output `out` equal the
// public `bytes`. Adds one constraint (of degree OUTPUT_DEGREE) per bit.
template <typename QS>
void qs_add_output_constraints(
    QS* qs, const keccak::detail::QsState<QS, keccak::detail::OUTPUT_DEGREE>& out,
    std::span<const uint8_t> bytes) {
    for (size_t i = 0; i < 8 * bytes.size(); ++i) {
        qs->add_constraint(vole_mole::detail::qs_to_gfsecpar(
            out[i] + faest::poly1((bytes[i / 8] >> (i % 8)) & 1)));
    }
}

using AnchorSpan = std::span<const AnchorRef>;

// The selector b is a vector of MAX_ANCHORS bits, with b[u] at bit u % 8 of byte u / 8.
static_assert(MAX_ANCHORS % 8 == 0 && MAX_ANCHORS > 0);
constexpr size_t SELECTOR_BYTES = MAX_ANCHORS / 8;

// Number of constraints added by qs_add_selector_constraints.
constexpr size_t SELECTOR_NUM_CONSTRAINTS = MAX_ANCHORS // each b[u] is a bit, or zero if u >= N
                                            + (MAX_ANCHORS - 1) // parity constraints
                                            + 1;                // weight constraint

// Set the selector for the Anchor at index i. (The bits must be zero beforehand.)
inline void encode_selector(std::span<uint8_t, SELECTOR_BYTES> b, size_t i) {
    // Write every selector bit so that the memory access pattern doesn't depend on i.
    for (size_t u = 0; u < MAX_ANCHORS; ++u) {
        b[u / 8] |= static_cast<uint8_t>(vole_mole::detail::ct_eq_mask(u, i) & (1u << (u % 8)));
    }
}

template <typename QS> using Selector = std::array<vole_mole::detail::qs_bit<QS, 1>, MAX_ANCHORS>;

// Add selector constraints for an Anchor Set of size n, where the selector starts at witness byte
// `wit_off_b`, and return the selector. The constraints are, in order:
//
//   - b[u] is a bit for u in [n] and 0 otherwise (degree 2 or 1);
//   - sum(b[0..u+1]) * b[u+1] = 0 for each u in [MAX_ANCHORS - 1] (parity constraints, degree 2);
//   - sum(b) = 1 (weight constraint, degree 1).
//
// Together, they imply that exactly one b[u] with u < n is set: if b[v] = 1, then the parity
// constraint for v - 1 implies that an even number of bits below v are set; if v is the
// second-lowest set bit, then this is a contradiction.
template <typename QS>
Selector<QS> qs_add_selector_constraints(QS* qs, size_t n, size_t wit_off_b) {
    using vole_mole::detail::qs_add_bit_constraint;
    using vole_mole::detail::qs_mul;
    using vole_mole::detail::qs_to_gfsecpar;
    using qs_bit = vole_mole::detail::qs_bit<QS, 1>;

    Selector<QS> b;
    for (size_t u = 0; u < MAX_ANCHORS; ++u) {
        b[u] = qs->get_witness_bit(8 * wit_off_b + u);
        if (u < n) {
            qs_add_bit_constraint(qs, b[u]);
        } else {
            qs->add_constraint(qs_to_gfsecpar(b[u]));
        }
    }

    qs_bit prefix = b[0];
    for (size_t u = 0; u + 1 < MAX_ANCHORS; ++u) {
        qs->add_constraint(qs_to_gfsecpar(qs_mul<QS, 1, 1>(prefix, b[u + 1])));
        prefix += b[u + 1];
    }

    qs->add_constraint(qs_to_gfsecpar(prefix + faest::poly1(1)));
    return b;
}

// Add the signature constraint: Q(s) equals the first M bytes of the Keccak output `out`, where
// Q = sum_u b[u] * P[u] is the public map of the selected Anchor and the preimage s is the N
// witness bytes starting at `wit_off_s`.
//
// Rather than comparing each of the M components, we compare a random linear combination l of them,
// with coefficients in GF(2^128) derived from `chal2`. l(Q(s)) is computed as
// sum_u b[u] * l(P[u](s)): each l(P[u](s)) has degree 2, so l(Q(s)) has degree 3. Each byte of
// `out` is combined into an element of the GF(256) subfield of GF(2^128).
template <typename QS, size_t CHALLENGE_BYTES>
void qs_add_signature_constraint(
    QS* qs, AnchorSpan anchors, const Selector<QS>& b, size_t wit_off_s,
    const keccak::detail::QsState<QS, keccak::detail::OUTPUT_DEGREE>& out,
    std::span<const uint8_t, CHALLENGE_BYTES> chal2, std::span<const uint8_t> dst) {
    using faest::poly1;
    using vole_mole::detail::qs_mul;
    using qs_1 = keccak::detail::qs_val<QS, 1>;
    using qs_2 = keccak::detail::qs_val<QS, 2>;
    using qs_3 = keccak::detail::qs_val<QS, 3>;
    using qs_out = keccak::detail::qs_val<QS, keccak::detail::OUTPUT_DEGREE>;
    static_assert(3 <= keccak::detail::OUTPUT_DEGREE);

    const uov::detail::Combination<QS> l(chal2, dst);
    std::array<qs_1, uov::N> s;
    for (size_t i = 0; i < uov::N; ++i) {
        s[i] = qs->load_witness_8_bits_and_combine(8 * (wit_off_s + i));
    }
    qs_3 lq(poly1(0), qs);
    for (size_t u = 0; u < anchors.size(); ++u) {
        const qs_2 lp = uov::detail::qs_eval_combined_public_map<QS>(anchors[u].get(), s, l);
        lq += qs_mul<QS, 1, 2>(b[u], lp);
    }

    qs_out lout(poly1(0), qs);
    for (size_t k = 0; k < uov::M; ++k) {
        lout += l.coeff(k) * keccak::detail::qs_byte(out, k);
    }
    qs->add_constraint(lout + keccak::detail::qs_lift<keccak::detail::OUTPUT_DEGREE>(lq));
}

// The instance of a redemption proof.
struct RedeemInstance {
    AnchorSpan anchors;
    Nullifier nf;
    Context ctx_iss;
    Context ctx_red;
    ChallengeDigest challenge_digest;
};

inline void hash_redeem_instance(faest::hash_state& hasher, const RedeemInstance& x) {
    static_assert(MAX_ANCHORS <= UINT32_MAX);
    const auto update_u32 = [&hasher](size_t v) {
        const auto u = static_cast<uint32_t>(v);
        const std::array<uint8_t, 4> bytes = {static_cast<uint8_t>(u), static_cast<uint8_t>(u >> 8),
                                              static_cast<uint8_t>(u >> 16),
                                              static_cast<uint8_t>(u >> 24)};
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

} // namespace vole_mole::ihat::detail

#endif
