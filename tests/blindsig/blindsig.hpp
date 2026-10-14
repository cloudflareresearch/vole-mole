// A simplified Moussaka-style blind signature, used to compare VOLEitH with Longfellow (see
// experiments/longfellow). Not part of the library.
//
// Issuance:
//   1. The Client commits t = Com(nf, r) and sends t to the Issuer.
//   2. The Issuer derives s such that P(s) = t and sends s to the Client.
//
// The blind signature on nf is a proof of knowledge of (r, s) such that P(s) = Com(nf, r):
//
//   Instance: P (UOV public key), nf (nullifier)
//   Witness:  r (opening), s (UOV preimage)
//   Constraint: P(s) = Com(nf, r)
//
// Com(nf, r) is the Moussaka commitment with both contexts set to zero, i.e., the first M bytes of
// Keccak-p[800, 12] applied to MOUSSAKA_COM_DST || r || 0^9 || 0^32 || nf || 0^12.
//
// Arithmetization: The same as the Moussaka redemption proof for an Anchor Set of size 1, but
// without the selector. The commitment is evaluated as described in keccak/segmented.hpp (800
// constraints of degree at most 9 for each of the two committed intermediate states), and the
// output is compared with a random linear combination of the M components of P(s) (one constraint
// of degree 8). The witness layout is as follows:
//
//     0 ..  16   r
//    16 .. 135   s
//   135 .. 235   s5, the state after 5 rounds of the commitment
//   235 .. 335   s9, the state after 9 rounds of the commitment
//
// Every witness bit is constrained to be a bit, adding 2680 constraints of degree 2.
//
// We use the VOLE-in-the-Head parameters of FAEST-EM-128f v3.

#ifndef VOLE_MOLE_TESTS_BLINDSIG_HPP
#define VOLE_MOLE_TESTS_BLINDSIG_HPP

#include "vole_mole/keccak.hpp"
#include "vole_mole/moussaka.hpp"
#include "vole_mole/uov.hpp"

#include "dst.hpp"
#include "keccak/segmented.hpp"
#include "moussaka/commit.hpp"
#include "qs_bit.hpp"
#include "uov/circuit.hpp"
#include "uov/public_key.hpp"
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

namespace vole_mole::blindsig {

using moussaka::Nullifier;
using moussaka::detail::Opening;
using moussaka::detail::R_BYTES;

constexpr vole_mole::detail::Dst PROOF_DST = vole_mole::detail::make_dst("blnd", 0, 'p', '0');
constexpr vole_mole::detail::Dst COMBINE_DST = vole_mole::detail::make_dst("blnd", 0, 'l', '0');

// The input of Keccak-p[800, 12] for Com(nf, r).
inline Kp800State encode_com_state(const Nullifier& nf, const Opening& r) {
    return moussaka::detail::encode_com_state(nf, {}, {}, r);
}

inline uov::Target commit(const Nullifier& nf, const Opening& r) {
    const Kp800State out = keccak_p800(encode_com_state(nf, r));
    uov::Target t;
    std::copy_n(out.begin(), t.size(), t.begin());
    return t;
}

constexpr size_t QS_DEGREE = keccak::detail::QS_DEGREE;
static_assert(QS_DEGREE >= 2);
static_assert(QS_DEGREE - 1 + 4 <= 32, "faest-arch-opt supports at most 32 masks");

// Witness layout.
constexpr size_t WIT_OFF_R = 0;
constexpr size_t WIT_OFF_S = WIT_OFF_R + R_BYTES;
constexpr size_t WIT_OFF_STATES = WIT_OFF_S + uov::N;
constexpr size_t WITNESS_BYTES = WIT_OFF_STATES + keccak::detail::COMMITTED_STATES_BYTES;
constexpr size_t WITNESS_BITS = 8 * WITNESS_BYTES;

constexpr keccak::detail::InputMap COM_TO_WIT = [] {
    keccak::detail::InputMap map;
    map.fill(-1);
    for (size_t i = 0; i < R_BYTES; ++i) {
        map[moussaka::detail::COM_OFF_R + i] = static_cast<int>(WIT_OFF_R + i);
    }
    return map;
}();
static_assert(keccak::detail::input_map_is_valid(COM_TO_WIT, WIT_OFF_R, WIT_OFF_R + R_BYTES));

constexpr size_t NUM_CONSTRAINTS = WITNESS_BITS                              // bit constraints
                                   + keccak::detail::NUM_SEGMENT_CONSTRAINTS // committed states
                                   + 1; // P(s) = commitment (random linear combination)

inline std::array<uint8_t, WITNESS_BYTES> encode_witness(const Nullifier& nf, const Opening& r,
                                                         const uov::Preimage& s) {
    std::array<uint8_t, WITNESS_BYTES> w{};
    std::ranges::copy(r, w.begin() + WIT_OFF_R);
    std::ranges::copy(s, w.begin() + WIT_OFF_S);
    keccak::detail::encode_committed_states(
        std::span(w).subspan<WIT_OFF_STATES, keccak::detail::COMMITTED_STATES_BYTES>(),
        encode_com_state(nf, r));
    return w;
}

constexpr faest::owf OWF_BLINDSIG =
    static_cast<faest::owf>((0x42u << 8) | 0b10'0000 /* owf_flag_witness_bits_check */);
static_assert(faest::is_owf_with_witness_bits_check(OWF_BLINDSIG));

} // namespace vole_mole::blindsig

template <> struct faest::OWF_CONSTANTS<faest::secpar::s128, vole_mole::blindsig::OWF_BLINDSIG> {
    constexpr static size_t WITNESS_BITS = vole_mole::blindsig::WITNESS_BITS;
    constexpr static size_t QS_DEGREE = vole_mole::blindsig::QS_DEGREE;
    constexpr static bool valid = true;
};

namespace vole_mole::blindsig {

// Same as faest::v3::faest_em_128_f, except for the OWF.
using Params =
    faest::parameter_set<faest::secpar::s128, /* TAU */ 17, OWF_BLINDSIG, faest::prg::aes_ctr,
                         faest::prg::aes_ctr, faest::leaf_hash::aes_ctr, /* W_GRIND */ 8,
                         {faest::bavc::one_tree, /* T_OPEN */ 105},
                         /* CRT_VOLE_MASKS */ true, /* HASH_INPUTS_V3 */ true>;

struct Relation {
    using params = Params;

    struct instance {
        const uov::PublicKey& pk;
        Nullifier nf;
    };

    static constexpr size_t NUM_CONSTRAINTS = blindsig::NUM_CONSTRAINTS;
    static constexpr size_t WITNESS_PREFIX_BYTES = WITNESS_BYTES;
    static constexpr std::span<const uint8_t> DST = PROOF_DST;

    static void hash_instance(faest::hash_state& hasher, const instance& x) {
        hasher.update(uov::detail::PublicKeyAccess::digest(x.pk));
        hasher.update(x.nf);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES> chal2) {
        static_assert(QS::max_degree == QS_DEGREE);
        using faest::poly1;
        using vole_mole::detail::qs_add_bit_constraint;
        using qs_1 = keccak::detail::qs_val<QS, 1>;
        using qs_out = keccak::detail::qs_val<QS, keccak::detail::OUTPUT_DEGREE>;

        for (size_t i = 0; i < WITNESS_BITS; ++i) {
            qs_add_bit_constraint(qs, qs->get_witness_bit(i));
        }

        const auto out = keccak::detail::qs_keccak(
            qs, keccak::detail::qs_input(qs, encode_com_state(x.nf, {}), COM_TO_WIT),
            WIT_OFF_STATES, 8 * uov::M);

        const uov::detail::Combination<QS> l(chal2, COMBINE_DST);
        std::array<qs_1, uov::N> s;
        for (size_t i = 0; i < uov::N; ++i) {
            s[i] = qs->load_witness_8_bits_and_combine(8 * (WIT_OFF_S + i));
        }
        const auto lp = uov::detail::qs_eval_combined_public_map<QS>(x.pk, s, l);

        qs_out lout(poly1(0), qs);
        for (size_t k = 0; k < uov::M; ++k) {
            lout += l.coeff(k) * keccak::detail::qs_byte(out, k);
        }
        qs->add_constraint(lout + keccak::detail::qs_lift<keccak::detail::OUTPUT_DEGREE>(lp));
    }
};

constexpr size_t PROOF_BYTES = vole_mole::detail::PROOF_BYTES<Relation>;
using Proof = std::array<uint8_t, PROOF_BYTES>;

inline void prove(std::span<uint8_t, PROOF_BYTES> proof, const uov::PublicKey& pk,
                  const Nullifier& nf, const Opening& r, const uov::Preimage& s,
                  const vole_mole::detail::ProveSeed<Relation>& rho) {
    const auto witness = encode_witness(nf, r, s);
    vole_mole::detail::voleith_prove<Relation>(proof, witness, {pk, nf}, rho);
}

inline bool verify(std::span<const uint8_t, PROOF_BYTES> proof, const uov::PublicKey& pk,
                   const Nullifier& nf) {
    return vole_mole::detail::voleith_verify<Relation>(proof, {pk, nf});
}

} // namespace vole_mole::blindsig

#endif
