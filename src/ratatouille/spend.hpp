// QuickSilver constraints for the spend proof:
//
//   Instance: P (Issuer public key), nf (nullifier of the current state), d (credits to spend),
//             c' (commitment to the updated state), ctx_iss (issuance context)
//   Witness:  t, r, x, s (current state and its signature), nf', t', r' (updated state)
//   Constraints:
//     - P(s) = Tag(Com(nf, ctx_iss, t, r), x)  // V1: current state was certified
//     - c' = Com(nf', ctx_iss, t', r')         // V2: c' commits to updated state
//     - t' = t + x - d                         // V3: credits are conserved
//     - t', x, d in [2^(8*L)]                  // V4: credits are in range
//
// Arithmetization: Each of the three Keccak-p[800, 12] evaluations (one Com() for the current state
// and another for the next state, and a Tag() for the refund) is evaluated as described in
// keccak/segmented.hpp, which adds 800 constraints of degree at most 9 for each of the two
// committed intermediate states per evaluation.
//
// V2 is similar to the issuance proof. For V1, the output of Com() is the input of Tag(). We commit
// to c = Com(nf, ctx_iss, t, r) in the witness, add one constraint (of degree 8) per bit of c that
// the output of Com is c, and use c as the input of Tag. As in the Moussaka redemption proof and
// the PomFRIT blind signature, each byte of the output of Tag() is combined into an element of the
// GF(256) subfield of GF(2^128). Rather than compare each of the M components with P(s), we compare
// a random linear combination l of them, with coefficients in GF(2^128) derived from chal2, adding
// a single constraint.
//
// V4 holds by construction, since each credit value is encoded with L bytes. For V3, we check that
// t + x = t' + d over the integers, with each sum computed by a ripple-carry adder: Let a_i be bit
// i of a (from the least significant bit), and similarly for b. We commit to the carries
// k_1, ..., k_64 of a + b, where k_0 = 0 and k_(i+1) = maj(a_i, b_i, k_i), the majority function
// of the three bits (i.e., the carry out of a_i + b_i + k_i), which over GF(2) is
// a_i b_i + a_i k_i + b_i k_i; bit i of a + b is a_i + b_i + k_i for i < 64, and bit 64 is k_64
// (see qs_add_credits). This adds 64 constraints (of degree 2) per adder, and 65 constraints (of
// degree 1) that the sums are equal.
//
// The witness layout is as follows:
//
//     0 ..  16   r
//    16 ..  24   t
//    24 ..  32   x
//    32 ..  64   c = Com(nf, ctx_iss, t, r)
//    64 ..  88   nf'
//    88 ..  96   t'
//    96 .. 112   r'
//   112 .. 231   s
//   231 .. 239   carries of t + x, encoded as a credit value with k_(i+1) as bit i
//   239 .. 247   carries of t' + d, likewise
//   247 .. 447   s5, s9 of Com
//   447 .. 647   s5, s9 of Tag
//   647 .. 847   s5, s9 of Com'
//
// As always, every witness bit is constrained to be a bit, adding 6776 constraints of degree 2. We
// use the VOLE-in-the-Head parameters of FAEST-EM-128f v3.

#ifndef VOLE_MOLE_RATATOUILLE_SPEND_HPP
#define VOLE_MOLE_RATATOUILLE_SPEND_HPP

#include "vole_mole/keccak.hpp"
#include "vole_mole/ratatouille.hpp"
#include "vole_mole/uov.hpp"

#include "dst.hpp"
#include "keccak/segmented.hpp"
#include "qs_bit.hpp"
#include "ratatouille/commit.hpp"
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
#include <functional>
#include <span>
#include <type_traits>

namespace vole_mole::ratatouille::detail {

constexpr size_t SPEND_QS_DEGREE =
    std::max(keccak::detail::QS_DEGREE, size_t{2}); // bit and carry constraints: 2
static_assert(SPEND_QS_DEGREE - 1 + 4 <= 32, "faest-arch-opt supports at most 32 masks");
static_assert(2 <= keccak::detail::OUTPUT_DEGREE); // P(s) is lifted to the output degree

// Number of bits of a credit value.
constexpr size_t CREDIT_BITS = 8 * CREDIT_BYTES;

// Witness layout.
constexpr size_t SPEND_WIT_OFF_R = 0;
constexpr size_t SPEND_WIT_OFF_T = SPEND_WIT_OFF_R + R_BYTES;
constexpr size_t SPEND_WIT_OFF_X = SPEND_WIT_OFF_T + CREDIT_BYTES;
constexpr size_t SPEND_WIT_OFF_C = SPEND_WIT_OFF_X + CREDIT_BYTES;
constexpr size_t SPEND_WIT_OFF_NF_NEXT = SPEND_WIT_OFF_C + COMMITMENT_BYTES;
constexpr size_t SPEND_WIT_OFF_T_NEXT = SPEND_WIT_OFF_NF_NEXT + NF_BYTES;
constexpr size_t SPEND_WIT_OFF_R_NEXT = SPEND_WIT_OFF_T_NEXT + CREDIT_BYTES;
constexpr size_t SPEND_WIT_OFF_S = SPEND_WIT_OFF_R_NEXT + R_BYTES;
constexpr size_t SPEND_WIT_OFF_K1 = SPEND_WIT_OFF_S + uov::N;        // carries of t + x
constexpr size_t SPEND_WIT_OFF_K2 = SPEND_WIT_OFF_K1 + CREDIT_BYTES; // carries of t' + d
constexpr size_t SPEND_WIT_OFF_COM_STATES = SPEND_WIT_OFF_K2 + CREDIT_BYTES;
constexpr size_t SPEND_WIT_OFF_TAG_STATES =
    SPEND_WIT_OFF_COM_STATES + keccak::detail::COMMITTED_STATES_BYTES;
constexpr size_t SPEND_WIT_OFF_COM_NEXT_STATES =
    SPEND_WIT_OFF_TAG_STATES + keccak::detail::COMMITTED_STATES_BYTES;
constexpr size_t SPEND_WITNESS_BYTES =
    SPEND_WIT_OFF_COM_NEXT_STATES + keccak::detail::COMMITTED_STATES_BYTES;
constexpr size_t SPEND_WITNESS_BITS = 8 * SPEND_WITNESS_BYTES;

// V1: Map of the index of each byte of the input of Com() to its index in the witness. The opening
// and credit are secret; the nullifier is public.
constexpr keccak::detail::InputMap SPEND_COM_TO_WIT = [] {
    keccak::detail::InputMap map;
    map.fill(-1);
    for (size_t i = 0; i < R_BYTES; ++i) {
        map[COM_OFF_R + i] = static_cast<int>(SPEND_WIT_OFF_R + i);
    }
    for (size_t i = 0; i < CREDIT_BYTES; ++i) {
        map[COM_OFF_T + i] = static_cast<int>(SPEND_WIT_OFF_T + i);
    }
    return map;
}();
static_assert(keccak::detail::input_map_is_valid(SPEND_COM_TO_WIT, SPEND_WIT_OFF_R,
                                                 SPEND_WIT_OFF_X),
              "SPEND_COM_TO_WIT is malformed");

// V1: Map of the index of each byte of the input of Tag() to its index in the witness. The
// commitment and refund are secret.
constexpr keccak::detail::InputMap SPEND_TAG_TO_WIT = [] {
    keccak::detail::InputMap map;
    map.fill(-1);
    for (size_t i = 0; i < COMMITMENT_BYTES; ++i) {
        map[TAG_OFF_C + i] = static_cast<int>(SPEND_WIT_OFF_C + i);
    }
    for (size_t i = 0; i < CREDIT_BYTES; ++i) {
        map[TAG_OFF_X + i] = static_cast<int>(SPEND_WIT_OFF_X + i);
    }
    return map;
}();
static_assert(keccak::detail::input_map_is_valid(SPEND_TAG_TO_WIT, SPEND_WIT_OFF_X,
                                                 SPEND_WIT_OFF_NF_NEXT),
              "SPEND_TAG_TO_WIT is malformed");

// V2: Map of the index of each byte of Com() to its index in the witness. The nullifier, opening,
// and credit of the updated state are secret.
constexpr keccak::detail::InputMap SPEND_COM_NEXT_TO_WIT = [] {
    keccak::detail::InputMap map;
    map.fill(-1);
    for (size_t i = 0; i < NF_BYTES; ++i) {
        map[COM_OFF_NF + i] = static_cast<int>(SPEND_WIT_OFF_NF_NEXT + i);
    }
    for (size_t i = 0; i < CREDIT_BYTES; ++i) {
        map[COM_OFF_T + i] = static_cast<int>(SPEND_WIT_OFF_T_NEXT + i);
    }
    for (size_t i = 0; i < R_BYTES; ++i) {
        map[COM_OFF_R + i] = static_cast<int>(SPEND_WIT_OFF_R_NEXT + i);
    }
    return map;
}();
static_assert(keccak::detail::input_map_is_valid(SPEND_COM_NEXT_TO_WIT, SPEND_WIT_OFF_NF_NEXT,
                                                 SPEND_WIT_OFF_S),
              "SPEND_COM_NEXT_TO_WIT is malformed");

constexpr size_t SPEND_NUM_CONSTRAINTS =
    SPEND_WITNESS_BITS                            // bit constraints
    + 2 * CREDIT_BITS                             // V3: carries of t + x and t' + d
    + CREDIT_BITS + 1                             // V3: t + x = t' + d
    + 3 * keccak::detail::NUM_SEGMENT_CONSTRAINTS // V1,V2: segments end in a committed state
    + 8 * COMMITMENT_BYTES                        // V1: Com() ends in c
    + 1                     // V1: Tag() ends in P(s) (random linear combination)
    + 8 * COMMITMENT_BYTES; // V2: Com() ends in c'

// The carries k_1, ..., k_64 of a + b, with k_(i+1) at bit i.
constexpr uint64_t carries(uint64_t a, uint64_t b) {
    uint64_t k = 0;
    uint64_t out = 0;
    for (size_t i = 0; i < CREDIT_BITS; ++i) {
        const uint64_t ai = (a >> i) & 1, bi = (b >> i) & 1;
        k = (ai & bi) | (ai & k) | (bi & k);
        out |= k << i;
    }
    return out;
}

// Ripple-carry adder: compute the CREDIT_BITS + 1 bits of a + b over the integers, where a and b
// are credit values given bit by bit: a(i) and b(i) return bit i (from the least significant bit)
// as a committed bit of degree 1, which may be public. The carries k_1, ..., k_64 are the witness
// bits starting at witness byte `wit_off_carries` (see `carries`).
//
// Adds CREDIT_BITS constraints of degree 2: k_(i+1) = maj(a_i, b_i, k_i), where k_0 = 0 and maj is
// the majority function, i.e., the carry out of a_i + b_i + k_i, which over GF(2) is
// a_i b_i + a_i k_i + b_i k_i. Bit i of the sum is a_i + b_i + k_i for i < 64, and bit 64 is k_64.
template <typename QS, typename A, typename B>
std::array<qs_bit<QS, 1>, CREDIT_BITS + 1> qs_add_credits(QS* qs, const A& a, const B& b,
                                                          size_t wit_off_carries) {
    using bit_1 = qs_bit<QS, 1>;
    using bit_2 = qs_bit<QS, 2>;
    std::array<bit_1, CREDIT_BITS + 1> sum;
    bit_1 k(faest::poly1(0), qs); // k_0
    for (size_t i = 0; i < CREDIT_BITS; ++i) {
        const bit_1 a_i = a(i), b_i = b(i);
        sum[i] = a_i + b_i + k;
        const bit_1 next = qs->get_witness_bit(8 * wit_off_carries + i);
        const bit_2 maj =
            qs_mul<QS, 1, 1>(a_i, b_i) + qs_mul<QS, 1, 1>(a_i, k) + qs_mul<QS, 1, 1>(b_i, k);
        qs->add_constraint(qs_to_gfsecpar(maj + keccak::detail::qs_lift<2>(next)));
        k = next;
    }
    sum[CREDIT_BITS] = k;
    return sum;
}

// The current and updated state of a spend.
struct SpendState {
    Nullifier nf;
    Credits t;
    Opening r;
    Credits x;
    uov::Preimage s;
    Nullifier nf_next; // nf'
    Credits t_next;    // t'
    Opening r_next;    // r'
};

// Compute the full witness, including c, the carries, and the intermediate Keccak states. The
// witness only satisfies the relation if the state is valid.
inline std::array<uint8_t, SPEND_WITNESS_BYTES>
encode_spend_witness(const SpendState& st, Credits d, const Context& ctx_iss) {
    std::array<uint8_t, SPEND_WITNESS_BYTES> w{};
    const auto put = [&w](size_t off, const auto& bytes) {
        std::ranges::copy(bytes, w.begin() + off);
    };

    const Kp800State com_in = encode_com_state(st.nf, ctx_iss, st.t, st.r);
    const Kp800State com_out = keccak_p800(com_in);
    Commitment c;
    std::copy_n(com_out.begin(), c.size(), c.begin());

    put(SPEND_WIT_OFF_R, st.r);
    put(SPEND_WIT_OFF_T, encode_credits(st.t));
    put(SPEND_WIT_OFF_X, encode_credits(st.x));
    put(SPEND_WIT_OFF_C, c);
    put(SPEND_WIT_OFF_NF_NEXT, st.nf_next);
    put(SPEND_WIT_OFF_T_NEXT, encode_credits(st.t_next));
    put(SPEND_WIT_OFF_R_NEXT, st.r_next);
    put(SPEND_WIT_OFF_S, st.s);

    put(SPEND_WIT_OFF_K1, encode_credits(carries(st.t, st.x)));
    put(SPEND_WIT_OFF_K2, encode_credits(carries(st.t_next, d)));

    using keccak::detail::COMMITTED_STATES_BYTES;
    using keccak::detail::encode_committed_states;
    encode_committed_states(
        std::span(w).subspan<SPEND_WIT_OFF_COM_STATES, COMMITTED_STATES_BYTES>(), com_in);
    encode_committed_states(
        std::span(w).subspan<SPEND_WIT_OFF_TAG_STATES, COMMITTED_STATES_BYTES>(),
        encode_tag_state(c, st.x));
    encode_committed_states(
        std::span(w).subspan<SPEND_WIT_OFF_COM_NEXT_STATES, COMMITTED_STATES_BYTES>(),
        encode_com_state(st.nf_next, ctx_iss, st.t_next, st.r_next));
    return w;
}

// The VOLEitH parameter set for SpendRelation.
constexpr faest::owf OWF_RATATOUILLE_SPEND =
    static_cast<faest::owf>((0x53u << 8) | 0b10'0000 /* owf_flag_witness_bits_check */);
static_assert(faest::is_owf_with_witness_bits_check(OWF_RATATOUILLE_SPEND));
static_assert(!faest::is_owf_with_aes_ecb(OWF_RATATOUILLE_SPEND));
static_assert(!faest::is_owf_with_aes_em(OWF_RATATOUILLE_SPEND));

} // namespace vole_mole::ratatouille::detail

// Must be declared outside of our namespace, since it specializes a template of faest-arch-opt.
template <>
struct faest::OWF_CONSTANTS<faest::secpar::s128,
                            vole_mole::ratatouille::detail::OWF_RATATOUILLE_SPEND>
    : vole_mole::detail::PaddedOwfConstants<faest::secpar::s128,
                                            vole_mole::ratatouille::detail::SPEND_WITNESS_BITS,
                                            vole_mole::ratatouille::detail::SPEND_QS_DEGREE> {};

namespace vole_mole::ratatouille::detail {

// Same as faest::v3::faest_em_128_f, except for the OWF.
using SpendParams =
    faest::parameter_set<faest::secpar::s128, /* TAU */ 17, OWF_RATATOUILLE_SPEND,
                         faest::prg::aes_ctr, faest::prg::aes_ctr, faest::leaf_hash::aes_ctr,
                         /* W_GRIND */ 8, {faest::bavc::one_tree, /* T_OPEN */ 105},
                         /* CRT_VOLE_MASKS */ true, /* HASH_INPUTS_V3 */ true>;

namespace check {
using EM128F = faest::v3::faest_em_128_f;
static_assert(std::is_same_v<SpendParams::bavc_t, EM128F::bavc_t>);
static_assert(SpendParams::tau_v == EM128F::tau_v);
static_assert(SpendParams::delta_bits_v == EM128F::delta_bits_v);
static_assert(SpendParams::vole_prg_v == EM128F::vole_prg_v);
static_assert(SpendParams::leaf_hash_v == EM128F::leaf_hash_v);
static_assert(SpendParams::use_crt_vole_masks == EM128F::use_crt_vole_masks);
static_assert(SpendParams::use_v3_hash_inputs == EM128F::use_v3_hash_inputs);
static_assert(SpendParams::use_grinding == EM128F::use_grinding);
} // namespace check

struct SpendRelation {
    using params = SpendParams;

    struct instance {
        std::reference_wrapper<const uov::PublicKey> pk;
        Nullifier nf;
        Credits d;
        Commitment c_next; // c'
        Context ctx_iss;
    };

    static constexpr size_t NUM_CONSTRAINTS = SPEND_NUM_CONSTRAINTS;

    static constexpr size_t WITNESS_PREFIX_BYTES = SPEND_WITNESS_BYTES;

    static constexpr std::span<const uint8_t> DST = RATATOUILLE_SPEND_PROOF_DST;

    static void hash_instance(faest::hash_state& hasher, const instance& x) {
        hasher.update(uov::detail::PublicKeyAccess::digest(x.pk));
        hasher.update(x.nf);
        hasher.update(encode_credits(x.d));
        hasher.update(x.c_next);
        hasher.update(x.ctx_iss);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES> chal2) {
        static_assert(QS::max_degree == SPEND_QS_DEGREE);
        using faest::poly1;
        using keccak::detail::OUTPUT_DEGREE;
        using keccak::detail::qs_lift;
        using qs_1 = keccak::detail::qs_val<QS, 1>;
        using qs_2 = keccak::detail::qs_val<QS, 2>;
        using qs_out = keccak::detail::qs_val<QS, OUTPUT_DEGREE>;
        using bit_1 = qs_bit<QS, 1>;

        // Add bit constraints: Every witness bit is a bit.
        for (size_t i = 0; i < SPEND_WITNESS_BITS; ++i) {
            qs_add_bit_constraint(qs, qs->get_witness_bit(i));
        }

        // V3: Add carry constraints for t + x and t' + d (see qs_add_credits).
        const auto witness_credit = [qs](size_t off) {
            return [qs, off](size_t i) { return bit_1(qs->get_witness_bit(credit_bit(off, i))); };
        };
        const auto sum1 = qs_add_credits(qs, witness_credit(SPEND_WIT_OFF_T),
                                         witness_credit(SPEND_WIT_OFF_X), SPEND_WIT_OFF_K1);
        const auto sum2 = qs_add_credits(
            qs, witness_credit(SPEND_WIT_OFF_T_NEXT),
            [qs, d = x.d](size_t i) { return bit_1(poly1((d >> i) & 1), qs); }, SPEND_WIT_OFF_K2);

        // V3: Add conservation constraints: t + x = t' + d.
        for (size_t i = 0; i <= CREDIT_BITS; ++i) {
            qs->add_constraint(qs_to_gfsecpar(sum1[i] + sum2[i]));
        }

        // V1: Add constraints for Com() and Tag().
        const auto com_out = keccak::detail::qs_keccak(
            qs,
            keccak::detail::qs_input(qs, encode_com_state(x.nf, x.ctx_iss, 0, {}),
                                     SPEND_COM_TO_WIT),
            SPEND_WIT_OFF_COM_STATES, 8 * COMMITMENT_BYTES);
        for (size_t i = 0; i < 8 * COMMITMENT_BYTES; ++i) {
            const bit_1 c_i = qs->get_witness_bit(8 * SPEND_WIT_OFF_C + i);
            qs->add_constraint(qs_to_gfsecpar(com_out[i] + qs_lift<OUTPUT_DEGREE>(c_i)));
        }

        const auto tag_out = keccak::detail::qs_keccak(
            qs, keccak::detail::qs_input(qs, encode_tag_state({}, 0), SPEND_TAG_TO_WIT),
            SPEND_WIT_OFF_TAG_STATES, 8 * uov::M);

        // V1: P(s) = Tag(c, x), checked as l(P(s)) = l(Tag(c, x)) for the random linear combination
        // l of the M components. Each byte of the output of Tag is combined into an element of
        // GF(256).
        const uov::detail::Combination<QS> l(chal2, RATATOUILLE_SPEND_COMBINE_DST);
        std::array<qs_1, uov::N> s;
        for (size_t i = 0; i < uov::N; ++i) {
            s[i] = qs->load_witness_8_bits_and_combine(8 * (SPEND_WIT_OFF_S + i));
        }
        const qs_2 lp = uov::detail::qs_eval_combined_public_map<QS>(x.pk, s, l);
        qs_out ly(poly1(0), qs);
        for (size_t k = 0; k < uov::M; ++k) {
            ly += l.coeff(k) * keccak::detail::qs_byte(tag_out, k);
        }
        qs->add_constraint(ly + qs_lift<OUTPUT_DEGREE>(lp));

        // V2: Add constraints for Com().
        const auto com_next_out = keccak::detail::qs_keccak(
            qs,
            keccak::detail::qs_input(qs, encode_com_state({}, x.ctx_iss, 0, {}),
                                     SPEND_COM_NEXT_TO_WIT),
            SPEND_WIT_OFF_COM_NEXT_STATES, 8 * COMMITMENT_BYTES);
        for (size_t i = 0; i < 8 * COMMITMENT_BYTES; ++i) {
            qs->add_constraint(
                qs_to_gfsecpar(com_next_out[i] + poly1((x.c_next[i / 8] >> (i % 8)) & 1)));
        }
    }
};

static_assert(WITNESS_BYTES<SpendRelation> == SPEND_WITNESS_BYTES);

static_assert(SPEND_PROOF_BYTES == PROOF_BYTES<SpendRelation>,
              "SPEND_PROOF_BYTES is out of sync with faest-arch-opt");

using SpendProof = std::span<uint8_t, SPEND_PROOF_BYTES>;
using ConstSpendProof = std::span<const uint8_t, SPEND_PROOF_BYTES>;

// Compute the spend proof. The caller must ensure that the witness satisfies the instance.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if grinding fails (which
// happens with negligible probability).
inline void prove_spend_request(SpendProof pf_spend, const uov::PublicKey& pk, const SpendState& st,
                                Credits d, const Commitment& c_next, const Context& ctx_iss,
                                const ProveSeed<SpendRelation>& rho) {
    const auto witness = encode_spend_witness(st, d, ctx_iss);
    voleith_prove<SpendRelation>(pf_spend, witness, {pk, st.nf, d, c_next, ctx_iss}, rho);
}

// Verify the spend proof.
inline bool verify_spend_proof(ConstSpendProof pf_spend, const uov::PublicKey& pk,
                               const Nullifier& nf, Credits d, const Commitment& c_next,
                               const Context& ctx_iss) {
    return voleith_verify<SpendRelation>(pf_spend, {pk, nf, d, c_next, ctx_iss});
}

} // namespace vole_mole::ratatouille::detail

#endif
