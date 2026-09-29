// QuickSilver constraints for the issuance proof:
//
//   Instance: t (commitment), ctx_iss (issuance context)
//   Witness:  nf (nullifier), r (opening), ctx_red (redemption context)
//   Constraint: t = commit(nf, ctx_iss, ctx_red, r)
//
// Arithmetization: Each round of Keccak-p[800, 12] has exactly one layer of ANDs, so the state
// after k rounds is a polynomial of degree 2^k in the input. We split the 12 rounds into segments
// of ROUNDS_PER_SEGMENT rounds and commit to the states between the segments as part of the
// witness. With 4 rounds per segment, each segment yields constraints of degree 2^4 = 16:
//
//   s4  = R_3(R_2(R_1(R_0(s0))))
//   s8  = R_7(R_6(R_5(R_4(s4))))
//   t   = R_11(R_10(R_9(R_8(s8))))[:45]
//
// where R_i is round i of Keccak-p[800, 12] and s0 is the initial state. Each segment except the
// last adds 800 constraints of degree 16; the last segment adds 360 constraints of degree 16. The
// witness layout is as follows:
//
//     0 ..  16   r
//    16 ..  32   ctx_red
//    32 ..  56   nf
//    56 .. 156   s4, the state after 4 rounds
//   156 .. 256   s8, the state after 8 rounds
//
// Soundness of the proof requires proving each witness bit is in fact a bit; this adds an
// additional 2048 constraints of degree 2.
//
// We use the VOLE-in-the-Head parameters of FAEST-EM-128f v3.

#ifndef VOLE_MOLE_MOUSSAKA_ISSUE_HPP
#define VOLE_MOLE_MOUSSAKA_ISSUE_HPP

#include "vole_mole/keccak.hpp"
#include "vole_mole/moussaka.hpp"

#include "dst.hpp"
#include "keccak/circuit.hpp"
#include "voleith.hpp"

#include "constants.hpp"
#include "hash.hpp"
#include "parameters.hpp"
#include "quicksilver.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace vole_mole::moussaka::detail {

using namespace vole_mole::detail;

// Commitment layout.
constexpr size_t COM_OFF_R = DST_BYTES;
constexpr size_t COM_OFF_CTX_ISS = COM_OFF_R + 25;
constexpr size_t COM_OFF_CTX_RED = COM_OFF_CTX_ISS + CTX_BYTES;
constexpr size_t COM_OFF_NF = COM_OFF_CTX_RED + CTX_BYTES;
static_assert(COM_OFF_NF + NF_BYTES + (68 - NF_BYTES - 2 * CTX_BYTES) == KP800_STATE_BYTES);

inline Kp800State encode_init_state(const Nullifier& nf, const Context& ctx_iss,
                                    const Context& ctx_red, const Opening& r) {
    Kp800State state{};
    std::ranges::copy(MOUSSAKA_COM_DST, state.begin());
    std::ranges::copy(r, state.begin() + COM_OFF_R);
    std::ranges::copy(ctx_iss, state.begin() + COM_OFF_CTX_ISS);
    std::ranges::copy(ctx_red, state.begin() + COM_OFF_CTX_RED);
    std::ranges::copy(nf, state.begin() + COM_OFF_NF);
    return state;
}

constexpr size_t ROUNDS_PER_SEGMENT = 4;
constexpr size_t NUM_SEGMENTS = KP800_ROUNDS / ROUNDS_PER_SEGMENT;
constexpr size_t NUM_COMMITTED_STATES = NUM_SEGMENTS - 1;
constexpr size_t ISSUE_QS_DEGREE = size_t{1} << ROUNDS_PER_SEGMENT;
static_assert(NUM_SEGMENTS * ROUNDS_PER_SEGMENT == KP800_ROUNDS);
// The CRT VOLE commitment needs ISSUE_QS_DEGREE - 1 masks for QuickSilver and 4 for the VOLE check.
// faest-arch-opt supports at most 32 masks.
static_assert(ISSUE_QS_DEGREE - 1 + 4 <= 32, "faest-arch-opt supports at most 32 masks");

// Witness layout.
constexpr size_t WIT_OFF_R = 0;
constexpr size_t WIT_OFF_CTX_RED = WIT_OFF_R + R_BYTES;
constexpr size_t WIT_OFF_NF = WIT_OFF_CTX_RED + CTX_BYTES;
constexpr size_t WIT_OFF_STATES = WIT_OFF_NF + NF_BYTES;
constexpr size_t ISSUE_WITNESS_BYTES = WIT_OFF_STATES + NUM_COMMITTED_STATES * KP800_STATE_BYTES;
constexpr size_t ISSUE_WITNESS_BITS = 8 * ISSUE_WITNESS_BYTES;

// Map of the index of each byte of the initial state of the commitment to its index in the witness.
// Index is -1 if the byte is public.
constexpr std::array<int, KP800_STATE_BYTES> COM_TO_WIT = [] {
    std::array<int, KP800_STATE_BYTES> map;
    map.fill(-1);
    for (size_t i = 0; i < R_BYTES; ++i) {
        map[COM_OFF_R + i] = static_cast<int>(WIT_OFF_R + i);
    }
    for (size_t i = 0; i < CTX_BYTES; ++i) {
        map[COM_OFF_CTX_RED + i] = static_cast<int>(WIT_OFF_CTX_RED + i);
    }
    for (size_t i = 0; i < NF_BYTES; ++i) {
        map[COM_OFF_NF + i] = static_cast<int>(WIT_OFF_NF + i);
    }
    return map;
}();

// Every entry of COM_TO_WIT is either -1 (public) or the index of a witness byte that holds part
// of the initial state (r, ctx_red, nf), and each of those witness bytes is used exactly once.
constexpr bool com_to_wit_is_valid() {
    std::array<int, WIT_OFF_STATES> uses{};
    for (const int w : COM_TO_WIT) {
        if (w == -1) {
            continue;
        }
        if (w < 0 || static_cast<size_t>(w) >= WIT_OFF_STATES) {
            return false;
        }
        ++uses[static_cast<size_t>(w)];
    }
    return std::ranges::all_of(uses, [](int n) { return n == 1; });
}
static_assert(com_to_wit_is_valid(), "COM_TO_WIT is malformed");

constexpr size_t ISSUE_NUM_CONSTRAINTS =
    ISSUE_WITNESS_BITS                                   // bit constraints
    + NUM_COMMITTED_STATES * vole_mole::KP800_STATE_BITS // segment ends in a committed state
    + 8 * uov::M;                                        // last segment ends in the commitment

// Compute the full witness, including the intermediate Keccak states.
inline std::array<uint8_t, ISSUE_WITNESS_BYTES> encode_issue_witness(const Nullifier& nf,
                                                                     const Context& ctx_iss,
                                                                     const Context& ctx_red,
                                                                     const Opening& r) {
    std::array<uint8_t, ISSUE_WITNESS_BYTES> w{};
    std::ranges::copy(r, w.begin() + WIT_OFF_R);
    std::ranges::copy(ctx_red, w.begin() + WIT_OFF_CTX_RED);
    std::ranges::copy(nf, w.begin() + WIT_OFF_NF);

    Kp800State state = encode_init_state(nf, ctx_iss, ctx_red, r);
    for (size_t k = 0; k < NUM_COMMITTED_STATES; ++k) {
        keccak_p800_rounds(state, k * ROUNDS_PER_SEGMENT, ROUNDS_PER_SEGMENT);
        std::ranges::copy(state, w.begin() + WIT_OFF_STATES + k * KP800_STATE_BYTES);
    }
    return w;
}

// A QuickSilver-committed value of degree `deg`.
//
// Keccak state bits are GF(2) values, but we represent them as elements of GF(2^128)
// (`quicksilver_gfsecpar`) rather than GF(2) (`quicksilver_gf2`): faest-arch-opt only implements
// products of `quicksilver_gf2` values for the verifier and for degree-0 operands, since FAEST
// itself never multiplies two GF(2) values of positive degree.
template <typename QS, size_t deg> using qs_val = faest::quicksilver_gfsecpar<QS, deg>;

// One Keccak round: degree d in, degree 2d out.
template <typename QS, size_t d>
std::vector<qs_val<QS, 2 * d>> qs_keccak_round(const std::vector<qs_val<QS, d>>& in, size_t round) {
    const auto chi = [](const qs_val<QS, d>& a, const qs_val<QS, d>& b, const qs_val<QS, d>& c) {
        // a ^ (~b & c) = a + (b + 1) * c
        return qs_val<QS, 2 * d>(a) + (b + faest::poly1(1)) * c;
    };
    const auto add_one = [](const qs_val<QS, 2 * d>& x) { return x + faest::poly1(1); };
    return keccak_round(in, round, chi, add_one);
}

// `num_rounds` rounds starting at `first_round`: degree d in, degree d * 2^num_rounds out.
template <typename QS, size_t num_rounds, size_t d = 1>
auto qs_keccak_rounds(const std::vector<qs_val<QS, d>>& in, size_t first_round) {
    if constexpr (num_rounds == 0) {
        return in;
    } else {
        return qs_keccak_rounds<QS, num_rounds - 1, 2 * d>(qs_keccak_round<QS, d>(in, first_round),
                                                           first_round + 1);
    }
}

// The VOLEitH parameter set for IssueRelation.
//
// faest-arch-opt describes the statement being proven through `faest::OWF_CONSTANTS<S, owf>`, from
// which it derives the witness length and the QuickSilver degree. We register the issuance relation
// as a new "one-way function" OWF_MOUSSAKA_ISSUE so that we can reuse the machinery unmodified.
//
// TODO(cjpatton) This is a bit hacky. Discuss with the faest-arch-opt authors whether/how to
// properly extract a generic VOLEitH implementation (that is wire compatible with FAEST).
constexpr faest::owf OWF_MOUSSAKA_ISSUE =
    static_cast<faest::owf>((0x4du << 8) | 0b10'0000 /* owf_flag_witness_bits_check */);
static_assert(faest::is_owf_with_witness_bits_check(OWF_MOUSSAKA_ISSUE));
static_assert(!faest::is_owf_with_aes_ecb(OWF_MOUSSAKA_ISSUE));
static_assert(!faest::is_owf_with_aes_em(OWF_MOUSSAKA_ISSUE));

} // namespace vole_mole::moussaka::detail

// Must be declared outside of our namespace, since it specializes a template of faest-arch-opt.
template <>
struct faest::OWF_CONSTANTS<faest::secpar::s128, vole_mole::moussaka::detail::OWF_MOUSSAKA_ISSUE> {
    constexpr static size_t WITNESS_BITS = vole_mole::moussaka::detail::ISSUE_WITNESS_BITS;
    constexpr static size_t QS_DEGREE = vole_mole::moussaka::detail::ISSUE_QS_DEGREE;
    constexpr static bool valid = true;
};

namespace vole_mole::moussaka::detail {

// Same as faest::v3::faest_em_128_f, except for the OWF.
using IssueParams =
    faest::parameter_set<faest::secpar::s128, /* TAU */ 17, OWF_MOUSSAKA_ISSUE, faest::prg::aes_ctr,
                         faest::prg::aes_ctr, faest::leaf_hash::aes_ctr, /* W_GRIND */ 8,
                         {faest::bavc::one_tree, /* T_OPEN */ 105},
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
        Commitment t;
        Context ctx_iss;
    };

    static constexpr size_t NUM_CONSTRAINTS = ISSUE_NUM_CONSTRAINTS;

    static constexpr size_t WITNESS_PREFIX_BYTES = ISSUE_WITNESS_BYTES;

    static constexpr std::span<const uint8_t> DST = MOUSSAKA_ISSUE_PROOF_DST;

    static void hash_instance(faest::hash_state& hasher, const instance& x) {
        hasher.update(x.t);
        hasher.update(x.ctx_iss);
    }

    template <typename QS> static void constraints(QS* qs, const instance& x) {
        static_assert(QS::max_degree == ISSUE_QS_DEGREE);
        using faest::poly1;
        using qs_bit = qs_val<QS, 1>;
        using qs_max = qs_val<QS, ISSUE_QS_DEGREE>;

        // Add bit constraints: Every witness bit is a bit.
        for (size_t i = 0; i < ISSUE_WITNESS_BITS; ++i) {
            qs->add_bit_constraint(qs_bit(qs->get_witness_bit(i)));
        }

        // Set up the initial state of the commitment.
        const Kp800State public_state = encode_init_state({}, x.ctx_iss, {}, {});
        std::vector<qs_bit> state;
        state.reserve(KP800_STATE_BITS);
        for (size_t i = 0; i < KP800_STATE_BITS; ++i) {
            const int witness_byte = COM_TO_WIT[i / 8];
            if (witness_byte >= 0) {
                state.emplace_back(
                    qs->get_witness_bit(8 * static_cast<size_t>(witness_byte) + i % 8));
            } else {
                // Public bytes are treated as constants.
                state.emplace_back(poly1((public_state[i / 8] >> (i % 8)) & 1), qs);
            }
        }

        // Add segment constraints: All but the last segment end in the expected intermediate state.
        for (size_t k = 0; k < NUM_COMMITTED_STATES; ++k) {
            const auto out =
                qs_keccak_rounds<QS, ROUNDS_PER_SEGMENT>(state, k * ROUNDS_PER_SEGMENT);
            const size_t bit_offset = 8 * (WIT_OFF_STATES + k * KP800_STATE_BYTES);
            for (size_t i = 0; i < KP800_STATE_BITS; ++i) {
                const qs_bit s(qs->get_witness_bit(bit_offset + i));
                qs->add_constraint(out[i] + qs_max(s));
                state[i] = s;
            }
        }

        // Add output constraint: The last segment ends in the commitment.
        const auto out = qs_keccak_rounds<QS, ROUNDS_PER_SEGMENT>(state, NUM_COMMITTED_STATES *
                                                                             ROUNDS_PER_SEGMENT);
        for (size_t i = 0; i < 8 * uov::M; ++i) {
            qs->add_constraint(out[i] + poly1((x.t[i / 8] >> (i % 8)) & 1));
        }
    }
};

// The public header hard-codes the proof size, so check it against faest-arch-opt's.
static_assert(ISSUE_PROOF_BYTES == PROOF_BYTES<IssueRelation>,
              "ISSUE_PROOF_BYTES is out of sync with faest-arch-opt");

using IssueProof = std::span<uint8_t, ISSUE_PROOF_BYTES>;

// Compute the issuance proof pf_iss that t = Com(nf, ctx_iss, ctx_red, r), where t and ctx_iss
// are public. `rho` is randomness for the VOLEitH prover (see `voleith_prove`).
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if grinding fails (which
// happens with negligible probability).
inline void prove_issue_request(IssueProof pf_iss, const Commitment& t, const Nullifier& nf,
                                const Context& ctx_iss, const Context& ctx_red, const Opening& r,
                                const ProveSeed<IssueRelation>& rho) {
    const auto witness = encode_issue_witness(nf, ctx_iss, ctx_red, r);
    voleith_prove<IssueRelation>(pf_iss, witness, {t, ctx_iss}, rho);
}

// Check that the issue request commits to the given issuance context, i.e., verify the issuance
// proof (steps 1-3 of IssueResponse).
//
// This is `inline` in an internal header, rather than part of the public API, so that it's only
// compiled into the code that uses it (currently just the tests).
inline bool verify_issue_request(const IssueRequest& request, const Context& ctx_iss) {
    Commitment t;
    std::ranges::copy(std::span(request).first<uov::M>(), t.begin());
    return voleith_verify<IssueRelation>(std::span(request).last<ISSUE_PROOF_BYTES>(),
                                         {t, ctx_iss});
}

} // namespace vole_mole::moussaka::detail

#endif
