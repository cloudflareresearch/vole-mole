// QuickSilver constraints for the issuance proof:
//
//   Instance: t (commitment), ctx_iss (issuance context)
//   Witness:  nf (nullifier), r (opening), ctx_red (redemption context)
//   Constraint: t = commit(nf, ctx_iss, ctx_red, r)
//
// Arithmetization: Each round of Keccak-p[800, 12] has exactly one layer of ANDs, so the state
// after k rounds is a polynomial of degree 2^k in the input. Each round is a permutation, and its
// inverse also has one non-linear layer, the inverse of chi, which has degree 3; so the state k
// rounds before is a polynomial of degree 3^k in the output.
//
// We commit to some intermediate states as part of the witness, and meet in the middle between
// them: for consecutive committed states s_i and s_j, we check that f rounds forward from s_i equal
// b = j - i - f rounds backward from s_j, which has degree max(2^f, 3^b). (This is equivalent to
// s_j = R_{j-1}(...(R_i(s_i))), since the rounds are invertible.) The inverse of the linear layer
// L = pi o rho o theta is more expensive to compute than L, so rather than inverting the linear
// layer of round i + f, we apply it to the forward side, i.e., we meet just before chi of round
// i + f. The last segment ends in t, of which we only know 360 of 800 bits, so it can only go
// forward. With the default layout, all constraints have degree at most 9:
//
//   R_2(R_1(R_0(s0)))  = R_3^-1(R_4^-1(s5))   (degree max(2^3, 3^2) = 9)
//   R_6(R_5(s5))       = R_7^-1(R_8^-1(s9))   (degree max(2^2, 3^2) = 9)
//   R_11(R_10(R_9(s9)))[:45] = t              (degree 2^3 = 8)
//
// where R_i is round i of Keccak-p[800, 12] and s0 is the initial state. The layout is set by
// SEGMENTS and FINAL_ROUNDS below; e.g., `{{5, 3}}` and 4 commits to s8 only and has degree 32
// (which needs more CRT VOLE masks than faest-arch-opt currently supports). Each segment except the
// last adds 800 constraints; the last segment adds 360 constraints. The witness layout is as
// follows:
//
//     0 ..  16   r
//    16 ..  32   ctx_red
//    32 ..  56   nf
//    56 .. 156   s5, the state after 5 rounds
//   156 .. 256   s9, the state after 9 rounds
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
#include <utility>
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

// A segment of the permutation that ends in a committed state: `forward` rounds forward from the
// previous state (s0 or a committed state) meet `backward` rounds backward from the committed
// state.
struct Segment {
    size_t forward;
    size_t backward;
};

// The segments ending in the committed states, in order, followed by FINAL_ROUNDS rounds forward
// from the last committed state to t.
constexpr std::array SEGMENTS = {Segment{3, 2}, Segment{2, 2}};
constexpr size_t FINAL_ROUNDS = 3;

constexpr size_t NUM_COMMITTED_STATES = SEGMENTS.size();

constexpr size_t ipow(size_t base, size_t exp) { return exp == 0 ? 1 : base * ipow(base, exp - 1); }

// Index of the first round of segment k; SEGMENT_START[NUM_COMMITTED_STATES] is the first round of
// the final segment. Committed state k is the state after SEGMENT_START[k + 1] rounds.
constexpr std::array<size_t, NUM_COMMITTED_STATES + 1> SEGMENT_START = [] {
    std::array<size_t, NUM_COMMITTED_STATES + 1> out{};
    for (size_t k = 0; k < NUM_COMMITTED_STATES; ++k) {
        out[k + 1] = out[k] + SEGMENTS[k].forward + SEGMENTS[k].backward;
    }
    return out;
}();
static_assert(SEGMENT_START[NUM_COMMITTED_STATES] + FINAL_ROUNDS == KP800_ROUNDS);

// The degree of the constraints of a segment.
constexpr size_t segment_degree(const Segment& s) {
    return std::max(ipow(2, s.forward), ipow(3, s.backward));
}

constexpr size_t ISSUE_QS_DEGREE = [] {
    size_t deg = ipow(2, FINAL_ROUNDS);
    for (const Segment& s : SEGMENTS) {
        deg = std::max(deg, segment_degree(s));
    }
    return std::max(deg, size_t{2}); // bit constraints have degree 2
}();
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
        keccak_p800_rounds(state, SEGMENT_START[k], SEGMENT_START[k + 1] - SEGMENT_START[k]);
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

// Inverse of chi and iota of one Keccak round: degree d in, degree 3d out.
template <typename QS, size_t d>
std::vector<qs_val<QS, 3 * d>> qs_keccak_iota_chi_inverse(const std::vector<qs_val<QS, d>>& in,
                                                          size_t round) {
    const auto chi_inv = [](const qs_val<QS, d>& a, const qs_val<QS, d>& b, const qs_val<QS, d>& c,
                            const qs_val<QS, d>& dd, const qs_val<QS, d>& e) {
        // a ^ (~b & (c ^ (~d & e))) = a + (b + 1) * (c + (d + 1) * e)
        return qs_val<QS, 3 * d>(a) +
               (b + faest::poly1(1)) * (qs_val<QS, 2 * d>(c) + (dd + faest::poly1(1)) * e);
    };
    const auto add_one = [](const qs_val<QS, d>& x) { return x + faest::poly1(1); };
    return keccak_iota_chi_inverse(in, round, chi_inv, add_one);
}

// Inverse of the `num_rounds` rounds ending before `end_round`, i.e., of rounds
// end_round - num_rounds, ..., end_round - 1, except for the linear layer (theta, rho, pi) of the
// first of these rounds: degree d in, degree d * 3^num_rounds out. (The linear layer is cheap to
// compute forward but expensive to invert, so we instead apply it to the other side of the
// constraint.) Requires num_rounds >= 1.
template <typename QS, size_t num_rounds, size_t d = 1>
auto qs_keccak_rounds_inverse_partial(const std::vector<qs_val<QS, d>>& in, size_t end_round) {
    static_assert(num_rounds >= 1);
    auto out = qs_keccak_iota_chi_inverse<QS, d>(in, end_round - 1);
    if constexpr (num_rounds == 1) {
        return out;
    } else {
        return qs_keccak_rounds_inverse_partial<QS, num_rounds - 1, 3 * d>(
            keccak_theta_rho_pi_inverse(out), end_round - 1);
    }
}

// Lift a value to degree `deg` (which may equal its degree).
template <size_t deg, typename QS, size_t d> qs_val<QS, deg> qs_lift(const qs_val<QS, d>& x) {
    static_assert(d <= deg);
    return qs_val<QS, deg>(x);
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
        segment_constraints(qs, state, std::make_index_sequence<NUM_COMMITTED_STATES>());

        // Add output constraint: The last segment ends in the commitment.
        const auto out =
            qs_keccak_rounds<QS, FINAL_ROUNDS>(state, SEGMENT_START[NUM_COMMITTED_STATES]);
        for (size_t i = 0; i < 8 * uov::M; ++i) {
            qs->add_constraint(out[i] + poly1((x.t[i / 8] >> (i % 8)) & 1));
        }
    }

  private:
    // Segment k: The rounds forward from `state` meet the rounds backward from committed state k.
    // Afterwards, `state` is committed state k.
    template <size_t k, typename QS>
    static void segment_constraint(QS* qs, std::vector<qs_val<QS, 1>>& state) {
        constexpr Segment seg = SEGMENTS[k];
        constexpr size_t deg = segment_degree(seg);
        const size_t bit_offset = 8 * (WIT_OFF_STATES + k * KP800_STATE_BYTES);

        std::vector<qs_val<QS, 1>> next;
        next.reserve(KP800_STATE_BITS);
        for (size_t i = 0; i < KP800_STATE_BITS; ++i) {
            next.emplace_back(qs->get_witness_bit(bit_offset + i));
        }

        const auto fwd = qs_keccak_rounds<QS, seg.forward>(state, SEGMENT_START[k]);
        if constexpr (seg.backward == 0) {
            for (size_t i = 0; i < KP800_STATE_BITS; ++i) {
                qs->add_constraint(qs_lift<deg>(fwd[i]) + qs_lift<deg>(next[i]));
            }
        } else {
            // Meet after the linear layer of round SEGMENT_START[k] + seg.forward.
            const auto lin = keccak_theta_rho_pi(fwd);
            const auto bwd =
                qs_keccak_rounds_inverse_partial<QS, seg.backward>(next, SEGMENT_START[k + 1]);
            for (size_t i = 0; i < KP800_STATE_BITS; ++i) {
                qs->add_constraint(qs_lift<deg>(lin[i]) + qs_lift<deg>(bwd[i]));
            }
        }
        state = std::move(next);
    }

    template <typename QS, size_t... k>
    static void segment_constraints(QS* qs, std::vector<qs_val<QS, 1>>& state,
                                    std::index_sequence<k...>) {
        (segment_constraint<k>(qs, state), ...);
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
