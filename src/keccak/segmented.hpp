// QuickSilver arithmetization of Keccak-p[800, 12] with committed intermediate states.
//
// Each round of Keccak-p[800, 12] has exactly one layer of ANDs, so the state after k rounds is a
// polynomial of degree 2^k in the input. Each round is a permutation, and its inverse also has one
// non-linear layer, the inverse of chi, which has degree 3; so the state k rounds before is a
// polynomial of degree 3^k in the output.
//
// We commit to some intermediate states as part of the witness, and meet in the middle between
// them: for consecutive committed states s_i and s_j, we check that f rounds forward from s_i equal
// b = j - i - f rounds backward from s_j, which has degree max(2^f, 3^b). (This is equivalent to
// s_j = R_{j-1}(...(R_i(s_i))), since the rounds are invertible.) The inverse of the linear layer
// L = pi o rho o theta is more expensive to compute than L, so rather than inverting the linear
// layer of round i + f, we apply it to the forward side, i.e., we meet just before chi of round
// i + f. The last segment goes forward from the last committed state to the output, which the
// caller constrains as it sees fit (e.g., by comparing part of it to a public value or to a UOV
// public map evaluation). With the default layout, all constraints have degree at most 9:
//
//   R_2(R_1(R_0(s0)))  = R_3^-1(R_4^-1(s5))   (degree max(2^3, 3^2) = 9)
//   R_6(R_5(s5))       = R_7^-1(R_8^-1(s9))   (degree max(2^2, 3^2) = 9)
//   out = R_11(R_10(R_9(s9)))                 (degree 2^3 = 8)
//
// where R_i is round i of Keccak-p[800, 12] and s0 is the input. The layout is set by
// SEGMENTS and FINAL_ROUNDS below; e.g., `{{5, 3}}` and 4 commits to s8 only and has
// degree 32 (which needs more CRT VOLE masks than faest-arch-opt currently supports). Each segment
// except the last adds 800 constraints.
//
// A relation may evaluate the permutation any number of times, as long as each evaluation has its
// own committed intermediate states in the witness.

#ifndef VOLE_MOLE_KECCAK_SEGMENTED_HPP
#define VOLE_MOLE_KECCAK_SEGMENTED_HPP

#include "vole_mole/keccak.hpp"

#include "keccak/circuit.hpp"
#include "qs_bit.hpp"

#include "polynomials.hpp" // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <utility>
#include <vector>

namespace vole_mole::keccak::detail {

using vole_mole::detail::keccak_iota_chi_inverse;
using vole_mole::detail::keccak_round;
using vole_mole::detail::keccak_theta_rho_pi;
using vole_mole::detail::keccak_theta_rho_pi_inverse;
using vole_mole::detail::qs_bit;
using vole_mole::detail::qs_mul;
using vole_mole::detail::qs_to_gfsecpar;

// A segment of the permutation that ends in a committed state: `forward` rounds forward from the
// previous state (the input or a committed state) meet `backward` rounds backward from the
// committed state.
struct Segment {
    size_t forward;
    size_t backward;
};

// The segments ending in the committed states, in order, followed by FINAL_ROUNDS rounds
// forward from the last committed state to the output.
constexpr std::array SEGMENTS = {Segment{3, 2}, Segment{2, 2}};
constexpr size_t FINAL_ROUNDS = 3;

constexpr size_t NUM_COMMITTED_STATES = SEGMENTS.size();

constexpr size_t ipow(size_t base, size_t exp) { return exp == 0 ? 1 : base * ipow(base, exp - 1); }

// Index of the first round of segment k; SEGMENT_START[NUM_COMMITTED_STATES] is the
// first round of the final segment. Committed state k is the state after SEGMENT_START[k + 1]
// rounds.
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

// The degree of the output of the permutation.
constexpr size_t OUTPUT_DEGREE = ipow(2, FINAL_ROUNDS);

// The maximum degree of the segment constraints and the output, and hence the minimum QuickSilver
// degree of a relation that evaluates the permutation.
constexpr size_t QS_DEGREE = [] {
    size_t deg = OUTPUT_DEGREE;
    for (const Segment& s : SEGMENTS) {
        deg = std::max(deg, segment_degree(s));
    }
    return deg;
}();

// Size of the intermediate states committed to in the witness for each evaluation.
constexpr size_t COMMITTED_STATES_BYTES = NUM_COMMITTED_STATES * KP800_STATE_BYTES;

// Number of constraints added by each call to `qs_keccak`.
constexpr size_t NUM_SEGMENT_CONSTRAINTS = NUM_COMMITTED_STATES * KP800_STATE_BITS;

// Compute the intermediate states to commit to in the witness, starting from input `state`.
inline void encode_committed_states(std::span<uint8_t, COMMITTED_STATES_BYTES> out,
                                    Kp800State state) {
    for (size_t k = 0; k < NUM_COMMITTED_STATES; ++k) {
        keccak_p800_rounds(state, SEGMENT_START[k], SEGMENT_START[k + 1] - SEGMENT_START[k]);
        std::ranges::copy(state, out.begin() + k * KP800_STATE_BYTES);
    }
}

// A QuickSilver-committed value in GF(2^128) of degree `deg`.
template <typename QS, size_t deg> using qs_val = faest::quicksilver_gfsecpar<QS, deg>;

// The committed bits of a Keccak-p[800] state, of degree `deg`. (Keccak state bits are GF(2)
// values, so we represent them as qs_bit rather than qs_val.)
template <typename QS, size_t deg = 1> using QsState = std::vector<qs_bit<QS, deg>>;

// One Keccak round: degree d in, degree 2d out. Only the first `num_out_bits` output bits are
// computed.
template <typename QS, size_t d>
QsState<QS, 2 * d> qs_keccak_round(const QsState<QS, d>& in, size_t round,
                                   size_t num_out_bits = KP800_STATE_BITS) {
    const auto chi = [](const qs_bit<QS, d>& a, const qs_bit<QS, d>& b, const qs_bit<QS, d>& c) {
        // a ^ (~b & c) = a + (b + 1) * c
        return qs_bit<QS, 2 * d>(a) + qs_mul<QS, d, d>(b + faest::poly1(1), c);
    };
    const auto add_one = [](const qs_bit<QS, 2 * d>& x) { return x + faest::poly1(1); };
    return keccak_round(in, round, chi, add_one, num_out_bits);
}

// `num_rounds` rounds starting at `first_round`: degree d in, degree d * 2^num_rounds out. Only the
// first `num_out_bits` bits of the output are computed (unless num_rounds = 0).
template <typename QS, size_t num_rounds, size_t d = 1>
auto qs_keccak_rounds(const QsState<QS, d>& in, size_t first_round,
                      size_t num_out_bits = KP800_STATE_BITS) {
    if constexpr (num_rounds == 0) {
        return in;
    } else if constexpr (num_rounds == 1) {
        return qs_keccak_round<QS, d>(in, first_round, num_out_bits);
    } else {
        return qs_keccak_rounds<QS, num_rounds - 1, 2 * d>(qs_keccak_round<QS, d>(in, first_round),
                                                           first_round + 1, num_out_bits);
    }
}

// Inverse of chi and iota of one Keccak round: degree d in, degree 3d out.
template <typename QS, size_t d>
QsState<QS, 3 * d> qs_keccak_iota_chi_inverse(const QsState<QS, d>& in, size_t round) {
    const auto chi_inv = [](const qs_bit<QS, d>& a, const qs_bit<QS, d>& b, const qs_bit<QS, d>& c,
                            const qs_bit<QS, d>& dd, const qs_bit<QS, d>& e) {
        // a ^ (~b & (c ^ (~d & e))) = a + (b + 1) * (c + (d + 1) * e)
        return qs_bit<QS, 3 * d>(a) +
               qs_mul<QS, d, 2 * d>(b + faest::poly1(1),
                                    qs_bit<QS, 2 * d>(c) +
                                        qs_mul<QS, d, d>(dd + faest::poly1(1), e));
    };
    const auto add_one = [](const qs_bit<QS, d>& x) { return x + faest::poly1(1); };
    return keccak_iota_chi_inverse(in, round, chi_inv, add_one);
}

// Inverse of the `num_rounds` rounds ending before `end_round`, i.e., of rounds
// end_round - num_rounds, ..., end_round - 1, except for the linear layer (theta, rho, pi) of the
// first of these rounds: degree d in, degree d * 3^num_rounds out. (The linear layer is cheap to
// compute forward but expensive to invert, so we instead apply it to the other side of the
// constraint.) Requires num_rounds >= 1.
template <typename QS, size_t num_rounds, size_t d = 1>
auto qs_keccak_rounds_inverse_partial(const QsState<QS, d>& in, size_t end_round) {
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
template <size_t deg, typename QS, size_t d> qs_bit<QS, deg> qs_lift(const qs_bit<QS, d>& x) {
    static_assert(d <= deg);
    return qs_bit<QS, deg>(x);
}

// Map of the index of each byte of a Keccak-p[800] input to its index in the witness. Index is -1
// if the byte is public.
using InputMap = std::array<int, KP800_STATE_BYTES>;

// Every entry of `map` is either -1 (public) or the index of a witness byte in
// [wit_begin, wit_end), and each of those witness bytes is used exactly once.
constexpr bool input_map_is_valid(const InputMap& map, size_t wit_begin, size_t wit_end) {
    std::array<int, KP800_STATE_BYTES> uses{};
    if (wit_end < wit_begin || wit_end - wit_begin > uses.size()) {
        return false;
    }
    for (const int w : map) {
        if (w == -1) {
            continue;
        }
        if (w < static_cast<int>(wit_begin) || static_cast<size_t>(w) >= wit_end) {
            return false;
        }
        ++uses[static_cast<size_t>(w) - wit_begin];
    }
    return std::all_of(uses.begin(),
                       uses.begin() + static_cast<std::ptrdiff_t>(wit_end - wit_begin),
                       [](int n) { return n == 1; });
}

// Build a committed input state consisting of the bytes of `public_state` and the witness bytes
// given by `map`.
template <typename QS>
QsState<QS> qs_input(const QS* qs, const Kp800State& public_state, const InputMap& map) {
    QsState<QS> state;
    state.reserve(KP800_STATE_BITS);
    for (size_t i = 0; i < KP800_STATE_BITS; ++i) {
        const int witness_byte = map[i / 8];
        if (witness_byte >= 0) {
            state.emplace_back(qs->get_witness_bit(8 * static_cast<size_t>(witness_byte) + i % 8));
        } else {
            // Public bytes are treated as constants.
            state.emplace_back(faest::poly1((public_state[i / 8] >> (i % 8)) & 1), qs);
        }
    }
    return state;
}

// Segment k: The rounds forward from `state` meet the rounds backward from committed state k.
// Afterwards, `state` is committed state k.
template <size_t k, typename QS>
void segment_constraint(QS* qs, QsState<QS>& state, size_t wit_off_states) {
    constexpr Segment seg = SEGMENTS[k];
    constexpr size_t deg = segment_degree(seg);
    const size_t bit_offset = 8 * (wit_off_states + k * KP800_STATE_BYTES);

    QsState<QS> next;
    next.reserve(KP800_STATE_BITS);
    for (size_t i = 0; i < KP800_STATE_BITS; ++i) {
        next.emplace_back(qs->get_witness_bit(bit_offset + i));
    }

    const auto fwd = qs_keccak_rounds<QS, seg.forward>(state, SEGMENT_START[k]);
    if constexpr (seg.backward == 0) {
        for (size_t i = 0; i < KP800_STATE_BITS; ++i) {
            qs->add_constraint(qs_to_gfsecpar(qs_lift<deg>(fwd[i]) + qs_lift<deg>(next[i])));
        }
    } else {
        // Meet after the linear layer of round SEGMENT_START[k] + seg.forward.
        const auto lin = keccak_theta_rho_pi(fwd);
        const auto bwd =
            qs_keccak_rounds_inverse_partial<QS, seg.backward>(next, SEGMENT_START[k + 1]);
        for (size_t i = 0; i < KP800_STATE_BITS; ++i) {
            qs->add_constraint(qs_to_gfsecpar(qs_lift<deg>(lin[i]) + qs_lift<deg>(bwd[i])));
        }
    }
    state = std::move(next);
}

template <typename QS, size_t... k>
void segment_constraints(QS* qs, QsState<QS>& state, size_t wit_off_states,
                         std::index_sequence<k...>) {
    (segment_constraint<k>(qs, state, wit_off_states), ...);
}

// Evaluate Keccak-p[800, 12] on the committed input `state`. The intermediate states are the
// witness bytes starting at `wit_off_states` (see encode_committed_states).
//
// Adds NUM_SEGMENT_CONSTRAINTS constraints (one per bit of each intermediate state) and
// returns the first `num_out_bits` bits of the output, of degree OUTPUT_DEGREE. (Only these are
// computed in the last round.)
template <typename QS>
QsState<QS, OUTPUT_DEGREE> qs_keccak(QS* qs, QsState<QS> state, size_t wit_off_states,
                                     size_t num_out_bits = KP800_STATE_BITS) {
    static_assert(QS::max_degree >= QS_DEGREE);
    static_assert(FINAL_ROUNDS >= 1);
    segment_constraints(qs, state, wit_off_states,
                        std::make_index_sequence<NUM_COMMITTED_STATES>());
    return qs_keccak_rounds<QS, FINAL_ROUNDS>(state, SEGMENT_START[NUM_COMMITTED_STATES],
                                              num_out_bits);
}

// Combine bits 8k .. 8k + 8 of a committed state into an element of the GF(256) subfield of
// GF(2^128), with bit j of the byte as the coefficient of x^j. This is the same embedding as
// `load_witness_8_bits_and_combine` and uov::detail::embed, so the result can be compared with a
// UOV public map evaluation.
template <typename QS, size_t deg>
qs_val<QS, deg> qs_byte(const QsState<QS, deg>& state, size_t k) {
    qs_val<QS, deg> out = qs_to_gfsecpar(state[8 * k]);
    for (size_t j = 1; j < 8; ++j) {
        out += qs_to_gfsecpar(state[8 * k + j]) *
               faest::poly_secpar<QS::secpar_v>::from_8_byte(static_cast<uint8_t>(1u << j));
    }
    return out;
}

} // namespace vole_mole::keccak::detail

#endif
