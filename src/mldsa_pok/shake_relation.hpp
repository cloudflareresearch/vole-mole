// EXPERIMENTAL: a VOLEitH proof of knowledge of a SHAKE256 preimage with a public prefix, used to
// measure the cost of the hash computations in a proof of knowledge of an ML-DSA signature.
//
//   Instance: a public prefix P and an output y
//   Witness:  a secret message S of fixed length
//   Statement: y = SHAKE256(P || S, |y|)
//
// For ML-DSA-44, c-tilde = H(mu || w1Encode(w1), 32) has P = mu (64 bytes) and |S| = 768 bytes.
//
// The sponge absorbs P || S || pad in blocks of RATE bytes; the input of each permutation is the
// output of the previous one (a committed state) plus the next block (public or witness bits). The
// permutation is arithmetized as in keccak/segmented.hpp, with its output committed (so that it
// has degree 1 as the input of the next permutation).

#ifndef VOLE_MOLE_MLDSA_POK_SHAKE_RELATION_HPP
#define VOLE_MOLE_MLDSA_POK_SHAKE_RELATION_HPP

#include "vole_mole/keccak.hpp"

#include "keccak/segmented.hpp"
#include "keccak/tables.hpp"
#include "qs_bit.hpp"

#include "hash.hpp"        // from faest-arch-opt
#include "parameters.hpp"  // from faest-arch-opt
#include "polynomials.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

namespace vole_mole::mldsa_pok::detail {

using keccak::detail::Segment;
using keccak::detail::SegmentedKeccak;
using vole_mole::detail::Kf1600;

constexpr size_t SHAKE256_RATE = 136;

// Two layouts of Keccak-f[1600]: degree 9 with 5 committed states, or degree 16 with 4.
using Kf1600Deg9 = keccak::detail::SegmentedKf1600;
using Kf1600Deg16 =
    SegmentedKeccak<Kf1600, std::array{Segment{4, 2}, Segment{4, 2}, Segment{4, 2}, Segment{4, 2}},
                    0>;
static_assert(Kf1600Deg9::QS_DEGREE == 9 && Kf1600Deg16::QS_DEGREE == 16);

template <typename Seg, size_t PREFIX_BYTES_, size_t SECRET_BYTES_, size_t OUT_BYTES_>
struct ShakeShape {
    using Segmented = Seg;
    static constexpr size_t PREFIX_BYTES = PREFIX_BYTES_;
    static constexpr size_t SECRET_BYTES = SECRET_BYTES_;
    static constexpr size_t OUT_BYTES = OUT_BYTES_;
    static_assert(OUT_BYTES <= SHAKE256_RATE, "single squeeze block");

    // P || S || 0x1f || 0^* || 0x80, a whole number of blocks.
    static constexpr size_t NUM_BLOCKS = (PREFIX_BYTES + SECRET_BYTES) / SHAKE256_RATE + 1;
    static constexpr size_t PADDED_BYTES = NUM_BLOCKS * SHAKE256_RATE;

    // Witness layout: S, then the committed states of each permutation.
    static constexpr size_t WIT_OFF_STATES = SECRET_BYTES;
    static constexpr size_t WITNESS_BYTES =
        WIT_OFF_STATES + NUM_BLOCKS * Seg::COMMITTED_STATES_BYTES;
    static constexpr size_t WITNESS_BITS = 8 * WITNESS_BYTES;
    static constexpr size_t QS_DEGREE = Seg::QS_DEGREE;

    static constexpr size_t NUM_CONSTRAINTS = WITNESS_BITS                                // bits
                                              + NUM_BLOCKS * Seg::NUM_SEGMENT_CONSTRAINTS // perms
                                              + 8 * OUT_BYTES;                            // output

    // Byte i of the padded input is public (>= 0, its value) or byte -1 - v of the witness.
    static int padded_byte(std::span<const uint8_t, PREFIX_BYTES> prefix, size_t i) {
        if (i < PREFIX_BYTES) {
            return prefix[i];
        }
        if (i < PREFIX_BYTES + SECRET_BYTES) {
            return -1 - static_cast<int>(i - PREFIX_BYTES);
        }
        uint8_t v = 0;
        if (i == PREFIX_BYTES + SECRET_BYTES) {
            v |= 0x1f;
        }
        if (i == PADDED_BYTES - 1) {
            v |= 0x80;
        }
        return v;
    }

    // The witness for secret message `s`, and the output.
    static std::vector<uint8_t> encode_witness(std::span<const uint8_t, PREFIX_BYTES> prefix,
                                               std::span<const uint8_t, SECRET_BYTES> s,
                                               std::span<uint8_t, OUT_BYTES> out) {
        std::vector<uint8_t> w(WITNESS_BYTES);
        std::ranges::copy(s, w.begin());
        Kf1600State state{};
        for (size_t b = 0; b < NUM_BLOCKS; ++b) {
            for (size_t i = 0; i < SHAKE256_RATE; ++i) {
                const int v = padded_byte(prefix, b * SHAKE256_RATE + i);
                state[i] ^= v >= 0 ? static_cast<uint8_t>(v) : s[static_cast<size_t>(-1 - v)];
            }
            const auto states = std::span(w)
                                    .subspan(WIT_OFF_STATES + b * Seg::COMMITTED_STATES_BYTES)
                                    .template first<Seg::COMMITTED_STATES_BYTES>();
            Seg::encode_committed_states(states, state);
            std::ranges::copy(states.template last<KF1600_STATE_BYTES>(), state.begin());
        }
        std::copy_n(state.begin(), OUT_BYTES, out.begin());
        return w;
    }

    // The sponge on committed bits: returns the state after the last permutation (of degree
    // Seg::OUTPUT_DEGREE). The witness is at bit offset 0. Adds NUM_SPONGE_CONSTRAINTS
    // constraints (no bit constraints, and no constraints on the output).
    static constexpr size_t NUM_SPONGE_CONSTRAINTS = NUM_BLOCKS * Seg::NUM_SEGMENT_CONSTRAINTS;
    template <typename QS>
    static auto qs_sponge(QS* qs, std::span<const uint8_t, PREFIX_BYTES> prefix) {
        using Bit = vole_mole::detail::qs_bit<QS, 1>;
        using faest::poly1;
        static_assert(Seg::OUTPUT_DEGREE == 1, "the output feeds the next permutation");

        // The state before absorbing the first block is zero.
        keccak::detail::QsState<QS> state(KF1600_STATE_BITS, Bit(poly1(0), qs));
        for (size_t b = 0; b < NUM_BLOCKS; ++b) {
            for (size_t i = 0; i < 8 * SHAKE256_RATE; ++i) {
                const int v = padded_byte(prefix, b * SHAKE256_RATE + i / 8);
                if (v >= 0) {
                    state[i] = state[i] + poly1((v >> (i % 8)) & 1);
                } else {
                    state[i] =
                        state[i] + qs->get_witness_bit(8 * static_cast<size_t>(-1 - v) + i % 8);
                }
            }
            state = Seg::qs_keccak(qs, std::move(state),
                                   WIT_OFF_STATES + b * Seg::COMMITTED_STATES_BYTES);
        }
        return state;
    }

    template <typename QS>
    static void constraints(QS* qs, std::span<const uint8_t, PREFIX_BYTES> prefix,
                            std::span<const uint8_t, OUT_BYTES> y) {
        using faest::poly1;
        using vole_mole::detail::qs_add_bit_constraint;
        using vole_mole::detail::qs_to_gfsecpar;

        for (size_t i = 0; i < WITNESS_BITS; ++i) {
            qs_add_bit_constraint(qs, qs->get_witness_bit(i));
        }
        const auto state = qs_sponge(qs, prefix);
        for (size_t i = 0; i < 8 * OUT_BYTES; ++i) {
            qs->add_constraint(qs_to_gfsecpar(state[i] + poly1((y[i / 8] >> (i % 8)) & 1)));
        }
    }
};

// ML-DSA-44's c-tilde = H(mu || w1Encode(w1), 32).
using CtildeDeg9 = ShakeShape<Kf1600Deg9, 64, 768, 32>;
using CtildeDeg16 = ShakeShape<Kf1600Deg16, 64, 768, 32>;

constexpr faest::owf OWF_CTILDE_DEG9 =
    static_cast<faest::owf>((0x6du << 8) | 0b10'0000 /* owf_flag_witness_bits_check */);
constexpr faest::owf OWF_CTILDE_DEG16 =
    static_cast<faest::owf>((0x6eu << 8) | 0b10'0000 /* owf_flag_witness_bits_check */);

} // namespace vole_mole::mldsa_pok::detail

template <>
struct faest::OWF_CONSTANTS<faest::secpar::s128, vole_mole::mldsa_pok::detail::OWF_CTILDE_DEG9> {
    constexpr static size_t WITNESS_BITS = vole_mole::mldsa_pok::detail::CtildeDeg9::WITNESS_BITS;
    constexpr static size_t QS_DEGREE = vole_mole::mldsa_pok::detail::CtildeDeg9::QS_DEGREE;
    constexpr static bool valid = true;
};
template <>
struct faest::OWF_CONSTANTS<faest::secpar::s128, vole_mole::mldsa_pok::detail::OWF_CTILDE_DEG16> {
    constexpr static size_t WITNESS_BITS = vole_mole::mldsa_pok::detail::CtildeDeg16::WITNESS_BITS;
    constexpr static size_t QS_DEGREE = vole_mole::mldsa_pok::detail::CtildeDeg16::QS_DEGREE;
    constexpr static bool valid = true;
};

namespace vole_mole::mldsa_pok::detail {

// A test-only DST: these relations are for measurement.
inline constexpr std::array<uint8_t, 8> SHAKE_RELATION_DST = {'m', 'd', 's', 'a', 0, 'x', 'h', '0'};

// FAEST-EM-128f (as in PomFRIT etc.), or FAEST-128s-style parameters with TAU = 11.
template <faest::owf OWF>
using Params128f = faest::parameter_set<faest::secpar::s128, /* TAU */ 17, OWF, faest::prg::aes_ctr,
                                        faest::prg::aes_ctr, faest::leaf_hash::aes_ctr,
                                        /* W_GRIND */ 8, {faest::bavc::one_tree, /* T_OPEN */ 105},
                                        /* CRT_VOLE_MASKS */ true, /* HASH_INPUTS_V3 */ true>;
template <faest::owf OWF>
using Params128s = faest::parameter_set<faest::secpar::s128, /* TAU */ 11, OWF, faest::prg::aes_ctr,
                                        faest::prg::aes_ctr, faest::leaf_hash::aes_ctr,
                                        /* W_GRIND */ 7, {faest::bavc::one_tree, /* T_OPEN */ 103},
                                        /* CRT_VOLE_MASKS */ true, /* HASH_INPUTS_V3 */ true>;

template <typename Shape, typename Params> struct ShakeRelation {
    using params = Params;
    using shape = Shape;

    struct instance {
        std::array<uint8_t, Shape::PREFIX_BYTES> prefix;
        std::array<uint8_t, Shape::OUT_BYTES> y;
    };

    static constexpr size_t NUM_CONSTRAINTS = Shape::NUM_CONSTRAINTS;
    static constexpr size_t WITNESS_PREFIX_BYTES = Shape::WITNESS_BYTES;
    static constexpr std::span<const uint8_t> DST = SHAKE_RELATION_DST;

    static void hash_instance(faest::hash_state& h, const instance& x) {
        h.update(x.prefix);
        h.update(x.y);
    }

    template <typename QS>
    static void constraints(QS* qs, const instance& x,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES>) {
        static_assert(QS::max_degree == Shape::QS_DEGREE);
        Shape::constraints(qs, std::span(x.prefix), std::span(x.y));
    }
};

} // namespace vole_mole::mldsa_pok::detail

#endif
