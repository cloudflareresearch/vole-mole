// Issuer reporting: the report, its expansion into the Aggregator's share and the report tag, and
// the QuickSilver constraints that tie them to the selector of the redemption proof.
//
// The report k is a 16-byte secret. Its expansion is the first REPORT_OUT_BYTES bytes of
//
//   out_0 || out_1 || out_2, where out_j = first 68 bytes of Keccak-p[800, 12](DST || j || k ||
//   0^76)
//
// and DST = IHAT_REPORT_DST. Each block keeps 32 bytes (256 bits) of the output secret, so that
// the output doesn't reveal k, and the blocks are independent evaluations of the permutation, so no
// state carries over between them. The first HISTOGRAM_SHARE_BYTES bytes are the Aggregator's share
// B, as MAX_ANCHORS little-endian 16-bit words, and the last REPORT_TAG_BYTES bytes are the tag t.
//
// The Moderator's share is A = V - B mod 2^16, where V is the one-hot vector of the selector b of
// the redemption proof. A is public, so B = V - A is an affine function of b: for each u,
// B[u] = c0 if b[u] = 0 and c1 = c0 + 1 if b[u] = 1, where c0 = -A[u] mod 2^16. Hence bit w of B[u]
// is c0_w + b[u] * (c0_w + c1_w), and each output bit of the expansion is constrained to equal
// either such an affine function of b or a bit of the public tag. This adds no multiplications
// beyond those of the permutation itself.
//
// Binding: the tag is 256 bits, so finding two reports with the same tag but different shares
// takes about 2^128 work. Hiding: without k, A and t are pseudorandom.

#ifndef VOLE_MOLE_IHAT_REPORT_HPP
#define VOLE_MOLE_IHAT_REPORT_HPP

#include "vole_mole/ihat.hpp"
#include "vole_mole/keccak.hpp"

#include "ct.hpp"
#include "dst.hpp"
#include "ihat/circuit.hpp"
#include "keccak/segmented.hpp"

#include "polynomials.hpp" // from faest-arch-opt

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

namespace vole_mole::ihat::detail {

using namespace vole_mole::detail;

// Report expansion layout.
constexpr size_t REPORT_OUT_BYTES = HISTOGRAM_SHARE_BYTES + REPORT_TAG_BYTES;
constexpr size_t REPORT_CAPACITY_BYTES = 32; // bytes of each block's output that stay secret
constexpr size_t REPORT_BLOCK_OUT_BYTES = KP800_STATE_BYTES - REPORT_CAPACITY_BYTES;
constexpr size_t REPORT_BLOCKS =
    (REPORT_OUT_BYTES + REPORT_BLOCK_OUT_BYTES - 1) / REPORT_BLOCK_OUT_BYTES;
static_assert(REPORT_BLOCKS == 3);

// Number of output bytes of block j.
constexpr size_t report_block_out_bytes(size_t j) {
    return std::min(REPORT_BLOCK_OUT_BYTES, REPORT_OUT_BYTES - j * REPORT_BLOCK_OUT_BYTES);
}

// Input layout of each block: DST || j || k || 0^76.
constexpr size_t REPORT_OFF_INDEX = DST_BYTES;
constexpr size_t REPORT_OFF_K = REPORT_OFF_INDEX + 1;
static_assert(REPORT_OFF_K + REPORT_BYTES <= KP800_STATE_BYTES);
static_assert(REPORT_BLOCKS <= UINT8_MAX);

inline Kp800State encode_report_state(const Report& k, size_t j) {
    Kp800State state{};
    std::ranges::copy(IHAT_REPORT_DST, state.begin());
    state[REPORT_OFF_INDEX] = static_cast<uint8_t>(j);
    std::ranges::copy(k, state.begin() + REPORT_OFF_K);
    return state;
}

using ReportOutput = std::array<uint8_t, REPORT_OUT_BYTES>;

// Expand the report into B || t.
inline ReportOutput expand_report(const Report& k) {
    ReportOutput out;
    for (size_t j = 0; j < REPORT_BLOCKS; ++j) {
        const Kp800State block = keccak_p800(encode_report_state(k, j));
        std::copy_n(block.begin(), report_block_out_bytes(j),
                    out.begin() + j * REPORT_BLOCK_OUT_BYTES);
    }
    return out;
}

using EncodedShare = std::array<uint8_t, HISTOGRAM_SHARE_BYTES>;

inline EncodedShare encode_share(const HistogramShare& share) {
    EncodedShare out;
    for (size_t u = 0; u < MAX_ANCHORS; ++u) {
        out[2 * u] = static_cast<uint8_t>(share[u]);
        out[2 * u + 1] = static_cast<uint8_t>(share[u] >> 8);
    }
    return out;
}

inline HistogramShare decode_share(std::span<const uint8_t, HISTOGRAM_SHARE_BYTES> bytes) {
    HistogramShare share;
    for (size_t u = 0; u < MAX_ANCHORS; ++u) {
        share[u] = static_cast<uint16_t>(bytes[2 * u] | (bytes[2 * u + 1] << 8));
    }
    return share;
}

inline OpenedReport open_report_output(const ReportOutput& out) {
    OpenedReport opened;
    opened.share = decode_share(std::span(out).first<HISTOGRAM_SHARE_BYTES>());
    std::ranges::copy(std::span(out).last<REPORT_TAG_BYTES>(), opened.tag.begin());
    return opened;
}

// The Moderator's share A = V - B mod 2^16 for the Anchor at index i, in constant time so that this
// doesn't leak the index.
inline HistogramShare moderator_share(const HistogramShare& b_share, size_t i) {
    HistogramShare a_share;
    for (size_t u = 0; u < MAX_ANCHORS; ++u) {
        const auto v = static_cast<uint16_t>(ct_eq_mask(u, i) & 1);
        a_share[u] = static_cast<uint16_t>(v - b_share[u]);
    }
    return a_share;
}

// Size of the intermediate states of all blocks committed to in the witness.
constexpr size_t REPORT_COMMITTED_STATES_BYTES =
    REPORT_BLOCKS * keccak::detail::COMMITTED_STATES_BYTES;

// Compute the intermediate states of all blocks to commit to in the witness.
inline void encode_report_states(std::span<uint8_t, REPORT_COMMITTED_STATES_BYTES> out,
                                 const Report& k) {
    using keccak::detail::COMMITTED_STATES_BYTES;
    for (size_t j = 0; j < REPORT_BLOCKS; ++j) {
        keccak::detail::encode_committed_states(
            out.subspan(j * COMMITTED_STATES_BYTES).first<COMMITTED_STATES_BYTES>(),
            encode_report_state(k, j));
    }
}

// Map of the index of each byte of the input of each block to its index in the witness, where k
// starts at witness byte `wit_off_k`. (The map is the same for every block.)
constexpr keccak::detail::InputMap report_input_map(size_t wit_off_k) {
    keccak::detail::InputMap map;
    map.fill(-1);
    for (size_t i = 0; i < REPORT_BYTES; ++i) {
        map[REPORT_OFF_K + i] = static_cast<int>(wit_off_k + i);
    }
    return map;
}

// Number of constraints added by qs_add_report_constraints.
constexpr size_t REPORT_NUM_CONSTRAINTS =
    REPORT_BLOCKS * keccak::detail::NUM_SEGMENT_CONSTRAINTS // segments end in a committed state
    + 8 * REPORT_OUT_BYTES;                                 // the expansion is V - A || t

// Add report constraints: The expansion of the report k, the REPORT_BYTES witness bytes starting at
// `wit_off_k`, is (V - A) || t, where V is the one-hot vector of the selector b, A is the
// Moderator's share, and t is the report tag. The intermediate states of the blocks are the witness
// bytes starting at `wit_off_states` (see encode_report_states).
template <typename QS>
void qs_add_report_constraints(QS* qs, const Selector<QS>& b, const HistogramShare& a_share,
                               const ReportTag& tag, size_t wit_off_k, size_t wit_off_states) {
    using faest::poly1;
    using keccak::detail::OUTPUT_DEGREE;
    using keccak::detail::qs_lift;

    const keccak::detail::InputMap map = report_input_map(wit_off_k);
    for (size_t j = 0; j < REPORT_BLOCKS; ++j) {
        const size_t out_bytes = report_block_out_bytes(j);
        const auto out = keccak::detail::qs_keccak(
            qs, keccak::detail::qs_input(qs, encode_report_state({}, j), map),
            wit_off_states + j * keccak::detail::COMMITTED_STATES_BYTES, 8 * out_bytes);

        for (size_t i = 0; i < 8 * out_bytes; ++i) {
            const size_t p = j * REPORT_BLOCK_OUT_BYTES + i / 8; // byte of the expansion
            if (p < HISTOGRAM_SHARE_BYTES) {
                // Bit w of B[u] is c0_w + b[u] * (c0_w + c1_w).
                const size_t u = p / 2;
                const size_t w = 8 * (p % 2) + i % 8;
                const auto c0 = static_cast<uint16_t>(0 - a_share[u]);
                const auto c1 = static_cast<uint16_t>(1 - a_share[u]);
                auto expected = out[i] + poly1((c0 >> w) & 1);
                if (((c0 ^ c1) >> w) & 1) {
                    expected += qs_lift<OUTPUT_DEGREE>(b[u]);
                }
                qs->add_constraint(qs_to_gfsecpar(expected));
            } else {
                const size_t t = p - HISTOGRAM_SHARE_BYTES; // byte of the tag
                qs->add_constraint(qs_to_gfsecpar(out[i] + poly1((tag[t] >> (i % 8)) & 1)));
            }
        }
    }
}

} // namespace vole_mole::ihat::detail

#endif
