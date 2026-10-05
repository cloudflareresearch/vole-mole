// The input layouts of the Ratatouille commitment and tag.

#ifndef VOLE_MOLE_RATATOUILLE_COMMIT_HPP
#define VOLE_MOLE_RATATOUILLE_COMMIT_HPP

#include "vole_mole/keccak.hpp"
#include "vole_mole/ratatouille.hpp"

#include "dst.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

namespace vole_mole::ratatouille::detail {

using namespace vole_mole::detail;

using CreditBytes = std::array<uint8_t, CREDIT_BYTES>;

// <v>_L, the little-endian encoding of a credit value.
constexpr CreditBytes encode_credits(Credits v) {
    CreditBytes out{};
    for (size_t i = 0; i < CREDIT_BYTES; ++i) {
        out[i] = static_cast<uint8_t>(v >> (8 * i));
    }
    return out;
}

constexpr Credits decode_credits(std::span<const uint8_t, CREDIT_BYTES> bytes) {
    Credits v = 0;
    for (size_t i = 0; i < CREDIT_BYTES; ++i) {
        v |= Credits{bytes[i]} << (8 * i);
    }
    return v;
}

// The witness bit index of bit i (counting from the least significant bit) of a credit value whose
// encoding starts at witness byte `byte_off`.
constexpr size_t credit_bit(size_t byte_off, size_t i) { return 8 * byte_off + i; }

// Commitment layout:
//
//   "rata" || VERSION || "c0" || r || 0^(25 - r_len) ||
//   ctx_iss || <t>_L || nf || 0^(68 - nf_len - ctx_len - L)
constexpr size_t COM_OFF_R = DST_BYTES;
constexpr size_t COM_OFF_CTX = COM_OFF_R + 25;
constexpr size_t COM_OFF_T = COM_OFF_CTX + CTX_BYTES;
constexpr size_t COM_OFF_NF = COM_OFF_T + CREDIT_BYTES;
static_assert(R_BYTES <= 25);
static_assert(COM_OFF_NF + NF_BYTES + (68 - NF_BYTES - CTX_BYTES - CREDIT_BYTES) ==
              KP800_STATE_BYTES);

inline Kp800State encode_com_state(const Nullifier& nf, const Context& ctx_iss, Credits t,
                                   const Opening& r) {
    Kp800State state{};
    std::ranges::copy(RATATOUILLE_COM_DST, state.begin());
    std::ranges::copy(r, state.begin() + COM_OFF_R);
    std::ranges::copy(ctx_iss, state.begin() + COM_OFF_CTX);
    std::ranges::copy(encode_credits(t), state.begin() + COM_OFF_T);
    std::ranges::copy(nf, state.begin() + COM_OFF_NF);
    return state;
}

// Tag layout:
//
//   "rata" || VERSION || "t0" || 0^25 || c || <x>_L || 0^(36 - L)
constexpr size_t TAG_OFF_C = DST_BYTES + 25;
constexpr size_t TAG_OFF_X = TAG_OFF_C + COMMITMENT_BYTES;
static_assert(TAG_OFF_X + CREDIT_BYTES + (36 - CREDIT_BYTES) == KP800_STATE_BYTES);
static_assert(uov::M <= KP800_STATE_BYTES);

inline Kp800State encode_tag_state(const Commitment& c, Credits x) {
    Kp800State state{};
    std::ranges::copy(RATATOUILLE_TAG_DST, state.begin());
    std::ranges::copy(c, state.begin() + TAG_OFF_C);
    std::ranges::copy(encode_credits(x), state.begin() + TAG_OFF_X);
    return state;
}

} // namespace vole_mole::ratatouille::detail

#endif
