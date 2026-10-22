// The VOLE-IHAT commitment and its input layout.

#ifndef VOLE_MOLE_IHAT_COMMIT_HPP
#define VOLE_MOLE_IHAT_COMMIT_HPP

#include "vole_mole/ihat.hpp"
#include "vole_mole/keccak.hpp"
#include "vole_mole/uov.hpp"

#include "dst.hpp"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>

namespace vole_mole::ihat::detail {

using namespace vole_mole::detail;

constexpr size_t R_BYTES = 16; // commitment opening length
using Opening = std::array<uint8_t, R_BYTES>;

// The commitment is the UOV target signed by the Anchor.
using Commitment = uov::Target;

// Compute a commitment to a nullifier, issuance context, and redemption context with the given
// opening.
Commitment commit(const Nullifier& nf, const Context& ctx_iss, const Context& ctx_red,
                  const Opening& r);

// Commitment layout.
constexpr size_t COM_OFF_R = DST_BYTES;
constexpr size_t COM_OFF_CTX_ISS = COM_OFF_R + 25;
constexpr size_t COM_OFF_CTX_RED = COM_OFF_CTX_ISS + CTX_BYTES;
constexpr size_t COM_OFF_NF = COM_OFF_CTX_RED + CTX_BYTES;
static_assert(COM_OFF_NF + NF_BYTES + (68 - NF_BYTES - 2 * CTX_BYTES) == KP800_STATE_BYTES);

inline Kp800State encode_com_state(const Nullifier& nf, const Context& ctx_iss,
                                   const Context& ctx_red, const Opening& r) {
    Kp800State state{};
    std::ranges::copy(IHAT_COM_DST, state.begin());
    std::ranges::copy(r, state.begin() + COM_OFF_R);
    std::ranges::copy(ctx_iss, state.begin() + COM_OFF_CTX_ISS);
    std::ranges::copy(ctx_red, state.begin() + COM_OFF_CTX_RED);
    std::ranges::copy(nf, state.begin() + COM_OFF_NF);
    return state;
}

// Unbound tokens. Rather than committing to the nullifier and the redemption context, we commit
// to a PRF key and derive the nullifier from the redemption context.

constexpr size_t NF_KEY_BYTES = 16; // nullifier key length
using NfKey = std::array<uint8_t, NF_KEY_BYTES>;

// Compute a commitment to a nullifier key and issuance context with the given opening.
Commitment unbound_commit(const NfKey& nf_key, const Context& ctx_iss, const Opening& r);

// Derive the nullifier for a redemption context from a nullifier key.
Nullifier derive(const NfKey& nf_key, const Context& ctx_red);

// Unbound commitment layout:
//
//   "mous" || UNBOUND_VERSION || "c0" || r || 0^(25 - r_len) || ctx_iss || nf_key ||
//   0^(68 - ctx_len - nf_key_len)
constexpr size_t UNBOUND_COM_OFF_R = DST_BYTES;
constexpr size_t UNBOUND_COM_OFF_CTX_ISS = UNBOUND_COM_OFF_R + 25;
constexpr size_t UNBOUND_COM_OFF_NF_KEY = UNBOUND_COM_OFF_CTX_ISS + CTX_BYTES;
static_assert(R_BYTES <= 25);
static_assert(UNBOUND_COM_OFF_NF_KEY + NF_KEY_BYTES + (68 - CTX_BYTES - NF_KEY_BYTES) ==
              KP800_STATE_BYTES);

inline Kp800State encode_unbound_com_state(const NfKey& nf_key, const Context& ctx_iss,
                                           const Opening& r) {
    Kp800State state{};
    std::ranges::copy(UNBOUND_IHAT_COM_DST, state.begin());
    std::ranges::copy(r, state.begin() + UNBOUND_COM_OFF_R);
    std::ranges::copy(ctx_iss, state.begin() + UNBOUND_COM_OFF_CTX_ISS);
    std::ranges::copy(nf_key, state.begin() + UNBOUND_COM_OFF_NF_KEY);
    return state;
}

// Derive layout:
//
//   "mous" || UNBOUND_VERSION || "d0" || nf_key || 0^(25 - nf_key_len) || ctx_red ||
//   0^(68 - ctx_len)
constexpr size_t DERIVE_OFF_NF_KEY = DST_BYTES;
constexpr size_t DERIVE_OFF_CTX_RED = DERIVE_OFF_NF_KEY + 25;
static_assert(NF_KEY_BYTES <= 25);
static_assert(DERIVE_OFF_CTX_RED + CTX_BYTES + (68 - CTX_BYTES) == KP800_STATE_BYTES);

inline Kp800State encode_derive_state(const NfKey& nf_key, const Context& ctx_red) {
    Kp800State state{};
    std::ranges::copy(UNBOUND_IHAT_DERIVE_DST, state.begin());
    std::ranges::copy(nf_key, state.begin() + DERIVE_OFF_NF_KEY);
    std::ranges::copy(ctx_red, state.begin() + DERIVE_OFF_CTX_RED);
    return state;
}

} // namespace vole_mole::ihat::detail

#endif
