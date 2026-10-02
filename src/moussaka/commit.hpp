// The input layout of the Moussaka commitment.

#ifndef VOLE_MOLE_MOUSSAKA_COMMIT_HPP
#define VOLE_MOLE_MOUSSAKA_COMMIT_HPP

#include "vole_mole/keccak.hpp"
#include "vole_mole/moussaka.hpp"

#include "dst.hpp"

#include <algorithm>
#include <cstddef>

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

} // namespace vole_mole::moussaka::detail

#endif
