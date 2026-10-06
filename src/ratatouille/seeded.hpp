// Deterministic functions used to implement the randomized Ratatouille API.

#ifndef VOLE_MOLE_RATATOUILLE_SEEDED_HPP
#define VOLE_MOLE_RATATOUILLE_SEEDED_HPP

#include "vole_mole/ratatouille.hpp"
#include "vole_mole/uov.hpp"

#include <array>
#include <cstddef>
#include <cstdint>

namespace vole_mole::ratatouille::detail {

constexpr size_t SEED_BYTES = 32;
using Seed = std::array<uint8_t, SEED_BYTES>;

// As ratatouille::issue_request, but using seed as the source of randomness.
//
// Throws std::invalid_argument if t_init is 0, std::bad_alloc if memory allocation fails, and
// std::runtime_error if proof generation fails (which happens with negligible probability).
IssueRequestResult issue_request_with_seed(Credits t_init, const Context& ctx_iss,
                                           const Seed& seed);

// As Token::spend_request, but using seed as the source of randomness. The token is consumed under
// the same conditions.
//
// Throws as for Token::spend_request, except that it doesn't use the operating system's random
// number generator.
SpendRequestResult spend_request_with_seed(Token&& token, const uov::PublicKey& pk, Credits d,
                                           const Context& ctx_iss, const Seed& seed);

} // namespace vole_mole::ratatouille::detail

#endif
