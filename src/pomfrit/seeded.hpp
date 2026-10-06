// Deterministic functions used to implement the randomized PomFRIT API.

#ifndef VOLE_MOLE_POMFRIT_SEEDED_HPP
#define VOLE_MOLE_POMFRIT_SEEDED_HPP

#include "vole_mole/pomfrit.hpp"
#include "vole_mole/uov.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

namespace vole_mole::pomfrit::detail {

constexpr size_t SEED_BYTES = 32;
using Seed = std::array<uint8_t, SEED_BYTES>;

// Request issuance for msg under public key pk using seed as the source of randomness.
//
// Throws std::bad_alloc if memory allocation fails.
IssueRequestResult issue_request_with_seed(const uov::PublicKey& pk, std::span<const uint8_t> msg,
                                           const Seed& seed);

} // namespace vole_mole::pomfrit::detail

#endif
