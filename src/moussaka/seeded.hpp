// Deterministic functions used to implement the randomized Moussaka API.

#ifndef VOLE_MOLE_MOUSSAKA_SEEDED_HPP
#define VOLE_MOLE_MOUSSAKA_SEEDED_HPP

#include "vole_mole/moussaka.hpp"

#include <array>
#include <cstddef>
#include <cstdint>

namespace vole_mole::moussaka::detail {

constexpr size_t SEED_BYTES = 32;
using Seed = std::array<uint8_t, SEED_BYTES>;

// As moussaka::issue_request, but using seed as the source of randomness.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if proof generation fails
// (which happens with negligible probability).
IssueRequestResult issue_request_with_seed(const Context& ctx_iss, const Context& ctx_red,
                                           const Seed& seed);

// As Token::redeem_request, but using seed as the source of randomness. The token is consumed
// under the same conditions.
//
// Throws as for Token::redeem_request, except that it doesn't use the operating system's random
// number generator.
RedeemRequest redeem_request_with_seed(Token&& token, const AnchorSet& anchors,
                                       const Context& ctx_iss, const Context& ctx_red,
                                       const ChallengeDigest& challenge_digest, const Seed& seed);

// As moussaka::unbound_issue_request, but using seed as the source of randomness.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if proof generation fails
// (which happens with negligible probability).
UnboundIssueRequestResult unbound_issue_request_with_seed(const Context& ctx_iss, const Seed& seed);

// As UnboundToken::redeem_request, but using seed as the source of randomness.
//
// Throws as for UnboundToken::redeem_request, except that it doesn't use the operating system's
// random number generator.
UnboundRedeemRequest
unbound_redeem_request_with_seed(const UnboundToken& token, const AnchorSet& anchors,
                                 const Context& ctx_iss, const Context& ctx_red,
                                 const ChallengeDigest& challenge_digest, const Seed& seed);

} // namespace vole_mole::moussaka::detail

#endif
