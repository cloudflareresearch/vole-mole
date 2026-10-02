// Moussaka, a post-quantum variant of the Issuer-Hiding Anonymous Token (IHAT) protocol.

#ifndef VOLE_MOLE_MOUSSAKA_HPP
#define VOLE_MOLE_MOUSSAKA_HPP

#include "vole_mole/uov.hpp"

#include <array>
#include <cstddef>
#include <cstdint>

namespace vole_mole::moussaka {

// Version of the draft this implements; used for domain separation.
constexpr uint8_t VERSION = 0;

// Protocol messages.
constexpr size_t NF_BYTES = 24;            // nullifier length
constexpr size_t R_BYTES = 16;             // commitment opening length
constexpr size_t CTX_BYTES = 16;           // context length
constexpr size_t ISSUE_PROOF_BYTES = 7272; // issuance proof length
constexpr size_t ISSUE_REQUEST_BYTES = uov::M + ISSUE_PROOF_BYTES;
using Nullifier = std::array<uint8_t, NF_BYTES>;
using Opening = std::array<uint8_t, R_BYTES>;
using Context = std::array<uint8_t, CTX_BYTES>;
using Commitment = uov::Target;
using IssueRequest = std::array<uint8_t, ISSUE_REQUEST_BYTES>;

// Randomness.
constexpr size_t SEED_BYTES = 32;
using Seed = std::array<uint8_t, SEED_BYTES>;

// Client state while awaiting the issue response from the Anchor.
struct PendingToken {
    Nullifier nf;
    Opening r;
};

struct IssueRequestResult {
    PendingToken pending_token;
    IssueRequest request;
};

// Compute a commitment to a nullifier, issuance context, and redemption context with the given
// opening.
Commitment commit(const Nullifier& nf, const Context& ctx_iss, const Context& ctx_red,
                  const Opening& r);

// Generate an issue request for an issuance and redemption context.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if the operating
// system's random number generator fails.
IssueRequestResult issue_request(const Context& ctx_iss, const Context& ctx_red);

// Compute the issuance request with the given random seed.
//
// Throws std::bad_alloc if memory allocation fails.
IssueRequestResult issue_request_with_seed(const Context& ctx_iss, const Context& ctx_red,
                                           const Seed& seed);

} // namespace vole_mole::moussaka

#endif
