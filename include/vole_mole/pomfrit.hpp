// PomFRIT <https://ia.cr/2026/109>, a post-quantum blind signature. The implementation is based on
// the optimized signature described in the paper (Algorithm 2), which avoids evaluating the
// commitment in the VOLEitH circuit. Security relies on the one-more preimage resistance of UOV.

#ifndef VOLE_MOLE_POMFRIT_HPP
#define VOLE_MOLE_POMFRIT_HPP

#include "vole_mole/uov.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <span>

namespace vole_mole::pomfrit {

// Version of PomFRIT. There is no spec yet, but an IETF draft would use this for domain separation
// between draft revisions.
constexpr uint8_t VERSION = 0;

// Protocol messages.
using IssueRequest = uov::Target;    // Client -> Issuer request
using IssueResponse = uov::Preimage; // Issuer -> Client response

// The blind signature presented by the Client to the relying party.
constexpr size_t SIGNATURE_BYTES = 5659;
using BlindSignature = std::array<uint8_t, SIGNATURE_BYTES>;

namespace detail {
struct PendingBlindSignatureAccess;
} // namespace detail

// Client state while awaiting the response from the Issuer.
class PendingBlindSignature {
  public:
    PendingBlindSignature(PendingBlindSignature&&) noexcept;
    PendingBlindSignature& operator=(PendingBlindSignature&&) noexcept;
    ~PendingBlindSignature();

    // Consume the response from the Issuer and return the blind signature. Returns std::nullopt if
    // the response is invalid.
    //
    // Throws std::logic_error if this pending signature was moved from (including by a previous
    // call to finalize_issue) and std::invalid_argument if pk isn't the public key passed to
    // issue_request; in these cases the pending signature is left unchanged. Otherwise, throws
    // std::bad_alloc if memory allocation fails and std::runtime_error if proof generation fails
    // (which happens with negligible probability); in these cases the pending signature is
    // consumed.
    std::optional<BlindSignature> finalize_issue(const uov::PublicKey& pk,
                                                 const IssueResponse& response) &&;

  private:
    struct Impl;
    std::unique_ptr<Impl> impl_;

    explicit PendingBlindSignature(std::unique_ptr<Impl> impl);
    friend struct detail::PendingBlindSignatureAccess;
};

struct IssueRequestResult {
    PendingBlindSignature pending;
    IssueRequest request;
};

// Request issuance for msg under public key pk.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if the operating
// system's random number generator fails.
IssueRequestResult issue_request(const uov::PublicKey& pk, std::span<const uint8_t> msg);

// Issue a blind signature under secret key sk.
//
// Throws std::runtime_error if preimage derivation fails (which happens with negligible
// probability).
IssueResponse issue_response(const uov::SecretKey& sk, const IssueRequest& request);

// Verify sig on msg under public key pk. Returns false if the signature is invalid.
//
// Throws std::bad_alloc if memory allocation fails. An invalid signature never causes an
// exception.
bool verify(const uov::PublicKey& pk, std::span<const uint8_t> msg, const BlindSignature& sig);

} // namespace vole_mole::pomfrit

#endif
