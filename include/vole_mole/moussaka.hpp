// Moussaka, a post-quantum Issuer-Hiding Anonymous Token (IHAT) protocol.

#ifndef VOLE_MOLE_MOUSSAKA_HPP
#define VOLE_MOLE_MOUSSAKA_HPP

#include "vole_mole/uov.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <initializer_list>
#include <memory>
#include <optional>
#include <span>
#include <vector>

namespace vole_mole::moussaka {

// Version of the draft this implements.
constexpr uint8_t VERSION = 0;

// The maximum size of an Anchor Set.
constexpr size_t MAX_ANCHORS = 64;

// Protocol messages.
constexpr size_t NF_BYTES = 24;               // nullifier length
constexpr size_t CTX_BYTES = 16;              // context length
constexpr size_t CHALLENGE_DIGEST_BYTES = 32; // challenge digest length
constexpr size_t ISSUE_PROOF_BYTES = 7272;    // issuance proof length
constexpr size_t ISSUE_REQUEST_BYTES = uov::M + ISSUE_PROOF_BYTES;
constexpr size_t REDEEM_PROOF_BYTES = 8751; // redemption proof length
constexpr size_t REDEEM_REQUEST_BYTES = NF_BYTES + REDEEM_PROOF_BYTES;
using Nullifier = std::array<uint8_t, NF_BYTES>;
using Context = std::array<uint8_t, CTX_BYTES>;
using ChallengeDigest = std::array<uint8_t, CHALLENGE_DIGEST_BYTES>;
using IssueRequest = std::array<uint8_t, ISSUE_REQUEST_BYTES>;
using IssueResponse = uov::Preimage;
using RedeemRequest = std::array<uint8_t, REDEEM_REQUEST_BYTES>;

// A reference to an Anchor's public key.
using AnchorRef = std::reference_wrapper<const uov::PublicKey>;

// The Anchor Set, a sequence of distinct Anchor public keys. An Anchor Set is non-empty and has at
// most MAX_ANCHORS keys.
class AnchorSet {
  public:
    // Throws std::invalid_argument if the keys are empty, if there are more than MAX_ANCHORS, or
    // if a key appears more than once, and std::bad_alloc if memory allocation fails.
    explicit AnchorSet(std::span<const AnchorRef> keys);
    explicit AnchorSet(std::span<const uov::PublicKey> keys);
    explicit AnchorSet(std::initializer_list<AnchorRef> keys);

    size_t size() const { return keys_.size(); }
    const uov::PublicKey& operator[](size_t i) const { return keys_[i]; }
    std::span<const AnchorRef> keys() const { return keys_; }

  private:
    std::vector<AnchorRef> keys_;
};

namespace detail {
struct TokenAccess;
} // namespace detail

// A Moussaka token.
class Token {
  public:
    Token(Token&&) noexcept;
    Token& operator=(Token&&) noexcept;
    ~Token();

    // Consume the token and generate a redemption request for it, where the token was issued by
    // anchors[i] for the given issuance and redemption context. challenge_digest binds the
    // challenge that triggered redemption to the proof; the Moderator must verify with the same
    // digest. The challenge digest is determined at redemption time and isn't in the commitment.
    //
    // Throws std::logic_error if the token was already consumed, std::invalid_argument if i is out
    // of range or the token wasn't issued by anchors[i] for ctx_iss and ctx_red, std::bad_alloc if
    // memory allocation fails, and std::runtime_error if the operating system's random number
    // generator fails or proof generation fails (which happens with negligible probability).
    RedeemRequest redeem_request(const AnchorSet& anchors, size_t i, const Context& ctx_iss,
                                 const Context& ctx_red,
                                 const ChallengeDigest& challenge_digest) &&;

  private:
    struct Impl;
    std::unique_ptr<Impl> impl_;

    explicit Token(std::unique_ptr<Impl> impl);
    friend class PendingToken;
    friend struct detail::TokenAccess;
};

// Client state while awaiting the issue response from the Anchor.
class PendingToken {
  public:
    PendingToken(PendingToken&&) noexcept;
    PendingToken& operator=(PendingToken&&) noexcept;
    ~PendingToken();

    // Consume the pending token and finalize issuance using the issuing Anchor's public key pk.
    // Returns std::nullopt if the response isn't a signature of the Client's commitment under pk.
    //
    // Throws std::logic_error if the pending token was already consumed and std::bad_alloc if
    // memory allocation fails.
    std::optional<Token> finalize_issue(const uov::PublicKey& pk, const IssueResponse& response) &&;

  private:
    struct Impl;
    std::unique_ptr<Impl> impl_;

    explicit PendingToken(std::unique_ptr<Impl> impl);
    friend struct detail::TokenAccess;
};

struct IssueRequestResult {
    PendingToken pending_token;
    IssueRequest request;
};

// Generate an issue request for an issuance and redemption context.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if the operating
// system's random number generator fails or if proof generation fails (which happens with
// negligible probability).
IssueRequestResult issue_request(const Context& ctx_iss, const Context& ctx_red);

// Respond to an issue request for the issuance context with the Anchor's secret key sk. Returns
// std::nullopt if the issuance proof is invalid, i.e., the request doesn't commit to ctx_iss.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if preimage derivation
// fails (which happens with negligible probability). An invalid request never causes an exception.
std::optional<IssueResponse> issue_response(const uov::SecretKey& sk, const IssueRequest& request,
                                            const Context& ctx_iss);

// Verify a redemption request for the Anchor Set, the issuance and redemption context, and the
// digest of the challenge that triggered redemption. Returns the nullifier of the redeemed token,
// or std::nullopt if the request is invalid (including if the challenge digest doesn't match).
//
// It's the caller's responsibility to record the nullifier of every token it accepts for ctx_iss
// and ctx_red, and to reject a request whose nullifier it has already recorded. The record must
// cover every Anchor Set the caller accepts for these contexts, since a token is valid under any
// Anchor Set that contains its Anchor. Records must be kept for as long as tokens for these
// contexts are accepted (so contexts that expire, e.g., an issuance epoch, bound the storage
// required).
//
// Throws std::bad_alloc if memory allocation fails. An invalid request never causes an exception.
std::optional<Nullifier> finalize_redeem(const AnchorSet& anchors, const RedeemRequest& request,
                                         const Context& ctx_iss, const Context& ctx_red,
                                         const ChallengeDigest& challenge_digest);

} // namespace vole_mole::moussaka

#endif
