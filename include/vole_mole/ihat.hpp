// VOLE-IHAT, a post-quantum Issuer-Hiding Anonymous Token (IHAT) protocol.

#ifndef VOLE_MOLE_IHAT_HPP
#define VOLE_MOLE_IHAT_HPP

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

namespace vole_mole::ihat {

// Version of the draft this implements.
constexpr uint8_t VERSION = 0;

// The maximum size of an Anchor Set.
constexpr size_t MAX_ANCHORS = 64;

// Issuer reporting. Every redemption also reports the index of the issuing Anchor in the Anchor
// Set, split between the Moderator and a third party, the Aggregator, so that neither learns it.
// The Client's contribution is the one-hot vector V of length MAX_ANCHORS with V[i] = 1 for the
// issuing Anchor at index i, split into two additive shares mod 2^16: A, the Moderator's share, and
// B, the Aggregator's share, with A[u] + B[u] = V[u] mod 2^16 for every u.
//
// The Client derives B and a report tag from a short secret, the report, which it sends to the
// Aggregator (e.g., encrypted to the Aggregator). The redemption request carries A and the tag, and
// the redemption proof shows that V is one-hot at the issuing Anchor and that A and the tag are
// consistent with the report. The Aggregator opens the report to get B and the tag, and counts B
// only if the Moderator vouches for the tag, i.e., the tag is the tag of a redemption that the
// Moderator accepted. The tag is collision resistant, so a Client can't get the Aggregator to count
// a share other than the one the Moderator verified.
//
// The Moderator and the Aggregator each sum the shares of the redemptions they both count, i.e.,
// those whose tags match one-to-one (see `aggregate`). Shares whose counterpart is missing must be
// discarded, since a share on its own is uniformly random. The sum of the two aggregates is the
// histogram of issuing Anchors, provided that fewer than 2^16 redemptions are counted.
constexpr size_t HISTOGRAM_SHARE_BYTES = 2 * MAX_ANCHORS; // encoded share length
constexpr size_t REPORT_BYTES = 16;                       // report length
constexpr size_t REPORT_TAG_BYTES = 32;                   // report tag length
using HistogramShare = std::array<uint16_t, MAX_ANCHORS>;
using Report = std::array<uint8_t, REPORT_BYTES>;
using ReportTag = std::array<uint8_t, REPORT_TAG_BYTES>;

// Protocol messages.
constexpr size_t NF_BYTES = 24;               // nullifier length
constexpr size_t CTX_BYTES = 16;              // context length
constexpr size_t CHALLENGE_DIGEST_BYTES = 32; // challenge digest length
constexpr size_t ISSUE_PROOF_BYTES = 7272;    // issuance proof length
constexpr size_t ISSUE_REQUEST_BYTES = uov::M + ISSUE_PROOF_BYTES;
constexpr size_t REDEEM_PROOF_BYTES = 19223; // redemption proof length
// A redemption request is nf || A || tag || proof, where A is encoded as MAX_ANCHORS little-endian
// 16-bit words.
constexpr size_t REDEEM_REQUEST_BYTES =
    NF_BYTES + HISTOGRAM_SHARE_BYTES + REPORT_TAG_BYTES + REDEEM_PROOF_BYTES;
using Nullifier = std::array<uint8_t, NF_BYTES>;
using Context = std::array<uint8_t, CTX_BYTES>;
using ChallengeDigest = std::array<uint8_t, CHALLENGE_DIGEST_BYTES>;
using IssueRequest = std::array<uint8_t, ISSUE_REQUEST_BYTES>;
using IssueResponse = uov::Preimage;
using RedeemRequest = std::array<uint8_t, REDEEM_REQUEST_BYTES>;

// Protocol messages for unbound tokens.
constexpr size_t UNBOUND_ISSUE_PROOF_BYTES = 6864; // issuance proof length
constexpr size_t UNBOUND_ISSUE_REQUEST_BYTES = uov::M + UNBOUND_ISSUE_PROOF_BYTES;
constexpr size_t UNBOUND_REDEEM_PROOF_BYTES = 22895; // redemption proof length
// As for RedeemRequest: nf || A || tag || proof.
constexpr size_t UNBOUND_REDEEM_REQUEST_BYTES =
    NF_BYTES + HISTOGRAM_SHARE_BYTES + REPORT_TAG_BYTES + UNBOUND_REDEEM_PROOF_BYTES;
using UnboundIssueRequest = std::array<uint8_t, UNBOUND_ISSUE_REQUEST_BYTES>;
using UnboundRedeemRequest = std::array<uint8_t, UNBOUND_REDEEM_REQUEST_BYTES>;

// The Moderator's output of a successful redemption.
struct Redemption {
    Nullifier nf;         // nullifier of the redeemed token
    HistogramShare share; // the Moderator's share A
    ReportTag tag;        // the report tag

    bool operator==(const Redemption&) const = default;
};

// The Aggregator's output of opening a report.
struct OpenedReport {
    HistogramShare share; // the Aggregator's share B
    ReportTag tag;        // the report tag

    bool operator==(const OpenedReport&) const = default;
};

// Aggregator: Open a report to get its share and tag. Any report opens successfully; it's the tag
// check (see above) that ensures the share is the one the Moderator verified.
OpenedReport open_report(const Report& report);

// Add `share` to the aggregate `agg`, mod 2^16. Each of the Moderator and the Aggregator sums its
// shares this way; summing the two aggregates the same way yields the histogram.
inline void aggregate(HistogramShare& agg, const HistogramShare& share) {
    for (size_t u = 0; u < MAX_ANCHORS; ++u) {
        agg[u] = static_cast<uint16_t>(agg[u] + share[u]);
    }
}

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

// The Client's output of redemption: the request for the Moderator and the report for the
// Aggregator. The report must be kept secret from the Moderator, which could otherwise learn the
// issuing Anchor.
struct RedeemRequestResult {
    RedeemRequest request;
    Report report;
};

// A VOLE-IHAT token.
class Token {
  public:
    Token(Token&&) noexcept;
    Token& operator=(Token&&) noexcept;
    ~Token();

    // Consume the token and generate a redemption request for the issuing Anchor in the given
    // Anchor Set and issuance and redemption contexts, along with the report of the issuing Anchor
    // for the Aggregator. challenge_digest binds the challenge that triggered redemption to the
    // proof; the Moderator must verify with the same digest. The challenge digest is determined at
    // redemption time and isn't in the commitment.
    //
    // Throws std::logic_error if the token was already consumed, std::invalid_argument if no Anchor
    // issued the token for ctx_iss and ctx_red, std::bad_alloc if memory allocation fails, and
    // std::runtime_error if the operating system's random number generator fails or proof
    // generation fails (which happens with negligible probability).
    RedeemRequestResult redeem_request(const AnchorSet& anchors, const Context& ctx_iss,
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
// digest of the challenge that triggered redemption. Returns the nullifier of the redeemed token
// and the Moderator's share and report tag, or std::nullopt if the request is invalid (including if
// the challenge digest doesn't match).
//
// It's the caller's responsibility to record the nullifier of every token it accepts for ctx_iss
// and ctx_red, and to reject a request whose nullifier it has already recorded. The record must
// cover every Anchor Set the caller accepts for these contexts, since a token is valid under any
// Anchor Set that contains its Anchor. Records must be kept for as long as tokens for these
// contexts are accepted (so contexts that expire, e.g., an issuance epoch, bound the storage
// required).
//
// Throws std::bad_alloc if memory allocation fails. An invalid request never causes an exception.
std::optional<Redemption> finalize_redeem(const AnchorSet& anchors, const RedeemRequest& request,
                                          const Context& ctx_iss, const Context& ctx_red,
                                          const ChallengeDigest& challenge_digest);

// As RedeemRequestResult, for unbound tokens.
struct UnboundRedeemRequestResult {
    UnboundRedeemRequest request;
    Report report;
};

// A VOLE-IHAT token that has not yet been bound to a redemption context.
//
// A Token is bound to its redemption context at issuance. An UnboundToken is bound later, during
// redemption, and can be redeemed in any number of redemption contexts. The nullifier is a
// pseudorandom function of the redemption context, keyed by a secret key that the Client commits
// to at issuance. Thus, redemptions of the same token for different redemption contexts can't be
// linked to each other (or to issuance). However, redemptions for the same issuance and redemption
// context have the same nullifier.
//
// Unbound tokens use their own commitment and proofs, so a Token can't be redeemed as an
// UnboundToken or vice versa, even if the same Anchor issued both.
class UnboundToken {
  public:
    UnboundToken(UnboundToken&&) noexcept;
    UnboundToken& operator=(UnboundToken&&) noexcept;
    ~UnboundToken();

    // Generate a redemption request for the issuing Anchor in the given Anchor Set and issuance
    // and redemption contexts, along with the report of the issuing Anchor for the Aggregator.
    // challenge_digest binds the challenge that triggered redemption to the proof; the Moderator
    // must verify with the same digest. Every redemption has a fresh report.
    //
    // Throws std::logic_error if the token was moved from, std::invalid_argument if no Anchor
    // issued the token for ctx_iss, std::bad_alloc if memory allocation fails, and
    // std::runtime_error if the operating system's random number generator fails or proof
    // generation fails (which happens with negligible probability).
    UnboundRedeemRequestResult redeem_request(const AnchorSet& anchors, const Context& ctx_iss,
                                              const Context& ctx_red,
                                              const ChallengeDigest& challenge_digest) const;

  private:
    struct Impl;
    std::unique_ptr<Impl> impl_;

    explicit UnboundToken(std::unique_ptr<Impl> impl);
    friend class PendingUnboundToken;
    friend struct detail::TokenAccess;
};

// Client state while awaiting the issue response for an unbound token.
class PendingUnboundToken {
  public:
    PendingUnboundToken(PendingUnboundToken&&) noexcept;
    PendingUnboundToken& operator=(PendingUnboundToken&&) noexcept;
    ~PendingUnboundToken();

    // Consume the pending token and finalize issuance using the issuing Anchor's public key pk.
    // Returns std::nullopt if the response isn't a signature of the Client's commitment under pk.
    //
    // Throws std::logic_error if the pending token was already consumed and std::bad_alloc if
    // memory allocation fails.
    std::optional<UnboundToken> finalize_issue(const uov::PublicKey& pk,
                                               const IssueResponse& response) &&;

  private:
    struct Impl;
    std::unique_ptr<Impl> impl_;

    explicit PendingUnboundToken(std::unique_ptr<Impl> impl);
    friend struct detail::TokenAccess;
};

struct UnboundIssueRequestResult {
    PendingUnboundToken pending_token;
    UnboundIssueRequest request;
};

// Generate an issue request for an unbound token for the given issuance context.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if the operating
// system's random number generator fails or if proof generation fails (which happens with
// negligible probability).
UnboundIssueRequestResult unbound_issue_request(const Context& ctx_iss);

// Respond to an issue request for an unbound token. Returns std::nullopt if the issuance proof is
// invalid, i.e., the request doesn't commit to ctx_iss.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if preimage derivation
// fails (which happens with negligible probability). An invalid request never causes an exception.
std::optional<IssueResponse> unbound_issue_response(const uov::SecretKey& sk,
                                                    const UnboundIssueRequest& request,
                                                    const Context& ctx_iss);

// Verify a redemption request for an unbound token. Returns the nullifier of the redeemed token for
// ctx_red and the Moderator's share and report tag, or std::nullopt if the request is invalid.
//
// As for finalize_redeem, it's the caller's responsibility to record the nullifier of every token
// it accepts for ctx_iss and ctx_red, and to reject a request whose nullifier it has already
// recorded, across every Anchor Set it accepts for these contexts. Since an unbound token can be
// redeemed for any context, this is necessary to limit the Client to one redemption per context.
//
// Throws std::bad_alloc if memory allocation fails. An invalid request never causes an exception.
std::optional<Redemption> unbound_finalize_redeem(const AnchorSet& anchors,
                                                  const UnboundRedeemRequest& request,
                                                  const Context& ctx_iss, const Context& ctx_red,
                                                  const ChallengeDigest& challenge_digest);

} // namespace vole_mole::ihat

#endif
