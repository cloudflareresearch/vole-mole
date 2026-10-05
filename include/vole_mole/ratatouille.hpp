// Ratatouille, a post-quantum Anonymous Credit Token (ACT) protocol.

#ifndef VOLE_MOLE_RATATOUILLE_HPP
#define VOLE_MOLE_RATATOUILLE_HPP

#include "vole_mole/uov.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>

namespace vole_mole::ratatouille {

// Version of the draft this implements.
constexpr uint8_t VERSION = 0;

// Credit values, i.e., credits held by a token, refunds, and spends.
using Credits = uint64_t;
constexpr size_t CREDIT_BYTES = sizeof(Credits);

// Protocol messages.
constexpr size_t NF_BYTES = 24;            // nullifier length
constexpr size_t R_BYTES = 16;             // commitment opening length
constexpr size_t CTX_BYTES = 16;           // issuance context length
constexpr size_t COMMITMENT_BYTES = 32;    // commitment length
constexpr size_t ISSUE_PROOF_BYTES = 7000; // issuance proof length
constexpr size_t ISSUE_REQUEST_BYTES = COMMITMENT_BYTES + ISSUE_PROOF_BYTES;
constexpr size_t SPEND_PROOF_BYTES = 17319; // spend proof length
constexpr size_t SPEND_REQUEST_BYTES =
    NF_BYTES + CREDIT_BYTES + COMMITMENT_BYTES + SPEND_PROOF_BYTES;
constexpr size_t SPEND_RESPONSE_BYTES = CREDIT_BYTES + uov::N;
using Nullifier = std::array<uint8_t, NF_BYTES>;
using Opening = std::array<uint8_t, R_BYTES>;
using Context = std::array<uint8_t, CTX_BYTES>;
using Commitment = std::array<uint8_t, COMMITMENT_BYTES>;

// The issue request is c || pf_iss, where c is the commitment and pf_iss the issuance proof.
using IssueRequest = std::array<uint8_t, ISSUE_REQUEST_BYTES>;

// The issue response is the Issuer's signature s.
using IssueResponse = uov::Preimage;

// Credit values are encoded little-endian with L = CREDIT_BYTES bytes, denoted <v>_L.
//
// The spend request is nf || <d>_L || c' || pf_spend, where nf is the nullifier of the token being
// spent, d is the number of credits to spend, c' is the commitment to the updated state, and
// pf_spend is the spend proof.
using SpendRequest = std::array<uint8_t, SPEND_REQUEST_BYTES>;

// The spend response is <x'>_L || s', where x' is the refund and s' is the Issuer's signature over
// the updated state.
using SpendResponse = std::array<uint8_t, SPEND_RESPONSE_BYTES>;

// Randomness.
constexpr size_t SEED_BYTES = 32;
using Seed = std::array<uint8_t, SEED_BYTES>;

namespace detail {
struct TokenAccess;
} // namespace detail

struct IssueRequestResult;
struct SpendRequestResult;

// A Ratatouille token. The state holds credit() credits and a refund of refund() credits, so it can
// spend up to credit() + refund() credits. (Note that the sum may exceed the largest credit value,
// in which case the change of a spend must be at most the largest credit value.)
class Token {
  public:
    Token(Token&&) noexcept;
    Token& operator=(Token&&) noexcept;
    ~Token();

    // The credit t held by the token. Throws std::logic_error if the token was consumed.
    Credits credit() const;

    // The refund x carried by the token. Throws std::logic_error if the token was consumed.
    Credits refund() const;

    // Consume the token and generate a request to spend d of its credits, where the token was
    // issued by the Issuer with public key pk for the given issuance context.
    //
    // Throws std::logic_error if the token was already consumed, std::invalid_argument if the
    // token wasn't issued by pk for ctx_iss, if d exceeds the token's balance, or if the change
    // credit() + refund() - d would exceed the largest credit value, std::bad_alloc if memory
    // allocation fails, and std::runtime_error if the operating system's random number generator
    // fails or proof generation fails (which happens with negligible probability).
    SpendRequestResult spend_request(const uov::PublicKey& pk, Credits d,
                                     const Context& ctx_iss) &&;

    // Consume the token and generate a spend request with the given random seed.
    //
    // Throws as for spend_request, except that it doesn't use the operating system's random number
    // generator.
    SpendRequestResult spend_request_with_seed(const uov::PublicKey& pk, Credits d,
                                               const Context& ctx_iss, const Seed& seed) &&;

  private:
    struct Impl;
    std::unique_ptr<Impl> impl_;

    explicit Token(std::unique_ptr<Impl> impl);
    friend class PendingToken;
    friend class PendingSpend;
    friend struct detail::TokenAccess;
};

// Client state while awaiting the issue response from the Issuer.
class PendingToken {
  public:
    PendingToken(PendingToken&&) noexcept;
    PendingToken& operator=(PendingToken&&) noexcept;
    ~PendingToken();

    // Consume the pending token and finalize issuance using the Issuer's public key pk.
    // (VerifyIssuance in the draft). Returns std::nullopt if the response isn't a signature of the
    // Client's commitment under pk.
    //
    // Throws std::logic_error if the pending token was already consumed and std::bad_alloc if
    // memory allocation fails.
    std::optional<Token> finalize_issue(const uov::PublicKey& pk, const IssueResponse& response) &&;

  private:
    struct Impl;
    std::unique_ptr<Impl> impl_;

    explicit PendingToken(std::unique_ptr<Impl> impl);
    friend IssueRequestResult issue_request_with_seed(Credits t_init, const Context& ctx_iss,
                                                      const Seed& seed);
    friend struct detail::TokenAccess;
};

// Client state while awaiting the spend response from the Issuer.
class PendingSpend {
  public:
    PendingSpend(PendingSpend&&) noexcept;
    PendingSpend& operator=(PendingSpend&&) noexcept;
    ~PendingSpend();

    // Consume the pending spend and finalize it using the Issuer's public key (VerifyRefund in the
    // draft). Returns the change token, or std::nullopt if the response isn't a signature of the
    // updated state and the refund under pk.
    //
    // Throws std::logic_error if the pending spend was already consumed and std::bad_alloc if
    // memory allocation fails.
    std::optional<Token> finalize_spend(const uov::PublicKey& pk, const SpendResponse& response) &&;

  private:
    struct Impl;
    std::unique_ptr<Impl> impl_;

    explicit PendingSpend(std::unique_ptr<Impl> impl);
    friend class Token;
    friend struct detail::TokenAccess;
};

struct IssueRequestResult {
    PendingToken pending_token;
    IssueRequest request;
};

struct SpendRequestResult {
    PendingSpend pending_spend;
    SpendRequest request;
};

// Compute the commitment Com(nf, ctx_iss, t, r) to a nullifier, issuance context, and credit value
// with the given opening.
Commitment commit(const Nullifier& nf, const Context& ctx_iss, Credits t, const Opening& r);

// Compute the UOV target Tag(c, x) that binds the commitment c to the refund x.
uov::Target tag(const Commitment& c, Credits x);

// Generate an issue request for t_init credits and the issuance context.
//
// Throws std::invalid_argument if t_init is 0, std::bad_alloc if memory allocation fails, and
// std::runtime_error if the operating system's random number generator fails or if proof
// generation fails (which happens with negligible probability).
IssueRequestResult issue_request(Credits t_init, const Context& ctx_iss);

// Compute the issuance request with the given random seed.
//
// Throws std::invalid_argument if t_init is 0, std::bad_alloc if memory allocation fails, and
// std::runtime_error if proof generation fails (which happens with negligible probability).
IssueRequestResult issue_request_with_seed(Credits t_init, const Context& ctx_iss,
                                           const Seed& seed);

// Respond to an issue request for t_init credits and the issuance context with the Issuer's secret
// key sk. Returns std::nullopt if the issuance proof is invalid, i.e., the request doesn't commit
// to t_init and ctx_iss.
//
// Throws std::invalid_argument if t_init is 0, std::bad_alloc if memory allocation fails, and
// std::runtime_error if preimage derivation fails (which happens with negligible probability). An
// invalid request never causes an exception.
std::optional<IssueResponse> issue_response(const uov::SecretKey& sk, const IssueRequest& request,
                                            Credits t_init, const Context& ctx_iss);

// The result of spend_response for a valid spend request.
struct SpendResponseResult {
    SpendResponse response; // the response to send to the Client (see spend_response)
    Nullifier nf;           // nullifier of the spent token
    Credits d;              // number of credits spent
};

// Respond to a spend request with the Issuer's secret key: verify the spend proof for the
// corresponding public key and the issuance context, and sign the updated state with the given
// refund. Returns the response, the nullifier of the spent token, and the number of credits spent,
// or std::nullopt if the request is invalid.
//
// Throws std::bad_alloc if memory allocation fails and std::runtime_error if preimage derivation
// fails (which happens with negligible probability). An invalid request never causes an exception.
std::optional<SpendResponseResult> spend_response(const uov::SecretKey& sk,
                                                  const SpendRequest& request,
                                                  const Context& ctx_iss, Credits refund);

} // namespace vole_mole::ratatouille

#endif
