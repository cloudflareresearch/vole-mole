#include "vole_mole/ratatouille.hpp"
#include "vole_mole/random.hpp"

#include "dst.hpp"
#include "ratatouille/commit.hpp"
#include "ratatouille/issue.hpp"
#include "ratatouille/seeded.hpp"
#include "ratatouille/spend.hpp"
#include "ratatouille/token.hpp"

#include <algorithm>
#include <memory>
#include <span>
#include <stdexcept>
#include <utility>

namespace vole_mole::ratatouille {

using detail::commit;
using detail::Commitment;
using detail::decode_credits;
using detail::encode_credits;
using detail::IssueRelation;
using detail::Opening;
using detail::Seed;
using detail::SEED_BYTES;
using detail::SpendRelation;
using detail::tag;
using detail::TokenAccess;

namespace {

using namespace vole_mole::detail;

// Layout of the spend request: nf || <d>_L || c' || pf_spend.
constexpr size_t REQ_OFF_NF = 0;
constexpr size_t REQ_OFF_D = REQ_OFF_NF + NF_BYTES;
constexpr size_t REQ_OFF_C_NEXT = REQ_OFF_D + CREDIT_BYTES;
constexpr size_t REQ_OFF_PROOF = REQ_OFF_C_NEXT + COMMITMENT_BYTES;
static_assert(REQ_OFF_PROOF + SPEND_PROOF_BYTES == SPEND_REQUEST_BYTES);

// Layout of the spend response: <x'>_L || s'.
constexpr size_t RESP_OFF_X = 0;
constexpr size_t RESP_OFF_S = RESP_OFF_X + CREDIT_BYTES;
static_assert(RESP_OFF_S + uov::N == SPEND_RESPONSE_BYTES);

// The randomness of an issue or spend request: the nullifier and opening of the state and the
// VOLEitH prover randomness.
template <typename Relation> struct RequestRandomness {
    Nullifier nf;
    Opening r;
    ProveSeed<Relation> rho;
};

template <typename Relation>
RequestRandomness<Relation> expand_seed(std::span<const uint8_t> dst, const Seed& seed) {
    static_assert(Relation::params::secpar_v == faest::secpar::s128);

    faest::hash_state xof;
    xof.init(faest::secpar::s128);
    xof.update(dst);
    xof.update(seed);
    Keccak_HashFinal(&xof.ctx, nullptr);

    RequestRandomness<Relation> rand;
    Keccak_HashSqueeze(&xof.ctx, rand.nf.data(), 8 * rand.nf.size());
    Keccak_HashSqueeze(&xof.ctx, rand.r.data(), 8 * rand.r.size());
    Keccak_HashSqueeze(&xof.ctx, rand.rho.data(), 8 * rand.rho.size());
    return rand;
}

void check_t_init(Credits t_init) {
    if (t_init == 0) {
        throw std::invalid_argument("Ratatouille: initial credit must be positive");
    }
}

} // namespace

Commitment detail::commit(const Nullifier& nf, const Context& ctx_iss, Credits t,
                          const Opening& r) {
    const Kp800State out = keccak_p800(detail::encode_com_state(nf, ctx_iss, t, r));
    Commitment c;
    std::copy_n(out.begin(), c.size(), c.begin());
    return c;
}

uov::Target detail::tag(const Commitment& c, Credits x) {
    const Kp800State out = keccak_p800(detail::encode_tag_state(c, x));
    uov::Target y;
    std::copy_n(out.begin(), y.size(), y.begin());
    return y;
}

// Token

struct Token::Impl {
    Nullifier nf;
    Credits t;
    Opening r;
    Credits x;
    uov::Preimage s;
};

Token::Token(std::unique_ptr<Impl> impl) : impl_(std::move(impl)) {}
Token::Token(Token&&) noexcept = default;
Token& Token::operator=(Token&&) noexcept = default;
Token::~Token() = default;

Credits Token::credit() const {
    if (!impl_) {
        throw std::logic_error("Ratatouille: token was moved from");
    }
    return impl_->t;
}

Credits Token::refund() const {
    if (!impl_) {
        throw std::logic_error("Ratatouille: token was moved from");
    }
    return impl_->x;
}

// Issuance

struct PendingToken::Impl {
    Nullifier nf;
    Opening r;
    Credits t_init;
    Commitment c; // Com(nf, ctx_iss, t_init, r)
};

PendingToken::PendingToken(std::unique_ptr<Impl> impl) : impl_(std::move(impl)) {}
PendingToken::PendingToken(PendingToken&&) noexcept = default;
PendingToken& PendingToken::operator=(PendingToken&&) noexcept = default;
PendingToken::~PendingToken() = default;

IssueRequestResult detail::issue_request_with_seed(Credits t_init, const Context& ctx_iss,
                                                   const Seed& seed) {
    check_t_init(t_init);
    const auto rand = expand_seed<IssueRelation>(RATATOUILLE_ISSUE_SEED_DST, seed);

    const Commitment c = commit(rand.nf, ctx_iss, t_init, rand.r);
    IssueRequest request;
    std::ranges::copy(c, std::span(request).first<COMMITMENT_BYTES>().begin());
    prove_issue_request(std::span(request).last<ISSUE_PROOF_BYTES>(), c, rand.nf, t_init, ctx_iss,
                        rand.r, rand.rho);
    return {TokenAccess::make_pending_token(rand.nf, rand.r, t_init, c), request};
}

IssueRequestResult issue_request(Credits t_init, const Context& ctx_iss) {
    check_t_init(t_init);
    return detail::issue_request_with_seed(t_init, ctx_iss, random_bytes<SEED_BYTES>());
}

std::optional<IssueResponse> issue_response(const uov::SecretKey& sk, const IssueRequest& request,
                                            Credits t_init, const Context& ctx_iss) {
    check_t_init(t_init);
    Commitment c;
    std::ranges::copy(std::span(request).first<COMMITMENT_BYTES>(), c.begin());

    if (!detail::verify_issue_proof(std::span(request).last<ISSUE_PROOF_BYTES>(), c, t_init,
                                    ctx_iss)) {
        return std::nullopt;
    }
    return sk.derive_preimage(tag(c, 0));
}

std::optional<Token> PendingToken::finalize_issue(const uov::PublicKey& pk,
                                                  const IssueResponse& response) && {
    if (!impl_) {
        throw std::logic_error("Ratatouille: pending token was moved from");
    }
    const std::unique_ptr<Impl> impl = std::move(impl_);

    if (pk.eval(response) != tag(impl->c, 0)) {
        return std::nullopt;
    }
    return Token(std::make_unique<Token::Impl>(
        Token::Impl{impl->nf, impl->t_init, impl->r, /* x */ 0, response}));
}

// Spending

struct PendingSpend::Impl {
    Nullifier nf; // nf'
    Credits t;    // t'
    Opening r;    // r'
    Commitment c; // c' = Com(nf', ctx_iss, t', r')
};

PendingSpend::PendingSpend(std::unique_ptr<Impl> impl) : impl_(std::move(impl)) {}
PendingSpend::PendingSpend(PendingSpend&&) noexcept = default;
PendingSpend& PendingSpend::operator=(PendingSpend&&) noexcept = default;
PendingSpend::~PendingSpend() = default;

SpendRequestResult detail::spend_request_with_seed(Token&& token, const uov::PublicKey& pk,
                                                   Credits d, const Context& ctx_iss,
                                                   const Seed& seed) {
    const Nullifier& nf = TokenAccess::nf(token); // throws if the token was moved from
    const Opening& r = TokenAccess::r(token);
    const uov::Preimage& s = TokenAccess::s(token);
    const Credits t = token.credit();
    const Credits x = token.refund();

    // The prover requires a valid witness. (A proof for an invalid one wouldn't verify anyway.)
    if (pk.eval(s) != tag(commit(nf, ctx_iss, t, r), x)) {
        throw std::invalid_argument(
            "Ratatouille: token wasn't issued by this Issuer for this issuance context");
    }

    // The change is t' = t + x - d, which must be a credit value. t + x may overflow, in which
    // case the true sum is 2^64 + lo.
    const Credits lo = t + x;
    const bool overflow = lo < t;
    if (!overflow && d > lo) {
        throw std::invalid_argument("Ratatouille: insufficient balance");
    }
    if (overflow && d <= lo) {
        throw std::invalid_argument("Ratatouille: change exceeds the largest credit value");
    }
    const Credits t_next = lo - d; // mod 2^64

    // The arguments are valid, so consume the token. (The references above remain valid, since the
    // contents live on the heap and are now owned by `consumed`.)
    const Token consumed = std::move(token);

    const auto rand = expand_seed<SpendRelation>(RATATOUILLE_SPEND_SEED_DST, seed);
    const Commitment c_next = commit(rand.nf, ctx_iss, t_next, rand.r);

    SpendRequest request;
    std::ranges::copy(nf, request.begin() + REQ_OFF_NF);
    std::ranges::copy(encode_credits(d), request.begin() + REQ_OFF_D);
    std::ranges::copy(c_next, request.begin() + REQ_OFF_C_NEXT);
    prove_spend_request(std::span(request).last<SPEND_PROOF_BYTES>(), pk,
                        {nf, t, r, x, s, rand.nf, t_next, rand.r}, d, c_next, ctx_iss, rand.rho);

    return {TokenAccess::make_pending_spend(rand.nf, t_next, rand.r, c_next), request};
}

SpendRequestResult Token::spend_request(const uov::PublicKey& pk, Credits d,
                                        const Context& ctx_iss) && {
    if (!impl_) {
        throw std::logic_error("Ratatouille: token was moved from");
    }
    return detail::spend_request_with_seed(std::move(*this), pk, d, ctx_iss,
                                           random_bytes<SEED_BYTES>());
}

std::optional<SpendResponseResult> spend_response(const uov::SecretKey& sk,
                                                  const SpendRequest& request,
                                                  const Context& ctx_iss, Credits refund) {
    // Parse the request nf || <d>_L || c' || pf_spend. (d is in range by construction.)
    SpendResponseResult out;
    std::copy_n(request.begin() + REQ_OFF_NF, NF_BYTES, out.nf.begin());
    out.d = decode_credits(std::span(request).subspan<REQ_OFF_D, CREDIT_BYTES>());
    Commitment c_next;
    std::copy_n(request.begin() + REQ_OFF_C_NEXT, COMMITMENT_BYTES, c_next.begin());

    // Verify the spend proof.
    if (!detail::verify_spend_proof(std::span(request).last<SPEND_PROOF_BYTES>(),
                                    sk.expanded_public_key(), out.nf, out.d, c_next, ctx_iss)) {
        return std::nullopt;
    }

    // Sign the updated state with the refund.
    std::ranges::copy(encode_credits(refund), out.response.begin() + RESP_OFF_X);
    std::ranges::copy(sk.derive_preimage(tag(c_next, refund)), out.response.begin() + RESP_OFF_S);
    return out;
}

std::optional<Token> PendingSpend::finalize_spend(const uov::PublicKey& pk,
                                                  const SpendResponse& response) && {
    if (!impl_) {
        throw std::logic_error("Ratatouille: pending spend was moved from");
    }
    const std::unique_ptr<Impl> impl = std::move(impl_);

    const Credits x_next = decode_credits(std::span(response).subspan<RESP_OFF_X, CREDIT_BYTES>());
    uov::Preimage s_next;
    std::copy_n(response.begin() + RESP_OFF_S, uov::N, s_next.begin());

    if (pk.eval(s_next) != tag(impl->c, x_next)) {
        return std::nullopt;
    }

    return Token(
        std::make_unique<Token::Impl>(Token::Impl{impl->nf, impl->t, impl->r, x_next, s_next}));
}

// Internal access

Token detail::TokenAccess::make_token(const Nullifier& nf, Credits t, const Opening& r, Credits x,
                                      const uov::Preimage& s) {
    return Token(std::make_unique<Token::Impl>(Token::Impl{nf, t, r, x, s}));
}

PendingToken detail::TokenAccess::make_pending_token(const Nullifier& nf, const Opening& r,
                                                     Credits t_init, const Commitment& c) {
    return PendingToken(std::make_unique<PendingToken::Impl>(PendingToken::Impl{nf, r, t_init, c}));
}

PendingSpend detail::TokenAccess::make_pending_spend(const Nullifier& nf, Credits t,
                                                     const Opening& r, const Commitment& c) {
    return PendingSpend(std::make_unique<PendingSpend::Impl>(PendingSpend::Impl{nf, t, r, c}));
}

const Token& detail::TokenAccess::checked(const Token& token) {
    if (!token.impl_) {
        throw std::logic_error("Ratatouille: token was moved from");
    }
    return token;
}

const PendingToken& detail::TokenAccess::checked(const PendingToken& pending_token) {
    if (!pending_token.impl_) {
        throw std::logic_error("Ratatouille: pending token was moved from");
    }
    return pending_token;
}

const PendingSpend& detail::TokenAccess::checked(const PendingSpend& pending_spend) {
    if (!pending_spend.impl_) {
        throw std::logic_error("Ratatouille: pending spend was moved from");
    }
    return pending_spend;
}

Token detail::TokenAccess::copy(const Token& token) {
    return Token(std::make_unique<Token::Impl>(*checked(token).impl_));
}

PendingToken detail::TokenAccess::copy(const PendingToken& pending_token) {
    return PendingToken(std::make_unique<PendingToken::Impl>(*checked(pending_token).impl_));
}

PendingSpend detail::TokenAccess::copy(const PendingSpend& pending_spend) {
    return PendingSpend(std::make_unique<PendingSpend::Impl>(*checked(pending_spend).impl_));
}

const Nullifier& detail::TokenAccess::nf(const Token& token) { return checked(token).impl_->nf; }
const Opening& detail::TokenAccess::r(const Token& token) { return checked(token).impl_->r; }
const uov::Preimage& detail::TokenAccess::s(const Token& token) { return checked(token).impl_->s; }

const Nullifier& detail::TokenAccess::nf(const PendingToken& pending_token) {
    return checked(pending_token).impl_->nf;
}
const Opening& detail::TokenAccess::r(const PendingToken& pending_token) {
    return checked(pending_token).impl_->r;
}

const Nullifier& detail::TokenAccess::nf(const PendingSpend& pending_spend) {
    return checked(pending_spend).impl_->nf;
}
Credits detail::TokenAccess::t(const PendingSpend& pending_spend) {
    return checked(pending_spend).impl_->t;
}
const Opening& detail::TokenAccess::r(const PendingSpend& pending_spend) {
    return checked(pending_spend).impl_->r;
}

} // namespace vole_mole::ratatouille
