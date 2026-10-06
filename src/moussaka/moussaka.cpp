#include "vole_mole/moussaka.hpp"

#include "vole_mole/keccak.hpp"
#include "vole_mole/random.hpp"
#include "vole_mole/uov.hpp"

#include "dst.hpp"
#include "moussaka/commit.hpp"
#include "moussaka/issue.hpp"
#include "moussaka/redeem.hpp"
#include "moussaka/seeded.hpp"
#include "moussaka/token.hpp"
#include "uov/public_key.hpp"
#include "voleith.hpp"

#include "hash.hpp"       // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt

extern "C" {
#include "KeccakHash.h" // from xkcp
}

#include <algorithm>
#include <cstddef>
#include <initializer_list>
#include <memory>
#include <optional>
#include <span>
#include <stdexcept>
#include <utility>
#include <vector>

namespace vole_mole::moussaka {

using detail::commit;
using detail::Commitment;
using detail::IssueRelation;
using detail::Opening;
using detail::RedeemRelation;
using detail::Seed;
using detail::SEED_BYTES;
using detail::TokenAccess;
using uov::detail::PublicKeyAccess;

namespace {

using namespace vole_mole::detail;

struct IssueRandomness {
    Nullifier nf;
    Opening r;
    ProveSeed<IssueRelation> rho;
};

// Expand `seed` into the issue request randomness.
IssueRandomness expand_issue_seed(const Seed& seed) {
    static_assert(IssueRelation::params::secpar_v == faest::secpar::s128);
    faest::hash_state xof;
    xof.init(faest::secpar::s128);
    xof.update(MOUSSAKA_ISSUE_SEED_DST);
    xof.update(seed);

    IssueRandomness rand;
    Keccak_HashFinal(&xof.ctx, nullptr);
    Keccak_HashSqueeze(&xof.ctx, rand.nf.data(), 8 * rand.nf.size());
    Keccak_HashSqueeze(&xof.ctx, rand.r.data(), 8 * rand.r.size());
    Keccak_HashSqueeze(&xof.ctx, rand.rho.data(), 8 * rand.rho.size());
    return rand;
}

// Expand `seed` into the redeem request randomness.
ProveSeed<RedeemRelation> expand_redeem_seed(const Seed& seed) {
    static_assert(RedeemRelation::params::secpar_v == faest::secpar::s128);
    faest::hash_state xof;
    xof.init(faest::secpar::s128);
    xof.update(MOUSSAKA_REDEEM_SEED_DST);
    xof.update(seed);

    ProveSeed<RedeemRelation> rho;
    Keccak_HashFinal(&xof.ctx, nullptr);
    Keccak_HashSqueeze(&xof.ctx, rho.data(), 8 * rho.size());
    return rho;
}

} // namespace

Commitment detail::commit(const Nullifier& nf, const Context& ctx_iss, const Context& ctx_red,
                          const Opening& r) {
    const Kp800State out = keccak_p800(detail::encode_com_state(nf, ctx_iss, ctx_red, r));

    Commitment t;
    std::copy_n(out.begin(), t.size(), t.begin());
    return t;
}

struct PendingToken::Impl {
    Nullifier nf;
    Opening r;
    Context ctx_iss;
    Context ctx_red;
    Commitment t; // Com(nf, ctx_iss, ctx_red, r)
};

PendingToken::PendingToken(std::unique_ptr<Impl> impl) : impl_(std::move(impl)) {}
PendingToken::PendingToken(PendingToken&&) noexcept = default;
PendingToken& PendingToken::operator=(PendingToken&&) noexcept = default;
PendingToken::~PendingToken() = default;

IssueRequestResult detail::issue_request_with_seed(const Context& ctx_iss, const Context& ctx_red,
                                                   const Seed& seed) {
    const IssueRandomness rand = expand_issue_seed(seed);

    const Commitment t = commit(rand.nf, ctx_iss, ctx_red, rand.r);
    IssueRequest request;
    std::ranges::copy(t, std::span(request).first<uov::M>().begin());
    prove_issue_request(std::span(request).last<ISSUE_PROOF_BYTES>(), t, rand.nf, ctx_iss, ctx_red,
                        rand.r, rand.rho);
    return {TokenAccess::make_pending_token(rand.nf, rand.r, ctx_iss, ctx_red, t), request};
}

IssueRequestResult issue_request(const Context& ctx_iss, const Context& ctx_red) {
    return detail::issue_request_with_seed(ctx_iss, ctx_red, random_bytes<SEED_BYTES>());
}

std::optional<IssueResponse> issue_response(const uov::SecretKey& sk, const IssueRequest& request,
                                            const Context& ctx_iss) {
    Commitment t;
    std::ranges::copy(std::span(request).first<uov::M>(), t.begin());

    if (!detail::verify_issue_proof(std::span(request).last<ISSUE_PROOF_BYTES>(), t, ctx_iss)) {
        return std::nullopt;
    }
    return sk.derive_preimage(t);
}

AnchorSet::AnchorSet(std::span<const AnchorRef> keys) : keys_(keys.begin(), keys.end()) {
    if (keys_.empty() || keys_.size() > MAX_ANCHORS) {
        throw std::invalid_argument(
            "Moussaka: Anchor Set must have between 1 and MAX_ANCHORS keys");
    }

    for (size_t u = 0; u < keys_.size(); ++u) {
        for (size_t v = u + 1; v < keys_.size(); ++v) {
            if (PublicKeyAccess::digest(keys_[u]) == PublicKeyAccess::digest(keys_[v])) {
                throw std::invalid_argument("Moussaka: Anchor Set contains a key more than once");
            }
        }
    }
}

AnchorSet::AnchorSet(std::span<const uov::PublicKey> keys)
    : AnchorSet(std::vector<AnchorRef>(keys.begin(), keys.end())) {}

AnchorSet::AnchorSet(std::initializer_list<AnchorRef> keys)
    : AnchorSet(std::span<const AnchorRef>(keys.begin(), keys.size())) {}

struct Token::Impl {
    Nullifier nf;
    Opening r;
    uov::Preimage s;
};

Token::Token(std::unique_ptr<Impl> impl) : impl_(std::move(impl)) {}
Token::Token(Token&&) noexcept = default;
Token& Token::operator=(Token&&) noexcept = default;
Token::~Token() = default;

std::optional<Token> PendingToken::finalize_issue(const uov::PublicKey& pk,
                                                  const IssueResponse& response) && {
    if (!impl_) {
        throw std::logic_error("Moussaka: pending token was moved from");
    }
    const std::unique_ptr<Impl> impl = std::move(impl_);

    if (pk.eval(response) != impl->t) {
        return std::nullopt;
    }

    return Token(std::make_unique<Token::Impl>(Token::Impl{impl->nf, impl->r, response}));
}

RedeemRequest detail::redeem_request_with_seed(Token&& token, const AnchorSet& anchors, size_t i,
                                               const Context& ctx_iss, const Context& ctx_red,
                                               const Seed& seed) {
    const Nullifier& nf = TokenAccess::nf(token); // throws if the token was moved from
    const Opening& r = TokenAccess::r(token);
    const uov::Preimage& s = TokenAccess::s(token);

    if (i >= anchors.size()) {
        throw std::invalid_argument("Moussaka: Anchor index is out of range");
    }

    // The prover requires a valid witness. (A proof for an invalid one wouldn't verify anyway.)
    if (anchors[i].eval(s) != commit(nf, ctx_iss, ctx_red, r)) {
        throw std::invalid_argument("Moussaka: token wasn't issued by this Anchor for this "
                                    "issuance and redemption context");
    }

    // The arguments are valid, so consume the token.
    const Token consumed = std::move(token);

    RedeemRequest request;
    std::ranges::copy(nf, std::span(request).first<NF_BYTES>().begin());
    prove_redeem_request(std::span(request).last<REDEEM_PROOF_BYTES>(), anchors.keys(), i, nf,
                         ctx_iss, ctx_red, r, s, expand_redeem_seed(seed));
    return request;
}

RedeemRequest Token::redeem_request(const AnchorSet& anchors, size_t i, const Context& ctx_iss,
                                    const Context& ctx_red) && {
    if (!impl_) {
        throw std::logic_error("Moussaka: token was moved from");
    }
    return detail::redeem_request_with_seed(std::move(*this), anchors, i, ctx_iss, ctx_red,
                                            random_bytes<SEED_BYTES>());
}

Token detail::TokenAccess::make_token(const Nullifier& nf, const Opening& r,
                                      const uov::Preimage& s) {
    return Token(std::make_unique<Token::Impl>(Token::Impl{nf, r, s}));
}

PendingToken detail::TokenAccess::make_pending_token(const Nullifier& nf, const Opening& r,
                                                     const Context& ctx_iss, const Context& ctx_red,
                                                     const Commitment& t) {
    return PendingToken(
        std::make_unique<PendingToken::Impl>(PendingToken::Impl{nf, r, ctx_iss, ctx_red, t}));
}

const Token& detail::TokenAccess::checked(const Token& token) {
    if (!token.impl_) {
        throw std::logic_error("Moussaka: token was moved from");
    }
    return token;
}

Token detail::TokenAccess::copy(const Token& token) {
    return Token(std::make_unique<Token::Impl>(*checked(token).impl_));
}

PendingToken detail::TokenAccess::copy(const PendingToken& pending_token) {
    return PendingToken(std::make_unique<PendingToken::Impl>(*checked(pending_token).impl_));
}

const PendingToken& detail::TokenAccess::checked(const PendingToken& pending_token) {
    if (!pending_token.impl_) {
        throw std::logic_error("Moussaka: pending token was moved from");
    }
    return pending_token;
}

const Nullifier& detail::TokenAccess::nf(const PendingToken& pending_token) {
    return checked(pending_token).impl_->nf;
}
const Opening& detail::TokenAccess::r(const PendingToken& pending_token) {
    return checked(pending_token).impl_->r;
}

const Nullifier& detail::TokenAccess::nf(const Token& token) { return checked(token).impl_->nf; }
const Opening& detail::TokenAccess::r(const Token& token) { return checked(token).impl_->r; }
const uov::Preimage& detail::TokenAccess::s(const Token& token) { return checked(token).impl_->s; }

std::optional<Nullifier> finalize_redeem(const AnchorSet& anchors, const RedeemRequest& request,
                                         const Context& ctx_iss, const Context& ctx_red) {
    Nullifier nf;
    std::ranges::copy(std::span(request).first<NF_BYTES>(), nf.begin());

    if (!detail::verify_redeem_proof(std::span(request).last<REDEEM_PROOF_BYTES>(), anchors.keys(),
                                     nf, ctx_iss, ctx_red)) {
        return std::nullopt;
    }
    return nf;
}

} // namespace vole_mole::moussaka
