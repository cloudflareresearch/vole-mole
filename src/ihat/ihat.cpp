#include "vole_mole/ihat.hpp"

#include "vole_mole/keccak.hpp"
#include "vole_mole/random.hpp"
#include "vole_mole/uov.hpp"

#include "ct.hpp"
#include "dst.hpp"
#include "ihat/commit.hpp"
#include "ihat/issue.hpp"
#include "ihat/redeem.hpp"
#include "ihat/seeded.hpp"
#include "ihat/token.hpp"
#include "ihat/unbound_issue.hpp"
#include "ihat/unbound_redeem.hpp"
#include "uov/public_key.hpp"
#include "voleith.hpp"

#include "hash.hpp"       // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt

extern "C" {
#include "KeccakHash.h" // from xkcp
}

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <memory>
#include <optional>
#include <span>
#include <stdexcept>
#include <utility>
#include <vector>

namespace vole_mole::ihat {

using detail::commit;
using detail::Commitment;
using detail::IssueRelation;
using detail::NfKey;
using detail::Opening;
using detail::RedeemRelation;
using detail::Seed;
using detail::SEED_BYTES;
using detail::TokenAccess;
using detail::unbound_commit;
using detail::UnboundIssueRelation;
using detail::UnboundRedeemRelation;
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
    xof.update(IHAT_ISSUE_SEED_DST);
    xof.update(seed);

    IssueRandomness rand;
    Keccak_HashFinal(&xof.ctx, nullptr);
    Keccak_HashSqueeze(&xof.ctx, rand.nf.data(), 8 * rand.nf.size());
    Keccak_HashSqueeze(&xof.ctx, rand.r.data(), 8 * rand.r.size());
    Keccak_HashSqueeze(&xof.ctx, rand.rho.data(), 8 * rand.rho.size());
    return rand;
}

struct UnboundIssueRandomness {
    NfKey nf_key;
    Opening r;
    ProveSeed<UnboundIssueRelation> rho;
};

// Expand `seed` into the unbound issue request randomness.
UnboundIssueRandomness expand_unbound_issue_seed(const Seed& seed) {
    static_assert(UnboundIssueRelation::params::secpar_v == faest::secpar::s128);
    faest::hash_state xof;
    xof.init(faest::secpar::s128);
    xof.update(UNBOUND_IHAT_ISSUE_SEED_DST);
    xof.update(seed);

    UnboundIssueRandomness rand;
    Keccak_HashFinal(&xof.ctx, nullptr);
    Keccak_HashSqueeze(&xof.ctx, rand.nf_key.data(), 8 * rand.nf_key.size());
    Keccak_HashSqueeze(&xof.ctx, rand.r.data(), 8 * rand.r.size());
    Keccak_HashSqueeze(&xof.ctx, rand.rho.data(), 8 * rand.rho.size());
    return rand;
}

// Expand `seed` into the redeem request randomness for the given relation.
template <typename Relation>
ProveSeed<Relation> expand_redeem_seed(const Seed& seed, std::span<const uint8_t> dst) {
    static_assert(Relation::params::secpar_v == faest::secpar::s128);
    faest::hash_state xof;
    xof.init(faest::secpar::s128);
    xof.update(dst);
    xof.update(seed);

    ProveSeed<Relation> rho;
    Keccak_HashFinal(&xof.ctx, nullptr);
    Keccak_HashSqueeze(&xof.ctx, rho.data(), 8 * rho.size());
    return rho;
}

// Find the index of the Anchor whose public map takes s to t, in constant time so that this doesn't
// leak the index.
//
// Throws std::invalid_argument if there's no such Anchor.
size_t find_issuer(const AnchorSet& anchors, const Commitment& t, const uov::Preimage& s) {
    size_t i = 0;
    uint64_t found = 0;
    for (size_t u = 0; u < anchors.size(); ++u) {
        const auto t_u = anchors[u].eval(s);
        uint64_t diff = 0;
        for (size_t j = 0; j < uov::M; ++j) {
            diff |= t[j] ^ t_u[j];
        }

        const auto matches = static_cast<size_t>(vole_mole::detail::ct_is_zero_mask(diff));
        i = (i & ~matches) | (u & matches);
        found |= matches;
    }
    if (!found) {
        throw std::invalid_argument("VOLE-IHAT: invalid token");
    }
    return i;
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
            "VOLE-IHAT: Anchor Set must have between 1 and MAX_ANCHORS keys");
    }

    for (size_t u = 0; u < keys_.size(); ++u) {
        for (size_t v = u + 1; v < keys_.size(); ++v) {
            if (PublicKeyAccess::digest(keys_[u]) == PublicKeyAccess::digest(keys_[v])) {
                throw std::invalid_argument("VOLE-IHAT: Anchor Set contains a key more than once");
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
        throw std::logic_error("VOLE-IHAT: pending token was moved from");
    }
    const std::unique_ptr<Impl> impl = std::move(impl_);

    if (pk.eval(response) != impl->t) {
        return std::nullopt;
    }

    return Token(std::make_unique<Token::Impl>(Token::Impl{impl->nf, impl->r, response}));
}

RedeemRequest detail::redeem_request_with_seed(Token&& token, const AnchorSet& anchors,
                                               const Context& ctx_iss, const Context& ctx_red,
                                               const ChallengeDigest& challenge_digest,
                                               const Seed& seed) {
    const Nullifier& nf = TokenAccess::nf(token); // throws if the token was moved from
    const Opening& r = TokenAccess::r(token);
    const uov::Preimage& s = TokenAccess::s(token);

    const size_t i = find_issuer(anchors, commit(nf, ctx_iss, ctx_red, r), s);

    // The arguments are valid, so consume the token.
    const Token consumed = std::move(token);

    RedeemRequest request;
    std::ranges::copy(nf, std::span(request).first<NF_BYTES>().begin());
    prove_redeem_request(std::span(request).last<REDEEM_PROOF_BYTES>(), anchors.keys(), i, nf,
                         ctx_iss, ctx_red, challenge_digest, r, s,
                         expand_redeem_seed<RedeemRelation>(seed, IHAT_REDEEM_SEED_DST));
    return request;
}

RedeemRequest Token::redeem_request(const AnchorSet& anchors, const Context& ctx_iss,
                                    const Context& ctx_red,
                                    const ChallengeDigest& challenge_digest) && {
    if (!impl_) {
        throw std::logic_error("VOLE-IHAT: token was moved from");
    }
    return detail::redeem_request_with_seed(std::move(*this), anchors, ctx_iss, ctx_red,
                                            challenge_digest, random_bytes<SEED_BYTES>());
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
        throw std::logic_error("VOLE-IHAT: token was moved from");
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
        throw std::logic_error("VOLE-IHAT: pending token was moved from");
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
                                         const Context& ctx_iss, const Context& ctx_red,
                                         const ChallengeDigest& challenge_digest) {
    Nullifier nf;
    std::ranges::copy(std::span(request).first<NF_BYTES>(), nf.begin());

    if (!detail::verify_redeem_proof(std::span(request).last<REDEEM_PROOF_BYTES>(), anchors.keys(),
                                     nf, ctx_iss, ctx_red, challenge_digest)) {
        return std::nullopt;
    }
    return nf;
}

Commitment detail::unbound_commit(const NfKey& nf_key, const Context& ctx_iss, const Opening& r) {
    const Kp800State out = keccak_p800(detail::encode_unbound_com_state(nf_key, ctx_iss, r));

    Commitment t;
    std::copy_n(out.begin(), t.size(), t.begin());
    return t;
}

Nullifier detail::derive(const NfKey& nf_key, const Context& ctx_red) {
    const Kp800State out = keccak_p800(detail::encode_derive_state(nf_key, ctx_red));

    Nullifier nf;
    std::copy_n(out.begin(), nf.size(), nf.begin());
    return nf;
}

struct PendingUnboundToken::Impl {
    NfKey nf_key;
    Opening r;
    Commitment t; // UnboundCom(nf_key, ctx_iss, r)
};

PendingUnboundToken::PendingUnboundToken(std::unique_ptr<Impl> impl) : impl_(std::move(impl)) {}
PendingUnboundToken::PendingUnboundToken(PendingUnboundToken&&) noexcept = default;
PendingUnboundToken& PendingUnboundToken::operator=(PendingUnboundToken&&) noexcept = default;
PendingUnboundToken::~PendingUnboundToken() = default;

UnboundIssueRequestResult detail::unbound_issue_request_with_seed(const Context& ctx_iss,
                                                                  const Seed& seed) {
    const UnboundIssueRandomness rand = expand_unbound_issue_seed(seed);

    const Commitment t = unbound_commit(rand.nf_key, ctx_iss, rand.r);
    UnboundIssueRequest request;
    std::ranges::copy(t, std::span(request).first<uov::M>().begin());
    prove_unbound_issue_request(std::span(request).last<UNBOUND_ISSUE_PROOF_BYTES>(), t,
                                rand.nf_key, ctx_iss, rand.r, rand.rho);
    return {TokenAccess::make_pending_unbound_token(rand.nf_key, rand.r, t), request};
}

UnboundIssueRequestResult unbound_issue_request(const Context& ctx_iss) {
    return detail::unbound_issue_request_with_seed(ctx_iss, random_bytes<SEED_BYTES>());
}

std::optional<IssueResponse> unbound_issue_response(const uov::SecretKey& sk,
                                                    const UnboundIssueRequest& request,
                                                    const Context& ctx_iss) {
    Commitment t;
    std::ranges::copy(std::span(request).first<uov::M>(), t.begin());

    if (!detail::verify_unbound_issue_proof(std::span(request).last<UNBOUND_ISSUE_PROOF_BYTES>(), t,
                                            ctx_iss)) {
        return std::nullopt;
    }
    return sk.derive_preimage(t);
}

struct UnboundToken::Impl {
    NfKey nf_key;
    Opening r;
    uov::Preimage s;
};

UnboundToken::UnboundToken(std::unique_ptr<Impl> impl) : impl_(std::move(impl)) {}
UnboundToken::UnboundToken(UnboundToken&&) noexcept = default;
UnboundToken& UnboundToken::operator=(UnboundToken&&) noexcept = default;
UnboundToken::~UnboundToken() = default;

std::optional<UnboundToken> PendingUnboundToken::finalize_issue(const uov::PublicKey& pk,
                                                                const IssueResponse& response) && {
    if (!impl_) {
        throw std::logic_error("VOLE-IHAT: pending token was moved from");
    }
    const std::unique_ptr<Impl> impl = std::move(impl_);

    if (pk.eval(response) != impl->t) {
        return std::nullopt;
    }

    return UnboundToken(
        std::make_unique<UnboundToken::Impl>(UnboundToken::Impl{impl->nf_key, impl->r, response}));
}

UnboundRedeemRequest detail::unbound_redeem_request_with_seed(
    const UnboundToken& token, const AnchorSet& anchors, const Context& ctx_iss,
    const Context& ctx_red, const ChallengeDigest& challenge_digest, const Seed& seed) {
    const NfKey& nf_key = TokenAccess::nf_key(token); // throws if the token was moved from
    const Opening& r = TokenAccess::r(token);
    const uov::Preimage& s = TokenAccess::s(token);

    const size_t i = find_issuer(anchors, unbound_commit(nf_key, ctx_iss, r), s);
    const Nullifier nf = derive(nf_key, ctx_red);

    UnboundRedeemRequest request;
    std::ranges::copy(nf, std::span(request).first<NF_BYTES>().begin());
    prove_unbound_redeem_request(
        std::span(request).last<UNBOUND_REDEEM_PROOF_BYTES>(), anchors.keys(), i, nf, ctx_iss,
        ctx_red, challenge_digest, nf_key, r, s,
        expand_redeem_seed<UnboundRedeemRelation>(seed, UNBOUND_IHAT_REDEEM_SEED_DST));
    return request;
}

UnboundRedeemRequest UnboundToken::redeem_request(const AnchorSet& anchors, const Context& ctx_iss,
                                                  const Context& ctx_red,
                                                  const ChallengeDigest& challenge_digest) const {
    if (!impl_) {
        throw std::logic_error("VOLE-IHAT: token was moved from");
    }
    return detail::unbound_redeem_request_with_seed(*this, anchors, ctx_iss, ctx_red,
                                                    challenge_digest, random_bytes<SEED_BYTES>());
}

UnboundToken detail::TokenAccess::make_unbound_token(const NfKey& nf_key, const Opening& r,
                                                     const uov::Preimage& s) {
    return UnboundToken(std::make_unique<UnboundToken::Impl>(UnboundToken::Impl{nf_key, r, s}));
}

PendingUnboundToken detail::TokenAccess::make_pending_unbound_token(const NfKey& nf_key,
                                                                    const Opening& r,
                                                                    const Commitment& t) {
    return PendingUnboundToken(
        std::make_unique<PendingUnboundToken::Impl>(PendingUnboundToken::Impl{nf_key, r, t}));
}

const UnboundToken& detail::TokenAccess::checked(const UnboundToken& token) {
    if (!token.impl_) {
        throw std::logic_error("VOLE-IHAT: token was moved from");
    }
    return token;
}

const PendingUnboundToken& detail::TokenAccess::checked(const PendingUnboundToken& pending_token) {
    if (!pending_token.impl_) {
        throw std::logic_error("VOLE-IHAT: pending token was moved from");
    }
    return pending_token;
}

UnboundToken detail::TokenAccess::copy(const UnboundToken& token) {
    return UnboundToken(std::make_unique<UnboundToken::Impl>(*checked(token).impl_));
}

PendingUnboundToken detail::TokenAccess::copy(const PendingUnboundToken& pending_token) {
    return PendingUnboundToken(
        std::make_unique<PendingUnboundToken::Impl>(*checked(pending_token).impl_));
}

const NfKey& detail::TokenAccess::nf_key(const UnboundToken& token) {
    return checked(token).impl_->nf_key;
}
const Opening& detail::TokenAccess::r(const UnboundToken& token) { return checked(token).impl_->r; }
const uov::Preimage& detail::TokenAccess::s(const UnboundToken& token) {
    return checked(token).impl_->s;
}

const NfKey& detail::TokenAccess::nf_key(const PendingUnboundToken& pending_token) {
    return checked(pending_token).impl_->nf_key;
}
const Opening& detail::TokenAccess::r(const PendingUnboundToken& pending_token) {
    return checked(pending_token).impl_->r;
}

std::optional<Nullifier> unbound_finalize_redeem(const AnchorSet& anchors,
                                                 const UnboundRedeemRequest& request,
                                                 const Context& ctx_iss, const Context& ctx_red,
                                                 const ChallengeDigest& challenge_digest) {
    Nullifier nf;
    std::ranges::copy(std::span(request).first<NF_BYTES>(), nf.begin());

    if (!detail::verify_unbound_redeem_proof(std::span(request).last<UNBOUND_REDEEM_PROOF_BYTES>(),
                                             anchors.keys(), nf, ctx_iss, ctx_red,
                                             challenge_digest)) {
        return std::nullopt;
    }
    return nf;
}

} // namespace vole_mole::ihat
