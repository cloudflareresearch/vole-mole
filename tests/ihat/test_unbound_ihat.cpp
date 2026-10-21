// Tests for the issuance and redemption of unbound tokens.

#include "vole_mole/ihat.hpp"
#include "vole_mole/uov.hpp"

#include "ihat/commit.hpp"         // internal
#include "ihat/seeded.hpp"         // internal
#include "ihat/token.hpp"          // internal
#include "ihat/unbound_issue.hpp"  // internal
#include "ihat/unbound_redeem.hpp" // internal

#include "test.hpp"

#include "faest_sig.hpp" // from faest-arch-opt

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <istream>
#include <optional>
#include <span>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::ihat;
using vole_mole::ihat::detail::Commitment;
using vole_mole::ihat::detail::derive;
using vole_mole::ihat::detail::NfKey;
using vole_mole::ihat::detail::Opening;
using vole_mole::ihat::detail::Seed;
using vole_mole::ihat::detail::SEED_BYTES;
using vole_mole::ihat::detail::TokenAccess;
using vole_mole::ihat::detail::unbound_commit;
using vole_mole::ihat::detail::unbound_issue_request_with_seed;
using vole_mole::ihat::detail::unbound_redeem_request_with_seed;
using vole_mole::test::filled;
using vole_mole::test::read_kat_field;
using vole_mole::test::read_kat_number;
using vole_mole::test::to_hex;
using vole_mole::test::uov_key_pair;
using vole_mole::test::UovKeyPair;

namespace {

const Context CTX_ISS = filled<CTX_BYTES>(0x10);
const Context CTX_RED = filled<CTX_BYTES>(0x20);
const ChallengeDigest CHALLENGE_DIGEST = filled<CHALLENGE_DIGEST_BYTES>(0x70);
const Seed SEED = filled<SEED_BYTES>(0x50);

UnboundIssueRequestResult make_request(const Seed& seed = SEED) {
    return unbound_issue_request_with_seed(CTX_ISS, seed);
}

// Whether an Anchor accepts the issue request.
bool verifies(const UnboundIssueRequest& request, const Context& ctx_iss) {
    return unbound_issue_response(uov_key_pair().sk, request, ctx_iss).has_value();
}

} // namespace

// Freeze both witness layouts and the complete deterministic protocol transcript, including
// redemption of the same token for several redemption contexts. Verification of the stored
// messages also catches changes that break compatibility with existing proofs.
TEST(IhatUnbound, KnownAnswers) {
    std::ifstream in(std::string(VOLE_MOLE_TEST_DATA_DIR) + "/ihat/unbound_ihat_kat.txt");
    ASSERT_TRUE(in.is_open()) << "can't open ihat/unbound_ihat_kat.txt";
    size_t count = 0;
    while (in >> std::ws && in.peek() != std::char_traits<char>::eof()) {
        if (in.peek() == '#') {
            std::string comment;
            std::getline(in, comment);
            continue;
        }
        SCOPED_TRACE("known answer " + std::to_string(count));
        Seed issue_seed;
        Context ctx_iss;
        NfKey nf_key;
        Opening r;
        Commitment commitment;
        std::array<uint8_t, ihat::detail::UNBOUND_ISSUE_WITNESS_BYTES> issue_witness;
        UnboundIssueRequest request;
        IssueResponse response;
        size_t anchor_count, issuer, redemption_count;
        ASSERT_TRUE(read_kat_field(in, "issue_seed", issue_seed));
        ASSERT_TRUE(read_kat_field(in, "ctx_iss", ctx_iss));
        ASSERT_TRUE(read_kat_number(in, "anchor_count", anchor_count));
        ASSERT_GE(anchor_count, 1u);
        ASSERT_LE(anchor_count, MAX_ANCHORS);
        ASSERT_TRUE(read_kat_number(in, "issuer", issuer));
        ASSERT_LT(issuer, anchor_count);
        std::vector<UovKeyPair> key_pairs;
        key_pairs.reserve(anchor_count);
        for (size_t u = 0; u < anchor_count; ++u) {
            uov::SecretKeyBytes sk;
            ASSERT_TRUE(read_kat_field(in, "anchor_sk", sk));
            key_pairs.emplace_back(uov::SecretKey{sk});
        }
        std::vector<AnchorRef> refs;
        for (const auto& kp : key_pairs) {
            refs.emplace_back(kp.pk);
        }
        const AnchorSet anchors(refs);
        ASSERT_TRUE(read_kat_field(in, "nf_key", nf_key));
        ASSERT_TRUE(read_kat_field(in, "r", r));
        ASSERT_TRUE(read_kat_field(in, "commitment", commitment));
        ASSERT_TRUE(read_kat_field(in, "issue_witness", issue_witness));
        ASSERT_TRUE(read_kat_field(in, "issue_request", request));
        ASSERT_TRUE(read_kat_field(in, "issue_response", response));

        auto res = unbound_issue_request_with_seed(ctx_iss, issue_seed);
        EXPECT_EQ(TokenAccess::nf_key(res.pending_token), nf_key);
        EXPECT_EQ(TokenAccess::r(res.pending_token), r);
        EXPECT_EQ(ihat::detail::encode_unbound_issue_witness(nf_key, ctx_iss, r), issue_witness);
        EXPECT_EQ(unbound_commit(nf_key, ctx_iss, r), commitment);
        EXPECT_EQ(to_hex(commitment), to_hex(std::span(request).first<uov::M>()));
        EXPECT_TRUE(std::ranges::equal(res.request, request)) << "request bytes differ";

        const auto generated_response =
            unbound_issue_response(key_pairs[issuer].sk, res.request, ctx_iss);
        ASSERT_TRUE(generated_response.has_value());
        EXPECT_EQ(*generated_response, response);
        // Verify the stored issuance proof independently of the regenerated request.
        const auto stored_response = unbound_issue_response(key_pairs[issuer].sk, request, ctx_iss);
        ASSERT_TRUE(stored_response.has_value());
        EXPECT_EQ(*stored_response, response);
        EXPECT_EQ(key_pairs[issuer].pk.eval(response), commitment);

        auto token = std::move(res.pending_token).finalize_issue(key_pairs[issuer].pk, response);
        ASSERT_TRUE(token.has_value());
        EXPECT_EQ(TokenAccess::nf_key(*token), nf_key);
        EXPECT_EQ(TokenAccess::r(*token), r);
        EXPECT_EQ(TokenAccess::s(*token), response);

        ASSERT_TRUE(read_kat_number(in, "redemption_count", redemption_count));
        ASSERT_GE(redemption_count, 1u);
        for (size_t j = 0; j < redemption_count; ++j) {
            SCOPED_TRACE("redemption " + std::to_string(j));
            Seed redeem_seed;
            Context ctx_red;
            ChallengeDigest challenge_digest;
            Nullifier nf;
            std::array<uint8_t, ihat::detail::UNBOUND_REDEEM_WITNESS_BYTES> redeem_witness;
            UnboundRedeemRequest redeem_request;
            ASSERT_TRUE(read_kat_field(in, "redeem_seed", redeem_seed));
            ASSERT_TRUE(read_kat_field(in, "ctx_red", ctx_red));
            ASSERT_TRUE(read_kat_field(in, "challenge_digest", challenge_digest));
            ASSERT_TRUE(read_kat_field(in, "nf", nf));
            ASSERT_TRUE(read_kat_field(in, "redeem_witness", redeem_witness));
            ASSERT_TRUE(read_kat_field(in, "redeem_request", redeem_request));

            EXPECT_EQ(derive(nf_key, ctx_red), nf);
            EXPECT_EQ(ihat::detail::encode_unbound_redeem_witness(nf_key, ctx_iss, ctx_red, r,
                                                                  response, issuer),
                      redeem_witness);
            const auto generated_redemption = unbound_redeem_request_with_seed(
                *token, anchors, ctx_iss, ctx_red, challenge_digest, redeem_seed);
            EXPECT_TRUE(std::ranges::equal(generated_redemption, redeem_request))
                << "redemption request bytes differ";
            EXPECT_EQ(to_hex(std::span(redeem_request).first<NF_BYTES>()), to_hex(nf));
            const auto generated_nf = unbound_finalize_redeem(anchors, generated_redemption,
                                                              ctx_iss, ctx_red, challenge_digest);
            ASSERT_TRUE(generated_nf.has_value());
            EXPECT_EQ(*generated_nf, nf);
            // Verify the stored redemption proof even if regeneration changes its bytes.
            const auto stored_nf = unbound_finalize_redeem(anchors, redeem_request, ctx_iss,
                                                           ctx_red, challenge_digest);
            ASSERT_TRUE(stored_nf.has_value());
            EXPECT_EQ(*stored_nf, nf);
        }
        ++count;
    }
    EXPECT_EQ(count, 3u);
}

TEST(UnboundIssueRequest, Verifies) {
    const auto res = make_request();
    EXPECT_TRUE(verifies(res.request, CTX_ISS));
    EXPECT_EQ(to_hex(std::span(res.request).first<uov::M>()),
              to_hex(unbound_commit(TokenAccess::nf_key(res.pending_token), CTX_ISS,
                                    TokenAccess::r(res.pending_token))));
}

TEST(UnboundIssueRequest, RandomizedVerifies) {
    const auto res = unbound_issue_request(CTX_ISS);
    EXPECT_TRUE(verifies(res.request, CTX_ISS));
    EXPECT_EQ(to_hex(std::span(res.request).first<uov::M>()),
              to_hex(unbound_commit(TokenAccess::nf_key(res.pending_token), CTX_ISS,
                                    TokenAccess::r(res.pending_token))));
}

TEST(UnboundIssueRequest, IsDeterministicGivenSeed) {
    const auto a = make_request();
    const auto b = make_request();
    EXPECT_EQ(TokenAccess::nf_key(a.pending_token), TokenAccess::nf_key(b.pending_token));
    EXPECT_EQ(TokenAccess::r(a.pending_token), TokenAccess::r(b.pending_token));
    EXPECT_TRUE(std::ranges::equal(a.request, b.request));

    // A different seed changes all of the randomness.
    const auto c = make_request(filled<SEED_BYTES>(0x99));
    EXPECT_NE(TokenAccess::nf_key(a.pending_token), TokenAccess::nf_key(c.pending_token));
    EXPECT_NE(TokenAccess::r(a.pending_token), TokenAccess::r(c.pending_token));
    EXPECT_FALSE(std::ranges::equal(std::span(a.request).first<uov::M>(),
                                    std::span(c.request).first<uov::M>()));
    EXPECT_FALSE(std::ranges::equal(std::span(a.request).last<UNBOUND_ISSUE_PROOF_BYTES>(),
                                    std::span(c.request).last<UNBOUND_ISSUE_PROOF_BYTES>()));
    EXPECT_TRUE(verifies(c.request, CTX_ISS));
}

// Known answer for the seed expansion: nf_key || r are the first 32 bytes of
// SHAKE128("mous" || UNBOUND_VERSION || "s0" || seed). Generated with Python:
//
//   hashlib.shake_128(b"mous" + bytes([1]) + b"s0" + bytes(range(0x50, 0x70))).digest(32)
TEST(UnboundIssueRequest, SeedExpansion) {
    const auto res = make_request(); // with SEED = 0x50, 0x51, ..., 0x6f
    EXPECT_EQ(to_hex(TokenAccess::nf_key(res.pending_token)), "c69776951efe0050355e7d494d51e877");
    EXPECT_EQ(to_hex(TokenAccess::r(res.pending_token)), "58762a3c0165aa296da5cd5708c18a38");
}

TEST(UnboundIssueRequest, RejectWrongCtxIss) {
    const auto res = make_request();
    Context ctx = CTX_ISS;
    ctx[5] ^= 1;
    EXPECT_FALSE(verifies(res.request, ctx));
}

TEST(UnboundIssueRequest, RejectWrongCommitment) {
    const auto res = make_request();
    UnboundIssueRequest req = res.request;
    req[0] ^= 0x80;
    EXPECT_FALSE(verifies(req, CTX_ISS));
}

// A commitment to different values (with a valid proof for those) doesn't transfer.
TEST(UnboundIssueRequest, RejectMismatchedProof) {
    const auto a = make_request();
    const auto b = unbound_issue_request(CTX_ISS);
    UnboundIssueRequest req = a.request;
    std::ranges::copy(std::span(b.request).last<UNBOUND_ISSUE_PROOF_BYTES>(),
                      std::span(req).last<UNBOUND_ISSUE_PROOF_BYTES>().begin());
    EXPECT_FALSE(verifies(req, CTX_ISS));
}

TEST(UnboundIssueRequest, RejectTamperedProof) {
    const auto res = make_request();
    UnboundIssueRequest req = res.request;
    auto proof = std::span(req).last<UNBOUND_ISSUE_PROOF_BYTES>();
    for (size_t i = 0; i < UNBOUND_ISSUE_PROOF_BYTES; i += 97) {
        proof[i] ^= 0x04;
        EXPECT_FALSE(verifies(req, CTX_ISS)) << "flipped a bit of byte " << i;
        proof[i] ^= 0x04;
    }
    // The last bytes are delta (chall_3), iv_pre and the grinding counter.
    for (size_t i = UNBOUND_ISSUE_PROOF_BYTES - 36; i < UNBOUND_ISSUE_PROOF_BYTES; ++i) {
        proof[i] ^= 0x01;
        EXPECT_FALSE(verifies(req, CTX_ISS)) << "flipped a bit of byte " << i;
        proof[i] ^= 0x01;
    }
    EXPECT_TRUE(verifies(req, CTX_ISS));
}

namespace {

// The Anchor Set used for redemption. The issuing Anchor is the fixed test key pair, at index
// ISSUER.
struct Anchors {
    UovKeyPair a{uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x61)}};
    UovKeyPair c{uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x62)}};
    AnchorSet keys{a.pk, uov_key_pair().pk, c.pk};
};
constexpr size_t ISSUER = 1;

const Anchors& anchors() {
    static const Anchors a;
    return a;
}

// An Anchor Set of size n with the issuer of `token()` at index i. The other Anchors are distinct
// keys.
AnchorSet anchor_set_with_issuer_at(size_t n, size_t i) {
    std::vector<AnchorRef> keys;
    for (size_t u = 0; u < n; ++u) {
        keys.emplace_back(u == i ? uov_key_pair().pk : vole_mole::test::distinct_uov_public_key(u));
    }
    return AnchorSet(keys);
}

// Run issuance with the fixed test key pair.
UnboundToken issue(const Seed& seed = SEED) {
    const auto& [pk, sk] = uov_key_pair();
    auto [pending, request] = unbound_issue_request_with_seed(CTX_ISS, seed);
    const auto response = unbound_issue_response(sk, request, CTX_ISS);
    EXPECT_TRUE(response.has_value());
    auto token = std::move(pending).finalize_issue(pk, *response);
    EXPECT_TRUE(token.has_value());
    return *std::move(token);
}

const UnboundToken& token() {
    static const UnboundToken t = issue();
    return t;
}

const Seed REDEEM_SEED = filled<SEED_BYTES>(0x90);

const UnboundRedeemRequest& redemption() {
    static const UnboundRedeemRequest req = unbound_redeem_request_with_seed(
        token(), anchors().keys, CTX_ISS, CTX_RED, CHALLENGE_DIGEST, REDEEM_SEED);
    return req;
}

std::optional<Nullifier> finalize(const UnboundRedeemRequest& req, const Context& ctx_red = CTX_RED,
                                  const ChallengeDigest& challenge_digest = CHALLENGE_DIGEST) {
    return unbound_finalize_redeem(anchors().keys, req, CTX_ISS, ctx_red, challenge_digest);
}

} // namespace

TEST(UnboundFinalizeIssue, ReturnsToken) {
    const auto& pk = uov_key_pair().pk;
    const auto res = make_request();
    const UnboundToken t = issue();
    const auto& nf_key = TokenAccess::nf_key(t);
    const auto& r = TokenAccess::r(t);
    EXPECT_EQ(nf_key, TokenAccess::nf_key(res.pending_token));
    EXPECT_EQ(r, TokenAccess::r(res.pending_token));
    EXPECT_EQ(to_hex(pk.eval(TokenAccess::s(t))), to_hex(unbound_commit(nf_key, CTX_ISS, r)));
}

// Each case consumes a pending token, so each uses a fresh copy of the same request (the request
// is deterministic given the seed).
TEST(UnboundFinalizeIssue, RejectsInvalidResponse) {
    const auto& [pk, sk] = uov_key_pair();
    const IssueResponse response = *unbound_issue_response(sk, make_request().request, CTX_ISS);

    // Wrong Anchor.
    EXPECT_FALSE(make_request().pending_token.finalize_issue(anchors().a.pk, response));

    // Tampered signature.
    IssueResponse bad = response;
    bad[0] ^= 1;
    EXPECT_FALSE(make_request().pending_token.finalize_issue(pk, bad));

    // Signature of a request for another issuance context, but with the same randomness.
    Context ctx = CTX_ISS;
    ctx[1] ^= 1;
    EXPECT_FALSE(
        unbound_issue_request_with_seed(ctx, SEED).pending_token.finalize_issue(pk, response));

    // Signature of another request.
    EXPECT_FALSE(make_request(filled<SEED_BYTES>(0x99)).pending_token.finalize_issue(pk, response));

    // The valid response.
    EXPECT_TRUE(make_request().pending_token.finalize_issue(pk, response));
}

// Finalizing issuance consumes the pending token, whether or not the response is valid.
TEST(UnboundFinalizeIssue, ConsumesPendingToken) {
    const auto& [pk, sk] = uov_key_pair();
    auto [pending, request] = make_request();
    const IssueResponse response = *unbound_issue_response(sk, request, CTX_ISS);

    IssueResponse bad = response;
    bad[0] ^= 1;
    EXPECT_FALSE(std::move(pending).finalize_issue(pk, bad));
    EXPECT_THROW((void)std::move(pending).finalize_issue(pk, response), std::logic_error);

    auto [pending2, request2] = make_request();
    EXPECT_TRUE(std::move(pending2).finalize_issue(pk, response));
    EXPECT_THROW((void)std::move(pending2).finalize_issue(pk, response), std::logic_error);
    EXPECT_THROW((void)TokenAccess::nf_key(pending2), std::logic_error);
}

TEST(UnboundRedeem, Verifies) {
    const auto nf = finalize(redemption());
    ASSERT_TRUE(nf.has_value());
    EXPECT_EQ(*nf, derive(TokenAccess::nf_key(token()), CTX_RED));
    EXPECT_EQ(to_hex(std::span(redemption()).first<NF_BYTES>()), to_hex(*nf));
}

TEST(UnboundRedeem, RandomizedVerifies) {
    const auto& [pk, sk] = uov_key_pair();
    auto [pending, request] = unbound_issue_request(CTX_ISS);
    const auto t =
        std::move(pending).finalize_issue(pk, *unbound_issue_response(sk, request, CTX_ISS));
    ASSERT_TRUE(t.has_value());
    const auto req = t->redeem_request(anchors().keys, CTX_ISS, CTX_RED, CHALLENGE_DIGEST);
    const auto nf = finalize(req);
    ASSERT_TRUE(nf.has_value());
    EXPECT_EQ(*nf, derive(TokenAccess::nf_key(*t), CTX_RED));
}

// Redemption doesn't consume the token. Redeeming it again for the same redemption context
// yields a fresh proof with the same nullifier, so the Moderator can detect the replay.
TEST(UnboundRedeem, DoesNotConsumeToken) {
    const auto req1 = token().redeem_request(anchors().keys, CTX_ISS, CTX_RED, CHALLENGE_DIGEST);
    const auto req2 = token().redeem_request(anchors().keys, CTX_ISS, CTX_RED, CHALLENGE_DIGEST);
    EXPECT_FALSE(std::ranges::equal(req1, req2));
    const auto nf1 = finalize(req1);
    const auto nf2 = finalize(req2);
    ASSERT_TRUE(nf1.has_value());
    ASSERT_TRUE(nf2.has_value());
    EXPECT_EQ(*nf1, *nf2);
    EXPECT_EQ(*nf1, *finalize(redemption()));
}

// The same token can be redeemed for several redemption contexts, with a different nullifier for
// each. Each request verifies only for its own redemption context.
TEST(UnboundRedeem, NullifierPerRedemptionContext) {
    std::vector<Context> contexts;
    std::vector<UnboundRedeemRequest> requests;
    std::vector<Nullifier> nullifiers;
    for (uint8_t k = 0; k < 3; ++k) {
        Context ctx_red = CTX_RED;
        ctx_red[k] ^= 0x01;
        contexts.push_back(ctx_red);
        requests.push_back(
            token().redeem_request(anchors().keys, CTX_ISS, ctx_red, CHALLENGE_DIGEST));
        const auto nf = finalize(requests.back(), ctx_red);
        ASSERT_TRUE(nf.has_value()) << "ctx_red " << unsigned{k};
        EXPECT_EQ(*nf, derive(TokenAccess::nf_key(token()), ctx_red));
        nullifiers.push_back(*nf);
    }
    for (size_t j = 0; j < contexts.size(); ++j) {
        EXPECT_NE(nullifiers[j], *finalize(redemption())) << j;
        for (size_t k = 0; k < contexts.size(); ++k) {
            if (j != k) {
                EXPECT_NE(nullifiers[j], nullifiers[k]) << j << ", " << k;
                EXPECT_FALSE(finalize(requests[j], contexts[k])) << j << ", " << k;
            }
        }
    }
}

// The issuing Anchor may be anywhere in the Anchor Set.
TEST(UnboundRedeem, VerifiesAtEveryPosition) {
    for (const size_t n : {size_t{1}, size_t{2}}) {
        for (size_t i = 0; i < n; ++i) {
            const AnchorSet keys = anchor_set_with_issuer_at(n, i);
            const auto req = unbound_redeem_request_with_seed(token(), keys, CTX_ISS, CTX_RED,
                                                              CHALLENGE_DIGEST, REDEEM_SEED);
            EXPECT_TRUE(unbound_finalize_redeem(keys, req, CTX_ISS, CTX_RED, CHALLENGE_DIGEST))
                << "n = " << n << ", i = " << i;
        }
    }
}

TEST(UnboundRedeem, VerifiesLargestAnchorSet) {
    const AnchorSet keys = anchor_set_with_issuer_at(MAX_ANCHORS, MAX_ANCHORS / 2);
    const auto req = unbound_redeem_request_with_seed(token(), keys, CTX_ISS, CTX_RED,
                                                      CHALLENGE_DIGEST, REDEEM_SEED);
    EXPECT_TRUE(unbound_finalize_redeem(keys, req, CTX_ISS, CTX_RED, CHALLENGE_DIGEST));
}

TEST(UnboundRedeem, IsDeterministicGivenSeed) {
    const auto& a = redemption();
    const auto b = unbound_redeem_request_with_seed(token(), anchors().keys, CTX_ISS, CTX_RED,
                                                    CHALLENGE_DIGEST, REDEEM_SEED);
    EXPECT_TRUE(std::ranges::equal(a, b));

    // A different seed yields a different proof for the same token.
    const auto c = unbound_redeem_request_with_seed(token(), anchors().keys, CTX_ISS, CTX_RED,
                                                    CHALLENGE_DIGEST, filled<SEED_BYTES>(0x91));
    EXPECT_FALSE(std::ranges::equal(a, c));
    EXPECT_TRUE(std::ranges::equal(std::span(a).first<NF_BYTES>(), std::span(c).first<NF_BYTES>()));
    EXPECT_TRUE(finalize(c));
}

TEST(UnboundRedeem, BindsChallengeDigest) {
    ChallengeDigest other = CHALLENGE_DIGEST;
    other.back() ^= 1;
    const auto req = unbound_redeem_request_with_seed(token(), anchors().keys, CTX_ISS, CTX_RED,
                                                      other, REDEEM_SEED);
    EXPECT_FALSE(std::ranges::equal(req, redemption()));
    EXPECT_EQ(finalize(req, CTX_RED, other), finalize(redemption()));
    EXPECT_FALSE(finalize(req));

    for (size_t i = 0; i < CHALLENGE_DIGEST_BYTES; ++i) {
        ChallengeDigest wrong = CHALLENGE_DIGEST;
        wrong[i] ^= 1;
        EXPECT_FALSE(finalize(redemption(), CTX_RED, wrong)) << "changed digest byte " << i;
    }
    EXPECT_TRUE(finalize(redemption()));
}

TEST(UnboundRedeem, RejectsWrongContext) {
    const auto& keys = anchors().keys;
    Context ctx = CTX_ISS;
    ctx[7] ^= 1;
    EXPECT_FALSE(unbound_finalize_redeem(keys, redemption(), ctx, CTX_RED, CHALLENGE_DIGEST));
    EXPECT_FALSE(unbound_finalize_redeem(keys, redemption(), CTX_ISS, ctx, CHALLENGE_DIGEST));
    EXPECT_FALSE(unbound_finalize_redeem(keys, redemption(), CTX_RED, CTX_ISS, CHALLENGE_DIGEST));
}

TEST(UnboundRedeem, RejectsWrongAnchorSet) {
    const auto& keys = anchors().keys;
    const uov::PublicKey& other = vole_mole::test::distinct_uov_public_key(0);
    const auto rejects = [](const AnchorSet& s) {
        return !unbound_finalize_redeem(s, redemption(), CTX_ISS, CTX_RED, CHALLENGE_DIGEST);
    };

    EXPECT_TRUE(rejects(AnchorSet({keys[0], keys[2]})));                 // issuer is missing
    EXPECT_TRUE(rejects(AnchorSet(keys.keys().first(ISSUER))));          // truncated
    EXPECT_TRUE(rejects(AnchorSet({keys[1], keys[0], keys[2]})));        // reordered
    EXPECT_TRUE(rejects(AnchorSet({keys[0], keys[1], keys[2], other}))); // added
    EXPECT_TRUE(rejects(AnchorSet({other, keys[1], keys[2]})));          // replaced
}

TEST(UnboundRedeem, RejectsWrongNullifier) {
    UnboundRedeemRequest req = redemption();
    req[0] ^= 1;
    EXPECT_FALSE(finalize(req));

    // The proof doesn't transfer to the same token's nullifier for another redemption context.
    Context ctx_red = CTX_RED;
    ctx_red[0] ^= 1;
    req = redemption();
    std::ranges::copy(derive(TokenAccess::nf_key(token()), ctx_red), req.begin());
    EXPECT_FALSE(finalize(req));
    EXPECT_FALSE(finalize(req, ctx_red));

    // Nor to another token's nullifier.
    const UnboundToken other = issue(filled<SEED_BYTES>(0x99));
    req = redemption();
    std::ranges::copy(derive(TokenAccess::nf_key(other), CTX_RED), req.begin());
    EXPECT_FALSE(finalize(req));
}

TEST(UnboundRedeem, RejectsTamperedProof) {
    UnboundRedeemRequest req = redemption();
    auto proof = std::span(req).last<UNBOUND_REDEEM_PROOF_BYTES>();
    for (size_t i = 0; i < UNBOUND_REDEEM_PROOF_BYTES; i += 101) {
        proof[i] ^= 0x10;
        EXPECT_FALSE(finalize(req)) << "flipped a bit of byte " << i;
        proof[i] ^= 0x10;
    }
    // The last bytes are delta (chall_3), iv_pre and the grinding counter.
    for (size_t i = UNBOUND_REDEEM_PROOF_BYTES - 36; i < UNBOUND_REDEEM_PROOF_BYTES; ++i) {
        proof[i] ^= 0x01;
        EXPECT_FALSE(finalize(req)) << "flipped a bit of byte " << i;
        proof[i] ^= 0x01;
    }
    EXPECT_TRUE(finalize(req));
}

// Even with the same witness and seed, the redemption proofs for different redemption contexts use
// different VOLE randomness. iv_pre is derived along with the VOLE seed from the instance hash mu.
TEST(UnboundRedeem, RedemptionContextsUseIndependentRandomness) {
    Context ctx_red = CTX_RED;
    ctx_red[0] ^= 1;
    const auto req = unbound_redeem_request_with_seed(token(), anchors().keys, CTX_ISS, ctx_red,
                                                      CHALLENGE_DIGEST, REDEEM_SEED);
    using P = ihat::detail::UnboundRedeemParams;
    const faest::faest_signature<P> a =
        std::span(redemption()).last<UNBOUND_REDEEM_PROOF_BYTES>().data();
    const faest::faest_signature<P> b = std::span(req).last<UNBOUND_REDEEM_PROOF_BYTES>().data();
    EXPECT_FALSE(std::ranges::equal(a.iv_pre(), b.iv_pre()));
}

// Invalid arguments throw and leave the token intact.
TEST(UnboundRedeem, RequestRejectsInvalidArguments) {
    const auto& keys = anchors().keys;
    UnboundToken t = TokenAccess::copy(token());

    // The token wasn't issued by any Anchor for this issuance context.
    Context ctx = CTX_ISS;
    ctx[0] ^= 1;
    EXPECT_THROW((void)t.redeem_request(keys, ctx, CTX_RED, CHALLENGE_DIGEST),
                 std::invalid_argument);
    EXPECT_THROW((void)t.redeem_request(keys, CTX_RED, CTX_ISS, CHALLENGE_DIGEST),
                 std::invalid_argument);
    EXPECT_THROW(
        (void)t.redeem_request(AnchorSet({keys[0], keys[2]}), CTX_ISS, CTX_RED, CHALLENGE_DIGEST),
        std::invalid_argument);
    Opening bad_r = TokenAccess::r(token());
    bad_r[0] ^= 1;
    const UnboundToken bad = TokenAccess::make_unbound_token(TokenAccess::nf_key(token()), bad_r,
                                                             TokenAccess::s(token()));
    EXPECT_THROW((void)bad.redeem_request(keys, CTX_ISS, CTX_RED, CHALLENGE_DIGEST),
                 std::invalid_argument);

    // The token is still intact.
    const auto req =
        unbound_redeem_request_with_seed(t, keys, CTX_ISS, CTX_RED, CHALLENGE_DIGEST, REDEEM_SEED);
    EXPECT_TRUE(std::ranges::equal(req, redemption()));

    // A token that was moved from can't be redeemed.
    const UnboundToken u = std::move(t);
    EXPECT_THROW((void)t.redeem_request(keys, CTX_ISS, CTX_RED, CHALLENGE_DIGEST),
                 std::logic_error);
    EXPECT_THROW((void)unbound_redeem_request_with_seed(t, keys, CTX_ISS, CTX_RED, CHALLENGE_DIGEST,
                                                        REDEEM_SEED),
                 std::logic_error);
    EXPECT_THROW((void)TokenAccess::nf_key(t), std::logic_error);
    EXPECT_TRUE(finalize(u.redeem_request(keys, CTX_ISS, CTX_RED, CHALLENGE_DIGEST)));
}

// An issuance proof isn't a redemption proof, even though both are VOLEitH proofs with the same
// parameters for statements about the same commitment.
TEST(UnboundRedeem, RejectsIssuanceProof) {
    const UnboundIssueRequest& issue_req = make_request().request;
    UnboundRedeemRequest req = redemption();
    std::ranges::copy(std::span(issue_req).last<UNBOUND_ISSUE_PROOF_BYTES>(),
                      std::span(req).last<UNBOUND_REDEEM_PROOF_BYTES>().begin());
    EXPECT_FALSE(finalize(req));
}

// An Anchor may issue both standard and unbound tokens with the same key; the two kinds of token
// are redeemed independently.
TEST(UnboundRedeem, CoexistsWithStandardTokens) {
    const auto& [pk, sk] = uov_key_pair();
    auto [pending, request] = issue_request(CTX_ISS, CTX_RED);
    auto standard = std::move(pending).finalize_issue(pk, *issue_response(sk, request, CTX_ISS));
    ASSERT_TRUE(standard.has_value());
    const auto standard_req =
        std::move(*standard).redeem_request(anchors().keys, CTX_ISS, CTX_RED, CHALLENGE_DIGEST);
    EXPECT_TRUE(finalize_redeem(anchors().keys, standard_req, CTX_ISS, CTX_RED, CHALLENGE_DIGEST));
    EXPECT_TRUE(finalize(redemption()));
}
