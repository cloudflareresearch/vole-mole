#include "vole_mole/moussaka.hpp"

#include "moussaka/issue.hpp" // internal
#include "moussaka/token.hpp" // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <span>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::moussaka;
using vole_mole::moussaka::detail::TokenAccess;
using vole_mole::test::filled;
using vole_mole::test::to_hex;
using vole_mole::test::uov_key_pair;
using vole_mole::test::UovKeyPair;

namespace {

const Context CTX_ISS = filled<CTX_BYTES>(0x10);
const Context CTX_RED = filled<CTX_BYTES>(0x20);
const Nullifier NF = filled<NF_BYTES>(0x30);
const Opening R = filled<R_BYTES>(0x40);
const Seed SEED = filled<SEED_BYTES>(0x50);

IssueRequestResult make_request(const Seed& seed = SEED) {
    return issue_request_with_seed(CTX_ISS, CTX_RED, seed);
}

// Whether an Anchor accepts the issue request.
bool verifies(const IssueRequest& request, const Context& ctx_iss) {
    return issue_response(uov_key_pair().sk, request, ctx_iss).has_value();
}

} // namespace

TEST(IssueRequest, WitnessIsConsistent) {
    using namespace moussaka::detail;
    using namespace keccak::detail;
    const auto w = encode_issue_witness(NF, CTX_ISS, CTX_RED, R);

    // Re-run the last segment from the last committed state; it must yield the commitment.
    Kp800State state;
    std::copy_n(w.begin() + WIT_OFF_STATES + (NUM_COMMITTED_STATES - 1) * KP800_STATE_BYTES,
                KP800_STATE_BYTES, state.begin());
    keccak_p800_rounds(state, SEGMENT_START[NUM_COMMITTED_STATES], FINAL_ROUNDS);
    const Commitment t = commit(NF, CTX_ISS, CTX_RED, R);
    EXPECT_EQ(to_hex(t), to_hex(std::span(state).first<uov::M>()));
}

TEST(IssueRequest, Verifies) {
    const auto res = make_request();
    EXPECT_TRUE(verifies(res.request, CTX_ISS));
    EXPECT_EQ(to_hex(std::span(res.request).first<uov::M>()),
              to_hex(commit(TokenAccess::nf(res.pending_token), CTX_ISS, CTX_RED,
                            TokenAccess::r(res.pending_token))));
}

TEST(IssueRequest, RandomizedVerifies) {
    const auto res = issue_request(CTX_ISS, CTX_RED);
    EXPECT_TRUE(verifies(res.request, CTX_ISS));
    EXPECT_EQ(to_hex(std::span(res.request).first<uov::M>()),
              to_hex(commit(TokenAccess::nf(res.pending_token), CTX_ISS, CTX_RED,
                            TokenAccess::r(res.pending_token))));
}

TEST(IssueRequest, IsDeterministicGivenSeed) {
    const auto a = make_request();
    const auto b = make_request();
    EXPECT_EQ(to_hex(TokenAccess::nf(a.pending_token)), to_hex(TokenAccess::nf(b.pending_token)));
    EXPECT_EQ(to_hex(TokenAccess::r(a.pending_token)), to_hex(TokenAccess::r(b.pending_token)));
    EXPECT_EQ(to_hex(std::span(a.request).first<uov::M>()),
              to_hex(std::span(b.request).first<uov::M>()));
    EXPECT_TRUE(std::ranges::equal(std::span(a.request).last<ISSUE_PROOF_BYTES>(),
                                   std::span(b.request).last<ISSUE_PROOF_BYTES>()));

    // A different seed changes all of the randomness.
    const auto c = make_request(filled<SEED_BYTES>(0x99));
    EXPECT_NE(to_hex(TokenAccess::nf(a.pending_token)), to_hex(TokenAccess::nf(c.pending_token)));
    EXPECT_NE(to_hex(TokenAccess::r(a.pending_token)), to_hex(TokenAccess::r(c.pending_token)));
    EXPECT_NE(to_hex(std::span(a.request).first<uov::M>()),
              to_hex(std::span(c.request).first<uov::M>()));
    EXPECT_FALSE(std::ranges::equal(std::span(a.request).last<ISSUE_PROOF_BYTES>(),
                                    std::span(c.request).last<ISSUE_PROOF_BYTES>()));
    EXPECT_TRUE(verifies(c.request, CTX_ISS));
}

// Known answer for the seed expansion: nf || r are the first 40 bytes of
// SHAKE128("mous" || VERSION || "s0" || seed). Generated with Python:
//
//   hashlib.shake_128(b"mous" + bytes([0]) + b"s0" + bytes(range(0x50, 0x70))).digest(40)
TEST(IssueRequest, SeedExpansion) {
    const auto res = make_request(); // with SEED = 0x50, 0x51, ..., 0x6f
    EXPECT_EQ(to_hex(TokenAccess::nf(res.pending_token)),
              "5f45ce3c1d41bbcba4d2363195d69d965e5c5b60ab69d68f");
    EXPECT_EQ(to_hex(TokenAccess::r(res.pending_token)), "4ea25e5192a154af3c2c0f63f32cdd6a");
}

TEST(IssueRequest, RejectWrongCtxIss) {
    const auto res = make_request();
    Context ctx = CTX_ISS;
    ctx[5] ^= 1;
    EXPECT_FALSE(verifies(res.request, ctx));
}

TEST(IssueRequest, RejectWrongCommitment) {
    const auto res = make_request();
    IssueRequest req = res.request;
    req[0] ^= 0x80;
    EXPECT_FALSE(verifies(req, CTX_ISS));
}

// A commitment to different values (with a valid proof for those) doesn't transfer.
TEST(IssueRequest, RejectMismatchedProof) {
    const auto a = make_request();
    const auto b = issue_request(CTX_ISS, CTX_RED);
    IssueRequest req = a.request;
    std::ranges::copy(std::span(b.request).last<ISSUE_PROOF_BYTES>(),
                      std::span(req).last<ISSUE_PROOF_BYTES>().begin());
    EXPECT_FALSE(verifies(req, CTX_ISS));
}

TEST(IssueRequest, RejectTamperedProof) {
    const auto res = make_request();
    IssueRequest req = res.request;

    // Flip one bit in (at least) every field of the proof. See faest::faest_signature for the
    // layout.
    for (size_t i = 0; i < ISSUE_PROOF_BYTES; i += 97) {
        std::span(req).last<ISSUE_PROOF_BYTES>()[i] ^= 0x04;
        EXPECT_FALSE(verifies(req, CTX_ISS)) << "flipped a bit of byte " << i;
        std::span(req).last<ISSUE_PROOF_BYTES>()[i] ^= 0x04;
    }
    // The last bytes are delta (chall_3), iv_pre and the grinding counter.
    for (size_t i = ISSUE_PROOF_BYTES - 36; i < ISSUE_PROOF_BYTES; ++i) {
        std::span(req).last<ISSUE_PROOF_BYTES>()[i] ^= 0x01;
        EXPECT_FALSE(verifies(req, CTX_ISS)) << "flipped a bit of byte " << i;
        std::span(req).last<ISSUE_PROOF_BYTES>()[i] ^= 0x01;
    }
    EXPECT_TRUE(verifies(req, CTX_ISS));
}

// Every mask's row of the CRT VOLECommit's c_mult matrix is bound by the proof.
TEST(IssueRequest, RejectTamperedCMult) {
    using P = vole_mole::moussaka::detail::IssueParams;
    constexpr size_t N_MASK = P::CONSTS::CRT_NUM_MASK;
    constexpr size_t N_MULT_BYTES = P::CONSTS::CRT_NUM_MULT_BYTES;
    static_assert(N_MASK == vole_mole::moussaka::detail::ISSUE_QS_DEGREE - 1 + 4);

    const auto res = make_request();
    IssueRequest req = res.request;
    const auto c_mult =
        faest::mutable_faest_signature<P>(std::span(req).last<ISSUE_PROOF_BYTES>().data())
            .vole_commitment_cmult();
    for (size_t m = 0; m < N_MASK; ++m) {
        c_mult[m * N_MULT_BYTES] ^= 0x01;
        EXPECT_FALSE(verifies(req, CTX_ISS)) << "flipped a bit of row " << m;
        c_mult[m * N_MULT_BYTES] ^= 0x01;
    }
    EXPECT_TRUE(verifies(req, CTX_ISS));
}

namespace {

// An Anchor Set can't contain null: its entries can only be constructed from an lvalue reference to
// a key, not from a pointer, nullptr, or a temporary (which would dangle).
static_assert(!std::is_constructible_v<AnchorRef, std::nullptr_t>);
static_assert(!std::is_constructible_v<AnchorRef, const uov::PublicKey*>);
static_assert(!std::is_constructible_v<AnchorRef, uov::PublicKey&&>);
static_assert(!std::is_default_constructible_v<AnchorRef>);

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
Token issue(const Seed& seed = SEED) {
    const auto& [pk, sk] = uov_key_pair();
    auto [pending, request] = issue_request_with_seed(CTX_ISS, CTX_RED, seed);
    const auto response = issue_response(sk, request, CTX_ISS);
    EXPECT_TRUE(response.has_value());
    auto token = std::move(pending).finalize_issue(pk, *response);
    EXPECT_TRUE(token.has_value());
    return *std::move(token);
}

const Token& token() {
    static const Token t = issue();
    return t;
}

// Redemption consumes a token, so tests that redeem the same token several times redeem copies.
Token copy(const Token& t) { return TokenAccess::copy(t); }

const Seed REDEEM_SEED = filled<SEED_BYTES>(0x90);

const RedeemRequest& redemption() {
    static const RedeemRequest req = copy(token()).redeem_request_with_seed(
        anchors().keys, ISSUER, CTX_ISS, CTX_RED, REDEEM_SEED);
    return req;
}

} // namespace

TEST(IssueResponse, SignsCommitment) {
    const auto& [pk, sk] = uov_key_pair();
    const auto res = make_request();
    const auto response = issue_response(sk, res.request, CTX_ISS);
    ASSERT_TRUE(response.has_value());
    EXPECT_EQ(to_hex(pk.eval(*response)), to_hex(std::span(res.request).first<uov::M>()));
}

TEST(FinalizeIssue, ReturnsToken) {
    const auto& [pk, sk] = uov_key_pair();
    const auto res = make_request();
    const Token t = issue();
    const auto& nf = TokenAccess::nf(t);
    const auto& r = TokenAccess::r(t);
    EXPECT_EQ(to_hex(nf), to_hex(TokenAccess::nf(res.pending_token)));
    EXPECT_EQ(to_hex(r), to_hex(TokenAccess::r(res.pending_token)));
    EXPECT_EQ(to_hex(pk.eval(TokenAccess::s(t))), to_hex(commit(nf, CTX_ISS, CTX_RED, r)));
}

// Each case consumes a pending token, so each uses a fresh copy of the same request (the request
// is deterministic given the seed).
TEST(FinalizeIssue, RejectsInvalidResponse) {
    const auto& [pk, sk] = uov_key_pair();
    const IssueResponse response = *issue_response(sk, make_request().request, CTX_ISS);

    // Wrong Anchor.
    EXPECT_FALSE(make_request().pending_token.finalize_issue(anchors().a.pk, response));

    // Tampered signature.
    IssueResponse bad = response;
    bad[0] ^= 1;
    EXPECT_FALSE(make_request().pending_token.finalize_issue(pk, bad));

    // Signature of a request for other contexts, but with the same randomness.
    Context ctx = CTX_ISS;
    ctx[1] ^= 1;
    EXPECT_FALSE(
        issue_request_with_seed(ctx, CTX_RED, SEED).pending_token.finalize_issue(pk, response));
    EXPECT_FALSE(
        issue_request_with_seed(CTX_ISS, ctx, SEED).pending_token.finalize_issue(pk, response));

    // Signature of another request.
    EXPECT_FALSE(make_request(filled<SEED_BYTES>(0x99)).pending_token.finalize_issue(pk, response));

    // The valid response.
    EXPECT_TRUE(make_request().pending_token.finalize_issue(pk, response));
}

// Finalizing issuance consumes the pending token, whether or not the response is valid.
TEST(FinalizeIssue, ConsumesPendingToken) {
    const auto& [pk, sk] = uov_key_pair();
    auto [pending, request] = make_request();
    const IssueResponse response = *issue_response(sk, request, CTX_ISS);

    IssueResponse bad = response;
    bad[0] ^= 1;
    EXPECT_FALSE(std::move(pending).finalize_issue(pk, bad));
    EXPECT_THROW((void)std::move(pending).finalize_issue(pk, response), std::logic_error);

    auto [pending2, request2] = make_request();
    EXPECT_TRUE(std::move(pending2).finalize_issue(pk, response));
    EXPECT_THROW((void)std::move(pending2).finalize_issue(pk, response), std::logic_error);
    EXPECT_THROW((void)TokenAccess::nf(pending2), std::logic_error);
}

TEST(Redeem, Verifies) {
    const auto nf = finalize_redeem(anchors().keys, redemption(), CTX_ISS, CTX_RED);
    ASSERT_TRUE(nf.has_value());
    EXPECT_EQ(to_hex(*nf), to_hex(TokenAccess::nf(token())));
    EXPECT_EQ(to_hex(std::span(redemption()).first<NF_BYTES>()), to_hex(TokenAccess::nf(token())));
}

TEST(Redeem, RandomizedVerifies) {
    const auto& [pk, sk] = uov_key_pair();
    auto [pending, request] = issue_request(CTX_ISS, CTX_RED);
    auto t = std::move(pending).finalize_issue(pk, *issue_response(sk, request, CTX_ISS));
    ASSERT_TRUE(t.has_value());
    const Nullifier want = TokenAccess::nf(*t);
    const auto req = std::move(*t).redeem_request(anchors().keys, ISSUER, CTX_ISS, CTX_RED);
    const auto nf = finalize_redeem(anchors().keys, req, CTX_ISS, CTX_RED);
    ASSERT_TRUE(nf.has_value());
    EXPECT_EQ(to_hex(*nf), to_hex(want));
}

// The issuing Anchor may be anywhere in the Anchor Set.
TEST(Redeem, VerifiesAtEveryPosition) {
    for (const size_t n : {size_t{1}, size_t{2}}) {
        for (size_t i = 0; i < n; ++i) {
            const AnchorSet keys = anchor_set_with_issuer_at(n, i);
            const auto req =
                copy(token()).redeem_request_with_seed(keys, i, CTX_ISS, CTX_RED, REDEEM_SEED);
            EXPECT_TRUE(finalize_redeem(keys, req, CTX_ISS, CTX_RED))
                << "n = " << n << ", i = " << i;
        }
    }
}

TEST(Redeem, VerifiesLargestAnchorSet) {
    const AnchorSet keys = anchor_set_with_issuer_at(MAX_ANCHORS, MAX_ANCHORS / 2);
    const auto req = copy(token()).redeem_request_with_seed(keys, MAX_ANCHORS / 2, CTX_ISS, CTX_RED,
                                                            REDEEM_SEED);
    EXPECT_TRUE(finalize_redeem(keys, req, CTX_ISS, CTX_RED));
}

// Example: An application that owns its Anchors' keys in a container builds an Anchor Set from
// them directly, or from references to a selection of them. (The Anchor Set refers to the keys, so
// the container must not be modified while the Anchor Set is in use.)
TEST(Redeem, AnchorSetFromOwnedKeys) {
    std::vector<uov::PublicKey> keys;
    keys.emplace_back(anchors().a.sk.public_key());
    keys.emplace_back(uov_key_pair().sk.public_key()); // the issuer, at index ISSUER
    keys.emplace_back(anchors().c.sk.public_key());

    const AnchorSet anchor_set(keys);
    const auto req = copy(token()).redeem_request(anchor_set, ISSUER, CTX_ISS, CTX_RED);
    const auto nf = finalize_redeem(anchor_set, req, CTX_ISS, CTX_RED);
    ASSERT_TRUE(nf.has_value());
    EXPECT_EQ(to_hex(*nf), to_hex(TokenAccess::nf(token())));

    // The same Anchor Set, from references to the keys.
    const std::vector<AnchorRef> refs(keys.begin(), keys.end());
    EXPECT_TRUE(finalize_redeem(AnchorSet(refs), req, CTX_ISS, CTX_RED));

    // A different Anchor Set: the first two keys in reverse order.
    const AnchorSet subset({keys[1], keys[0]});
    const auto req2 = copy(token()).redeem_request(subset, 0, CTX_ISS, CTX_RED);
    EXPECT_TRUE(finalize_redeem(subset, req2, CTX_ISS, CTX_RED));
}

TEST(Redeem, IsDeterministicGivenSeed) {
    const auto& a = redemption();
    const auto b = copy(token()).redeem_request_with_seed(anchors().keys, ISSUER, CTX_ISS, CTX_RED,
                                                          REDEEM_SEED);
    EXPECT_TRUE(std::ranges::equal(a, b));

    // A different seed yields a different proof for the same token.
    const auto c = copy(token()).redeem_request_with_seed(anchors().keys, ISSUER, CTX_ISS, CTX_RED,
                                                          filled<SEED_BYTES>(0x91));
    EXPECT_FALSE(std::ranges::equal(a, c));
    EXPECT_TRUE(std::ranges::equal(std::span(a).first<NF_BYTES>(), std::span(c).first<NF_BYTES>()));
    EXPECT_TRUE(finalize_redeem(anchors().keys, c, CTX_ISS, CTX_RED));
}

TEST(Redeem, RejectsWrongContext) {
    Context ctx = CTX_ISS;
    ctx[7] ^= 1;
    EXPECT_FALSE(finalize_redeem(anchors().keys, redemption(), ctx, CTX_RED));
    EXPECT_FALSE(finalize_redeem(anchors().keys, redemption(), CTX_ISS, ctx));
    EXPECT_FALSE(finalize_redeem(anchors().keys, redemption(), CTX_RED, CTX_ISS));
}

TEST(Redeem, RejectsWrongAnchorSet) {
    const auto& keys = anchors().keys;

    const uov::PublicKey& other = vole_mole::test::distinct_uov_public_key(0);

    // The issuing Anchor is missing.
    EXPECT_FALSE(finalize_redeem(AnchorSet({keys[0], keys[2]}), redemption(), CTX_ISS, CTX_RED));
    EXPECT_FALSE(
        finalize_redeem(AnchorSet(keys.keys().first(ISSUER)), redemption(), CTX_ISS, CTX_RED));

    // The Anchors are reordered.
    EXPECT_FALSE(
        finalize_redeem(AnchorSet({keys[1], keys[0], keys[2]}), redemption(), CTX_ISS, CTX_RED));

    // An Anchor is added.
    EXPECT_FALSE(finalize_redeem(AnchorSet({keys[0], keys[1], keys[2], other}), redemption(),
                                 CTX_ISS, CTX_RED));

    // An Anchor that didn't issue the token is replaced.
    EXPECT_FALSE(
        finalize_redeem(AnchorSet({other, keys[1], keys[2]}), redemption(), CTX_ISS, CTX_RED));
}

TEST(Redeem, RejectsWrongNullifier) {
    RedeemRequest req = redemption();
    req[0] ^= 1;
    EXPECT_FALSE(finalize_redeem(anchors().keys, req, CTX_ISS, CTX_RED));

    // The proof for one token doesn't transfer to another token's nullifier.
    const Token other = issue(filled<SEED_BYTES>(0x99));
    req = redemption();
    std::ranges::copy(TokenAccess::nf(other), req.begin());
    EXPECT_FALSE(finalize_redeem(anchors().keys, req, CTX_ISS, CTX_RED));
}

TEST(Redeem, RejectsTamperedProof) {
    RedeemRequest req = redemption();
    auto proof = std::span(req).last<REDEEM_PROOF_BYTES>();
    for (size_t i = 0; i < REDEEM_PROOF_BYTES; i += 101) {
        proof[i] ^= 0x10;
        EXPECT_FALSE(finalize_redeem(anchors().keys, req, CTX_ISS, CTX_RED))
            << "flipped a bit of byte " << i;
        proof[i] ^= 0x10;
    }
    // The last bytes are delta (chall_3), iv_pre and the grinding counter.
    for (size_t i = REDEEM_PROOF_BYTES - 36; i < REDEEM_PROOF_BYTES; ++i) {
        proof[i] ^= 0x01;
        EXPECT_FALSE(finalize_redeem(anchors().keys, req, CTX_ISS, CTX_RED))
            << "flipped a bit of byte " << i;
        proof[i] ^= 0x01;
    }
    EXPECT_TRUE(finalize_redeem(anchors().keys, req, CTX_ISS, CTX_RED));
}

// An issuance proof isn't a redemption proof, and vice versa, even though both are VOLEitH proofs
// with the same parameters for statements about the same commitment.
TEST(Redeem, RejectsIssuanceProof) {
    const IssueRequest& issue_req = make_request().request;
    RedeemRequest req = redemption();
    std::ranges::copy(std::span(issue_req).last<ISSUE_PROOF_BYTES>(),
                      std::span(req).last<REDEEM_PROOF_BYTES>().begin());
    EXPECT_FALSE(finalize_redeem(anchors().keys, req, CTX_ISS, CTX_RED));
}

// Invalid arguments leave the token unchanged, so it can still be redeemed afterwards.
TEST(Redeem, RequestRejectsInvalidArguments) {
    const auto& keys = anchors().keys;
    Token t = copy(token());

    // Index out of range.
    EXPECT_THROW((void)std::move(t).redeem_request(keys, keys.size(), CTX_ISS, CTX_RED),
                 std::invalid_argument);

    // The token wasn't issued by the Anchor at the given index, or for these contexts.
    EXPECT_THROW((void)std::move(t).redeem_request(keys, 0, CTX_ISS, CTX_RED),
                 std::invalid_argument);
    Context ctx = CTX_ISS;
    ctx[0] ^= 1;
    EXPECT_THROW((void)std::move(t).redeem_request(keys, ISSUER, ctx, CTX_RED),
                 std::invalid_argument);
    ctx = CTX_RED;
    ctx[0] ^= 1;
    EXPECT_THROW((void)std::move(t).redeem_request(keys, ISSUER, CTX_ISS, ctx),
                 std::invalid_argument);
    EXPECT_THROW((void)std::move(t).redeem_request(keys, ISSUER, CTX_RED, CTX_ISS),
                 std::invalid_argument);
    Opening bad_r = TokenAccess::r(token());
    bad_r[0] ^= 1;
    Token bad = TokenAccess::make(TokenAccess::nf(token()), bad_r, TokenAccess::s(token()));
    EXPECT_THROW((void)std::move(bad).redeem_request(keys, ISSUER, CTX_ISS, CTX_RED),
                 std::invalid_argument);

    // The token is still intact.
    const auto req =
        std::move(t).redeem_request_with_seed(keys, ISSUER, CTX_ISS, CTX_RED, REDEEM_SEED);
    EXPECT_TRUE(std::ranges::equal(req, redemption()));
}

// Redemption consumes the token, so it can't be redeemed twice.
TEST(Redeem, ConsumesToken) {
    const auto& keys = anchors().keys;
    Token t = copy(token());
    (void)std::move(t).redeem_request(keys, ISSUER, CTX_ISS, CTX_RED);
    EXPECT_THROW((void)std::move(t).redeem_request(keys, ISSUER, CTX_ISS, CTX_RED),
                 std::logic_error);
    EXPECT_THROW(
        (void)std::move(t).redeem_request_with_seed(keys, ISSUER, CTX_ISS, CTX_RED, REDEEM_SEED),
        std::logic_error);

    // Likewise for a token that was moved from.
    Token u = copy(token());
    const Token v = std::move(u);
    EXPECT_THROW((void)std::move(u).redeem_request(keys, ISSUER, CTX_ISS, CTX_RED),
                 std::logic_error);
    EXPECT_THROW((void)TokenAccess::nf(u), std::logic_error);
}

TEST(AnchorSet, AcceptsDistinctKeys) {
    const AnchorSet& keys = anchors().keys;
    ASSERT_EQ(keys.size(), 3u);
    EXPECT_EQ(&keys[0], &anchors().a.pk);
    EXPECT_EQ(&keys[ISSUER], &uov_key_pair().pk);
    EXPECT_EQ(&keys[2], &anchors().c.pk);
    EXPECT_EQ(keys.keys().size(), 3u);

    std::vector<AnchorRef> max;
    for (size_t u = 0; u < MAX_ANCHORS; ++u) {
        max.emplace_back(vole_mole::test::distinct_uov_public_key(u));
    }
    EXPECT_EQ(AnchorSet(max).size(), MAX_ANCHORS);
}

TEST(AnchorSet, RejectsEmpty) {
    EXPECT_THROW(AnchorSet(std::span<const AnchorRef>{}), std::invalid_argument);
    EXPECT_THROW(AnchorSet(std::span<const uov::PublicKey>{}), std::invalid_argument);
    EXPECT_THROW(AnchorSet({}), std::invalid_argument);
}

TEST(AnchorSet, RejectsTooMany) {
    std::vector<AnchorRef> too_many;
    for (size_t u = 0; u < MAX_ANCHORS + 1; ++u) {
        too_many.emplace_back(vole_mole::test::distinct_uov_public_key(u));
    }
    EXPECT_THROW((void)AnchorSet(too_many), std::invalid_argument);
}

TEST(AnchorSet, RejectsRepeatedKey) {
    const uov::PublicKey& a = anchors().a.pk;
    const uov::PublicKey& b = uov_key_pair().pk;

    // The same key object, adjacent or not.
    EXPECT_THROW(AnchorSet({a, a}), std::invalid_argument);
    EXPECT_THROW(AnchorSet({a, b, a}), std::invalid_argument);

    // Distinct copies of the same key.
    std::vector<uov::PublicKey> copies;
    copies.emplace_back(anchors().a.sk.public_key());
    copies.emplace_back(anchors().a.sk.public_key());
    EXPECT_THROW((void)AnchorSet(copies), std::invalid_argument);
    EXPECT_THROW(AnchorSet({b, copies[0], a}), std::invalid_argument);
}
