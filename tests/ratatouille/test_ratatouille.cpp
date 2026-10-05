#include "vole_mole/ratatouille.hpp"

#include "ratatouille/commit.hpp" // internal
#include "ratatouille/issue.hpp"  // internal
#include "ratatouille/spend.hpp"  // internal
#include "ratatouille/token.hpp"  // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <fstream>
#include <limits>
#include <optional>
#include <set>
#include <span>
#include <stdexcept>
#include <string>
#include <utility>

using namespace vole_mole;
using namespace vole_mole::ratatouille;
using vole_mole::ratatouille::detail::TokenAccess;
using vole_mole::test::filled;
using vole_mole::test::read_kat_field;
using vole_mole::test::read_kat_number;
using vole_mole::test::to_hex;
using vole_mole::test::uov_key_pair;
using vole_mole::test::UovKeyPair;

namespace {

constexpr Credits MAX_CREDITS = std::numeric_limits<Credits>::max();

const Context CTX_ISS = filled<CTX_BYTES>(0x10);
const Seed SEED = filled<SEED_BYTES>(0x50);
const Seed SPEND_SEED = filled<SEED_BYTES>(0x90);
constexpr Credits T_INIT = 100;
constexpr Credits D = 30;

// Offsets of the fields of a spend request and response.
constexpr size_t REQ_OFF_D = NF_BYTES;
constexpr size_t REQ_OFF_C_NEXT = REQ_OFF_D + CREDIT_BYTES;
constexpr size_t RESP_OFF_S = CREDIT_BYTES;

const UovKeyPair& other_issuer() {
    static const UovKeyPair kp(uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x61)});
    return kp;
}

IssueRequestResult make_request(const Seed& seed = SEED) {
    return issue_request_with_seed(T_INIT, CTX_ISS, seed);
}

// Whether the Issuer accepts the issue request.
bool verifies(const IssueRequest& request, Credits t_init, const Context& ctx_iss) {
    return issue_response(uov_key_pair().sk, request, t_init, ctx_iss).has_value();
}

// Run issuance with the fixed test key pair.
Token issue(const Seed& seed = SEED, Credits t_init = T_INIT) {
    const auto& [pk, sk] = uov_key_pair();
    auto [pending, request] = issue_request_with_seed(t_init, CTX_ISS, seed);
    const auto response = issue_response(sk, request, t_init, CTX_ISS);
    EXPECT_TRUE(response.has_value());
    auto token = std::move(pending).finalize_issue(pk, *response);
    EXPECT_TRUE(token.has_value());
    return *std::move(token);
}

const Token& token() {
    static const Token t = issue();
    return t;
}

// Spending consumes a token, so tests that spend the same token several times spend copies.
Token copy(const Token& t) { return TokenAccess::copy(t); }

// The spend of D credits from token().
const SpendRequestResult& spend() {
    static const SpendRequestResult res =
        copy(token()).spend_request_with_seed(uov_key_pair().pk, D, CTX_ISS, SPEND_SEED);
    return res;
}

// Respond to a spend request with the fixed test key pair, granting `refund` without tracking
// nullifiers.
std::optional<SpendResponse> respond(const SpendRequest& request, Credits refund = 0,
                                     const Context& ctx_iss = CTX_ISS) {
    const auto& [pk, sk] = uov_key_pair();
    const auto res = spend_response(sk, request, ctx_iss, refund);
    if (!res) {
        return std::nullopt;
    }
    return res->response;
}

// Whether the Issuer accepts the spend request.
bool spend_verifies(const SpendRequest& request, const Context& ctx_iss = CTX_ISS) {
    return respond(request, 0, ctx_iss).has_value();
}

// Spend d credits from the token and finalize the spend with the given refund.
Token spend_and_finalize(Token t, Credits d, Credits refund) {
    const auto& pk = uov_key_pair().pk;
    auto [pending, request] = std::move(t).spend_request(pk, d, CTX_ISS);
    const auto response = respond(request, refund);
    EXPECT_TRUE(response.has_value());
    auto change = std::move(pending).finalize_spend(pk, *response);
    EXPECT_TRUE(change.has_value());
    return *std::move(change);
}

} // namespace

// Freeze both witness layouts and the complete deterministic protocol transcript: issuance followed
// by several spends, each spending the change token of the previous one. Verification of the stored
// messages also catches changes that break compatibility with existing proofs.
TEST(Ratatouille, KnownAnswers) {
    std::ifstream in(std::string(VOLE_MOLE_TEST_DATA_DIR) + "/ratatouille/ratatouille_kat.txt");
    ASSERT_TRUE(in.is_open()) << "can't open ratatouille/ratatouille_kat.txt";
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
        Credits t_init;
        uov::SecretKeyBytes issuer_sk;
        Nullifier nf;
        Opening r;
        Commitment commitment;
        std::array<uint8_t, ratatouille::detail::ISSUE_WITNESS_BYTES> issue_witness;
        IssueRequest request;
        IssueResponse response;
        size_t spend_count;
        ASSERT_TRUE(read_kat_field(in, "issue_seed", issue_seed));
        ASSERT_TRUE(read_kat_field(in, "ctx_iss", ctx_iss));
        ASSERT_TRUE(read_kat_number(in, "t_init", t_init));
        ASSERT_TRUE(read_kat_field(in, "issuer_sk", issuer_sk));
        ASSERT_TRUE(read_kat_field(in, "nf", nf));
        ASSERT_TRUE(read_kat_field(in, "r", r));
        ASSERT_TRUE(read_kat_field(in, "commitment", commitment));
        ASSERT_TRUE(read_kat_field(in, "issue_witness", issue_witness));
        ASSERT_TRUE(read_kat_field(in, "issue_request", request));
        ASSERT_TRUE(read_kat_field(in, "issue_response", response));
        ASSERT_TRUE(read_kat_number(in, "spend_count", spend_count));
        ASSERT_GE(spend_count, 1u);
        const UovKeyPair kp(uov::SecretKey{issuer_sk});

        // Issuance.
        auto res = issue_request_with_seed(t_init, ctx_iss, issue_seed);
        EXPECT_EQ(TokenAccess::nf(res.pending_token), nf);
        EXPECT_EQ(TokenAccess::r(res.pending_token), r);
        EXPECT_EQ(ratatouille::detail::encode_issue_witness(nf, ctx_iss, t_init, r), issue_witness);
        EXPECT_EQ(commit(nf, ctx_iss, t_init, r), commitment);
        EXPECT_EQ(to_hex(commitment), to_hex(std::span(request).first<COMMITMENT_BYTES>()));
        EXPECT_TRUE(std::ranges::equal(res.request, request)) << "issue request bytes differ";

        const auto generated_response = issue_response(kp.sk, res.request, t_init, ctx_iss);
        ASSERT_TRUE(generated_response.has_value());
        EXPECT_EQ(*generated_response, response);
        // Verify the stored issuance proof independently of the regenerated request.
        const auto stored_response = issue_response(kp.sk, request, t_init, ctx_iss);
        ASSERT_TRUE(stored_response.has_value());
        EXPECT_EQ(*stored_response, response);
        EXPECT_EQ(kp.pk.eval(response), tag(commitment, 0));

        auto token = std::move(res.pending_token).finalize_issue(kp.pk, response);
        ASSERT_TRUE(token.has_value());
        EXPECT_EQ(token->credit(), t_init);
        EXPECT_EQ(token->refund(), 0u);

        // Spends.
        for (size_t j = 0; j < spend_count; ++j) {
            SCOPED_TRACE("spend " + std::to_string(j));
            Seed spend_seed;
            Credits d, refund, t_next;
            Nullifier nf_next;
            Opening r_next;
            std::array<uint8_t, ratatouille::detail::SPEND_WITNESS_BYTES> spend_witness;
            SpendRequest spend_req;
            SpendResponse spend_resp;
            ASSERT_TRUE(read_kat_field(in, "spend_seed", spend_seed));
            ASSERT_TRUE(read_kat_number(in, "d", d));
            ASSERT_TRUE(read_kat_number(in, "refund", refund));
            ASSERT_TRUE(read_kat_field(in, "nf_next", nf_next));
            ASSERT_TRUE(read_kat_number(in, "t_next", t_next));
            ASSERT_TRUE(read_kat_field(in, "r_next", r_next));
            ASSERT_TRUE(read_kat_field(in, "spend_witness", spend_witness));
            ASSERT_TRUE(read_kat_field(in, "spend_request", spend_req));
            ASSERT_TRUE(read_kat_field(in, "spend_response", spend_resp));

            const Nullifier spent_nf = TokenAccess::nf(*token);
            EXPECT_EQ(t_next, token->credit() + token->refund() - d);
            const ratatouille::detail::SpendState st{spent_nf,
                                                     token->credit(),
                                                     TokenAccess::r(*token),
                                                     token->refund(),
                                                     TokenAccess::s(*token),
                                                     nf_next,
                                                     t_next,
                                                     r_next};
            EXPECT_EQ(ratatouille::detail::encode_spend_witness(st, d, ctx_iss), spend_witness);

            auto [pending, generated_req] =
                std::move(*token).spend_request_with_seed(kp.pk, d, ctx_iss, spend_seed);
            EXPECT_EQ(TokenAccess::nf(pending), nf_next);
            EXPECT_EQ(TokenAccess::t(pending), t_next);
            EXPECT_EQ(TokenAccess::r(pending), r_next);
            EXPECT_TRUE(std::ranges::equal(generated_req, spend_req))
                << "spend request bytes differ";
            // The request is nf || d || c' || proof.
            EXPECT_EQ(to_hex(std::span(spend_req).first<NF_BYTES>()), to_hex(spent_nf));
            EXPECT_EQ(
                to_hex(std::span(spend_req).subspan<NF_BYTES + CREDIT_BYTES, COMMITMENT_BYTES>()),
                to_hex(commit(nf_next, ctx_iss, t_next, r_next)));

            const auto generated = spend_response(kp.sk, generated_req, ctx_iss, refund);
            ASSERT_TRUE(generated.has_value());
            EXPECT_EQ(generated->response, spend_resp);
            // Verify the stored spend proof even if regeneration changes its bytes.
            const auto stored = spend_response(kp.sk, spend_req, ctx_iss, refund);
            ASSERT_TRUE(stored.has_value());
            EXPECT_EQ(stored->response, spend_resp);
            EXPECT_EQ(stored->nf, spent_nf);
            EXPECT_EQ(stored->d, d);

            token = std::move(pending).finalize_spend(kp.pk, spend_resp);
            ASSERT_TRUE(token.has_value());
            EXPECT_EQ(token->credit(), t_next);
            EXPECT_EQ(token->refund(), refund);
        }
        ++count;
    }
    EXPECT_EQ(count, 3u);
}

// Issuance

TEST(IssueRequest, Verifies) {
    const auto res = make_request();
    EXPECT_TRUE(verifies(res.request, T_INIT, CTX_ISS));
    EXPECT_EQ(to_hex(std::span(res.request).first<COMMITMENT_BYTES>()),
              to_hex(commit(TokenAccess::nf(res.pending_token), CTX_ISS, T_INIT,
                            TokenAccess::r(res.pending_token))));
}

TEST(IssueRequest, RandomizedVerifies) {
    const auto res = issue_request(T_INIT, CTX_ISS);
    EXPECT_TRUE(verifies(res.request, T_INIT, CTX_ISS));
}

TEST(IssueRequest, IsDeterministicGivenSeed) {
    const auto a = make_request();
    const auto b = make_request();
    EXPECT_EQ(to_hex(TokenAccess::nf(a.pending_token)), to_hex(TokenAccess::nf(b.pending_token)));
    EXPECT_EQ(to_hex(TokenAccess::r(a.pending_token)), to_hex(TokenAccess::r(b.pending_token)));
    EXPECT_TRUE(std::ranges::equal(a.request, b.request));

    const auto c = make_request(filled<SEED_BYTES>(0x99));
    EXPECT_NE(to_hex(TokenAccess::nf(a.pending_token)), to_hex(TokenAccess::nf(c.pending_token)));
    EXPECT_NE(to_hex(TokenAccess::r(a.pending_token)), to_hex(TokenAccess::r(c.pending_token)));
    EXPECT_FALSE(std::ranges::equal(a.request, c.request));
    EXPECT_TRUE(verifies(c.request, T_INIT, CTX_ISS));
}

// Known answer for the seed expansion: nf || r are the first 40 bytes of
// SHAKE128("rata" || VERSION || "s0" || seed). Generated with Python:
//
//   hashlib.shake_128(b"rata" + bytes([0]) + b"s0" + bytes(range(0x50, 0x70))).digest(40)
TEST(IssueRequest, SeedExpansion) {
    const auto res = make_request();
    EXPECT_EQ(to_hex(TokenAccess::nf(res.pending_token)),
              "8eea0a9ddefda10aa0cf801dbc01dbe8492165eaebc44e20");
    EXPECT_EQ(to_hex(TokenAccess::r(res.pending_token)), "8f96fd313dd712eb63273fa1c5a96662");
}

TEST(IssueRequest, RejectsZeroInitialCredit) {
    EXPECT_THROW((void)issue_request(0, CTX_ISS), std::invalid_argument);
    EXPECT_THROW((void)issue_request_with_seed(0, CTX_ISS, SEED), std::invalid_argument);
    EXPECT_THROW((void)issue_response(uov_key_pair().sk, make_request().request, 0, CTX_ISS),
                 std::invalid_argument);
}

TEST(IssueRequest, RejectsWrongContext) {
    const auto res = make_request();
    Context ctx = CTX_ISS;
    ctx[5] ^= 1;
    EXPECT_FALSE(verifies(res.request, T_INIT, ctx));
}

TEST(IssueRequest, RejectsWrongInitialCredit) {
    const auto res = make_request();
    for (const Credits t_init : {T_INIT + 1, T_INIT - 1, MAX_CREDITS}) {
        EXPECT_FALSE(verifies(res.request, t_init, CTX_ISS)) << "T_init = " << t_init;
    }
}

TEST(IssueRequest, RejectsWrongCommitment) {
    IssueRequest req = make_request().request;
    req[0] ^= 0x80;
    EXPECT_FALSE(verifies(req, T_INIT, CTX_ISS));
}

TEST(IssueRequest, RejectsTamperedProof) {
    IssueRequest req = make_request().request;
    auto proof = std::span(req).last<ISSUE_PROOF_BYTES>();
    for (size_t i = 0; i < ISSUE_PROOF_BYTES; i += 97) {
        proof[i] ^= 0x04;
        EXPECT_FALSE(verifies(req, T_INIT, CTX_ISS)) << "flipped a bit of byte " << i;
        proof[i] ^= 0x04;
    }
    // The last bytes are delta (chall_3), iv_pre and the grinding counter.
    for (size_t i = ISSUE_PROOF_BYTES - 36; i < ISSUE_PROOF_BYTES; ++i) {
        proof[i] ^= 0x01;
        EXPECT_FALSE(verifies(req, T_INIT, CTX_ISS)) << "flipped a bit of byte " << i;
        proof[i] ^= 0x01;
    }
    EXPECT_TRUE(verifies(req, T_INIT, CTX_ISS));
}

TEST(IssueResponse, SignsTag) {
    const auto& [pk, sk] = uov_key_pair();
    const auto res = make_request();
    const auto response = issue_response(sk, res.request, T_INIT, CTX_ISS);
    ASSERT_TRUE(response.has_value());
    Commitment c;
    std::ranges::copy(std::span(res.request).first<COMMITMENT_BYTES>(), c.begin());
    EXPECT_EQ(to_hex(pk.eval(*response)), to_hex(tag(c, 0)));
}

TEST(FinalizeIssue, ReturnsToken) {
    const auto& pk = uov_key_pair().pk;
    const auto res = make_request();
    const Token& t = token();
    EXPECT_EQ(t.credit(), T_INIT);
    EXPECT_EQ(t.refund(), 0u);
    EXPECT_EQ(to_hex(TokenAccess::nf(t)), to_hex(TokenAccess::nf(res.pending_token)));
    EXPECT_EQ(to_hex(TokenAccess::r(t)), to_hex(TokenAccess::r(res.pending_token)));
    EXPECT_EQ(to_hex(pk.eval(TokenAccess::s(t))),
              to_hex(tag(commit(TokenAccess::nf(t), CTX_ISS, T_INIT, TokenAccess::r(t)), 0)));
}

TEST(FinalizeIssue, RejectsInvalidResponse) {
    const auto& [pk, sk] = uov_key_pair();
    const IssueResponse response = *issue_response(sk, make_request().request, T_INIT, CTX_ISS);

    // Wrong Issuer.
    EXPECT_FALSE(make_request().pending_token.finalize_issue(other_issuer().pk, response));

    // Tampered signature.
    IssueResponse bad = response;
    bad[0] ^= 1;
    EXPECT_FALSE(make_request().pending_token.finalize_issue(pk, bad));

    // Signature of a request for another context or initial credit, with the same randomness.
    Context ctx = CTX_ISS;
    ctx[1] ^= 1;
    EXPECT_FALSE(
        issue_request_with_seed(T_INIT, ctx, SEED).pending_token.finalize_issue(pk, response));
    EXPECT_FALSE(issue_request_with_seed(T_INIT + 1, CTX_ISS, SEED)
                     .pending_token.finalize_issue(pk, response));

    // Signature of the commitment rather than its tag.
    const IssueRequest req = make_request().request;
    uov::Target untagged{};
    std::copy_n(req.begin(), COMMITMENT_BYTES, untagged.begin());
    EXPECT_FALSE(make_request().pending_token.finalize_issue(pk, sk.derive_preimage(untagged)));

    // The valid response.
    EXPECT_TRUE(make_request().pending_token.finalize_issue(pk, response));
}

TEST(FinalizeIssue, ConsumesPendingToken) {
    const auto& [pk, sk] = uov_key_pair();
    auto [pending, request] = make_request();
    const IssueResponse response = *issue_response(sk, request, T_INIT, CTX_ISS);

    IssueResponse bad = response;
    bad[0] ^= 1;
    EXPECT_FALSE(std::move(pending).finalize_issue(pk, bad));
    EXPECT_THROW((void)std::move(pending).finalize_issue(pk, response), std::logic_error);
    EXPECT_THROW((void)TokenAccess::nf(pending), std::logic_error);
}

// Spending

TEST(Spend, Verifies) {
    EXPECT_TRUE(spend_verifies(spend().request));
    EXPECT_EQ(to_hex(std::span(spend().request).first<NF_BYTES>()),
              to_hex(TokenAccess::nf(token())));
}

TEST(Spend, RequestCommitsToChange) {
    const auto& pending = spend().pending_spend;
    EXPECT_EQ(TokenAccess::t(pending), T_INIT - D);
    EXPECT_EQ(
        to_hex(std::span(spend().request).subspan<REQ_OFF_C_NEXT, COMMITMENT_BYTES>()),
        to_hex(commit(TokenAccess::nf(pending), CTX_ISS, T_INIT - D, TokenAccess::r(pending))));
    EXPECT_NE(to_hex(TokenAccess::nf(pending)), to_hex(TokenAccess::nf(token())));
}

// Known answer for the seed expansion: nf' || r' are the first 40 bytes of
// SHAKE128("rata" || VERSION || "s1" || seed). Generated with Python:
//
//   hashlib.shake_128(b"rata" + bytes([0]) + b"s1" + bytes(range(0x90, 0xb0))).digest(40)
TEST(Spend, SeedExpansion) {
    const auto& pending = spend().pending_spend;
    EXPECT_EQ(to_hex(TokenAccess::nf(pending)), "a76a1d19445904e37d2dc54f97fcaccbb4fc96467f9bb4ae");
    EXPECT_EQ(to_hex(TokenAccess::r(pending)), "95d6311377d29c53952720fc0baf61a4");
}

TEST(Spend, IsDeterministicGivenSeed) {
    const auto& pk = uov_key_pair().pk;
    const auto b = copy(token()).spend_request_with_seed(pk, D, CTX_ISS, SPEND_SEED);
    EXPECT_TRUE(std::ranges::equal(spend().request, b.request));

    const auto c = copy(token()).spend_request_with_seed(pk, D, CTX_ISS, filled<SEED_BYTES>(0x91));
    EXPECT_FALSE(std::ranges::equal(spend().request, c.request));
    EXPECT_TRUE(spend_verifies(c.request));
}

TEST(Spend, RandomizedVerifies) {
    const auto res = copy(token()).spend_request(uov_key_pair().pk, D, CTX_ISS);
    EXPECT_TRUE(spend_verifies(res.request));
}

// Issue a token, then spend it repeatedly with refunds, until the balance is exhausted.
TEST(Spend, RoundTrip) {
    Token t = issue(filled<SEED_BYTES>(0x01));
    std::set<Nullifier> nullifiers = {TokenAccess::nf(t)};

    t = spend_and_finalize(std::move(t), 30, 0);
    EXPECT_EQ(t.credit(), T_INIT - 30);
    EXPECT_EQ(t.refund(), 0u);
    EXPECT_TRUE(nullifiers.insert(TokenAccess::nf(t)).second);

    t = spend_and_finalize(std::move(t), 50, 7);
    EXPECT_EQ(t.credit(), T_INIT - 80);
    EXPECT_EQ(t.refund(), 7u);
    EXPECT_TRUE(nullifiers.insert(TokenAccess::nf(t)).second);

    // Spending the whole balance includes the refund.
    t = spend_and_finalize(std::move(t), T_INIT - 80 + 7, 0);
    EXPECT_EQ(t.credit(), 0u);
    EXPECT_EQ(t.refund(), 0u);
    EXPECT_TRUE(nullifiers.insert(TokenAccess::nf(t)).second);

    // An empty token can only spend 0 credits.
    const auto& pk = uov_key_pair().pk;
    EXPECT_THROW((void)copy(t).spend_request(pk, 1, CTX_ISS), std::invalid_argument);
    t = spend_and_finalize(std::move(t), 0, 1);
    EXPECT_EQ(t.credit(), 0u);
    EXPECT_EQ(t.refund(), 1u);
    t = spend_and_finalize(std::move(t), 1, 0);
    EXPECT_EQ(t.credit(), 0u);
}

TEST(SpendResponse, ReturnsNullifierAndAmount) {
    const auto& [pk, sk] = uov_key_pair();
    const auto res = spend_response(sk, spend().request, CTX_ISS, 3);
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(to_hex(res->nf), to_hex(TokenAccess::nf(token())));
    EXPECT_EQ(res->d, D);
    EXPECT_EQ(ratatouille::detail::decode_credits(std::span(res->response).first<CREDIT_BYTES>()),
              3u);
}

// spend_response doesn't track nullifiers: it responds to a second spend of the same token, but
// returns the same nullifier, so the caller can reject it.
TEST(SpendResponse, CallerRejectsDoubleSpend) {
    const auto& [pk, sk] = uov_key_pair();
    std::set<Nullifier> used;

    // The Issuer's spend handling: verify, then check and record the nullifier before releasing
    // the response.
    const auto issuer = [&](const SpendRequest& request) -> std::optional<SpendResponse> {
        const auto res = spend_response(sk, request, CTX_ISS, 3);
        if (!res || !used.insert(res->nf).second) {
            return std::nullopt;
        }
        return res->response;
    };

    const auto first = issuer(spend().request);
    ASSERT_TRUE(first.has_value());

    // The same token, spent again with a different proof.
    const auto again = copy(token()).spend_request(pk, 1, CTX_ISS);
    const auto res = spend_response(sk, again.request, CTX_ISS, 3);
    ASSERT_TRUE(res.has_value());
    EXPECT_EQ(to_hex(res->nf), to_hex(TokenAccess::nf(token())));
    EXPECT_FALSE(issuer(again.request));

    // The change token can be spent.
    auto change = TokenAccess::copy(spend().pending_spend).finalize_spend(pk, *first);
    ASSERT_TRUE(change.has_value());
    EXPECT_EQ(change->credit(), T_INIT - D);
    EXPECT_EQ(change->refund(), 3u);
    const auto next = std::move(*change).spend_request(pk, T_INIT - D + 3, CTX_ISS);
    EXPECT_TRUE(issuer(next.request));
}

TEST(SpendResponse, RejectsInvalidRequest) {
    SpendRequest req = spend().request;
    req[REQ_OFF_D + CREDIT_BYTES - 1] ^= 1;
    EXPECT_FALSE(respond(req));
    EXPECT_TRUE(respond(spend().request));
}

TEST(Spend, RejectsWrongContext) {
    Context ctx = CTX_ISS;
    ctx[7] ^= 1;
    EXPECT_FALSE(spend_verifies(spend().request, ctx));
    EXPECT_FALSE(respond(spend().request, 0, ctx));
}

TEST(Spend, RejectsWrongIssuer) {
    // Another Issuer doesn't accept the token: spend_response verifies against the public key of
    // the secret key it signs with.
    EXPECT_FALSE(spend_response(other_issuer().sk, spend().request, CTX_ISS, 0));
}

TEST(Spend, RejectsWrongNullifier) {
    SpendRequest req = spend().request;
    req[0] ^= 1;
    EXPECT_FALSE(spend_verifies(req));

    // The proof for one token doesn't transfer to another token's nullifier.
    const Token other = issue(filled<SEED_BYTES>(0x99));
    req = spend().request;
    std::ranges::copy(TokenAccess::nf(other), req.begin());
    EXPECT_FALSE(spend_verifies(req));
}

TEST(Spend, RejectsWrongAmount) {
    for (const Credits d : {D - 1, D + 1, Credits{0}, MAX_CREDITS}) {
        SpendRequest req = spend().request;
        const auto bytes = ratatouille::detail::encode_credits(d);
        std::ranges::copy(bytes, req.begin() + REQ_OFF_D);
        EXPECT_FALSE(spend_verifies(req)) << "d = " << d;
    }
}

TEST(Spend, RejectsWrongCommitment) {
    for (size_t i = 0; i < 8 * COMMITMENT_BYTES; i += 37) {
        SpendRequest req = spend().request;
        req[REQ_OFF_C_NEXT + i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_FALSE(spend_verifies(req)) << "flipped bit " << i << " of c'";
    }

    // The commitment of another spend.
    SpendRequest req = spend().request;
    const auto other =
        copy(token()).spend_request_with_seed(uov_key_pair().pk, D, CTX_ISS, filled<SEED_BYTES>(1));
    std::copy_n(other.request.begin() + REQ_OFF_C_NEXT, COMMITMENT_BYTES,
                req.begin() + REQ_OFF_C_NEXT);
    EXPECT_FALSE(spend_verifies(req));
}

TEST(Spend, RejectsTamperedProof) {
    SpendRequest req = spend().request;
    auto proof = std::span(req).last<SPEND_PROOF_BYTES>();
    for (size_t i = 0; i < SPEND_PROOF_BYTES; i += 211) {
        proof[i] ^= 0x10;
        EXPECT_FALSE(spend_verifies(req)) << "flipped a bit of byte " << i;
        proof[i] ^= 0x10;
    }
    // The last bytes are delta (chall_3), iv_pre and the grinding counter.
    for (size_t i = SPEND_PROOF_BYTES - 36; i < SPEND_PROOF_BYTES; ++i) {
        proof[i] ^= 0x01;
        EXPECT_FALSE(spend_verifies(req)) << "flipped a bit of byte " << i;
        proof[i] ^= 0x01;
    }
    EXPECT_TRUE(spend_verifies(req));
}

// Invalid arguments leave the token unchanged, so it can still be spent afterwards.
TEST(Spend, RequestRejectsInvalidArguments) {
    const auto& pk = uov_key_pair().pk;
    Token t = copy(token());

    // Insufficient balance.
    EXPECT_THROW((void)std::move(t).spend_request(pk, T_INIT + 1, CTX_ISS), std::invalid_argument);
    EXPECT_THROW((void)std::move(t).spend_request(pk, MAX_CREDITS, CTX_ISS), std::invalid_argument);

    // The token wasn't issued by this Issuer or for this context.
    EXPECT_THROW((void)std::move(t).spend_request(other_issuer().pk, D, CTX_ISS),
                 std::invalid_argument);
    Context ctx = CTX_ISS;
    ctx[0] ^= 1;
    EXPECT_THROW((void)std::move(t).spend_request(pk, D, ctx), std::invalid_argument);

    // The token's contents are wrong.
    Token bad = TokenAccess::make(TokenAccess::nf(token()), T_INIT + 1, TokenAccess::r(token()), 0,
                                  TokenAccess::s(token()));
    EXPECT_THROW((void)std::move(bad).spend_request(pk, D, CTX_ISS), std::invalid_argument);
    bad = TokenAccess::make(TokenAccess::nf(token()), T_INIT, TokenAccess::r(token()), 1,
                            TokenAccess::s(token()));
    EXPECT_THROW((void)std::move(bad).spend_request(pk, D, CTX_ISS), std::invalid_argument);

    // The token is still intact.
    const auto res = std::move(t).spend_request_with_seed(pk, D, CTX_ISS, SPEND_SEED);
    EXPECT_TRUE(std::ranges::equal(res.request, spend().request));
}

// The balance t + x may exceed the largest credit value, in which case the change must not.
TEST(Spend, OverflowingBalance) {
    const auto& [pk, sk] = uov_key_pair();
    const Nullifier nf = filled<NF_BYTES>(0x30);
    const Opening r = filled<R_BYTES>(0x40);
    const Credits t = MAX_CREDITS - 1, x = 10;
    const uov::Preimage s = sk.derive_preimage(tag(commit(nf, CTX_ISS, t, r), x));
    const Token big = TokenAccess::make(nf, t, r, x, s);

    // t + x - d = 2^64 + 8 - d must be at most 2^64 - 1.
    EXPECT_THROW((void)copy(big).spend_request(pk, 0, CTX_ISS), std::invalid_argument);
    EXPECT_THROW((void)copy(big).spend_request(pk, 8, CTX_ISS), std::invalid_argument);

    auto res = copy(big).spend_request(pk, 9, CTX_ISS);
    EXPECT_EQ(TokenAccess::t(res.pending_spend), MAX_CREDITS);
    EXPECT_TRUE(spend_verifies(res.request));

    res = copy(big).spend_request(pk, MAX_CREDITS, CTX_ISS);
    EXPECT_EQ(TokenAccess::t(res.pending_spend), 9u);
    EXPECT_TRUE(spend_verifies(res.request));
}

TEST(Spend, ConsumesToken) {
    const auto& pk = uov_key_pair().pk;
    Token t = copy(token());
    (void)std::move(t).spend_request(pk, D, CTX_ISS);
    EXPECT_THROW((void)std::move(t).spend_request(pk, D, CTX_ISS), std::logic_error);
    EXPECT_THROW((void)std::move(t).spend_request_with_seed(pk, D, CTX_ISS, SPEND_SEED),
                 std::logic_error);
    EXPECT_THROW((void)t.credit(), std::logic_error);
    EXPECT_THROW((void)t.refund(), std::logic_error);
}

TEST(FinalizeSpend, ReturnsChangeToken) {
    const auto& pk = uov_key_pair().pk;
    const auto response = respond(spend().request, 12);
    ASSERT_TRUE(response.has_value());
    auto t = TokenAccess::copy(spend().pending_spend).finalize_spend(pk, *response);
    ASSERT_TRUE(t.has_value());
    EXPECT_EQ(t->credit(), T_INIT - D);
    EXPECT_EQ(t->refund(), 12u);
    EXPECT_EQ(to_hex(TokenAccess::nf(*t)), to_hex(TokenAccess::nf(spend().pending_spend)));
}

TEST(FinalizeSpend, RejectsInvalidResponse) {
    const auto& pk = uov_key_pair().pk;
    const SpendResponse response = *respond(spend().request, 12);
    const auto pending = [] { return TokenAccess::copy(spend().pending_spend); };

    // Wrong Issuer.
    EXPECT_FALSE(pending().finalize_spend(other_issuer().pk, response));

    // Wrong refund.
    for (const Credits x : {Credits{0}, Credits{13}, MAX_CREDITS}) {
        SpendResponse bad = response;
        std::ranges::copy(ratatouille::detail::encode_credits(x), bad.begin());
        EXPECT_FALSE(pending().finalize_spend(pk, bad)) << "x' = " << x;
    }

    // Tampered signature.
    SpendResponse bad = response;
    bad[RESP_OFF_S] ^= 1;
    EXPECT_FALSE(pending().finalize_spend(pk, bad));

    // The response to another spend.
    const auto other =
        copy(token()).spend_request_with_seed(pk, D, CTX_ISS, filled<SEED_BYTES>(0x91));
    EXPECT_FALSE(pending().finalize_spend(pk, *respond(other.request, 12)));

    EXPECT_TRUE(pending().finalize_spend(pk, response));
}

TEST(FinalizeSpend, ConsumesPendingSpend) {
    const auto& pk = uov_key_pair().pk;
    const SpendResponse response = *respond(spend().request);
    PendingSpend pending = TokenAccess::copy(spend().pending_spend);
    EXPECT_TRUE(std::move(pending).finalize_spend(pk, response));
    EXPECT_THROW((void)std::move(pending).finalize_spend(pk, response), std::logic_error);
    EXPECT_THROW((void)TokenAccess::t(pending), std::logic_error);
}
