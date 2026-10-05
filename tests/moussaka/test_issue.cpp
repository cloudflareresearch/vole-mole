// Tests for the issuance proof relation.

#include "moussaka/issue.hpp" // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::moussaka;
using namespace vole_mole::moussaka::detail;
using vole_mole::test::filled;
using vole_mole::test::PlainQS;

namespace {

const Context CTX_ISS = filled<CTX_BYTES>(0x10);
const Context CTX_RED = filled<CTX_BYTES>(0x20);
const Nullifier NF = filled<NF_BYTES>(0x30);
const Opening R = filled<R_BYTES>(0x40);

std::vector<bool> evaluate(const std::array<uint8_t, ISSUE_WITNESS_BYTES>& w,
                           const IssueRelation::instance& x) {
    PlainQS qs{w.data(), {}};
    const std::array<uint8_t, IssueParams::CONSTS::QS::CHALLENGE_BYTES> chal2{};
    IssueRelation::constraints(&qs, x, chal2);
    return qs.violated;
}

size_t count_violated(const std::vector<bool>& v) {
    size_t n = 0;
    for (bool b : v) {
        n += b;
    }
    return n;
}

const IssueRelation::instance INSTANCE = {commit(NF, CTX_ISS, CTX_RED, R), CTX_ISS};

} // namespace

TEST(IssueRelation, HonestWitnessSatisfiesAllConstraints) {
    const auto w = encode_issue_witness(NF, CTX_ISS, CTX_RED, R);
    const auto violated = evaluate(w, INSTANCE);
    EXPECT_EQ(violated.size(), IssueRelation::NUM_CONSTRAINTS);
    EXPECT_EQ(count_violated(violated), 0u);
}

TEST(IssueRelation, AnyWitnessBitFlipViolatesAConstraint) {
    const auto honest = encode_issue_witness(NF, CTX_ISS, CTX_RED, R);
    for (size_t i = 0; i < ISSUE_WITNESS_BITS; ++i) {
        auto w = honest;
        w[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_GT(count_violated(evaluate(w, INSTANCE)), 0u)
            << "flipping witness bit " << i << " is not detected";
    }
}

TEST(IssueRelation, WrongInstanceViolatesAConstraint) {
    const auto w = encode_issue_witness(NF, CTX_ISS, CTX_RED, R);

    // Each bit of t is constrained.
    for (size_t i = 0; i < 8 * uov::M; ++i) {
        auto x = INSTANCE;
        x.t[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_EQ(count_violated(evaluate(w, x)), 1u) << "flipping bit " << i << " of t";
    }

    // The issuance context is bound.
    auto x = INSTANCE;
    x.ctx_iss[0] ^= 1;
    EXPECT_GT(count_violated(evaluate(w, x)), 0u);
}

// Consistently changing the witness (e.g., to a different redemption context) yields a witness
// for a different commitment only.
TEST(IssueRelation, OtherOpeningSatisfiesOtherCommitmentOnly) {
    Context other_ctx_red = CTX_RED;
    other_ctx_red[3] ^= 0x10;
    const auto w = encode_issue_witness(NF, CTX_ISS, other_ctx_red, R);
    EXPECT_GT(count_violated(evaluate(w, INSTANCE)), 0u);

    const IssueRelation::instance other = {commit(NF, CTX_ISS, other_ctx_red, R), CTX_ISS};
    EXPECT_EQ(count_violated(evaluate(w, other)), 0u);
}
