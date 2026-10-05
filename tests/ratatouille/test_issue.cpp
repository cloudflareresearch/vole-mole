// Tests for the issuance proof relation.

#include "ratatouille/issue.hpp" // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::ratatouille;
using namespace vole_mole::ratatouille::detail;
using vole_mole::test::filled;
using vole_mole::test::PlainQS;

namespace {

const Context CTX_ISS = filled<CTX_BYTES>(0x10);
const Nullifier NF = filled<NF_BYTES>(0x30);
const Opening R = filled<R_BYTES>(0x40);
constexpr Credits T_INIT = 1000;

std::vector<bool> evaluate(const std::array<uint8_t, ISSUE_WITNESS_BYTES>& w,
                           const IssueRelation::instance& x) {
    // An arbitrary QuickSilver challenge, from which any random linear combination is derived.
    static const auto chal2 = filled<IssueParams::CONSTS::QS::CHALLENGE_BYTES>(0x50);
    PlainQS qs{w.data(), {}};
    IssueRelation::constraints(&qs, x, chal2);
    return qs.violated;
}

size_t count_violated(const std::vector<bool>& v) {
    return static_cast<size_t>(std::ranges::count(v, true));
}

const IssueRelation::instance INSTANCE = {commit(NF, CTX_ISS, T_INIT, R), T_INIT, CTX_ISS};

} // namespace

TEST(Credits, Encoding) {
    EXPECT_EQ(encode_credits(0x0102030405060708),
              (CreditBytes{0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01}));
    const CreditBytes b = encode_credits(0xfedcba9876543210);
    EXPECT_EQ(decode_credits(b), 0xfedcba9876543210u);

    // Bit i of the credit value is bit credit_bit(0, i) of the encoding.
    const Credits v = 0x8000000000000001 | (Credits{1} << 9);
    for (size_t i = 0; i < 64; ++i) {
        const size_t j = credit_bit(0, i);
        EXPECT_EQ((encode_credits(v)[j / 8] >> (j % 8)) & 1, (v >> i) & 1) << "bit " << i;
    }
}

TEST(IssueRelation, HonestWitnessSatisfiesAllConstraints) {
    const auto violated = evaluate(encode_issue_witness(NF, CTX_ISS, T_INIT, R), INSTANCE);
    EXPECT_EQ(violated.size(), IssueRelation::NUM_CONSTRAINTS);
    EXPECT_EQ(count_violated(violated), 0u);
}

TEST(IssueRelation, AnyWitnessBitFlipViolatesAConstraint) {
    const auto honest = encode_issue_witness(NF, CTX_ISS, T_INIT, R);
    for (size_t i = 0; i < ISSUE_WITNESS_BITS; ++i) {
        auto w = honest;
        w[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_GT(count_violated(evaluate(w, INSTANCE)), 0u)
            << "flipping witness bit " << i << " is not detected";
    }
}

TEST(IssueRelation, WrongInstanceViolatesAConstraint) {
    const auto w = encode_issue_witness(NF, CTX_ISS, T_INIT, R);

    // Each bit of c is constrained.
    for (size_t i = 0; i < 8 * COMMITMENT_BYTES; ++i) {
        auto x = INSTANCE;
        x.c[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_EQ(count_violated(evaluate(w, x)), 1u) << "flipping bit " << i << " of c";
    }

    // The initial credit is bound.
    for (size_t i = 0; i < 64; ++i) {
        auto x = INSTANCE;
        x.t_init ^= Credits{1} << i;
        EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "flipping bit " << i << " of T_init";
    }

    // The issuance context is bound.
    auto x = INSTANCE;
    x.ctx_iss[0] ^= 1;
    EXPECT_GT(count_violated(evaluate(w, x)), 0u);
}

// A witness for a commitment to a different credit value satisfies that commitment only.
TEST(IssueRelation, OtherCreditSatisfiesOtherCommitmentOnly) {
    const auto w = encode_issue_witness(NF, CTX_ISS, T_INIT + 1, R);
    EXPECT_GT(count_violated(evaluate(w, INSTANCE)), 0u);

    const IssueRelation::instance other = {commit(NF, CTX_ISS, T_INIT + 1, R), T_INIT + 1, CTX_ISS};
    EXPECT_EQ(count_violated(evaluate(w, other)), 0u);
}

TEST(IssueRelation, WitnessIsConsistent) {
    using namespace keccak::detail;
    const auto w = encode_issue_witness(NF, CTX_ISS, T_INIT, R);
    Kp800State state;
    std::copy_n(w.begin() + ISSUE_WIT_OFF_STATES + (NUM_COMMITTED_STATES - 1) * KP800_STATE_BYTES,
                KP800_STATE_BYTES, state.begin());
    keccak_p800_rounds(state, SEGMENT_START[NUM_COMMITTED_STATES], FINAL_ROUNDS);
    const Commitment c = commit(NF, CTX_ISS, T_INIT, R);
    EXPECT_TRUE(std::equal(c.begin(), c.end(), state.begin()));
}

// The commitment and tag have the layout given in the draft.
TEST(Commitment, Layout) {
    const Kp800State com = encode_com_state(NF, CTX_ISS, 0x0102030405060708, R);
    Kp800State want{};
    size_t off = 0;
    const auto put = [&](std::span<const uint8_t> bytes) {
        std::ranges::copy(bytes, want.begin() + static_cast<std::ptrdiff_t>(off));
        off += bytes.size();
    };
    const std::array<uint8_t, 7> com_dst = {'r', 'a', 't', 'a', VERSION, 'c', '0'};
    put(com_dst);
    put(R);
    off += 25 - R_BYTES;
    put(CTX_ISS);
    put(encode_credits(0x0102030405060708));
    put(NF);
    EXPECT_EQ(off + 68 - NF_BYTES - CTX_BYTES - CREDIT_BYTES, KP800_STATE_BYTES);
    EXPECT_EQ(com, want);

    const Commitment c = filled<COMMITMENT_BYTES>(0xa0);
    const Kp800State tg = encode_tag_state(c, 42);
    want = {};
    off = 0;
    const std::array<uint8_t, 7> tag_dst = {'r', 'a', 't', 'a', VERSION, 't', '0'};
    put(tag_dst);
    off += 25;
    put(c);
    put(encode_credits(42));
    EXPECT_EQ(off + 36 - CREDIT_BYTES, KP800_STATE_BYTES);
    EXPECT_EQ(tg, want);
}
