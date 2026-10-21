// Tests for the issuance proof relation of unbound tokens.

#include "vole_mole/ihat.hpp"
#include "vole_mole/keccak.hpp"
#include "vole_mole/uov.hpp"

#include "ihat/commit.hpp"        // internal
#include "ihat/unbound_issue.hpp" // internal
#include "keccak/segmented.hpp"   // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::ihat;
using namespace vole_mole::ihat::detail;
using vole_mole::test::filled;
using vole_mole::test::PlainQS;
using vole_mole::test::to_hex;

namespace {

const Context CTX_ISS = filled<CTX_BYTES>(0x10);
const Context CTX_RED = filled<CTX_BYTES>(0x20);
const NfKey NF_KEY = filled<NF_KEY_BYTES>(0x30);
const Opening R = filled<R_BYTES>(0x40);

std::vector<bool> evaluate(const std::array<uint8_t, UNBOUND_ISSUE_WITNESS_BYTES>& w,
                           const UnboundIssueRelation::instance& x) {
    PlainQS qs{w.data(), {}};
    const std::array<uint8_t, UnboundIssueParams::CONSTS::QS::CHALLENGE_BYTES> chal2{};
    UnboundIssueRelation::constraints(&qs, x, chal2);
    return qs.violated;
}

size_t count_violated(const std::vector<bool>& v) {
    size_t n = 0;
    for (bool b : v) {
        n += b;
    }
    return n;
}

const UnboundIssueRelation::instance INSTANCE = {unbound_commit(NF_KEY, CTX_ISS, R), CTX_ISS};

} // namespace

// Known answers for UnboundCom and Derive, which check their input layouts. Generated with
// tests/keccak/keccak_ref.py:
//
//   f = lambda n, s: bytes((s + i) & 0xff for i in range(n))
//   pad = lambda st: st + bytes(100 - len(st))
//   keccak_p(pad(b"mous\x01c0" + f(16, 0x40) + bytes(9) + f(16, 0x10) + f(16, 0x30)), 800, 12)[:45]
//   keccak_p(pad(b"mous\x01d0" + f(16, 0x30) + bytes(9) + f(16, 0x20)), 800, 12)[:24]
TEST(Unbound, CommitKnownAnswer) {
    EXPECT_EQ(to_hex(unbound_commit(NF_KEY, CTX_ISS, R)),
              "f190ca1f196f73bbfb0cd0734d6f35363c5e0dc65b77a1740579856b498f9fd9417a0b509e40712bb4d6"
              "7b2237");
}

TEST(Unbound, DeriveKnownAnswer) {
    EXPECT_EQ(to_hex(derive(NF_KEY, CTX_RED)), "61cf25dd8db795cd60d38d41d0648eee17108af59db7e0a1");
}

// The commitment and nullifier depend on each of their inputs.
TEST(Unbound, CommitAndDeriveBindInputs) {
    const Commitment t = unbound_commit(NF_KEY, CTX_ISS, R);
    const Nullifier nf = derive(NF_KEY, CTX_RED);
    for (size_t i = 0; i < 8 * NF_KEY_BYTES; ++i) {
        NfKey k = NF_KEY;
        k[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_NE(unbound_commit(k, CTX_ISS, R), t) << "nf_key bit " << i;
        EXPECT_NE(derive(k, CTX_RED), nf) << "nf_key bit " << i;
    }
    for (size_t i = 0; i < 8 * CTX_BYTES; ++i) {
        Context ctx = CTX_ISS;
        ctx[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_NE(unbound_commit(NF_KEY, ctx, R), t) << "ctx_iss bit " << i;
        ctx = CTX_RED;
        ctx[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_NE(derive(NF_KEY, ctx), nf) << "ctx_red bit " << i;
    }
    for (size_t i = 0; i < 8 * R_BYTES; ++i) {
        Opening r = R;
        r[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_NE(unbound_commit(NF_KEY, CTX_ISS, r), t) << "r bit " << i;
    }
}

TEST(UnboundIssueRelation, HonestWitnessSatisfiesAllConstraints) {
    const auto w = encode_unbound_issue_witness(NF_KEY, CTX_ISS, R);
    const auto violated = evaluate(w, INSTANCE);
    EXPECT_EQ(violated.size(), UnboundIssueRelation::NUM_CONSTRAINTS);
    EXPECT_EQ(count_violated(violated), 0u);
}

TEST(UnboundIssueRelation, AnyWitnessBitFlipViolatesAConstraint) {
    const auto honest = encode_unbound_issue_witness(NF_KEY, CTX_ISS, R);
    for (size_t i = 0; i < UNBOUND_ISSUE_WITNESS_BITS; ++i) {
        auto w = honest;
        w[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_GT(count_violated(evaluate(w, INSTANCE)), 0u)
            << "flipping witness bit " << i << " is not detected";
    }
}

TEST(UnboundIssueRelation, WrongInstanceViolatesAConstraint) {
    const auto w = encode_unbound_issue_witness(NF_KEY, CTX_ISS, R);

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

// Consistently changing the witness (e.g., to a different nullifier key) yields a witness for a
// different commitment only.
TEST(UnboundIssueRelation, OtherOpeningSatisfiesOtherCommitmentOnly) {
    NfKey other_nf_key = NF_KEY;
    other_nf_key[3] ^= 0x10;
    const auto w = encode_unbound_issue_witness(other_nf_key, CTX_ISS, R);
    EXPECT_GT(count_violated(evaluate(w, INSTANCE)), 0u);

    const UnboundIssueRelation::instance other = {unbound_commit(other_nf_key, CTX_ISS, R),
                                                  CTX_ISS};
    EXPECT_EQ(count_violated(evaluate(w, other)), 0u);
}

TEST(UnboundIssueRelation, WitnessIsConsistent) {
    using namespace keccak::detail;
    const auto w = encode_unbound_issue_witness(NF_KEY, CTX_ISS, R);
    EXPECT_TRUE(std::ranges::equal(std::span(w).subspan<UNBOUND_ISSUE_WIT_OFF_R, R_BYTES>(), R));
    EXPECT_TRUE(std::ranges::equal(
        std::span(w).subspan<UNBOUND_ISSUE_WIT_OFF_NF_KEY, NF_KEY_BYTES>(), NF_KEY));

    // Re-run the last segment from the last committed state; it must yield the commitment.
    Kp800State state;
    std::copy_n(w.begin() + UNBOUND_ISSUE_WIT_OFF_STATES +
                    (NUM_COMMITTED_STATES - 1) * KP800_STATE_BYTES,
                KP800_STATE_BYTES, state.begin());
    keccak_p800_rounds(state, SEGMENT_START[NUM_COMMITTED_STATES], FINAL_ROUNDS);
    EXPECT_EQ(to_hex(INSTANCE.t), to_hex(std::span(state).first<uov::M>()));
}
