// Tests for the issuance proof relation.

#include "vole_mole/keccak.hpp"
#include "vole_mole/moussaka.hpp"
#include "vole_mole/uov.hpp"

#include "keccak/segmented.hpp" // internal
#include "moussaka/commit.hpp"  // internal
#include "moussaka/issue.hpp"   // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
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

namespace {

// The input of the Keccak evaluation of IssueRelation::constraints for witness w, as a state.
Kp800State keccak_input(const std::array<uint8_t, ISSUE_WITNESS_BYTES>& w, const Context& ctx_iss) {
    PlainQS qs{w.data(), {}};
    const auto bits =
        keccak::detail::qs_input(&qs, encode_com_state({}, ctx_iss, {}, {}), COM_TO_WIT);
    Kp800State s{};
    for (size_t i = 0; i < bits.size(); ++i) {
        s[i / 8] |= static_cast<uint8_t>(bits[i].v << (i % 8));
    }
    return s;
}

} // namespace

// For any witness, the input of the Keccak evaluation is the commitment input for the nf, ctx_red,
// and r read from the witness. Each input byte is either a public constant or a copy of one witness
// byte, so two witnesses suffice: in the first, the bytes of r, ctx_red, and nf are pairwise
// distinct (which pins down the witness byte that each secret input byte is copied from), and the
// second is its complement (so a public input byte can't depend on the witness).
TEST(IssueRelation, KeccakInputIsCommitmentInput) {
    std::array<uint8_t, ISSUE_WITNESS_BYTES> w{};
    for (size_t i = 0; i < WIT_OFF_STATES; ++i) {
        w[i] = static_cast<uint8_t>(i + 1);
    }
    for (int pass = 0; pass < 2; ++pass) {
        Opening r;
        Context ctx_red;
        Nullifier nf;
        std::copy_n(w.begin() + WIT_OFF_R, R_BYTES, r.begin());
        std::copy_n(w.begin() + WIT_OFF_CTX_RED, CTX_BYTES, ctx_red.begin());
        std::copy_n(w.begin() + WIT_OFF_NF, NF_BYTES, nf.begin());
        EXPECT_EQ(keccak_input(w, CTX_ISS), encode_com_state(nf, CTX_ISS, ctx_red, r))
            << "pass " << pass;
        for (uint8_t& b : w) {
            b = static_cast<uint8_t>(~b);
        }
    }
}

// The commitment input has the layout
//
//   "mous" || VERSION || "c0" || r || 0^(25 - r_len) || ctx_iss || ctx_red || nf ||
//   0^(68 - nf_len - 2 ctx_len),
//
// and the commitment is its first M bytes after Keccak-p[800, 12].
TEST(Commitment, Layout) {
    const Kp800State com = encode_com_state(NF, CTX_ISS, CTX_RED, R);
    Kp800State want{};
    size_t off = 0;
    const auto put = [&](std::span<const uint8_t> bytes) {
        std::ranges::copy(bytes, want.begin() + static_cast<std::ptrdiff_t>(off));
        off += bytes.size();
    };
    const std::array<uint8_t, 7> dst = {'m', 'o', 'u', 's', VERSION, 'c', '0'};
    put(dst);
    put(R);
    off += 25 - R_BYTES;
    put(CTX_ISS);
    put(CTX_RED);
    put(NF);
    EXPECT_EQ(off + 68 - NF_BYTES - 2 * CTX_BYTES, KP800_STATE_BYTES);
    EXPECT_EQ(com, want);

    const Kp800State out = keccak_p800(com);
    const Commitment t = commit(NF, CTX_ISS, CTX_RED, R);
    EXPECT_TRUE(std::equal(t.begin(), t.end(), out.begin()));
}
