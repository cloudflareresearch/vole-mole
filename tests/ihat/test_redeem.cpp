// Tests for the redemption proof relation.

#include "vole_mole/ihat.hpp"
#include "vole_mole/keccak.hpp"
#include "vole_mole/uov.hpp"

#include "ihat/circuit.hpp"     // internal
#include "ihat/commit.hpp"      // internal
#include "ihat/redeem.hpp"      // internal
#include "ihat/report.hpp"      // internal
#include "keccak/segmented.hpp" // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::ihat;
using namespace vole_mole::ihat::detail;
using vole_mole::test::filled;
using vole_mole::test::PlainQS;
using vole_mole::test::uov_key_pair;
using vole_mole::test::UovKeyPair;

namespace {

const Context CTX_ISS = filled<CTX_BYTES>(0x10);
const Context CTX_RED = filled<CTX_BYTES>(0x20);
const ChallengeDigest CHALLENGE_DIGEST = filled<CHALLENGE_DIGEST_BYTES>(0x70);
const Nullifier NF = filled<NF_BYTES>(0x30);
const Opening R = filled<R_BYTES>(0x40);
const Report K = filled<REPORT_BYTES>(0xa0);

using Witness = std::array<uint8_t, REDEEM_WITNESS_BYTES>;

// Three distinct Anchors. The issuing Anchor is the fixed test key pair, at index ISSUER.
struct Anchors {
    UovKeyPair a{uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x61)}};
    UovKeyPair c{uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x62)}};
    std::array<AnchorRef, 3> keys = {a.pk, uov_key_pair().pk, c.pk};
};
constexpr size_t ISSUER = 1;

const Anchors& anchors() {
    static const Anchors a;
    return a;
}

const uov::Preimage& signature() {
    static const uov::Preimage s =
        uov_key_pair().sk.derive_preimage(commit(NF, CTX_ISS, CTX_RED, R));
    return s;
}

// The Moderator's share and the tag for report k and the Anchor at index i.
Redemption public_report(const Report& k, size_t i) {
    const OpenedReport opened = open_report_output(expand_report(k));
    return {NF, moderator_share(opened.share, i), opened.tag};
}

RedeemRelation::instance make_instance(AnchorSpan keys = anchors().keys, size_t i = ISSUER,
                                       const Report& k = K) {
    const Redemption pub = public_report(k, i);
    return {keys, NF, CTX_ISS, CTX_RED, CHALLENGE_DIGEST, pub.share, pub.tag};
}

Witness honest_witness(size_t i = ISSUER, const Report& k = K) {
    return encode_redeem_witness(NF, CTX_ISS, CTX_RED, R, signature(), k, i);
}

std::vector<bool> evaluate(const Witness& w, const RedeemRelation::instance& x) {
    // An arbitrary QuickSilver challenge, from which the random linear combination is derived.
    static const auto chal2 = filled<RedeemParams::CONSTS::QS::CHALLENGE_BYTES>(0x50);
    PlainQS qs{w.data(), {}};
    RedeemRelation::constraints(&qs, x, chal2);
    return qs.violated;
}

size_t count_violated(const std::vector<bool>& v) {
    size_t n = 0;
    for (bool b : v) {
        n += b;
    }
    return n;
}

// Indices of the selector constraints.
constexpr size_t SELECTOR_OFF = 8 * REDEEM_WIT_OFF_B; // b[u] is a bit, or zero if u >= N
constexpr size_t PARITY_OFF = SELECTOR_OFF + MAX_ANCHORS;
constexpr size_t WEIGHT_OFF = PARITY_OFF + MAX_ANCHORS - 1;
// The report constraints come last.
constexpr size_t REPORT_OFF = RedeemRelation::NUM_CONSTRAINTS - REPORT_NUM_CONSTRAINTS;

// Number of violated constraints before the report constraints.
size_t count_violated_before_report(const std::vector<bool>& v) {
    return count_violated(std::vector<bool>(v.begin(), v.begin() + REPORT_OFF));
}

void set_selector(Witness& w, size_t u, bool value) {
    const size_t b = selector_bit(u);
    w[b / 8] = static_cast<uint8_t>((w[b / 8] & ~(1u << (b % 8))) | (unsigned{value} << (b % 8)));
}

} // namespace

TEST(RedeemRelation, HonestWitnessSatisfiesAllConstraints) {
    const auto violated = evaluate(honest_witness(), make_instance());
    EXPECT_EQ(violated.size(), RedeemRelation::NUM_CONSTRAINTS);
    EXPECT_EQ(count_violated(violated), 0u);
}

// The issuing Anchor may be anywhere in the Anchor Set, including when it's the only Anchor.
TEST(RedeemRelation, HonestWitnessAtEveryPosition) {
    const uov::PublicKey& issuer = uov_key_pair().pk;
    const uov::PublicKey& other = anchors().keys[0];
    for (const size_t n : {size_t{1}, size_t{2}, size_t{5}}) {
        for (size_t i = 0; i < n; ++i) {
            std::vector<AnchorRef> keys(n, other);
            keys[i] = issuer;
            const auto violated = evaluate(honest_witness(i), make_instance(keys, i));
            EXPECT_EQ(violated.size(), RedeemRelation::NUM_CONSTRAINTS);
            EXPECT_EQ(count_violated(violated), 0u) << "n = " << n << ", i = " << i;
        }
    }
}

TEST(RedeemRelation, HonestWitnessForLargestAnchorSet) {
    std::vector<AnchorRef> keys(MAX_ANCHORS, anchors().keys[0]);
    keys.back() = uov_key_pair().pk;
    EXPECT_EQ(count_violated(
                  evaluate(honest_witness(MAX_ANCHORS - 1), make_instance(keys, MAX_ANCHORS - 1))),
              0u);
}

// Every bit of the witness matters: r and the intermediate states determine the commitment, s
// determines the signature, k and its intermediate states determine the report, and b determines
// the selected Anchor.
TEST(RedeemRelation, AnyWitnessBitFlipViolatesAConstraint) {
    const auto honest = honest_witness();
    const auto x = make_instance();
    for (size_t i = 0; i < REDEEM_WITNESS_BITS; ++i) {
        auto w = honest;
        w[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_GT(count_violated(evaluate(w, x)), 0u)
            << "flipping witness bit " << i << " is not detected";
    }
}

TEST(RedeemRelation, RejectsWrongSelector) {
    const auto x = make_instance();
    const auto honest = honest_witness();

    // No Anchor is selected. (Then Q = 0, so the output constraints are violated too.)
    auto w = honest;
    set_selector(w, ISSUER, false);
    EXPECT_TRUE(evaluate(w, x)[WEIGHT_OFF]) << "empty selector";

    // Another Anchor is selected.
    for (size_t u = 0; u < x.anchors.size(); ++u) {
        if (u != ISSUER) {
            EXPECT_GT(count_violated(evaluate(honest_witness(u), x)), 0u) << "selected " << u;
        }
    }

    // Two or three Anchors are selected.
    for (size_t u = 0; u < x.anchors.size(); ++u) {
        if (u != ISSUER) {
            w = honest;
            set_selector(w, u, true);
            EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "also selected " << u;
        }
    }
    w = honest;
    set_selector(w, 0, true);
    set_selector(w, 2, true);
    EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "selected all three";

    // An index beyond the end of the Anchor Set is selected. (Then Q = 0, so the output
    // constraints are violated too.)
    for (const size_t u : {x.anchors.size(), MAX_ANCHORS - 1}) {
        w = honest;
        set_selector(w, ISSUER, false);
        set_selector(w, u, true);
        const auto violated = evaluate(w, x);
        EXPECT_TRUE(violated[SELECTOR_OFF + u]) << "selected " << u;
        EXPECT_FALSE(violated[WEIGHT_OFF]) << "selected " << u;
    }
}

// The parity constraints are needed: the weight constraint alone accepts any odd number of
// selected Anchors. If P[0] and P[2] are the same key, then selecting all of 0, 1, 2 selects
// Q = P[1], since P[0] + P[2] cancel out in characteristic 2. (AnchorSet rejects repeated keys, but
// the relation doesn't rely on that. Even with distinct keys, selecting several Anchors would
// select their sum, which is a different map than any one of them.)
TEST(RedeemRelation, ParityConstraintsRejectOddWeight) {
    const uov::PublicKey& other = anchors().keys[0];
    const std::array<AnchorRef, 3> keys = {other, uov_key_pair().pk, other};
    const auto x = make_instance(keys);
    auto w = honest_witness();
    set_selector(w, 0, true);
    set_selector(w, 2, true);
    const auto violated = evaluate(w, x);

    // Only the first parity constraint is violated, apart from the report constraints. (The
    // report is for V = e_1, not for b = e_0 + e_1 + e_2.)
    EXPECT_EQ(count_violated_before_report(violated), 1u);
    EXPECT_TRUE(violated[PARITY_OFF]); // b[0] * b[1] = 0
}

TEST(RedeemRelation, WrongInstanceViolatesAConstraint) {
    const auto w = honest_witness();

    auto x = make_instance();
    x.nf[0] ^= 1;
    EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "nf";

    x = make_instance();
    x.ctx_iss[0] ^= 1;
    EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "ctx_iss";

    x = make_instance();
    x.ctx_red[CTX_BYTES - 1] ^= 0x80;
    EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "ctx_red";

    x = make_instance();
    x.share[MAX_ANCHORS - 1] ^= 0x8000;
    EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "share";

    x = make_instance();
    x.tag[REPORT_TAG_BYTES - 1] ^= 0x80;
    EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "tag";

    // The issuing Anchor is moved or removed.
    auto keys = anchors().keys;
    std::swap(keys[0], keys[ISSUER]);
    EXPECT_GT(count_violated(evaluate(w, make_instance(keys))), 0u) << "moved";
    keys = anchors().keys;
    keys[ISSUER] = keys[0];
    EXPECT_GT(count_violated(evaluate(w, make_instance(keys))), 0u) << "removed";
    EXPECT_GT(count_violated(evaluate(w, make_instance(AnchorSpan(keys).first(ISSUER)))), 0u)
        << "truncated";
}

// Every bit of the Moderator's share and of the tag is bound by the report constraints, and only
// by those.
TEST(RedeemRelation, AnyShareOrTagBitFlipViolatesAReportConstraint) {
    const auto w = honest_witness();
    for (size_t u = 0; u < MAX_ANCHORS; ++u) {
        for (size_t b = 0; b < 16; ++b) {
            auto x = make_instance();
            x.share[u] ^= static_cast<uint16_t>(1u << b);
            const auto violated = evaluate(w, x);
            EXPECT_EQ(count_violated_before_report(violated), 0u);
            EXPECT_GT(count_violated(violated), 0u) << "share[" << u << "] bit " << b;
        }
    }
    for (size_t i = 0; i < 8 * REPORT_TAG_BYTES; ++i) {
        auto x = make_instance();
        x.tag[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        const auto violated = evaluate(w, x);
        EXPECT_EQ(count_violated_before_report(violated), 0u);
        EXPECT_GT(count_violated(violated), 0u) << "tag bit " << i;
    }
}

// A Client can't attribute its redemption to an Anchor other than the issuing one.
TEST(RedeemRelation, RejectsMisattribution) {
    const auto w = honest_witness();
    for (size_t j = 0; j < MAX_ANCHORS; ++j) {
        if (j == ISSUER) {
            continue;
        }
        // The share is for e_j, but the selector (and the signature) is for the issuer.
        const auto violated = evaluate(w, make_instance(anchors().keys, j));
        EXPECT_EQ(count_violated_before_report(violated), 0u) << "j = " << j;
        EXPECT_GT(count_violated(violated), 0u) << "j = " << j;
    }

    // Nor can it prove a share for another report than the one it gives the Aggregator: the share
    // and tag for one report don't verify with another report in the witness.
    const Report other = filled<REPORT_BYTES>(0xb0);
    EXPECT_EQ(count_violated(evaluate(honest_witness(ISSUER, other),
                                      make_instance(anchors().keys, ISSUER, other))),
              0u);
    EXPECT_GT(count_violated(evaluate(honest_witness(ISSUER, other), make_instance())), 0u);

    // A share for a "vector" that isn't one-hot, e.g., V = 0 or V = 2 e_i, is rejected too.
    for (const uint16_t delta : {uint16_t{0xffff}, uint16_t{1}}) {
        auto x = make_instance();
        x.share[ISSUER] = static_cast<uint16_t>(x.share[ISSUER] + delta);
        EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "delta = " << delta;
    }
}

// The shares add up to the one-hot vector of the issuer, mod 2^16.
TEST(RedeemRelation, SharesAddUpToOneHot) {
    for (const size_t i : {size_t{0}, ISSUER, MAX_ANCHORS - 1}) {
        const OpenedReport opened = open_report_output(expand_report(K));
        HistogramShare sum = public_report(K, i).share;
        aggregate(sum, opened.share);
        for (size_t u = 0; u < MAX_ANCHORS; ++u) {
            EXPECT_EQ(sum[u], u == i ? 1 : 0) << "i = " << i << ", u = " << u;
        }
    }
}

// The witness is consistent with the plaintext commitment and report expansion.
TEST(RedeemRelation, WitnessIsConsistent) {
    using namespace keccak::detail;
    const auto w = honest_witness();
    Kp800State state;
    std::copy_n(w.begin() + REDEEM_WIT_OFF_STATES + (NUM_COMMITTED_STATES - 1) * KP800_STATE_BYTES,
                KP800_STATE_BYTES, state.begin());
    keccak_p800_rounds(state, SEGMENT_START[NUM_COMMITTED_STATES], FINAL_ROUNDS);
    EXPECT_TRUE(
        std::equal(state.begin(), state.begin() + uov::M, commit(NF, CTX_ISS, CTX_RED, R).begin()));

    EXPECT_TRUE(std::equal(K.begin(), K.end(), w.begin() + REDEEM_WIT_OFF_K));
    const ReportOutput out = expand_report(K);
    for (size_t j = 0; j < REPORT_BLOCKS; ++j) {
        std::copy_n(w.begin() + REDEEM_WIT_OFF_REPORT_STATES + j * COMMITTED_STATES_BYTES +
                        (NUM_COMMITTED_STATES - 1) * KP800_STATE_BYTES,
                    KP800_STATE_BYTES, state.begin());
        keccak_p800_rounds(state, SEGMENT_START[NUM_COMMITTED_STATES], FINAL_ROUNDS);
        EXPECT_TRUE(std::equal(state.begin(), state.begin() + report_block_out_bytes(j),
                               out.begin() + j * REPORT_BLOCK_OUT_BYTES))
            << "block " << j;
    }
}
