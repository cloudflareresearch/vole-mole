// Tests for the redemption proof relation.

#include "vole_mole/keccak.hpp"
#include "vole_mole/moussaka.hpp"
#include "vole_mole/uov.hpp"

#include "keccak/segmented.hpp" // internal
#include "moussaka/commit.hpp"  // internal
#include "moussaka/redeem.hpp"  // internal

#include "test.hpp"

#include "polynomials.hpp" // from faest-arch-opt

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <random>
#include <utility>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::moussaka;
using namespace vole_mole::moussaka::detail;
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

RedeemRelation::instance make_instance(AnchorSpan keys = anchors().keys) {
    return {keys, NF, CTX_ISS, CTX_RED, CHALLENGE_DIGEST};
}

Witness honest_witness(size_t i = ISSUER) {
    return encode_redeem_witness(NF, CTX_ISS, CTX_RED, R, signature(), i);
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
            const auto violated = evaluate(honest_witness(i), make_instance(keys));
            EXPECT_EQ(violated.size(), RedeemRelation::NUM_CONSTRAINTS);
            EXPECT_EQ(count_violated(violated), 0u) << "n = " << n << ", i = " << i;
        }
    }
}

TEST(RedeemRelation, HonestWitnessForLargestAnchorSet) {
    std::vector<AnchorRef> keys(MAX_ANCHORS, anchors().keys[0]);
    keys.back() = uov_key_pair().pk;
    EXPECT_EQ(count_violated(evaluate(honest_witness(MAX_ANCHORS - 1), make_instance(keys))), 0u);
}

// Every bit of the witness matters: r and the intermediate states determine the commitment, s
// determines the signature, and b determines the selected Anchor.
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

    // Only the first parity constraint is violated.
    EXPECT_EQ(count_violated(violated), 1u);
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

// The witness is consistent with the plaintext commitment.
TEST(RedeemRelation, WitnessIsConsistent) {
    using namespace keccak::detail;
    const auto w = honest_witness();
    Kp800State state;
    std::copy_n(w.begin() + REDEEM_WIT_OFF_STATES + (NUM_COMMITTED_STATES - 1) * KP800_STATE_BYTES,
                KP800_STATE_BYTES, state.begin());
    keccak_p800_rounds(state, SEGMENT_START[NUM_COMMITTED_STATES], FINAL_ROUNDS);
    EXPECT_TRUE(
        std::equal(state.begin(), state.begin() + uov::M, commit(NF, CTX_ISS, CTX_RED, R).begin()));
}

// The selector constraints (each b[u] is a bit, or zero if u >= N; the parity constraints; and the
// weight constraint) hold if and only if b is one-hot with its set bit in [N]. Check every selector
// of weight at most 2, every selector supported on the first 8 indices, and random selectors.
TEST(RedeemRelation, SelectorConstraintsHoldIffOneHot) {
    const std::vector<AnchorRef> keys(5, anchors().keys[0]);
    const auto x = make_instance(keys);
    const auto selector_ok = [&](uint64_t b) {
        auto w = honest_witness();
        for (size_t u = 0; u < MAX_ANCHORS; ++u) {
            set_selector(w, u, (b >> u) & 1);
        }
        const auto violated = evaluate(w, x);
        return std::none_of(violated.begin() + SELECTOR_OFF, violated.begin() + WEIGHT_OFF + 1,
                            [](bool v) { return v; });
    };
    const auto expected = [&](uint64_t b) {
        return std::popcount(b) == 1 && std::countr_zero(b) < static_cast<int>(keys.size());
    };
    static_assert(MAX_ANCHORS == 64);

    std::vector<uint64_t> selectors = {0, ~uint64_t{0}};
    for (size_t u = 0; u < MAX_ANCHORS; ++u) {
        for (size_t v = u; v < MAX_ANCHORS; ++v) {
            selectors.push_back((uint64_t{1} << u) | (uint64_t{1} << v));
        }
    }
    for (uint64_t b = 0; b < 256; ++b) {
        selectors.push_back(b);
    }
    std::mt19937_64 rng(0); // fixed seed, so that failures are reproducible
    for (int n = 0; n < 64; ++n) {
        selectors.push_back(rng());
        selectors.push_back(rng() & rng() & rng() & rng()); // sparse
    }
    for (const uint64_t b : selectors) {
        EXPECT_EQ(selector_ok(b), expected(b)) << "selector " << std::hex << b;
    }
}

// For any witness, the input of the Keccak evaluation is the commitment input for the public nf,
// ctx_iss, ctx_red, and the r read from the witness. (See KeccakInputIsCommitmentInput in
// test_issue.cpp for why two witnesses suffice.) Bytes of the witness other than r don't enter.
TEST(RedeemRelation, KeccakInputIsCommitmentInput) {
    Witness w;
    for (size_t i = 0; i < w.size(); ++i) {
        w[i] = static_cast<uint8_t>(i + 1);
    }
    for (int pass = 0; pass < 2; ++pass) {
        PlainQS qs{w.data(), {}};
        const auto bits = keccak::detail::qs_input(&qs, encode_com_state(NF, CTX_ISS, CTX_RED, {}),
                                                   REDEEM_COM_TO_WIT);
        Kp800State in{};
        for (size_t i = 0; i < bits.size(); ++i) {
            in[i / 8] |= static_cast<uint8_t>(bits[i].v << (i % 8));
        }
        Opening r;
        std::copy_n(w.begin() + REDEEM_WIT_OFF_R, R_BYTES, r.begin());
        EXPECT_EQ(in, encode_com_state(NF, CTX_ISS, CTX_RED, r)) << "pass " << pass;
        for (uint8_t& b : w) {
            b = static_cast<uint8_t>(~b);
        }
    }
}

// The M output bytes of the Keccak evaluation, embedded in GF(2^128) as the relation compares them
// with Q(s), are the embedded bytes of the commitment, for the honest intermediate states.
TEST(RedeemRelation, KeccakOutputBytesAreCommitment) {
    const auto w = honest_witness();
    PlainQS qs{w.data(), {}};
    const auto out = keccak::detail::qs_keccak(
        &qs,
        keccak::detail::qs_input(&qs, encode_com_state(NF, CTX_ISS, CTX_RED, {}),
                                 REDEEM_COM_TO_WIT),
        REDEEM_WIT_OFF_STATES);
    EXPECT_EQ(count_violated(qs.violated), 0u);
    const Commitment t = commit(NF, CTX_ISS, CTX_RED, R);
    for (size_t k = 0; k < uov::M; ++k) {
        EXPECT_TRUE(keccak::detail::qs_byte(out, k).v ==
                    faest::poly_secpar<faest::secpar::s128>::from_8_byte(t[k]))
            << "byte " << k;
    }
}
