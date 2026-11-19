// Tests for the spend proof relation.

#include "vole_mole/act.hpp"
#include "vole_mole/keccak.hpp"
#include "vole_mole/uov.hpp"

#include "act/commit.hpp"       // internal
#include "act/spend.hpp"        // internal
#include "keccak/segmented.hpp" // internal
#include "qs_bit.hpp"           // internal

#include "test.hpp"

#include "polynomials.hpp" // from faest-arch-opt

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <random>
#include <utility>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::act;
using namespace vole_mole::act::detail;
using vole_mole::test::filled;
using vole_mole::test::PlainQS;
using vole_mole::test::uov_key_pair;

namespace {

constexpr Credits MAX_CREDITS = std::numeric_limits<Credits>::max();

const Context CTX_ISS = filled<CTX_BYTES>(0x10);
const Nullifier NF = filled<NF_BYTES>(0x30);
const Opening R = filled<R_BYTES>(0x40);
const Nullifier NF_NEXT = filled<NF_BYTES>(0x50);
const Opening R_NEXT = filled<R_BYTES>(0x60);

constexpr Credits T = 100;
constexpr Credits X = 5;
constexpr Credits D = 30;

using Witness = std::array<uint8_t, SPEND_WITNESS_BYTES>;

// The current state (nf, t, r, x, s) signed by the fixed test key pair, and the updated state
// (nf', t', r').
SpendState make_state(Credits t, Credits x, Credits t_next) {
    const uov::Preimage s = uov_key_pair().sk.derive_preimage(tag(commit(NF, CTX_ISS, t, R), x));
    return {NF, t, R, x, s, NF_NEXT, t_next, R_NEXT};
}

const SpendState& honest_state() {
    static const SpendState st = make_state(T, X, T + X - D);
    return st;
}

SpendRelation::instance make_instance(const SpendState& st, Credits d) {
    return {uov_key_pair().pk, st.nf, d, commit(st.nf_next, CTX_ISS, st.t_next, st.r_next),
            CTX_ISS};
}

std::vector<bool> evaluate(const Witness& w, const SpendRelation::instance& x) {
    // An arbitrary QuickSilver challenge, from which any random linear combination is derived.
    static const auto chal2 = filled<SpendParams::CONSTS::QS::CHALLENGE_BYTES>(0x50);
    PlainQS qs{w.data(), {}};
    SpendRelation::constraints(&qs, x, chal2);
    return qs.violated;
}

size_t count_violated(const std::vector<bool>& v) {
    return static_cast<size_t>(std::ranges::count(v, true));
}

// Indices of the constraints.
constexpr size_t CARRY_OFF = SPEND_WITNESS_BITS;
constexpr size_t SUM_OFF = CARRY_OFF + 2 * CREDIT_BITS;
constexpr size_t KECCAK_OFF = SUM_OFF + CREDIT_BITS + 1;

// Whether every violated constraint is in [begin, end).
bool only_violated_in(const std::vector<bool>& v, size_t begin, size_t end) {
    for (size_t i = 0; i < v.size(); ++i) {
        if (v[i] && (i < begin || i >= end)) {
            return false;
        }
    }
    return true;
}

} // namespace

TEST(SpendRelation, Carries) {
    EXPECT_EQ(carries(0, 0), 0u);
    EXPECT_EQ(carries(1, 1), 0b1u);        // k_1 = 1
    EXPECT_EQ(carries(0b11, 0b01), 0b11u); // k_1 = k_2 = 1
    EXPECT_EQ(carries(MAX_CREDITS, 1), MAX_CREDITS);
    EXPECT_EQ(carries(uint64_t{1} << 63, uint64_t{1} << 63), uint64_t{1} << 63);
}

// Tests for the ripple-carry adder, qs_add_credits, on its own. The witness holds a, b, and the
// carries of a + b, each as a little-endian credit value.
namespace {

constexpr size_t ADDER_OFF_A = 0;
constexpr size_t ADDER_OFF_B = CREDIT_BYTES;
constexpr size_t ADDER_OFF_K = 2 * CREDIT_BYTES;
using AdderWitness = std::array<uint8_t, 3 * CREDIT_BYTES>;

AdderWitness adder_witness(uint64_t a, uint64_t b, uint64_t k) {
    AdderWitness w{};
    for (size_t i = 0; i < CREDIT_BYTES; ++i) {
        w[ADDER_OFF_A + i] = uint8_t(a >> (8 * i));
        w[ADDER_OFF_B + i] = uint8_t(b >> (8 * i));
        w[ADDER_OFF_K + i] = uint8_t(k >> (8 * i));
    }
    return w;
}

struct AdderResult {
    uint64_t low; // bits 0, ..., 63 of the sum
    bool high;    // bit 64 of the sum
    std::vector<bool> violated;
};

// Run the adder on the witness. If `b_public` is set, then b is a public input, as d is in the
// spend relation; otherwise b is read from the witness.
AdderResult run_adder(const AdderWitness& w, uint64_t b, bool b_public) {
    PlainQS qs{w.data(), {}};
    using bit_1 = qs_bit<PlainQS, 1>;
    const auto witness_credit = [&qs](size_t off) {
        return [&qs, off](size_t i) { return bit_1(qs.get_witness_bit(credit_bit(off, i))); };
    };
    const auto public_credit = [&qs, b](size_t i) {
        return bit_1(faest::poly1((b >> i) & 1), &qs);
    };
    const auto sum =
        b_public ? qs_add_credits(&qs, witness_credit(ADDER_OFF_A), public_credit, ADDER_OFF_K)
                 : qs_add_credits(&qs, witness_credit(ADDER_OFF_A), witness_credit(ADDER_OFF_B),
                                  ADDER_OFF_K);
    AdderResult r{0, sum[CREDIT_BITS].v, qs.violated};
    for (size_t i = 0; i < CREDIT_BITS; ++i) {
        r.low |= uint64_t(sum[i].v) << i;
    }
    return r;
}

// Edge cases (including long carry chains) followed by random pairs.
std::vector<std::pair<uint64_t, uint64_t>> adder_test_cases() {
    const uint64_t edges[] = {0,
                              1,
                              2,
                              0x5555555555555555,
                              0xaaaaaaaaaaaaaaaa,
                              0x00000000ffffffff,
                              0xffffffff00000000,
                              uint64_t{1} << 63,
                              MAX_CREDITS - 1,
                              MAX_CREDITS};
    std::vector<std::pair<uint64_t, uint64_t>> cases;
    for (const uint64_t a : edges) {
        for (const uint64_t b : edges) {
            cases.emplace_back(a, b);
        }
    }
    std::mt19937_64 rng(0x7a7a70011e);
    for (size_t n = 0; n < 500; ++n) {
        const uint64_t a = rng(), b = rng();
        cases.emplace_back(a, b);
    }
    return cases;
}

} // namespace

TEST(SpendRelation, AdderComputesSum) {
    for (const auto& [a, b] : adder_test_cases()) {
        const auto w = adder_witness(a, b, carries(a, b));
        const unsigned __int128 expected = (unsigned __int128)a + b;
        for (const bool b_public : {false, true}) {
            const auto r = run_adder(w, b, b_public);
            EXPECT_EQ(r.violated.size(), CREDIT_BITS);
            EXPECT_EQ(count_violated(r.violated), 0u)
                << "a = " << a << ", b = " << b << ", public = " << b_public;
            EXPECT_EQ(r.low, uint64_t(expected))
                << "a = " << a << ", b = " << b << ", public = " << b_public;
            EXPECT_EQ(r.high, bool(expected >> 64))
                << "a = " << a << ", b = " << b << ", public = " << b_public;
        }
    }
}

TEST(SpendRelation, AdderRejectsWrongCarries) {
    for (const auto& [a, b] : adder_test_cases()) {
        const uint64_t k = carries(a, b);
        for (size_t i = 0; i < CREDIT_BITS; ++i) {
            const auto w = adder_witness(a, b, k ^ (uint64_t{1} << i));
            for (const bool b_public : {false, true}) {
                EXPECT_GT(count_violated(run_adder(w, b, b_public).violated), 0u)
                    << "a = " << a << ", b = " << b << ", flipped k_" << i + 1
                    << ", public = " << b_public;
            }
        }
    }
}

TEST(SpendRelation, HonestWitnessSatisfiesAllConstraints) {
    const auto& st = honest_state();
    const auto violated = evaluate(encode_spend_witness(st, D, CTX_ISS), make_instance(st, D));
    EXPECT_EQ(violated.size(), SpendRelation::NUM_CONSTRAINTS);
    EXPECT_EQ(count_violated(violated), 0u);
}

// Edge cases for the credit values: spending nothing, spending everything, and sums that overflow
// 64 bits.
TEST(SpendRelation, HonestWitnessForEdgeCases) {
    struct Case {
        Credits t, x, d;
    };
    for (const auto& [t, x, d] : {
             Case{T, X, 0},
             Case{T, X, T + X},
             Case{T, 0, T},
             Case{0, X, 1},
             Case{MAX_CREDITS, 0, 0},
             Case{MAX_CREDITS, 0, MAX_CREDITS},
             Case{0, MAX_CREDITS, 1},
             Case{MAX_CREDITS, 10, 20},                   // t + x overflows
             Case{MAX_CREDITS, MAX_CREDITS, MAX_CREDITS}, // t' = MAX_CREDITS
         }) {
        const Credits t_next =
            t + x - d; // mod 2^64; the true value is a credit value in every case
        const SpendState st = make_state(t, x, t_next);
        EXPECT_EQ(
            count_violated(evaluate(encode_spend_witness(st, d, CTX_ISS), make_instance(st, d))),
            0u)
            << "t = " << t << ", x = " << x << ", d = " << d;
    }
}

// Every bit of the witness matters.
TEST(SpendRelation, AnyWitnessBitFlipViolatesAConstraint) {
    const auto& st = honest_state();
    const auto honest = encode_spend_witness(st, D, CTX_ISS);
    const auto x = make_instance(st, D);
    for (size_t i = 0; i < SPEND_WITNESS_BITS; ++i) {
        auto w = honest;
        w[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_GT(count_violated(evaluate(w, x)), 0u)
            << "flipping witness bit " << i << " is not detected";
    }
}

// A witness that is consistent except that the change isn't t + x - d only violates the
// conservation constraints.
TEST(SpendRelation, RejectsUnconservedCredits) {
    for (const Credits t_next : {T + X - D + 1, T + X - D - 1, T + X, Credits{0}, MAX_CREDITS}) {
        const SpendState st = make_state(T, X, t_next);
        const auto violated = evaluate(encode_spend_witness(st, D, CTX_ISS), make_instance(st, D));
        EXPECT_GT(count_violated(violated), 0u) << "t' = " << t_next;
        EXPECT_TRUE(only_violated_in(violated, SUM_OFF, KECCAK_OFF)) << "t' = " << t_next;
    }
}

// If t + x - d isn't a credit value, then no t' satisfies the relation. In particular, the change
// can't wrap around.
TEST(SpendRelation, RejectsOutOfRangeChange) {
    // t + x - d < 0
    for (const Credits t_next : {T + X - (T + X + 1), Credits{0}}) {
        const SpendState st = make_state(T, X, t_next);
        const Credits d = T + X + 1;
        const auto violated = evaluate(encode_spend_witness(st, d, CTX_ISS), make_instance(st, d));
        EXPECT_GT(count_violated(violated), 0u) << "t' = " << t_next;
    }

    // t + x - d >= 2^64
    const Credits t = MAX_CREDITS, x = 10, d = 5;
    for (const Credits t_next : {t + x - d, MAX_CREDITS}) {
        const SpendState st = make_state(t, x, t_next);
        const auto violated = evaluate(encode_spend_witness(st, d, CTX_ISS), make_instance(st, d));
        EXPECT_GT(count_violated(violated), 0u) << "t' = " << t_next;
        EXPECT_TRUE(only_violated_in(violated, SUM_OFF, KECCAK_OFF)) << "t' = " << t_next;
    }
}

// The refund is bound by the signature: claiming a larger refund is rejected, even if the rest of
// the witness is consistent.
TEST(SpendRelation, RejectsWrongRefund) {
    SpendState st = honest_state();
    st.x += 1;
    st.t_next += 1;
    const auto violated = evaluate(encode_spend_witness(st, D, CTX_ISS), make_instance(st, D));
    EXPECT_GT(count_violated(violated), 0u);
    // Only the Tag constraints (V1) are violated.
    EXPECT_TRUE(only_violated_in(violated, KECCAK_OFF, SpendRelation::NUM_CONSTRAINTS));
}

TEST(SpendRelation, RejectsWrongCredit) {
    SpendState st = honest_state();
    st.t += 1;
    st.t_next += 1;
    EXPECT_GT(count_violated(evaluate(encode_spend_witness(st, D, CTX_ISS), make_instance(st, D))),
              0u);
}

TEST(SpendRelation, WrongInstanceViolatesAConstraint) {
    const auto& st = honest_state();
    const auto w = encode_spend_witness(st, D, CTX_ISS);

    auto x = make_instance(st, D);
    x.nf[0] ^= 1;
    EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "nf";

    for (const Credits d : {D + 1, D - 1, D ^ (uint64_t{1} << 63)}) {
        x = make_instance(st, D);
        x.d = d;
        EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "d = " << d;
    }

    x = make_instance(st, D);
    x.ctx_iss[CTX_BYTES - 1] ^= 0x80;
    EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "ctx_iss";

    // Each bit of c' is constrained.
    for (size_t i = 0; i < 8 * COMMITMENT_BYTES; ++i) {
        x = make_instance(st, D);
        x.c_next[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_EQ(count_violated(evaluate(w, x)), 1u) << "flipping bit " << i << " of c'";
    }

    // Another Issuer.
    const vole_mole::test::UovKeyPair other(uov::SecretKey{filled<uov::SECRET_KEY_BYTES>(0x61)});
    x = make_instance(st, D);
    x.pk = other.pk;
    EXPECT_GT(count_violated(evaluate(w, x)), 0u) << "pk";
}

// The witness is consistent with the plaintext commitment and tag.
TEST(SpendRelation, WitnessIsConsistent) {
    using namespace keccak::detail;
    const auto& st = honest_state();
    const auto w = encode_spend_witness(st, D, CTX_ISS);

    const Commitment c = commit(st.nf, CTX_ISS, st.t, st.r);
    EXPECT_TRUE(std::equal(c.begin(), c.end(), w.begin() + SPEND_WIT_OFF_C));

    const auto last_segment = [&w](size_t wit_off_states) {
        Kp800State state;
        std::copy_n(w.begin() + wit_off_states + (NUM_COMMITTED_STATES - 1) * KP800_STATE_BYTES,
                    KP800_STATE_BYTES, state.begin());
        keccak_p800_rounds(state, SEGMENT_START[NUM_COMMITTED_STATES], FINAL_ROUNDS);
        return state;
    };
    const auto com = last_segment(SPEND_WIT_OFF_COM_STATES);
    EXPECT_TRUE(std::equal(c.begin(), c.end(), com.begin()));
    const auto y = tag(c, st.x);
    const auto tg = last_segment(SPEND_WIT_OFF_TAG_STATES);
    EXPECT_TRUE(std::equal(y.begin(), y.end(), tg.begin()));
    EXPECT_EQ(uov_key_pair().pk.eval(st.s), y);
    const Commitment c_next = commit(st.nf_next, CTX_ISS, st.t_next, st.r_next);
    const auto com_next = last_segment(SPEND_WIT_OFF_COM_NEXT_STATES);
    EXPECT_TRUE(std::equal(c_next.begin(), c_next.end(), com_next.begin()));
}

// The adder is sound for every carry vector, not just for single flips: exhaustively over a, b with
// four low (or four high) bits and every value of the five carries around them, the carry
// constraints hold iff the carries are the true ones, and then the 65-bit sum is a + b.
TEST(SpendRelation, AdderExhaustiveSmall) {
    for (const size_t shift : {size_t{0}, size_t{60}}) {
        for (uint64_t a4 = 0; a4 < 16; ++a4) {
            for (uint64_t b4 = 0; b4 < 16; ++b4) {
                const uint64_t a = a4 << shift, b = b4 << shift;
                for (uint64_t k5 = 0; k5 < 32; ++k5) {
                    // Every value of k_1, ..., k_5 (shift 0) or k_60, ..., k_64 (shift 60); the
                    // other carries are 0, which is their true value.
                    const uint64_t k = shift == 0 ? k5 : k5 << (shift - 1);
                    const unsigned __int128 expected = (unsigned __int128)a + b;
                    for (const bool b_public : {false, true}) {
                        const auto r = run_adder(adder_witness(a, b, k), b, b_public);
                        const bool ok = count_violated(r.violated) == 0;
                        EXPECT_EQ(ok, k == carries(a, b))
                            << "a = " << a << ", b = " << b << ", k = " << k;
                        if (ok) {
                            EXPECT_EQ(r.low, uint64_t(expected));
                            EXPECT_EQ(r.high, bool(expected >> 64));
                        }
                    }
                }
            }
        }
    }
}

// The carry and conservation constraints (V3) hold iff t + x = t' + d over the integers:
// exhaustively for small t', d, and at the top of the range.
TEST(SpendRelation, ConservationExhaustiveSmall) {
    struct Case {
        Credits t, x;
        std::vector<Credits> values; // for t' and d
    };
    const std::vector<Case> cases = {
        {5, 3, {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, MAX_CREDITS - 1, MAX_CREDITS}},
        {MAX_CREDITS, 2, {0, 1, 2, 3, MAX_CREDITS - 2, MAX_CREDITS - 1, MAX_CREDITS}},
    };
    for (const Case& c : cases) {
        SpendState st = make_state(c.t, c.x, 0);
        for (const Credits t_next : c.values) {
            for (const Credits d : c.values) {
                st.t_next = t_next;
                const auto violated =
                    evaluate(encode_spend_witness(st, d, CTX_ISS), make_instance(st, d));
                const bool v3_ok =
                    std::none_of(violated.begin() + CARRY_OFF, violated.begin() + KECCAK_OFF,
                                 [](bool b) { return b; });
                const bool conserved =
                    (unsigned __int128)c.t + c.x == (unsigned __int128)t_next + d;
                EXPECT_EQ(v3_ok, conserved)
                    << "t = " << c.t << ", x = " << c.x << ", t' = " << t_next << ", d = " << d;
                EXPECT_EQ(count_violated(violated) == 0, conserved);
            }
        }
    }
}

// For any witness, the inputs of the three Keccak evaluations are those of the relation: Com(nf,
// ctx_iss, t, r) and Tag(c, x) for the current state, and Com(nf', ctx_iss, t', r') for the updated
// state, with nf and ctx_iss public and everything else read from the witness. Each input byte is
// either a public constant or a copy of one witness byte, so two witnesses suffice: in the first,
// the witness bytes are pairwise distinct (mod 256, which suffices for the first 112 bytes that
// enter the inputs), and the second is its complement.
TEST(SpendRelation, KeccakInputsAreRelationInputs) {
    static_assert(SPEND_WIT_OFF_S <= 256);
    Witness w;
    for (size_t i = 0; i < w.size(); ++i) {
        w[i] = static_cast<uint8_t>(i + 1);
    }
    const auto input = [](const Witness& wit, const Kp800State& pub,
                          const keccak::detail::InputMap& map) {
        PlainQS qs{wit.data(), {}};
        const auto bits = keccak::detail::qs_input(&qs, pub, map);
        Kp800State s{};
        for (size_t i = 0; i < bits.size(); ++i) {
            s[i / 8] |= static_cast<uint8_t>(bits[i].v << (i % 8));
        }
        return s;
    };
    for (int pass = 0; pass < 2; ++pass) {
        const auto field = [&w]<size_t N>(size_t off, std::array<uint8_t, N>& out) {
            std::copy_n(w.begin() + static_cast<std::ptrdiff_t>(off), N, out.begin());
        };
        Opening r, r_next;
        Nullifier nf_next;
        Commitment c;
        CreditBytes t, x, t_next;
        field(SPEND_WIT_OFF_R, r);
        field(SPEND_WIT_OFF_T, t);
        field(SPEND_WIT_OFF_X, x);
        field(SPEND_WIT_OFF_C, c);
        field(SPEND_WIT_OFF_NF_NEXT, nf_next);
        field(SPEND_WIT_OFF_T_NEXT, t_next);
        field(SPEND_WIT_OFF_R_NEXT, r_next);

        // As in SpendRelation::constraints.
        EXPECT_EQ(input(w, encode_com_state(NF, CTX_ISS, 0, {}), SPEND_COM_TO_WIT),
                  encode_com_state(NF, CTX_ISS, decode_credits(t), r))
            << "Com, pass " << pass;
        EXPECT_EQ(input(w, encode_tag_state({}, 0), SPEND_TAG_TO_WIT),
                  encode_tag_state(c, decode_credits(x)))
            << "Tag, pass " << pass;
        EXPECT_EQ(input(w, encode_com_state({}, CTX_ISS, 0, {}), SPEND_COM_NEXT_TO_WIT),
                  encode_com_state(nf_next, CTX_ISS, decode_credits(t_next), r_next))
            << "Com', pass " << pass;

        for (uint8_t& b : w) {
            b = static_cast<uint8_t>(~b);
        }
    }
}
