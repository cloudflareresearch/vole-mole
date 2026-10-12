// Tests for the prototype of the ML-KEM proof of possession in binary VOLEitH (binary.hpp).

#include "vole_mole/mlkem.hpp"

#include "mlkem/mlkem.hpp"      // internal
#include "mlkem_pop/binary.hpp" // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <ratio>
#include <span>
#include <string_view>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::mlkem_pop::binary;
using vole_mole::test::filled;

namespace {

constexpr std::string_view CONTEXT_STR = "CSR challenge 1234";
const std::span<const uint8_t> CONTEXT(reinterpret_cast<const uint8_t*>(CONTEXT_STR.data()),
                                       CONTEXT_STR.size());
const Rho RHO = filled<32>(0x50);

template <mlkem::ParamSet P> const mlkem::KeyPair<P>& key_pair() {
    static const mlkem::KeyPair<P> kp = mlkem::keygen<P>(filled<mlkem::SEED_BYTES>(0x00));
    return kp;
}

template <mlkem::ParamSet P> const Statement<P>& statement() {
    static const Statement<P> s = *make_statement<P>(key_pair<P>().ek, CONTEXT);
    return s;
}

template <typename P> class MlKemPopBinaryTest : public ::testing::Test {};
using ParamSets = ::testing::Types<mlkem::MlKem512, mlkem::MlKem768, mlkem::MlKem1024>;
TYPED_TEST_SUITE(MlKemPopBinaryTest, ParamSets);

double ms_since(std::chrono::steady_clock::time_point t0) {
    return std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - t0).count();
}

} // namespace

TYPED_TEST(MlKemPopBinaryTest, Constants) {
    using P = TypeParam;
    using R = BinRelation<P, true>;
    std::printf("K=%zu: proof %zu bytes (key %zu bits, e %zu bytes); witness %zu bits (values %zu, "
                "checks %zu); without the PRG: %zu bytes\n",
                P::K, PROOF_BYTES<P, true>, 8 * vole_mole::detail::VOLE_WITNESS_BYTES<R>,
                vole_mole::detail::DERIVED_E_BYTES<R>, Layout<P>::WITNESS_BITS,
                Layout<P>::PREFIX_BITS, MQ<P>::ANSWER_BITS, PROOF_BYTES<P, false>);
}

// The checks hold on the honest witness, and fail if one coefficient changes.
TYPED_TEST(MlKemPopBinaryTest, ChecksHold) {
    using P = TypeParam;
    const auto& stmt = statement<P>();
    auto x = witness_of<P>(stmt, key_pair<P>().dk);
    for (const int32_t v : x) {
        ASSERT_LE(std::abs(v), static_cast<int32_t>(P::ETA1));
    }
    const auto weights = make_weights<P>(check_weights<P>(stmt, filled<32>(0x01)));
    auto holds = [&](const std::vector<int32_t>& xs) {
        const auto prefix = encode_prefix<P>(xs);
        return MQ<P>::holds(weights, [&](size_t j, size_t i) {
            return get_bit(prefix, Layout<P>::value_bit(j, i));
        });
    };
    EXPECT_TRUE(holds(x));
    for (const size_t j : {size_t{0}, P::K * mlkem::detail::N + 17}) {
        auto y = x;
        y[j] = y[j] == 0 ? 1 : 0;
        EXPECT_FALSE(holds(y));
    }
}

// The carry budget is far above the number of carries needed.
TYPED_TEST(MlKemPopBinaryTest, CarryBudget) {
    using P = TypeParam;
    const auto& stmt = statement<P>();
    std::vector<double> counts;
    for (uint8_t i = 0; i < 100; ++i) {
        counts.push_back(static_cast<double>(
            MQ<P>::count_carries(make_weights<P>(check_weights<P>(stmt, filled<32>(i))))));
    }
    double mean = 0;
    for (const double c : counts) {
        mean += c;
    }
    mean /= static_cast<double>(counts.size());
    double var = 0;
    for (const double c : counts) {
        var += (c - mean) * (c - mean);
    }
    const double sd = std::sqrt(var / static_cast<double>(counts.size() - 1));
    std::printf("K=%zu check carries: mean %.1f, sd %.1f, max %.0f, budget %zu (mean + %.1f sd)\n",
                P::K, mean, sd, *std::ranges::max_element(counts), MQ<P>::CARRY_BUDGET,
                (static_cast<double>(MQ<P>::CARRY_BUDGET) - mean) / sd);
    EXPECT_GT(static_cast<double>(MQ<P>::CARRY_BUDGET), mean + 8 * sd);
}

TYPED_TEST(MlKemPopBinaryTest, ProvesAndVerifies) {
    using P = TypeParam;
    const auto& [ek, dk] = key_pair<P>();
    (void)verify<P, true>(ek, CONTEXT, std::vector<uint8_t>(PROOF_BYTES<P, true>)); // warm up
    auto t0 = std::chrono::steady_clock::now();
    const auto proof = prove<P, true>(dk, CONTEXT, RHO);
    const double tp = ms_since(t0);
    t0 = std::chrono::steady_clock::now();
    EXPECT_TRUE((verify<P, true>(ek, CONTEXT, proof)));
    const double tv = ms_since(t0);
    std::printf("K=%zu: prove %.1f ms, verify %.1f ms\n", P::K, tp, tv);
}

TYPED_TEST(MlKemPopBinaryTest, ProvesAndVerifiesWithoutPrg) {
    using P = TypeParam;
    const auto& [ek, dk] = key_pair<P>();
    const auto proof = prove<P, false>(dk, CONTEXT, RHO);
    EXPECT_TRUE((verify<P, false>(ek, CONTEXT, proof)));
}

TYPED_TEST(MlKemPopBinaryTest, RejectsTampering) {
    using P = TypeParam;
    const auto& [ek, dk] = key_pair<P>();
    const auto proof = prove<P, true>(dk, CONTEXT, RHO);
    for (const size_t i : {size_t{0}, size_t{100}, proof.size() / 2, proof.size() - 1}) {
        auto bad = proof;
        bad[i] ^= 1;
        EXPECT_FALSE((verify<P, true>(ek, CONTEXT, bad))) << i;
    }
    EXPECT_FALSE((verify<P, true>(ek, {}, proof)));
    const auto other = mlkem::keygen<P>(filled<mlkem::SEED_BYTES>(0x01));
    EXPECT_FALSE((verify<P, true>(other.ek, CONTEXT, proof)));
    auto ek2 = ek;
    ek2[0] ^= 1; // one coefficient of t-hat
    EXPECT_FALSE((verify<P, true>(ek2, CONTEXT, proof)));
}

// Cheating provers produce invalid proofs. (Release builds only: in debug builds, the prover
// asserts that its constraints hold.)
TYPED_TEST(MlKemPopBinaryTest, RejectsCheatingProvers) {
#ifdef NDEBUG
    using P = TypeParam;
    const auto& stmt = statement<P>();
    const auto x = witness_of<P>(stmt, key_pair<P>().dk);
    const auto check = [&](const std::vector<int32_t>& y) {
        const auto proof = prove_prefix<P, true>(stmt, encode_prefix<P>(y), RHO);
        return verify<P, true>(*stmt.ek, CONTEXT, proof);
    };
    EXPECT_TRUE(check(x));
    // A short witness that doesn't satisfy the equation.
    auto y = x;
    y[5] = y[5] == 0 ? 1 : 0;
    EXPECT_FALSE(check(y));
    // A coefficient out of range (2 eta + 1 fits in the 3 bits).
    y = x;
    y[3] = static_cast<int32_t>(P::ETA1) + 1;
    EXPECT_FALSE(check(y));
    // e shifted by a multiple of q can't be encoded; neither can a large s. Instead, fix
    // s = 0 and e = t, which satisfies the equation with e far out of range.
    y.assign(x.size(), 0);
    for (size_t i = 0; i < P::K; ++i) {
        for (size_t n = 0; n < mlkem::detail::N; ++n) {
            y[P::K * mlkem::detail::N + i * mlkem::detail::N + n] = centered(stmt.t[i][n]);
        }
    }
    EXPECT_FALSE(check(y));
#else
    GTEST_SKIP() << "the prover asserts its constraints in debug builds";
#endif
}
