#include "mldsa/mldsa.hpp"              // internal
#include "mldsa_pok/sample_in_ball.hpp" // internal
#include "mldsa_pok/shake_relation.hpp" // internal
#include "qs_bit.hpp"                   // internal
#include "voleith.hpp"                  // internal

#include "constants.hpp"  // from faest-arch-opt
#include "hash.hpp"       // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <random>
#include <span>
#include <vector>

using namespace vole_mole::mldsa_pok::detail;
namespace mldsa = vole_mole::mldsa;

namespace {

using Sib = SampleInBall<39, 80>;

// Witness: the stream bytes, then the SampleInBall witness.
constexpr size_t STREAM_BITS = 8 * Sib::STREAM_BYTES;
constexpr size_t WITNESS_BYTES = (STREAM_BITS + Sib::WITNESS_BITS + 7) / 8;

constexpr faest::owf OWF_SIB =
    static_cast<faest::owf>((0x70u << 8) | 0b10'0000 /* owf_flag_witness_bits_check */);

} // namespace

template <> struct faest::OWF_CONSTANTS<faest::secpar::s128, OWF_SIB> {
    constexpr static size_t WITNESS_BITS = 8 * WITNESS_BYTES;
    constexpr static size_t QS_DEGREE = 16;
    constexpr static bool valid = true;
};

namespace {

inline constexpr std::array<uint8_t, 8> SIB_DST = {'m', 'd', 's', 'a', 0, 'x', 's', '0'};

struct SibRelation {
    using params = Params128f<OWF_SIB>;
    struct instance {};
    static constexpr size_t NUM_CONSTRAINTS = 8 * WITNESS_BYTES + Sib::NUM_CONSTRAINTS;
    static constexpr size_t WITNESS_PREFIX_BYTES = WITNESS_BYTES;
    static constexpr std::span<const uint8_t> DST = SIB_DST;
    static void hash_instance(faest::hash_state&, const instance&) {}

    template <typename QS>
    static void constraints(QS* qs, const instance&,
                            std::span<const uint8_t, params::CONSTS::QS::CHALLENGE_BYTES>) {
        for (size_t i = 0; i < 8 * WITNESS_BYTES; ++i) {
            vole_mole::detail::qs_add_bit_constraint(qs, qs->get_witness_bit(i));
        }
        std::vector<vole_mole::detail::qs_bit<QS, 1>> stream;
        for (size_t i = 0; i < STREAM_BITS; ++i) {
            stream.push_back(qs->get_witness_bit(i));
        }
        Sib::constraints(qs, std::span<const vole_mole::detail::qs_bit<QS, 1>>(stream),
                         STREAM_BITS);
    }
};

std::array<uint8_t, Sib::STREAM_BYTES> stream_of(std::span<const uint8_t> c_tilde) {
    std::array<uint8_t, Sib::STREAM_BYTES> out;
    const std::array<std::span<const uint8_t>, 1> parts = {c_tilde};
    mldsa::detail::shake256(parts, out);
    return out;
}

std::array<uint8_t, 32> random_c_tilde(uint32_t seed) {
    std::mt19937 rng(seed);
    std::array<uint8_t, 32> out;
    for (auto& b : out) {
        b = static_cast<uint8_t>(rng());
    }
    return out;
}

std::vector<uint8_t> witness_of(const std::array<uint8_t, Sib::STREAM_BYTES>& stream) {
    std::vector<uint8_t> w(WITNESS_BYTES);
    std::ranges::copy(stream, w.begin());
    EXPECT_TRUE(Sib::encode_witness(stream, w, STREAM_BITS).has_value());
    return w;
}

std::vector<uint8_t> prove(const std::vector<uint8_t>& w) {
    using vole_mole::detail::PROOF_BYTES;
    std::vector<uint8_t> proof(PROOF_BYTES<SibRelation>);
    vole_mole::detail::voleith_prove<SibRelation>(
        std::span<uint8_t, PROOF_BYTES<SibRelation>>(proof),
        std::span<const uint8_t, WITNESS_BYTES>(w), {}, {});
    return proof;
}

bool verify(const std::vector<uint8_t>& proof) {
    using vole_mole::detail::PROOF_BYTES;
    return vole_mole::detail::voleith_verify<SibRelation>(
        std::span<const uint8_t, PROOF_BYTES<SibRelation>>(proof), {});
}

} // namespace

TEST(SampleInBall, MatchesPlaintext) {
    for (uint32_t seed = 0; seed < 2000; ++seed) {
        const auto ct = random_c_tilde(seed);
        const auto stream = stream_of(ct);
        std::vector<uint8_t> w(WITNESS_BYTES);
        const auto c = Sib::encode_witness(stream, w, STREAM_BITS);
        ASSERT_TRUE(c.has_value()) << seed;
        const auto want = mldsa::detail::sample_in_ball(ct, 39);
        for (size_t x = 0; x < 256; ++x) {
            const int expect = want[x] == 0 ? 0 : (want[x] == 1 ? 1 : -1);
            ASSERT_EQ((*c)[x], expect) << seed << " " << x;
        }
    }
}

TEST(SampleInBall, ScanFailureIsNegligible) {
    // Pr[TAU accepts need more than SCAN_BYTES bytes], exactly (in log2), by dynamic programming
    // over the number of accepts so far.
    std::vector<long double> dp(Sib::TAU + 1, 0);
    dp[0] = 1;
    for (size_t p = 0; p < Sib::SCAN_BYTES; ++p) {
        std::vector<long double> next(Sib::TAU + 1, 0);
        for (size_t t = 0; t <= Sib::TAU; ++t) {
            if (t == Sib::TAU) {
                next[t] += dp[t];
                continue;
            }
            const long double accept = static_cast<long double>(Sib::FIRST + t + 1) / 256;
            next[t + 1] += dp[t] * accept;
            next[t] += dp[t] * (1 - accept);
        }
        dp = next;
    }
    long double fail = 0;
    for (size_t t = 0; t < Sib::TAU; ++t) {
        fail += dp[t];
    }
    EXPECT_LT(std::log2(fail), -77);
}

TEST(SampleInBall, ProvesAndVerifies) {
    for (uint32_t seed : {1u, 2u, 3u}) {
        const auto w = witness_of(stream_of(random_c_tilde(seed)));
        EXPECT_TRUE(verify(prove(w))) << seed;
    }
    std::printf("SampleInBall: %zu witness bits, %zu constraints\n", Sib::WITNESS_BITS,
                Sib::NUM_CONSTRAINTS);
}

TEST(SampleInBall, ConstructedCollisions) {
    // Streams with many repeated and self-referencing j's: j = i, j = an earlier i, and repeats.
    std::mt19937 rng(7);
    for (size_t trial = 0; trial < 200; ++trial) {
        std::array<uint8_t, Sib::STREAM_BYTES> stream;
        for (auto& b : stream) {
            const uint32_t r = rng() % 4;
            b = static_cast<uint8_t>(r == 0 ? 217 + rng() % 39 : r == 1 ? rng() % 8 : rng());
        }
        std::vector<uint8_t> w(WITNESS_BYTES);
        std::ranges::copy(stream, w.begin());
        const auto c = Sib::encode_witness(stream, w, STREAM_BITS);
        if (!c) {
            continue;
        }
        // Simulate SampleInBall on this stream.
        std::array<int, 256> want{};
        size_t pos = Sib::SIGN_BYTES;
        for (size_t i = Sib::FIRST; i < 256; ++i) {
            size_t j;
            do {
                j = stream[pos++];
            } while (j > i);
            want[i] = want[j];
            const size_t n = i - Sib::FIRST;
            want[j] = ((stream[n / 8] >> (n % 8)) & 1) ? -1 : 1;
        }
        for (size_t x = 0; x < 256; ++x) {
            ASSERT_EQ((*c)[x], want[x]) << trial << " " << x;
        }
        if (trial < 3) {
            EXPECT_TRUE(verify(prove(w))) << trial;
        }
    }
}

TEST(SampleInBall, RejectsWrongWitness) {
    const auto w = witness_of(stream_of(random_c_tilde(5)));
    ASSERT_TRUE(verify(prove(w)));
    // Flipping any one witness bit (outside the stream) breaks some constraint. (The prover then
    // produces an invalid proof. In debug builds, the prover asserts that constraints hold, so only
    // run this in release builds.)
#ifdef NDEBUG
    std::mt19937 rng(11);
    for (size_t trial = 0; trial < 20; ++trial) {
        auto bad = w;
        const size_t i = STREAM_BITS + rng() % Sib::WITNESS_BITS;
        bad[i / 8] ^= static_cast<uint8_t>(1u << (i % 8));
        EXPECT_FALSE(verify(prove(bad))) << i;
    }
#endif
}
