// Tests for GF(256) arithmetic and QuickSilver-committed elements of GF(256).

#include "gf256.hpp"    // internal
#include "qs_gf256.hpp" // internal

#include "test.hpp"

#include "constants.hpp"   // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <random>
#include <span>
#include <vector>

using namespace vole_mole::detail;
using vole_mole::test::to_hex;

namespace {

constexpr auto S = faest::secpar::s128;
using QS = faest::quicksilver_state<S, false, 4>;
using P = faest::poly_secpar<S>;

// Multiplication in GF(256), as a reference: shift-and-add, with reduction by x^8 + x^4 + x^3 + x
// + 1.
uint8_t reference_mul(uint8_t a, uint8_t b) {
    unsigned out = 0;
    for (size_t i = 0; i < 8; ++i) {
        if ((b >> i) & 1) {
            out ^= unsigned{a} << i;
        }
    }
    for (size_t i = 15; i >= 8; --i) {
        if ((out >> i) & 1) {
            out ^= 0x11bu << (i - 8);
        }
    }
    return static_cast<uint8_t>(out);
}

// A prover's QuickSilver state over `witness` with random VOLE tags.
struct RandomProver {
    std::vector<uint8_t> witness;
    std::vector<faest::block_secpar<S>> macs;
    std::array<uint8_t, faest::QS_CONSTANTS<S, 4>::CHALLENGE_BYTES> challenge{};
    QS qs;

    RandomProver(std::vector<uint8_t> w, std::mt19937& rng)
        : witness(std::move(w)), macs(8 * witness.size()), qs(init(rng)) {}

  private:
    QS init(std::mt19937& rng) {
        for (auto& mac : macs) {
            std::array<uint8_t, sizeof(mac)> bytes;
            for (uint8_t& b : bytes) {
                b = static_cast<uint8_t>(rng());
            }
            std::memcpy(&mac, bytes.data(), sizeof(mac));
        }
        return QS(witness.data(), macs.data(), 1, challenge.data());
    }
};

template <size_t deg>
bool equal(const faest::quicksilver_gfsecpar<QS, deg>& a,
           const faest::quicksilver_gfsecpar<QS, deg>& b) {
    for (size_t i = 0; i <= deg; ++i) {
        if (!(a.mac.coeffs[i] == b.mac.coeffs[i])) {
            return false;
        }
    }
    return true;
}

} // namespace

TEST(Gf256, MulMatchesReference) {
    for (unsigned a = 0; a < 256; ++a) {
        for (unsigned b = 0; b < 256; ++b) {
            const auto x = static_cast<uint8_t>(a);
            const auto y = static_cast<uint8_t>(b);
            ASSERT_EQ(gf256_mul(x, y), reference_mul(x, y)) << a << " * " << b;
        }
    }
}

TEST(Gf256, EmbeddingIsHomomorphism) {
    for (unsigned a = 0; a < 256; ++a) {
        for (unsigned b = 0; b < 256; ++b) {
            const auto x = static_cast<uint8_t>(a);
            const auto y = static_cast<uint8_t>(b);
            ASSERT_TRUE(gf256_embed<S>(x) + gf256_embed<S>(y) == gf256_embed<S>(x ^ y));
            ASSERT_TRUE((gf256_embed<S>(x) * gf256_embed<S>(y)).reduce_to<128>() ==
                        gf256_embed<S>(gf256_mul(x, y)))
                << a << " * " << b;
        }
    }
}

TEST(Gf256, MulByConst) {
    for (unsigned v = 0; v < 256; ++v) {
        const Gf256MulByConst mul(static_cast<uint8_t>(v));
        for (unsigned a = 0; a < 256; ++a) {
            ASSERT_EQ(mul(static_cast<uint8_t>(a)),
                      gf256_mul(static_cast<uint8_t>(a), static_cast<uint8_t>(v)));
        }
    }
}

namespace {

// gf256_madd computes acc[k] += a[k] v for vectors of length len.
template <size_t len> void check_madd(std::mt19937& rng) {
    for (unsigned v = 0; v < 256; ++v) {
        const Gf256MulByConst mul(static_cast<uint8_t>(v));
        std::array<uint8_t, len> a;
        std::array<uint8_t, gf256_padded(len)> acc;
        for (uint8_t& b : a) {
            b = static_cast<uint8_t>(rng());
        }
        for (uint8_t& b : acc) {
            b = static_cast<uint8_t>(rng());
        }
        auto want = acc;
        for (size_t k = 0; k < len; ++k) {
            want[k] ^= gf256_mul(a[k], static_cast<uint8_t>(v));
        }
        gf256_madd<len>(acc, a, mul);
        ASSERT_EQ(to_hex(acc), to_hex(want)) << "len = " << len << ", v = " << v;
    }
}

} // namespace

TEST(Gf256, Madd) {
    std::mt19937 rng(0); // fixed seed, so that failures are reproducible
    check_madd<16>(rng);
    check_madd<17>(rng);
    check_madd<32>(rng);
    check_madd<45>(rng);
}

// The prover's operations on qs_gf256 compute the same MAC polynomials as the corresponding
// operations on quicksilver_gfsecpar, for arbitrary VOLE tags.
TEST(QsGf256, ProverMatchesGfsecpar) {
    std::mt19937 rng(1); // fixed seed, so that failures are reproducible
    for (int n = 0; n < 50; ++n) {
        std::vector<uint8_t> w(4);
        for (uint8_t& b : w) {
            b = static_cast<uint8_t>(rng());
        }
        const RandomProver p(w, rng);
        const auto c = static_cast<uint8_t>(rng());

        const auto a = qs_load_gf256(&p.qs, 0);
        const auto b = qs_load_gf256(&p.qs, 8);
        const auto d = qs_load_gf256(&p.qs, 16);
        ASSERT_EQ(a.value, w[0]);
        const auto ga = p.qs.load_witness_8_bits_and_combine(0);
        const auto gb = p.qs.load_witness_8_bits_and_combine(8);
        const auto gd = p.qs.load_witness_8_bits_and_combine(16);
        ASSERT_TRUE(equal(qs_to_gfsecpar(a), ga));

        EXPECT_TRUE(equal(qs_to_gfsecpar(a + b), ga + gb));
        EXPECT_TRUE(equal(qs_to_gfsecpar(a + c), ga + gf256_embed<S>(c)));
        EXPECT_TRUE(equal(qs_to_gfsecpar(qs_mul_const(c, a)), gf256_embed<S>(c) * ga));
        const auto ab = qs_mul(a, b);
        EXPECT_EQ(ab.value, gf256_mul(w[0], w[1]));
        EXPECT_TRUE(equal(qs_to_gfsecpar(ab), ga * gb));
        EXPECT_TRUE(equal(qs_to_gfsecpar(qs_mul(ab, d)), ga * gb * gd));
        EXPECT_TRUE(equal(qs_to_gfsecpar(qs_mul(d, ab)), gd * (ga * gb)));
    }
}
