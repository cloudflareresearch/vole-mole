// faest-arch-opt's reduced product of poly2d with 128-bit coefficients, mul_reduce, which we add in
// subprojects/packagefiles/faest-arch-opt/0004-Faster-poly2d-product-for-128-bit-coefficients.patch.

#include "poly2d.hpp" // from faest-arch-opt

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <random>

namespace {

template <size_t n> faest::poly2d<n, 128> random_poly2d(std::mt19937_64& rng) {
    faest::poly2d<n, 128> out;
    for (size_t i = 0; i < n; ++i) {
        const std::array<uint64_t, 2> words = {rng(), rng()};
        out.coeffs[i] = faest::poly128::load(words.data());
    }
    return out;
}

// Schoolbook product of the coefficients, each a 128x128-bit carry-less product, then reduced.
template <size_t na, size_t nb>
faest::poly2d<na + nb - 1, 128> reference_mul(const faest::poly2d<na, 128>& a,
                                              const faest::poly2d<nb, 128>& b) {
    auto out = faest::poly2d<na + nb - 1, 256>::set_zero();
    for (size_t i = 0; i < na; ++i) {
        for (size_t j = 0; j < nb; ++j) {
            out.coeffs[i + j] = out.coeffs[i + j] + a.coeffs[i] * b.coeffs[j];
        }
    }
    return out.template reduce_to<128>();
}

template <size_t n> bool equal(const faest::poly2d<n, 128>& x, const faest::poly2d<n, 128>& y) {
    for (size_t i = 0; i < n; ++i) {
        std::array<uint8_t, 16> bx, by;
        x.coeffs[i].store(bx.data());
        y.coeffs[i].store(by.data());
        if (bx != by) {
            return false;
        }
    }
    return true;
}

template <size_t na, size_t nb> void check_mul() {
    std::mt19937_64 rng(1000 * na + nb);
    for (int iter = 0; iter < 100; ++iter) {
        const auto a = random_poly2d<na>(rng);
        const auto b = random_poly2d<nb>(rng);
        EXPECT_TRUE(equal(faest::mul_reduce<128>(a, b), reference_mul(a, b)))
            << na << "x" << nb << ", iteration " << iter;
    }
}

} // namespace

TEST(Poly2d, MulReduceMatchesSchoolbook) {
    check_mul<1, 1>();
    check_mul<1, 2>();
    check_mul<2, 1>();
    check_mul<2, 2>();
    check_mul<3, 3>();
    check_mul<3, 6>();
    check_mul<4, 4>();
    check_mul<4, 5>();
    check_mul<6, 6>();
    check_mul<6, 12>();
    check_mul<8, 8>();
}
