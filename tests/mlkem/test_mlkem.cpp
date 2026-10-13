#include "vole_mole/mlkem.hpp"

#include "mlkem/mlkem.hpp"      // internal
#include "voleith_fq/field.hpp" // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <span>
#include <string>

using namespace vole_mole;
using namespace vole_mole::mlkem;
using vole_mole::test::filled;
using vole_mole::test::to_hex;
namespace mk = vole_mole::mlkem::detail;
namespace fq = vole_mole::voleith_fq::detail;

namespace {

// Known answers computed with OpenSSL 4.0, for the seed d || z = 00 01 02 ... 3f:
//
//   openssl genpkey -algorithm ML-KEM-768 -pkeyopt hexseed:000102...3f -out key.pem
//
// We record SHA3-256 of ek and of dk (the former is also embedded in dk).
const Seed SEED = filled<SEED_BYTES>(0x00);

struct Kat {
    std::string ek_digest;
    std::string dk_digest;
};

template <ParamSet P> Kat kat();
template <> Kat kat<MlKem512>() {
    return {"82f101ff648063b376e2bb6c5b7455f655a50c2feadade150efa0e0e6f365aea",
            "0bd3f5df01098ac9c29d687c7f1bd0588a5573feeef8f1e3b4573fa7f6ab57c8"};
}
template <> Kat kat<MlKem768>() {
    return {"a24e16d8f8f9383a95b77050f4d9fd2f5733eec1d63ef3c23ebf9918173669a7",
            "1149f17c3c4ac6ab1e3e2d9d8bd0171355ac0fa31bb8855c48ceade874c0864b"};
}
template <> Kat kat<MlKem1024>() {
    return {"61349e5c131a7e116a0463861d7d18663c5627c38c7147ddaadfd48acd7a4535",
            "f0db5d938027fcd9bad87847d52c14cf0c4abcf0703b749793f212111ffb303b"};
}

template <typename P> class MlKemTest : public ::testing::Test {};
using ParamSets = ::testing::Types<MlKem512, MlKem768, MlKem1024>;
TYPED_TEST_SUITE(MlKemTest, ParamSets);

} // namespace

static_assert(ENCAPS_KEY_BYTES<MlKem512> == 800 && DECAPS_KEY_BYTES<MlKem512> == 1632);
static_assert(ENCAPS_KEY_BYTES<MlKem768> == 1184 && DECAPS_KEY_BYTES<MlKem768> == 2400);
static_assert(ENCAPS_KEY_BYTES<MlKem1024> == 1568 && DECAPS_KEY_BYTES<MlKem1024> == 3168);

TYPED_TEST(MlKemTest, KeyGenKnownAnswer) {
    using P = TypeParam;
    const auto kp = keygen<P>(SEED);
    EXPECT_EQ(to_hex(mk::hash_h(kp.ek)), kat<P>().ek_digest);
    EXPECT_EQ(to_hex(mk::hash_h(kp.dk)), kat<P>().dk_digest);
}

TYPED_TEST(MlKemTest, KeyGenIsRandomized) {
    using P = TypeParam;
    EXPECT_NE(keygen<P>().ek, keygen<P>().ek);
}

TYPED_TEST(MlKemTest, ParseEncapsKey) {
    using P = TypeParam;
    auto ek = keygen<P>(SEED).ek;
    EXPECT_TRUE(mk::parse_encaps_key<P>(ek).has_value());

    // Modulus check: set the first coefficient to q.
    ek[0] = static_cast<uint8_t>(mk::Q);
    ek[1] = static_cast<uint8_t>((ek[1] & 0xf0) | (mk::Q >> 8));
    EXPECT_FALSE(mk::parse_encaps_key<P>(ek).has_value());
}

TEST(Ntt, InverseIsInverse) {
    mk::Poly f;
    for (size_t i = 0; i < f.size(); ++i) {
        f[i] = static_cast<mk::Fq>((i * 1337 + 42) % mk::Q);
    }
    mk::Poly g = f;
    mk::ntt(g);
    EXPECT_NE(f, g);
    mk::inv_ntt(g);
    EXPECT_EQ(f, g);
}

// The NTT turns multiplication in R_q = Z_q[X] / (X^256 + 1) into MultiplyNTTs.
TEST(Ntt, MultiplicationMatchesSchoolbook) {
    mk::Poly f, g;
    for (size_t i = 0; i < f.size(); ++i) {
        f[i] = static_cast<mk::Fq>((i * 7 + 3) % mk::Q);
        g[i] = static_cast<mk::Fq>((i * i + 11) % mk::Q);
    }
    mk::Poly want{};
    for (size_t i = 0; i < f.size(); ++i) {
        for (size_t j = 0; j < g.size(); ++j) {
            const mk::Fq prod = fq::fq_mul(f[i], g[j]);
            const size_t k = (i + j) % f.size();
            want[k] = i + j < f.size() ? fq::fq_add(want[k], prod) : fq::fq_sub(want[k], prod);
        }
    }
    mk::ntt(f);
    mk::ntt(g);
    mk::Poly got{};
    mk::multiply_ntts_acc(got, f, g);
    mk::inv_ntt(got);
    EXPECT_EQ(got, want);
}
