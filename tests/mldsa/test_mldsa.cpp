#include "vole_mole/mldsa.hpp"

#include "mldsa/mldsa.hpp" // internal
#include "mlkem/mlkem.hpp" // internal, for SHA3-256

#include "test.hpp"

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <string>
#include <string_view>

using namespace vole_mole;
using namespace vole_mole::mldsa;
using vole_mole::test::to_hex;
namespace md = vole_mole::mldsa::detail;

namespace {

std::span<const uint8_t> bytes(std::string_view s) {
    return {reinterpret_cast<const uint8_t*>(s.data()), s.size()};
}

template <size_t N> std::string sha3(const std::array<uint8_t, N>& b) {
    return to_hex(mlkem::detail::hash_h(b));
}

// Known answers computed with OpenSSL 4.0, for the seed xi = 00 01 02 ... 1f, signing the
// message "message to sign" with context "ctx" deterministically:
//
//   openssl genpkey -algorithm ML-DSA-44 -pkeyopt hexseed:000102...1f -out key.pem
//   openssl pkeyutl -sign -inkey key.pem -in msg -rawin -pkeyopt deterministic:1 \
//       -pkeyopt context-string:ctx -out sig.bin
//
// We record SHA3-256 of pk, sk, and the signature.
struct Kat {
    std::string pk, sk, sig;
};
template <ParamSet P> Kat kat();
template <> Kat kat<MlDsa44>() {
    return {"373c7bf2cac5bd2a6c35933bab0fa1c951f22247e1333383fcb618822080373f",
            "da0665a6d807669d06aeb7010507aa6bd4640641055462e38e37344a274f36a6",
            "6d59ff2d136475a6af21fe6248d24360c6212d9496b8a82ca457372eed4b88b3"};
}
template <> Kat kat<MlDsa65>() {
    return {"1800725067e388d837d911fe4f66101cc1961b1bb755030dc574272cfb00013f",
            "4ecfbd119980b1090a7feda39c225539ffa3ef3ff673b239b60189bfd4541170",
            "0eeb099f4fe4a022bf76cd64844069c399563b288b3ba3860a354f48c052f400"};
}
template <> Kat kat<MlDsa87>() {
    return {"e6cf50a9c2fa5234f59949ff61f8161db4d629532127f4aefa8bb10811ecfb1e",
            "db6218a2eeae53e567d25222055251eab0ba85d1c69aeb8a62253d2096fd96a2",
            "e2f4b0a8a6631c4b1f1c39cd51e770583165d0c30dd3cd3369142b4b5e739175"};
}

Seed seed() {
    Seed s;
    for (size_t i = 0; i < s.size(); ++i) {
        s[i] = static_cast<uint8_t>(i);
    }
    return s;
}

template <typename P> class MlDsaTest : public ::testing::Test {};
using ParamSets = ::testing::Types<MlDsa44, MlDsa65, MlDsa87>;
TYPED_TEST_SUITE(MlDsaTest, ParamSets);

} // namespace

static_assert(PUBLIC_KEY_BYTES<MlDsa44> == 1312 && SECRET_KEY_BYTES<MlDsa44> == 2560 &&
              SIGNATURE_BYTES<MlDsa44> == 2420);
static_assert(PUBLIC_KEY_BYTES<MlDsa65> == 1952 && SECRET_KEY_BYTES<MlDsa65> == 4032 &&
              SIGNATURE_BYTES<MlDsa65> == 3309);
static_assert(PUBLIC_KEY_BYTES<MlDsa87> == 2592 && SECRET_KEY_BYTES<MlDsa87> == 4896 &&
              SIGNATURE_BYTES<MlDsa87> == 4627);

TYPED_TEST(MlDsaTest, KnownAnswer) {
    using P = TypeParam;
    const auto kp = keygen<P>(seed());
    EXPECT_EQ(sha3(kp.pk), kat<P>().pk);
    EXPECT_EQ(sha3(kp.sk), kat<P>().sk);
    const auto sig = sign<P>(kp.sk, bytes("message to sign"), bytes("ctx"), Rnd{});
    EXPECT_EQ(sha3(sig), kat<P>().sig);
    EXPECT_TRUE(verify<P>(kp.pk, bytes("message to sign"), bytes("ctx"), sig));
}

TYPED_TEST(MlDsaTest, SignVerify) {
    using P = TypeParam;
    for (int i = 0; i < 5; ++i) {
        const auto kp = keygen<P>();
        const auto sig = sign<P>(kp.sk, bytes("hello"), {});
        EXPECT_TRUE(verify<P>(kp.pk, bytes("hello"), {}, sig));
        EXPECT_FALSE(verify<P>(kp.pk, bytes("hellp"), {}, sig));
        EXPECT_FALSE(verify<P>(kp.pk, bytes("hello"), bytes("x"), sig));
        auto bad = sig;
        bad[5] ^= 1; // c-tilde
        EXPECT_FALSE(verify<P>(kp.pk, bytes("hello"), {}, bad));
        bad = sig;
        bad[100] ^= 1; // z
        EXPECT_FALSE(verify<P>(kp.pk, bytes("hello"), {}, bad));
        EXPECT_FALSE(verify<P>(keygen<P>().pk, bytes("hello"), {}, sig));
    }
}

TYPED_TEST(MlDsaTest, RejectsMalformedHints) {
    using P = TypeParam;
    const auto kp = keygen<P>(seed());
    const auto sig = sign<P>(kp.sk, bytes("m"), {}, Rnd{});
    ASSERT_TRUE(md::decode_signature<P>(sig).has_value());
    // The count for the last row exceeds omega.
    auto bad = sig;
    bad.back() = static_cast<uint8_t>(P::OMEGA + 1);
    EXPECT_FALSE(md::decode_signature<P>(bad).has_value());
    EXPECT_FALSE(verify<P>(kp.pk, bytes("m"), {}, bad));
}

TEST(MlDsa, Ntt) {
    md::Poly f{}, g{};
    for (size_t i = 0; i < md::N; ++i) {
        f[i] = static_cast<md::Fq>((i * 7919 + 13) % md::Q);
        g[i] = static_cast<md::Fq>((i * i * 31 + 5) % md::Q);
    }
    // Schoolbook multiplication in Z_q[X] / (X^256 + 1).
    md::Poly want{};
    for (size_t i = 0; i < md::N; ++i) {
        for (size_t j = 0; j < md::N; ++j) {
            const md::Fq p = md::fq_mul(f[i], g[j]);
            const size_t k = (i + j) % md::N;
            want[k] = i + j < md::N ? md::fq_add(want[k], p) : md::fq_sub(want[k], p);
        }
    }
    md::Poly fh = f, gh = g, h{};
    md::ntt(fh);
    md::ntt(gh);
    md::multiply_ntts_acc(h, fh, gh);
    md::inv_ntt(h);
    EXPECT_EQ(h, want);
    md::inv_ntt(fh);
    EXPECT_EQ(fh, f);
}

TEST(MlDsa, DecomposeAndUseHint) {
    constexpr uint32_t g2 = MlDsa44::GAMMA2;
    for (md::Fq r = 0; r < md::Q; r += 97) {
        const auto [r1, r0] = md::decompose(r, g2);
        EXPECT_LT(r1, 44u);
        EXPECT_LE(r0, static_cast<int32_t>(g2));
        EXPECT_GE(r0, -static_cast<int32_t>(g2));
        EXPECT_EQ(md::fq_from_int(int64_t{r1} * 2 * g2 + r0), r);
    }
    // The corner case: r1 would be (q - 1) / (2 gamma2).
    EXPECT_EQ(md::decompose(md::Q - 1, g2).r1, 0u);
    EXPECT_EQ(md::decompose(md::Q - 1, g2).r0, -1);
}
