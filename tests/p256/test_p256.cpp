#include "p256/curve.hpp"
#include "p256/field.hpp"
#include "sha256/sha256.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <random>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

namespace {

using namespace vole_mole::p256;

std::vector<uint8_t> from_hex(std::string_view hex) {
    std::vector<uint8_t> out;
    for (size_t i = 0; i + 1 < hex.size(); i += 2) {
        out.push_back(static_cast<uint8_t>(std::stoi(std::string(hex.substr(i, 2)), nullptr, 16)));
    }
    return out;
}

Bytes32 b32(std::string_view hex) {
    const auto v = from_hex(hex);
    Bytes32 out{};
    std::copy(v.begin(), v.end(), out.begin());
    return out;
}

std::vector<uint8_t> bytes(std::string_view s) { return {s.begin(), s.end()}; }

template <typename F> F random_elem(std::mt19937_64& rng) {
    Limbs x;
    do {
        for (auto& l : x) {
            l = rng();
        }
    } while (vole_mole::p256::detail::limbs_ge(x, F::M));
    return F::from_canonical(x);
}

template <typename F> void field_laws() {
    std::mt19937_64 rng(1);
    for (int i = 0; i < 200; ++i) {
        const F a = random_elem<F>(rng), b = random_elem<F>(rng), c = random_elem<F>(rng);
        EXPECT_EQ((a + b) * c, a * c + b * c);
        EXPECT_EQ(a - b + b, a);
        EXPECT_EQ(a * F::one(), a);
        EXPECT_EQ(-a + a, F::zero());
        if (!a.is_zero()) {
            EXPECT_EQ(a * a.inv(), F::one());
        }
        EXPECT_EQ(F::from_canonical(a.canonical()), a);
        EXPECT_EQ(*F::from_bytes(a.to_bytes()), a);
    }
    // M - 1 + 1 = 0, and M itself doesn't decode.
    Limbs m1 = F::M;
    m1[0] -= 1;
    EXPECT_EQ(F::from_canonical(m1) + F::one(), F::zero());
    EXPECT_FALSE(F::from_bytes(F::from_canonical(m1).to_bytes()) == std::nullopt);
    Bytes32 mb{};
    for (size_t i = 0; i < 32; ++i) {
        mb[i] = static_cast<uint8_t>(F::M[(31 - i) / 8] >> (8 * ((31 - i) % 8)));
    }
    EXPECT_EQ(F::from_bytes(mb), std::nullopt);
    EXPECT_EQ(F::reduce_32(mb), F::zero());
    // reduce_be agrees with reduce_32.
    EXPECT_EQ(F::reduce_be(mb), F::zero());
    std::vector<uint8_t> wide(40, 0xff);
    // 2^320 - 1 = (2^64 - 1) 2^256 + (2^256 - 1)
    const F two64 = F::from_u64(1ull << 32) * F::from_u64(1ull << 32);
    F r256 = F::one();
    for (int i = 0; i < 4; ++i) {
        r256 *= two64;
    }
    EXPECT_EQ(F::reduce_be(wide), (two64 - F::one()) * r256 + (r256 - F::one()));
}

// Sums of products with lazy reduction match the field's, including at the maximum (128 products
// of M - 1, doubled).
template <typename F> void lazy_reduction() {
    std::mt19937_64 rng(7);
    auto random = [&] { return F::from_canonical(Limbs{rng(), rng(), rng(), rng() >> 1}); };
    for (const size_t n : {1, 2, 5, 69, 128}) {
        typename F::Wide acc{};
        F expect = F::zero();
        for (size_t i = 0; i < n; ++i) {
            const F a = random(), b = random();
            F::mul_add_wide(acc, a, b);
            expect += a * b;
        }
        EXPECT_EQ(F::reduce_wide(acc), expect) << n;
        F::double_wide(acc);
        EXPECT_EQ(F::reduce_wide(acc), expect + expect) << n;
    }
    const F max = F::zero() - F::one();
    // Representations near M: from_mont of M - 1.
    Limbs m1 = F::M;
    m1[0] -= 1;
    const F rmax = F::from_mont(m1);
    for (const F x : {max, rmax}) {
        typename F::Wide acc{};
        for (size_t i = 0; i < 128; ++i) {
            F::mul_add_wide(acc, x, x);
        }
        F::double_wide(acc);
        EXPECT_EQ(F::reduce_wide(acc), x * x * F::from_u64(256));
    }
}

TEST(Field, FpLazyReduction) { lazy_reduction<Fp>(); }
TEST(Field, FnLazyReduction) { lazy_reduction<Fn>(); }

TEST(Field, FpLaws) { field_laws<Fp>(); }
TEST(Field, FnLaws) { field_laws<Fn>(); }

TEST(Sha256, Vectors) {
    EXPECT_EQ(vole_mole::sha256::hash(bytes("abc")),
              b32("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"));
    EXPECT_EQ(vole_mole::sha256::hash(bytes("")),
              b32("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"));
    EXPECT_EQ(
        vole_mole::sha256::hash(bytes("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")),
        b32("248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"));
}

TEST(Curve, GeneratorOrder) {
    EXPECT_TRUE(GENERATOR.on_curve());
    EXPECT_TRUE(scalar_mul(GENERATOR, Fn::M).is_inf());
    Limbs nm1 = Fn::M;
    nm1[0] -= 1;
    EXPECT_EQ(scalar_mul(GENERATOR, nm1).to_affine(), GENERATOR.neg());
    // 2G + G = 3G
    const auto g = Jacobian::from(GENERATOR);
    EXPECT_EQ(g.dbl().add(g).to_affine(), scalar_mul(GENERATOR, Limbs{3, 0, 0, 0}).to_affine());
    EXPECT_EQ(g.add(g).to_affine(), g.dbl().to_affine());
    EXPECT_TRUE(g.add(Jacobian::from(GENERATOR.neg())).is_inf());
}

TEST(Curve, HashToPoint) {
    const auto p = hash_to_point(bytes("test"));
    EXPECT_TRUE(p.on_curve());
    EXPECT_FALSE(p.y.bit(0));
    EXPECT_FALSE(p == hash_to_point(bytes("test2")));
}

// RFC 6979, A.2.5 (P-256, SHA-256).
// slope_chain agrees with incomplete affine additions and doublings, one inversion per step.
TEST(Curve, SlopeChain) {
    using namespace vole_mole::p256;
    const Fp three = Fp::from_u64(3);
    std::vector<ChainStep> steps;
    for (uint64_t i = 0; i < 40; ++i) {
        const bool dbl = i % 3 == 1;
        steps.push_back(
            {dbl, dbl ? Affine{} : scalar_mul(GENERATOR, Limbs{1000 + i, 7, 0, 0}).to_affine()});
    }
    const Affine start = scalar_mul(GENERATOR, Limbs{5, 0, 0, 0}).to_affine();
    const Chain c = slope_chain(start, steps);
    Fp ax = start.x, ay = start.y;
    for (size_t i = 0; i < steps.size(); ++i) {
        const Affine& t = steps[i].t;
        const Fp lambda = steps[i].dbl ? (ax.square() * three - three) * (ay + ay).inv()
                                       : (t.y - ay) * (t.x - ax).inv();
        const Fp nx = lambda.square() - ax - (steps[i].dbl ? ax : t.x);
        ay = lambda * (ax - nx) - ay;
        ax = nx;
        EXPECT_EQ(c.slopes[i], lambda) << i;
        EXPECT_EQ(c.points[i + 1], (Affine{ax, ay, false})) << i;
    }
    // A degenerate addition (T = A) throws.
    const std::vector<ChainStep> bad = {{false, start}};
    EXPECT_THROW(slope_chain(start, bad), std::runtime_error);
}

TEST(Ecdsa, Rfc6979) {
    const Fn d =
        Fn::reduce_32(b32("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721"));
    const Affine q = scalar_mul(GENERATOR, d.canonical()).to_affine();
    EXPECT_EQ(q.x.to_bytes(),
              b32("60fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6"));
    EXPECT_EQ(q.y.to_bytes(),
              b32("7903fe1008b8bc99a41ae9e95628bc64f2f1b20c2d7e9f5177a3c294d4462299"));
    EXPECT_EQ(decode_point(encode_point(q)), q);

    struct Vector {
        const char* msg;
        const char *k, *r, *s;
    };
    for (const auto& v :
         {Vector{"sample", "a6e3c57dd01abe90086538398355dd4c3b17aa873382b0f24d6129493d8aad60",
                 "efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716",
                 "f7cb1c942d657c41d436c7a1b6e29f65f3e900dbb9aff4064dc4ab2f843acda8"},
          Vector{"test", "d16b6ae827f17175e040871a1c7ec3500192c4c92677336ec2537acaee0008e0",
                 "f1abb023518351cd71d881567b1ea663ed3efcf6c5132b354f28d3b0b7d38367",
                 "019f4113742a2b14bd25926b49c649155f267e60d3814b4c0cc84250e46f0083"}}) {
        const auto sig = ecdsa_sign_with_nonce(d, Fn::reduce_32(b32(v.k)), bytes(v.msg));
        ASSERT_TRUE(sig);
        EXPECT_EQ(sig->r, b32(v.r));
        EXPECT_EQ(sig->s, b32(v.s));
        EXPECT_TRUE(ecdsa_verify(q, bytes(v.msg), *sig));
        EXPECT_FALSE(ecdsa_verify(q, bytes("other"), *sig));
        auto bad = *sig;
        bad.s[31] ^= 1;
        EXPECT_FALSE(ecdsa_verify(q, bytes(v.msg), bad));
    }
}

TEST(Curve, DecodeRejectsInvalid) {
    PublicKeyBytes b = encode_point(GENERATOR);
    b[64] ^= 1;
    EXPECT_EQ(decode_point(b), std::nullopt);
    b = encode_point(GENERATOR);
    b[0] = 0x02;
    EXPECT_EQ(decode_point(b), std::nullopt);
}

} // namespace
