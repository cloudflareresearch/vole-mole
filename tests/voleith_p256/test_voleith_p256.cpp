#include "p256/field.hpp"
#include "voleith_p256/voleith.hpp"

#include "aes.hpp"        // from faest-arch-opt
#include "block.hpp"      // from faest-arch-opt
#include "parameters.hpp" // from faest-arch-opt

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

namespace {

using namespace vole_mole::voleith_p256;
using vole_mole::p256::Fn;
using vole_mole::p256::Fp;

// Witness: (a, b, c) in F_p and (x, y) in F_n with a b c = k_p, a + b = c (a constraint of degree
// 1), x^3 = y, and x y != 0 (via the inverse z = (x y)^-1, an extra F_n witness).
struct ToyRelation {
    static constexpr size_t LP = 3, LN = 3, DP = 4, DN = 3;
    struct instance {
        Fp kp;
    };
    template <typename Ctx> static void constraints(Ctx& ctx, const instance& x) {
        const auto a = ctx.wp(0), b = ctx.wp(1), c = ctx.wp(2);
        ctx.add_p(a * b * c - x.kp);
        ctx.add_p(a + b - c);
        ctx.add_p((a - c) * (b + Fp::one()) * a * b - (a - c) * (b + Fp::one()) * a * b);
        const auto xx = ctx.wn(0), y = ctx.wn(1), z = ctx.wn(2);
        ctx.add_n(xx * xx * xx - y);
        ctx.add_n(xx * y * z - Fn::one());
    }
};

template <typename P> using Proof = std::array<uint8_t, Layout<ToyRelation, P>::PROOF_BYTES>;

struct Witness {
    std::array<Fp, 3> wp;
    std::array<Fn, 3> wn;
    Fp kp;
};

Witness honest() {
    Witness w;
    w.wp = {Fp::from_u64(3), Fp::from_u64(5), Fp::from_u64(8)};
    w.kp = Fp::from_u64(120);
    const Fn x = Fn::from_u64(7);
    w.wn = {x, x * x * x, (x * x * x * x).inv()};
    return w;
}

const Digest MU = {1, 2, 3};
const std::array<uint8_t, 3> BINDER = {9, 9, 9};

template <typename P> Proof<P> prove(const Witness& w, size_t* failed = nullptr) {
    Proof<P> proof{};
    ProveSeed rho{};
    auto st = prove_commit<ToyRelation, P>(proof, MU, w.wp, w.wn, rho);
    prove_finish<ToyRelation, P>(proof, st, ToyRelation::instance{w.kp}, BINDER, failed);
    return proof;
}

template <typename P>
bool verify(const Proof<P>& proof, const Fp& kp, const Digest& mu = MU,
            std::span<const uint8_t> binder = BINDER) {
    auto st = verify_commit<ToyRelation, P>(proof, mu);
    return st && verify_finish<ToyRelation, P>(proof, *st, ToyRelation::instance{kp}, binder);
}

template <typename P> void honest_and_tampered() {
    const Witness w = honest();
    size_t failed = 1;
    const auto proof = prove<P>(w, &failed);
    EXPECT_EQ(failed, 0u);
    EXPECT_TRUE(verify<P>(proof, w.kp));
    EXPECT_FALSE(verify<P>(proof, w.kp + Fp::one()));
    EXPECT_FALSE(verify<P>(proof, w.kp, Digest{}));
    const std::array<uint8_t, 1> other{0};
    EXPECT_FALSE(verify<P>(proof, w.kp, MU, other));

    // Flip a bit in every 97th byte, one at a time.
    for (size_t i = 0; i < proof.size(); i += 97) {
        auto bad = proof;
        bad[i] ^= 1;
        EXPECT_FALSE(verify<P>(bad, w.kp)) << "byte " << i;
    }
}

TEST(VoleithP256, HonestFast) { honest_and_tampered<Fast>(); }
TEST(VoleithP256, HonestSmall) { honest_and_tampered<Small>(); }

TEST(VoleithP256, CheatingProver) {
    // Wrong product.
    Witness w = honest();
    w.wp[2] = Fp::from_u64(9);
    size_t failed = 0;
    auto proof = prove<Fast>(w, &failed);
    EXPECT_GT(failed, 0u);
    EXPECT_FALSE(verify<Fast>(proof, w.kp));

    // x y = 0.
    w = honest();
    w.wn = {Fn::zero(), Fn::zero(), Fn::one()};
    proof = prove<Fast>(w, &failed);
    EXPECT_GT(failed, 0u);
    EXPECT_FALSE(verify<Fast>(proof, w.kp));
}

// The leaf PRG matches faest's AES-CTR PRG.
TEST(VoleithP256, LeafPrg) {
    using namespace vole_mole::voleith_p256::detail;
    for (uint8_t seed_byte : {0, 1, 77}) {
        Seed seed{};
        seed.fill(seed_byte);
        seed[3] = 9;
        Prg::expanded_key_t key;
        faest::aes_keygen<faest::secpar::s128>(&key, faest::block128::load(seed.data()));
        std::array<uint8_t, 16> iv_bytes{};
        iv_bytes.fill(static_cast<uint8_t>(seed_byte * 3 + 1));
        const auto iv = faest::block128::load(iv_bytes.data());
        std::array<faest::block128, 64> a, b;
        leaf_prg<64>(key, iv, 0x12345u + seed_byte, a.data());
        Prg::gen<1, 64>(&key, iv, 0x12345u + seed_byte, uint32_t{0}, b.data());
        for (size_t i = 0; i < 64; ++i) {
            std::array<uint8_t, 16> x, y;
            a[i].store(x.data());
            b[i].store(y.data());
            EXPECT_EQ(x, y) << i;
        }
    }
}

} // namespace
