#include "voleith_p256/voleith.hpp"

#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <vector>

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

} // namespace
