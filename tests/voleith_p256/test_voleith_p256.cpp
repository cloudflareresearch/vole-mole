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

// A relation with a derived F_p witness: w_0 = 3 and w_(i+1) = w_i^2 + i (degree 2), and
// w_0 w_1 w_2 w_3 = k_p (degree 4), so the QuickSilver degree over F_p is 8.
struct DerivedRelation {
    static constexpr size_t LP = 40, LN = 3, DP = 4, DN = 3, KP = 12;
    struct instance {
        Fp kp;
    };
    template <typename Ctx> static void constraints(Ctx& ctx, const instance& x) {
        ctx.add_p(ctx.wp(0) - Fp::from_u64(3));
        for (size_t i = 0; i + 1 < LP; ++i) {
            ctx.add_p(ctx.wp(i) * ctx.wp(i) + Fp::from_u64(i) - ctx.wp(i + 1));
        }
        ctx.add_p(ctx.wp(0) * ctx.wp(1) * ctx.wp(2) * ctx.wp(3) - x.kp);
        const auto xx = ctx.wn(0), y = ctx.wn(1), z = ctx.wn(2);
        ctx.add_n(xx * xx * xx - y);
        ctx.add_n(xx * y * z - Fn::one());
    }
};

template <typename P>
using DerivedProof = std::array<uint8_t, Layout<DerivedRelation, P>::PROOF_BYTES>;

struct DerivedWitness {
    std::array<Fp, DerivedRelation::LP> wp;
    std::array<Fn, 3> wn;
    Fp kp;
};

DerivedWitness derived_honest() {
    DerivedWitness w;
    w.wp[0] = Fp::from_u64(3);
    for (size_t i = 0; i + 1 < DerivedRelation::LP; ++i) {
        w.wp[i + 1] = w.wp[i] * w.wp[i] + Fp::from_u64(i);
    }
    w.kp = w.wp[0] * w.wp[1] * w.wp[2] * w.wp[3];
    const Fn x = Fn::from_u64(7);
    w.wn = {x, x * x * x, (x * x * x * x).inv()};
    return w;
}

template <typename P> DerivedProof<P> prove_derived(const DerivedWitness& w, size_t* failed) {
    DerivedProof<P> proof{};
    ProveSeed rho{};
    auto st = prove_commit<DerivedRelation, P>(proof, MU, w.wp, w.wn, rho);
    prove_finish<DerivedRelation, P>(proof, st, DerivedRelation::instance{w.kp}, BINDER, failed);
    return proof;
}

template <typename P> bool verify_derived(const DerivedProof<P>& proof, const Fp& kp) {
    auto st = verify_commit<DerivedRelation, P>(proof, MU);
    return st &&
           verify_finish<DerivedRelation, P>(proof, *st, DerivedRelation::instance{kp}, BINDER);
}

template <typename P> void derived_honest_and_tampered() {
    using Lay = Layout<DerivedRelation, P>;
    static_assert(Lay::DERIVED && Lay::DP == 8 && Lay::WP_ROWS == 12);
    const DerivedWitness w = derived_honest();
    size_t failed = 1;
    const auto proof = prove_derived<P>(w, &failed);
    EXPECT_EQ(failed, 0u);
    EXPECT_TRUE(verify_derived<P>(proof, w.kp));
    EXPECT_FALSE(verify_derived<P>(proof, w.kp + Fp::one()));
    for (size_t i = 0; i < proof.size(); i += 97) {
        auto bad = proof;
        bad[i] ^= 1;
        EXPECT_FALSE(verify_derived<P>(bad, w.kp)) << "byte " << i;
    }
    // Every element of e.
    for (size_t i = 0; i < DerivedRelation::LP; ++i) {
        auto bad = proof;
        bad[Lay::OFF_E + ELEM_BYTES * i + 3] ^= 1;
        EXPECT_FALSE(verify_derived<P>(bad, w.kp)) << "e " << i;
    }
}

TEST(VoleithP256, DerivedHonestFast) { derived_honest_and_tampered<Fast>(); }
TEST(VoleithP256, DerivedHonestSmall) { derived_honest_and_tampered<Small>(); }

TEST(VoleithP256, DerivedCheatingProver) {
    // Each element of the chain, wrong.
    for (const size_t i : {size_t{0}, size_t{1}, size_t{17}, DerivedRelation::LP - 1}) {
        DerivedWitness w = derived_honest();
        w.wp[i] += Fp::one();
        size_t failed = 0;
        const auto proof = prove_derived<Fast>(w, &failed);
        EXPECT_GT(failed, 0u);
        EXPECT_FALSE(verify_derived<Fast>(proof, w.kp)) << i;
    }
}

struct DirectRelation : DerivedRelation {
    static constexpr size_t KP = 0;
};

TEST(VoleithP256, DerivedProofIsSmaller) {
    using Direct = DirectRelation;
    // Each derived element costs 1 element instead of TAU; the key, TAU each; the degree doubles.
    using D = Layout<DerivedRelation, Fast>;
    using C = Layout<Direct, Fast>;
    static_assert(!C::DERIVED);
    EXPECT_EQ(static_cast<long>(C::PROOF_BYTES) - static_cast<long>(D::PROOF_BYTES),
              static_cast<long>(ELEM_BYTES) *
                  (static_cast<long>(Fast::TAU) * (40 - 12) - 40 - (Fast::TAU - 1) * 4 - 4));
}

TEST(VoleithP256, LocalPrg) {
    const LocalPrg<Fp> g('t', 64, 200);
    EXPECT_EQ(g.key_len(), 64u);
    std::array<Fp, 64> v, k;
    for (size_t j = 0; j < 64; ++j) {
        v[j] = Fp::from_u64(1000 + 7 * j);
        k[j] = Fp::from_u64(5 + 3 * j * j);
    }
    const Fp delta = Fp::from_u64(0x1234567);
    std::array<Fp, 64> macs;
    for (size_t j = 0; j < 64; ++j) {
        macs[j] = v[j] + k[j] * delta;
    }
    for (size_t i = 0; i < 200; ++i) {
        const auto c = g.eval_prover(i, v, k);
        // The value, and the homogeneous evaluation of the MACs.
        EXPECT_EQ(c[2], g.eval(i, k));
        EXPECT_EQ(c[0] + c[1] * delta + c[2] * delta * delta, g.eval_verifier(i, macs, delta));
    }
    // The outputs depend on the tag and the sizes.
    EXPECT_NE(g.eval(0, k), LocalPrg<Fp>('u', 64, 200).eval(0, k));
    EXPECT_NE(g.eval(0, k), LocalPrg<Fp>('t', 64, 201).eval(0, k));
    EXPECT_EQ(g.eval(5, k), LocalPrg<Fp>('t', 64, 200).eval(5, k));
}

TEST(VoleithP256, PrgKeyLen) {
    EXPECT_EQ(prg_key_len(694), 192u);
    for (const auto& e : detail::PRG_KEY_LENS) {
        EXPECT_LT(e.key, e.max_outputs);
        EXPECT_EQ(prg_key_len(e.max_outputs), e.key);
    }
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
