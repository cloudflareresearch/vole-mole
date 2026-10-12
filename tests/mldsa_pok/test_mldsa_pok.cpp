#include "vole_mole/mldsa.hpp"
#include "vole_mole/mldsa_pok.hpp"

#include "mldsa/mldsa.hpp"        // internal
#include "mldsa_pok/prover.hpp"   // internal
#include "mldsa_pok/relation.hpp" // internal
#include "voleith.hpp"            // internal

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <random>
#include <ratio>
#include <span>
#include <stdexcept>
#include <string_view>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::mldsa_pok::detail;
namespace md = vole_mole::mldsa::detail;

namespace {

std::span<const uint8_t> bytes(std::string_view s) {
    return {reinterpret_cast<const uint8_t*>(s.data()), s.size()};
}

struct Fixture {
    mldsa::KeyPair<P> kp;
    mldsa::Signature<P> sig;
    std::string_view msg = "message to sign";
    std::string_view ctx = "ctx";

    explicit Fixture(uint8_t s = 0) {
        mldsa::Seed xi;
        for (size_t i = 0; i < xi.size(); ++i) {
            xi[i] = static_cast<uint8_t>(i + s);
        }
        kp = mldsa::keygen<P>(xi);
        mldsa::Rnd rnd{};
        rnd[0] = s;
        sig = mldsa::sign<P>(kp.sk, bytes(msg), bytes(ctx), rnd);
    }

    Statement statement() const { return statement_for(kp.pk, bytes(msg), bytes(ctx)); }
    Witness witness() const { return make_witness(statement(), *md::decode_signature<P>(sig)); }
};

bool verify(const Fixture& f, const mldsa_pok::Proof& proof) {
    return mldsa_pok::verify(f.kp.pk, bytes(f.msg), bytes(f.ctx), proof);
}

bool get_bit(std::span<const uint8_t> b, size_t i) { return ((b[i / 8] >> (i % 8)) & 1) != 0; }

CheckSeed seed_of(uint32_t s) {
    CheckSeed seed{};
    for (size_t i = 0; i < 4; ++i) {
        seed[i] = static_cast<uint8_t>(s >> (8 * i));
    }
    return seed;
}

// Whether the checks hold on the witness (in the clear).
bool checks_hold(const Statement& stmt, const Witness& w, const CheckSeed& seed) {
    const auto weights = MlDsaModQ::make_weights(check_weights(stmt, seed));
    return MlDsaModQ::holds(weights,
                            [&](size_t j, size_t i) { return get_bit(w.prefix, value_bit(j, i)); });
}

} // namespace

// The UseHint characterization of relation.hpp: if r = alpha w1 + gamma2 (hp - hn) + f (mod q)
// with f in (-gamma2, gamma2], then UseHint(0, r) = w1, or there's a hint and UseHint(1, r) = w1.
// And conversely, for every r and h, the honest representation exists except for the three
// boundary cases.
TEST(MlDsaPok, UseHintCharacterization) {
    const int32_t g2 = static_cast<int32_t>(GAMMA2);
    size_t uncovered = 0;
    for (uint32_t r = 0; r < Q; ++r) {
        const uint32_t r1 = md::high_bits(r, GAMMA2);
        for (int dw = -2; dw <= 2; ++dw) {
            const uint32_t w1 = static_cast<uint32_t>((static_cast<int>(r1) + dw + 44) % 44);
            const int32_t e = md::fq_centered(md::fq_sub(r, md::fq_mul(ALPHA, w1)));
            for (int u = 0; u < 3; ++u) { // neg, none, pos
                const int32_t f = e - g2 * (u - 1);
                if (-g2 < f && f <= g2) {
                    const bool ok = md::use_hint(false, r, GAMMA2) == w1 ||
                                    (u != 1 && md::use_hint(true, r, GAMMA2) == w1);
                    ASSERT_TRUE(ok) << r << " " << w1 << " " << u;
                }
            }
        }
        for (const bool h : {false, true}) {
            const uint32_t w1 = md::use_hint(h, r, GAMMA2);
            const int32_t e = md::fq_centered(md::fq_sub(r, md::fq_mul(ALPHA, w1)));
            const bool none = -g2 < e && e <= g2;
            const bool hinted = (g2 < e && e <= 2 * g2) || (-2 * g2 < e && e <= -g2);
            if (!h) {
                // Without a hint, e is in (-gamma2, gamma2], except e = -gamma2 for w1 = 0.
                ASSERT_TRUE(none || (w1 == 0 && e == -g2)) << r;
            } else {
                ASSERT_FALSE(none) << r;
                uncovered += !hinted;
            }
        }
    }
    // e = -alpha with w1 = 0, and e = alpha + 1 with w1 = 43.
    EXPECT_EQ(uncovered, 2u);
}

TEST(MlDsaPok, Constants) {
    // The hint-weight sum needs exactly HINT_CARRIES committed bits.
    HintCols::CountOps ops;
    std::vector<std::vector<HintCols::CountOps::Wire>> cols;
    hint_weight_columns(ops, [](size_t) { return HintCols::CountOps::Wire{}; }, cols);
    HintCols::reduce(ops, cols, [](size_t, HintCols::CountOps::Wire) {});
    EXPECT_EQ(ops.carries, HINT_CARRIES);

    std::printf("proof: %zu bytes (key %zu bits, e %zu bytes); witness %zu bits (prefix %zu, "
                "checks %zu)\n",
                mldsa_pok::PROOF_BYTES, 8 * vole_mole::detail::VOLE_WITNESS_BYTES<BinRelation>,
                vole_mole::detail::DERIVED_E_BYTES<BinRelation>, B_WITNESS_BITS, B_PREFIX_BITS,
                MlDsaModQ::ANSWER_BITS);
}

// The weights computed with NTTs (relation.hpp) are those of <gamma, A z - c t1 2^d - gamma2 psi -
// f>, for random z, c, psi, and f, computed directly.
TEST(MlDsaPok, CheckWeights) {
    const Fixture f;
    const auto stmt = f.statement();
    const CheckSeed seed = seed_of(5);
    const auto w = check_weights(stmt, seed);

    std::mt19937_64 rng(1);
    const auto rand_q = [&] { return static_cast<Fq>(rng() % Q); };
    std::array<Poly, L> z;
    Poly c;
    std::array<Poly, K> psi, fv;
    for (auto& p : z) {
        std::ranges::generate(p, rand_q);
    }
    std::ranges::generate(c, rand_q);
    for (size_t i = 0; i < K; ++i) {
        std::ranges::generate(psi[i], rand_q);
        std::ranges::generate(fv[i], rand_q);
    }
    // e = A z - c t1 2^d - gamma2 psi - f
    std::array<Poly, K> e;
    {
        std::array<Poly, L> z_hat = z;
        for (auto& p : z_hat) {
            md::ntt(p);
        }
        Poly c_hat = c;
        md::ntt(c_hat);
        for (size_t i = 0; i < K; ++i) {
            Poly acc{};
            for (size_t l = 0; l < L; ++l) {
                md::multiply_ntts_acc(acc, stmt.parsed.a_hat[i * L + l], z_hat[l]);
            }
            Poly t1_hat;
            for (size_t n = 0; n < N; ++n) {
                t1_hat[n] = md::fq_mul(stmt.parsed.t1[i][n], 1u << md::D);
            }
            md::ntt(t1_hat);
            Poly ct{};
            md::multiply_ntts_acc(ct, c_hat, t1_hat);
            for (size_t n = 0; n < N; ++n) {
                acc[n] = md::fq_sub(acc[n], ct[n]);
            }
            md::inv_ntt(acc);
            for (size_t n = 0; n < N; ++n) {
                e[i][n] = md::fq_sub(md::fq_sub(acc[n], md::fq_mul(GAMMA2, psi[i][n])), fv[i][n]);
            }
        }
    }
    // gamma, recovered from the weights of f.
    for (size_t k = 0; k < ModQSpec::NUM_CHECKS; ++k) {
        const auto wk = std::span(w).subspan(k * NUM_VALUES, NUM_VALUES);
        Fq direct = 0, weighted = 0;
        for (size_t i = 0; i < K; ++i) {
            for (size_t n = 0; n < N; ++n) {
                const Fq gamma = md::fq_neg(wk[V_OFF_F + i * N + n]);
                EXPECT_EQ(wk[V_OFF_PSI + i * N + n], md::fq_mul(GAMMA2, wk[V_OFF_F + i * N + n]));
                direct = md::fq_add(direct, md::fq_mul(gamma, e[i][n]));
                weighted = md::fq_add(weighted, md::fq_mul(wk[V_OFF_PSI + i * N + n], psi[i][n]));
                weighted = md::fq_add(weighted, md::fq_mul(wk[V_OFF_F + i * N + n], fv[i][n]));
            }
        }
        for (size_t l = 0; l < L; ++l) {
            for (size_t n = 0; n < N; ++n) {
                weighted = md::fq_add(weighted, md::fq_mul(wk[V_OFF_Z + l * N + n], z[l][n]));
            }
        }
        for (size_t x = 0; x < N; ++x) {
            weighted = md::fq_add(weighted, md::fq_mul(wk[V_OFF_C + x], c[x]));
        }
        EXPECT_EQ(direct, weighted) << k;
    }
}

// The checks hold on an honest witness and (almost surely) fail if a value is off.
TEST(MlDsaPok, ChecksHoldOnWitness) {
    const Fixture f;
    const auto stmt = f.statement();
    const auto w = f.witness();
    for (uint32_t s = 0; s < 4; ++s) {
        EXPECT_TRUE(checks_hold(stmt, w, seed_of(s))) << s;
    }
    for (const size_t bit : {z_bit(3, 0), z_bit(1000, 17), c_bit(5, 1), hint_bit(9, 0),
                             w1_bit(77, 4), f_bit(1023, 2)}) {
        auto bad = w;
        bad.prefix[bit / 8] ^= static_cast<uint8_t>(1u << (bit % 8));
        EXPECT_FALSE(checks_hold(stmt, bad, seed_of(0))) << bit;
    }
}

// The range checks in the clear: x <= MAX iff the constraints hold.
TEST(MlDsaPok, RangeLe) {
    const auto holds = [](auto range, uint32_t max, uint32_t x) {
        using R = decltype(range);
        const auto bit = [&](size_t i) { return ((x >> i) & 1) != 0; };
        const bool t = R::helper(bit);
        // Evaluate the constraints in the clear: as in RangeLe::rec, with the prefix product.
        bool prefix = bit(R::NUM_BITS - 1);
        bool ok = true;
        bool cut_done = !R::HELPER;
        for (ptrdiff_t i = static_cast<ptrdiff_t>(R::NUM_BITS) - 2; i >= 0; --i) {
            if (!cut_done && i + 1 == static_cast<ptrdiff_t>(R::CUT_BIT)) {
                cut_done = true;
                prefix = t;
            }
            if ((max >> i) & 1) {
                prefix = prefix && bit(static_cast<size_t>(i));
            } else {
                ok = ok && !(prefix && bit(static_cast<size_t>(i)));
            }
        }
        return ok;
    };
    for (uint32_t x = 0; x < (1u << Z_BITS); ++x) {
        ASSERT_EQ(holds(ZRange{}, 2 * Z_BOUND, x), x <= 2 * Z_BOUND) << x;
        ASSERT_EQ(holds(FRange{}, ALPHA - 1, x), x <= ALPHA - 1) << x;
    }
}

// The carry budget is far above the number the checks need.
TEST(MlDsaPok, CarryBudget) {
    const Fixture f;
    const auto stmt = f.statement();
    std::vector<double> counts;
    for (uint32_t s = 0; s < 100; ++s) {
        counts.push_back(static_cast<double>(
            MlDsaModQ::count_carries(MlDsaModQ::make_weights(check_weights(stmt, seed_of(s))))));
    }
    double mean = 0, var = 0;
    for (const auto c : counts) {
        mean += c;
    }
    mean /= static_cast<double>(counts.size());
    for (const auto c : counts) {
        var += (c - mean) * (c - mean);
    }
    const double sd = std::sqrt(var / static_cast<double>(counts.size()));
    std::printf("check carries: mean %.1f, sd %.1f, max %.0f, budget %zu (mean + %.1f sd)\n", mean,
                sd, *std::ranges::max_element(counts), MlDsaModQ::CARRY_BUDGET,
                (static_cast<double>(MlDsaModQ::CARRY_BUDGET) - mean) / sd);
    EXPECT_GT(static_cast<double>(MlDsaModQ::CARRY_BUDGET), mean + 8 * sd);
}

TEST(MlDsaPok, ProvesAndVerifies) {
    const Fixture f;
    const auto t0 = std::chrono::steady_clock::now();
    const auto proof = mldsa_pok::prove(f.kp.pk, bytes(f.msg), bytes(f.ctx), f.sig);
    const auto t1 = std::chrono::steady_clock::now();
    EXPECT_EQ(proof.size(), mldsa_pok::PROOF_BYTES);
    EXPECT_TRUE(verify(f, proof));
    const auto t2 = std::chrono::steady_clock::now();
    std::printf("prove %.1f ms, verify %.1f ms\n",
                std::chrono::duration<double, std::milli>(t1 - t0).count(),
                std::chrono::duration<double, std::milli>(t2 - t1).count());

    // Wrong statement.
    EXPECT_FALSE(mldsa_pok::verify(f.kp.pk, bytes("another message"), bytes(f.ctx), proof));
    EXPECT_FALSE(mldsa_pok::verify(f.kp.pk, bytes(f.msg), bytes("ctx2"), proof));
    const Fixture other(1);
    EXPECT_FALSE(mldsa_pok::verify(other.kp.pk, bytes(f.msg), bytes(f.ctx), proof));
    // Wrong length.
    EXPECT_FALSE(verify(f, std::vector<uint8_t>(proof.begin(), proof.end() - 1)));
}

TEST(MlDsaPok, RejectsTampering) {
    const Fixture f(2);
    const auto proof = prove_with_seed(f.kp.pk, bytes(f.msg), bytes(f.ctx), f.sig, Rho{1});
    ASSERT_TRUE(verify(f, proof));
    constexpr size_t E_BYTES = vole_mole::detail::DERIVED_E_BYTES<BinRelation>;
    constexpr size_t FAEST_BYTES = PROOF_BYTES_ - E_BYTES;
    for (const size_t i :
         {size_t{0}, FAEST_BYTES / 2, FAEST_BYTES - 1, FAEST_BYTES,
          FAEST_BYTES + B_PREFIX_BYTES / 2, FAEST_BYTES + B_PREFIX_BYTES, PROOF_BYTES_ - 1}) {
        auto bad = proof;
        bad[i] ^= 1;
        EXPECT_FALSE(verify(f, bad)) << i;
    }
}

TEST(MlDsaPok, RejectsInvalidSignature) {
    const Fixture f;
    auto sig = f.sig;
    sig[100] ^= 1;
    EXPECT_THROW(mldsa_pok::prove(f.kp.pk, bytes(f.msg), bytes(f.ctx), sig), std::invalid_argument);
}

// Cheating provers, each with a witness that's wrong in one place: the prover then produces an
// invalid proof. (Release builds only: in debug builds, the prover asserts that its constraints
// hold.)
TEST(MlDsaPok, RejectsCheatingProvers) {
#ifdef NDEBUG
    const Fixture f(4);
    const auto stmt = f.statement();
    const Rho rho{9};
    const auto honest = f.witness();
    ASSERT_TRUE(verify(f, prove_witness(stmt, honest, rho)));
    const auto flip = [&](size_t bit) {
        auto w = honest;
        w.prefix[bit / 8] ^= static_cast<uint8_t>(1u << (bit % 8));
        return w;
    };
    // A bit of w1 (so the hash input), a hint bit, a bit of c, the slack, bits of z and f, and a
    // range helper.
    for (const size_t bit :
         {w1_bit(17, 3), hint_bit(100, 0), hint_bit(101, 1), c_bit(200, 0), B_OFF_SLACK + 2,
          z_bit(12, 5), z_bit(13, 17), f_bit(400, 0), f_bit(401, 17), z_helper_bit(14)}) {
        EXPECT_FALSE(verify(f, prove_witness(stmt, flip(bit), rho))) << bit;
    }

    // z + Z_BOUND out of range. (This breaks the equations, too; RangeLe tests the range check
    // alone.)
    {
        auto w = honest;
        const size_t j = 20;
        for (size_t b = 0; b < Z_BITS; ++b) {
            const bool v = (((2 * Z_BOUND + 1) >> b) & 1) != 0;
            w.prefix[z_bit(j, b) / 8] =
                static_cast<uint8_t>((w.prefix[z_bit(j, b) / 8] & ~(1u << (z_bit(j, b) % 8))) |
                                     (unsigned{v} << (z_bit(j, b) % 8)));
        }
        EXPECT_FALSE(verify(f, prove_witness(stmt, w, rho)));
    }
#else
    GTEST_SKIP() << "the prover asserts its constraints in debug builds";
#endif
}

// The honest prover handles many signatures.
TEST(MlDsaPok, Completeness) {
    size_t proven = 0;
    for (uint8_t s = 10; s < 60; ++s) {
        const Fixture f(s);
        const auto stmt = f.statement();
        const auto w = f.witness();
        ASSERT_TRUE(checks_hold(stmt, w, seed_of(s))) << int{s};
        if (s < 12) {
            EXPECT_TRUE(verify(f, prove_witness(stmt, w, Rho{s})));
            ++proven;
        }
    }
    EXPECT_EQ(proven, 2u);
}
