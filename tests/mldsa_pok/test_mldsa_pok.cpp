#include "vole_mole/mldsa.hpp"
#include "vole_mole/mldsa_pok.hpp"

#include "mldsa/mldsa.hpp"             // internal
#include "mldsa_pok/prover.hpp"        // internal
#include "mldsa_pok/relation.hpp"      // internal
#include "mldsa_pok/verify_gadget.hpp" // internal
#include "voleith.hpp"                 // internal

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

mldsa_pok::Message message(uint8_t s) {
    mldsa_pok::Message m;
    for (size_t i = 0; i < m.size(); ++i) {
        m[i] = static_cast<uint8_t>(31 * i + s);
    }
    return m;
}

struct Fixture {
    mldsa::KeyPair<P> kp;
    mldsa_pok::Message msg;
    mldsa::Signature<P> sig;

    explicit Fixture(uint8_t s = 0) : msg(message(s)) {
        mldsa::Seed xi;
        for (size_t i = 0; i < xi.size(); ++i) {
            xi[i] = static_cast<uint8_t>(i + s);
        }
        kp = mldsa::keygen<P>(xi);
        sig = sign(msg, s);
    }

    // A signature on m with an empty context.
    mldsa::Signature<P> sign(const mldsa_pok::Message& m, uint8_t s = 0) const {
        mldsa::Rnd rnd{};
        rnd[0] = s;
        return mldsa::sign<P>(kp.sk, m, {}, rnd);
    }

    Statement statement() const { return make_statement(kp.pk); }
    Witness witness(const Statement& stmt) const {
        return make_witness(stmt, msg, *md::decode_signature<P>(sig));
    }
};

bool verify(const Fixture& f, std::span<const uint8_t> proof) {
    return mldsa_pok::verify(f.kp.pk, proof);
}

bool get_bit(std::span<const uint8_t> b, size_t i) { return ((b[i / 8] >> (i % 8)) & 1) != 0; }
void set_bit(std::span<uint8_t> b, size_t i, bool v) {
    b[i / 8] = static_cast<uint8_t>((b[i / 8] & ~(1u << (i % 8))) | (unsigned{v} << (i % 8)));
}
void flip_bit(std::span<uint8_t> b, size_t i) { b[i / 8] ^= static_cast<uint8_t>(1u << (i % 8)); }

CheckSeed seed_of(uint32_t s) {
    CheckSeed seed{};
    for (size_t i = 0; i < 4; ++i) {
        seed[i] = static_cast<uint8_t>(s >> (8 * i));
    }
    return seed;
}

// Whether the checks hold on the witness (in the clear).
bool checks_hold(const Statement& stmt, const Witness& w, const CheckSeed& seed) {
    return SIG.holds(w.prefix, MlDsaModQ::make_weights(check_weights(stmt.key, seed)));
}

// The value f' + gamma2 - 1 of coefficient j, and w1_j.
uint32_t f_value(const Witness& w, size_t j) {
    uint32_t v = 0;
    for (size_t b = 0; b < F_BITS; ++b) {
        v |= uint32_t{get_bit(w.prefix, SIG.f_bit(j, b))} << b;
    }
    return v;
}
void set_f_value(Witness& w, size_t j, uint32_t v) {
    for (size_t b = 0; b < F_BITS; ++b) {
        set_bit(w.prefix, SIG.f_bit(j, b), ((v >> b) & 1) != 0);
    }
}
uint32_t w1_value(const Witness& w, size_t j) {
    uint32_t v = 0;
    for (size_t b = 0; b < W1_BITS; ++b) {
        v |= uint32_t{get_bit(w.prefix, SIG.w1_bit(j, b))} << b;
    }
    return v;
}

} // namespace

// The UseHint characterization of verify_gadget.hpp. Soundness: if
// r = alpha w1 + gamma2 (hp - hn) + f (mod q) with f in (-gamma2, gamma2], or f = -gamma2 if
// w1 = 0, or f = gamma2 + 1 if w1 = 43 and there's a hint, then UseHint(0, r) = w1, or there's a
// hint and UseHint(1, r) = w1. Completeness: for every r and h, there's such a representation of
// w1 = UseHint(h, r), without a hint if h = 0.
TEST(MlDsaPok, UseHintCharacterization) {
    const int32_t g2 = static_cast<int32_t>(GAMMA2);
    const auto allowed = [&](uint32_t w1, int u, int32_t f) {
        return (-g2 < f && f <= g2) || (f == -g2 && w1 == 0) || (f == g2 + 1 && w1 == 43 && u != 1);
    };
    size_t guarded = 0;
    for (uint32_t r = 0; r < Q; ++r) {
        const uint32_t r1 = md::high_bits(r, GAMMA2);
        for (int dw = -2; dw <= 2; ++dw) {
            const uint32_t w1 = static_cast<uint32_t>((static_cast<int>(r1) + dw + 44) % 44);
            const int32_t e = md::fq_centered(md::fq_sub(r, md::fq_mul(ALPHA, w1)));
            for (int u = 0; u < 3; ++u) { // neg, none, pos
                const int32_t f = e - g2 * (u - 1);
                if (allowed(w1, u, f)) {
                    const bool ok = md::use_hint(false, r, GAMMA2) == w1 ||
                                    (u != 1 && md::use_hint(true, r, GAMMA2) == w1);
                    ASSERT_TRUE(ok) << r << " " << w1 << " " << u;
                }
            }
        }
        for (const bool h : {false, true}) {
            const uint32_t w1 = md::use_hint(h, r, GAMMA2);
            const int32_t e = md::fq_centered(md::fq_sub(r, md::fq_mul(ALPHA, w1)));
            bool covered = allowed(w1, 1, e);
            if (h) {
                covered = covered || allowed(w1, 0, e + g2) || allowed(w1, 2, e - g2);
            }
            ASSERT_TRUE(covered) << r << " " << h;
            const auto plain = [&](int32_t fv) { return -g2 < fv && fv <= g2; };
            guarded += !(plain(e) || (h && (plain(e + g2) || plain(e - g2))));
        }
    }
    // e = -gamma2 with w1 = 0 (without a hint), e = -alpha with w1 = 0, and e = alpha + 1 with
    // w1 = 43, which need the guarded values of f.
    EXPECT_EQ(guarded, 3u);
}

TEST(MlDsaPok, Constants) {
    // The hint-weight sum needs exactly HINT_CARRIES committed bits.
    HintCols::CountOps ops;
    std::vector<std::vector<HintCols::CountOps::Wire>> cols;
    SIG.hint_weight_columns(ops, [](size_t) { return HintCols::CountOps::Wire{}; }, cols);
    HintCols::reduce(ops, cols, [](size_t, HintCols::CountOps::Wire) {});
    EXPECT_EQ(ops.carries, HINT_CARRIES);

    std::printf("proof: %zu bytes (key %zu bits, e %zu bytes); witness %zu bits (message hash %zu, "
                "signature %zu, checks %zu)\n",
                mldsa_pok::PROOF_BYTES, 8 * vole_mole::detail::VOLE_WITNESS_BYTES<BinRelation>,
                vole_mole::detail::DERIVED_E_BYTES<BinRelation>, B_WITNESS_BITS,
                8 * Mu::WITNESS_BYTES, VerifyGadget::WITNESS_BITS, MlDsaModQ::ANSWER_BITS);
}

// MuHash computes the message representative of FIPS 204, with an empty context, also for
// messages that take more than one block.
TEST(MlDsaPok, MessageRepresentative) {
    const Fixture f;
    const auto stmt = f.statement();
    const auto check = [&](auto mu_hash, size_t base) {
        using M = decltype(mu_hash);
        std::vector<uint8_t> msg(M::MSG_BYTES);
        for (size_t i = 0; i < msg.size(); ++i) {
            msg[i] = static_cast<uint8_t>(7 * i + 1);
        }
        std::vector<uint8_t> witness(base + M::WITNESS_BYTES);
        const auto mu = M(base).encode_witness(witness, stmt.key.parsed.tr,
                                               std::span<const uint8_t, M::MSG_BYTES>(msg));
        EXPECT_EQ(mu, md::message_representative(stmt.key.parsed.tr, msg, {})) << M::MSG_BYTES;
        for (size_t i = 0; i < 8 * M::MSG_BYTES; ++i) {
            ASSERT_EQ(get_bit(witness, M(base).msg_bit(i)), get_bit(msg, i));
        }
    };
    check(Mu{0}, 0);
    check(MuHash<69>{0}, 3); // the longest message in one block
    static_assert(MuHash<69>::NUM_PERMUTATIONS == 1 && MuHash<70>::NUM_PERMUTATIONS == 2);
    check(MuHash<70>{0}, 0);
    check(MuHash<300>{0}, 5);
}

// The gadget's witness doesn't depend on where it is.
TEST(MlDsaPok, GadgetRelocates) {
    const Fixture f;
    const auto stmt = f.statement();
    const auto w = f.witness(stmt);
    const auto mu = md::message_representative(stmt.key.parsed.tr, f.msg, {});
    constexpr size_t BASE = 1000;
    const VerifyGadget moved{BASE, BASE + VerifyGadget::WITNESS_BYTES};
    std::vector<uint8_t> w2(BASE + VerifyGadget::WITNESS_BYTES);
    moved.encode_witness(w2, stmt.key, mu, *md::decode_signature<P>(f.sig));
    EXPECT_TRUE(std::equal(w2.begin() + BASE, w2.end(),
                           w.prefix.begin() + static_cast<ptrdiff_t>(SIG.base())));
    EXPECT_TRUE(moved.holds(w2, MlDsaModQ::make_weights(check_weights(stmt.key, seed_of(1)))));
    std::vector<uint8_t> short_witness(BASE + VerifyGadget::WITNESS_BYTES - 1);
    EXPECT_THROW(moved.encode_witness(short_witness, stmt.key, mu, *md::decode_signature<P>(f.sig)),
                 std::logic_error);
}

// The weights computed with NTTs (verify_gadget.hpp) are those of
// <gamma, A z - c t1 2^d - gamma2 psi - f>, for random z, c, psi, and f, computed directly.
TEST(MlDsaPok, CheckWeights) {
    const Fixture f;
    const auto stmt = f.statement();
    const auto w = check_weights(stmt.key, seed_of(5));

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
                md::multiply_ntts_acc(acc, stmt.key.parsed.a_hat[i * L + l], z_hat[l]);
            }
            Poly t1_hat;
            for (size_t n = 0; n < N; ++n) {
                t1_hat[n] = md::fq_mul(stmt.key.parsed.t1[i][n], 1u << md::D);
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
    const auto w = f.witness(stmt);
    for (uint32_t s = 0; s < 4; ++s) {
        EXPECT_TRUE(checks_hold(stmt, w, seed_of(s))) << s;
    }
    for (const size_t bit :
         {SIG.z_bit(3, 0), SIG.z_bit(1000, 17), SIG.c_bit(5, 1), SIG.hint_bit(9, 0),
          SIG.w1_bit(77, 4), SIG.f_bit(1023, 2), SIG.nb_bit(5), SIG.yb_bit(6)}) {
        auto bad = w;
        flip_bit(bad.prefix, bit);
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
        counts.push_back(static_cast<double>(MlDsaModQ::count_carries(
            MlDsaModQ::make_weights(check_weights(stmt.key, seed_of(s))))));
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
    const auto proof = mldsa_pok::prove(f.kp.pk, f.msg, f.sig);
    const auto t1 = std::chrono::steady_clock::now();
    EXPECT_EQ(proof.size(), mldsa_pok::PROOF_BYTES);
    EXPECT_TRUE(verify(f, proof));
    const auto t2 = std::chrono::steady_clock::now();
    std::printf("prove %.1f ms, verify %.1f ms\n",
                std::chrono::duration<double, std::milli>(t1 - t0).count(),
                std::chrono::duration<double, std::milli>(t2 - t1).count());

    // Wrong key.
    const Fixture other(1);
    EXPECT_FALSE(mldsa_pok::verify(other.kp.pk, proof));
    // Wrong length.
    EXPECT_FALSE(verify(f, std::span(proof).first(proof.size() - 1)));

    // Another message, under the same key.
    const auto msg2 = message(99);
    EXPECT_TRUE(verify(f, mldsa_pok::prove(f.kp.pk, msg2, f.sign(msg2))));
}

TEST(MlDsaPok, RejectsTampering) {
    const Fixture f(2);
    const auto proof = prove_with_seed(f.kp.pk, f.msg, f.sig, Rho{1});
    ASSERT_TRUE(verify(f, proof));
    EXPECT_EQ(proof, prove_with_seed(f.kp.pk, f.msg, f.sig, Rho{1}));
    constexpr size_t E_BYTES = vole_mole::detail::DERIVED_E_BYTES<BinRelation>;
    constexpr size_t FAEST_BYTES = PROOF_BYTES_ - E_BYTES;
    for (const size_t i :
         {size_t{0}, FAEST_BYTES / 2, FAEST_BYTES - 1, FAEST_BYTES, FAEST_BYTES + 7,
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
    EXPECT_THROW(mldsa_pok::prove(f.kp.pk, f.msg, sig), std::invalid_argument);
    // A signature on another message, with a context, or under another key.
    EXPECT_THROW(mldsa_pok::prove(f.kp.pk, message(1), f.sig), std::invalid_argument);
    EXPECT_THROW(mldsa_pok::prove(f.kp.pk, f.msg,
                                  mldsa::sign<P>(f.kp.sk, f.msg, bytes("ctx"), mldsa::Rnd{})),
                 std::invalid_argument);
    const Fixture other(1);
    EXPECT_THROW(mldsa_pok::prove(other.kp.pk, f.msg, f.sig), std::invalid_argument);
}

// Cheating provers, each with a witness that's wrong in one place: the prover then produces an
// invalid proof. (Release builds only: in debug builds, the prover asserts that its constraints
// hold.)
TEST(MlDsaPok, RejectsCheatingProvers) {
#ifdef NDEBUG
    const Fixture f(4);
    const auto stmt = f.statement();
    const Rho rho{9};
    const auto honest = f.witness(stmt);
    ASSERT_TRUE(verify(f, prove_witness(stmt, honest, rho)));
    const auto flip = [&](size_t bit) {
        auto w = honest;
        flip_bit(w.prefix, bit);
        return w;
    };
    // A bit of the message, a bit of the mu hash's state, a bit of w1 (so the hash input), a hint
    // bit, a bit of c, the slack, bits of z and f, a range helper, and the guarded bits.
    for (const size_t bit :
         {MU.msg_bit(0), MU.msg_bit(255), 8 * mldsa_pok::MESSAGE_BYTES + 1000, SIG.w1_bit(17, 3),
          SIG.hint_bit(100, 0), SIG.hint_bit(101, 1), SIG.c_bit(200, 0), SIG.slack_bit(2),
          SIG.z_bit(12, 5), SIG.z_bit(13, 17), SIG.f_bit(400, 0), SIG.f_bit(401, 17),
          SIG.z_helper_bit(14), SIG.nb_bit(402), SIG.yb_bit(403)}) {
        EXPECT_FALSE(verify(f, prove_witness(stmt, flip(bit), rho))) << bit;
    }

    // z + Z_BOUND out of range. (This breaks the equations, too; RangeLe tests the range check
    // alone.)
    {
        auto w = honest;
        for (size_t b = 0; b < Z_BITS; ++b) {
            set_bit(w.prefix, SIG.z_bit(20, b), (((2 * Z_BOUND + 1) >> b) & 1) != 0);
        }
        EXPECT_FALSE(verify(f, prove_witness(stmt, w, rho)));
    }

    // A signature on another message, with the witness of the message hash for this one.
    {
        const auto msg2 = message(77);
        auto w = make_witness(stmt, msg2, *md::decode_signature<P>(f.sign(msg2)));
        MU.encode_witness(w.prefix, stmt.key.parsed.tr, f.msg);
        EXPECT_FALSE(verify(f, prove_witness(stmt, w, rho)));
    }

    // The guards: f' + 1 with nb = 0 (or f' - 1 with yb = 1) represents the same f, but only if
    // w1 = 0 (w1 = 43 and there's a hint).
    {
        size_t j = 0;
        while (w1_value(honest, j) == 0 || f_value(honest, j) == ALPHA - 1) {
            ++j;
        }
        auto w = honest;
        set_bit(w.prefix, SIG.nb_bit(j), false);
        set_f_value(w, j, f_value(w, j) + 1);
        EXPECT_FALSE(verify(f, prove_witness(stmt, w, rho)));
    }
    {
        size_t j = 0;
        while (w1_value(honest, j) == 43 || f_value(honest, j) == 0) {
            ++j;
        }
        auto w = honest;
        set_bit(w.prefix, SIG.yb_bit(j), true);
        set_f_value(w, j, f_value(w, j) - 1);
        EXPECT_FALSE(verify(f, prove_witness(stmt, w, rho)));
    }
#else
    GTEST_SKIP() << "the prover asserts its constraints in debug builds";
#endif
}

// The guarded values of f in the circuit: f' + 1 with nb = 0 for a coefficient with w1 = 0 is
// another valid encoding of f, as is f' - 1 with yb = 1 for one with w1 = 43 and a hint.
TEST(MlDsaPok, GuardedValues) {
    const Fixture f(5);
    const auto stmt = f.statement();
    bool nb_done = false, yb_done = false;
    for (uint8_t s = 0; s < 40 && !(nb_done && yb_done); ++s) {
        const auto msg = message(s);
        auto w = make_witness(stmt, msg, *md::decode_signature<P>(f.sign(msg, s)));
        bool changed = false;
        for (size_t j = 0; j < NUM_R; ++j) {
            if (!nb_done && w1_value(w, j) == 0 && f_value(w, j) < ALPHA - 1) {
                set_bit(w.prefix, SIG.nb_bit(j), false);
                set_f_value(w, j, f_value(w, j) + 1);
                nb_done = changed = true;
            }
            if (!yb_done && w1_value(w, j) == 43 && !get_bit(w.prefix, SIG.hint_bit(j, 0)) &&
                f_value(w, j) > 0) {
                set_bit(w.prefix, SIG.yb_bit(j), true);
                set_f_value(w, j, f_value(w, j) - 1);
                yb_done = changed = true;
            }
        }
        if (changed) {
            for (uint32_t k = 0; k < 2; ++k) {
                EXPECT_TRUE(checks_hold(stmt, w, seed_of(k)));
            }
            EXPECT_TRUE(verify(f, prove_witness(stmt, w, Rho{s}))) << int{s};
        }
    }
    EXPECT_TRUE(nb_done);
    EXPECT_TRUE(yb_done);
}

// The honest prover handles many signatures.
TEST(MlDsaPok, Completeness) {
    size_t proven = 0;
    for (uint8_t s = 10; s < 60; ++s) {
        const Fixture f(s);
        const auto stmt = f.statement();
        const auto w = f.witness(stmt);
        ASSERT_TRUE(checks_hold(stmt, w, seed_of(s))) << int{s};
        if (s < 12) {
            EXPECT_TRUE(verify(f, prove_witness(stmt, w, Rho{s})));
            ++proven;
        }
    }
    EXPECT_EQ(proven, 2u);
}
