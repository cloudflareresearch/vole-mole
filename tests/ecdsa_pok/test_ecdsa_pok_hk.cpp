// Tests of the experimental hidden-key ECDSA proof (src/ecdsa_pok/hk_relation.hpp).

#include "vole_mole/ecdsa_pok.hpp"

#include "ecdsa_pok/bin_ops.hpp"
#include "ecdsa_pok/hk_arith.hpp"
#include "ecdsa_pok/hk_binary.hpp"
#include "ecdsa_pok/hk_relation.hpp"
#include "ecdsa_pok/link.hpp"
#include "p256/curve.hpp"
#include "p256/field.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <random>
#include <span>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <vector>

namespace {

using namespace vole_mole::ecdsa_pok;
using namespace vole_mole::ecdsa_pok::detail;
namespace hk = vole_mole::ecdsa_pok::detail::hk;
namespace p256 = vole_mole::p256;

struct KeyPair {
    p256::Fn d;
    p256::Affine q;
    PublicKey pk;
};

p256::Fn random_scalar(std::mt19937_64& rng) {
    p256::Limbs x;
    do {
        for (auto& l : x) {
            l = rng();
        }
    } while (p256::detail::limbs_ge(x, p256::Fn::M) || (x[0] | x[1] | x[2] | x[3]) == 0);
    return p256::Fn::from_canonical(x);
}

KeyPair keypair(const p256::Fn& d) {
    KeyPair kp;
    kp.d = d;
    kp.q = p256::scalar_mul(p256::GENERATOR, d.canonical()).to_affine();
    kp.pk = p256::encode_point(kp.q);
    return kp;
}
KeyPair keygen(std::mt19937_64& rng) { return keypair(random_scalar(rng)); }

p256::Signature sign_raw(const KeyPair& kp, std::span<const uint8_t> msg, std::mt19937_64& rng) {
    for (;;) {
        const auto sig = p256::ecdsa_sign_with_nonce(kp.d, random_scalar(rng), msg);
        if (sig) {
            return *sig;
        }
    }
}
Signature sign(const KeyPair& kp, std::span<const uint8_t> msg, std::mt19937_64& rng) {
    const auto sig = sign_raw(kp, msg, rng);
    Signature out;
    std::copy(sig.r.begin(), sig.r.end(), out.begin());
    std::copy(sig.s.begin(), sig.s.end(), out.begin() + 32);
    return out;
}

std::vector<uint8_t> bytes(const char* s) { return {s, s + std::char_traits<char>::length(s)}; }

TEST(EcdsaHk, Offsets) {
    EXPECT_TRUE(hk::offsets_are_sound());
    const auto& o = hk::offsets();
    for (const auto* p : {&o.h0, &o.h1, &o.h2, &o.pstar}) {
        EXPECT_TRUE(p->on_curve());
        EXPECT_FALSE(p->inf);
    }
    // Spot-check the comb tables: T_j[a] = a 16^j G + H_2.
    const auto& tab = hk::comb_tables();
    for (const auto [j, a] : {std::array<size_t, 2>{0, 0}, {0, 3}, {7, 15}, {63, 9}}) {
        p256::Fn k = p256::Fn::from_u64(a);
        for (size_t i = 0; i < j; ++i) {
            k *= p256::Fn::from_u64(16);
        }
        const auto expect = p256::scalar_mul(p256::GENERATOR, k.canonical())
                                .add(p256::Jacobian::from(o.h2))
                                .to_affine();
        EXPECT_EQ(tab.at(j, a), expect) << j << " " << a;
    }
}

TEST(EcdsaHk, Counts) {
    for (const size_t log : {2, 3}) {
        CountOps ops;
        if (log == 2) {
            hk::prefix_circuit<2>(ops, nullptr);
        } else {
            hk::prefix_circuit<3>(ops, nullptr);
        }
        EXPECT_EQ(ops.next, hk::PREFIX_BITS) << log;
    }
    EXPECT_EQ(hk::count_circuit_constraints<SHAPE_DIRECT>(),
              hk::CIRCUIT_CONSTRAINTS<SHAPE_DIRECT>());
    EXPECT_EQ(hk::count_circuit_constraints<SHAPE_DERIVED>(),
              hk::CIRCUIT_CONSTRAINTS<SHAPE_DERIVED>());
    auto carries = [&]<size_t LOG>() {
        size_t max = 0;
        double sum = 0, sq = 0;
        constexpr size_t TRIALS = 3000;
        for (size_t i = 0; i < TRIALS; ++i) {
            Digest d{};
            d[0] = static_cast<uint8_t>(i);
            d[1] = static_cast<uint8_t>(i >> 8);
            const size_t c = hk::link_carries<LOG>(derive_link_challenge(d));
            max = std::max(max, c);
            sum += static_cast<double>(c);
            sq += static_cast<double>(c) * static_cast<double>(c);
        }
        const double mean = sum / TRIALS;
        std::printf(
            "link carries (counters of size %zu): mean %.0f, sd %.1f, max %zu, budget %zu\n", LOG,
            mean, std::sqrt(sq / TRIALS - mean * mean), max, hk::LINK_BUDGET<LOG>);
        EXPECT_LT(max, hk::LINK_BUDGET<LOG>);
    };
    carries.template operator()<2>();
    carries.template operator()<4>();
    for (const auto prg : {WitnessPrg::none, WitnessPrg::local, WitnessPrg::mq}) {
        std::printf("proof bytes (witness PRG %d): fast %zu, medium %zu, small %zu\n",
                    static_cast<int>(prg), hk::proof_bytes({Vole::fast, prg}),
                    hk::proof_bytes({Vole::medium, prg}), hk::proof_bytes({Vole::small, prg}));
    }
    using S = hk::Scheme<Vole::fast, BinPrg::local>;
    std::printf("fast/local: binary %zu B, F_p/F_n %zu B (LP %zu, DP %zu, LN %zu, DN %zu)\n",
                S::BIN_BYTES, S::ARITH_BYTES, hk::LP, hk::DP, hk::LN, hk::DN);
}

TEST(EcdsaHk, Honest) {
    std::mt19937_64 rng(1);
    const auto ctx = bytes("context");
    for (const size_t len : {0, 32, 200}) {
        const KeyPair kp = keygen(rng);
        std::vector<uint8_t> msg(len);
        for (auto& b : msg) {
            b = static_cast<uint8_t>(rng());
        }
        const Signature sig = sign(kp, msg, rng);
        const auto proof = hk::prove(kp.pk, msg, sig, ctx);
        EXPECT_EQ(proof.size(), hk::proof_bytes());
        EXPECT_TRUE(hk::verify(msg, ctx, proof)) << len;
        EXPECT_FALSE(hk::verify(msg, bytes("other"), proof));
        auto other = msg;
        other.push_back(0);
        EXPECT_FALSE(hk::verify(other, ctx, proof));
    }
}

// A key equal to an offset makes an addition exceptional (P_0 + Q = H_1 + H_1), so an honest
// prover fails. (A cheating prover could exploit it, but it knows the secret key h_1; see
// hk_arith.hpp.)
TEST(EcdsaHk, KeyAtOffset) {
    std::mt19937_64 rng(2);
    const KeyPair kp = keypair(hk::offsets().h[1]);
    EXPECT_EQ(kp.q, hk::offsets().h1);
    const auto msg = bytes("message");
    const auto sig = sign_raw(kp, msg, rng);
    EXPECT_THROW(hk::make_witness(kp.q, msg, sig, std::array<uint8_t, 32>{}), std::runtime_error);
}

// White-box tests: prove with a modified witness, and check that the proof is rejected.
template <typename PrgT> struct WhiteBox {
    static constexpr BinPrg PRG = PrgT::value;
    std::mt19937_64 rng{3};
    KeyPair kp = keygen(rng);
    std::vector<uint8_t> msg = bytes("a public message");
    p256::Signature sig = sign_raw(kp, msg, rng);
    std::array<uint8_t, 32> seed{7};
    Digest mu = hk::statement_digest(msg, bytes("ctx"), Vole::fast, PRG);
    p256::Fn e = p256::Fn::reduce_32(vole_mole::sha256::hash(msg));

    hk::Witness witness() const { return hk::make_witness(kp.q, msg, sig, seed); }
    using S = hk::Scheme<Vole::fast, PRG>;
    std::vector<uint8_t> prove(const hk::Witness& w) const {
        std::vector<uint8_t> proof(S::PROOF_BYTES);
        hk::prove_with_witness<Vole::fast, PRG>(std::span<uint8_t, S::PROOF_BYTES>(proof), mu, e, w,
                                                seed);
        return proof;
    }
    bool verify(const std::vector<uint8_t>& proof) const {
        return hk::verify_proof<Vole::fast, PRG>(std::span<const uint8_t, S::PROOF_BYTES>(proof),
                                                 mu, e);
    }
};

template <typename PrgT> struct EcdsaHkWhiteBox : ::testing::Test {};
using Prgs = ::testing::Types<std::integral_constant<BinPrg, BinPrg::none>,
                              std::integral_constant<BinPrg, BinPrg::local>>;
TYPED_TEST_SUITE(EcdsaHkWhiteBox, Prgs);

TYPED_TEST(EcdsaHkWhiteBox, Honest) {
    const WhiteBox<TypeParam> wb;
    EXPECT_TRUE(wb.verify(wb.prove(wb.witness())));
}

TYPED_TEST(EcdsaHkWhiteBox, Tampered) {
    const WhiteBox<TypeParam> wb;
    const auto proof = wb.prove(wb.witness());
    using S = typename WhiteBox<TypeParam>::S;
    std::vector<size_t> offsets = {
        0,         S::OFF_ARITH - 1, S::OFF_ARITH,  S::OFF_ARITH + 16, S::OFF_ZN,
        S::OFF_ZP, S::OFF_Y,         S::OFF_Y + 32, proof.size() - 1};
    for (size_t i = 0; i < 24; ++i) {
        offsets.push_back((i * 7919 * 13) % proof.size());
    }
    for (const size_t off : offsets) {
        auto bad = proof;
        bad[off] ^= 0x10;
        EXPECT_FALSE(wb.verify(bad)) << off;
    }
}

// A signature on another message.
TYPED_TEST(EcdsaHkWhiteBox, CheatOtherMessage) {
    WhiteBox<TypeParam> wb;
    const auto other = bytes("another message");
    const auto w = hk::make_witness(wb.kp.q, other, sign_raw(wb.kp, other, wb.rng), wb.seed);
    EXPECT_FALSE(wb.verify(wb.prove(w)));
}

// Q isn't on the curve, or the table isn't of Q.
TYPED_TEST(EcdsaHkWhiteBox, CheatKey) {
    const WhiteBox<TypeParam> wb;
    auto w = wb.witness();
    w.wp[hk::WP_Q + 1] += p256::Fp::one();
    EXPECT_FALSE(wb.verify(wb.prove(w)));
    for (const size_t i : {hk::WP_TABLE + 3, hk::WP_TABLE_PTS + 4, hk::WP_TABLE_PTS + 29}) {
        w = wb.witness();
        w.wp[i] += p256::Fp::one();
        EXPECT_FALSE(wb.verify(wb.prove(w))) << i;
    }
}

// A digit out of range, or a wrong slope in the ladder (doubling or addition), comb, or last step.
TYPED_TEST(EcdsaHkWhiteBox, CheatScalarMul) {
    const WhiteBox<TypeParam> wb;
    for (const size_t i : {hk::WP_A + 5, hk::WP_B + 60, hk::WP_LADDER, hk::WP_LADDER + 1,
                           hk::WP_LADDER + 5, hk::WP_LADDER + hk::LADDER_STEPS - 1, hk::WP_SELECTED,
                           hk::WP_SELECTED + 77, hk::WP_COMB + 7, hk::WP_FINAL}) {
        auto w = wb.witness();
        w.wp[i] += (i < hk::WP_LADDER ? p256::Fp::from_u64(16) : p256::Fp::one());
        EXPECT_FALSE(wb.verify(wb.prove(w))) << i;
    }
}

// X in the binary proof isn't x(R).
TYPED_TEST(EcdsaHkWhiteBox, CheatX) {
    const WhiteBox<TypeParam> wb;
    auto w = wb.witness();
    w.bin.x[0] ^= 1;
    EXPECT_FALSE(wb.verify(wb.prove(w)));
}

// faest-arch-opt's QuickSilver prover asserts that the binary constraints hold.
#ifdef NDEBUG
#define SKIP_IF_ASSERTS()
#else
#define SKIP_IF_ASSERTS() GTEST_SKIP() << "the binary prover asserts that its constraints hold"
#endif

// X is x(R) + p, which isn't canonical.
TYPED_TEST(EcdsaHkWhiteBox, CheatNonCanonicalX) {
    SKIP_IF_ASSERTS();
    const WhiteBox<TypeParam> wb;
    auto w = wb.witness();
    p256::Limbs x = load_limbs_le(w.bin.x.data());
    if (x[3] >= 0xffffffff00000000ULL) {
        GTEST_SKIP() << "x(R) + p >= 2^256";
    }
    p256::Limbs y{};
    p256::detail::limbs_add(y, x, p256::Fp::M);
    store_limbs_le(w.bin.x.data(), y);
    std::array<uint8_t, 32> be;
    for (size_t i = 0; i < 32; ++i) {
        be[i] = w.bin.x[31 - i];
    }
    w.wn[hk::WN_X] = p256::Fn::reduce_32(be);
    w.wn[hk::WN_INV] = (p256::Fn::from_canonical(w.u[1]) * w.wn[hk::WN_X]).inv();
    EXPECT_FALSE(wb.verify(wb.prove(w)));
}

// The limbs over F_n don't match the digits; the scalar equation or the inverse is wrong; the masks
// differ between the proofs.
TYPED_TEST(EcdsaHkWhiteBox, CheatFn) {
    const WhiteBox<TypeParam> wb;
    for (const size_t i : {hk::WN_U1, hk::WN_U2 + 3, hk::WN_X, hk::WN_INV, hk::WN_RHO, hk::WN_SIGMA,
                           hk::WN_SIGMA + 1}) {
        auto w = wb.witness();
        w.wn[i] += p256::Fn::one();
        EXPECT_FALSE(wb.verify(wb.prove(w))) << i;
    }
    for (const size_t i : {hk::WP_RHO, hk::WP_SIGMA}) {
        auto w = wb.witness();
        w.wp[i] += p256::Fp::one();
        EXPECT_FALSE(wb.verify(wb.prove(w))) << i;
    }
}

TEST(EcdsaHk, OtherParams) {
    std::mt19937_64 rng(5);
    const KeyPair kp = keygen(rng);
    const auto msg = bytes("message");
    const Signature sig = sign(kp, msg, rng);
    for (const auto vole : {Vole::medium, Vole::small}) {
        for (const auto prg : {WitnessPrg::none, WitnessPrg::local, WitnessPrg::mq}) {
            const Params params{vole, prg};
            const auto proof = hk::prove(kp.pk, msg, sig, {}, params);
            EXPECT_EQ(proof.size(), hk::proof_bytes(params));
            EXPECT_TRUE(hk::verify(msg, {}, proof, params));
            for (const auto other : {WitnessPrg::none, WitnessPrg::local, WitnessPrg::mq}) {
                const Params o{vole, other};
                if (other != prg && hk::proof_bytes(o) == proof.size()) {
                    EXPECT_FALSE(hk::verify(msg, {}, proof, o));
                }
            }
        }
    }
}

TEST(EcdsaHk, RejectsBadInputs) {
    std::mt19937_64 rng(6);
    const KeyPair kp = keygen(rng);
    const auto msg = bytes("message");
    Signature sig = sign(kp, msg, rng);
    EXPECT_THROW(hk::prove(kp.pk, bytes("other"), sig, {}), std::invalid_argument);
    sig[63] ^= 1;
    EXPECT_THROW(hk::prove(kp.pk, msg, sig, {}), std::invalid_argument);
    PublicKey pk = kp.pk;
    pk[64] ^= 1;
    EXPECT_THROW(hk::prove(pk, msg, sign(kp, msg, rng), {}), std::invalid_argument);
    EXPECT_FALSE(hk::verify(msg, {}, std::vector<uint8_t>(100)));
}

} // namespace
