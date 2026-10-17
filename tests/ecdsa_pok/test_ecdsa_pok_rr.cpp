// Tests of the experimental ECDSA proof with a hidden key and a revealed R
// (src/ecdsa_pok/rr_relation.hpp).

#include "vole_mole/ecdsa_pok.hpp"

#include "ecdsa_pok/bin_ops.hpp"
#include "ecdsa_pok/link.hpp"
#include "ecdsa_pok/rr_arith.hpp"
#include "ecdsa_pok/rr_binary.hpp"
#include "ecdsa_pok/rr_relation.hpp"
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
namespace rr = vole_mole::ecdsa_pok::detail::rr;
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

KeyPair keygen(std::mt19937_64& rng) {
    KeyPair kp;
    kp.d = random_scalar(rng);
    kp.q = p256::scalar_mul(p256::GENERATOR, kp.d.canonical()).to_affine();
    kp.pk = p256::encode_point(kp.q);
    return kp;
}

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

TEST(EcdsaRr, Counts) {
    for (const size_t log : {2, 3}) {
        CountOps ops;
        if (log == 2) {
            rr::prefix_circuit<2>(ops, nullptr);
        } else {
            rr::prefix_circuit<3>(ops, nullptr);
        }
        EXPECT_EQ(ops.next, rr::PREFIX_BITS) << log;
    }
    EXPECT_EQ(rr::count_circuit_constraints<SHAPE_DIRECT>(),
              rr::CIRCUIT_CONSTRAINTS<SHAPE_DIRECT>());
    EXPECT_EQ(rr::count_circuit_constraints<SHAPE_DERIVED>(),
              rr::CIRCUIT_CONSTRAINTS<SHAPE_DERIVED>());
    auto carries = [&]<size_t LOG>() {
        size_t max = 0;
        double sum = 0, sq = 0;
        constexpr size_t TRIALS = 3000;
        for (size_t i = 0; i < TRIALS; ++i) {
            Digest d{};
            d[0] = static_cast<uint8_t>(i);
            d[1] = static_cast<uint8_t>(i >> 8);
            const size_t c = rr::link_carries<LOG>(derive_link_challenge(d));
            max = std::max(max, c);
            sum += static_cast<double>(c);
            sq += static_cast<double>(c) * static_cast<double>(c);
        }
        const double mean = sum / TRIALS;
        std::printf(
            "link carries (counters of size %zu): mean %.0f, sd %.1f, max %zu, budget %zu\n", LOG,
            mean, std::sqrt(sq / TRIALS - mean * mean), max, rr::LINK_BUDGET<LOG>);
        EXPECT_LT(max, rr::LINK_BUDGET<LOG>);
    };
    carries.template operator()<2>();
    carries.template operator()<4>();
    for (const auto prg : {WitnessPrg::none, WitnessPrg::local, WitnessPrg::mq}) {
        std::printf("proof bytes (witness PRG %d): fast %zu, medium %zu, small %zu\n",
                    static_cast<int>(prg), rr::proof_bytes({Vole::fast, prg}),
                    rr::proof_bytes({Vole::medium, prg}), rr::proof_bytes({Vole::small, prg}));
    }
    using S = rr::Scheme<Vole::fast, BinPrg::local>;
    std::printf("fast/local: R %zu B, binary %zu B, F_p/F_n %zu B (LP %zu, DP %zu)\n", rr::R_BYTES,
                S::BIN_BYTES, S::ARITH_BYTES, rr::LP, rr::DP);
}

TEST(EcdsaRr, Honest) {
    std::mt19937_64 rng(1);
    const auto ctx = bytes("context");
    for (const size_t len : {0, 32, 200}) {
        const KeyPair kp = keygen(rng);
        std::vector<uint8_t> msg(len);
        for (auto& b : msg) {
            b = static_cast<uint8_t>(rng());
        }
        const Signature sig = sign(kp, msg, rng);
        const auto proof = rr::prove(kp.pk, msg, sig, ctx);
        EXPECT_EQ(proof.size(), rr::proof_bytes());
        EXPECT_TRUE(rr::verify(msg, ctx, proof)) << len;
        EXPECT_FALSE(rr::verify(msg, bytes("other"), proof));
        auto other = msg;
        other.push_back(0);
        EXPECT_FALSE(rr::verify(other, ctx, proof));
        // The revealed R is the signature's nonce point, and r = x(R) mod n.
        p256::Signature s;
        std::copy_n(sig.begin(), 32, s.r.begin());
        std::copy_n(sig.begin() + 32, 32, s.s.begin());
        const auto rb = rr::encode_r(rr::nonce_point(kp.q, msg, s));
        EXPECT_TRUE(std::equal(rb.begin(), rb.end(), proof.begin()));
        EXPECT_EQ(p256::Fn::reduce_32(std::span<const uint8_t, 32>(proof.data(), 32)),
                  *p256::Fn::from_bytes(s.r));
    }
}

// White-box tests: prove with a modified witness, and check that the proof is rejected.
template <typename PrgT> struct WhiteBox {
    static constexpr BinPrg PRG = PrgT::value;
    std::mt19937_64 rng{3};
    KeyPair kp = keygen(rng);
    std::vector<uint8_t> msg = bytes("a public message");
    std::vector<uint8_t> ctx = bytes("ctx");
    p256::Signature sig = sign_raw(kp, msg, rng);
    std::array<uint8_t, rr::R_BYTES> rb = rr::encode_r(rr::nonce_point(kp.q, msg, sig));
    rr::Public pub = *rr::make_public(msg, ctx, rb, Vole::fast, PRG);
    std::array<uint8_t, 32> seed{7};

    rr::Witness witness() const { return rr::make_witness(kp.q, sig, pub, seed); }
    using S = rr::Scheme<Vole::fast, PRG>;
    std::vector<uint8_t> prove(const rr::Witness& w) const {
        std::vector<uint8_t> proof(S::PROOF_BYTES);
        rr::prove_with_witness<Vole::fast, PRG>(std::span<uint8_t, S::PROOF_BYTES>(proof), rb, pub,
                                                w, seed);
        return proof;
    }
    bool verify(const std::vector<uint8_t>& proof) const {
        return rr::verify(msg, ctx, proof, {Vole::fast, static_cast<WitnessPrg>(PRG)});
    }
};

template <typename PrgT> struct EcdsaRrWhiteBox : ::testing::Test {};
using Prgs = ::testing::Types<std::integral_constant<BinPrg, BinPrg::none>,
                              std::integral_constant<BinPrg, BinPrg::local>>;
TYPED_TEST_SUITE(EcdsaRrWhiteBox, Prgs);

TYPED_TEST(EcdsaRrWhiteBox, Honest) {
    const WhiteBox<TypeParam> wb;
    EXPECT_TRUE(wb.verify(wb.prove(wb.witness())));
}

TYPED_TEST(EcdsaRrWhiteBox, Tampered) {
    const WhiteBox<TypeParam> wb;
    const auto proof = wb.prove(wb.witness());
    using S = typename WhiteBox<TypeParam>::S;
    std::vector<size_t> offsets = {0,
                                   31,
                                   32,
                                   63,
                                   S::OFF_BIN,
                                   S::OFF_ARITH - 1,
                                   S::OFF_ARITH,
                                   S::OFF_ARITH + 16,
                                   S::OFF_ZP,
                                   proof.size() - 1};
    for (size_t i = 0; i < 24; ++i) {
        offsets.push_back((i * 7919 * 13) % proof.size());
    }
    for (const size_t off : offsets) {
        auto bad = proof;
        bad[off] ^= 0x10;
        EXPECT_FALSE(wb.verify(bad)) << off;
    }
}

// The bits of Q in the binary proof aren't Q (another key, or a flipped bit).
TYPED_TEST(EcdsaRrWhiteBox, CheatKeyBits) {
    WhiteBox<TypeParam> wb;
    auto w = wb.witness();
    w.bin.x[3] ^= 1;
    EXPECT_FALSE(wb.verify(wb.prove(w)));
    w = wb.witness();
    const KeyPair other = keygen(wb.rng);
    store_limbs_le(w.bin.x.data(), other.q.x.canonical());
    store_limbs_le(w.bin.y.data(), other.q.y.canonical());
    EXPECT_FALSE(wb.verify(wb.prove(w)));
}

// A digit out of range, or a wrong slope; the masks differ between the proofs.
TYPED_TEST(EcdsaRrWhiteBox, CheatComb) {
    const WhiteBox<TypeParam> wb;
    for (const size_t i : {rr::WP_S, rr::WP_S + 63, rr::WP_LAMBDA, rr::WP_LAMBDA + 17,
                           rr::WP_LAMBDA + rr::COMB_STEPS, rr::WP_RHO}) {
        auto w = wb.witness();
        w.wp[i] += (i < rr::WP_LAMBDA ? p256::Fp::from_u64(16) : p256::Fp::one());
        EXPECT_FALSE(wb.verify(wb.prove(w))) << i;
    }
    // A different s in range: Q' = s' T + U != Q.
    auto w = wb.witness();
    w.wp[rr::WP_S + 10] =
        w.wp[rr::WP_S + 10] == p256::Fp::zero() ? p256::Fp::one() : p256::Fp::zero();
    EXPECT_FALSE(wb.verify(wb.prove(w)));
}

// The R of another signature by the same key (a valid signature, but on another message).
TYPED_TEST(EcdsaRrWhiteBox, CheatOtherSignature) {
    WhiteBox<TypeParam> wb;
    const auto other = bytes("another message");
    const auto sig2 = sign_raw(wb.kp, other, wb.rng);
    const auto rb2 = rr::encode_r(rr::nonce_point(wb.kp.q, other, sig2));
    // The proof for the other message, presented for this one.
    const auto pub2 = *rr::make_public(other, wb.ctx, rb2, Vole::fast, WhiteBox<TypeParam>::PRG);
    const auto w2 = rr::make_witness(wb.kp.q, sig2, pub2, wb.seed);
    using S = typename WhiteBox<TypeParam>::S;
    std::vector<uint8_t> proof(S::PROOF_BYTES);
    rr::prove_with_witness<Vole::fast, WhiteBox<TypeParam>::PRG>(
        std::span<uint8_t, S::PROOF_BYTES>(proof), rb2, pub2, w2, wb.seed);
    EXPECT_TRUE(rr::verify(other, wb.ctx, proof,
                           {Vole::fast, static_cast<WitnessPrg>(WhiteBox<TypeParam>::PRG)}));
    EXPECT_FALSE(wb.verify(proof));
}

#ifdef NDEBUG
#define SKIP_IF_ASSERTS()
#else
#define SKIP_IF_ASSERTS() GTEST_SKIP() << "the binary prover asserts that its constraints hold"
#endif

// x_Q + p, which agrees with x_Q modulo p but isn't canonical.
TYPED_TEST(EcdsaRrWhiteBox, CheatNonCanonicalKey) {
    SKIP_IF_ASSERTS();
    const WhiteBox<TypeParam> wb;
    auto w = wb.witness();
    const p256::Limbs x = load_limbs_le(w.bin.x.data());
    if (x[3] >= 0xffffffff00000000ULL) {
        GTEST_SKIP() << "x_Q + p >= 2^256";
    }
    p256::Limbs y{};
    p256::detail::limbs_add(y, x, p256::Fp::M);
    store_limbs_le(w.bin.x.data(), y);
    EXPECT_FALSE(wb.verify(wb.prove(w)));
}

TEST(EcdsaRr, OtherParams) {
    std::mt19937_64 rng(5);
    const KeyPair kp = keygen(rng);
    const auto msg = bytes("message");
    const Signature sig = sign(kp, msg, rng);
    for (const auto vole : {Vole::medium, Vole::small}) {
        for (const auto prg : {WitnessPrg::none, WitnessPrg::local, WitnessPrg::mq}) {
            const Params params{vole, prg};
            const auto proof = rr::prove(kp.pk, msg, sig, {}, params);
            EXPECT_EQ(proof.size(), rr::proof_bytes(params));
            EXPECT_TRUE(rr::verify(msg, {}, proof, params));
            for (const auto other : {WitnessPrg::none, WitnessPrg::local, WitnessPrg::mq}) {
                const Params o{vole, other};
                if (other != prg && rr::proof_bytes(o) == proof.size()) {
                    EXPECT_FALSE(rr::verify(msg, {}, proof, o));
                }
            }
        }
    }
}

TEST(EcdsaRr, RejectsBadInputs) {
    std::mt19937_64 rng(6);
    const KeyPair kp = keygen(rng);
    const auto msg = bytes("message");
    Signature sig = sign(kp, msg, rng);
    EXPECT_THROW(rr::prove(kp.pk, bytes("other"), sig, {}), std::invalid_argument);
    auto proof = rr::prove(kp.pk, msg, sig, {});
    // R off the curve, or not a field element.
    auto bad = proof;
    bad[63] ^= 1;
    EXPECT_FALSE(rr::verify(msg, {}, bad));
    std::fill_n(bad.begin(), 32, 0xff);
    EXPECT_FALSE(rr::verify(msg, {}, bad));
    sig[63] ^= 1;
    EXPECT_THROW(rr::prove(kp.pk, msg, sig, {}), std::invalid_argument);
    EXPECT_FALSE(rr::verify(msg, {}, std::vector<uint8_t>(100)));
}

} // namespace
