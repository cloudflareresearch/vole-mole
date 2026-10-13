#include "vole_mole/ecdsa_pok.hpp"

#include "ecdsa_pok/relation.hpp"
#include "p256/curve.hpp"

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <random>
#include <vector>

namespace {

using namespace vole_mole::ecdsa_pok;
using namespace vole_mole::ecdsa_pok::detail;
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

Signature sign(const KeyPair& kp, std::span<const uint8_t> msg, std::mt19937_64& rng) {
    for (;;) {
        const auto sig = p256::ecdsa_sign_with_nonce(kp.d, random_scalar(rng), msg);
        if (sig) {
            Signature out;
            std::copy(sig->r.begin(), sig->r.end(), out.begin());
            std::copy(sig->s.begin(), sig->s.end(), out.begin() + 32);
            return out;
        }
    }
}

std::vector<uint8_t> bytes(const char* s) { return {s, s + std::char_traits<char>::length(s)}; }

TEST(EcdsaPok, Counts) {
    for (const size_t nb : {1, 2}) {
        CountOps ops;
        prefix_circuit(ops, 64 * nb - 9, nullptr);
        EXPECT_EQ(ops.next, prefix_bits(nb)) << nb;
    }
    // The link carries over random challenges.
    size_t max = 0, sum = 0;
    constexpr size_t TRIALS = 3000;
    for (size_t i = 0; i < TRIALS; ++i) {
        Digest d{};
        d[0] = static_cast<uint8_t>(i);
        d[1] = static_cast<uint8_t>(i >> 8);
        const size_t c = link_carries(derive_link_challenge(d));
        max = std::max(max, c);
        sum += c;
    }
    std::printf("link carries: mean %zu, max %zu, budget %zu\n", sum / TRIALS, max, LINK_BUDGET);
    EXPECT_LT(max, LINK_BUDGET);
    for (const size_t len : {0, 55, 56, 119}) {
        std::printf("proof bytes (msg %zu B): fast %zu, small %zu\n", len,
                    proof_bytes(len, Params::fast), proof_bytes(len, Params::small));
    }
}

TEST(EcdsaPok, Honest) {
    std::mt19937_64 rng(1);
    const KeyPair kp = keygen(rng);
    const auto ctx = bytes("context");
    for (const size_t len : {0, 32, 55, 100}) {
        std::vector<uint8_t> msg(len);
        for (auto& b : msg) {
            b = static_cast<uint8_t>(rng());
        }
        const Signature sig = sign(kp, msg, rng);
        const auto proof = prove(kp.pk, msg, sig, ctx);
        EXPECT_EQ(proof.size(), proof_bytes(len));
        EXPECT_TRUE(verify(kp.pk, len, ctx, proof)) << len;
        EXPECT_FALSE(verify(kp.pk, len, bytes("other"), proof));
        if (len > 0) {
            EXPECT_FALSE(verify(kp.pk, len - 1, ctx, proof));
        }
        const KeyPair other = keygen(rng);
        EXPECT_FALSE(verify(other.pk, len, ctx, proof));
    }
}

// White-box tests: prove with a modified witness, and check that the proof is rejected.
struct WhiteBox {
    std::mt19937_64 rng{3};
    KeyPair kp = keygen(rng);
    std::vector<uint8_t> msg = bytes("a hidden message");
    Signature sig = sign(kp, msg, rng);
    std::array<uint8_t, 32> seed{7};
    Tables tables = make_tables(kp.q);
    Digest mu = statement_digest(kp.pk, msg.size(), bytes("ctx"), false);

    Witness witness() const {
        p256::Signature s;
        std::copy_n(sig.begin(), 32, s.r.begin());
        std::copy_n(sig.begin() + 32, 32, s.s.begin());
        return make_witness(kp.q, tables, msg, s, seed);
    }
    using S = Scheme<1, false>;
    std::vector<uint8_t> prove(const Witness& w) const {
        std::vector<uint8_t> proof(S::PROOF_BYTES);
        prove_with_witness<1, false>(std::span<uint8_t, S::PROOF_BYTES>(proof), mu, msg.size(),
                                     tables, w, seed);
        return proof;
    }
    bool verify(const std::vector<uint8_t>& proof) const {
        return verify_proof<1, false>(std::span<const uint8_t, S::PROOF_BYTES>(proof), mu,
                                      msg.size(), tables);
    }
};

TEST(EcdsaPok, WhiteBoxHonest) {
    const WhiteBox wb;
    EXPECT_TRUE(wb.verify(wb.prove(wb.witness())));
}

TEST(EcdsaPok, Tampered) {
    const WhiteBox wb;
    const auto proof = wb.prove(wb.witness());
    using S = WhiteBox::S;
    std::vector<size_t> offsets = {0,          S::OFF_ARITH, S::OFF_ARITH + 16, S::OFF_ZN,
                                   S::OFF_ZP,  S::OFF_Y,     S::OFF_Y + 32,     proof.size() - 1};
    for (size_t i = 0; i < 24; ++i) {
        offsets.push_back((i * 7919 * 13) % proof.size());
    }
    for (const size_t off : offsets) {
        auto bad = proof;
        bad[off] ^= 0x10;
        EXPECT_FALSE(wb.verify(bad)) << off;
    }
}

// A different message, with a consistent SHA-256 computation in the binary proof, but the hash
// of the signed message over F_n.
TEST(EcdsaPok, CheatOtherMessage) {
    const WhiteBox wb;
    auto w = wb.witness();
    auto other = wb.msg;
    other[0] ^= 1;
    w.bin.padded = vole_mole::sha256::pad(other);
    w.bin.traces = sha256_traces(w.bin.padded);
    EXPECT_FALSE(wb.verify(wb.prove(w)));
}

// faest-arch-opt's QuickSilver prover asserts that the binary constraints hold, so cheating in
// the binary proof can only be tested with NDEBUG.
#ifdef NDEBUG
#define SKIP_IF_ASSERTS()
#else
#define SKIP_IF_ASSERTS() GTEST_SKIP() << "the binary prover asserts that its constraints hold"
#endif

// The message bits don't match the SHA-256 trace.
TEST(EcdsaPok, CheatInconsistentHash) {
    SKIP_IF_ASSERTS();
    const WhiteBox wb;
    auto w = wb.witness();
    w.bin.padded[0] ^= 1;
    EXPECT_FALSE(wb.verify(wb.prove(w)));
}

// X in the binary proof isn't x(R).
TEST(EcdsaPok, CheatX) {
    const WhiteBox wb;
    auto w = wb.witness();
    w.bin.x[0] ^= 1;
    EXPECT_FALSE(wb.verify(wb.prove(w)));
}

// X is x(R) + p, which isn't canonical (and so gives the wrong r).
TEST(EcdsaPok, CheatNonCanonicalX) {
    SKIP_IF_ASSERTS();
    const WhiteBox wb;
    auto w = wb.witness();
    p256::Limbs x = load_limbs_le(w.bin.x.data());
    if (x[3] < 0xffffffff00000000ULL) { // x + p < 2^256
        p256::Limbs y{};
        p256::detail::limbs_add(y, x, p256::Fp::M);
        store_limbs_le(w.bin.x.data(), y);
        // Keep the F_n side consistent with the non-canonical X.
        std::array<uint8_t, 32> be;
        for (size_t i = 0; i < 32; ++i) {
            be[i] = w.bin.x[31 - i];
        }
        w.wn[WN_X] = p256::Fn::reduce_32(be);
        w.wn[WN_INV] = (p256::Fn::from_canonical(w.u[1]) * w.wn[WN_X]).inv();
        EXPECT_FALSE(wb.verify(wb.prove(w)));
    } else {
        GTEST_SKIP() << "x(R) + p >= 2^256";
    }
}

// The scalars over F_n don't match the digits over F_p.
TEST(EcdsaPok, CheatLimbs) {
    const WhiteBox wb;
    auto w = wb.witness();
    w.wn[WN_U1] += p256::Fn::one();
    EXPECT_FALSE(wb.verify(wb.prove(w)));
}

// u1 X = u2 e doesn't hold, or the inverse is wrong.
TEST(EcdsaPok, CheatScalarEquation) {
    const WhiteBox wb;
    auto w = wb.witness();
    w.wn[WN_E] += p256::Fn::one();
    EXPECT_FALSE(wb.verify(wb.prove(w)));
    w = wb.witness();
    w.wn[WN_INV] += p256::Fn::one();
    EXPECT_FALSE(wb.verify(wb.prove(w)));
}

// A digit out of range, or a wrong slope.
TEST(EcdsaPok, CheatComb) {
    const WhiteBox wb;
    auto w = wb.witness();
    w.wp[WP_A + 5] += p256::Fp::from_u64(16);
    EXPECT_FALSE(wb.verify(wb.prove(w)));
    w = wb.witness();
    w.wp[WP_LAMBDA + 10] += p256::Fp::one();
    EXPECT_FALSE(wb.verify(wb.prove(w)));
}

// The masks of a link differ between the two proofs.
TEST(EcdsaPok, CheatMasks) {
    const WhiteBox wb;
    auto w = wb.witness();
    w.wn[WN_RHO] += p256::Fn::one();
    EXPECT_FALSE(wb.verify(wb.prove(w)));
    w = wb.witness();
    w.wp[WP_RHO] += p256::Fp::one();
    EXPECT_FALSE(wb.verify(wb.prove(w)));
    w = wb.witness();
    w.wn[WN_SIGMA] += p256::Fn::one();
    EXPECT_FALSE(wb.verify(wb.prove(w)));
}

TEST(EcdsaPok, SmallParams) {
    std::mt19937_64 rng(5);
    const KeyPair kp = keygen(rng);
    const auto msg = bytes("message");
    const Signature sig = sign(kp, msg, rng);
    const auto proof = prove(kp.pk, msg, sig, {}, Params::small);
    EXPECT_EQ(proof.size(), proof_bytes(msg.size(), Params::small));
    EXPECT_TRUE(verify(kp.pk, msg.size(), {}, proof, Params::small));
    EXPECT_FALSE(verify(kp.pk, msg.size(), {}, proof, Params::fast));
}

TEST(EcdsaPok, RejectsBadInputs) {
    std::mt19937_64 rng(6);
    const KeyPair kp = keygen(rng);
    const auto msg = bytes("message");
    Signature sig = sign(kp, msg, rng);
    // A signature on another message, or a modified one.
    EXPECT_THROW(prove(kp.pk, bytes("other"), sig, {}), std::invalid_argument);
    sig[63] ^= 1;
    EXPECT_THROW(prove(kp.pk, msg, sig, {}), std::invalid_argument);
    // An invalid public key.
    PublicKey pk = kp.pk;
    pk[64] ^= 1;
    EXPECT_THROW(prove(pk, msg, sign(kp, msg, rng), {}), std::invalid_argument);
    EXPECT_FALSE(verify(pk, msg.size(), {}, std::vector<uint8_t>(proof_bytes(msg.size()))));
    // Too long a message.
    const std::vector<uint8_t> long_msg(MAX_MESSAGE_BYTES + 1);
    EXPECT_THROW(prove(kp.pk, long_msg, sign(kp, long_msg, rng), {}), std::invalid_argument);
    EXPECT_FALSE(verify(kp.pk, long_msg.size(), {}, std::vector<uint8_t>(100)));
    // A proof of the wrong length.
    EXPECT_FALSE(verify(kp.pk, msg.size(), {}, std::vector<uint8_t>(100)));
}

} // namespace
