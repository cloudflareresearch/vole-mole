#include "mldsa_pok/shake_relation.hpp" // internal
#include "voleith.hpp"                  // internal

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <span>
#include <vector>

extern "C" {
#include "KeccakHash.h" // from xkcp
}

using namespace vole_mole::mldsa_pok::detail;
using vole_mole::detail::PROOF_BYTES;
using vole_mole::detail::ProveSeed;
using vole_mole::detail::voleith_prove;
using vole_mole::detail::voleith_verify;
using vole_mole::detail::WITNESS_BYTES;

namespace {

template <typename R> struct Fixture {
    using S = typename R::shape;
    typename R::instance x{};
    std::vector<uint8_t> witness;

    Fixture() {
        for (size_t i = 0; i < x.prefix.size(); ++i) {
            x.prefix[i] = static_cast<uint8_t>(3 * i + 1);
        }
        std::array<uint8_t, S::SECRET_BYTES> s;
        for (size_t i = 0; i < s.size(); ++i) {
            s[i] = static_cast<uint8_t>(i * i + 5);
        }
        witness = S::encode_witness(x.prefix, s, x.y);

        // The output is SHAKE256(P || S).
        std::array<uint8_t, S::OUT_BYTES> want;
        Keccak_HashInstance h;
        Keccak_HashInitialize_SHAKE256(&h);
        Keccak_HashUpdate(&h, x.prefix.data(), 8 * x.prefix.size());
        Keccak_HashUpdate(&h, s.data(), 8 * s.size());
        Keccak_HashFinal(&h, nullptr);
        Keccak_HashSqueeze(&h, want.data(), 8 * want.size());
        EXPECT_EQ(x.y, want);
    }

    std::vector<uint8_t> prove(const typename R::instance& inst) const {
        EXPECT_EQ(witness.size(), WITNESS_BYTES<R>);
        std::vector<uint8_t> proof(PROOF_BYTES<R>);
        voleith_prove<R>(std::span<uint8_t, PROOF_BYTES<R>>(proof),
                         std::span<const uint8_t, WITNESS_BYTES<R>>(witness), inst, ProveSeed<R>{});
        return proof;
    }
    bool verify(const typename R::instance& inst, const std::vector<uint8_t>& proof) const {
        return voleith_verify<R>(std::span<const uint8_t, PROOF_BYTES<R>>(proof), inst);
    }
};

template <typename R> class ShakeRelationTest : public ::testing::Test {};
using Relations = ::testing::Types<ShakeRelation<CtildeDeg9, Params128f<OWF_CTILDE_DEG9>>,
                                   ShakeRelation<CtildeDeg16, Params128f<OWF_CTILDE_DEG16>>,
                                   ShakeRelation<CtildeDeg9, Params128s<OWF_CTILDE_DEG9>>,
                                   ShakeRelation<CtildeDeg16, Params128s<OWF_CTILDE_DEG16>>>;
TYPED_TEST_SUITE(ShakeRelationTest, Relations);

} // namespace

TYPED_TEST(ShakeRelationTest, ProvesAndVerifies) {
    using R = TypeParam;
    using S = typename R::shape;
    const Fixture<R> f;
    const auto proof = f.prove(f.x);
    EXPECT_TRUE(f.verify(f.x, proof));
    std::printf("tau %zu, degree %zu: %zu blocks, %zu witness bits, %zu-byte proof\n",
                size_t{R::params::tau_v}, S::QS_DEGREE, S::NUM_BLOCKS, S::WITNESS_BITS,
                proof.size());

    auto other = f.x;
    other.y[0] ^= 1;
    EXPECT_FALSE(f.verify(other, proof));
    other = f.x;
    other.prefix[0] ^= 1;
    EXPECT_FALSE(f.verify(other, proof));
}
