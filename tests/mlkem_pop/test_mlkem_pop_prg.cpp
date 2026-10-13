// The ML-KEM PoP with a witness derived from a short key with the MQ PRG over F_q (experimental).

#include "vole_mole/mlkem.hpp"

#include "mlkem_pop/prg_helpers.hpp"
#include "voleith_fq/field.hpp"   // internal
#include "voleith_fq/local.hpp"   // internal
#include "voleith_fq/mq.hpp"      // internal
#include "voleith_fq/voleith.hpp" // internal

#include "test.hpp"

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <random>
#include <span>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::mlkem;
using namespace vole_mole::test::mlkem_pop_prg;
using namespace vole_mole::voleith_fq::detail;
using vole_mole::test::filled;

namespace {

const std::array<uint8_t, 4> CONTEXT = {1, 2, 3, 4};
const ProveSeed RHO = filled<PROVE_SEED_BYTES>(0x50);

template <ParamSet P> const KeyPair<P>& key_pair() {
    static const KeyPair<P> kp = keygen<P>(filled<mlkem::SEED_BYTES>(0x00));
    return kp;
}

template <typename P_, typename Prg_> struct Config {
    using P = P_;
    using Prg = Prg_;
};

template <typename C> class MlKemPopPrgTest : public ::testing::Test {};
using Configs =
    ::testing::Types<Config<MlKem512, MqPrg<1>>, Config<MlKem768, MqPrg<1>>,
                     Config<MlKem768, MqPrg<3>>, Config<MlKem1024, MqPrg<1>>,
                     Config<MlKem512, LocalPrg<true>>, Config<MlKem768, LocalPrg<true>>,
                     Config<MlKem1024, LocalPrg<true>>, Config<MlKem768, LocalPrg<false>>>;
TYPED_TEST_SUITE(MlKemPopPrgTest, Configs);

} // namespace

// The committed evaluation of the PRG is consistent: c0 + c1 Delta + c2 Delta^2 = G(V + k Delta),
// and c2 = G(k).
template <typename Map> class FqPrgTest : public ::testing::Test {};
using Maps = ::testing::Types<MqMap<96, 2>, LocalPrg<true>::Map<96>, LocalPrg<false>::Map<256>>;
TYPED_TEST_SUITE(FqPrgTest, Maps);

TYPED_TEST(FqPrgTest, CommittedEvalConsistent) {
    using Map = TypeParam;
    constexpr size_t N = Map::NUM_OUTPUTS_V;
    const Map map{std::span<const uint8_t>(CONTEXT)};
    constexpr size_t n = Map::KEY_LEN;
    std::mt19937 rng(1);
    auto rand_fq = [&] { return static_cast<Fq>(rng() % Q); };

    std::vector<Fq> key(n);
    std::array<std::vector<Fq>, EXT_DEGREE> v, k;
    for (auto& x : key) {
        x = rand_fq();
    }
    Fq16 delta;
    for (auto& c : delta.c) {
        c = rand_fq();
    }
    for (size_t t = 0; t < EXT_DEGREE; ++t) {
        v[t].resize(n);
        k[t].resize(n);
    }
    for (size_t j = 0; j < n; ++j) {
        Fq16 vj;
        for (size_t t = 0; t < EXT_DEGREE; ++t) {
            vj.c[t] = v[t][j] = rand_fq();
        }
        Fq16 kj = vj;
        kj.add_scaled(key[j], delta);
        for (size_t t = 0; t < EXT_DEGREE; ++t) {
            k[t][j] = kj.c[t];
        }
    }
    std::array<std::span<const Fq>, EXT_DEGREE> vs, ks;
    for (size_t t = 0; t < EXT_DEGREE; ++t) {
        vs[t] = v[t];
        ks[t] = k[t];
    }
    std::vector<Fq> c0(EXT_DEGREE * N), c1(EXT_DEGREE * N), c2(N), out(EXT_DEGREE * N);
    std::array<Fq, N> plain;
    map.prove_eval(vs, key, c0, c1, c2);
    map.verify_eval(ks, delta, out);
    map.eval(std::span<const Fq, n>(key), plain);
    for (size_t i = 0; i < N; ++i) {
        EXPECT_EQ(c2[i], plain[i]);
        Fq16 a0, a1, kk;
        for (size_t t = 0; t < EXT_DEGREE; ++t) {
            a0.c[t] = c0[t * N + i];
            a1.c[t] = c1[t * N + i];
            kk.c[t] = out[t * N + i];
        }
        const Fq16 expect = a0 + a1 * delta + c2[i] * (delta * delta);
        EXPECT_EQ(expect, kk);
    }
}

TYPED_TEST(MlKemPopPrgTest, Verifies) {
    using P = typename TypeParam::P;
    using Prg = typename TypeParam::Prg;
    const auto& [ek, dk] = key_pair<P>();
    const auto s = witness_of<P>(dk);
    const auto proof = prove<P, Prg>(ek, s, CONTEXT, RHO);
    EXPECT_TRUE((verify<P, Prg>(ek, CONTEXT, proof)));
    // Wrong context.
    EXPECT_FALSE((verify<P, Prg>(ek, {}, proof)));
}

TYPED_TEST(MlKemPopPrgTest, RejectsTampering) {
    using P = typename TypeParam::P;
    using Prg = typename TypeParam::Prg;
    using Lay = Layout<Rel<P, Prg>>;
    const auto& [ek, dk] = key_pair<P>();
    const auto proof = prove<P, Prg>(ek, witness_of<P>(dk), CONTEXT, RHO);
    for (const size_t off : {Lay::OFF_D, Lay::OFF_E, Lay::OFF_E + Lay::E_BYTES / 2, Lay::OFF_QS}) {
        auto bad = proof;
        bad[off] ^= 1;
        EXPECT_FALSE((verify<P, Prg>(ek, CONTEXT, bad))) << off;
    }
}

// A short but wrong s: s is in range, but e = L(s) + e0 isn't.
TYPED_TEST(MlKemPopPrgTest, RejectsWrongWitness) {
    using P = typename TypeParam::P;
    using Prg = typename TypeParam::Prg;
    const auto& [ek, dk] = key_pair<P>();
    auto s = witness_of<P>(dk);
    s[0] = s[0] == 0 ? 1 : 0;
    EXPECT_FALSE((verify<P, Prg>(ek, CONTEXT, prove<P, Prg>(ek, s, CONTEXT, RHO))));
    // s = 0: s is short, e = e0 isn't.
    std::vector<Fq> zero(s.size());
    EXPECT_FALSE((verify<P, Prg>(ek, CONTEXT, prove<P, Prg>(ek, zero, CONTEXT, RHO))));
}
