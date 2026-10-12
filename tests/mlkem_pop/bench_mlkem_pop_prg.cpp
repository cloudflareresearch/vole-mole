// Benchmarks of the ML-KEM PoP with the witness committed directly (NoPrg) and derived with the MQ
// PRG over F_q split into c instances (MqPrg<c>). Experimental.

#include "vole_mole/mlkem.hpp"

#include "mlkem_pop/prg_helpers.hpp"
#include "voleith_fq/field.hpp"   // internal
#include "voleith_fq/local.hpp"   // internal
#include "voleith_fq/mq.hpp"      // internal
#include "voleith_fq/voleith.hpp" // internal

#include "test.hpp"

#include <benchmark/benchmark.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <string>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::test::mlkem_pop_prg;
using voleith_fq::detail::LocalPrg;
using voleith_fq::detail::MqPrg;
using voleith_fq::detail::NoPrg;

namespace {

const auto CONTEXT = vole_mole::test::filled<32>(0x10);

voleith_fq::detail::ProveSeed seed_from_counter(uint64_t i) {
    voleith_fq::detail::ProveSeed seed{};
    for (size_t j = 0; j < sizeof(i); ++j) {
        seed[j] = static_cast<uint8_t>(i >> (8 * j));
    }
    return seed;
}

template <mlkem::ParamSet P, typename Prg> std::string label() {
    using Lay = voleith_fq::detail::Layout<Rel<P, Prg>>;
    return std::to_string(PROOF_BYTES<P, Prg>) + " B, key " + std::to_string(Lay::VL) +
           ", QS degree " + std::to_string(Lay::D);
}

template <mlkem::ParamSet P, typename Prg> void BM_Prove(benchmark::State& state) {
    const auto kp = mlkem::keygen<P>(vole_mole::test::filled<mlkem::SEED_BYTES>(0));
    const auto s = witness_of<P>(kp.dk);
    (void)prove<P, Prg>(kp.ek, s, CONTEXT, seed_from_counter(0)); // expand the PRG's map
    uint64_t i = 0;
    for (auto _ : state) {
        auto proof = prove<P, Prg>(kp.ek, s, CONTEXT, seed_from_counter(i++));
        benchmark::DoNotOptimize(proof);
    }
    state.SetLabel(label<P, Prg>());
}

template <mlkem::ParamSet P, typename Prg> void BM_Verify(benchmark::State& state) {
    const auto kp = mlkem::keygen<P>(vole_mole::test::filled<mlkem::SEED_BYTES>(0));
    const auto proof = prove<P, Prg>(kp.ek, witness_of<P>(kp.dk), CONTEXT, seed_from_counter(0));
    for (auto _ : state) {
        bool ok = verify<P, Prg>(kp.ek, CONTEXT, proof);
        benchmark::DoNotOptimize(ok);
        if (!ok) {
            state.SkipWithError("proof failed to verify");
            break;
        }
    }
    state.SetLabel(label<P, Prg>());
}

#define BENCH_ALL(P)                                                                               \
    BENCHMARK(BM_Prove<P, NoPrg>)->Unit(benchmark::kMillisecond);                                  \
    BENCHMARK(BM_Verify<P, NoPrg>)->Unit(benchmark::kMillisecond);                                 \
    BENCHMARK(BM_Prove<P, MqPrg<1>>)->Unit(benchmark::kMillisecond);                               \
    BENCHMARK(BM_Verify<P, MqPrg<1>>)->Unit(benchmark::kMillisecond);                              \
    BENCHMARK(BM_Prove<P, MqPrg<2>>)->Unit(benchmark::kMillisecond);                               \
    BENCHMARK(BM_Verify<P, MqPrg<2>>)->Unit(benchmark::kMillisecond);                              \
    BENCHMARK(BM_Prove<P, MqPrg<4>>)->Unit(benchmark::kMillisecond);                               \
    BENCHMARK(BM_Verify<P, MqPrg<4>>)->Unit(benchmark::kMillisecond);                              \
    BENCHMARK(BM_Prove<P, MqPrg<8>>)->Unit(benchmark::kMillisecond);                               \
    BENCHMARK(BM_Verify<P, MqPrg<8>>)->Unit(benchmark::kMillisecond);                              \
    BENCHMARK(BM_Prove<P, LocalPrg<true>>)->Unit(benchmark::kMillisecond);                         \
    BENCHMARK(BM_Verify<P, LocalPrg<true>>)->Unit(benchmark::kMillisecond);                        \
    BENCHMARK(BM_Prove<P, LocalPrg<false>>)->Unit(benchmark::kMillisecond);                        \
    BENCHMARK(BM_Verify<P, LocalPrg<false>>)->Unit(benchmark::kMillisecond);

BENCH_ALL(mlkem::MlKem512)
BENCH_ALL(mlkem::MlKem768)
BENCH_ALL(mlkem::MlKem1024)

} // namespace

namespace {

// The committed evaluation of the PRG alone (prover side).
template <size_t N, size_t C> void BM_PrgProveEval(benchmark::State& state) {
    using Map = voleith_fq::detail::MqMap<N, C>;
    using voleith_fq::detail::EXT_DEGREE;
    using voleith_fq::detail::Fq;
    const Map map{std::span<const uint8_t>(CONTEXT)};
    std::vector<Fq> key(Map::KEY_LEN, 5);
    std::array<std::vector<Fq>, EXT_DEGREE> v;
    std::array<std::span<const Fq>, EXT_DEGREE> vs;
    for (size_t t = 0; t < EXT_DEGREE; ++t) {
        v[t].assign(Map::KEY_LEN, static_cast<Fq>(t + 1));
        vs[t] = v[t];
    }
    std::vector<Fq> c0(EXT_DEGREE * N), c1(EXT_DEGREE * N), c2(N);
    for (auto _ : state) {
        map.prove_eval(vs, key, c0, c1, c2);
        benchmark::DoNotOptimize(c0.data());
    }
}
BENCHMARK(BM_PrgProveEval<768, 1>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_PrgProveEval<768, 8>)->Unit(benchmark::kMillisecond);

} // namespace

namespace {

// Expanding the PRG's public map (done once per process and parameter set).
template <size_t N, size_t C> void BM_PrgExpand(benchmark::State& state) {
    using Map = voleith_fq::detail::MqMap<N, C>;
    for (auto _ : state) {
        const Map map{std::span<const uint8_t>(CONTEXT)};
        benchmark::DoNotOptimize(&map);
    }
    size_t coeffs = 0;
    using Lay = voleith_fq::detail::MqLayout<N, C>;
    for (size_t t = 0; t < C; ++t) {
        coeffs += Lay::outputs(t) * Map::tri(Lay::key_len(t));
    }
    state.SetLabel(std::to_string(2 * coeffs / 1000) + " kB");
}
BENCHMARK(BM_PrgExpand<512, 1>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_PrgExpand<768, 1>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_PrgExpand<768, 8>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_PrgExpand<1024, 1>)->Unit(benchmark::kMillisecond);

} // namespace
