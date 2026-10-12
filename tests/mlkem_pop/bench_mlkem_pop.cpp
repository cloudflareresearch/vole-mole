#include "vole_mole/mlkem.hpp"
#include "vole_mole/mlkem_pop.hpp"

#include "mlkem_pop/seeded.hpp" // internal

#include "test.hpp"

#include <benchmark/benchmark.h>

#include <cstddef>
#include <cstdint>
#include <string>

using namespace vole_mole;

namespace {

const auto CONTEXT = vole_mole::test::filled<32>(0x10);

// A different seed per iteration, so that every run computes a fresh proof.
mlkem_pop::detail::ProveSeed seed_from_counter(uint64_t i) {
    mlkem_pop::detail::ProveSeed seed{};
    for (size_t j = 0; j < sizeof(i); ++j) {
        seed[j] = static_cast<uint8_t>(i >> (8 * j));
    }
    return seed;
}

template <mlkem::ParamSet P> void BM_Prove(benchmark::State& state) {
    const auto kp = mlkem::keygen<P>(vole_mole::test::filled<mlkem::SEED_BYTES>(0));
    uint64_t i = 0;
    for (auto _ : state) {
        auto proof = mlkem_pop::detail::prove_with_seed<P>(kp.dk, CONTEXT, seed_from_counter(i++));
        benchmark::DoNotOptimize(proof);
    }
    state.SetLabel(std::to_string(mlkem_pop::PROOF_BYTES<P>) + "-byte proof");
}
BENCHMARK(BM_Prove<mlkem::MlKem512>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Prove<mlkem::MlKem768>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Prove<mlkem::MlKem1024>)->Unit(benchmark::kMillisecond);

template <mlkem::ParamSet P> void BM_Verify(benchmark::State& state) {
    const auto kp = mlkem::keygen<P>(vole_mole::test::filled<mlkem::SEED_BYTES>(0));
    const auto proof = mlkem_pop::detail::prove_with_seed<P>(kp.dk, CONTEXT, seed_from_counter(0));
    for (auto _ : state) {
        bool ok = mlkem_pop::verify<P>(kp.ek, CONTEXT, proof);
        benchmark::DoNotOptimize(ok);
        if (!ok) {
            state.SkipWithError("proof failed to verify");
            break;
        }
    }
}
BENCHMARK(BM_Verify<mlkem::MlKem512>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Verify<mlkem::MlKem768>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Verify<mlkem::MlKem1024>)->Unit(benchmark::kMillisecond);

} // namespace
