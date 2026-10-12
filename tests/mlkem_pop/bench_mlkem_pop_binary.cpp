// Benchmarks for the prototype of the ML-KEM proof of possession in binary VOLEitH (binary.hpp).

#include "vole_mole/mlkem.hpp"

#include "mlkem_pop/binary.hpp" // internal

#include "test.hpp"

#include <benchmark/benchmark.h>

#include <cstddef>
#include <cstdint>
#include <string>

using namespace vole_mole;
using namespace vole_mole::mlkem_pop::binary;

namespace {

const auto CONTEXT = vole_mole::test::filled<32>(0x10);

Rho seed_from_counter(uint64_t i) {
    Rho seed{};
    for (size_t j = 0; j < sizeof(i); ++j) {
        seed[j] = static_cast<uint8_t>(i >> (8 * j));
    }
    return seed;
}

template <mlkem::ParamSet P> void BM_Prove(benchmark::State& state) {
    const auto kp = mlkem::keygen<P>(vole_mole::test::filled<mlkem::SEED_BYTES>(0));
    uint64_t i = 0;
    for (auto _ : state) {
        auto proof = prove<P, true>(kp.dk, CONTEXT, seed_from_counter(i++));
        benchmark::DoNotOptimize(proof);
    }
    state.SetLabel(std::to_string(PROOF_BYTES<P, true>) + "-byte proof");
}
BENCHMARK(BM_Prove<mlkem::MlKem512>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Prove<mlkem::MlKem768>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Prove<mlkem::MlKem1024>)->Unit(benchmark::kMillisecond);

template <mlkem::ParamSet P> void BM_Verify(benchmark::State& state) {
    const auto kp = mlkem::keygen<P>(vole_mole::test::filled<mlkem::SEED_BYTES>(0));
    const auto proof = prove<P, true>(kp.dk, CONTEXT, seed_from_counter(0));
    for (auto _ : state) {
        benchmark::DoNotOptimize(verify<P, true>(kp.ek, CONTEXT, proof));
    }
}
BENCHMARK(BM_Verify<mlkem::MlKem512>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Verify<mlkem::MlKem768>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Verify<mlkem::MlKem1024>)->Unit(benchmark::kMillisecond);

} // namespace
