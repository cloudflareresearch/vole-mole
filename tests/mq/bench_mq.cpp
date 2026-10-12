// Benchmarks for the MQ PRG, at the parameters of the Moussaka issuance relation.

#include "mq/prg.hpp" // internal

#include "test.hpp"

#include "block.hpp"       // from faest-arch-opt
#include "parameters.hpp"  // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

#include <benchmark/benchmark.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <span>
#include <vector>

using namespace vole_mole::mq::detail;
using vole_mole::test::filled;
using vole_mole::test::PlainQS;

namespace {

constexpr size_t NUM_OUTPUTS = 2048;
constexpr size_t KEY_BITS = key_bits(NUM_OUTPUTS);
using Map = PublicMap<KEY_BITS, NUM_OUTPUTS>;

const Map& map() {
    static const Map m(filled<7>(0));
    return m;
}

// Generating all coefficient matrices.
void BM_Coefficients(benchmark::State& state) {
    auto m = std::make_unique<Map::Matrix>();
    for (auto _ : state) {
        for (size_t i = 0; i < NUM_OUTPUTS; ++i) {
            map().matrix(i, *m);
            benchmark::DoNotOptimize(m->data());
        }
    }
    state.SetBytesProcessed(static_cast<int64_t>(state.iterations() * NUM_OUTPUTS * sizeof(*m)));
}
BENCHMARK(BM_Coefficients)->Unit(benchmark::kMillisecond);

void BM_PlainEval(benchmark::State& state) {
    const auto key = filled<KEY_BITS / 8>(0x42);
    std::array<uint8_t, NUM_OUTPUTS / 8> out;
    for (auto _ : state) {
        eval(map(), std::span(key), std::span(out));
        benchmark::DoNotOptimize(out.data());
    }
}
BENCHMARK(BM_PlainEval)->Unit(benchmark::kMillisecond);

// Evaluation on plaintext stand-ins for committed values, i.e., the cost of the circuit structure
// without the QuickSilver arithmetic.
void BM_CircuitEvalPlain(benchmark::State& state) {
    using qs_1 = faest::quicksilver_gf2<PlainQS, 1>;
    const auto key = filled<KEY_BITS / 8>(0x42);
    const auto e = filled<NUM_OUTPUTS / 8>(0x17);
    std::vector<qs_1> committed;
    for (size_t i = 0; i < KEY_BITS; ++i) {
        committed.emplace_back(((key[i / 8] >> (i % 8)) & 1) != 0);
    }
    for (auto _ : state) {
        auto w = qs_eval<PlainQS>(map(), std::span<const qs_1, KEY_BITS>(committed), std::span(e));
        benchmark::DoNotOptimize(w.data());
    }
}
BENCHMARK(BM_CircuitEvalPlain)->Unit(benchmark::kMillisecond);

// Committed evaluation with faest-arch-opt's QuickSilver (see qs_eval_fast), for the prover and the
// verifier.
template <bool verifier> void BM_CircuitEval(benchmark::State& state) {
    using QS = faest::quicksilver_state<faest::secpar::s128, verifier, 18>;
    const auto key = filled<KEY_BITS / 8>(0x42);
    const auto e = filled<NUM_OUTPUTS / 8>(0x17);
    const std::vector<uint8_t> challenge(1024, 0x77);
    std::vector<faest::block128> macs(KEY_BITS);
    for (size_t j = 0; j < KEY_BITS; ++j) {
        const auto bytes = filled<16>(static_cast<uint8_t>(3 * j + 1));
        macs[j] = faest::block128::load(bytes.data());
    }
    const auto qs = [&] {
        if constexpr (verifier) {
            return QS(macs.data(), 1, macs[0], challenge.data());
        } else {
            return QS(key.data(), macs.data(), 1, challenge.data());
        }
    }();
    std::vector<faest::quicksilver_gf2<QS, 1>> committed;
    for (size_t j = 0; j < KEY_BITS; ++j) {
        committed.push_back(qs.get_witness_bit(j));
    }
    for (auto _ : state) {
        auto w =
            qs_eval<QS>(map(), std::span<const faest::quicksilver_gf2<QS, 1>, KEY_BITS>(committed),
                        std::span(e));
        benchmark::DoNotOptimize(w.data());
    }
}
BENCHMARK(BM_CircuitEval<false>)->Name("BM_CircuitEvalProver")->Unit(benchmark::kMillisecond);
BENCHMARK(BM_CircuitEval<true>)->Name("BM_CircuitEvalVerifier")->Unit(benchmark::kMillisecond);

} // namespace
