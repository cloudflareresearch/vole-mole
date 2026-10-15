#include "vole_mole/mldsa.hpp"
#include "vole_mole/mldsa_pok.hpp"

#include <benchmark/benchmark.h>

#include <cstdint>
#include <string>

using namespace vole_mole;

namespace {

struct Setup {
    mldsa::KeyPair<mldsa::MlDsa44> kp = mldsa::keygen<mldsa::MlDsa44>(mldsa::Seed{});
    mldsa_pok::Message msg{1, 2, 3};
    mldsa::Signature<mldsa::MlDsa44> sig =
        mldsa::sign<mldsa::MlDsa44>(kp.sk, msg, {}, mldsa::Rnd{});
};

void BM_Prove(benchmark::State& state) {
    const Setup s;
    for (auto _ : state) {
        auto proof = mldsa_pok::prove(s.kp.pk, s.msg, s.sig);
        benchmark::DoNotOptimize(proof);
    }
    state.SetLabel(std::to_string(mldsa_pok::PROOF_BYTES) + "-byte proof");
}
BENCHMARK(BM_Prove)->Unit(benchmark::kMillisecond);

void BM_Verify(benchmark::State& state) {
    const Setup s;
    const auto proof = mldsa_pok::prove(s.kp.pk, s.msg, s.sig);
    for (auto _ : state) {
        bool ok = mldsa_pok::verify(s.kp.pk, proof);
        benchmark::DoNotOptimize(ok);
        if (!ok) {
            state.SkipWithError("proof failed to verify");
            break;
        }
    }
}
BENCHMARK(BM_Verify)->Unit(benchmark::kMillisecond);

} // namespace
