#include "vole_mole/uov.hpp"

#include "test.hpp"

#include <benchmark/benchmark.h>

#include <cstdint>

using namespace vole_mole;

namespace {

// A different target per iteration. Preimage derivation is deterministic, so this makes every
// iteration derive a fresh preimage.
uov::Target target_from_counter(uint64_t i) {
    uov::Target target = test::filled<uov::M>(0x10);
    for (size_t j = 0; j < sizeof(i); ++j) {
        target[j] = static_cast<uint8_t>(i >> (8 * j));
    }
    return target;
}

void BM_UovExpandSecretKey(benchmark::State& state) {
    for (auto _ : state) {
        uov::SecretKey sk(test::UOV_SK_BYTES);
        benchmark::DoNotOptimize(sk);
    }
}
BENCHMARK(BM_UovExpandSecretKey)->Unit(benchmark::kMicrosecond);

void BM_UovExpandPublicKey(benchmark::State& state) {
    const uov::PublicKeyBytes& bytes = test::uov_key_pair().sk.public_key();
    for (auto _ : state) {
        uov::PublicKey pk(bytes);
        benchmark::DoNotOptimize(pk);
    }
}
BENCHMARK(BM_UovExpandPublicKey)->Unit(benchmark::kMicrosecond);

void BM_UovDerivePreimage(benchmark::State& state) {
    const uov::SecretKey& sk = test::uov_key_pair().sk;
    uint64_t i = 0;
    for (auto _ : state) {
        auto preimage = sk.derive_preimage(target_from_counter(i++));
        benchmark::DoNotOptimize(preimage);
    }
}
BENCHMARK(BM_UovDerivePreimage)->Unit(benchmark::kMicrosecond);

void BM_UovEval(benchmark::State& state) {
    const uov::SecretKey& sk = test::uov_key_pair().sk;
    const uov::PublicKey& pk = test::uov_key_pair().pk;
    const uov::Target target = target_from_counter(0);
    const uov::Preimage preimage = sk.derive_preimage(target);
    for (auto _ : state) {
        auto t = pk.eval(preimage);
        benchmark::DoNotOptimize(t);
        if (t != target) {
            state.SkipWithError("preimage does not map to the target");
            break;
        }
    }
}
BENCHMARK(BM_UovEval)->Unit(benchmark::kMicrosecond);

} // namespace
