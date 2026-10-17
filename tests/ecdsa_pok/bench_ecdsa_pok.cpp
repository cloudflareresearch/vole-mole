#include "vole_mole/ecdsa_pok.hpp"

#include "ecdsa_pok/arith.hpp" // internal
#include "p256/curve.hpp"      // internal
#include "p256/field.hpp"      // internal

#include <benchmark/benchmark.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <vector>

using namespace vole_mole::ecdsa_pok;
namespace p256 = vole_mole::p256;

namespace {

struct Fixture {
    PublicKey pk;
    std::vector<uint8_t> msg;
    Signature sig;
};

Fixture fixture(size_t msg_len) {
    const p256::Fn d = p256::Fn::from_u64(0x1234567890abcdefULL) * p256::Fn::from_u64(77);
    const p256::Fn k = p256::Fn::from_u64(0xfedcba0987654321ULL) * p256::Fn::from_u64(99);
    Fixture f;
    f.pk = p256::encode_point(p256::scalar_mul(p256::GENERATOR, d.canonical()).to_affine());
    f.msg.assign(msg_len, 0x42);
    const auto sig = *p256::ecdsa_sign_with_nonce(d, k, f.msg);
    std::copy(sig.r.begin(), sig.r.end(), f.sig.begin());
    std::copy(sig.s.begin(), sig.s.end(), f.sig.begin() + 32);
    return f;
}

const std::vector<uint8_t> CTX = {'c', 't', 'x'};

// Args: message length, Vole, WitnessPrg.
Params params_of(const benchmark::State& state) {
    return {static_cast<Vole>(state.range(1)), static_cast<WitnessPrg>(state.range(2))};
}

// Generic, since the benchmark class is benchmark::internal::Benchmark before Google Benchmark 1.9
// and benchmark::Benchmark (with the former deprecated) after.
constexpr auto args = [](auto* b) {
    for (const int64_t len : {32, 100}) {
        for (const int64_t vole : {0, 1, 2}) {
            for (const int64_t prg : {0, 1, 2}) {
                b->Args({len, vole, prg});
            }
        }
    }
};

void BM_Prove(benchmark::State& state) {
    const auto f = fixture(static_cast<size_t>(state.range(0)));
    const auto params = params_of(state);
    for (auto _ : state) {
        auto proof = prove(f.pk, f.msg, f.sig, CTX, params);
        benchmark::DoNotOptimize(proof);
    }
    state.counters["bytes"] = static_cast<double>(proof_bytes(f.msg.size(), params));
}
BENCHMARK(BM_Prove)->Apply(args)->Unit(benchmark::kMillisecond);

void BM_Verify(benchmark::State& state) {
    const auto f = fixture(static_cast<size_t>(state.range(0)));
    const auto params = params_of(state);
    const auto proof = prove(f.pk, f.msg, f.sig, CTX, params);
    for (auto _ : state) {
        bool ok = verify(f.pk, f.msg.size(), CTX, proof, params);
        benchmark::DoNotOptimize(ok);
    }
}
BENCHMARK(BM_Verify)->Apply(args)->Unit(benchmark::kMillisecond);

// The comb tables for a public key, which both the prover and verifier compute.
void BM_Tables(benchmark::State& state) {
    const auto f = fixture(32);
    const auto q = *p256::decode_point(f.pk);
    for (auto _ : state) {
        auto t = vole_mole::ecdsa_pok::detail::make_tables(q);
        benchmark::DoNotOptimize(t);
    }
}
BENCHMARK(BM_Tables)->Unit(benchmark::kMillisecond);

} // namespace
