// Benchmarks of the experimental hidden-key ECDSA proof (src/ecdsa_pok/hk_relation.hpp).

#include "vole_mole/ecdsa_pok.hpp"

#include "ecdsa_pok/hk_arith.hpp"    // internal
#include "ecdsa_pok/hk_relation.hpp" // internal
#include "p256/curve.hpp"            // internal
#include "p256/field.hpp"            // internal

#include <benchmark/benchmark.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <vector>

using namespace vole_mole::ecdsa_pok;
namespace hk = vole_mole::ecdsa_pok::detail::hk;
namespace p256 = vole_mole::p256;

namespace {

struct Fixture {
    PublicKey pk;
    std::vector<uint8_t> msg;
    Signature sig;
};

Fixture fixture() {
    const p256::Fn d = p256::Fn::from_u64(0x1234567890abcdefULL) * p256::Fn::from_u64(77);
    const p256::Fn k = p256::Fn::from_u64(0xfedcba0987654321ULL) * p256::Fn::from_u64(99);
    Fixture f;
    f.pk = p256::encode_point(p256::scalar_mul(p256::GENERATOR, d.canonical()).to_affine());
    f.msg.assign(100, 0x42); // e.g., an mdoc session transcript (public)
    const auto sig = *p256::ecdsa_sign_with_nonce(d, k, f.msg);
    std::copy(sig.r.begin(), sig.r.end(), f.sig.begin());
    std::copy(sig.s.begin(), sig.s.end(), f.sig.begin() + 32);
    return f;
}

const std::vector<uint8_t> CTX = {'c', 't', 'x'};

// Args: Vole, WitnessPrg.
Params params_of(const benchmark::State& state) {
    return {static_cast<Vole>(state.range(0)), static_cast<WitnessPrg>(state.range(1))};
}

constexpr auto args = [](auto* b) {
    for (const int64_t vole : {0, 1, 2}) {
        for (const int64_t prg : {0, 1, 2}) {
            b->Args({vole, prg});
        }
    }
};

void BM_HkProve(benchmark::State& state) {
    const auto f = fixture();
    const auto params = params_of(state);
    (void)hk::comb_tables(); // static, computed once per process
    for (auto _ : state) {
        auto proof = hk::prove(f.pk, f.msg, f.sig, CTX, params);
        benchmark::DoNotOptimize(proof);
    }
    state.counters["bytes"] = static_cast<double>(hk::proof_bytes(params));
}
BENCHMARK(BM_HkProve)->Apply(args)->Unit(benchmark::kMillisecond);

void BM_HkVerify(benchmark::State& state) {
    const auto f = fixture();
    const auto params = params_of(state);
    const auto proof = hk::prove(f.pk, f.msg, f.sig, CTX, params);
    for (auto _ : state) {
        bool ok = hk::verify(f.msg, CTX, proof, params);
        benchmark::DoNotOptimize(ok);
    }
}
BENCHMARK(BM_HkVerify)->Apply(args)->Unit(benchmark::kMillisecond);

} // namespace
