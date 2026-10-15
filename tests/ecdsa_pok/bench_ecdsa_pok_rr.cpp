// Benchmarks of the experimental ECDSA proof with a hidden key and a revealed R
// (src/ecdsa_pok/rr_relation.hpp).

#include "vole_mole/ecdsa_pok.hpp"

#include "ecdsa_pok/rr_relation.hpp" // internal
#include "p256/curve.hpp"            // internal
#include "p256/field.hpp"            // internal

#include <benchmark/benchmark.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <vector>

using namespace vole_mole::ecdsa_pok;
namespace rr = vole_mole::ecdsa_pok::detail::rr;
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

void BM_RrProve(benchmark::State& state) {
    const auto f = fixture();
    const auto params = params_of(state);
    for (auto _ : state) {
        auto proof = rr::prove(f.pk, f.msg, f.sig, CTX, params);
        benchmark::DoNotOptimize(proof);
    }
    state.counters["bytes"] = static_cast<double>(rr::proof_bytes(params));
}
BENCHMARK(BM_RrProve)->Apply(args)->Unit(benchmark::kMillisecond);

void BM_RrVerify(benchmark::State& state) {
    const auto f = fixture();
    const auto params = params_of(state);
    const auto proof = rr::prove(f.pk, f.msg, f.sig, CTX, params);
    for (auto _ : state) {
        bool ok = rr::verify(f.msg, CTX, proof, params);
        benchmark::DoNotOptimize(ok);
    }
}
BENCHMARK(BM_RrVerify)->Apply(args)->Unit(benchmark::kMillisecond);

// The per-proof public values (T, U, the offsets, and the comb tables of T), which both the prover
// and the verifier compute.
void BM_RrPublic(benchmark::State& state) {
    const auto f = fixture();
    const auto proof = rr::prove(f.pk, f.msg, f.sig, CTX);
    for (auto _ : state) {
        auto pub = rr::make_public(f.msg, CTX,
                                   std::span<const uint8_t, rr::R_BYTES>(proof.data(), rr::R_BYTES),
                                   Vole::fast, vole_mole::ecdsa_pok::detail::BinPrg::local);
        benchmark::DoNotOptimize(pub);
    }
}
BENCHMARK(BM_RrPublic)->Unit(benchmark::kMillisecond);

} // namespace
