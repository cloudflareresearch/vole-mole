// Benchmarks of the experimental mdoc proof (src/ecdsa_pok/mdoc_relation.hpp), with mdocs from
// Longfellow's tests: vector 0 for 1 attribute, and vector 3 for 4.

#include "ecdsa_pok/mdoc_relation.hpp" // internal

#include "mdoc_vectors.hpp"

#include <benchmark/benchmark.h>

#include <cstdint>
#include <vector>

using namespace mdoc_vectors;
using vole_mole::ecdsa_pok::Params;
using vole_mole::ecdsa_pok::Vole;
using vole_mole::ecdsa_pok::WitnessPrg;

namespace {

struct Case {
    md::Request req;
    const std::vector<uint8_t>* mdoc;
};

Case case_of(const benchmark::State& state) {
    if (state.range(2) == 1) {
        return {request(0, {AGE_OVER_18}), &vectors().at(0).mdoc};
    }
    return {request(3, {FAMILY_NAME, BIRTH_DATE, HEIGHT, AGE_OVER_18}), &vectors().at(3).mdoc};
}

Params params_of(const benchmark::State& state) {
    return {static_cast<Vole>(state.range(0)), static_cast<WitnessPrg>(state.range(1))};
}

// Args: VOLE parameters, witness PRG (none, local), number of attributes.
constexpr auto args = [](auto* b) {
    for (const int64_t na : {1, 4}) {
        for (const int64_t vole : {0, 1, 2}) {
            for (const int64_t prg : {0, 1}) {
                b->Args({vole, prg, na});
            }
        }
    }
};

void BM_MdocProve(benchmark::State& state) {
    const auto c = case_of(state);
    const auto params = params_of(state);
    for (auto _ : state) {
        auto proof = md::prove(*c.mdoc, c.req, params);
        benchmark::DoNotOptimize(proof);
    }
    state.counters["bytes"] = static_cast<double>(md::proof_bytes(c.req.attributes.size(), params));
}
BENCHMARK(BM_MdocProve)->Apply(args)->Unit(benchmark::kMillisecond);

void BM_MdocVerify(benchmark::State& state) {
    const auto c = case_of(state);
    const auto params = params_of(state);
    const auto proof = md::prove(*c.mdoc, c.req, params);
    for (auto _ : state) {
        bool ok = md::verify(c.req, proof, params);
        benchmark::DoNotOptimize(ok);
    }
}
BENCHMARK(BM_MdocVerify)->Apply(args)->Unit(benchmark::kMillisecond);

} // namespace
