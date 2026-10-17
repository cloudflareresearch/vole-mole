#include "test.hpp"

#include "blindsig/blindsig.hpp"

#include <benchmark/benchmark.h>

#include <cstddef>
#include <cstdint>
#include <string>

using namespace vole_mole;
using namespace vole_mole::blindsig;
using vole_mole::test::uov_key_pair;

namespace {

const Nullifier NF = vole_mole::test::filled<moussaka::NF_BYTES>(0x30);
const Opening R = vole_mole::test::filled<R_BYTES>(0x40);

// A different seed per iteration, so that every run proves a fresh statement.
vole_mole::detail::ProveSeed<Relation> seed_from_counter(uint64_t i) {
    vole_mole::detail::ProveSeed<Relation> seed{};
    for (size_t j = 0; j < sizeof(i); ++j) {
        seed[j] = static_cast<uint8_t>(i >> (8 * j));
    }
    return seed;
}

const uov::Preimage& signature() {
    static const uov::Preimage s = uov_key_pair().sk.derive_preimage(commit(NF, R));
    return s;
}

// Client: commit to nf.
void BM_Commit(benchmark::State& state) {
    for (auto _ : state) {
        auto t = commit(NF, R);
        benchmark::DoNotOptimize(t);
    }
}
BENCHMARK(BM_Commit)->Unit(benchmark::kMicrosecond);

// Issuer: derive the preimage of the commitment.
void BM_DerivePreimage(benchmark::State& state) {
    const auto& [pk, sk] = uov_key_pair();
    const auto t = commit(NF, R);
    for (auto _ : state) {
        auto s = sk.derive_preimage(t);
        benchmark::DoNotOptimize(s);
    }
}
BENCHMARK(BM_DerivePreimage)->Unit(benchmark::kMicrosecond);

// Client: prove knowledge of (r, s) such that P(s) = Com(nf, r).
void BM_Prove(benchmark::State& state) {
    const auto& pk = uov_key_pair().pk;
    const auto& s = signature();
    uint64_t i = 0;
    Proof proof;
    for (auto _ : state) {
        prove(proof, pk, NF, R, s, seed_from_counter(i++));
        benchmark::DoNotOptimize(proof);
    }
    state.SetLabel(std::to_string(PROOF_BYTES) + "-byte proof");
}
BENCHMARK(BM_Prove)->Unit(benchmark::kMillisecond);

void BM_Verify(benchmark::State& state) {
    const auto& pk = uov_key_pair().pk;
    Proof proof;
    prove(proof, pk, NF, R, signature(), seed_from_counter(0));
    for (auto _ : state) {
        bool ok = verify(proof, pk, NF);
        benchmark::DoNotOptimize(ok);
        if (!ok) {
            state.SkipWithError("proof failed to verify");
            break;
        }
    }
    proof[PROOF_BYTES / 2] ^= 1;
    if (verify(proof, pk, NF)) {
        state.SkipWithError("tampered proof verified");
    }
}
BENCHMARK(BM_Verify)->Unit(benchmark::kMillisecond);

} // namespace
