#include "vole_mole/uov.hpp"

#include "qs_gf256.hpp"    // internal
#include "uov/circuit.hpp" // internal

#include "test.hpp"

#include "constants.hpp"   // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

#include <benchmark/benchmark.h>

#include <array>
#include <cstdint>
#include <vector>

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

// Evaluation of the public map circuit on a committed preimage, as in the redemption proofs. (The
// VOLE tags are zero, which doesn't affect the running time.)
constexpr auto S = faest::secpar::s128;
using ProverQS = faest::quicksilver_state<S, false, 2>;
using VerifierQS = faest::quicksilver_state<S, true, 2>;

// Evaluate with `eval`, on s loaded as `Value`s with `load`.
template <typename Value, typename QS, typename Load, typename Eval>
void bench_circuit_eval(benchmark::State& state, const QS& qs, Load load, Eval eval) {
    const uov::PublicKey& pk = test::uov_key_pair().pk;
    std::array<Value, uov::N> s;
    for (size_t i = 0; i < uov::N; ++i) {
        s[i] = load(qs, 8 * i);
    }
    for (auto _ : state) {
        auto p = eval(pk, std::span<const Value, uov::N>(s));
        benchmark::DoNotOptimize(p);
    }
}

template <typename QS> auto load_gf256(const QS& qs, size_t i) {
    return vole_mole::detail::qs_load_gf256(&qs, i);
}
template <typename QS> auto load_gfsecpar(const QS& qs, size_t i) {
    return qs.load_witness_8_bits_and_combine(i);
}

struct CircuitFixture {
    uov::Preimage preimage = test::uov_key_pair().sk.derive_preimage(target_from_counter(0));
    std::vector<faest::block_secpar<S>> macs = std::vector<faest::block_secpar<S>>(8 * uov::N);
    std::array<uint8_t, faest::QS_CONSTANTS<S, 2>::CHALLENGE_BYTES> challenge{};
};

void BM_UovCircuitEvalProver(benchmark::State& state) {
    CircuitFixture f;
    const ProverQS qs(f.preimage.data(), f.macs.data(), uov::M, f.challenge.data());
    bench_circuit_eval<vole_mole::detail::qs_gf256<ProverQS, 1>>(
        state, qs, load_gf256<ProverQS>, uov::detail::qs_eval_public_map<ProverQS>);
}
BENCHMARK(BM_UovCircuitEvalProver)->Unit(benchmark::kMicrosecond);

void BM_UovCircuitEvalProverGeneric(benchmark::State& state) {
    CircuitFixture f;
    const ProverQS qs(f.preimage.data(), f.macs.data(), uov::M, f.challenge.data());
    bench_circuit_eval<uov::detail::qs_val<ProverQS, 1>>(
        state, qs, load_gfsecpar<ProverQS>, uov::detail::qs_eval_public_map_generic<ProverQS>);
}
BENCHMARK(BM_UovCircuitEvalProverGeneric)->Unit(benchmark::kMicrosecond);

void BM_UovCircuitEvalVerifier(benchmark::State& state) {
    CircuitFixture f;
    const VerifierQS qs(f.macs.data(), uov::M, faest::block_secpar<S>{}, f.challenge.data());
    bench_circuit_eval<vole_mole::detail::qs_gf256<VerifierQS, 1>>(
        state, qs, load_gf256<VerifierQS>, uov::detail::qs_eval_public_map<VerifierQS>);
}
BENCHMARK(BM_UovCircuitEvalVerifier)->Unit(benchmark::kMicrosecond);

} // namespace
