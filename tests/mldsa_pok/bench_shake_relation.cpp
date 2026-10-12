#include "mldsa_pok/shake_relation.hpp" // internal
#include "voleith.hpp"                  // internal

#include <benchmark/benchmark.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <string>
#include <vector>

using namespace vole_mole::mldsa_pok::detail;
using vole_mole::detail::PROOF_BYTES;
using vole_mole::detail::ProveSeed;
using vole_mole::detail::voleith_prove;
using vole_mole::detail::voleith_verify;
using vole_mole::detail::WITNESS_BYTES;

namespace {

template <typename R> struct Setup {
    using S = typename R::shape;
    typename R::instance x{};
    std::vector<uint8_t> witness;
    std::vector<uint8_t> proof = std::vector<uint8_t>(PROOF_BYTES<R>);
    Setup() {
        std::array<uint8_t, S::SECRET_BYTES> s{};
        for (size_t i = 0; i < s.size(); ++i) {
            s[i] = static_cast<uint8_t>(i);
        }
        witness = S::encode_witness(x.prefix, s, x.y);
    }
    void prove() {
        voleith_prove<R>(std::span<uint8_t, PROOF_BYTES<R>>(proof),
                         std::span<const uint8_t, WITNESS_BYTES<R>>(witness), x, ProveSeed<R>{});
    }
};

template <typename R> void BM_Prove(benchmark::State& state) {
    Setup<R> s;
    for (auto _ : state) {
        s.prove();
        benchmark::DoNotOptimize(s.proof);
    }
    state.SetLabel(std::to_string(PROOF_BYTES<R>) + "-byte proof");
}

template <typename R> void BM_Verify(benchmark::State& state) {
    Setup<R> s;
    s.prove();
    for (auto _ : state) {
        bool ok = voleith_verify<R>(std::span<const uint8_t, PROOF_BYTES<R>>(s.proof), s.x);
        benchmark::DoNotOptimize(ok);
        if (!ok) {
            state.SkipWithError("proof failed to verify");
            break;
        }
    }
}

using Deg9F = ShakeRelation<CtildeDeg9, Params128f<OWF_CTILDE_DEG9>>;
using Deg16F = ShakeRelation<CtildeDeg16, Params128f<OWF_CTILDE_DEG16>>;
using Deg9S = ShakeRelation<CtildeDeg9, Params128s<OWF_CTILDE_DEG9>>;
using Deg16S = ShakeRelation<CtildeDeg16, Params128s<OWF_CTILDE_DEG16>>;

BENCHMARK(BM_Prove<Deg9F>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Prove<Deg16F>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Prove<Deg9S>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Prove<Deg16S>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Verify<Deg9F>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Verify<Deg16F>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Verify<Deg9S>)->Unit(benchmark::kMillisecond);
BENCHMARK(BM_Verify<Deg16S>)->Unit(benchmark::kMillisecond);

} // namespace
