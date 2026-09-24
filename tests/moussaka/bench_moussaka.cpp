// Benchmarks of the issuance proof: IssueRequest() (commit + prove) and its verification.
//
// Run in a release build, so that assertions are disabled:
//
//   meson setup build-release --buildtype=release
//   meson test -C build-release --benchmark -v
//
// or run the executable directly to pass Google Benchmark flags, e.g.:
//
//   ./build-release/tests/bench_moussaka --benchmark_repetitions=10
//       --benchmark_report_aggregates_only=true

#include "test.hpp"
#include "vole_mole/moussaka.hpp"

#include "moussaka/issue.hpp" // internal: verify_issue_request

#include <benchmark/benchmark.h>

#include <cstdint>
#include <string>

using namespace vole_mole::moussaka;
using vole_mole::moussaka::detail::verify_issue_request;

namespace {

const Context CTX_ISS = vole_mole::test::filled<CTX_BYTES>(0x10);
const Context CTX_RED = vole_mole::test::filled<CTX_BYTES>(0x20);

// A different seed per iteration, so that every run proves a fresh statement.
Seed seed_from_counter(uint64_t i) {
    Seed seed{};
    for (size_t j = 0; j < sizeof(i); ++j) {
        seed[j] = static_cast<uint8_t>(i >> (8 * j));
    }
    return seed;
}

void BM_IssueRequest(benchmark::State& state) {
    uint64_t i = 0;
    for (auto _ : state) {
        auto res = issue_request_with_seed(CTX_ISS, CTX_RED, seed_from_counter(i++));
        benchmark::DoNotOptimize(res);
    }
    state.SetLabel(std::to_string(ISSUE_PROOF_BYTES) + "-byte proof");
}
BENCHMARK(BM_IssueRequest)->Unit(benchmark::kMillisecond);

void BM_VerifyIssueRequest(benchmark::State& state) {
    const auto res = issue_request_with_seed(CTX_ISS, CTX_RED, seed_from_counter(0));
    for (auto _ : state) {
        bool ok = verify_issue_request(res.request, CTX_ISS);
        benchmark::DoNotOptimize(ok);
        if (!ok) {
            state.SkipWithError("proof failed to verify");
            break;
        }
    }
}
BENCHMARK(BM_VerifyIssueRequest)->Unit(benchmark::kMillisecond);

} // namespace
