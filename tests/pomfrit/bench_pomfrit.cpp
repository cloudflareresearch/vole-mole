#include "vole_mole/pomfrit.hpp"

#include "pomfrit/seeded.hpp" // internal

#include "test.hpp"

#include <benchmark/benchmark.h>

#include <cstdint>
#include <span>
#include <string>
#include <utility>

using namespace vole_mole;
using namespace vole_mole::pomfrit;
using vole_mole::pomfrit::detail::issue_request_with_seed;
using vole_mole::pomfrit::detail::Seed;
using vole_mole::test::uov_key_pair;

namespace {

const auto MSG = vole_mole::test::filled<32>(0x10);

// A different seed per iteration, so that every run proves a fresh statement.
Seed seed_from_counter(uint64_t i) {
    Seed seed{};
    for (size_t j = 0; j < sizeof(i); ++j) {
        seed[j] = static_cast<uint8_t>(i >> (8 * j));
    }
    return seed;
}

void BM_IssueRequest(benchmark::State& state) {
    const auto& [pk, sk] = uov_key_pair();
    uint64_t i = 0;
    for (auto _ : state) {
        auto res = issue_request_with_seed(pk, MSG, seed_from_counter(i++));
        benchmark::DoNotOptimize(res);
    }
}
BENCHMARK(BM_IssueRequest)->Unit(benchmark::kMillisecond);

void BM_IssueResponse(benchmark::State& state) {
    const auto& [pk, sk] = uov_key_pair();
    const auto [pending, request] = issue_request_with_seed(pk, MSG, seed_from_counter(0));
    for (auto _ : state) {
        auto response = issue_response(sk, request);
        benchmark::DoNotOptimize(response);
    }
}
BENCHMARK(BM_IssueResponse)->Unit(benchmark::kMillisecond);

void BM_FinalizeIssue(benchmark::State& state) {
    const auto& [pk, sk] = uov_key_pair();
    uint64_t i = 0;
    for (auto _ : state) {
        state.PauseTiming();
        auto [pending, request] = issue_request_with_seed(pk, MSG, seed_from_counter(i++));
        const auto response = issue_response(sk, request);
        state.ResumeTiming();
        auto sig = std::move(pending).finalize_issue(pk, response);
        benchmark::DoNotOptimize(sig);
    }
    state.SetLabel(std::to_string(SIGNATURE_BYTES) + "-byte signature");
}
BENCHMARK(BM_FinalizeIssue)->Unit(benchmark::kMillisecond);

void BM_Verify(benchmark::State& state) {
    const auto& [pk, sk] = uov_key_pair();
    auto [pending, request] = issue_request_with_seed(pk, MSG, seed_from_counter(0));
    const auto sig = *std::move(pending).finalize_issue(pk, issue_response(sk, request));
    for (auto _ : state) {
        bool ok = verify(pk, MSG, sig);
        benchmark::DoNotOptimize(ok);
        if (!ok) {
            state.SkipWithError("signature failed to verify");
            break;
        }
    }
}
BENCHMARK(BM_Verify)->Unit(benchmark::kMillisecond);

} // namespace
