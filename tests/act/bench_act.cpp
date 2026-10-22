#include "vole_mole/act.hpp"

#include "act/seeded.hpp" // internal
#include "act/token.hpp"  // internal: TokenAccess

#include "test.hpp"

#include <benchmark/benchmark.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>

using namespace vole_mole;
using namespace vole_mole::act;
using vole_mole::act::detail::issue_request_with_seed;
using vole_mole::act::detail::Seed;
using vole_mole::act::detail::spend_request_with_seed;
using vole_mole::act::detail::TokenAccess;
using vole_mole::test::uov_key_pair;

namespace {

const Context CTX_ISS = vole_mole::test::filled<CTX_BYTES>(0x10);
constexpr Credits T_INIT = 1000;
constexpr Credits D = 1;

// A different seed per iteration, so that every run proves a fresh statement.
Seed seed_from_counter(uint64_t i) {
    Seed seed{};
    for (size_t j = 0; j < sizeof(i); ++j) {
        seed[j] = static_cast<uint8_t>(i >> (8 * j));
    }
    return seed;
}

// A token issued by the fixed test key pair.
const Token& token() {
    static const Token t = [] {
        const auto& [pk, sk] = uov_key_pair();
        auto [pending, request] = issue_request_with_seed(T_INIT, CTX_ISS, Seed{});
        return *std::move(pending).finalize_issue(pk,
                                                  *issue_response(sk, request, T_INIT, CTX_ISS));
    }();
    return t;
}

// Spending consumes a token, so each spend spends a copy. (Copying is negligible compared to proof
// generation.)
Token copy(const Token& t) { return TokenAccess::copy(t); }

void BM_IssueRequest(benchmark::State& state) {
    uint64_t i = 0;
    for (auto _ : state) {
        auto res = issue_request_with_seed(T_INIT, CTX_ISS, seed_from_counter(i++));
        benchmark::DoNotOptimize(res);
    }
    state.SetLabel(std::to_string(ISSUE_PROOF_BYTES) + "-byte proof");
}
BENCHMARK(BM_IssueRequest)->Unit(benchmark::kMillisecond);

// Verify the issuance proof and sign the tag.
void BM_IssueResponse(benchmark::State& state) {
    const auto& [pk, sk] = uov_key_pair();
    const auto res = issue_request_with_seed(T_INIT, CTX_ISS, seed_from_counter(0));
    for (auto _ : state) {
        auto response = issue_response(sk, res.request, T_INIT, CTX_ISS);
        benchmark::DoNotOptimize(response);
        if (!response) {
            state.SkipWithError("proof failed to verify");
            break;
        }
    }
}
BENCHMARK(BM_IssueResponse)->Unit(benchmark::kMillisecond);

void BM_FinalizeIssue(benchmark::State& state) {
    const auto& [pk, sk] = uov_key_pair();
    const auto [pending, request] = issue_request_with_seed(T_INIT, CTX_ISS, seed_from_counter(0));
    const auto response = *issue_response(sk, request, T_INIT, CTX_ISS);
    for (auto _ : state) {
        auto t = TokenAccess::copy(pending).finalize_issue(pk, response);
        benchmark::DoNotOptimize(t);
    }
}
BENCHMARK(BM_FinalizeIssue)->Unit(benchmark::kMillisecond);

void BM_SpendRequest(benchmark::State& state) {
    const auto& pk = uov_key_pair().pk;
    uint64_t i = 0;
    for (auto _ : state) {
        auto res = spend_request_with_seed(copy(token()), pk, D, CTX_ISS, seed_from_counter(i++));
        benchmark::DoNotOptimize(res);
    }
    state.SetLabel(std::to_string(SPEND_PROOF_BYTES) + "-byte proof");
}
BENCHMARK(BM_SpendRequest)->Unit(benchmark::kMillisecond);

// Verify the spend proof and sign the updated state.
void BM_SpendResponse(benchmark::State& state) {
    const auto& [pk, sk] = uov_key_pair();
    const auto res = spend_request_with_seed(copy(token()), pk, D, CTX_ISS, seed_from_counter(0));
    for (auto _ : state) {
        auto response = spend_response(sk, res.request, CTX_ISS, 0);
        benchmark::DoNotOptimize(response);
        if (!response) {
            state.SkipWithError("proof failed to verify");
            break;
        }
    }
}
BENCHMARK(BM_SpendResponse)->Unit(benchmark::kMillisecond);

void BM_FinalizeSpend(benchmark::State& state) {
    const auto& [pk, sk] = uov_key_pair();
    const auto res = spend_request_with_seed(copy(token()), pk, D, CTX_ISS, seed_from_counter(0));
    const auto response = spend_response(sk, res.request, CTX_ISS, 0)->response;
    for (auto _ : state) {
        auto t = TokenAccess::copy(res.pending_spend).finalize_spend(pk, response);
        benchmark::DoNotOptimize(t);
    }
}
BENCHMARK(BM_FinalizeSpend)->Unit(benchmark::kMillisecond);

} // namespace
