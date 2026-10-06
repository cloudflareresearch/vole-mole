#include "test.hpp"
#include "vole_mole/moussaka.hpp"

#include "moussaka/seeded.hpp" // internal
#include "moussaka/token.hpp"  // internal: TokenAccess

#include <benchmark/benchmark.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

using namespace vole_mole;
using namespace vole_mole::moussaka;
using vole_mole::moussaka::detail::issue_request_with_seed;
using vole_mole::moussaka::detail::redeem_request_with_seed;
using vole_mole::moussaka::detail::Seed;
using vole_mole::moussaka::detail::TokenAccess;
using vole_mole::test::uov_key_pair;

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

// A token issued by the fixed test key pair.
const Token& token() {
    static const Token t = [] {
        const auto& [pk, sk] = uov_key_pair();
        auto [pending, request] = issue_request_with_seed(CTX_ISS, CTX_RED, Seed{});
        return *std::move(pending).finalize_issue(pk, *issue_response(sk, request, CTX_ISS));
    }();
    return t;
}

// Redemption consumes a token, so each redemption redeems a copy. (Copying is negligible compared
// to proof generation.)
Token copy(const Token& t) { return TokenAccess::copy(t); }

// An Anchor Set of size n, with the issuer of `token()` last.
AnchorSet anchor_set(size_t n) {
    std::vector<AnchorRef> keys;
    for (size_t u = 0; u + 1 < n; ++u) {
        keys.emplace_back(vole_mole::test::distinct_uov_public_key(u));
    }
    keys.emplace_back(uov_key_pair().pk);
    return AnchorSet(keys);
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

// Verify the issuance proof and sign the commitment.
void BM_IssueResponse(benchmark::State& state) {
    const auto& [pk, sk] = uov_key_pair();
    const auto res = issue_request_with_seed(CTX_ISS, CTX_RED, seed_from_counter(0));
    for (auto _ : state) {
        auto response = issue_response(sk, res.request, CTX_ISS);
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
    const auto [pending, request] = issue_request_with_seed(CTX_ISS, CTX_RED, seed_from_counter(0));
    const auto response = *issue_response(sk, request, CTX_ISS);
    for (auto _ : state) {
        // Finalization consumes the pending token, so finalize a copy. (Copying is negligible
        // compared to evaluating the public map.)
        auto t = TokenAccess::copy(pending).finalize_issue(pk, response);
        benchmark::DoNotOptimize(t);
    }
}
BENCHMARK(BM_FinalizeIssue)->Unit(benchmark::kMillisecond);

// Argument: size of the Anchor Set.
void BM_RedeemRequest(benchmark::State& state) {
    const auto keys = anchor_set(static_cast<size_t>(state.range(0)));
    uint64_t i = 0;
    for (auto _ : state) {
        auto req = redeem_request_with_seed(copy(token()), keys, keys.size() - 1, CTX_ISS, CTX_RED,
                                            seed_from_counter(i++));
        benchmark::DoNotOptimize(req);
    }
    state.SetLabel(std::to_string(REDEEM_PROOF_BYTES) + "-byte proof");
}
BENCHMARK(BM_RedeemRequest)->Arg(1)->Arg(8)->Arg(MAX_ANCHORS)->Unit(benchmark::kMillisecond);

// Argument: size of the Anchor Set.
void BM_FinalizeRedeem(benchmark::State& state) {
    const auto keys = anchor_set(static_cast<size_t>(state.range(0)));
    const auto req = redeem_request_with_seed(copy(token()), keys, keys.size() - 1, CTX_ISS,
                                              CTX_RED, seed_from_counter(0));
    for (auto _ : state) {
        auto nf = finalize_redeem(keys, req, CTX_ISS, CTX_RED);
        benchmark::DoNotOptimize(nf);
        if (!nf) {
            state.SkipWithError("proof failed to verify");
            break;
        }
    }
}
BENCHMARK(BM_FinalizeRedeem)->Arg(1)->Arg(8)->Arg(MAX_ANCHORS)->Unit(benchmark::kMillisecond);

} // namespace
