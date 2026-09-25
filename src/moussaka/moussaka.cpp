#include "vole_mole/moussaka.hpp"

#include "dst.hpp"
#include "moussaka/issue.hpp"

extern "C" {
#include "randomness.h" // from faest-arch-opt
}

#include <stdexcept>

namespace vole_mole::moussaka {

using detail::IssueRelation;

namespace {

using namespace vole_mole::detail;

struct IssueRandomness {
    Nullifier nf;
    Opening r;
    std::array<uint8_t, 32> rho;
};

// Expand `seed` into the issue request randomness.
IssueRandomness expand_seed(const Seed& seed) {
    static_assert(IssueRelation::params::secpar_v == faest::secpar::s128);
    faest::hash_state xof;
    xof.init(faest::secpar::s128);
    xof.update(MOUSSAKA_ISSUE_SEED_DST);
    xof.update(seed);

    IssueRandomness rand;
    Keccak_HashFinal(&xof.ctx, nullptr);
    Keccak_HashSqueeze(&xof.ctx, rand.nf.data(), 8 * rand.nf.size());
    Keccak_HashSqueeze(&xof.ctx, rand.r.data(), 8 * rand.r.size());
    Keccak_HashSqueeze(&xof.ctx, rand.rho.data(), 8 * rand.rho.size());
    return rand;
}

} // namespace

Commitment commit(const Nullifier& nf, const Context& ctx_iss, const Context& ctx_red,
                  const Opening& r) {
    const Kp800State out = keccak_p800(detail::encode_init_state(nf, ctx_iss, ctx_red, r));

    Commitment t;
    std::copy_n(out.begin(), t.size(), t.begin());
    return t;
}

IssueRequestResult issue_request_with_seed(const Context& ctx_iss, const Context& ctx_red,
                                           const Seed& seed) {
    const IssueRandomness rand = expand_seed(seed);

    IssueRequestResult result;
    result.pending_token = {rand.nf, rand.r};
    const Commitment t = commit(rand.nf, ctx_iss, ctx_red, rand.r);
    std::ranges::copy(t, std::span(result.request).first<uov::M>().begin());
    detail::prove_issue_request(std::span(result.request).last<ISSUE_PROOF_BYTES>(), t, rand.nf,
                                ctx_iss, ctx_red, rand.r, rand.rho);
    return result;
}

IssueRequestResult issue_request(const Context& ctx_iss, const Context& ctx_red) {
    Seed seed;
    if (rand_bytes(seed.data(), seed.size()) != 0) {
        throw std::runtime_error("failed to get randomness from the operating system");
    }

    return issue_request_with_seed(ctx_iss, ctx_red, seed);
}

} // namespace vole_mole::moussaka
