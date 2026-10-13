#include "vole_mole/ecdsa_pok.hpp"

#include "ecdsa_pok/relation.hpp"
#include "p256/curve.hpp"
#include "sha256/sha256.hpp"
#include "vole_mole/random.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <utility>
#include <vector>

namespace vole_mole::ecdsa_pok {

namespace {

using namespace detail;

// Call f.template operator()<NB, SMALL>() for the message length and parameters.
template <typename F> auto dispatch(size_t msg_len, Params params, F&& f) {
    if (msg_len > MAX_MESSAGE_BYTES) {
        throw std::invalid_argument("ecdsa_pok: message too long");
    }
    static_assert(MAX_BLOCKS == 2);
    const size_t nb = sha256::num_blocks(msg_len);
    const bool small = params == Params::small;
    if (nb == 1) {
        return small ? f.template operator()<1, true>() : f.template operator()<1, false>();
    }
    return small ? f.template operator()<2, true>() : f.template operator()<2, false>();
}

} // namespace

size_t proof_bytes(size_t msg_len, Params params) {
    return dispatch(msg_len, params,
                    []<size_t NB, bool SMALL>() { return Scheme<NB, SMALL>::PROOF_BYTES; });
}

std::vector<uint8_t> prove(const PublicKey& pk, std::span<const uint8_t> msg,
                           const Signature& sig, std::span<const uint8_t> ctx, Params params) {
    const auto q = p256::decode_point(pk);
    if (!q) {
        throw std::invalid_argument("ecdsa_pok: invalid public key");
    }
    p256::Signature s;
    std::copy_n(sig.begin(), 32, s.r.begin());
    std::copy_n(sig.begin() + 32, 32, s.s.begin());
    const Tables tables = make_tables(*q);
    const Digest mu = statement_digest(pk, msg.size(), ctx, params == Params::small);
    // The link challenge depends on the prover's randomness: if its carries exceed the budget
    // (which is very unlikely, see binary.hpp), retry with a fresh seed. This only reveals that
    // the challenge of the output proof is within the budget, which the verifier checks anyway.
    // The degenerate cases of the comb don't depend on the seed, so they fail every attempt.
    constexpr int ATTEMPTS = 8;
    for (int attempt = 1;; ++attempt) {
        const auto seed = random_bytes<32>();
        try {
            const Witness wit = make_witness(*q, tables, msg, s, seed);
            return dispatch(msg.size(), params, [&]<size_t NB, bool SMALL>() {
                std::vector<uint8_t> proof(Scheme<NB, SMALL>::PROOF_BYTES);
                prove_with_witness<NB, SMALL>(
                    std::span<uint8_t, Scheme<NB, SMALL>::PROOF_BYTES>(proof), mu, msg.size(),
                    tables, wit, seed);
                return proof;
            });
        } catch (const std::runtime_error&) {
            if (attempt == ATTEMPTS) {
                throw;
            }
        }
    }
}

bool verify(const PublicKey& pk, size_t msg_len, std::span<const uint8_t> ctx,
            std::span<const uint8_t> proof, Params params) {
    if (msg_len > MAX_MESSAGE_BYTES || proof.size() != proof_bytes(msg_len, params)) {
        return false;
    }
    const auto q = p256::decode_point(pk);
    if (!q) {
        return false;
    }
    Tables tables;
    try {
        tables = make_tables(*q);
    } catch (const std::runtime_error&) {
        return false;
    }
    const Digest mu = statement_digest(pk, msg_len, ctx, params == Params::small);
    return dispatch(msg_len, params, [&]<size_t NB, bool SMALL>() {
        return verify_proof<NB, SMALL>(
            std::span<const uint8_t, Scheme<NB, SMALL>::PROOF_BYTES>(proof.data(), proof.size()),
            mu, msg_len, tables);
    });
}

} // namespace vole_mole::ecdsa_pok
