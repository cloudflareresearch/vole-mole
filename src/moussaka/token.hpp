// Internal access to the contents of a Moussaka token or pending token, e.g., for testing.

#ifndef VOLE_MOLE_MOUSSAKA_TOKEN_HPP
#define VOLE_MOLE_MOUSSAKA_TOKEN_HPP

#include "vole_mole/moussaka.hpp"
#include "vole_mole/uov.hpp"

#include "moussaka/commit.hpp"

namespace vole_mole::moussaka::detail {

struct TokenAccess {
    // Throws std::bad_alloc if memory allocation fails.
    static Token make_token(const Nullifier& nf, const Opening& r, const uov::Preimage& s);

    // Throws std::bad_alloc if memory allocation fails.
    static PendingToken make_pending_token(const Nullifier& nf, const Opening& r,
                                           const Context& ctx_iss, const Context& ctx_red,
                                           const Commitment& t);

    // Copy a token or pending token. (They're move-only so that redemption and finalization
    // consume them, but tests and benchmarks need to consume the same one several times.) Throws
    // std::logic_error if the token or pending token was moved from and std::bad_alloc if memory
    // allocation fails.
    static Token copy(const Token& token);
    static PendingToken copy(const PendingToken& pending_token);

    // The contents of `token`. Throws std::logic_error if the token was moved from.
    static const Nullifier& nf(const Token& token);
    static const Opening& r(const Token& token);
    static const uov::Preimage& s(const Token& token);

    // The contents of `pending_token`. Throws std::logic_error if the pending token was moved
    // from.
    static const Nullifier& nf(const PendingToken& pending_token);
    static const Opening& r(const PendingToken& pending_token);

  private:
    static const Token& checked(const Token& token);
    static const PendingToken& checked(const PendingToken& pending_token);
};

} // namespace vole_mole::moussaka::detail

#endif
