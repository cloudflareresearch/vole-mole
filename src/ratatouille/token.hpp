// Internal access to the contents of a Ratatouille token, pending token, or pending spend, e.g.,
// for testing.

#ifndef VOLE_MOLE_RATATOUILLE_TOKEN_HPP
#define VOLE_MOLE_RATATOUILLE_TOKEN_HPP

#include "vole_mole/ratatouille.hpp"
#include "vole_mole/uov.hpp"

#include "ratatouille/commit.hpp"

namespace vole_mole::ratatouille::detail {

struct TokenAccess {
    // Construct a token (nf, t, r, x, s) from its contents. The contents aren't validated.
    //
    // Throws std::bad_alloc if memory allocation fails.
    static Token make_token(const Nullifier& nf, Credits t, const Opening& r, Credits x,
                            const uov::Preimage& s);

    // Construct a pending token from its contents, where c = Com(nf, ctx_iss, t_init, r). The
    // contents aren't validated.
    //
    // Throws std::bad_alloc if memory allocation fails.
    static PendingToken make_pending_token(const Nullifier& nf, const Opening& r, Credits t_init,
                                           const Commitment& c);

    // Construct a pending spend from the updated state (nf', t', r'), where
    // c' = Com(nf', ctx_iss, t', r'). The contents aren't validated.
    //
    // Throws std::bad_alloc if memory allocation fails.
    static PendingSpend make_pending_spend(const Nullifier& nf, Credits t, const Opening& r,
                                           const Commitment& c);

    // Copy a token, pending token, or pending spend. (They're move-only so that spending and
    // finalization consume them, but tests and benchmarks need to consume the same one several
    // times.) Throws std::logic_error if it was moved from and std::bad_alloc if memory allocation
    // fails.
    static Token copy(const Token& token);
    static PendingToken copy(const PendingToken& pending_token);
    static PendingSpend copy(const PendingSpend& pending_spend);

    // The contents of `token`. (The credit and refund are public.) Throws std::logic_error if the
    // token was moved from.
    static const Nullifier& nf(const Token& token);
    static const Opening& r(const Token& token);
    static const uov::Preimage& s(const Token& token);

    // The contents of `pending_token`. Throws std::logic_error if the pending token was moved
    // from.
    static const Nullifier& nf(const PendingToken& pending_token);
    static const Opening& r(const PendingToken& pending_token);

    // The contents of `pending_spend`, i.e., the updated state (nf', t', r'). Throws
    // std::logic_error if the pending spend was moved from.
    static const Nullifier& nf(const PendingSpend& pending_spend);
    static Credits t(const PendingSpend& pending_spend);
    static const Opening& r(const PendingSpend& pending_spend);

  private:
    static const Token& checked(const Token& token);
    static const PendingToken& checked(const PendingToken& pending_token);
    static const PendingSpend& checked(const PendingSpend& pending_spend);
};

} // namespace vole_mole::ratatouille::detail

#endif
