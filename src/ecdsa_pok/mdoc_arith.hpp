// The arithmetic part of the mdoc proof (see mdoc_relation.hpp), in the VOLEitH proof system over
// F_p and F_n (voleith_p256/voleith.hpp): the issuer's signature, as arith.hpp (a joint comb on the
// public tables of G and the issuer's key, and the scalar equation over F_n), and the device's, as
// rr_arith.hpp (a comb on the public T = r^-1 R). The device's F_p witness follows the issuer's.

#ifndef VOLE_MOLE_ECDSA_POK_MDOC_ARITH_HPP
#define VOLE_MOLE_ECDSA_POK_MDOC_ARITH_HPP

#include "ecdsa_pok/arith.hpp"
#include "ecdsa_pok/rr_arith.hpp"
#include "p256/field.hpp"

#include <cstddef>

namespace vole_mole::ecdsa_pok::detail::mdoc {

// The F_p witness: the issuer's (arith.hpp), then the device's (rr_arith.hpp).
constexpr size_t WP_DEVICE = detail::LP;
constexpr size_t LP = detail::LP + rr::LP;
constexpr size_t LN = detail::LN;
constexpr size_t DP = detail::DP;
constexpr size_t DN = detail::DN;
static_assert(rr::DP == DP && rr::DN <= DN);

struct ArithInstance {
    detail::ArithInstance issuer;
    rr::ArithInstance device;
};

// A constraint context whose F_p witness starts at `off`.
template <typename Ctx> struct OffsetCtx {
    using PV = typename Ctx::PV;
    using NV = typename Ctx::NV;
    Ctx* ctx;
    size_t off;

    PV wp(size_t i) const { return ctx->wp(off + i); }
    NV wn(size_t i) const { return ctx->wn(i); }
    PV cp(const p256::Fp& x) const { return ctx->cp(x); }
    NV cn(const p256::Fn& x) const { return ctx->cn(x); }
    void add_p(const PV& f) { ctx->add_p(f); }
    void add_n(const NV& f) { ctx->add_n(f); }
};

struct ArithRelation {
    static constexpr size_t LP = mdoc::LP, LN = mdoc::LN, DP = mdoc::DP, DN = mdoc::DN;
    using instance = ArithInstance;

    template <typename Ctx> static void constraints(Ctx& ctx, const instance& x) {
        detail::ArithRelation::constraints(ctx, x.issuer);
        OffsetCtx<Ctx> dev{&ctx, WP_DEVICE};
        rr::RrArithRelation::constraints(dev, x.device);
    }
};

} // namespace vole_mole::ecdsa_pok::detail::mdoc

#endif
