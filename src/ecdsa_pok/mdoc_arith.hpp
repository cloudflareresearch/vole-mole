// The arithmetic part of the mdoc proof (see mdoc_relation.hpp), in the VOLEitH proof system over
// F_p and F_n (voleith_p256/voleith.hpp): the issuer's signature, as arith.hpp (a joint comb on the
// public tables of G and the issuer's key, and the scalar equation over F_n), and the device's, as
// hk_arith.hpp (R = u1 G + u2 Q with the device key Q committed, and the scalar equation). The
// device's witness follows the issuer's, over both fields; then comes the mask rho_q of the link
//
//   Z_q = c_x x_Q + c_y y_Q + rho_q (over F_p),
//
// which ties Q to the device key in the MSO, committed as bits in the binary proof (as
// rr_binary.hpp's link sum).

#ifndef VOLE_MOLE_ECDSA_POK_MDOC_ARITH_HPP
#define VOLE_MOLE_ECDSA_POK_MDOC_ARITH_HPP

#include "ecdsa_pok/arith.hpp"
#include "ecdsa_pok/hk_arith.hpp"
#include "p256/field.hpp"

#include <algorithm>
#include <cstddef>

namespace vole_mole::ecdsa_pok::detail::mdoc {

// The F_p witness: the issuer's (arith.hpp), the device's (hk_arith.hpp), then rho_q.
constexpr size_t WP_DEVICE = detail::LP;
constexpr size_t WP_RHO_Q = WP_DEVICE + hk::LP;
constexpr size_t LP = WP_RHO_Q + 1;
// The F_n witness: the issuer's, then the device's.
constexpr size_t WN_DEVICE = detail::LN;
constexpr size_t LN = WN_DEVICE + hk::LN;
constexpr size_t DP = std::max(detail::DP, hk::DP); // 34
constexpr size_t DN = std::max(detail::DN, hk::DN);

struct ArithInstance {
    detail::ArithInstance issuer;
    hk::ArithInstance device;
    Fp cx, cy; // link weights for x_Q and y_Q
    Fp zq;     // Z_q mod p
};

// A constraint context whose F_p and F_n witnesses start at off_p and off_n.
template <typename Ctx> struct OffsetCtx {
    using PV = typename Ctx::PV;
    using NV = typename Ctx::NV;
    Ctx* ctx;
    size_t off_p, off_n;

    PV wp(size_t i) const { return ctx->wp(off_p + i); }
    NV wn(size_t i) const { return ctx->wn(off_n + i); }
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
        OffsetCtx<Ctx> dev{&ctx, WP_DEVICE, WN_DEVICE};
        hk::HkArithRelation::constraints(dev, x.device);
        // Z_q = c_x x_Q + c_y y_Q + rho_q.
        ctx.add_p(ctx.wp(WP_DEVICE + hk::WP_Q) * x.cx + ctx.wp(WP_DEVICE + hk::WP_Q + 1) * x.cy +
                  ctx.wp(WP_RHO_Q) - x.zq);
    }
};

} // namespace vole_mole::ecdsa_pok::detail::mdoc

#endif
