// The arithmetic part of the ECDSA proof with a hidden key and a revealed R (see rr_relation.hpp),
// in the VOLEitH proof system over F_p and F_n (voleith_p256/voleith.hpp).
//
// With R public, the signature equation s R = e G + r Q (r = x(R) mod n) is
//
//   Q = s T + U,  for the public points T = r^-1 R and U = -(e / r) G,
//
// a fixed-base scalar multiplication on T. It's computed with a joint comb on T (arith.hpp's
// JointTables), two base-16 digits of s per step, with tables that the prover and the verifier
// compute per proof:
// for j < 32, T_j[a][a'] = (a + 16 a') 256^j T + H, and
//
//   A_0 = H_0,  A_(j+1) = A_j + T_j[s_(2j)][s_(2j+1)],  Q = A_32 + P*,
//
// where P* = U - (H_0 + 32 H). Q is never committed: its coordinates are expressions of degree 30
// (x) and 31 (y) in the slopes and digits, which the link to the binary proof uses.
//
//   Instance: the tables (from T, U, and the offsets), the link weights, and the link value Z_p
//   Witness over F_p: the digits s_k (k < 64), the slopes lambda_j (j < 33), and the mask rho_p
//   Witness over F_n: none
//
// Constraints: each digit is in [0, 16) (degree 16), each addition lambda (x_T - x_A) = y_T - y_A
// (degree 31), and Z_p = c_x x_Q + c_y y_Q + rho_p (degree 31). (One digit per step would lower
// the degree to 16, as in arith.hpp, but the witness isn't derived here, and the 32 extra slopes
// would cost more proof than the 15 fewer QuickSilver masks save.)
//
// Incomplete additions. The prover chooses R, and so T, so the offsets H_0 and H are hashed to the
// curve from the statement, which includes R (see rr_relation.hpp): the prover can't choose T as a
// function of them. As in arith.hpp, an addition is wrong only if A_j = T_j[..] (if A_j = -T_j[..],
// then its constraint can't hold), i.e., alpha T + H_0 + (j - 1) H = O for an alpha the prover
// knows, or, in the last step, if 2 H_0 + 64 H = U - s T. Either is a discrete-logarithm relation
// between H_0, H, and T, G (with H_0's coefficient nonzero), which is infeasible to find for points
// hashed after T is fixed. (A_32 = -P*, i.e., Q = O, is the case A = -T of the last addition.) So
// Q = s T + U.

#ifndef VOLE_MOLE_ECDSA_POK_RR_ARITH_HPP
#define VOLE_MOLE_ECDSA_POK_RR_ARITH_HPP

#include "ecdsa_pok/arith.hpp"
#include "p256/curve.hpp"
#include "p256/field.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <vector>

namespace vole_mole::ecdsa_pok::detail::rr {

constexpr size_t COMB_STEPS = NUM_DIGITS / 2; // two digits of s per step

// F_p witness layout.
constexpr size_t WP_S = 0;                      // digits of s
constexpr size_t WP_LAMBDA = WP_S + NUM_DIGITS; // slopes of the comb, then of + P*
constexpr size_t WP_RHO = WP_LAMBDA + COMB_STEPS + 1;
constexpr size_t LP = WP_RHO + 1;
static_assert(LP == 98);
constexpr size_t LN = 0;

constexpr size_t DP = 2 * (RADIX - 1) + 1; // 31
constexpr size_t DN = 2;                   // the minimum of voleith_p256 (no constraints)

// The comb tables of T with offset H, and the start H_0 and last addend P* = U - (H_0 + 32 H), in
// the layout of arith.hpp's JointTables (with b = a'). Throws std::runtime_error if a table entry
// or P* is the identity (which happens with negligible probability).
inline JointTables make_tables(const Affine& t, const Affine& u, const Affine& h0,
                               const Affine& h) {
    JointTables out;
    std::vector<Jacobian> pts;
    pts.reserve(COMB_STEPS * RADIX * RADIX);
    Jacobian b1 = Jacobian::from(t);
    Jacobian b2 = b1;
    for (size_t i = 0; i < DIGIT_BITS; ++i) {
        b2 = b2.dbl();
    }
    const Jacobian hj = Jacobian::from(h);
    for (size_t j = 0; j < COMB_STEPS; ++j) {
        Jacobian row = hj;
        for (size_t a = 0; a < RADIX; ++a) {
            Jacobian e = row;
            for (size_t a2 = 0; a2 < RADIX; ++a2) {
                pts.push_back(e);
                e = e.add(b2);
            }
            row = row.add(b1);
        }
        for (size_t i = 0; i < 2 * DIGIT_BITS; ++i) {
            b1 = b1.dbl();
            b2 = b2.dbl();
        }
    }
    // P* = U - H_0 - 32 H.
    Jacobian off = Jacobian::from(h0);
    for (size_t j = 0; j < COMB_STEPS; ++j) {
        off = off.add(hj);
    }
    pts.push_back(Jacobian::from(u).add(Jacobian::from(off.to_affine().neg())));
    std::vector<Affine> aff = p256::batch_to_affine(pts);
    for (const Affine& p : aff) {
        if (p.inf) {
            throw std::runtime_error("ecdsa_pok: degenerate table");
        }
    }
    out.pstar = aff.back();
    aff.pop_back();
    out.t = std::move(aff);
    out.nx.resize(out.t.size());
    out.ny.resize(out.t.size());
    for (size_t i = 0; i < out.t.size(); ++i) {
        out.nx[i] = out.t[i].x;
        out.ny[i] = out.t[i].y;
    }
    for (size_t j = 0; j < COMB_STEPS; ++j) {
        newton_form(std::span<Fp, RADIX * RADIX>(&out.nx[RADIX * RADIX * j], RADIX * RADIX));
        newton_form(std::span<Fp, RADIX * RADIX>(&out.ny[RADIX * RADIX * j], RADIX * RADIX));
    }
    out.h0 = h0;
    return out;
}

struct ArithInstance {
    const JointTables* tables;
    Fp cx, cy; // link weights for x_Q and y_Q
    Fp zp;     // Z_p mod p
};

struct RrArithRelation {
    static constexpr size_t LP = rr::LP, LN = rr::LN, DP = rr::DP, DN = rr::DN;
    using instance = ArithInstance;

    template <typename Ctx> static void constraints(Ctx& ctx, const instance& x) {
        using PV = typename Ctx::PV;
        const JointTables& tab = *x.tables;
        auto add = [&](PV& ax, PV& ay, const PV& tx, const PV& ty, const PV& lambda) {
            ctx.add_p(lambda * (tx - ax) - (ty - ay));
            const PV nx = lambda * lambda - ax - tx;
            const PV ny = lambda * (ax - nx) - ay;
            ax = nx;
            ay = ny;
        };
        PV ax = ctx.cp(tab.h0.x), ay = ctx.cp(tab.h0.y);
        for (size_t j = 0; j < COMB_STEPS; ++j) {
            const PV a2 = ctx.wp(WP_S + 2 * j + 1);
            const auto fa = detail::ArithRelation::falling(ctx, ctx.wp(WP_S + 2 * j));
            const auto fb = detail::ArithRelation::falling(ctx, a2);
            ctx.add_p(fa[RADIX]);
            ctx.add_p(fb[RADIX]);
            const PV tx = detail::ArithRelation::newton_eval(
                ctx, fa, a2, [&](size_t i, size_t i2) { return tab.newton_x(j, i, i2); });
            const PV ty = detail::ArithRelation::newton_eval(
                ctx, fa, a2, [&](size_t i, size_t i2) { return tab.newton_y(j, i, i2); });
            add(ax, ay, tx, ty, ctx.wp(WP_LAMBDA + j));
        }
        add(ax, ay, ctx.cp(tab.pstar.x), ctx.cp(tab.pstar.y), ctx.wp(WP_LAMBDA + COMB_STEPS));
        // Z_p = c_x x_Q + c_y y_Q + rho_p.
        ctx.add_p(ax * x.cx + ay * x.cy + ctx.wp(WP_RHO) - x.zp);
    }
};

} // namespace vole_mole::ecdsa_pok::detail::rr

#endif
