// The arithmetic part of the ECDSA proof of knowledge (see relation.hpp for the whole statement),
// in the VOLEitH proof system over F_p and F_n (voleith_p256/voleith.hpp).
//
//   Instance: the public key Q (through the tables below), the link challenge and the link values
//             Z_n, Z_p, Y_1, Y_2
//   Witness over F_p: the base-16 digits a_k of u1 and b_k of u2 (k < 64), the slopes lambda_k
//             (k < 65), the mask rho_p, and the masks sigma_1, sigma_2
//   Witness over F_n: the 64-bit limbs of u1 and u2, e, X, the inverse of u2 X, the mask rho_n,
//             and the masks sigma_1, sigma_2 (reduced modulo n)
//
// Fixed-base scalar multiplication, R = u1 G + u2 Q. Both bases are public, so we use a joint
// comb with public tables: for k < 64, T_k[a][b] = a 16^k G + b 16^k Q + H, and
//
//   A_0 = H_0,  A_{k+1} = A_k + T_k[a_k][b_k] (k < 64),  R = A_64 + P*,
//
// where P* = -(H_0 + 64 H), and H_0, H are points of unknown discrete logarithm. The coordinates of
// T_k[a_k][b_k] are polynomials of degree 15 + 15 in the committed digits, by Lagrange
// interpolation on [0, 16)^2. Each addition A + T commits only to the slope lambda, constrained by
// lambda (x_T - x_A) = y_T - y_A, and the coordinates of the sum are expressions in lambda and the
// inputs: x' = lambda^2 - x_A - x_T and y' = lambda (x_A - x') - y_A. They're linear in x_A and
// y_A, so the coordinates of every A_k have degree at most 31, without committing to them, and so
// does the constraint. Each digit d is constrained by prod_{m < 16} (d - m) = 0, of degree 16.
//
// The incomplete addition formula is wrong only if x_T = x_A, i.e., A_k = +-T_k[a_k][b_k]. If
// A_k = -T, then the constraint can't hold (y_T - y_A = 2 y_T != 0, since P-256 has no points of
// order 2). If A_k = T, then lambda is unconstrained. But then H_0 + (k - 1) H = alpha G + beta Q
// for known alpha, beta, so the prover found a discrete-logarithm relation between H_0, H, G, and
// Q, which is infeasible even for a prover who knows the discrete logarithm of Q. Likewise for the
// last step (A_64 = P* means 2 H_0 + 128 H = -(u1 G + u2 Q)). So R = u1 G + u2 Q, where u1, u2 are
// the integers of the digits. (An honest prover fails with negligible probability.)
//
// The scalar equation, over F_n: u1 X = u2 e and (u2 X) inv = 1, where u1 and u2 are the
// combinations of their limbs.
//
// Links (see relation.hpp):
//   - Z_p = c_3 x_R + rho_p (over F_p), where x_R is the expression for the x-coordinate of R;
//   - Z_n = c_1 e + c_2 X + rho_n (over F_n);
//   - Y_i = sum_l gamma_{i,l} L_l + sigma_i (over F_p and F_n), where L_l are the limbs of u1 and
//     u2: over F_p, as integer combinations of the digits; over F_n, the committed limbs.

#ifndef VOLE_MOLE_ECDSA_POK_ARITH_HPP
#define VOLE_MOLE_ECDSA_POK_ARITH_HPP

#include "ecdsa_pok/link.hpp"
#include "p256/curve.hpp"
#include "p256/field.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <vector>

namespace vole_mole::ecdsa_pok::detail {

using p256::Affine;
using p256::Fn;
using p256::Fp;
using p256::Jacobian;

constexpr size_t DIGIT_BITS = 4;
constexpr size_t RADIX = size_t{1} << DIGIT_BITS; // 16
constexpr size_t NUM_DIGITS = 256 / DIGIT_BITS;   // 64 per scalar
constexpr size_t NUM_STEPS = NUM_DIGITS + 1;      // the comb, then P*

// F_p witness layout.
constexpr size_t WP_A = 0;                      // digits of u1
constexpr size_t WP_B = WP_A + NUM_DIGITS;      // digits of u2
constexpr size_t WP_LAMBDA = WP_B + NUM_DIGITS; // slopes
constexpr size_t WP_RHO = WP_LAMBDA + NUM_STEPS;
constexpr size_t WP_SIGMA = WP_RHO + 1;
constexpr size_t LP = WP_SIGMA + NUM_Y_CHECKS;

// F_n witness layout.
constexpr size_t WN_U1 = 0; // limbs of u1
constexpr size_t WN_U2 = WN_U1 + NUM_LIMBS;
constexpr size_t WN_E = WN_U2 + NUM_LIMBS;
constexpr size_t WN_X = WN_E + 1;
constexpr size_t WN_INV = WN_X + 1;
constexpr size_t WN_RHO = WN_INV + 1;
constexpr size_t WN_SIGMA = WN_RHO + 1;
constexpr size_t LN = WN_SIGMA + NUM_Y_CHECKS;

// The QuickSilver degrees.
constexpr size_t DP = 2 * (RADIX - 1) + 1; // 31
constexpr size_t DN = 3;

// Y_i < Y_BOUND = 2^255 + 2^132. The weighted limbs sum to less than 8 2^64 2^64 = 2^131, and
// Y_BOUND + 2^131 < p, so Y_i determines the integer sigma_i (see relation.hpp).
inline bool y_in_range(const p256::Limbs& y) {
    return y[3] < (uint64_t{1} << 63) || (y[3] == (uint64_t{1} << 63) && y[2] < 16);
}

inline const Affine& offset_h0() {
    static const Affine p = p256::hash_to_point(std::array<uint8_t, 10>{'e', 'c', 'd', 's', 'a',
                                                                       '-', 'p', 'o', 'k', '0'});
    return p;
}
inline const Affine& offset_h() {
    static const Affine p = p256::hash_to_point(std::array<uint8_t, 10>{'e', 'c', 'd', 's', 'a',
                                                                       '-', 'p', 'o', 'k', '1'});
    return p;
}

// The comb tables for a public key.
struct Tables {
    std::vector<Affine> t; // t[256 k + 16 a + b] = T_k[a][b]
    Affine h0, pstar;

    const Affine& at(size_t k, size_t a, size_t b) const { return t[RADIX * RADIX * k + RADIX * a + b]; }
};

// Throws std::runtime_error if a table entry is the identity (which happens with negligible
// probability).
inline Tables make_tables(const Affine& q) {
    Tables out;
    std::vector<Jacobian> pts;
    pts.reserve(NUM_DIGITS * RADIX * RADIX);
    Jacobian gk = Jacobian::from(p256::GENERATOR), qk = Jacobian::from(q);
    const Jacobian h = Jacobian::from(offset_h());
    for (size_t k = 0; k < NUM_DIGITS; ++k) {
        Jacobian row = h; // a G_k + H
        for (size_t a = 0; a < RADIX; ++a) {
            Jacobian e = row;
            for (size_t b = 0; b < RADIX; ++b) {
                pts.push_back(e);
                e = e.add(qk);
            }
            row = row.add(gk);
        }
        for (size_t i = 0; i < DIGIT_BITS; ++i) {
            gk = gk.dbl();
            qk = qk.dbl();
        }
    }
    out.t = p256::batch_to_affine(pts);
    for (const auto& p : out.t) {
        if (p.inf) {
            throw std::runtime_error("ecdsa_pok: degenerate table");
        }
    }
    out.h0 = offset_h0();
    Jacobian s = Jacobian::from(out.h0);
    for (size_t k = 0; k < NUM_DIGITS; ++k) {
        s = s.add(h);
    }
    out.pstar = s.to_affine().neg();
    return out;
}

// The public values of the arithmetic relation.
struct ArithInstance {
    const Tables* tables;
    Fn c1, c2;    // link weights for e and X (F_n)
    Fp c3;        // link weight for X (F_p)
    Fn zn;        // Z_n mod n
    Fp zp;        // Z_p mod p
    std::array<std::array<Fp, 2 * NUM_LIMBS>, NUM_Y_CHECKS> gamma_p;
    std::array<std::array<Fn, 2 * NUM_LIMBS>, NUM_Y_CHECKS> gamma_n;
    std::array<Fp, NUM_Y_CHECKS> y_p;
    std::array<Fn, NUM_Y_CHECKS> y_n;
};

// 1 / prod_{m != i} (i - m) for the Lagrange basis on [0, 16).
template <typename F> const std::array<F, RADIX>& lagrange_denominators() {
    static const std::array<F, RADIX> out = [] {
        std::array<F, RADIX> d;
        for (size_t i = 0; i < RADIX; ++i) {
            F acc = F::one();
            for (size_t m = 0; m < RADIX; ++m) {
                if (m != i) {
                    acc *= i > m ? F::from_u64(i - m) : -F::from_u64(m - i);
                }
            }
            d[i] = acc.inv();
        }
        return d;
    }();
    return out;
}

struct ArithRelation {
    static constexpr size_t LP = detail::LP, LN = detail::LN, DP = detail::DP, DN = detail::DN;
    using instance = ArithInstance;

    // The Lagrange basis l_0(z), ..., l_15(z) on [0, 16), and prod_m (z - m).
    template <typename Ctx, typename V>
    static std::array<V, RADIX> lagrange(const Ctx& ctx, const V& z, V* range) {
        std::array<V, RADIX> lin;
        for (size_t m = 0; m < RADIX; ++m) {
            lin[m] = z - ctx.cp(Fp::from_u64(m));
        }
        std::array<V, RADIX> pre, suf;
        pre[0] = ctx.cp(Fp::one());
        for (size_t i = 1; i < RADIX; ++i) {
            pre[i] = pre[i - 1] * lin[i - 1];
        }
        suf[RADIX - 1] = ctx.cp(Fp::one());
        for (size_t i = RADIX - 1; i-- > 0;) {
            suf[i] = suf[i + 1] * lin[i + 1];
        }
        *range = pre[RADIX - 1] * lin[RADIX - 1];
        const auto& den = lagrange_denominators<Fp>();
        std::array<V, RADIX> out;
        for (size_t i = 0; i < RADIX; ++i) {
            out[i] = pre[i] * suf[i] * den[i];
        }
        return out;
    }

    template <typename Ctx> static void constraints(Ctx& ctx, const instance& x) {
        using PV = typename Ctx::PV;
        using NV = typename Ctx::NV;
        const Tables& tab = *x.tables;

        // The comb.
        PV ax = ctx.cp(tab.h0.x), ay = ctx.cp(tab.h0.y);
        for (size_t k = 0; k < NUM_STEPS; ++k) {
            PV tx, ty;
            if (k < NUM_DIGITS) {
                PV range_a, range_b;
                const auto la = lagrange(ctx, ctx.wp(WP_A + k), &range_a);
                const auto lb = lagrange(ctx, ctx.wp(WP_B + k), &range_b);
                ctx.add_p(range_a);
                ctx.add_p(range_b);
                // x_T = sum_b l_b(b_k) sum_a X[a][b] l_a(a_k), and likewise y_T.
                for (size_t b = 0; b < RADIX; ++b) {
                    PV cx = la[0] * tab.at(k, 0, b).x, cy = la[0] * tab.at(k, 0, b).y;
                    for (size_t a = 1; a < RADIX; ++a) {
                        cx += la[a] * tab.at(k, a, b).x;
                        cy += la[a] * tab.at(k, a, b).y;
                    }
                    if (b == 0) {
                        tx = cx * lb[b];
                        ty = cy * lb[b];
                    } else {
                        tx += cx * lb[b];
                        ty += cy * lb[b];
                    }
                }
            } else {
                tx = ctx.cp(tab.pstar.x);
                ty = ctx.cp(tab.pstar.y);
            }
            const PV lambda = ctx.wp(WP_LAMBDA + k);
            ctx.add_p(lambda * (tx - ax) - (ty - ay));
            const PV nx = lambda * lambda - ax - tx;
            const PV ny = lambda * (ax - nx) - ay;
            ax = nx;
            ay = ny;
        }

        // Z_p = c_3 x_R + rho_p.
        ctx.add_p(ax * x.c3 + ctx.wp(WP_RHO) - x.zp);

        // u1 X = u2 e, (u2 X) inv = 1.
        const Fn two64 = Fn::from_u64(uint64_t{1} << 32) * Fn::from_u64(uint64_t{1} << 32);
        NV u1 = ctx.wn(WN_U1 + NUM_LIMBS - 1), u2 = ctx.wn(WN_U2 + NUM_LIMBS - 1);
        for (size_t l = NUM_LIMBS - 1; l-- > 0;) {
            u1 = u1 * two64 + ctx.wn(WN_U1 + l);
            u2 = u2 * two64 + ctx.wn(WN_U2 + l);
        }
        const NV xn = ctx.wn(WN_X), en = ctx.wn(WN_E);
        ctx.add_n(u1 * xn - u2 * en);
        ctx.add_n(u2 * xn * ctx.wn(WN_INV) - Fn::one());

        // Z_n = c_1 e + c_2 X + rho_n.
        ctx.add_n(en * x.c1 + xn * x.c2 + ctx.wn(WN_RHO) - x.zn);

        // Y_i, over F_p from the digits and over F_n from the limbs.
        const Fp sixteen = Fp::from_u64(RADIX);
        std::array<PV, 2 * NUM_LIMBS> limbs_p;
        for (size_t s = 0; s < 2; ++s) {
            const size_t off = s == 0 ? WP_A : WP_B;
            for (size_t l = 0; l < NUM_LIMBS; ++l) {
                constexpr size_t PER_LIMB = 64 / DIGIT_BITS;
                PV acc = ctx.wp(off + PER_LIMB * l + PER_LIMB - 1);
                for (size_t d = PER_LIMB - 1; d-- > 0;) {
                    acc = acc * sixteen + ctx.wp(off + PER_LIMB * l + d);
                }
                limbs_p[NUM_LIMBS * s + l] = acc;
            }
        }
        for (size_t i = 0; i < NUM_Y_CHECKS; ++i) {
            PV yp = ctx.wp(WP_SIGMA + i) - x.y_p[i];
            NV yn = ctx.wn(WN_SIGMA + i) - x.y_n[i];
            for (size_t l = 0; l < 2 * NUM_LIMBS; ++l) {
                yp += limbs_p[l] * x.gamma_p[i][l];
                yn += ctx.wn(WN_U1 + l) * x.gamma_n[i][l];
            }
            ctx.add_p(yp);
            ctx.add_n(yn);
        }
    }
};

} // namespace vole_mole::ecdsa_pok::detail

#endif
