// The arithmetic part of the hidden-key ECDSA proof (see hk_relation.hpp for the whole statement),
// in the VOLEitH proof system over F_p and F_n (voleith_p256/voleith.hpp).
//
// Unlike arith.hpp, the public key Q is part of the witness, so u2 Q is a variable-base scalar
// multiplication. The message, and so e, is public.
//
//   Instance: e, the link challenge, and the link values Z_n, Z_p, Y_1, Y_2
//   Witness over F_p: Q = (x_Q, y_Q), the slopes of the table of Q, the base-16 digits a_k of u1
//             and b_k of u2 (k < 64), the slopes of the ladder, the comb and the final step, the
//             mask rho_p, and the masks sigma_1, sigma_2
//   Witness over F_n: the 64-bit limbs of u1 and u2, X, the inverse of u2 X, the mask rho_n, and
//             the masks sigma_1, sigma_2 (reduced modulo n)
//
// R = u1 G + u2 Q is computed in three parts, all with incomplete affine additions that commit only
// to the slope (as in arith.hpp):
//
//   1. The table P_b = b Q + H_1 for b < 16: P_0 = H_1 and P_b = P_(b - 1) + Q (15 slopes). The
//      coordinates of P_b have degree 2 (x) and 3 (y) in the slopes and Q.
//   2. A ladder on the digits of u2, from the most significant: A = H_0, then for k = 63, ..., 0,
//      A = 16 A (four doublings, except for k = 63) and A = A + P_(b_k). The coordinates of
//      P_(b_k) are the Newton interpolation of the table at the committed digit, of degree
//      15 + 2 (x) and 15 + 3 (y). A doubling commits to its slope lambda, constrained by
//      lambda 2 y_A = 3 x_A^2 - 3, of degree 2 (15 + 2) = 34: that's the QuickSilver degree DP.
//      Then A = u2 Q + (16^63 h_0 + h_1 sum_k 16^k) G.
//   3. A fixed-base comb on the digits of u1, two per step: for j < 32,
//      A = A + T_j[a_(2j)][a_(2j + 1)], where T_j[a][a'] = (a + 16 a') 256^j G + H_2 are public, in
//      Newton form (as in arith.hpp, of degree 15 + 15). Finally R = A + P*, for the public
//      P* = -(16^63 h_0 + h_1 sum_k 16^k + 32 h_2) G.
//
// Each digit d is constrained by prod_(m < 16) (d - m) = 0, and Q by the curve equation.
//
// Incomplete additions. In arith.hpp, Q is fixed by the statement and the offsets have unknown
// discrete logarithms. Here the prover chooses Q, so it could pick Q to make an addition
// exceptional (e.g., Q = H_1 if H_1 were a hashed point). So the offsets are instead known
// multiples H_i = h_i G, for hashed scalars h_i. Every point of the computation is then
// alpha Q + beta G for integers alpha, beta that the extractor can compute from the digits and the
// step. An addition A + T is wrong only if x_A = x_T. If A = -T, then its constraint can't hold
// (y_T - y_A = 2 y_T != 0, since P-256 has no points of order 2). If A = T, then
// (alpha_A - alpha_T) Q = (beta_T - beta_A) G:
//
//   - if alpha_A != alpha_T (mod n), this gives the discrete logarithm d of Q, and a prover who
//     knows d can sign e anyway, so it doesn't break knowledge soundness (the extractor signs);
//   - if alpha_A = alpha_T, then beta_A = beta_T, a "structural" collision that doesn't depend on
//     Q. In the table, beta_A = beta_T means h_1 = 0. In the ladder at digit k,
//     beta_A = 16^(63 - k) h_0 + h_1 sum_(k < j < 64) 16^(j - k) and beta_T = h_1, which
//     offsets_are_sound() checks never collide. In the comb and the last step, alpha_A = u2 and
//     alpha_T = 0, and u2 != 0 (mod n) by the scalar equation below.
//
// A doubling is wrong only if y_A = 0, which no point of P-256 has. So R = u1 G + u2 Q (an affine
// point, so R != O), or the prover knows d.
//
// The scalar equation, over F_n: u1 X = u2 e and (u2 X) inv = 1, where e is public.
//
// Links (see hk_relation.hpp):
//   - Z_p = c_3 x_R + rho_p (over F_p), where x_R is the expression for the x-coordinate of R;
//   - Z_n = c_2 X + rho_n (over F_n);
//   - Y_i = sum_l gamma_(i,l) L_l + sigma_i (over F_p and F_n), as in arith.hpp.

#ifndef VOLE_MOLE_ECDSA_POK_HK_ARITH_HPP
#define VOLE_MOLE_ECDSA_POK_HK_ARITH_HPP

#include "ecdsa_pok/arith.hpp"
#include "ecdsa_pok/link.hpp"
#include "p256/curve.hpp"
#include "p256/field.hpp"
#include "sha256/sha256.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <vector>

namespace vole_mole::ecdsa_pok::detail::hk {

constexpr size_t NUM_WINDOWS = NUM_DIGITS;                       // 64 digits of u2
constexpr size_t NUM_DOUBLINGS = DIGIT_BITS * (NUM_WINDOWS - 1); // 252
constexpr size_t LADDER_STEPS = NUM_DOUBLINGS + NUM_WINDOWS;     // 316
constexpr size_t COMB_STEPS = NUM_DIGITS / 2;                    // two digits of u1 per step

// F_p witness layout.
constexpr size_t WP_Q = 0;                           // x_Q, y_Q
constexpr size_t WP_TABLE = WP_Q + 2;                // slopes of P_1, ..., P_15
constexpr size_t WP_A = WP_TABLE + RADIX - 1;        // digits of u1
constexpr size_t WP_B = WP_A + NUM_DIGITS;           // digits of u2
constexpr size_t WP_LADDER = WP_B + NUM_DIGITS;      // slopes of the ladder, in order
constexpr size_t WP_COMB = WP_LADDER + LADDER_STEPS; // slopes of the comb
constexpr size_t WP_FINAL = WP_COMB + COMB_STEPS;    // slope of the last step (+ P*)
constexpr size_t WP_RHO = WP_FINAL + 1;
constexpr size_t WP_SIGMA = WP_RHO + 1;
constexpr size_t LP = WP_SIGMA + NUM_Y_CHECKS;
static_assert(LP == 497);

// F_n witness layout.
constexpr size_t WN_U1 = 0; // limbs of u1
constexpr size_t WN_U2 = WN_U1 + NUM_LIMBS;
constexpr size_t WN_X = WN_U2 + NUM_LIMBS;
constexpr size_t WN_INV = WN_X + 1;
constexpr size_t WN_RHO = WN_INV + 1;
constexpr size_t WN_SIGMA = WN_RHO + 1;
constexpr size_t LN = WN_SIGMA + NUM_Y_CHECKS;

// The QuickSilver degrees. The ladder's x-coordinate has the degree of the selected table entry,
// RADIX - 1 + 2, and the doubling constraint squares it.
constexpr size_t TABLE_X_DEGREE = 2;
constexpr size_t LADDER_X_DEGREE = RADIX - 1 + TABLE_X_DEGREE; // 17
constexpr size_t DP = 2 * LADDER_X_DEGREE;                     // 34
static_assert(DP >= 2 * (RADIX - 1) + 1);                      // the comb (as in arith.hpp)
constexpr size_t DN = 3;

// The offsets H_i = h_i G, with h_i = SHA-256("ecdsa-pok-hk-h" || i) mod n, and P*.
struct Offsets {
    std::array<Fn, 3> h;
    Affine h0, h1, h2, pstar;
};

// sum_(k < m) 16^k mod n.
inline Fn sum_pow16(size_t m) {
    Fn s = Fn::zero(), p = Fn::one();
    const Fn sixteen = Fn::from_u64(RADIX);
    for (size_t k = 0; k < m; ++k) {
        s += p;
        p *= sixteen;
    }
    return s;
}
inline Fn pow16(size_t m) {
    Fn p = Fn::one();
    const Fn sixteen = Fn::from_u64(RADIX);
    for (size_t k = 0; k < m; ++k) {
        p *= sixteen;
    }
    return p;
}

inline const Offsets& offsets() {
    static const Offsets out = [] {
        Offsets o;
        for (size_t i = 0; i < 3; ++i) {
            const std::array<uint8_t, 15> label{'e', 'c', 'd', 's', 'a',
                                                '-', 'p', 'o', 'k', '-',
                                                'h', 'k', '-', 'h', static_cast<uint8_t>('0' + i)};
            o.h[i] = Fn::reduce_32(sha256::hash(label));
        }
        auto mul_g = [](const Fn& k) {
            const Affine p = p256::scalar_mul(p256::GENERATOR, k.canonical()).to_affine();
            if (p.inf) {
                throw std::logic_error("ecdsa_pok: degenerate offset");
            }
            return p;
        };
        o.h0 = mul_g(o.h[0]);
        o.h1 = mul_g(o.h[1]);
        o.h2 = mul_g(o.h[2]);
        const Fn t = pow16(NUM_WINDOWS - 1) * o.h[0] + o.h[1] * sum_pow16(NUM_WINDOWS) +
                     Fn::from_u64(COMB_STEPS) * o.h[2];
        o.pstar = mul_g(-t);
        return o;
    }();
    return out;
}

// Whether no addition can collide structurally (see above): h_1 != 0, and for each digit k of the
// ladder, 16^(63 - k) h_0 + h_1 sum_(k < j < 64) 16^(j - k) != h_1.
inline bool offsets_are_sound() {
    const Offsets& o = offsets();
    if (o.h[1].is_zero()) {
        return false;
    }
    for (size_t k = 0; k < NUM_WINDOWS; ++k) {
        const size_t above = NUM_WINDOWS - 1 - k;
        // sum_(k < j < 64) 16^(j - k) = sum_(1 <= i <= above) 16^i = 16 sum_(i < above) 16^i
        const Fn beta_a = pow16(above) * o.h[0] + o.h[1] * Fn::from_u64(RADIX) * sum_pow16(above);
        if (beta_a == o.h[1]) {
            return false;
        }
    }
    return true;
}

// The comb tables of G: T_j[a][a'] = (a + 16 a') 256^j G + H_2 for j < 32, with Newton
// coefficients as in arith.hpp's Tables (with b = a').
inline const Tables& comb_tables() {
    static const Tables out = [] {
        Tables t;
        std::vector<Jacobian> pts;
        pts.reserve(COMB_STEPS * RADIX * RADIX);
        Jacobian b1 = Jacobian::from(p256::GENERATOR);
        Jacobian b2 = b1;
        for (size_t i = 0; i < DIGIT_BITS; ++i) {
            b2 = b2.dbl();
        }
        const Jacobian h2 = Jacobian::from(offsets().h2);
        for (size_t j = 0; j < COMB_STEPS; ++j) {
            Jacobian row = h2;
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
        t.t = p256::batch_to_affine(pts);
        t.nx.resize(t.t.size());
        t.ny.resize(t.t.size());
        for (size_t i = 0; i < t.t.size(); ++i) {
            if (t.t[i].inf) {
                throw std::logic_error("ecdsa_pok: degenerate comb table");
            }
            t.nx[i] = t.t[i].x;
            t.ny[i] = t.t[i].y;
        }
        for (size_t j = 0; j < COMB_STEPS; ++j) {
            newton_form(std::span<Fp, RADIX * RADIX>(&t.nx[RADIX * RADIX * j], RADIX * RADIX));
            newton_form(std::span<Fp, RADIX * RADIX>(&t.ny[RADIX * RADIX * j], RADIX * RADIX));
        }
        t.h0 = offsets().h0;
        t.pstar = offsets().pstar;
        return t;
    }();
    return out;
}

// The public values of the arithmetic relation.
struct ArithInstance {
    Fn e;  // the message hash, reduced modulo n
    Fn c2; // link weight for X (F_n)
    Fp c3; // link weight for X (F_p)
    Fn zn; // Z_n mod n
    Fp zp; // Z_p mod p
    std::array<std::array<Fp, 2 * NUM_LIMBS>, NUM_Y_CHECKS> gamma_p;
    std::array<std::array<Fn, 2 * NUM_LIMBS>, NUM_Y_CHECKS> gamma_n;
    std::array<Fp, NUM_Y_CHECKS> y_p;
    std::array<Fn, NUM_Y_CHECKS> y_n;
};

struct HkArithRelation {
    static constexpr size_t LP = hk::LP, LN = hk::LN, DP = hk::DP, DN = hk::DN;
    using instance = ArithInstance;

    // prod_(m < 16) (d - m), which is zero iff d is in [0, 16).
    template <typename Ctx, typename V> static V range16(const Ctx& ctx, const V& d) {
        const auto& c = small_constants();
        V acc = d;
        for (size_t m = 1; m < RADIX; ++m) {
            acc = acc * (d - ctx.cp(c[m]));
        }
        return acc;
    }

    // In place, from the values v_b (b < 16) to the Newton coefficients n_i = (D^i v)_0 / i!.
    template <typename V> static void newton_1d(std::array<V, RADIX>& v) {
        for (size_t i = 1; i < RADIX; ++i) {
            for (size_t b = RADIX - 1; b >= i; --b) {
                v[b] = v[b] - v[b - 1];
            }
        }
        const auto& inv_fact = inv_factorials();
        for (size_t i = 2; i < RADIX; ++i) {
            v[i] *= inv_fact[i];
        }
    }

    // sum_i n_i F_i(d) = n_0 + d (n_1 + (d - 1) (n_2 + ... + (d - 14) n_15)).
    template <typename Ctx, typename V>
    static V select(const Ctx& ctx, const std::array<V, RADIX>& n, const V& d) {
        const auto& c = small_constants();
        V acc = n[RADIX - 1];
        for (size_t i = RADIX - 1; i-- > 0;) {
            acc = n[i] + (d - ctx.cp(c[i])) * acc;
        }
        return acc;
    }

    template <typename Ctx> static void constraints(Ctx& ctx, const instance& x) {
        using PV = typename Ctx::PV;
        using NV = typename Ctx::NV;
        const Offsets& off = offsets();
        const Tables& tab = comb_tables();
        const Fp three = Fp::from_u64(3);

        // A + T: commit to the slope, and update A.
        auto add = [&](PV& ax, PV& ay, const PV& tx, const PV& ty, const PV& lambda) {
            ctx.add_p(lambda * (tx - ax) - (ty - ay));
            const PV nx = lambda * lambda - ax - tx;
            const PV ny = lambda * (ax - nx) - ay;
            ax = nx;
            ay = ny;
        };

        // Q is on the curve.
        const PV xq = ctx.wp(WP_Q), yq = ctx.wp(WP_Q + 1);
        ctx.add_p(yq * yq - ((xq * xq - three) * xq + p256::CURVE_B));

        // The table P_b = b Q + H_1, in Newton form.
        std::array<PV, RADIX> tx, ty;
        tx[0] = ctx.cp(off.h1.x);
        ty[0] = ctx.cp(off.h1.y);
        for (size_t b = 1; b < RADIX; ++b) {
            tx[b] = tx[b - 1];
            ty[b] = ty[b - 1];
            add(tx[b], ty[b], xq, yq, ctx.wp(WP_TABLE + b - 1));
        }
        newton_1d(tx);
        newton_1d(ty);

        // The ladder.
        PV ax = ctx.cp(off.h0.x), ay = ctx.cp(off.h0.y);
        size_t s = WP_LADDER;
        for (size_t w = 0; w < NUM_WINDOWS; ++w) {
            if (w > 0) {
                for (size_t i = 0; i < DIGIT_BITS; ++i) {
                    const PV lambda = ctx.wp(s++);
                    ctx.add_p(lambda * (ay + ay) - (ax * ax * three - three));
                    const PV nx = lambda * lambda - ax - ax;
                    const PV ny = lambda * (ax - nx) - ay;
                    ax = nx;
                    ay = ny;
                }
            }
            const PV d = ctx.wp(WP_B + NUM_WINDOWS - 1 - w);
            ctx.add_p(range16(ctx, d));
            add(ax, ay, select(ctx, tx, d), select(ctx, ty, d), ctx.wp(s++));
        }

        // The comb.
        for (size_t j = 0; j < COMB_STEPS; ++j) {
            const PV a2 = ctx.wp(WP_A + 2 * j + 1);
            const auto fa = detail::ArithRelation::falling(ctx, ctx.wp(WP_A + 2 * j));
            const auto fb = detail::ArithRelation::falling(ctx, a2);
            ctx.add_p(fa[RADIX]);
            ctx.add_p(fb[RADIX]);
            const PV cx = detail::ArithRelation::newton_eval(
                ctx, fa, a2, [&](size_t i, size_t i2) { return tab.newton_x(j, i, i2); });
            const PV cy = detail::ArithRelation::newton_eval(
                ctx, fa, a2, [&](size_t i, size_t i2) { return tab.newton_y(j, i, i2); });
            add(ax, ay, cx, cy, ctx.wp(WP_COMB + j));
        }
        add(ax, ay, ctx.cp(off.pstar.x), ctx.cp(off.pstar.y), ctx.wp(WP_FINAL));

        // Z_p = c_3 x_R + rho_p.
        ctx.add_p(ax * x.c3 + ctx.wp(WP_RHO) - x.zp);

        // u1 X = u2 e, (u2 X) inv = 1.
        const Fn two64 = Fn::from_u64(uint64_t{1} << 32) * Fn::from_u64(uint64_t{1} << 32);
        NV u1 = ctx.wn(WN_U1 + NUM_LIMBS - 1), u2 = ctx.wn(WN_U2 + NUM_LIMBS - 1);
        for (size_t l = NUM_LIMBS - 1; l-- > 0;) {
            u1 = u1 * two64 + ctx.wn(WN_U1 + l);
            u2 = u2 * two64 + ctx.wn(WN_U2 + l);
        }
        const NV xn = ctx.wn(WN_X);
        ctx.add_n(u1 * xn - u2 * x.e);
        ctx.add_n(u2 * xn * ctx.wn(WN_INV) - Fn::one());

        // Z_n = c_2 X + rho_n.
        ctx.add_n(xn * x.c2 + ctx.wn(WN_RHO) - x.zn);

        // Y_i, over F_p from the digits and over F_n from the limbs.
        const Fp sixteen = Fp::from_u64(RADIX);
        std::array<PV, 2 * NUM_LIMBS> limbs_p;
        for (size_t u = 0; u < 2; ++u) {
            const size_t first = u == 0 ? WP_A : WP_B;
            for (size_t l = 0; l < NUM_LIMBS; ++l) {
                constexpr size_t PER_LIMB = 64 / DIGIT_BITS;
                PV acc = ctx.wp(first + PER_LIMB * l + PER_LIMB - 1);
                for (size_t i = PER_LIMB - 1; i-- > 0;) {
                    acc = acc * sixteen + ctx.wp(first + PER_LIMB * l + i);
                }
                limbs_p[NUM_LIMBS * u + l] = acc;
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

} // namespace vole_mole::ecdsa_pok::detail::hk

#endif
