// The arithmetic part of the hidden-key ECDSA proof (see hk_relation.hpp for the whole statement),
// in the VOLEitH proof system over F_p and F_n (voleith_p256/voleith.hpp).
//
// Unlike arith.hpp, the public key Q is part of the witness, so u2 Q is a variable-base scalar
// multiplication. The message, and so e, is public.
//
//   Instance: e, the link challenge, and the link values Z_n, Z_p, Y_1, Y_2
//   Witness over F_p: Q = (x_Q, y_Q), the slopes and points of the table of Q, the base-16 digits
//             a_k of u1 (k < 64), the base-4 digits c_(k,0) and c_(k,1) of u2 (so that its
//             base-16 digit b_k = c_(k,0) + 4 c_(k,1)), the slopes of the ladder, the comb and the
//             final step, the mask rho_p, and the masks sigma_1, sigma_2
//   Witness over F_n: the 64-bit limbs of u1 and u2, X, the inverse of u2 X, the mask rho_n, and
//             the masks sigma_1, sigma_2 (reduced modulo n)
//
// R = u1 G + u2 Q is computed in three parts, all with incomplete affine additions that commit only
// to the slope (as in arith.hpp):
//
//   1. The table P_b = b Q + H_1 for b < 16: P_0 = H_1 and P_b = P_(b - 1) + Q. Both the slopes
//      and the points P_1, ..., P_15 are committed (degree-2 constraints), so that the points have
//      degree 1.
//   2. A ladder on the digits of u2, from the most significant: A = H_0, then for k = 63, ..., 0,
//      A = 16 A (four doublings, except for k = 63) and A = A + S_k, where S_k = P_(b_k) is the
//      two-dimensional Newton interpolation of the table (as a 4 x 4 grid) at (c_(k,0), c_(k,1)),
//      of degree 3 + 3 + 1 = 7 (S_k isn't committed). A doubling commits to its slope lambda,
//      constrained by lambda 2 y_A = 3 x_A^2 - 3. An addition or doubling keeps the degree of x_A
//      (x' = lambda^2 - x_A - x_S), so along the ladder x_A has degree at most 7 and y_A at most
//      8, and the doubling constraints have degree 14. Then
//      A = u2 Q + (16^63 h_0 + h_1 sum_k 16^k) G.
//   3. A fixed-base comb on the digits of u1: for k < 64, A = A + T_k[a_k], where
//      T_k[a] = a 16^k G + H_2 are public, in Newton form (arith.hpp's Comb, of degree 15). Finally
//      R = A + P*, for the public P* = -(16^63 h_0 + h_1 sum_k 16^k + 64 h_2) G. As in arith.hpp,
//      the constraints have degree 16.
//
// So the QuickSilver degree DP is 16, that of the comb and of the range checks of the digits of u1.
// (Without committing the table points, the selection would have degree 7 + 2 = 9 and the doubling
// constraints 18. Selecting with the base-16 digits of u2 would need degree 15 + 1, and so
// committing the selected points to keep the doublings within degree 16: 128 elements rather than
// the 64 extra digits. With two digits per comb step, the comb would have degree 31.)
//
// Each digit a of u1 is constrained by prod_(m < 16) (a - m) = 0, each base-4 digit c of u2 by
// c (c - 1) (c - 2) (c - 3) = 0, and Q by the curve equation.
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
constexpr size_t COMB_STEPS = NUM_DIGITS;                        // one digit of u1 per step

// F_p witness layout.
constexpr size_t WP_Q = 0;                              // x_Q, y_Q
constexpr size_t WP_TABLE = WP_Q + 2;                   // slopes of P_1, ..., P_15
constexpr size_t WP_TABLE_PTS = WP_TABLE + RADIX - 1;   // x, y of P_1, ..., P_15
constexpr size_t SUB = 4;                               // base of the digits of u2
constexpr size_t WP_A = WP_TABLE_PTS + 2 * (RADIX - 1); // digits of u1
constexpr size_t WP_B = WP_A + NUM_DIGITS;              // c_(k,0), c_(k,1) for k < 64
constexpr size_t WP_LADDER = WP_B + 2 * NUM_DIGITS;     // slopes of the ladder, in order
constexpr size_t WP_COMB = WP_LADDER + LADDER_STEPS;    // slopes of the comb
constexpr size_t WP_FINAL = WP_COMB + COMB_STEPS;       // slope of the last step (+ P*)
constexpr size_t WP_RHO = WP_FINAL + 1;
constexpr size_t WP_SIGMA = WP_RHO + 1;
constexpr size_t LP = WP_SIGMA + NUM_Y_CHECKS;
static_assert(LP == 623);
static_assert(SUB * SUB == RADIX);

// F_n witness layout.
constexpr size_t WN_U1 = 0; // limbs of u1
constexpr size_t WN_U2 = WN_U1 + NUM_LIMBS;
constexpr size_t WN_X = WN_U2 + NUM_LIMBS;
constexpr size_t WN_INV = WN_X + 1;
constexpr size_t WN_RHO = WN_INV + 1;
constexpr size_t WN_SIGMA = WN_RHO + 1;
constexpr size_t LN = WN_SIGMA + NUM_Y_CHECKS;

// The QuickSilver degrees (see above).
constexpr size_t DP = RADIX; // 16
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

// The comb tables of G: T_k[a] = a 16^k G + H_2 for k < 64 (see arith.hpp's Comb).
inline const Comb& comb_tables() {
    static const Comb out = make_comb(p256::GENERATOR, offsets().h2);
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

    // c (c - 1) (c - 2) (c - 3), which is zero iff c is in [0, 4).
    template <typename Ctx, typename V> static V range4(const Ctx& ctx, const V& c) {
        const auto& k = small_constants();
        return c * (c - ctx.cp(k[1])) * ((c - ctx.cp(k[2])) * (c - ctx.cp(k[3])));
    }

    // In place, from the values v_b (b < 4) to the Newton coefficients n_i = (D^i v)_0 / i!.
    template <typename V> static void newton_4(std::array<V, SUB>& v) {
        for (size_t i = 1; i < SUB; ++i) {
            for (size_t b = SUB - 1; b >= i; --b) {
                v[b] = v[b] - v[b - 1];
            }
        }
        const auto& inv_fact = inv_factorials();
        for (size_t i = 2; i < SUB; ++i) {
            v[i] *= inv_fact[i];
        }
    }

    // sum_i n_i F_i(c) = n_0 + c (n_1 + (c - 1) (n_2 + (c - 2) n_3)).
    template <typename Ctx, typename V>
    static V select_4(const Ctx& ctx, const std::array<V, SUB>& n, const V& c) {
        const auto& k = small_constants();
        V acc = n[SUB - 1];
        for (size_t i = SUB - 1; i-- > 0;) {
            acc = n[i] + (c - ctx.cp(k[i])) * acc;
        }
        return acc;
    }

    // The two-dimensional Newton coefficients n[j][i] of v[4 c1 + c0] (c0, c1 < 4), in place:
    // v(c0, c1) = sum_(i, j) n[j][i] F_i(c0) F_j(c1).
    template <typename V> static void newton_grid(std::array<std::array<V, SUB>, SUB>& g) {
        for (auto& row : g) {
            newton_4(row);
        }
        for (size_t i = 0; i < SUB; ++i) {
            std::array<V, SUB> col;
            for (size_t j = 0; j < SUB; ++j) {
                col[j] = g[j][i];
            }
            newton_4(col);
            for (size_t j = 0; j < SUB; ++j) {
                g[j][i] = col[j];
            }
        }
    }
    template <typename Ctx, typename V>
    static V select_grid(const Ctx& ctx, const std::array<std::array<V, SUB>, SUB>& n, const V& c0,
                         const V& c1) {
        std::array<V, SUB> rows;
        for (size_t j = 0; j < SUB; ++j) {
            rows[j] = select_4(ctx, n[j], c0);
        }
        return select_4(ctx, rows, c1);
    }

    template <typename Ctx> static void constraints(Ctx& ctx, const instance& x) {
        using PV = typename Ctx::PV;
        using NV = typename Ctx::NV;
        const Offsets& off = offsets();
        const Comb& tab = comb_tables();
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

        // The table P_b = b Q + H_1 (committed), as a 4 x 4 grid in Newton form.
        std::array<std::array<PV, SUB>, SUB> tx, ty;
        tx[0][0] = ctx.cp(off.h1.x);
        ty[0][0] = ctx.cp(off.h1.y);
        for (size_t b = 1; b < RADIX; ++b) {
            PV px = tx[(b - 1) / SUB][(b - 1) % SUB], py = ty[(b - 1) / SUB][(b - 1) % SUB];
            add(px, py, xq, yq, ctx.wp(WP_TABLE + b - 1));
            PV& bx = tx[b / SUB][b % SUB];
            PV& by = ty[b / SUB][b % SUB];
            bx = ctx.wp(WP_TABLE_PTS + 2 * (b - 1));
            by = ctx.wp(WP_TABLE_PTS + 2 * (b - 1) + 1);
            ctx.add_p(bx - px);
            ctx.add_p(by - py);
        }
        newton_grid(tx);
        newton_grid(ty);

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
            const size_t k = NUM_WINDOWS - 1 - w;
            const PV c0 = ctx.wp(WP_B + 2 * k), c1 = ctx.wp(WP_B + 2 * k + 1);
            ctx.add_p(range4(ctx, c0));
            ctx.add_p(range4(ctx, c1));
            add(ax, ay, select_grid(ctx, tx, c0, c1), select_grid(ctx, ty, c0, c1), ctx.wp(s++));
        }

        // The comb.
        for (size_t k = 0; k < COMB_STEPS; ++k) {
            const auto fa = detail::ArithRelation::falling(ctx, ctx.wp(WP_A + k));
            ctx.add_p(fa[RADIX]);
            add(ax, ay,
                detail::ArithRelation::newton_eval_1d(fa,
                                                      [&](size_t i) { return tab.newton_x(k, i); }),
                detail::ArithRelation::newton_eval_1d(fa,
                                                      [&](size_t i) { return tab.newton_y(k, i); }),
                ctx.wp(WP_COMB + k));
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
        const Fp sixteen = Fp::from_u64(RADIX), four = Fp::from_u64(SUB);
        // The base-16 digit k of u1 or u2.
        auto digit = [&](size_t u, size_t k) -> PV {
            if (u == 0) {
                return ctx.wp(WP_A + k);
            }
            return ctx.wp(WP_B + 2 * k + 1) * four + ctx.wp(WP_B + 2 * k);
        };
        std::array<PV, 2 * NUM_LIMBS> limbs_p;
        for (size_t u = 0; u < 2; ++u) {
            for (size_t l = 0; l < NUM_LIMBS; ++l) {
                constexpr size_t PER_LIMB = 64 / DIGIT_BITS;
                PV acc = digit(u, PER_LIMB * l + PER_LIMB - 1);
                for (size_t i = PER_LIMB - 1; i-- > 0;) {
                    acc = acc * sixteen + digit(u, PER_LIMB * l + i);
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
