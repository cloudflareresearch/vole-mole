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
// T_k[a_k][b_k] are polynomials of degree 15 + 15 in the committed digits, by interpolation on
// [0, 16)^2 (in Newton form, see Tables). Each addition A + T commits only to the slope lambda,
// constrained by lambda (x_T - x_A) = y_T - y_A, and the coordinates of the sum are expressions in
// lambda and the inputs: x' = lambda^2 - x_A - x_T and y' = lambda (x_A - x') - y_A. They're linear
// in x_A and y_A, so the coordinates of every A_k have degree at most 31, without committing to
// them, and so does the constraint. Each digit d is constrained by prod_{m < 16} (d - m) = 0, of
// degree 16.
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
#include "voleith_p256/prg.hpp"

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
    static const Affine p = p256::hash_to_point(
        std::array<uint8_t, 10>{'e', 'c', 'd', 's', 'a', '-', 'p', 'o', 'k', '0'});
    return p;
}
inline const Affine& offset_h() {
    static const Affine p = p256::hash_to_point(
        std::array<uint8_t, 10>{'e', 'c', 'd', 's', 'a', '-', 'p', 'o', 'k', '1'});
    return p;
}

// The comb tables for a public key, and the coordinates of T_k in Newton form: with the falling
// factorials F_i(z) = z (z - 1) ... (z - i + 1),
//
//   x(T_k[a][b]) = sum_{i, j < 16} nx_k[i][j] F_i(a) F_j(b)  for a, b in [0, 16),
//
// where nx_k[i][j] = (D_a^i D_b^j x(T_k))[0][0] / (i! j!) for the forward differences D_a, D_b
// (Newton's forward difference formula, in each variable), and likewise for y. The differences
// take only subtractions, and evaluating the Newton form on committed digits takes about a third
// of the multiplications that the Lagrange form takes.
struct Tables {
    std::vector<Affine> t;  // t[256 k + 16 a + b] = T_k[a][b]
    std::vector<Fp> nx, ny; // nx[256 k + 16 i + j] = nx_k[i][j]
    Affine h0, pstar;

    const Affine& at(size_t k, size_t a, size_t b) const {
        return t[RADIX * RADIX * k + RADIX * a + b];
    }
    const Fp& newton_x(size_t k, size_t i, size_t j) const {
        return nx[RADIX * RADIX * k + RADIX * i + j];
    }
    const Fp& newton_y(size_t k, size_t i, size_t j) const {
        return ny[RADIX * RADIX * k + RADIX * i + j];
    }
};

// 1/i! for i < 16.
inline const std::array<Fp, RADIX>& inv_factorials() {
    static const std::array<Fp, RADIX> out = [] {
        std::array<Fp, RADIX> f;
        Fp acc = Fp::one();
        for (size_t i = 0; i < RADIX; ++i) {
            if (i > 0) {
                acc *= Fp::from_u64(i);
            }
            f[i] = acc.inv();
        }
        return f;
    }();
    return out;
}

// In place, the Newton coefficients of a function on [0, 16)^2 (see Tables).
inline void newton_form(std::span<Fp, RADIX * RADIX> m) {
    for (size_t i = 1; i < RADIX; ++i) {
        for (size_t a = RADIX - 1; a >= i; --a) {
            for (size_t b = 0; b < RADIX; ++b) {
                m[RADIX * a + b] -= m[RADIX * (a - 1) + b];
            }
        }
    }
    for (size_t j = 1; j < RADIX; ++j) {
        for (size_t b = RADIX - 1; b >= j; --b) {
            for (size_t a = 0; a < RADIX; ++a) {
                m[RADIX * a + b] -= m[RADIX * a + b - 1];
            }
        }
    }
    const auto& inv_fact = inv_factorials();
    for (size_t a = 0; a < RADIX; ++a) {
        for (size_t b = 0; b < RADIX; ++b) {
            m[RADIX * a + b] *= inv_fact[a] * inv_fact[b];
        }
    }
}

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
    out.nx.resize(out.t.size());
    out.ny.resize(out.t.size());
    for (size_t i = 0; i < out.t.size(); ++i) {
        if (out.t[i].inf) {
            throw std::runtime_error("ecdsa_pok: degenerate table");
        }
        out.nx[i] = out.t[i].x;
        out.ny[i] = out.t[i].y;
    }
    for (size_t k = 0; k < NUM_DIGITS; ++k) {
        newton_form(std::span<Fp, RADIX * RADIX>(&out.nx[RADIX * RADIX * k], RADIX * RADIX));
        newton_form(std::span<Fp, RADIX * RADIX>(&out.ny[RADIX * RADIX * k], RADIX * RADIX));
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
    Fn c1, c2; // link weights for e and X (F_n)
    Fp c3;     // link weight for X (F_p)
    Fn zn;     // Z_n mod n
    Fp zp;     // Z_p mod p
    std::array<std::array<Fp, 2 * NUM_LIMBS>, NUM_Y_CHECKS> gamma_p;
    std::array<std::array<Fn, 2 * NUM_LIMBS>, NUM_Y_CHECKS> gamma_n;
    std::array<Fp, NUM_Y_CHECKS> y_p;
    std::array<Fn, NUM_Y_CHECKS> y_n;
};

// The small constants 0, ..., 16 of F_p.
inline const std::array<Fp, RADIX + 1>& small_constants() {
    static const std::array<Fp, RADIX + 1> out = [] {
        std::array<Fp, RADIX + 1> c;
        for (size_t i = 0; i <= RADIX; ++i) {
            c[i] = Fp::from_u64(i);
        }
        return c;
    }();
    return out;
}

struct ArithRelation {
    static constexpr size_t LP = detail::LP, LN = detail::LN, DP = detail::DP, DN = detail::DN;
    using instance = ArithInstance;

    // The falling factorials F_0(z), ..., F_16(z), where F_i(z) = z (z - 1) ... (z - i + 1).
    // F_16(z) is zero iff z is in [0, 16).
    template <typename Ctx, typename V>
    static std::array<V, RADIX + 1> falling(const Ctx& ctx, const V& z) {
        const auto& c = small_constants();
        std::array<V, RADIX + 1> f;
        f[0] = ctx.cp(c[1]);
        f[1] = z;
        for (size_t i = 2; i <= RADIX; ++i) {
            f[i] = f[i - 1] * (z - ctx.cp(c[i - 1]));
        }
        return f;
    }

    // sum_{i, j} n(i, j) F_i(a) F_j(b) = Q_0 + b (Q_1 + (b - 1) (Q_2 + ... + (b - 14) Q_15)) for
    // Q_j = sum_i n(i, j) F_i(a).
    template <typename Ctx, typename V, typename N>
    static V newton_eval(const Ctx& ctx, const std::array<V, RADIX + 1>& fa, const V& b, N&& n) {
        const auto& c = small_constants();
        auto q = [&](size_t j) {
            return V::lincomb(std::span<const V>(fa.data(), RADIX),
                              [&](size_t i) { return Fp(n(i, j)); });
        };
        V acc = q(RADIX - 1);
        for (size_t j = RADIX - 1; j-- > 0;) {
            acc = q(j) + (b - ctx.cp(c[j])) * acc;
        }
        return acc;
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
                const PV bk = ctx.wp(WP_B + k);
                const auto fa = falling(ctx, ctx.wp(WP_A + k));
                const auto fb = falling(ctx, bk);
                ctx.add_p(fa[RADIX]);
                ctx.add_p(fb[RADIX]);
                // The coordinates of T_k[a_k][b_k], in Newton form.
                tx = newton_eval(ctx, fa, bk,
                                 [&](size_t i, size_t j) { return tab.newton_x(k, i, j); });
                ty = newton_eval(ctx, fa, bk,
                                 [&](size_t i, size_t j) { return tab.newton_y(k, i, j); });
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

// R, with its F_p witness derived from a key with the local PRG over F_p if DERIVED (see
// voleith_p256/voleith.hpp, step 6). Each witness element then costs one field element of proof
// instead of TAU, the key prg_key_len(R::LP) elements, TAU each, and the QuickSilver degree over
// F_p doubles; it's worth it for large witnesses (e.g., 196 elements, but not 98).
template <typename R, bool DERIVED> struct WithDerivedWitness : R {
    static constexpr size_t KP = DERIVED ? voleith_p256::prg_key_len(R::LP) : 0;
    static_assert(!DERIVED || (KP > 0 && KP < R::LP));
};

} // namespace vole_mole::ecdsa_pok::detail

#endif
