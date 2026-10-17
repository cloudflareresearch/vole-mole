// Selection constraints for binary circuits (see bin_ops.hpp), for the mdoc proof
// (mdoc_binary.hpp): one-hot vectors, selecting one of several vectors of wires, and comparing a
// window of a byte string at a secret offset with a pattern.
//
// Each is a single QuickSilver constraint (two for one-hot vectors), whatever the number of wires:
// the constraints are random linear combinations, with coefficients derived from the QuickSilver
// challenge chal2 (see "Challenge-dependent constraints" in voleith.hpp), of constraints over
// GF(2). Since chal2 is derived after the prover is committed to the whole witness, a combination
// of constraints that don't all hold is zero with probability at most d / 2^128, for a polynomial
// of degree d in the coefficients (Schwartz-Zippel). With CountOps they're only counted, and
// with PlainOps (the prover's plaintext evaluation) they're checked directly, without
// coefficients.
//
// The constraints, for committed bits s_k, w_k, and vectors of wires X_k, Y:
//
//   - assert_onehot(s): exactly one s_k is 1. Its parity is 1 (a linear constraint), and
//     (sum_k a_k s_k)(sum_k b_k s_k) = sum_k a_k b_k s_k for random a, b in GF(2^128) (degree 2).
//     The difference is sum_{k < l} (a_k b_l + a_l b_k) s_k s_l, a nonzero polynomial of degree 2
//     in (a, b) if two s_k are 1.
//   - assert_select(s, X, Y): sum_k s_k X_k = Y over GF(2), i.e., for one-hot s, Y is the selected
//     X_k. With random rho, sum_k s_k <rho, X_k> = <rho, Y> (degree 2).
//   - assert_and_zero(w, X): w_k X_k = 0 for every k (componentwise), with independent random
//   rho_k:
//     sum_k w_k <rho_k, X_k> = 0 (degree 2).
//   - assert_window(B, T, P): for the bytes B_0, ..., B_{N-1} of a buffer, terms T = {(a_t, b_t,
//     pos_t)} (pairs of bits, and offsets with pos_t + |P| <= N), and a pattern P of |P| bytes,
//     sum_t a_t b_t B[pos_t .. pos_t + |P|) = P over GF(2). For one-hot selections (exactly one
//     a_t b_t is 1), the selected window is P. Bytes are embedded in GF(2^128) by an injective
//     GF(2)-linear map phi (faest's combine_8_bits), and with a random r, this is
//     sum_t a_t b_t V_{pos_t}(r) = sum_j r^j phi(P_j) for V_k(r) = sum_{j < |P|} r^j phi(B_{k+j}),
//     a polynomial identity of degree |P| - 1 in r (degree 3 in the witness). Every V_k comes from
//     the suffix sums S_k = phi(B_k) + r S_{k+1}, as V_k = S_k + r^|P| S_{k+|P|}.
//   - assert_poly(M): the sum of monomials M (products of up to 3 wires; the empty product is 1)
//     is 0 over GF(2) (degree up to 3).

#ifndef VOLE_MOLE_ECDSA_POK_SELECT_OPS_HPP
#define VOLE_MOLE_ECDSA_POK_SELECT_OPS_HPP

#include "ecdsa_pok/bin_ops.hpp"
#include "qs_bit.hpp"

#include "hash.hpp"        // from faest-arch-opt
#include "parameters.hpp"  // from faest-arch-opt
#include "polynomials.hpp" // from faest-arch-opt
#include "quicksilver.hpp" // from faest-arch-opt

extern "C" {
#include "KeccakHash.h" // from xkcp
}

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <stdexcept>
#include <vector>

namespace vole_mole::ecdsa_pok::detail {

// A term of assert_window: the window at byte offset pos, selected by a b.
template <typename Wire> struct SelTerm {
    Wire a, b;
    size_t pos;
};

// A monomial of assert_poly: the product of n <= 3 wires.
template <typename Wire> struct Monomial {
    std::array<Wire, 3> w;
    size_t n;
};

// QsOps with a stream of public coefficients in GF(2^128), derived from chal2.
template <typename QS> struct SelQsOps : QsOps<QS> {
    using Poly = faest::poly_secpar<QS::secpar_v>;
    Keccak_HashInstance stream;

    SelQsOps(QS* q, std::span<const uint8_t> chal2, std::span<const uint8_t> dst)
        : QsOps<QS>(q, chal2) {
        faest::hash_state h;
        h.init(faest::secpar::s128);
        h.update(dst);
        h.update(chal2);
        Keccak_HashFinal(&h.ctx, nullptr);
        stream = h.ctx;
    }
    Poly coeff() {
        std::array<uint8_t, 16> b;
        Keccak_HashSqueeze(&stream, b.data(), 8 * b.size());
        return Poly::load(b.data());
    }
};

// CountOps: one constraint each (two for one-hot vectors).
inline void assert_onehot(CountOps& ops, std::span<const CountOps::Wire>) { ops.constraints += 2; }
inline void assert_select(CountOps& ops, std::span<const CountOps::Wire>,
                          std::span<const std::vector<CountOps::Wire>>,
                          std::span<const CountOps::Wire>) {
    ++ops.constraints;
}
inline void assert_and_zero(CountOps& ops, std::span<const CountOps::Wire>,
                            std::span<const std::vector<CountOps::Wire>>) {
    ++ops.constraints;
}
inline void assert_window(CountOps& ops, std::span<const CountOps::Wire>,
                          std::span<const SelTerm<CountOps::Wire>>,
                          std::span<const CountOps::Wire>) {
    ++ops.constraints;
}
inline void assert_poly(CountOps& ops, std::span<const Monomial<CountOps::Wire>>) {
    ++ops.constraints;
}

// PlainOps: check the constraints over GF(2).
inline void assert_onehot(PlainOps& ops, std::span<const PlainOps::Wire> s) {
    ops.constraints += 2;
    const auto ones = std::ranges::count(s, PlainOps::Wire{1});
    ops.failed += (ones % 2 != 1) + (ones > 1);
}
inline void assert_select(PlainOps& ops, std::span<const PlainOps::Wire> s,
                          std::span<const std::vector<PlainOps::Wire>> x,
                          std::span<const PlainOps::Wire> y) {
    ++ops.constraints;
    std::vector<PlainOps::Wire> acc(y.begin(), y.end());
    for (size_t k = 0; k < s.size(); ++k) {
        if (s[k]) {
            for (size_t i = 0; i < acc.size(); ++i) {
                acc[i] ^= x[k][i];
            }
        }
    }
    ops.failed += std::ranges::any_of(acc, [](auto v) { return v != 0; });
}
inline void assert_and_zero(PlainOps& ops, std::span<const PlainOps::Wire> w,
                            std::span<const std::vector<PlainOps::Wire>> x) {
    ++ops.constraints;
    bool bad = false;
    for (size_t k = 0; k < w.size(); ++k) {
        bad = bad || (w[k] && std::ranges::any_of(x[k], [](auto v) { return v != 0; }));
    }
    ops.failed += bad;
}
inline void assert_window(PlainOps& ops, std::span<const PlainOps::Wire> buf,
                          std::span<const SelTerm<PlainOps::Wire>> terms,
                          std::span<const PlainOps::Wire> pattern) {
    ++ops.constraints;
    std::vector<PlainOps::Wire> acc(pattern.begin(), pattern.end());
    for (const auto& t : terms) {
        if (t.a & t.b) {
            for (size_t i = 0; i < acc.size(); ++i) {
                acc[i] ^= buf[8 * t.pos + i];
            }
        }
    }
    ops.failed += std::ranges::any_of(acc, [](auto v) { return v != 0; });
}
inline void assert_poly(PlainOps& ops, std::span<const Monomial<PlainOps::Wire>> m) {
    ++ops.constraints;
    PlainOps::Wire acc = 0;
    for (const auto& t : m) {
        PlainOps::Wire p = 1;
        for (size_t i = 0; i < t.n; ++i) {
            p &= t.w[i];
        }
        acc ^= p;
    }
    ops.failed += acc;
}

// SelQsOps: random linear combinations.
namespace sel_impl {

template <typename QS, size_t d> using G = faest::quicksilver_gfsecpar<QS, d>;

template <typename QS> G<QS, 1> lin(const typename QsOps<QS>::Wire& w) {
    return vole_mole::detail::qs_to_gfsecpar(w);
}

// <rho, x> for fresh coefficients rho.
template <typename QS>
G<QS, 1> inner(SelQsOps<QS>& ops, std::span<const typename QsOps<QS>::Wire> x) {
    G<QS, 1> acc(ops.qs);
    for (const auto& w : x) {
        acc += lin<QS>(w) * ops.coeff();
    }
    return acc;
}

} // namespace sel_impl

template <typename QS>
void assert_onehot(SelQsOps<QS>& ops, std::span<const typename QsOps<QS>::Wire> s) {
    using namespace sel_impl;
    using Wire = typename QsOps<QS>::Wire;
    Wire parity = ops.zero();
    G<QS, 1> a(ops.qs), b(ops.qs), c(ops.qs);
    for (const auto& w : s) {
        parity = ops.add(parity, w);
        const auto ca = ops.coeff(), cb = ops.coeff();
        const G<QS, 1> l = lin<QS>(w);
        a += l * ca;
        b += l * cb;
        c += l * (ca * cb).template reduce_to<QS::secpar_bits>();
    }
    ops.assert_eq(parity, true);
    ++ops.constraints;
    ops.constrain(a * b + G<QS, 2>(c));
}

template <typename QS>
void assert_select(SelQsOps<QS>& ops, std::span<const typename QsOps<QS>::Wire> s,
                   std::span<const std::vector<typename QsOps<QS>::Wire>> x,
                   std::span<const typename QsOps<QS>::Wire> y) {
    using namespace sel_impl;
    using Wire = typename QsOps<QS>::Wire;
    const size_t len = y.size();
    std::vector<typename SelQsOps<QS>::Poly> rho(len);
    for (auto& r : rho) {
        r = ops.coeff();
    }
    auto dot = [&](std::span<const Wire> v) {
        G<QS, 1> acc(ops.qs);
        for (size_t i = 0; i < len; ++i) {
            acc += lin<QS>(v[i]) * rho[i];
        }
        return acc;
    };
    G<QS, 2> acc(dot(y));
    for (size_t k = 0; k < s.size(); ++k) {
        acc += vole_mole::detail::qs_mul(s[k], dot(x[k]));
    }
    ++ops.constraints;
    ops.constrain(acc);
}

template <typename QS>
void assert_and_zero(SelQsOps<QS>& ops, std::span<const typename QsOps<QS>::Wire> w,
                     std::span<const std::vector<typename QsOps<QS>::Wire>> x) {
    using namespace sel_impl;
    G<QS, 2> acc(ops.qs);
    for (size_t k = 0; k < w.size(); ++k) {
        acc += vole_mole::detail::qs_mul(w[k], inner<QS>(ops, x[k]));
    }
    ++ops.constraints;
    ops.constrain(acc);
}

template <typename QS>
void assert_window(SelQsOps<QS>& ops, std::span<const typename QsOps<QS>::Wire> buf,
                   std::span<const SelTerm<typename QsOps<QS>::Wire>> terms,
                   std::span<const typename QsOps<QS>::Wire> pattern) {
    using namespace sel_impl;
    using Poly = typename SelQsOps<QS>::Poly;
    const size_t n = buf.size() / 8, w = pattern.size() / 8;
    const Poly r = ops.coeff();
    Poly rw = Poly::from_1(faest::poly1(1));
    for (size_t j = 0; j < w; ++j) {
        rw = (rw * r).template reduce_to<QS::secpar_bits>();
    }
    auto byte = [&](std::span<const typename QsOps<QS>::Wire> v, size_t i) {
        return G<QS, 1>::combine_8_bits(v.data() + 8 * i);
    };
    // Suffix sums S_k = phi(B_k) + r S_{k+1}, S_n = 0.
    std::vector<G<QS, 1>> suf(n + 1, G<QS, 1>(ops.qs));
    for (size_t k = n; k-- > 0;) {
        suf[k] = byte(buf, k) + suf[k + 1] * r;
    }
    G<QS, 1> pat(ops.qs);
    for (size_t j = w; j-- > 0;) {
        pat = byte(pattern, j) + pat * r;
    }
    G<QS, 3> acc(pat);
    for (const auto& t : terms) {
        if (t.pos + w > n) {
            throw std::logic_error("ecdsa_pok: window out of range");
        }
        const G<QS, 1> v = suf[t.pos] + suf[t.pos + w] * rw;
        acc += vole_mole::detail::qs_mul(t.a, vole_mole::detail::qs_mul(t.b, v));
    }
    ++ops.constraints;
    ops.constrain(acc);
}

template <typename QS>
void assert_poly(SelQsOps<QS>& ops, std::span<const Monomial<typename QsOps<QS>::Wire>> m) {
    using namespace sel_impl;
    G<QS, 3> acc(ops.qs);
    for (const auto& t : m) {
        switch (t.n) {
        case 0:
            acc += G<QS, 3>(faest::poly1(1), ops.qs);
            break;
        case 1:
            acc += G<QS, 3>(lin<QS>(t.w[0]));
            break;
        case 2:
            acc += G<QS, 3>(
                vole_mole::detail::qs_to_gfsecpar(vole_mole::detail::qs_mul(t.w[0], t.w[1])));
            break;
        case 3:
            acc += vole_mole::detail::qs_to_gfsecpar(
                vole_mole::detail::qs_mul(vole_mole::detail::qs_mul(t.w[0], t.w[1]), t.w[2]));
            break;
        default:
            throw std::logic_error("ecdsa_pok: monomial of degree > 3");
        }
    }
    ++ops.constraints;
    ops.constrain(acc);
}

} // namespace vole_mole::ecdsa_pok::detail

#endif
