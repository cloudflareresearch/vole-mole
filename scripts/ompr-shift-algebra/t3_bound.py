#!/usr/bin/env python3
"""Exact evaluation of the bounds of lean/docs/security/ompr-shift-algebra.md, section 8
(Theorem T3: the UOV public map has no symmetries but the scalings).

Everything is integer or rational arithmetic; the output is log_q and log_2 of each bound.

  eps_lin : Pr[some non-scalar linear A (invertible), some T, with P∘A = T∘P]      (Theorem G)
            and, with the same value, Pr[some non-scalar X, some Y, B(s, Xs) = Y P(s)] (Theorem L)
  eps_semi: Pr[some Frobenius-semilinear bijection A, semilinear T, with P∘A = T∘P]  (Theorem S)
  eps_dec : Pr[F^N = R ⊕ R' with R, R' ≠ 0 and B(R, R') = 0]                         (Lemma I)

Usage: t3_bound.py [N M [q]]        default 119 45 256
"""
import sys
from fractions import Fraction
from math import log2


def rank_count(n, r, q):
    """Number of n x n matrices of rank r over F_q."""
    num = 1
    den = 1
    for i in range(r):
        num *= (q ** n - q ** i) ** 2
        den *= q ** r - q ** i
    return num // den


def gauss_binom(n, k, q):
    num = 1
    den = 1
    for i in range(k):
        num *= q ** (n - i) - 1
        den *= q ** (i + 1) - 1
    return num // den


def rprime(N, r):
    """Lower bound on rank(A - c) over the algebraic closure, for all c, when
    min over c in F of rank(A - c) = r < N (attained at an eigenvalue in F)."""
    return min(r, N - r // 2)


def bound_eigen(N, M, r):
    """Lemma E, worst case over e0 = dim(E ∩ O)."""
    if r >= N:
        return 0
    e = N - r
    rp = rprime(N, r)
    worst = None
    for e0 in range(max(0, e - (N - M)), min(M, e) + 1):
        e1 = e - e0
        best = 0
        for m in range(0, e1 + 1):
            j = min(m, rp)
            val = m * rp - j * (j + 1) // 2 + e0 * max(0, rp - M - m)
            best = max(best, val)
        worst = best if worst is None else min(worst, best)
    return worst


def bound_free(N, M, r):
    """Lemma F: rho(rho+1)/2 with rho = floor((r - M)/2), for r >= M + 2."""
    if r < M + 2:
        return 0
    rho = (r - M) // 2
    return rho * (rho + 1) // 2


def logq(x, q):
    """log_q of a positive Fraction."""
    x = Fraction(x)
    return (log2(x.numerator) - log2(x.denominator)) / log2(q) if x > 0 else float("-inf")


def eps_lin(N, M, q, verbose=False):
    terms = []
    worst = None
    for r in range(1, N + 1):
        de, df = bound_eigen(N, M, r), bound_free(N, M, r)
        d = max(de, df)
        cnt = q * rank_count(N, r, q)
        expo = M * (d - M)
        terms.append((cnt, expo))
        lt = logq(cnt, q) - expo
        if worst is None or lt > worst[1]:
            worst = (r, lt, de, df)
        if verbose:
            print(f"    r={r:3d}: delta >= {d:5d} (eigen {de:5d}, free {df:4d}); "
                  f"log_q #A = {logq(cnt, q):9.1f}; log_q term = {lt:10.1f}")
    emax = max(e for _, e in terms)
    emin = min(0, min(e for _, e in terms))
    total_num = sum(cnt * q ** (emax - e) for cnt, e in terms)
    return Fraction(total_num, q ** (emax - emin)) * q ** (-emin), worst


def eps_semi(N, M, q):
    D = N * (N + 1) // 2 - M * (M + 1) // 2
    full = N * (N + 1) // 2
    # q = 2^k: Frobenius powers sigma != 1 are k - 1; the fixed field has index >= 2,
    # so the fixed space has at most q^{full*M/2} elements.
    k = q.bit_length() - 1
    num = (k - 1) * q ** (N * N + M * M)
    expo = Fraction(M * D) - Fraction(full * M, 2)
    return Fraction(num) / Fraction(q) ** int(expo) if expo.denominator == 1 else \
        Fraction(num) / Fraction(q) ** int(expo - Fraction(1, 2))


def eps_dec(N, M, q):
    total = Fraction(0)
    worst = None
    lam = M * (M - 1) // 2  # dim of Alt(O)
    for a in range(1, N // 2 + 1):
        b = N - a
        rho = None
        for a0 in range(0, min(a, M) + 1):
            a1 = a - a0
            v = max(a * b - lam, a1 * b + a0 * max(0, b - a1 - M))
            rho = v if rho is None else min(rho, v)
        cnt = gauss_binom(N, a, q) * q ** (a * b)
        term = Fraction(cnt, q ** (M * rho))
        total += term
        lt = logq(term, q)
        if worst is None or lt > worst[1]:
            worst = (a, lt, rho)
    return total, worst


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 2 else 119
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 45
    q = int(sys.argv[3]) if len(sys.argv) > 3 else 256
    verbose = "-v" in sys.argv
    lq = log2(q)
    D = N * (N + 1) // 2 - M * (M + 1) // 2
    print(f"(N, M, q) = ({N}, {M}, {q});  D = dim of quadrics vanishing on O = {D}")
    tot, worst = eps_lin(N, M, q, verbose)
    print(f"eps_lin  <= q^{logq(tot, q):.1f} = 2^{logq(tot, q)*lq:.0f}   "
          f"(largest term r = {worst[0]}: q^{worst[1]:.1f}, delta bounds eigen {worst[2]}, "
          f"free {worst[3]})")
    es = eps_semi(N, M, q)
    print(f"eps_semi <= q^{logq(es, q):.1f} = 2^{logq(es, q)*lq:.0f}")
    ed, wd = eps_dec(N, M, q)
    print(f"eps_dec  <= q^{logq(ed, q):.1f} = 2^{logq(ed, q)*lq:.0f}   "
          f"(largest term dim R = {wd[0]}: q^{wd[1]:.1f}, rank >= {wd[2]})")
    # P_1..P_M linearly dependent
    dep = Fraction((q ** M - 1) // (q - 1), q ** D)
    print(f"eps_indep<= q^{logq(dep, q):.1f}   (the M forms are linearly dependent)")
    allb = tot * 2 + es + ed + dep
    print(f"total (2 eps_lin + eps_semi + eps_dec + eps_indep) <= 2^{logq(allb, q)*lq:.0f}")


if __name__ == "__main__":
    main()
