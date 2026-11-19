#!/usr/bin/env python3
"""Cost estimates for the systems in lean/docs/security/uov-open-structure.md, Part B.

Model (the usual one for UOV parameter selection): a system of m quadratic equations in n
variables over F_q is solved by hybrid XL with a sparse (Wiedemann) solver.  After guessing k
variables the operating degree D is the first d at which the coefficient of t^d in
(1 - t^2)^m / (1 - t)^(n - k + 1) is non-positive (semi-regularity assumption), and the cost is

    q^k * 3 * binom(n - k + D, D)^2 * binom(n - k + 2, 2)      field multiplications.

Bit operations: one multiplication in F_q is counted as 2 (log2 q)^2 + log2 q.
All figures are estimates under the semi-regularity heuristic; the bilinear structure of some of
the systems is ignored.
"""
from math import comb, log2
import sys


def operating_degree(n, m, dmax=400):
    # coefficients of (1 - t^2)^m / (1 - t)^(n + 1)
    num = [0] * (dmax + 1)
    for i in range(0, min(m, dmax // 2) + 1):
        num[2 * i] = (-1) ** i * comb(m, i)
    for d in range(dmax + 1):
        c = sum(num[j] * comb(n + d - j, d - j) for j in range(d + 1))
        if c <= 0:
            return d
    return None


def xl_cost(n, m, q):
    """log2 field multiplications, best k, D."""
    best = None
    for k in range(0, n):
        nn = n - k
        D = operating_degree(nn, m)
        if D is None:
            continue
        c = k * log2(q) + log2(3) + 2 * log2(comb(nn + D, D)) + log2(comb(nn + 2, 2))
        if best is None or c < best[0]:
            best = (c, k, D)
        if k > 40:
            break
    return best


def bits(logmul, q):
    lq = log2(q)
    return logmul + log2(2 * lq * lq + lq)


def report(name, n, m, q):
    c, k, D = xl_cost(n, m, q)
    print(f"{name:58s} vars={n:4d} eqs={m:4d}  k={k:2d} D={D:3d}  "
          f"log2 mults={c:6.1f}  log2 bit ops={bits(c, q):6.1f}")


def main():
    q = 256
    for (N, M) in [(112, 44), (119, 45)]:
        V = N - M
        print(f"--- (N, M, q) = ({N}, {M}, {q}), V = {V}")
        # Direct forgery: M equations; fix N - M variables (no further reduction applied).
        report("direct (M eqs in M vars)", M, M, q)
        # Kipnis-Shamir: q^(N - 2M) trials, each a few N^3 multiplications.
        ks = (N - 2 * M) * log2(q) + 3 * log2(N)
        print(f"{'Kipnis-Shamir  q^(N-2M) * N^3':58s} log2 mults={ks:6.1f}  log2 bit ops={bits(ks, q):6.1f}")
        # Intersection attack [Beu21], k = 2: 3M - 2 equations, 2N - 3M free variables
        # (the solution space has dimension 3M - N; one coordinate normalised).
        report("intersection k=2 (3M-2 eqs, 2N-3M vars)", 2 * N - 3 * M, 3 * M - 2, q)
        # Dedicated badness tests (Part B, section B.4)
        # (a) one sample: o in K_s (V - 1 vars after normalisation), M equations: underdetermined.
        print(f"{'B.4(a) one sample: o in K_s':58s} vars={V-1:4d} eqs={M:4d}  underdetermined: always solvable")
        # (b) one sample + intersection pair: vars (2N-3M) + (V-1); eqs (3M-2) + M + 2M
        report("B.4(b) sample + intersection pair", (2 * N - 3 * M) + (V - 1), (3 * M - 2) + 3 * M, q)
        # (c) three candidate bad samples: 3(V-1) vars, 3M + 3M eqs
        report("B.4(c) three bad samples", 3 * (V - 1), 6 * M, q)
        # (d) two bad samples + one free oil vector: 2(V-1) + (N-M) vars... free oil vector has
        #     N - (M - 1) - 1 = V free coordinates; eqs 3M + 3M
        report("B.4(d) two bad samples + one oil vector", 2 * (V - 1) + V, 6 * M, q)


if __name__ == "__main__":
    main()
