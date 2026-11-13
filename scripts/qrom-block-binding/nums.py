#!/usr/bin/env python3
"""Numbers for Q6 Theorems 4 and 5 (docs: lean/docs/extraction/Q6-cipher-binding.md, sections 11-13).

Block representation of the ideal cipher: E_k = Q_k o G_k, with G_k acting independently on
the blocks of a key-dependent partition P_k of X into blocks of size B (unions of e0-cycles).

    mu_B   = nbar / (B(B-1))               density of a new agreement per stored entry (typical)
    a^2    = (32/9) Q^3 mu_B               bound on the expected number of agreement triples
    eps    = (a + c_R)^2                   bound on Pr[MULTI_end]   (c_R: real-world transfer)

Pure Python, exact where it matters (logs in floating point for the table only).
"""
from math import log, log2, sqrt, exp

LN = 128
N = 2 ** LN
TAU = 17


def chernoff_exp(delta):
    """log of e^delta / (1+delta)^(1+delta) (per unit of mean, natural log)."""
    return delta - (1 + delta) * log(1 + delta)


def nbar_for(lb, eps_typ=2.0 ** -8, tail_log2=-460.0):
    """Smallest threshold nbar = 2(1+delta)*mu_half with Chernoff tail <= 2^tail_log2 per half."""
    B = 2.0 ** lb
    mu_half = (1 + eps_typ) ** 3 * B ** 4 / (2 * float(N) ** 3)
    lo, hi = 0.0, 1e6
    for _ in range(200):
        mid = (lo + hi) / 2
        if mu_half * chernoff_exp(mid) <= tail_log2 * log(2):
            hi = mid
        else:
            lo = mid
    return 2 * (1 + hi) * mu_half, mu_half, hi


def a2_log2(lq, nbar, lb):
    return log2(32 / 9) + 3 * lq + log2(nbar) - 2 * lb


def c_R(lq, lb):
    """Transfer terms of Theorems 4 and 5 (amplitudes): key level and block level."""
    q = 2.0 ** lq
    key = sqrt((2 * TAU * q + 2) / (N - 1)) + sqrt(TAU * q / (N - 1))
    cbar_over = 2.0 * (1 + 2.0 ** -8) / float(N)          # cbar / (B(B-1)), cbar <= 2(1+eps)B^2/N
    blk = sqrt(cbar_over * (2 * TAU * q + 2)) + sqrt(cbar_over * TAU * q)
    return key + blk


def main():
    print("== choice of block size B (tail per half-sum <= 2^-460, eps_T <= 2^-301) ==")
    for lb in (96, 97, 98, 99, 100):
        nbar, mu_half, d = nbar_for(lb)
        print(f"B=2^{lb}: mean(half)={mu_half:10.2f} delta={d:7.3f} nbar={nbar:10.1f} "
              f"log2 mu_B={log2(nbar) - 2 * lb:8.2f}  log2(a^2/Q^3)={a2_log2(0, nbar, lb):8.2f}")
    lb = 98
    nbar = 1037            # = ceil(8 * 128 * (1+2^-8)^3), delta = 3
    assert 8 * 128 * (1 + 2.0 ** -8) ** 3 <= nbar
    assert 128 * chernoff_exp(3.0) <= -460 * log(2), "Chernoff tail at delta = 3"
    print(f"\nfixed: B=2^{lb}, nbar={nbar}, log2 mu_B={log2(nbar) - 2 * lb:.3f}")
    print("vacuity of a^2 at log2 Q =", -a2_log2(0, nbar, lb) / 3)

    print("\n== Q2, one proof (Q_E = q; main term 200 q^2/N) ==")
    print(" log2 q | main  | old eps_multi (Q6 Thm 1) | new eps_multi (Thm 4+5) | total")
    for lq in (30, 35, 40, 42, 45, 48, 50, 52, 54, 55, 56, 57, 58, 59, 60, 60.1, 60.2):
        q = 2.0 ** lq
        main_t = 200 * q * q / N
        # old: Theorem 1
        q4 = 3 * q + 1
        a = (4 * sqrt(2) / 3) * q ** 1.5 / sqrt(N - 1)
        ez = min(a * a, 1.0005 * a)
        old = (q4 * sqrt(8 * TAU * ez / N) + 2 * sqrt(2) * q * sqrt(q * q4 * TAU / (N * (N - 1)))) ** 2
        anew = sqrt(2.0 ** a2_log2(lq, nbar, lb))
        new = (anew + c_R(lq, lb)) ** 2
        best = min(old, new)
        tot = main_t + best
        f = lambda v: "vacuous" if v >= 1 else f"2^{log2(v):7.2f}"
        print(f" {lq:6} | {f(main_t):9} | {f(old):9} | {f(new):9} | {f(tot):9}")

    print("\ncrossover new eps_multi = main term at log2 q =",
          (log2(200) - LN - a2_log2(0, nbar, lb)))
    # atypical-database correction: 8 Q^2 sqrt(2 S eps_T / N), eps_T = 2^-301
    lq = 61
    corr = 3 + 2 * lq + 0.5 * (1 + lq - LN - 301)
    print("atypical correction (amplitude) at Q=2^61: 2^%.1f" % corr)


if __name__ == "__main__":
    main()
