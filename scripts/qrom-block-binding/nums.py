#!/usr/bin/env python3
"""Numbers for Q6 Theorems 4 and 5 (docs: lean/docs/extraction/Q6-cipher-binding.md, sections 11-13).

Block representation of the ideal cipher: E_k = Q_k o G_k, with G_k acting independently on
the blocks of a key-dependent partition P_k of X into blocks of size B (unions of e0-cycles).

    mu_B   = nbar / (B(B-1))               density of a new agreement per stored entry (typical)
    a^2    = (32/9) Q^3 mu_B               bound on the expected number of agreement triples
    eps    = (a + c_R)^2                   bound on Pr[MULTI_end]   (c_R: real-world transfer)

Review (Q6 §14): the transfer term is c_R' = 5 sqrt(|T|/N), with |T| the number of targets; it
does not grow with the query count (the original c_R = 6 sqrt(tau (Q+1)/N) is kept for comparison).
The last two tables apply Theorem 5 to simulation-extractability (Q5) and to multi-proof
extraction (Q7), next to Q6 Theorems 1 and 2.

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


def c_R_refined(n_targets):
    """Review, Q6 §14.3: both transfer steps together cost 5 sqrt(|T|/N) in amplitude."""
    return 5 * sqrt(n_targets / float(N))


def thm5(lq_E, n_targets, nbar=1037, lb=98):
    """Theorem 5 with the refined transfer: ((1+2^-61) a + c_R')^2 (c_atyp, eps_Theta negligible)."""
    a = sqrt(2.0 ** a2_log2(lq_E, nbar, lb))
    return ((1 + 2.0 ** -61) * a + c_R_refined(n_targets)) ** 2


def thm1(QE, q4, T):
    """Q6 Theorem 1 (key level, H4)."""
    a = (4 * sqrt(2) / 3) * QE ** 1.5 / sqrt(N - 1)
    ez = min(a * a, 1.0005 * a)
    return (q4 * sqrt(8 * T * ez / N) + 2 * sqrt(2) * QE * sqrt(QE * q4 * T / (N * (N - 1)))) ** 2


def thm2(QA, QC, q4, T):
    """Q6 Theorem 2 (mixed classical/quantum, key level, H4)."""
    S = QA + QC
    G = QC * S / (N - 1)
    X = 2 ** 9 * G
    aA = 2 * sqrt(2) * QA * sqrt(S / (N - 1))
    ez = min((aA + sqrt(G + X)) ** 2, 1.0005 * aA + G + X)
    p = 1.0 / (N * (N - 1))
    GB = QC * S * q4 * T * p
    return (q4 * sqrt(8 * T * ez / N) + 2 * sqrt(2) * QA * sqrt(S * q4 * T * p)
            + sqrt(GB * (1 + 2 ** 9))) ** 2


L_LEAVES = 2304
K_FETCH = 4607          # Lemma K: key fetches per proof / verification
C_EVAL = 2 ** 18        # cipher evaluations per simulated proof / verification (Q5 section 1.1)


def fmt(v):
    return "vacuous" if v >= 1 else f"2^{log2(v):7.2f}"


def se_table():
    print("\n== SE (Q5): eps_bind = min(Theorem 2 [fetches, H4], Theorem 5 [evaluations]) ==")
    print(" log2 q | log2 Q_S | main 200q^2/N | Thm2 weak | Thm2 strong | Thm5 (both) | total weak | total strong")
    n_out = 1
    for lq, lqs in ((30, 20), (30, 30), (35, 30), (40, 20), (40, 30), (45, 20), (45, 30),
                    (50, 20), (50, 30), (55, 30), (58, 30)):
        q, QS = 2.0 ** lq, 2.0 ** lqs
        main_t = 200 * q * q / N
        QA = q + n_out * K_FETCH
        QC = QS * K_FETCH
        q4 = q + 2 * (q + QS + n_out) + 3 * QS + n_out + 1
        t2w, t2s = thm2(QA, QC, q4, 17), thm2(QA, QC, q4, 2320)
        QEev = q + (QS + n_out) * C_EVAL
        t5 = thm5(log2(QEev), (n_out + 2 * QS) * L_LEAVES)
        print(f" {lq:6} | {lqs:8} | {fmt(main_t):9} | {fmt(t2w):9} | {fmt(t2s):9} | {fmt(t5):9} "
              f"(Q_E=2^{log2(QEev):.1f}) | {fmt(main_t + min(t2w, t5)):9} | {fmt(main_t + min(t2s, t5)):9}")


def multi_table():
    print("\n== Theorem M (Q7): eps_multi = min(Theorem 1 [fetches, H4], Theorem 5 [evaluations]) ==")
    print(" log2 q | log2 n | main 8(5q+7n)^2/N | Thm1 | Thm5 | old c_R^2 (tau=17n) | total")
    for lq, ln in ((30, 0), (30, 20), (30, 30), (40, 20), (45, 20), (50, 20), (50, 30), (55, 20), (58, 20)):
        q, n = 2.0 ** lq, 2.0 ** ln
        main_t = 8 * (5 * q + 7 * n) ** 2 / N
        QEf = q + n * K_FETCH
        q4 = 3 * q + n + 1
        t1 = thm1(QEf, q4, 17)
        QEev = q + n * C_EVAL
        t5 = thm5(log2(QEev), n * L_LEAVES)
        old_cr = 36 * 17 * n * (QEev + 1) / N
        print(f" {lq:6} | {ln:6} | {fmt(main_t):9} | {fmt(t1):9} | {fmt(t5):9} | {fmt(old_cr):9} "
              f"| {fmt(main_t + min(t1, t5)):9}")


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
        orig = (anew + c_R(lq, lb)) ** 2
        new = thm5(lq, L_LEAVES)
        best = min(old, new)
        tot = main_t + best
        f = fmt
        print(f" {lq:6} | {f(main_t):9} | {f(old):9} | {f(new):9} | {f(tot):9}   "
              f"(with the original c_R: {f(orig)})")

    print("\ncrossover new eps_multi = main term at log2 q =",
          (log2(200) - LN - a2_log2(0, nbar, lb)))
    # atypical-database correction: 8 Q^2 sqrt(2 S eps_T / N), eps_T = 2^-301
    lq = 61
    corr = 3 + 2 * lq + 0.5 * (1 + lq - LN - 301)
    print("atypical correction (amplitude) at Q=2^61: 2^%.1f" % corr)
    print("refined transfer c_R'^2 = 25 |T|/N at |T| = L: 2^%.1f" % log2(25 * L_LEAVES / float(N)))
    se_table()
    multi_table()


if __name__ == "__main__":
    main()
