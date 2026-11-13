#!/usr/bin/env python3
"""Cost estimates and toy experiments for lean/docs/security/ompr-shift-algebra.md, section 4.1.

C1: with collinear shifts lambda_a * c (a <= tau), a forgery is a solution of the M - 1 equations
pi_c(P(s)) = pi_c(h) whose remaining coordinate mu(s) is one of the tau values lambda_a.

Part 1 (pure Python, a few seconds).  Hybrid-solver estimates over F_256 for uov-Ip-pkc
(N, M) = (119, 45) and, for comparison, (112, 44).  With n free variables left after guessing,

    direct forgery     min_j  q^j         * S(M - j variables, M     quadrics)
    C1 at tau          min_j  q^j / tau   * S(M - j variables, M - 1 quadrics)

so C1 is the direct attack with one equation dropped from the solver and tau guesses saved.
Break-even: tau* = q * (C1 cost per solution of the M - 1 equations) / (direct cost).
Solver models S (all heuristic, semi-regular systems; formulas quoted from memory):
  xl0   XL + Wiedemann, 3 T^2 binom(n+2, 2), T = binom(n+D, D), D the first degree at which the
        coefficient of (1-t^2)^m / (1-t)^(n+1) is <= 0   (scripts/uov-open-structure/mq_estimates.py)
  xl1   the same with "<= 1" (XL with corank one still isolates one candidate point; see part 2)
  f5_w  F5-type dense linear algebra, binom(n+d-1, d)^w, d the first degree at which the
        coefficient of (1-t^2)^m / (1-t)^n is <= 0, for w = 2, 2.37, 2.81
Preprocessing of the underdetermined system (N variables, m equations):
  plain fix N - m variables: m equations in m variables;
  tw    Thomae-Wolf as improved by Furue-Nakamura-Takagi: after k guesses, m - a equations in
        m - k - a variables, a = floor((N - k) / (m - k)) - 1.

Part 2 (needs gcc; builds c1_toy.c).  Toy UOV keys over F_16 and F_256, direct attack against
C1, by XL with dense elimination.  Measured: the degree at which XL decides, calls per solution,
the law of mu over the solutions of the M - 1 equations, field multiplications per call.

Part 3 (pure Python, uses shift_algebra_toy.py).  Section 4.3: a singular vector z (P(z) = 0,
e.g. D(0)) makes the landing free without any shift.  On W_c = {s : B(s, z) in F c} the map
pi_c o P is invariant under s -> s + lambda z, and P(s + lambda z) = P(s) + lambda B(s, z).
Checked on toy keys over F_16: dim W_c = N - M + 1, and every s in W_c with
pi_c(P(s)) = pi_c(t), B(s, z) != 0 gives a preimage of t.

Usage: c1_experiments.py [estimates | line | toy [full|quick [i,j,...]]]   (default: all)
Run it under a memory cap; the toy part uses all cores and takes about 20 minutes on 24 cores
(2 minutes with `quick`).  The optional list selects toy configurations by index.
"""
import os
import subprocess
import sys
import tempfile
from math import comb, log2

INF = float("inf")


# ---------------------------------------------------------------- part 1: estimates

def first_nonpositive(n_den, m, thr=0, dmax=400):
    """First d >= 2 with [t^d] (1 - t^2)^m / (1 - t)^n_den <= thr, or None."""
    for d in range(2, dmax + 1):
        c = sum((-1) ** i * comb(m, i) * comb(n_den - 1 + d - 2 * i, d - 2 * i)
                for i in range(0, min(m, d // 2) + 1))
        if c <= thr:
            return d
    return None


def solver_cost(model, n, m):
    """log2 multiplications to solve m quadrics in n variables, and the degree used."""
    if n < 1 or m <= n:
        return INF, None
    if model in ("xl0", "xl1"):
        D = first_nonpositive(n + 1, m, 0 if model == "xl0" else 1)
        if D is None:
            return INF, None
        return log2(3) + 2 * log2(comb(n + D, D)) + log2(comb(n + 2, 2)), D
    w = {"f5_2": 2.0, "f5_2.37": 2.37, "f5_2.81": 2.81}[model]
    d = first_nonpositive(n, m, 0)
    if d is None:
        return INF, None
    return w * log2(comb(n + d - 1, d)), d


def hybrid(model, n, m, q):
    """min over j of q^j * S(n - j, m): (log2 cost, j, degree)."""
    best = (INF, None, None)
    for j in range(0, n):
        c, D = solver_cost(model, n - j, m)
        c += j * log2(q)
        if c < best[0]:
            best = (c, j, D)
    return best


def underdetermined(model, N, m, q, prep):
    """Best cost for one solution of m quadrics in N >= m variables: (log2 cost, description)."""
    if prep == "plain":
        c, j, D = hybrid(model, m, m, q)
        return c, f"{m} eqs, {m}-{j} vars, D={D}"
    best = (INF, "")
    for k in range(0, m - 1):
        a = (N - k) // (m - k) - 1
        me, nv = m - a, m - k - a
        if nv < 1:
            break
        c, j, D = hybrid(model, nv, me, q)
        c += k * log2(q)
        if c < best[0]:
            best = (c, f"k={k}, {me} eqs, {nv}-{j} vars, D={D}")
    return best


MODELS = ["xl0", "xl1", "f5_2", "f5_2.37", "f5_2.81"]


def estimates():
    q = 256
    print("=== Part 1: estimates over F_256 (log2 field multiplications; +7.1 for bit operations)")
    for (N, M) in [(119, 45), (112, 44)]:
        print(f"\n--- (N, M) = ({N}, {M})")
        print(f"{'model':8s} {'prep':5s} {'direct':>7s} {'C1 unit':>8s} {'step':>5s} {'tau*':>6s} "
              f"{'C1(17)':>7s} {'C1(17)-direct':>13s}   direct / C1 configuration")
        for prep in ("plain", "tw"):
            for model in MODELS:
                d, dd = underdetermined(model, N, M, q, prep)
                u, ud = underdetermined(model, N, M - 1, q, prep)
                step = d - u
                taustar = 2 ** (log2(q) - step)
                c17 = u + log2(q / 17)
                print(f"{model:8s} {prep:5s} {d:7.1f} {u:8.1f} {step:5.2f} {taustar:6.1f} {c17:7.1f} "
                      f"{c17 - d:+13.2f}   {dd} / {ud}")
        # per-j view in the reference model
        print("  per number j of guesses, model xl0, plain (cost of C1 at tau = 17 in brackets):")
        for j in range(2, 9):
            a, Da = solver_cost("xl0", M - j, M)
            b, Db = solver_cost("xl0", M - j, M - 1)
            print(f"    j={j}: direct D={Da} 2^{8*j + a:.1f};  C1 D={Db} 2^{8*j + b:.1f}/tau "
                  f"[2^{8*j + b - log2(17):.1f}]")
    # the size of one step across neighbouring sizes: how much of tau* is the grid of degrees
    print("\n--- step = log2 H(m) - log2 H(m-1), H(m) = hybrid cost of m quadrics in m variables")
    print(f"{'m':>4s} " + " ".join(f"{mo:>8s}" for mo in MODELS))
    steps = {mo: [] for mo in MODELS}
    for m in range(36, 56):
        row = []
        for mo in MODELS:
            s = hybrid(mo, m, m, q)[0] - hybrid(mo, m - 1, m - 1, q)[0]
            steps[mo].append(s)
            row.append(f"{s:8.2f}")
        print(f"{m:4d} " + " ".join(row))
    print("mean " + " ".join(f"{sum(steps[mo]) / len(steps[mo]):8.2f}" for mo in MODELS))
    print("tau* at the mean step: "
          + " ".join(f"{mo}: {2 ** (8 - sum(steps[mo]) / len(steps[mo])):.0f}" for mo in MODELS))
    print("tau* = 2^(8 - step); C1 at tau gains the factor tau / tau* (a loss if tau < tau*); "
          "the gain is at most tau.")
    # key recovery (not affected by the shifts), same model as mq_estimates.py
    N, M = 119, 45
    ks = (N - 2 * M) * log2(q) + 3 * log2(N)
    it = hybrid("xl0", 2 * N - 3 * M, 3 * M - 2, q)[0]
    print(f"\n--- key recovery for (119, 45), unaffected by shifts: Kipnis-Shamir 2^{ks:.0f}, "
          f"intersection (k = 2) 2^{it:.0f}")
    # PomFRIT: what using m distinct tree prefixes costs in H_2^3 queries
    print("\n--- PomFRIT: completing a proof with the prefix of a group of trees of total width w "
          "needs about 2^(128 - w) H_2^3 queries")
    for desc, w in [("17 distinct prefixes, the 8-bit tree", 8), ("17 distinct prefixes, a 7-bit tree", 7),
                    ("two groups, 9 trees of 7 bits", 63), ("two groups, 8 + 7*7 bits", 57),
                    ("one tree split off, the other 16", 113), ("one tree split off, that tree", 7)]:
        print(f"    {desc:40s} w = {w:3d}: 2^{128 - w}")


# ---------------------------------------------------------------- part 2: toy experiments

TOY_FULL = [  # q, N, M, jmin, jmax, target solutions, seconds per batch
    (16, 21, 8, 2, 5, 400, 20),
    (16, 24, 9, 2, 6, 400, 20),
    (16, 26, 10, 3, 6, 400, 20),
    (16, 29, 11, 3, 6, 400, 20),
    (256, 16, 6, 2, 4, 300, 40),
    (256, 24, 9, 2, 4, 300, 20),
    (256, 29, 11, 2, 4, 300, 20),
]
TOY_QUICK = [
    (16, 21, 8, 3, 5, 150, 5),
    (16, 24, 9, 3, 5, 150, 5),
    (256, 16, 6, 2, 3, 100, 10),
    (256, 24, 9, 3, 4, 100, 5),
]


def wied(n, D):
    return 3 * comb(n + D, D) ** 2 * comb(n + 2, 2)


def toy(quick, only=None):
    here = os.path.dirname(os.path.abspath(__file__))
    tmp = tempfile.mkdtemp(prefix="c1_toy_")
    exe = os.path.join(tmp, "c1_toy")
    subprocess.run(["gcc", "-O3", "-march=native", "-fopenmp", "-o", exe,
                    os.path.join(here, "c1_toy.c"), "-lm"], check=True)
    print("\n=== Part 2: toy UOV keys, hybrid XL with dense elimination")
    print("D0/D1: degree predicted by the series with '<= 0' / '<= 1'; Dm: measured.")
    print("sols/exp: solutions found / calls * q^-j (direct), calls * q^-(j-1) (C1).")
    print("W: multiplications per solution; measured if >= 30 solutions, else (marked ~) "
          "mults per call * q^j or q^(j-1).")
    summary = []
    configs = TOY_QUICK if quick else TOY_FULL
    if only is not None:
        configs = [configs[i] for i in only]
    for (q, N, M, jmin, jmax, target, secs) in configs:
        out = subprocess.run([exe, str(q), str(N), str(M), "1", str(jmin), str(jmax), str(target),
                              str(secs)], check=True, capture_output=True, text=True).stdout
        print(f"\n--- q = {q}, (N, M) = ({N}, {M})")
        best = {0: (INF, None), 1: (INF, None)}
        bestw = {0: (INF, None), 1: (INF, None)}
        bestd = {0: (INF, None), 1: (INF, None)}
        chi = {}
        for line in out.splitlines():
            if line.startswith(("direct", "C1")) and "chi2=" in line:
                chi[int(line.split("j=")[1].split()[0])] = line.split("chi2=")[1]
            if line.startswith(("direct", "C1")) and "skipped" in line:
                print("  " + line)
            if not line.startswith("@"):
                continue
            f = line.split()
            proj, j, D0, D1, Dm, D = (int(x) for x in f[4:10])
            calls, _with_sol, sols = (int(x) for x in f[10:13])
            mults = float(f[13])
            n = M - j
            p = q ** -(j - proj)  # expected solutions per call
            exp = calls * p
            per_call = mults / calls
            W = mults / sols if sols >= 30 else per_call / p
            mark = " " if sols >= 30 else "~"
            Wm = wied(n, D) / p  # the Wiedemann model at the degree used
            txt = (f"  {'C1    ' if proj else 'direct'} j={j} n={n} eqs={M - proj}: D0={D0} D1={D1} "
                   f"Dm={Dm}; calls={calls} sols/exp={sols}/{exp:.1f}; mults/call=2^{log2(per_call):.1f} "
                   f"(model 2^{log2(wied(n, D)):.1f}); W={mark}2^{log2(W):.2f} (model 2^{log2(Wm):.2f})")
            if proj:
                land = dict((int(a), int(b)) for a, b in (x.split(":") for x in f[f.index("land") + 1:]))
                txt += f"; chi2 of mu {chi.get(j, '?')}; landings tau:found/expected " + " ".join(
                    f"{t}:{c}/{sols * t / q:.1f}" for t, c in sorted(land.items()) if t < q)
            print(txt)
            if W < best[proj][0]:
                best[proj] = (W, j)
            if Wm < bestw[proj][0]:
                bestw[proj] = (Wm, j)
            Wd = comb(n + D, D) ** 2.81 / p  # dense linear algebra, exponent 2.81
            if Wd < bestd[proj][0]:
                bestd[proj] = (Wd, j)
        (wd, jd), (wc, jc) = best[0], best[1]
        (md, mjd), (mc, mjc) = bestw[0], bestw[1]
        ts, tsm = q * wc / wd, q * mc / md
        tsd = q * bestd[1][0] / bestd[0][0]
        print(f"  best direct: j={jd}, 2^{log2(wd):.2f} per forgery.  best C1: j={jc}, "
              f"2^{log2(wc):.2f} per solution, 2^{log2(wc * q):.2f}/tau per forgery.")
        print(f"  break-even tau* = {ts:.2f} measured (dense elimination).  Models at the measured "
              f"degrees: {tsm:.2f} for 3 T^2 binom(n+2, 2) (best j: direct {mjd}, C1 {mjc}); "
              f"{tsd:.2f} for T^2.81 (best j: direct {bestd[0][1]}, C1 {bestd[1][1]}).")
        summary.append((q, N, M, jd, jc, ts, tsm, tsd))
    print("\n--- summary: break-even tau* (C1 at tau costs tau*/tau of the direct attack)")
    for (q, N, M, jd, jc, ts, tsm, tsd) in summary:
        print(f"  q={q:3d} (N, M)=({N}, {M}): measured {ts:7.2f} (direct j={jd}, C1 j={jc}); "
              f"model T^2 {tsm:7.2f}; model T^2.81 {tsd:7.2f}")


# ---------------------------------------------------------------- part 3: singular line

def singular_line(seed=1):
    import random
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import shift_algebra_toy as t
    rng = random.Random(seed)
    print("\n=== Part 3: landing by a singular vector, toy keys over F_16")
    for (N, M, trials) in [(8, 3, 100), (10, 4, 20), (11, 4, 20)]:
        key = t.Key(N, M, rng)
        z = key.D([0] * M, rng)
        assert any(z) and key.P(z) == [0] * M
        c = t.rvec(M, rng)
        piv = next(i for i in range(M) if c[i])
        ci = t.inv(c[piv])

        def proj(y):  # pi_c in coordinates: kill the component along c
            mu = t.mul(y[piv], ci)
            return [a ^ t.mul(mu, b) for a, b in zip(y, c)], mu

        # W_c = kernel of s -> pi_c(B(s, z))
        cols = [proj(key.B([1 if j == i else 0 for j in range(N)], z))[0] for i in range(N)]
        W = t.kernel([[cols[i][k] for i in range(N)] for k in range(M)], N)
        assert len(W) == N - M + 1, len(W)
        found = tries = 0
        for _ in range(trials):
            tgt = t.rvec(M, rng)
            while True:
                tries += 1
                s = [0] * N
                for b in W:
                    s = t.vadd(s, t.vscale(rng.randrange(t.Q), b))
                d, mu = proj(t.vadd(key.P(s), tgt))
                if any(d):
                    continue
                beta = proj(key.B(s, z))[1]  # B(s, z) = beta c
                assert key.B(s, z) == t.vscale(beta, c)
                if beta == 0:
                    continue
                lam = t.mul(mu, t.inv(beta))
                assert key.P(t.vadd(s, t.vscale(lam, z))) == tgt
                found += 1
                break
        print(f"  (N, M) = ({N}, {M}): dim W_c = {len(W)} = N - M + 1; {found} preimages of random "
              f"targets, {tries / found:.0f} random points of W_c each (q^(M-1) = {t.Q ** (M - 1)})")


def main():
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    if what in ("estimates", "both", "all"):
        estimates()
    if what in ("line", "all"):
        singular_line()
    if what in ("toy", "both", "all"):
        only = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else None
        toy(len(sys.argv) > 2 and sys.argv[2] == "quick", only)


if __name__ == "__main__":
    main()
