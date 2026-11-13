#!/usr/bin/env python3
"""Review of the class attack P1 (lean/docs/security/ompr-cryptanalysis-2.md, section 8).

  estimates   Forgery cost with and without P1 in the cost model of the UOV round-3
              specification, section 4.2: hybrid Wiedemann XL, after Thomae-Wolf or after
              Hashimoto's reduction, whichever is cheaper.  log2 bit operations.
  toy [quick | i,j,..]
              Independent toy experiment (p1_review_toy.c): direct attack and P1, each with
              plain variable fixing and with the Thomae-Wolf step, hybrid XL, dense elimination.

Run under a memory cap.  `toy` takes about 15 minutes on 8 threads (`quick`: 2); `toy 0,1` runs the first two keys.
"""
import os
import shutil
import subprocess
import sys
import tempfile
from functools import lru_cache
from math import comb, log2

INF = float("inf")
HERE = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------- estimates
@lru_cache(None)
def xl_degree(n, m, thr=0):
    """Smallest d with [t^d] (1 - t^2)^m / (1 - t)^(n+1) <= thr, or None."""
    for d in range(1, 400):
        c = sum((-1) ** i * comb(m, i) * comb(n + d - 2 * i, d - 2 * i)
                for i in range(0, min(m, d // 2) + 1))
        if c <= thr:
            return d
    return None


def mul_bits(q):
    return log2(2 * log2(q) ** 2 + log2(q))


@lru_cache(None)
def mq(q, n, m):
    """MQ(q; n, m) of the specification: (log2 bit operations, guesses k, degree)."""
    if n == 0:
        return (0.0, 0, 0)
    best = (INF, None, None)
    for k in range(0, n):
        d = xl_degree(n - k, m)
        if d is None:
            continue
        c = (k * log2(q) + log2(3) + log2(comb(n - k + 2, 2)) + 2 * log2(comb(n - k + d, d))
             + mul_bits(q))
        if c < best[0]:
            best = (c, k, d)
    # all variables guessed (needed for the tiny square systems inside Hashimoto's formula)
    ex = n * log2(q) + log2(m * comb(n + 2, 2)) + mul_bits(q)
    return best if best[0] <= ex else (ex, n, 0)


def log2sum(*xs):
    top = max(xs)
    return top + log2(sum(2 ** (x - top) for x in xs))


def thomae_wolf(q, n, m):
    a = n // m - 1
    c, k, d = mq(q, m - a, m - a)
    return c, f"{m - a} eqs in {m - a} vars, k = {k}, D = {d}"


def hashimoto(q, n, m):
    best = (INF, "")
    for a in range(1, m):
        for c in range(0, m - a):
            if n < max((a + 1) * (m - c - a + 1), a * (m - c) - (a - 1) ** 2 + c):
                continue
            big, k, d = mq(q, m - a - c, m - a)
            tot = log2sum(log2(m - a - c + 1) + mq(q, a, a)[0],
                          c * log2(q) + log2sum(mq(q, a - 1, a - 1)[0], big))
            if tot < best[0]:
                best = (tot, f"a = {a}, c = {c}: {m - a} eqs in {m - a - c} vars, k = {k}, D = {d}")
    return best


def spec_direct(q, n, m):
    return min(thomae_wolf(q, n, m), hashimoto(q, n, m))


def class_attack(f, q, n, m, d=1):
    """d targets through one solve: m - d quadrics in n - 1 variables (one coordinate set to 1);
    a solution lies on one of the d lines with probability d (q - 1) / (q^d - 1)."""
    c, desc = f(q, n - 1, m - d)
    return c - log2(d * (q - 1) / (q ** d - 1)), desc


SETS = [("uov-Ip, round 3", 119, 45, 256, 143), ("uov-Ip, rounds 1 and 2", 112, 44, 256, 143),
        ("uov-Is", 160, 64, 16, 143), ("uov-III, round 3", 193, 72, 256, 207),
        ("uov-III, rounds 1 and 2", 184, 72, 256, 207), ("uov-V, round 3", 259, 96, 256, 272),
        ("uov-V, rounds 1 and 2", 244, 96, 256, 272)]


def estimates():
    print("Forgery, log2 bit operations (RAM model of the UOV round-3 specification, section 4.2)")
    for name, n, m, q, level in SETS:
        print(f"\n{name}: (n, m, q) = ({n}, {m}, {q}); NIST level: 2^{level}")
        for label, f in (("Thomae-Wolf", thomae_wolf), ("Hashimoto", hashimoto),
                         ("minimum (spec)", spec_direct)):
            d, dd = f(q, n, m)
            p, pd = class_attack(f, q, n, m)
            print(f"  {label:15s} direct {d:7.2f} [{dd}]\n"
                  f"  {'':15s} P1     {p:7.2f} [{pd}]  gain {d - p:.2f}"
                  f"{'  BELOW the level' if p < level else ''}")
    print("\nd targets in one solve at (119, 45, 256), per forgery (section 3.3 of the note):")
    for d in (1, 2, 3, 4):
        c, desc = class_attack(spec_direct, 256, 119, 45, d)
        print(f"  d = {d}: {c:7.2f} [{desc}]")
    print("\nP1 gain = cost(m) - cost(m - 1) at n = 2.6 m, q = 256, for m = 40..52:")
    for label, f in (("Thomae-Wolf", thomae_wolf), ("minimum (spec)", spec_direct)):
        g = [f(256, int(2.6 * m), m)[0] - class_attack(f, 256, int(2.6 * m), m)[0]
             for m in range(40, 53)]
        print(f"  {label:15s} " + " ".join(f"{x:.1f}" for x in g) + f"   mean {sum(g) / len(g):.2f}")


# ---------------------------------------------------------------- toy experiment
TOY = [  # q, N, M, gmin, gmax, seconds per cell
    (16, 21, 8, 2, 5, 6),
    (16, 24, 9, 2, 6, 6),
    (16, 26, 10, 3, 6, 6),
    (16, 29, 11, 3, 7, 6),
    (256, 16, 6, 1, 3, 8),
    (256, 24, 9, 1, 3, 8),
]


def wiedemann(n, d):
    return log2(3) + 2 * log2(comb(n + d, d)) + log2(comb(n + 2, 2))


def toy(quick, only=None):
    tmp = tempfile.mkdtemp(prefix="p1_review_")
    exe = os.path.join(tmp, "p1_review_toy")
    subprocess.run(["gcc", "-O3", "-march=native", "-fopenmp", "-o", exe,
                    os.path.join(HERE, "p1_review_toy.c")], check=True)
    env = dict(os.environ, OMP_NUM_THREADS=os.environ.get("OMP_NUM_THREADS", "8"))
    print("W = log2 multiplications per forgery (measured when >= 30 forgeries, else per call"
          " times q^g, marked ~).\nWd = the same in the Wiedemann model with the measured degree."
          "  D = measured degree (series <= 0 / <= 1).")
    sel = TOY[:2] + TOY[4:5] if quick else [TOY[i] for i in only] if only else TOY
    for (q, N, M, gmin, gmax, secs) in sel:
        out = subprocess.run([exe, str(q), str(N), str(M), "1", str(gmin), str(gmax),
                              str(2 if quick else secs)], check=True, capture_output=True,
                             text=True, env=env).stdout
        best, bestw, tot = {}, {}, {}
        print(f"\nF_{q} ({N}, {M})")
        for line in out.splitlines():
            f = line.split()
            tw, p1, g, me, n, D, T = (int(x) for x in f[4:11])
            calls, dec, sols, forg, mults = int(f[11]), int(f[12]), int(f[13]), int(f[14]), float(f[15])
            land = log2(q / (q - 1)) if p1 else 0.0
            meas = forg >= 30
            W = log2(mults / forg) if meas else log2(mults / calls) + g * log2(q) + land
            Wd = wiedemann(n, D) + g * log2(q) + land
            key = (tw, p1)
            t = tot.setdefault(key, [0, 0.0, 0, 0])
            t[0] += sols
            t[1] += calls / q ** g
            t[2] += forg
            t[3] += calls - dec
            if W < best.get(key, (INF,))[0]:
                best[key] = (W, g, D, meas)
            if Wd < bestw.get(key, (INF,))[0]:
                bestw[key] = (Wd, g, D)
            print(f"    {'TW' if tw else 'plain':5s} {'P1' if p1 else 'direct':6s} g={g}: {me} eqs, "
                  f"{n} vars, D={D} ({xl_degree(n, me)}/{xl_degree(n, me, 1)}), T={T}, calls {calls}, "
                  f"solutions {sols} (expected {calls / q ** g:.1f}), forgeries {forg}, "
                  f"W={'' if meas else '~'}{W:.2f}, Wd={Wd:.2f}")
        for tw in (0, 1):
            (wd, gd, Dd, md), (wp, gp, Dp, mp) = best[(tw, 0)], best[(tw, 1)]
            s, e, fo, und = tot[(tw, 1)]
            sd, ed, _, undd = tot[(tw, 0)]
            print(f"  {'TW' if tw else 'plain':5s}: direct {'' if md else '~'}{wd:.2f} (g={gd}, D={Dd}); "
                  f"P1 {'' if mp else '~'}{wp:.2f} (g={gp}, D={Dp}); GAIN {wd - wp:.2f}; "
                  f"Wiedemann model at the measured degrees: {bestw[(tw, 0)][0] - bestw[(tw, 1)][0]:.2f}; "
                  f"model 3T^2 binom, series: "
                  f"{mq_toy(q, M - tw) - mq_toy(q, M - 1 - tw) - log2(q / (q - 1)):.2f}")
            print(f"         solutions: direct {sd} for {ed:.1f} expected, P1 {s} for {e:.1f}; "
                  f"P1 forgeries / solutions {fo}/{s} (expected {(q - 1) / q:.4f}); "
                  f"undecided calls {undd} + {und}")
    shutil.rmtree(tmp, ignore_errors=True)


def mq_toy(q, m):
    """min over g of q^g * Wiedemann cost of m quadrics in m - g variables (log2 mults)."""
    return mq(q, m, m)[0] - mul_bits(q)


def main():
    what = sys.argv[1] if len(sys.argv) > 1 else "estimates"
    if what == "estimates":
        estimates()
    elif what == "toy":
        arg = sys.argv[2] if len(sys.argv) > 2 else ""
        toy(arg == "quick", [int(x) for x in arg.split(",")] if arg[:1].isdigit() else None)
    else:
        print(__doc__)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
