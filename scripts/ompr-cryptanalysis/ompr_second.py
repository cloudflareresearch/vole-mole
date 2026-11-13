#!/usr/bin/env python3
"""Second pass on the cryptanalysis of OMPR: experiments and estimates for
lean/docs/security/ompr-cryptanalysis-2.md.

Toy keys are those of ompr_toy.py (uniform block S).  Pure Python except `scale`, which builds
scripts/ompr-shift-algebra/c1_toy.c with gcc.

  fourier  E8   Exact formula for the character sums of the bad vinegar set (Theorem H):
                X(w) = sum over matrices T != 0 with L*(T) = w of kappa(rank T),
                kappa(r) = (-1)^(r-1) q^(V - rM + r(r-1)/2) prod_{i=1}^{M-r} (1 - q^-i).
                Checked as an identity of rationals for every w, on every key.
  moment4  E9   Fourth moment (Theorem T): sum_{w != 0} X(w)^4 against the proved bound B4 and
                against the Gaussian value; the bound on the largest character that follows.
  degree   E10  Statistics of degree d of the vinegar: all characters psi(g(v)) of a family of
                polynomials g at once (a Walsh-Hadamard transform of a push-forward).  Mean square
                against Theorem V, largest value against the Gaussian extreme value.
  scale    E11  The class attack P1: solve pi_h(P(s)) = 0 (M - 1 quadrics), then scale.  Toy XL
                experiment: landing rate and work per forgery against the direct attack.
  quantum       Estimates: Grover-hybrid XL forgery, Grover Kipnis-Shamir, depth limits.
  multi         Estimates: the class attack, collinear shifts on top of it, joint systems for
                d targets, targets on a flat.
  table         The figures at (119, 45, 256) quoted in the note.

Usage: ompr_second.py [fourier|moment4|degree|scale|quantum|multi|table|all] [seed]
Run under a memory cap.  `all` without `scale` takes about five minutes on one core and less
than 2 GB; `scale` uses 8 threads for about ten minutes.
"""
import os
import random
import shutil
import subprocess
import sys
import tempfile
from fractions import Fraction
from math import comb, log, log2, sqrt

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "ompr-shift-algebra"))
from ompr_toy import GF, Key, all_vectors, bad_table, char_mask, delta_unif, fwht, trace  # noqa: E402
from c1_experiments import INF, hybrid, solver_cost, underdetermined  # noqa: E402


def lg(x):
    """log2 of a positive rational of any size."""
    x = Fraction(x)
    return log2(x.numerator) - log2(x.denominator)


# ---------- Theorem H: the Fourier transform of the bad set ----------
def kappa(q, V, M, r):
    """Coefficient of a matrix of rank r >= 1 in X(w); for r = 0 the value q^V delta_unif."""
    if r == 0:
        p = Fraction(1)
        for i in range(1, M + 1):
            p *= 1 - Fraction(1, q ** i)
        return q ** V * (1 - p)
    p = Fraction((-1) ** (r - 1)) * Fraction(q) ** (V - r * M + r * (r - 1) // 2)
    for i in range(1, M - r + 1):
        p *= 1 - Fraction(1, q ** i)
    return p


def rank_counts(q, M):
    """Number of M x M matrices of rank r over F_q."""
    out = []
    for r in range(M + 1):
        num = den = 1
        for i in range(r):
            num *= (q ** M - q ** i) ** 2
            den *= q ** r - q ** i
        out.append(num // den)
    assert sum(out) == q ** (M * M)
    return out


def adjoint_images(key):
    """For every matrix T: (rank of T, mask of w = L*(T)), w_i = sum_{k,j} T[k][j] C_k[i][j]."""
    gf, M, V = key.gf, key.M, key.V
    mt = gf.mt
    cols = [[[key.C[k][i][j] for i in range(V)] for j in range(M)] for k in range(M)]
    for t in all_vectors(gf, M * M):
        T = [t[k * M:(k + 1) * M] for k in range(M)]
        w = [0] * V
        for k in range(M):
            for j in range(M):
                a = T[k][j]
                if a:
                    m = mt[a]
                    w = [x ^ m[c] for x, c in zip(w, cols[k][j])]
        yield gf.rank(T, M), char_mask(gf, w)


def exp_fourier(seed):
    print("E8  Theorem H: X(w) = sum_{T != 0, L*(T) = w} kappa(rank T), exactly, for every w")
    for k, V, M in ((2, 3, 2), (2, 4, 3), (2, 5, 3), (2, 7, 3), (4, 3, 2), (4, 4, 2)):
        gf = GF(k)
        q = gf.q
        rng = random.Random(seed + 77 * V + k)
        key = Key(gf, V + M, M, rng)
        X = fwht(bad_table(key))
        kap = [kappa(q, V, M, r) for r in range(M + 1)]
        acc = [Fraction(0)] * len(X)
        part = [[Fraction(0)] * len(X) for _ in range(M + 1)]
        for r, m in adjoint_images(key):
            acc[m] += kap[r]
            part[r][m] += kap[r]
        bad = sum(1 for a, b in zip(acc, X) if a != b)
        nz = len(X) - 1
        ms = [float(sum(x * x for x in part[r][1:])) / nz for r in range(1, M + 1)]
        tot = sum(x * x for x in X[1:]) / nz
        r1 = sum(float(a) * b for a, b in zip(part[1][1:], X[1:])) / sqrt(
            float(sum(a * a for a in part[1][1:])) * sum(b * b for b in X[1:]))
        print(f"    F_{q:<2d} V = {V} M = {M}: {len(X)} characters, mismatches {bad}; mean square of "
              f"X {tot:.1f}; of the rank-r parts " + ", ".join(f"r={r + 1}: {x:.1f}" for r, x in enumerate(ms))
              + f"; correlation of X with its rank-one part {r1:.3f}")
    print("    figures at (V, M, q) = (74, 45, 256), log2:")
    q, V, M = 256, 74, 45
    nr = rank_counts(q, M)
    for r in (1, 2, 3):
        kr = kappa(q, V, M, r)
        mean = log2(nr[r]) - 8 * V
        print(f"      rank {r}: |kappa| = 2^{lg(abs(kr)):.1f}; matrices of this rank over a given "
              f"w: 2^{mean:.1f} on average; standard deviation of their sum 2^{lg(abs(kr)) + mean / 2:.1f}")


# ---------- Theorem T: the fourth moment ----------
def b4_bound(q, V, M):
    """(B4, eta4): E sum_{w != 0} X(w)^4 <= B4 for a uniform block S; eta4 = sum_{T != 0} fhat(T)^4."""
    d = Fraction(kappa(q, V, M, 0), q ** V)
    nr = rank_counts(q, M)
    eta = sum(nr[r] * (kappa(q, V, M, r) / q ** V) ** 4 for r in range(1, M + 1))
    planes = Fraction((q ** V - 1) * (q ** (V - 1) - 1), (q * q - 1) * (q - 1))
    b4 = (q ** (4 * V) * eta
          + q ** V * (planes * q ** 6 * d * d + (q ** V - 1) * (q * q + q + 1) * d + 1))
    return b4, eta


def exp_moment4(seed, keys=12):
    print("E9  Theorem T: E sum_{w != 0} X(w)^4 <= B4 (uniform block S)")
    for k, V, M in ((2, 4, 3), (2, 5, 3), (2, 6, 4), (2, 8, 3), (4, 3, 2), (4, 4, 3)):
        gf = GF(k)
        q = gf.q
        s4, s2, mx = 0.0, 0.0, 0.0
        for i in range(keys):
            rng = random.Random(seed + 1000 * i + 31 * V + k)
            key = Key(gf, V + M, M, rng)
            X = fwht(bad_table(key))
            s4 += sum(x ** 4 for x in X[1:])
            s2 += sum(x * x for x in X[1:])
            mx = max(mx, max(abs(x) for x in X[1:]))
        s4 /= keys
        s2 /= keys * (q ** V - 1)
        b4, _ = b4_bound(q, V, M)
        gauss = 3 * s2 * s2 * (q ** V - 1)
        print(f"    F_{q:<2d} V = {V} M = {M}: mean sum X^4 = {s4:.4g}; B4 = {float(b4):.4g} "
              f"(ratio {s4 / float(b4):.3f}); Gaussian value 3 sigma^4 (q^V - 1) = {gauss:.4g}; "
              f"largest |X| over the keys {mx:.0f}, B4^(1/4) = {float(b4) ** 0.25:.0f}")
    q, V, M = 256, 74, 45
    b4, eta = b4_bound(q, V, M)
    d = delta_unif(q, M)
    lb = lg(b4)
    print(f"    (74, 45, 256): eta4 = 2^{lg(eta):.1f}; B4 = 2^{lb:.2f}; with probability 1 - eps over "
          f"the key every character has |X(w)| <= 2^{lb / 4:.2f} eps^(-1/4), bias <= "
          f"2^{lb / 4 - 8 * V - log2(1 - 2 * d):.2f} eps^(-1/4)")
    for e in (0, 64, 128):
        bias = lb / 4 - 8 * V - log2(1 - 2 * d) + e / 4
        print(f"      eps = 2^-{e}: bias <= 2^{bias:.1f}, answers needed >= 2^{-2 * bias:.1f}")


# ---------- statistics of degree d ----------
def monomials(V, deg):
    """Exponent tuples of total degree deg."""
    out = []

    def rec(i, left, cur):
        if i == V - 1:
            out.append(tuple(cur + [left]))
            return
        for e in range(left, -1, -1):
            rec(i + 1, left - e, cur + [e])
    rec(0, deg, [])
    return out


def family_transform(key, mons, weights):
    """Y[g] = sum_{v != 0} weights[v] psi(g(v)) for all g in the span of `mons` (coefficients in F).
    Returns the list Y indexed by the bits of g, and the number of projective points."""
    gf, V = key.gf, key.V
    mt, k = gf.mt, gf.k
    A = [0.0] * (1 << (k * len(mons)))
    for idx, v in enumerate(all_vectors(gf, V)):
        if idx == 0:
            continue
        pw = [[1] * 4 for _ in range(V)]
        for i in range(V):
            for e in range(1, 4):
                pw[i][e] = mt[pw[i][e - 1]][v[i]]
        code = 0
        for mon in mons:
            val = 1
            for i, e in enumerate(mon):
                if e:
                    val = mt[val][pw[i][e]]
            for b in range(k):
                code = (code << 1) | trace(gf, mt[1 << b][val])
        A[code] += weights[idx]
    return fwht(A)


def gamma_square(key, mons, samples, rng):
    """Average over g in the family of sum over projective points p of |sum_{v in p} psi(g(v))|^2,
    estimated on `samples` random g."""
    gf, V = key.gf, key.V
    mt, q = gf.mt, gf.q
    pts = [v[:] for v in all_vectors(gf, V) if next((t for t in v if t), 0) == 1]
    tot = 0.0
    for _ in range(samples):
        coef = [rng.randrange(q) for _ in mons]
        for p in pts:
            s = 0
            for lam in range(1, q):
                v = [mt[lam][x] for x in p]
                g = 0
                for c, mon in zip(coef, mons):
                    if c:
                        val = c
                        for i, e in enumerate(mon):
                            for _ in range(e):
                                val = mt[val][v[i]]
                        g ^= val
                s += -1 if trace(gf, g) else 1
            tot += s * s
    return tot / samples


def exp_degree(seed, keys=16):
    print("E10 statistics of degree d of the vinegar: Y(g) = sum_{v != 0} (1_bad(v) - delta_unif) psi(g(v))")
    print("    Theorem V: E_key Y(g)^2 = delta(1 - delta) sum_p |Gamma_p(g)|^2 <= delta(1 - delta)(q - 1)(q^V - 1)")
    configs = [
        (2, 4, 3, "linear", [m for m in monomials(4, 1)]),
        (2, 4, 3, "all quadrics", monomials(4, 2)),
        (2, 4, 3, "10 cubic monomials", monomials(4, 3)[:10]),
        (2, 6, 4, "linear", monomials(6, 1)),
        (2, 6, 4, "10 quadratic monomials", monomials(6, 2)[:10]),
        (2, 6, 4, "linear + 4 quadratic monomials", monomials(6, 1) + monomials(6, 2)[:4]),
        (2, 6, 4, "10 cubic monomials", monomials(6, 3)[:10]),
        (4, 3, 2, "linear", monomials(3, 1)),
        (4, 3, 2, "5 quadratic monomials", monomials(3, 2)[:5]),
    ]
    for k, V, M, name, mons in configs:
        gf = GF(k)
        q = gf.q
        d = delta_unif(q, M)
        nfam = (1 << (k * len(mons))) - 1
        ms, mx, gsz = 0.0, 0.0, 0.0
        rng = random.Random(seed + 5)
        for i in range(keys):
            key = Key(gf, V + M, M, random.Random(seed + 1000 * i + 31 * V + k))
            tab = bad_table(key)
            Y = family_transform(key, mons, [t - d for t in tab])
            ms += sum(y * y for y in Y[1:]) / nfam
            gsz += (q ** V - sum(tab)) / keys
            mx = max(mx, max(abs(y) for y in Y[1:]))
            if i == 0:
                g2 = gamma_square(key, mons, 40, rng)
        ms /= keys
        model = d * (1 - d) * g2
        cap = d * (1 - d) * (q - 1) * (q ** V - 1)
        sig = sqrt(model)
        print(f"    F_{q:<2d} V = {V} M = {M}, {name} ({k * len(mons)} bits): mean Y^2 = {ms:.1f}, "
              f"Theorem V {model:.1f} (ratio {ms / model:.2f}; cap {cap:.1f}); largest |Y| = "
              f"{mx / sig:.2f} sigma, Gaussian extreme value sqrt(2 ln(2 #g)) = "
              f"{sqrt(2 * log(2 * nfam)):.2f}; largest bias {mx / gsz:.4f}")
    print("    figures at (74, 45, 256): rms bias of a fixed statistic <= 2^-296.0 (2^-300.0 without the")
    print("    cone factor); largest bias over all g of degree <= d, Gaussian heuristic, and answers needed:")
    V = 74
    dl = delta_unif(256, 45)
    for dd in (1, 2, 3, 4, 8, 16, 45, 255):
        nco = comb(V + dd, dd) - 1
        sigma = 0.5 * (log2(dl) + log2(1 - dl) + 8 * V) + (4 if dd % 255 == 0 else 0)
        mxb = sigma + 0.5 * log2(2 * 8 * nco * log(2)) - 8 * V - log2(1 - dl)
        print(f"      d = {dd:3d}: {nco} coefficients (2^{log2(nco):.1f}); largest bias about 2^{mxb:.1f}; "
              f"answers 2^{-2 * mxb:.1f}")


# ---------- E11: the class attack on toy keys ----------
SCALE_CONFIGS = [  # q, N, M, jmin, jmax, target solutions, seconds per batch
    (16, 21, 8, 2, 5, 400, 5),
    (16, 24, 9, 2, 6, 400, 5),
    (16, 26, 10, 3, 6, 400, 5),
    (256, 16, 6, 2, 4, 300, 8),
    (256, 24, 9, 2, 4, 300, 8),
]


def exp_scale():
    src = os.path.join(HERE, "..", "ompr-shift-algebra", "c1_toy.c")
    tmp = tempfile.mkdtemp(prefix="ompr_scale_")
    exe = os.path.join(tmp, "c1_toy")
    subprocess.run(["gcc", "-O3", "-march=native", "-fopenmp", "-o", exe, src, "-lm"], check=True)
    env = dict(os.environ, OMP_NUM_THREADS=os.environ.get("OMP_NUM_THREADS", "8"))
    print("E11 class attack P1: solve pi_h(P(s)) = 0 (M - 1 quadrics), P(s) = nu h, scale by 1/sqrt(nu)")
    print("    hybrid XL with dense elimination (c1_toy.c, cmode 1); W = multiplications per forgery")
    for (q, N, M, jmin, jmax, target, secs) in SCALE_CONFIGS:
        out = subprocess.run([exe, str(q), str(N), str(M), "1", str(jmin), str(jmax), str(target),
                              str(secs), "0", "1"], check=True, capture_output=True, text=True,
                             env=env).stdout
        best = {0: (INF, None, ""), 1: (INF, None, "")}
        sols = land = 0
        for line in out.splitlines():
            if not line.startswith("@"):
                continue
            f = line.split()
            proj, j, D = int(f[4]), int(f[5]), int(f[9])
            calls, nsol, mults = int(f[10]), int(f[12]), float(f[13])
            if proj:
                ok = int(f[f.index("scale") + 1])
                sols += nsol
                land += ok
                W = mults / ok if ok >= 30 else mults / calls * q ** (j - 1) * q / (q - 1)
                note = f"{ok} forgeries of {nsol} solutions in {calls} calls" if ok >= 30 else "by calls"
            else:
                W = mults / nsol if nsol >= 30 else mults / calls * q ** j
                note = f"{nsol} forgeries in {calls} calls" if nsol >= 30 else "by calls"
            if W < best[proj][0]:
                best[proj] = (W, j, f"D={D}, {note}")
        (wd, jd, nd), (wc, jc, nc) = best[0], best[1]
        print(f"    F_{q:<3d} ({N}, {M}): direct j={jd} W=2^{log2(wd):.2f} ({nd}); class attack j={jc} "
              f"W=2^{log2(wc):.2f} ({nc}); gain 2^{log2(wd / wc):.2f}; scalable solutions {land}/{sols}"
              f" (expected fraction {(q - 1) / q:.4f})")
        # the model, plain preprocessing, dense exponent as measured in [SA] and Wiedemann
        for nm, mdl in (("3 T^2 binom(n+2,2)", "xl1"),):
            a = hybrid(mdl, M, M, q)[0]
            b = hybrid(mdl, M - 1, M - 1, q)[0]
            print(f"        model {nm}, plain: direct 2^{a:.2f}, class attack 2^{b:.2f}, gain 2^{a - b:.2f}")
    shutil.rmtree(tmp, ignore_errors=True)


# ---------- estimates ----------
Q = 256
GATES_PER_MUL = log2(2 * 64 + 8)  # the bit-operation count of [UOS] B.5, used as a gate count


def tw_configs(N, m):
    """(k, equations, variables) after Thomae-Wolf with k guesses (Furue-Nakamura-Takagi)."""
    for k in range(0, m - 1):
        a = (N - k) // (m - k) - 1
        if m - k - a < 1:
            break
        yield k, m - a, m - k - a


def grover_hybrid(N, m, maxdepth=None):
    """Grover over all guessed variables, XL-Wiedemann inside.  Returns (log2 gates, log2 mults,
    guesses, equations, variables, degree).  Depth of one iteration: 3 T matrix-vector products
    in sequence, each counted as depth 1 (favourable to the attacker)."""
    best = (INF,)
    for k, me, nv in tw_configs(N, m):
        for j in range(0, nv):
            c, D = solver_cost("xl0", nv - j, me)
            if c == INF:
                continue
            it = 4 * (k + j)
            depth = log2(3) + log2(comb(nv - j + D, D))
            if maxdepth is None or it + depth <= maxdepth:
                tot = it + c
            else:
                tot = 2 * it + depth + c - maxdepth
            if tot < best[0]:
                best = (tot, it + c, k + j, me, nv - j, D)
    return (best[0] + GATES_PER_MUL,) + best[1:]


def exp_quantum():
    N, M = 119, 45
    print("Quantum estimates at (119, 45, 256).  log2; gates = multiplications * 2^7.1 (optimistic).")
    for name, n, m in (("forgery, 45 equations (B0)", N, M), ("forgery, class attack P1 (44 equations)", N - 1, M - 1)):
        c = underdetermined("xl0", n, m, Q, "tw")
        g = grover_hybrid(n, m)
        print(f"    {name}: classical 2^{c[0]:.1f} mults ({c[1]}); Grover-hybrid 2^{g[1]:.1f} mults, "
              f"2^{g[0]:.1f} gates ({g[2]} guessed variables, {g[3]} eqs in {g[4]} vars, D={g[5]})")
        for md in (40, 64, 96):
            gd = grover_hybrid(n, m, md)
            print(f"        MAXDEPTH 2^{md}: 2^{gd[0]:.1f} gates ({gd[2]} guesses, D={gd[5]}); "
                  f"AES-128 key search: 2^{170 - md}")
    ks_it = (N - 2 * M) * 8
    ks_mul = 3 * log2(N)
    print(f"    Kipnis-Shamir: classical 2^{ks_it + ks_mul:.1f} mults; Grover 2^{ks_it / 2 + ks_mul:.1f} mults, "
          f"2^{ks_it / 2 + ks_mul + GATES_PER_MUL:.1f} gates, depth >= 2^{ks_it / 2 + 2 * log2(N):.0f}")
    for md in (40, 64, 96):
        d1 = 2 * log2(N)
        print(f"        MAXDEPTH 2^{md}: 2^{ks_it + d1 + ks_mul + GATES_PER_MUL - md:.1f} gates")
    # intersection attack: 3M - 2 equations in 2N - 3M variables, Grover on the hybrid guesses
    n, m = 2 * N - 3 * M, 3 * M - 2
    cl = hybrid("xl0", n, m, Q)
    best = (INF,)
    for j in range(0, 40):
        c, D = solver_cost("xl0", n - j, m)
        if c + 4 * j < best[0]:
            best = (c + 4 * j, j, D)
    print(f"    intersection: classical 2^{cl[0]:.1f} mults (j={cl[1]}); Grover on the guesses "
          f"2^{best[0]:.1f} mults, 2^{best[0] + GATES_PER_MUL:.1f} gates (j={best[1]}, D={best[2]})")
    print("    with the oracle (classical calls, quantum offline work):")
    print(f"      search a list of W images for one of n targets: sqrt(2^352 / n) evaluations; "
          f"n = 2^64: 2^{(352 - 64) / 2:.0f}")
    print(f"      collision between images and hashed targets (BHT): 2^{360 / 3:.0f} with 2^{360 / 3:.0f} qRAM; "
          f"classical 2^{360 / 2:.0f}")
    print(f"      vinegar collisions (K1): the data hold one with probability Q^2 2^-585; no quantum gain")
    print(f"      an oil vector in the span of answers: Grover over q^29 zeros, 2^{29 * 4} forgery-sized steps")


def exp_multi():
    N, M = 119, 45
    print("Multi-target and class attacks at (119, 45, 256), log2 multiplications (model of [SA] 4.1)")
    rows = {}
    for prep in ("plain", "tw"):
        for mdl in ("xl0", "f5_2", "f5_2.37", "f5_2.81"):
            h45 = underdetermined(mdl, N, M, Q, prep)
            h44 = underdetermined(mdl, N - 1, M - 1, Q, prep)
            h43 = underdetermined(mdl, N - 1, M - 2, Q, prep)
            p1 = h44[0] + log2(Q / (Q - 1))
            step = h44[0] - h43[0]
            ts = (Q + 1) / 2 ** step
            c17 = h43[0] + log2((Q + 1) / 17)
            rows[(prep, mdl)] = (h45[0], p1, c17)
            print(f"    {mdl:8s} {prep:5s}: direct (45 eqs) {h45[0]:6.1f}; class attack P1 (44 eqs) {p1:6.1f} "
                  f"[{h44[1]}]; gain 2^{h45[0] - p1:.2f}; collinear shifts on top (43 eqs): step "
                  f"{step:.2f}, tau* = {ts:.1f}, C1' at tau = 17: {c17:6.1f} ({c17 - p1:+.2f})")
    print(f"    bit operations of P1 in the reference model: 2^{rows[('tw', 'xl0')][1] + GATES_PER_MUL:.1f}")
    for (n2, m2) in ((112, 44),):
        a = underdetermined("xl0", n2, m2, Q, "tw")[0]
        b = underdetermined("xl0", n2 - 1, m2 - 1, Q, "tw")[0]
        print(f"    ({n2}, {m2}): direct 2^{a:.1f}, class attack 2^{b:.1f} mults "
              f"(2^{a + GATES_PER_MUL:.1f}, 2^{b + GATES_PER_MUL:.1f} bit operations)")
    print("    d targets on one d-flat through 0 (one solve, 45 - d quadrics, lands on a class w.p. about d / q^(d-1)):")
    for d in (1, 2, 3, 4):
        h = underdetermined("xl0", N - 1, M - d, Q, "tw")
        land = log2(d * (Q - 1) / (Q ** d - 1))
        print(f"      d = {d}: solve 2^{h[0]:.1f}, per forgery 2^{h[0] - land:.1f}  [{h[1]}]")
    print("    joint system: a d-space Z with P(Z) inside the span of d targets, then d quadrics in d unknowns:")
    for d in (1, 2, 3):
        eqs = comb(d + 1, 2) * (M - d)
        var = d * (N - d)
        best = (INF, None, None)
        for k, me, nv in tw_configs(var, eqs):
            if k > 12:
                break
            for j in range(0, min(nv, 30)):
                c, D = solver_cost("xl0", nv - j, me)
                if c + 8 * (k + j) < best[0]:
                    best = (c + 8 * (k + j), me, D)
        print(f"      d = {d}: {eqs} quadrics in {var} unknowns; 2^{best[0]:.0f} "
              f"({best[1]} eqs after Thomae-Wolf, D = {best[2]}); per target 2^{best[0] - log2(d):.0f}")
    print(f"    budget: c calls outside the challenge classes need c + 1 forgeries; D(0) and the singular "
          f"line: 2 forgeries, 2^{rows[('tw', 'xl0')][1] + 1:.1f}")


def exp_table():
    exp_fourier_figures_only()
    exp_quantum()
    exp_multi()


def exp_fourier_figures_only():
    q, V, M = 256, 74, 45
    b4, eta = b4_bound(q, V, M)
    d = delta_unif(q, M)
    lb = lg(b4)
    print(f"Figures at (V, M, q) = (74, 45, 256): delta_unif = 2^{log2(d):.3f}; eta4 = 2^{lg(eta):.1f}; "
          f"B4 = 2^{lb:.2f}; largest character bias <= 2^{lb / 4 - 8 * V - log2(1 - 2 * d):.2f} eps^(-1/4)")
    print(f"    rms bias of a fixed statistic of any degree <= 2^"
          f"{0.5 * (log2(d) + log2(255) - 8 * V - log2(1 - d)):.1f}")


def main():
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    table = {"fourier": lambda: exp_fourier(seed), "moment4": lambda: exp_moment4(seed),
             "degree": lambda: exp_degree(seed), "scale": exp_scale, "quantum": exp_quantum,
             "multi": exp_multi, "table": exp_table}
    if what == "all":
        for name in ("fourier", "moment4", "degree", "quantum", "multi"):
            table[name]()
            print()
    elif what in table:
        table[what]()
    else:
        print(__doc__)
        sys.exit(2)


if __name__ == "__main__":
    main()
