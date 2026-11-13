#!/usr/bin/env python3
"""Toy experiments for lean/docs/security/ompr-cryptanalysis.md.

Scaled-down UOV keys over F_4, F_16 and F_256 with the sampler of derive_preimage: the vinegar
is SHAKE256(target || seed || "pqov-derive-preimage" || ctr), retried (at most 255 times) until
the oil system is invertible, and the oil part is solved.  Pure Python, no dependencies.

  law      E1  The answer to a chosen target (0, a point c, a multiple of c) is uniform on the
               good fibre: chi-square over the good vinegars, the seed playing the random oracle.
  fibre    E2  Exact fraction of bad points in every fibre P^{-1}(y) (the distance between the
               sampler and the keyless uniform-fibre sampler).
  fourier  E3  Exact additive-character sums of the bad set: support on the annihilator of the
               oil space, and the mean square against delta(1-delta)(q^V - q + 1) + (1-delta)^2.
  attack   E4  The first-order statistical attack: recover the oil space from answers to
               uniform targets by the largest empirical characters.  Sample threshold against
               1/b^2 (b the largest bias) and q^V / delta.
  collide  E5  Vinegar collisions (projective) among answers, against the birthday estimate;
               each one gives an oil vector.
  annih    E6  Polynomials of degree <= 3 vanishing on the answers (F_256): only those of the
               public ideal.  Positive control: a signer whose vinegars lie in a hyperplane.
  span     E7  Targets covered by the span of r answers, against the span of r random points.
  table        Probabilities and costs at (N, M, q) = (119, 45, 256) quoted in the note.

Usage: ompr_toy.py [law|fibre|fourier|attack|collide|annih|span|table|all] [seed]
Run under a memory cap; `all` takes about four minutes on one core and less than 1 GB.
"""
import hashlib
import random
import sys
from math import comb, exp, factorial, log, log2, sqrt

DST = b"pqov-derive-preimage"


# ---------- fields F_{2^k} ----------
class GF:
    POLY = {2: 0b111, 4: 0b10011, 8: 0x11B}
    GEN = {2: 2, 4: 2, 8: 3}

    def __init__(self, k):
        self.k, self.q = k, 1 << k
        q = self.q
        self.exp = [0] * (2 * q)
        self.log = [0] * q
        x = 1
        for i in range(q - 1):
            self.exp[i] = x
            self.log[x] = i
            x = self._slow(x, self.GEN[k])
        for i in range(q - 1, 2 * q):
            self.exp[i] = self.exp[i - (q - 1)]
        self.mt = [[self._slow(a, b) for b in range(q)] for a in range(q)]

    def _slow(self, a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            a <<= 1
            if a & self.q:
                a ^= self.POLY[self.k]
            b >>= 1
        return r

    def inv(self, a):
        return self.exp[(self.q - 1 - self.log[a]) % (self.q - 1)]

    def sqrt(self, a):
        r = a
        for _ in range(self.k - 1):
            r = self.mt[r][r]
        return r

    def rref(self, rows, ncols):
        """Reduced row echelon form; returns (rows, pivot columns)."""
        mt = self.mt
        A = [r[:] for r in rows]
        piv = []
        r = 0
        for c in range(ncols):
            p = next((i for i in range(r, len(A)) if A[i][c]), None)
            if p is None:
                continue
            A[r], A[p] = A[p], A[r]
            iv = mt[self.inv(A[r][c])]
            A[r] = [iv[t] for t in A[r]]
            Ar = A[r]
            for i in range(len(A)):
                if i != r and A[i][c]:
                    f = mt[A[i][c]]
                    A[i] = [a ^ f[b] for a, b in zip(A[i], Ar)]
            piv.append(c)
            r += 1
            if r == len(A):
                break
        return A[:r], piv

    def rank(self, rows, ncols):
        return len(self.rref(rows, ncols)[1]) if rows else 0

    def solve(self, Amat, b):
        """The solution of the square system A x = b, or None if A is singular."""
        n = len(Amat)
        R, piv = self.rref([r[:] + [bb] for r, bb in zip(Amat, b)], n)
        if len(piv) < n:
            return None
        return [R[i][n] for i in range(n)]


# ---------- toy UOV ----------
class Key:
    """Central map F_k(v, x) = v^t A_k v + v^t C_k x; public point s = (v + O x, x).

    The oil space is {(O x, x)}.  L_v = (sum_i v_i C_k[i][j])_{k,j}, so P(s) = P1(v) + L_v x.
    The C_k are uniform, as the block S = (P1 + P1^t) O + P2 of pqov is for a uniform P2."""

    def __init__(self, gf, N, M, rng):
        self.gf, self.N, self.M, self.V = gf, N, M, N - M
        q, V = gf.q, self.V
        self.O = [[rng.randrange(q) for _ in range(M)] for _ in range(V)]
        self.A = [[[rng.randrange(q) if j >= i else 0 for j in range(V)] for i in range(V)]
                  for _ in range(M)]
        self.C = [[[rng.randrange(q) for _ in range(M)] for _ in range(V)] for _ in range(M)]

    def P1(self, v):
        mt = self.gf.mt
        out = []
        for a in self.A:
            acc = 0
            for i, vi in enumerate(v):
                if vi:
                    t = 0
                    row = a[i]
                    for j in range(i, self.V):
                        if v[j]:
                            t ^= mt[row[j]][v[j]]
                    acc ^= mt[vi][t]
            out.append(acc)
        return out

    def L(self, v):
        mt = self.gf.mt
        out = []
        for c in self.C:
            row = [0] * self.M
            for i, vi in enumerate(v):
                if vi:
                    m = mt[vi]
                    ci = c[i]
                    row = [r ^ m[t] for r, t in zip(row, ci)]
            out.append(row)
        return out

    def central(self, v, x):
        mt = self.gf.mt
        return [p ^ self._dot(row, x) for p, row in zip(self.P1(v), self.L(v))]

    def _dot(self, a, b):
        mt = self.gf.mt
        r = 0
        for s, t in zip(a, b):
            r ^= mt[s][t]
        return r

    def to_public(self, v, x):
        return [vi ^ self._dot(row, x) for vi, row in zip(v, self.O)] + list(x)

    def vin(self, s):
        x = s[self.V:]
        return [si ^ self._dot(row, x) for si, row in zip(s[:self.V], self.O)]

    def P(self, s):
        return self.central(self.vin(s), s[self.V:])

    def good(self, v):
        return self.gf.rank(self.L(v), self.M) == self.M

    def attempt(self, y, v):
        L = self.L(v)
        x = self.gf.solve(L, [a ^ b for a, b in zip(y, self.P1(v))])
        return None if x is None else self.to_public(v, x)

    def derive_preimage(self, y, seed, vinegar_filter=None):
        """The sampler of ov_derive_preimage.  `vinegar_filter` is used only by the positive
        control of E6 (a broken signer)."""
        mask = self.gf.q - 1
        for ctr in range(255):
            h = hashlib.shake_256(bytes(y) + seed + DST + bytes([ctr])).digest(self.V)
            v = [b & mask for b in h]
            if vinegar_filter:
                v = vinegar_filter(v)
            s = self.attempt(y, v)
            if s is not None:
                return s
        raise RuntimeError("derive_preimage failed")


def vec_index(gf, v):
    r = 0
    for a in v:
        r = (r << gf.k) | a
    return r


def all_vectors(gf, n):
    q = gf.q
    v = [0] * n
    while True:
        yield v
        i = n - 1
        while i >= 0 and v[i] == q - 1:
            v[i] = 0
            i -= 1
        if i < 0:
            return
        v[i] += 1


def delta_unif(q, M):
    p = 1.0
    for i in range(1, M + 1):
        p *= 1 - q ** (-i)
    return 1 - p


def fwht(a):
    n, h = len(a), 1
    while h < n:
        for i in range(0, n, 2 * h):
            x = a[i:i + h]
            y = a[i + h:i + 2 * h]
            a[i:i + h] = [p + r for p, r in zip(x, y)]
            a[i + h:i + 2 * h] = [p - r for p, r in zip(x, y)]
        h *= 2
    return a


# ---------- E1: the law of the answer to a chosen target ----------
def exp_law(seed, samples=120000):
    print("E1  law of derive_preimage on chosen targets (F_16, (N, M) = (5, 2))")
    rng = random.Random(seed)
    gf = GF(4)
    key = Key(gf, 5, 2, rng)
    goodv = [v[:] for v in all_vectors(gf, key.V) if key.good(v)]
    cell = {vec_index(gf, v): i for i, v in enumerate(goodv)}
    print(f"    good vinegars {len(goodv)} of {gf.q ** key.V}, delta = "
          f"{1 - len(goodv) / gf.q ** key.V:.4f} (uniform model {delta_unif(gf.q, key.M):.4f})")
    c = [rng.randrange(1, gf.q), rng.randrange(gf.q)]
    mu = 7
    targets = [("0", [0, 0], 1), ("c", c, 1), ("mu*c, rescaled to c", [gf.mt[mu][t] for t in c], mu)]
    for name, y, scale in targets:
        counts = [0] * len(goodv)
        root = gf.inv(gf.sqrt(scale))
        want = y if scale == 1 else c
        for i in range(samples):
            s = key.derive_preimage(y, i.to_bytes(8, "little") + b"/" + name.encode())
            s = [gf.mt[root][t] for t in s]
            assert key.P(s) == want
            counts[cell[vec_index(gf, key.vin(s))]] += 1  # KeyError here would be a bad answer
        e = samples / len(goodv)
        chi = sum((n - e) ** 2 / e for n in counts)
        df = len(goodv) - 1
        print(f"    target {name:22s} chi-square {chi:8.1f} on {df} d.f. "
              f"(z = {(chi - df) / sqrt(2 * df):+.2f}), all answers good")


# ---------- E2: bad fraction of every fibre ----------
def exp_fibre(seed):
    print("E2  fraction of bad points in each fibre P^{-1}(y)")
    for k, N, M in ((2, 7, 2), (2, 8, 3), (4, 5, 2), (4, 6, 2)):
        rng = random.Random(seed + 17 * N + k)
        gf = GF(k)
        key = Key(gf, N, M, rng)
        q, mt = gf.q, gf.mt
        tot = [0] * q ** M
        bad = [0] * q ** M
        nbad = 0
        xs = [x[:] for x in all_vectors(gf, M)]
        for v in all_vectors(gf, key.V):
            L, p1 = key.L(v), key.P1(v)
            isbad = gf.rank(L, M) < M
            nbad += isbad
            for x in xs:
                y = 0
                for p, row in zip(p1, L):
                    t = p
                    for a, b in zip(row, x):
                        t ^= mt[a][b]
                    y = (y << k) | t
                tot[y] += 1
                bad[y] += isbad
        d = nbad / q ** key.V
        fr = [b / t for b, t in zip(bad[1:], tot[1:])]
        print(f"    F_{q} (N, M) = ({N}, {M}): delta = {d:.4f}; beta(y), y != 0: min {min(fr):.4f} "
              f"mean {sum(fr) / len(fr):.4f} max {max(fr):.4f}; beta(0) = {bad[0] / tot[0]:.4f} "
              f"(oil space is {q ** M / tot[0]:.4f} of the fibre of 0)")


# ---------- E3: character sums of the bad set ----------
def bad_table(key):
    gf = key.gf
    return [0 if key.good(v) else 1 for v in all_vectors(gf, key.V)]


def trace(gf, a):
    r, t = 0, a
    for _ in range(gf.k):
        r ^= t
        t = gf.mt[t][t]
    return r


def char_mask(gf, w):
    """Bit mask m with psi(w.v) = (-1)^popcount(m & index(v))."""
    m = 0
    for wi in w:
        for b in range(gf.k - 1, -1, -1):
            m = (m << 1) | trace(gf, gf.mt[wi][1 << b])
    return m


def rank_one_counts(key):
    """N1[mask of w] = number of rank-one matrices a b^t with w.v = a^t L_v b for all v,
    i.e. of representations w = M_a o (M_a the polar matrix of a.P, o an oil vector)."""
    gf, M, V = key.gf, key.M, key.V
    mt = gf.mt
    n1 = {}
    proj = [a[:] for a in all_vectors(gf, M) if next((t for t in a if t), 0) == 1]
    nz = [b[:] for b in all_vectors(gf, M) if any(b)]
    for a in proj:
        # rows_i = sum_k a_k C_k[i][.]
        rows = []
        for i in range(V):
            row = [0] * M
            for ak, c in zip(a, key.C):
                if ak:
                    m = mt[ak]
                    row = [r ^ m[t] for r, t in zip(row, c[i])]
            rows.append(row)
        for b in nz:
            w = [key._dot(row, b) for row in rows]
            if any(w):
                mk = char_mask(gf, w)
                n1[mk] = n1.get(mk, 0) + 1
    return n1


def exp_fourier(seed, keys=6):
    print("E3  additive characters of the bad vinegar set: X(w) = sum_{v bad} psi(w.v), w != 0")
    print("    model (uniform S): E[X^2] = (1-d)^2 + d(1-d)(q^V - q + 1), d = delta_unif")
    for k, V, M in ((2, 4, 3), (2, 5, 3), (2, 6, 4), (2, 8, 3), (4, 3, 2), (4, 4, 3), (8, 2, 2)):
        gf = GF(k)
        q = gf.q
        acc, cnt, dsum, mx = 0.0, 0, 0.0, 0.0
        for i in range(keys):
            rng = random.Random(seed + 1000 * i + 31 * V + k)
            key = Key(gf, V + M, M, rng)
            tab = bad_table(key)
            dsum += sum(tab) / len(tab)
            X = fwht(tab[:])
            acc += sum(x * x for x in X[1:])
            cnt += len(X) - 1
            mx = max(mx, max(abs(x) for x in X[1:]))
        d = delta_unif(q, M)
        model = (1 - d) ** 2 + d * (1 - d) * (q ** V - q + 1)
        print(f"    F_{q:<3d} V = {V} M = {M}: delta {dsum / keys:.4f} (model {d:.4f}); "
              f"mean X^2 {acc / cnt:10.2f}, model {model:10.2f}, ratio {acc / cnt / model:.3f}; "
              f"rms bias of a sample {sqrt(acc / cnt) / ((1 - d) * q ** V):.2e}, "
              f"max {mx / ((1 - d) * q ** V):.2e}")
        # the last key: X(w) against the number of representations w = M_a o
        n1 = rank_one_counts(key)
        by = {}
        for m in range(1, len(X)):
            c = n1.get(m, 0)
            t = by.setdefault(c, [0, 0.0])
            t[0] += 1
            t[1] += X[m]
        slope = q ** V * (1 - d) / (q ** M - 1)
        print("        mean X(w) by number N1 of representations w = M_a o: "
              + ", ".join(f"N1={c}: {t[1] / t[0]:+.1f} ({t[0]})" for c, t in sorted(by.items())[:6])
              + f"; rank-one term per representation {slope:.1f}")


# ---------- E4: the first-order statistical attack ----------
def annihilator_masks(key):
    """F_2-basis (as bit masks of a public point) of the oil space."""
    gf = key.gf
    out = []
    for j in range(key.M):
        for b in range(gf.k):
            x = [0] * key.M
            x[j] = 1 << b
            out.append(vec_index(gf, key.to_public([0] * key.V, x)))
    return out


def span_dim_f2(masks):
    basis = []
    for m in masks:
        for b in basis:
            m = min(m, m ^ b)
        if m:
            basis.append(m)
    return len(basis)


def exp_attack(seed):
    print("E4  recovering the oil space from answers to uniform targets (largest characters)")
    print("    success: the characters taken in decreasing order of |empirical sum| until they")
    print("    span k*V dimensions over F_2 all annihilate the oil space (then it is their kernel)")
    for k, N, M in ((2, 7, 3), (2, 8, 3), (2, 9, 4), (2, 10, 4), (4, 5, 2)):
        gf = GF(k)
        q = gf.q
        rng = random.Random(seed + 7 * N + k)
        key = Key(gf, N, M, rng)
        V = key.V
        goodv = [v[:] for v in all_vectors(gf, V) if key.good(v)]
        d = 1 - len(goodv) / q ** V
        oil = annihilator_masks(key)
        # largest true bias: the most favourable character for the attacker
        X = fwht(bad_table(key))
        best = max(abs(x) for x in X[1:]) / len(goodv)
        unit = 1 / best ** 2
        res = []
        nbits = k * N
        thr = None
        for e in range(0, 14):
            n = int(unit * 2 ** (e / 2))
            ok = 0
            trials = 3
            for _ in range(trials):
                hist = [0] * (1 << nbits)
                for _ in range(n):
                    # a uniform target and its answer: (v, x) uniform on G x F^M (Lemma C)
                    v = goodv[rng.randrange(len(goodv))]
                    x = [rng.randrange(q) for _ in range(M)]
                    hist[vec_index(gf, key.to_public(v, x))] += 1
                fwht(hist)
                order = sorted(range(1, 1 << nbits), key=lambda m: -abs(hist[m]))
                basis, good_so_far = [], True
                for m in order:
                    r = m
                    for b in basis:
                        r = min(r, r ^ b)
                    if not r:
                        continue
                    if any(bin(m & o).count("1") & 1 for o in oil):
                        good_so_far = False
                        break
                    basis.append(r)
                    if len(basis) == k * V:
                        break
                ok += good_so_far
            res.append((n, ok))
            if ok == trials and thr is None:
                thr = n
            if ok == trials and len(res) >= 2 and res[-2][1] == trials:
                break
        line = " ".join(f"{n}:{ok}/3" for n, ok in res)
        print(f"    F_{q} (N, M) = ({N}, {M}), V = {V}: delta {d:.3f}, q^V/delta = {q ** V / d:.0f}, "
              f"largest bias b = {best:.3e}, 1/b^2 = {unit:.0f}")
        print(f"        samples:successes  {line}")
        if thr:
            print(f"        threshold {thr} = {thr / unit:.1f} / b^2 = "
                  f"{thr * d / q ** V:.2f} * q^V/delta = 2^{log2(thr):.1f} answers")


# ---------- E5: vinegar collisions ----------
def exp_collide(seed):
    print("E5  projective vinegar collisions among answers (each gives an oil vector)")
    for k, N, M, n in ((4, 8, 3, 600), (4, 9, 3, 1500), (8, 5, 2, 3000), (8, 6, 2, 20000)):
        gf = GF(k)
        q = gf.q
        rng = random.Random(seed + 13 * N + k)
        key = Key(gf, N, M, rng)
        V = key.V
        found, runs = 0, 12
        for r in range(runs):
            seen = {}
            asked = set()
            while len(asked) < n:  # n distinct targets: a repeated target repeats the answer
                y = [rng.randrange(q) for _ in range(M)]
                if tuple(y) in asked:
                    continue
                asked.add(tuple(y))
                s = key.derive_preimage(y, b"k%d" % r)
                v = key.vin(s)
                lead = next(a for a in v if a)
                iv = gf.inv(lead)
                pt = vec_index(gf, [gf.mt[iv][a] for a in v])
                if pt in seen:
                    s2, lead2 = seen[pt]
                    lam = gf.mt[lead][gf.inv(lead2)]
                    o = [a ^ gf.mt[lam][b] for a, b in zip(s, s2)]
                    assert key.vin(o) == [0] * V and any(o)  # a nonzero oil vector
                    found += 1
                else:
                    seen[pt] = (s, lead)
        proj = (q ** V - 1) // (q - 1)
        print(f"    F_{q} (N, M) = ({N}, {M}): {n} distinct targets, collisions per run {found / runs:.2f}, "
              f"birthday estimate n^2/(2 (1-delta) |P(F^V)|) = "
              f"{n * n / (2 * (1 - delta_unif(q, M)) * proj):.2f}")


# ---------- E6: polynomials vanishing on the answers ----------
def monomials(n, deg, homogeneous):
    """Exponent supports (tuples of variable indices, with repetition) of the monomials."""
    out = []

    def rec(start, left, cur):
        if left == 0:
            out.append(tuple(cur))
            return
        for i in range(start, n):
            rec(i, left - 1, cur + [i])

    for d in ([deg] if homogeneous else range(deg + 1)):
        rec(0, d, [])
    return out


def nullity(gf, points, deg, homogeneous):
    mons = monomials(len(points[0]), deg, homogeneous)
    mt = gf.mt
    rows = []
    for p in points:
        row = []
        for m in mons:
            t = 1
            for i in m:
                t = mt[t][p[i]]
            row.append(t)
        rows.append(row)
    return len(mons) - gf.rank(rows, len(mons)), len(mons)


def exp_annih(seed):
    print("E6  polynomials vanishing on the answers (F_256); expected = the public ideal only")
    gf = GF(8)
    q = gf.q
    for N, M, cubic in ((10, 4, True), (13, 5, False)):
        rng = random.Random(seed + N)
        key = Key(gf, N, M, rng)
        sd = b"annih"
        nq = comb(N + 2, 2)
        # (a) distinct random targets
        pts = [key.derive_preimage([rng.randrange(q) for _ in range(M)], sd)
               for _ in range(comb(N + 3, 3) + 40 if cubic else nq + 40)]
        r = [nullity(gf, pts, 2, False)]
        if cubic:
            r.append(nullity(gf, pts, 3, False))
        print(f"    (N, M) = ({N}, {M}) random targets, {len(pts)} answers: vanishing polynomials "
              f"of degree <= 2: {r[0][0]} (expected 0)"
              + (f", <= 3: {r[1][0]} (expected 0)" if cubic else ""))
        # (b) one class: D(mu c) for all mu != 0
        c = [rng.randrange(1, q) for _ in range(M)]
        raw = [key.derive_preimage([gf.mt[mu][t] for t in c], sd) for mu in range(1, q)]
        resc = [[gf.mt[gf.inv(gf.sqrt(mu))][t] for t in s] for mu, s in zip(range(1, q), raw)]
        assert all(key.P(s) == c for s in resc)
        a2 = nullity(gf, resc, 2, False)[0]
        h1 = nullity(gf, raw, 1, True)[0]
        h2 = nullity(gf, raw, 2, True)[0]
        msg = (f"    (N, M) = ({N}, {M}) one class, 255 answers: rescaled, degree <= 2: {a2} "
               f"(expected M = {M}); cone, linear forms {h1} (0), quadrics {h2} (M - 1 = {M - 1})")
        if cubic:
            msg += f", cubics {nullity(gf, raw, 3, True)[0]} ((M - 1) N = {(M - 1) * N})"
        print(msg)
        # (c) targets in a plane T
        t1 = [rng.randrange(q) for _ in range(M)]
        t2 = [rng.randrange(q) for _ in range(M)]
        need = (comb(N + 2, 3) if cubic else nq) + 40
        pts = []
        while len(pts) < need:
            a, b = rng.randrange(q), rng.randrange(q)
            if a or b:
                pts.append(key.derive_preimage([gf.mt[a][x] ^ gf.mt[b][y] for x, y in zip(t1, t2)], sd))
        h2 = nullity(gf, pts, 2, True)[0]
        msg = (f"    (N, M) = ({N}, {M}) targets in a plane, {len(pts)} answers: quadrics {h2} "
               f"(M - 2 = {M - 2})")
        if cubic:
            msg += f", cubics {nullity(gf, pts, 3, True)[0]} ((M - 2) N = {(M - 2) * N})"
        print(msg)
        # (d) positive control: vinegars in the hyperplane v_0 = 0
        pts = [key.derive_preimage([rng.randrange(q) for _ in range(M)], sd,
                                   vinegar_filter=lambda v: [0] + v[1:]) for _ in range(nq + 40)]
        print(f"    (N, M) = ({N}, {M}) control (vinegar in a hyperplane): linear forms "
              f"{nullity(gf, pts, 1, True)[0]} (expected 1: a vector of the annihilator of the oil space)")


# ---------- E7: targets covered by spans ----------
def exp_span(seed, trials=150):
    print("E7  target classes covered by the span of r answers, against r random points")
    gf = GF(4)
    q = gf.q
    for N, M, r in ((9, 3, 2), (9, 3, 3), (10, 4, 3), (10, 4, 4)):
        rng = random.Random(seed + 5 * N + r)
        key = Key(gf, N, M, rng)
        res = {}
        for mode in ("answers, random targets", "answers, one class", "random points"):
            tot = 0
            for t in range(trials):
                if mode == "random points":
                    pts = [[rng.randrange(q) for _ in range(N)] for _ in range(r)]
                elif mode == "answers, one class":
                    c = [rng.randrange(1, q) for _ in range(M)]
                    pts = [key.derive_preimage([gf.mt[mu][x] for x in c], b"s%d" % t)
                           for mu in rng.sample(range(1, q), r)]
                else:
                    pts = [key.derive_preimage([rng.randrange(q) for _ in range(M)], b"s%d" % t)
                           for _ in range(r)]
                classes = set()
                for al in all_vectors(gf, r):
                    lead = next((a for a in al if a), None)
                    if lead != 1:  # one representative per projective point
                        continue
                    s = [0] * N
                    for a, p in zip(al, pts):
                        if a:
                            m = gf.mt[a]
                            s = [u ^ m[w] for u, w in zip(s, p)]
                    y = key.P(s)
                    ly = next((a for a in y if a), None)
                    if ly is None:
                        continue
                    iv = gf.inv(ly)
                    classes.add(vec_index(gf, [gf.mt[iv][a] for a in y]))
                tot += len(classes)
            res[mode] = tot / trials
        npts = (q ** r - 1) // (q - 1)
        ncls = (q ** M - 1) // (q - 1)
        model = ncls * (1 - exp(-npts / ncls))
        print(f"    F_{q} (N, M) = ({N}, {M}), r = {r}: {npts} points of the span, {ncls} classes; "
              + "; ".join(f"{m} {v:.1f}" for m, v in res.items()) + f"; random map {model:.1f}")


# ---------- figures at (119, 45, 256) ----------
def exp_table():
    print("Figures at (N, M, V, q) = (119, 45, 74, 256), log2")
    V, M, lq = 74, 45, 8
    d = delta_unif(256, M)
    ld = log2(d)
    print(f"    delta_unif = 2^{ld:.3f}")
    for Q in (20, 40, 64):
        coll = 2 * Q - 1 + log2(255) - lq * V - log2(1 - d)
        iso = 2 * Q - 1 - lq * M
        print(f"    q = 2^{Q}: projective vinegar collision 2^{coll:.1f}; isotropic pair "
              f"2^{iso:.1f}; a pair whose plane meets a given class "
              f"2^{2 * Q - 1 + 2 * lq - lq * M:.1f}")
    print(f"    calls for one projective vinegar collision: 2^{(lq * V - log2(255) + 1) / 2:.1f}")
    rms = 0.5 * (ld + log2(1 - d) - lq * V) - log2(1 - d)
    print(f"    rms bias of a character on the annihilator of the oil space: 2^{rms:.1f}; "
          f"samples for one character 2^{-2 * rms:.1f}")
    print(f"    advantage of one such character with 2^64 samples: about 2^{32 + rms:.1f}")
    print(f"    Pluecker unknowns of the bad hypersurface: 2^{log2(comb(119, 45)):.1f}; "
          f"monomials of degree 45 in 119 variables: 2^{log2(comb(163, 45)):.1f}")
    for r in (2, 3, 4, 5, 9):
        print(f"    r = {r}: r-subsets of 2^64 answers 2^{64 * r - log2(factorial(r)):.1f}; "
              f"with dependent vinegars 2^{64 * r - log2(factorial(r)) - lq * (V - r + 1):.1f}")
    print(f"    exhaustive search for one of n targets: 2^{lq * M} / n evaluations "
          f"(n = 2^64: 2^{lq * M - 64})")


def main():
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    runs = {"law": exp_law, "fibre": exp_fibre, "fourier": exp_fourier, "attack": exp_attack,
            "collide": exp_collide, "annih": exp_annih, "span": exp_span}
    if what == "table":
        exp_table()
    elif what == "all":
        for f in runs.values():
            f(seed)
            sys.stdout.flush()
        exp_table()
    else:
        runs[what](seed)


if __name__ == "__main__":
    main()
