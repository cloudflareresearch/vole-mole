#!/usr/bin/env python3
"""Toy experiments for lean/docs/security/ompr-shift-algebra.md.

Field F_16, toy UOV keys (N, M) = (8, 3) by default.  Pure Python, no dependencies.

  1. Identities of section 1: polar form, scaling, kernel translation, oil translation,
     the preimage line through a singular vector (D(0)), the plane of two preimages,
     good <=> O ∩ K_s = 0, rad B = 0.
  2. Section 3.1: the Lie algebra {(X, Y) : B(s, Xs) = Y P(s) for all s} of infinitesimal
     symmetries P∘A = T∘P.  Expected: dimension 1, spanned by (I, 0).
  3. Section 3.3: the cross term B(s1, s2) of two sampler answers on fixed targets, chi-square
     against the uniform law on F^M (keys (6, 2) and (8, 2)).  With 300000 samples the key
     (6, 2) shows a small deviation (chi-square about 320 on 255); (8, 2) and (10, 2) show none.
  4. Section 4: hybrid-XL estimates for 45 and 44 equations over F_256, and for 44 quadrics
     plus one equation of degree 34 (the model of scripts/uov-open-structure/mq_estimates.py).

Usage: shift_algebra_toy.py [seed [N M [samples]]]
"""
import random
import sys
from math import comb, log2

# ---------- F_16 = F_2[x]/(x^4 + x + 1) ----------
Q = 16
EXP = [0] * 30
LOG = [0] * 16
_x = 1
for _i in range(15):
    EXP[_i] = _x
    LOG[_x] = _i
    _x <<= 1
    if _x & 16:
        _x ^= 0b10011
for _i in range(15, 30):
    EXP[_i] = EXP[_i - 15]


def mul(a, b):
    return 0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]


def inv(a):
    return EXP[(15 - LOG[a]) % 15]


def sqrt(a):  # a^8 is the square root in F_16
    r = a
    for _ in range(3):
        r = mul(r, r)
    return r


def rref(rows, ncols):
    A = [r[:] for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(A)) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        iv = inv(A[r][c])
        A[r] = [mul(iv, t) for t in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [a ^ mul(f, b) for a, b in zip(A[i], A[r])]
        piv.append(c)
        r += 1
        if r == len(A):
            break
    return A[:r], piv


def rank(rows, ncols):
    return len(rref(rows, ncols)[1]) if rows else 0


def kernel(rows, ncols):
    R, piv = rref(rows, ncols)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fc in free:
        v = [0] * ncols
        v[fc] = 1
        for i, pc in enumerate(piv):
            v[pc] = R[i][fc]
        basis.append(v)
    return basis


def solve(Amat, b):
    """One solution of A x = b, or None."""
    n = len(Amat[0])
    R, piv = rref([r[:] + [bb] for r, bb in zip(Amat, b)], n + 1)
    if n in piv:
        return None
    x = [0] * n
    for i, pc in enumerate(piv):
        x[pc] = R[i][n]
    return x


def vadd(a, b):
    return [x ^ y for x, y in zip(a, b)]


def vscale(c, a):
    return [mul(c, x) for x in a]


class Key:
    """Toy UOV key: P(s) = F(vin(s), oil(s)), F without oil-oil terms; O = {(Ox, x)}."""

    def __init__(self, N, M, rng):
        self.N, self.M, self.V = N, M, N - M
        V = self.V
        self.O = [[rng.randrange(Q) for _ in range(M)] for _ in range(V)]
        # central forms: upper triangular, zero on the oil-oil block
        self.F = []
        for _ in range(M):
            f = [[0] * N for _ in range(N)]
            for i in range(N):
                for j in range(i, N):
                    if i < V:
                        f[i][j] = rng.randrange(Q)
            self.F.append(f)
        # public matrices Qk = T^t F T with T s = (s_v + O s_o, s_o)   (char 2)
        T = [[0] * N for _ in range(N)]
        for i in range(N):
            T[i][i] = 1
        for i in range(V):
            for j in range(M):
                T[i][V + j] = self.O[i][j]
        self.T = T
        self.Qm = []
        for f in self.F:
            FT = [[0] * N for _ in range(N)]
            for i in range(N):
                for j in range(N):
                    acc = 0
                    for a in range(N):
                        if f[i][a] and T[a][j]:
                            acc ^= mul(f[i][a], T[a][j])
                    FT[i][j] = acc
            q = [[0] * N for _ in range(N)]
            for i in range(N):
                for j in range(N):
                    acc = 0
                    for a in range(N):
                        if T[a][i] and FT[a][j]:
                            acc ^= mul(T[a][i], FT[a][j])
                    q[i][j] = acc
            self.Qm.append(q)
        self.Bm = [[[q[i][j] ^ q[j][i] for j in range(N)] for i in range(N)] for q in self.Qm]

    def P(self, s):
        out = []
        for q in self.Qm:
            acc = 0
            for i in range(self.N):
                if s[i]:
                    row = q[i]
                    t = 0
                    for j in range(self.N):
                        if row[j] and s[j]:
                            t ^= mul(row[j], s[j])
                    acc ^= mul(s[i], t)
            out.append(acc)
        return out

    def B(self, a, b):
        out = []
        for bm in self.Bm:
            acc = 0
            for i in range(self.N):
                if a[i]:
                    t = 0
                    for j in range(self.N):
                        if bm[i][j] and b[j]:
                            t ^= mul(bm[i][j], b[j])
                    acc ^= mul(a[i], t)
            out.append(acc)
        return out

    def DP(self, s):
        """M x N matrix of u -> B(s, u)."""
        return [[self.B(s, [1 if j == i else 0 for j in range(self.N)])[k] for i in range(self.N)]
                for k in range(self.M)]

    def iota(self, x):
        v = [0] * self.V
        for i in range(self.V):
            for j in range(self.M):
                if x[j]:
                    v[i] ^= mul(self.O[i][j], x[j])
        return v + list(x)

    def oil_basis(self):
        return [self.iota([1 if j == i else 0 for j in range(self.M)]) for i in range(self.M)]

    def L(self, s):
        """M x M matrix of x -> B(s, iota(x)); for s = (v, 0) this is L_v."""
        ob = self.oil_basis()
        cols = [self.B(s, o) for o in ob]
        return [[cols[j][k] for j in range(self.M)] for k in range(self.M)]

    def good(self, s):
        return rank(self.L(s), self.M) == self.M

    def D(self, y, rng):
        """Uniform good preimage of y (the ideal sampler D*)."""
        while True:
            v0 = [rng.randrange(Q) for _ in range(self.V)] + [0] * self.M
            Lm = self.L(v0)
            if rank(Lm, self.M) < self.M:
                continue
            x = solve(Lm, vadd(y, self.P(v0)))
            return vadd(v0, self.iota(x))


def rvec(n, rng):
    return [rng.randrange(Q) for _ in range(n)]


def check_identities(key, rng, trials=200):
    N, M = key.N, key.M
    zero = [0] * M
    z = key.D(zero, rng)
    assert any(z) and key.P(z) == zero
    n_bad = 0
    for _ in range(trials):
        s, u = rvec(N, rng), rvec(N, rng)
        lam, al, be = rng.randrange(Q), rng.randrange(Q), rng.randrange(Q)
        # polar form, scaling, alternating
        assert key.P(vadd(s, u)) == vadd(vadd(key.P(s), key.P(u)), key.B(s, u))
        assert key.P(vscale(lam, s)) == vscale(mul(lam, lam), key.P(s))
        assert key.B(s, s) == zero
        # preimage line through the singular vector z = D(0)
        assert key.P(vadd(s, vscale(lam, z))) == vadd(key.P(s), vscale(lam, key.B(s, z)))
        # two preimages of one target: a plane
        y = rvec(M, rng)
        s1, s2 = key.D(y, rng), key.D(y, rng)
        lhs = key.P(vadd(vscale(al, s1), vscale(be, s2)))
        rhs = vadd(vscale(mul(al ^ be, al ^ be), y), vscale(mul(al, be), key.B(s1, s2)))
        assert lhs == rhs
        # kernel translation
        Ks = kernel(key.DP(s), N)
        g = key.good(s)
        if Ks:
            w = [0] * N
            for b in Ks:
                w = vadd(w, vscale(rng.randrange(Q), b))
            assert key.P(vadd(s, w)) == vadd(key.P(s), key.P(w))
        # good <=> O ∩ K_s = 0  (dim(K_s + O) = dim K_s + M)
        meets = rank(Ks + key.oil_basis(), N) < len(Ks) + M
        assert g == (not meets)
        if g:
            assert len(Ks) == N - M
            # oil translation: P(s + o) = P(s) + Delta, o = iota(L_s^{-1} Delta)
            dl = rvec(M, rng)
            x = solve(key.L(s), dl)
            assert key.P(vadd(s, key.iota(x))) == vadd(key.P(s), dl)
        else:
            n_bad += 1
        # scaled preimage
        if lam:
            sp = key.D(vscale(lam, y), rng)
            assert key.P(vscale(sqrt(inv(lam)), sp)) == y
    # radical of B
    rows = []
    for k in range(M):
        rows += key.Bm[k]
    rad = N - rank(rows, N)
    print(f"  identities: {trials} trials ok; bad points {n_bad}/{trials} "
          f"(1/15 = {trials/15:.1f}); dim rad B = {rad}")


def lie_algebra_dim(key):
    """dim {(X, Y) : s^t B_k X s = sum_l Y_kl P_l(s) as quadratic forms, all k}."""
    N, M = key.N, key.M
    nun = N * N + M * M
    rows = []
    # coefficient of s_i s_j (i <= j) in the form of matrix C: C_ii, or C_ij + C_ji
    for k in range(M):
        bm = key.Bm[k]
        for i in range(N):
            for j in range(i, N):
                row = [0] * nun
                # C = B_k X : C_ij = sum_a B_k[i][a] X[a][j]
                for a in range(N):
                    row[a * N + j] ^= bm[i][a]
                    if i != j:
                        row[a * N + i] ^= bm[j][a]
                for l in range(M):
                    q = key.Qm[l]
                    row[N * N + k * M + l] ^= q[i][j] if i == j else (q[i][j] ^ q[j][i])
                rows.append(row)
    return nun - rank(rows, nun), len(rows), nun


def cross_term_chi2(rng, N=6, samples=40000):
    key = Key(N, 2, rng)
    y1, y2 = rvec(2, rng), rvec(2, rng)
    cells = [0] * (Q * Q)
    for _ in range(samples):
        b = key.B(key.D(y1, rng), key.D(y2, rng))
        cells[b[0] * Q + b[1]] += 1
    e = samples / (Q * Q)
    chi2 = sum((c - e) ** 2 / e for c in cells)
    return chi2, Q * Q - 1


# ---------- hybrid XL estimates (same model as scripts/uov-open-structure/mq_estimates.py) ----


def operating_degree(n, m, dmax=200):
    num = [0] * (dmax + 1)
    for i in range(0, min(m, dmax // 2) + 1):
        num[2 * i] = (-1) ** i * comb(m, i)
    for d in range(dmax + 1):
        c = sum(num[j] * comb(n + d - j, d - j) for j in range(d + 1))
        if c <= 0:
            return d
    return None


def xl_cost(n, m, q):
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


def operating_degree_mixed(n, m, e, dmax=200):
    """As operating_degree, with one extra equation of degree e."""
    num = [0] * (dmax + 1)
    for i in range(0, min(m, dmax // 2) + 1):
        c = (-1) ** i * comb(m, i)
        num[2 * i] += c
        if 2 * i + e <= dmax:
            num[2 * i + e] -= c
    for d in range(dmax + 1):
        c = sum(num[j] * comb(n + d - j, d - j) for j in range(d + 1))
        if c <= 0:
            return d
    return None


def xl_cost_mixed(n, m, e, q):
    """m quadrics and one equation of degree e in n variables."""
    best = None
    for k in range(0, 12):
        nn = n - k
        D = operating_degree_mixed(nn, m, e)
        if D is None:
            continue
        c = k * log2(q) + log2(3) + 2 * log2(comb(nn + D, D)) + log2(comb(nn + 2, 2))
        if best is None or c < best[0]:
            best = (c, k, D)
    return best


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    N = int(sys.argv[2]) if len(sys.argv) > 3 else 8
    M = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    rng = random.Random(seed)
    print(f"F_16, (N, M) = ({N}, {M}), seed {seed}")
    print("1. identities")
    for _ in range(3):
        check_identities(Key(N, M, rng), rng)
    print("2. infinitesimal symmetries B(s, Xs) = Y P(s)")
    for (n, m) in [(N, M), (10, 4), (12, 5)]:
        for _ in range(3):
            d, neq, nun = lie_algebra_dim(Key(n, m, rng))
            print(f"  (N, M) = ({n}, {m}): {neq} equations, {nun} unknowns, solution space dim {d}")
    big = len(sys.argv) > 4  # 5th argument: sample count for the chi-square test
    samples = int(sys.argv[4]) if big else 40000
    print(f"3. cross term B(D(y1), D(y2)), fixed targets, {samples} samples")
    for n in (6, 8):
        for _ in range(2):
            chi2, df = cross_term_chi2(rng, n, samples)
            print(f"  key ({n}, 2): chi-square = {chi2:.1f} on {df} degrees of freedom "
                  f"(mean {df}, sd {(2*df)**0.5:.1f})")
    print("4. hybrid XL over F_256, log2 multiplications")
    c45 = xl_cost(45, 45, 256)
    c44 = xl_cost(44, 44, 256)
    print(f"  45 equations: 2^{c45[0]:.1f} (k={c45[1]}, D={c45[2]});  "
          f"44 equations: 2^{c44[0]:.1f} (k={c44[1]}, D={c44[2]})")
    print(f"  gain of one dropped equation: 2^{c45[0]-c44[0]:.1f};  "
          f"landing cost 256/17 = 2^{log2(256/17):.2f}, 256/16 = 2^4")
    c41, c48 = xl_cost(41, 41, 256), xl_cost(48, 48, 256)
    print(f"  average over 41..48 equations: 2^{(c48[0]-c41[0])/7:.2f} per equation")
    cm = xl_cost_mixed(45, 44, 34, 256)
    print(f"  44 quadrics + one equation of degree 34 (17 collinear shifts): 2^{cm[0]:.1f} "
          f"(k={cm[1]}, D={cm[2]})")


if __name__ == "__main__":
    main()
