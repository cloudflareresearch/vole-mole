#!/usr/bin/env python3
"""Toy experiments for lean/docs/security/uov-open-structure.md, Part B.

Field F_16, UOV with (N, M, V) = (8, 3, 5) by default.  Pure Python, no dependencies.

  1. Builds a UOV public map P (upper-triangular matrices P_k) with oil space O = {(Ox, x)}.
  2. Checks, from the public Jacobian J(s) only, that
         det L_vin(s) = 0   <=>   ker J(s) meets the oil space nontrivially,
     and reports the bad fraction against delta_unif.
  3. Proposition B.3: recovers the oil space from an exact badness oracle alone, by interpolating
     f(s) = det L_vin(s) on random affine 3-spaces and reading off its gradient.
  4. The same with a one-sided oracle that misses each bad point with probability 1/2.

Usage: bad_oracle_toy.py [seed [N M]]
"""
import random
import sys
from itertools import product

# ---------- F_16 = F_2[x]/(x^4 + x + 1) ----------
Q = 16
EXP = [0] * 30
LOG = [0] * 16
x = 1
for i in range(15):
    EXP[i] = x
    LOG[x] = i
    x <<= 1
    if x & 16:
        x ^= 0b10011
for i in range(15, 30):
    EXP[i] = EXP[i - 15]


def mul(a, b):
    return 0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]


def inv(a):
    return EXP[(15 - LOG[a]) % 15]


def rref(rows, ncols):
    """Row-reduce (list of lists, modified copy). Returns (matrix, pivot columns)."""
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
    return len(rref(rows, ncols)[1])


def kernel(rows, ncols):
    """Basis of {x : rows * x = 0}."""
    R, piv = rref(rows, ncols)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fcol in free:
        v = [0] * ncols
        v[fcol] = 1
        for i, pc in enumerate(piv):
            v[pc] = R[i][fcol]  # char 2: minus = plus
        basis.append(v)
    return basis


def det(Mx):
    A = [r[:] for r in Mx]
    n = len(A)
    d = 1
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c]), None)
        if p is None:
            return 0
        A[c], A[p] = A[p], A[c]
        d = mul(d, A[c][c])
        iv = inv(A[c][c])
        for i in range(c + 1, n):
            if A[i][c]:
                f = mul(A[i][c], iv)
                A[i] = [a ^ mul(f, b) for a, b in zip(A[i], A[c])]
    return d


# ---------- toy UOV ----------
class UOV:
    def __init__(self, N, M, rng):
        self.N, self.M, self.V = N, M, N - M
        V = self.V
        self.O = [[rng.randrange(Q) for _ in range(M)] for _ in range(V)]
        # central maps F_k(v, x) = v^T A_k v + v^T B_k x  (no oil-oil terms)
        self.A = [[[rng.randrange(Q) if j >= i else 0 for j in range(V)] for i in range(V)]
                  for _ in range(M)]
        self.B = [[[rng.randrange(Q) for _ in range(M)] for _ in range(V)] for _ in range(M)]
        # public polar matrices Mk[a][b] = P'_k(e_a, e_b), computed through the secret change of
        # variables once; afterwards they are "the public key" for the checks below.
        self.polar = []
        for k in range(M):
            Mk = [[self._polar_secret(k, a, b) for b in range(N)] for a in range(N)]
            self.polar.append(Mk)

    def split(self, s):
        V, M = self.V, self.M
        xo = s[V:]
        v = [s[i] ^ self._dot(self.O[i], xo) for i in range(V)]
        return v, xo

    @staticmethod
    def _dot(a, b):
        r = 0
        for u, w in zip(a, b):
            r ^= mul(u, w)
        return r

    def _polar_secret(self, k, a, b):
        ea = [1 if i == a else 0 for i in range(self.N)]
        eb = [1 if i == b else 0 for i in range(self.N)]
        va, xa = self.split(ea)
        vb, xb = self.split(eb)
        V, M = self.V, self.M
        r = 0
        A, B = self.A[k], self.B[k]
        for i in range(V):
            for j in range(V):
                if A[i][j]:
                    r ^= mul(A[i][j], mul(va[i], vb[j]) ^ mul(vb[i], va[j]))
            for j in range(M):
                if B[i][j]:
                    r ^= mul(B[i][j], mul(va[i], xb[j]) ^ mul(vb[i], xa[j]))
        return r

    # secret-key side
    def L(self, v):
        return [[self._dot([self.B[k][i][j] for i in range(self.V)], v) for j in range(self.M)]
                for k in range(self.M)]

    def bad(self, s):
        return det(self.L(self.split(s)[0])) == 0

    def oil_basis(self):
        return [[self.O[i][j] for i in range(self.V)] + [1 if t == j else 0 for t in range(self.M)]
                for j in range(self.M)]

    # public side
    def jacobian(self, s):
        return [[self._dot(self.polar[k][b], s) for b in range(self.N)] for k in range(self.M)]


def check_public_characterisation(u, rng, trials):
    oil = u.oil_basis()
    nbad = 0
    for _ in range(trials):
        s = [rng.randrange(Q) for _ in range(u.N)]
        K = kernel(u.jacobian(s), u.N)
        meets = rank(K + oil, u.N) < len(K) + len(oil)
        b = u.bad(s)
        assert b == meets, "bad <=> ker J(s) meets O: violated"
        nbad += b
    return nbad / trials


# ---------- Proposition B.3: key recovery from a badness oracle ----------
def monomials(d, deg):
    return [e for e in product(range(deg + 1), repeat=d) if sum(e) <= deg]


def powtab():
    return [[1 if e == 0 else (0 if a == 0 else EXP[(LOG[a] * e) % 15]) for e in range(Q)]
            for a in range(Q)]


POW = powtab()


def interpolate(oracle, s0, dirs, deg, counter):
    """Polynomials of degree <= deg on the affine space s0 + span(dirs) vanishing on every point
    the oracle flags.  Returns a basis of that space (coefficient vectors over `monomials`)."""
    d = len(dirs)
    mons = monomials(d, deg)
    rows = []
    N = len(s0)
    for c in product(range(Q), repeat=d):
        s = s0[:]
        for cj, e in zip(c, dirs):
            if cj:
                s = [a ^ mul(cj, b) for a, b in zip(s, e)]
        counter[0] += 1
        if oracle(s):
            row = []
            for e in mons:
                t = 1
                for cj, ej in zip(c, e):
                    t = mul(t, POW[cj][ej])
                row.append(t)
            rows.append(row)
    return kernel(rows, len(mons)), mons, len(rows)


def recover_oil(oracle, N, M, rng, counter, d=3):
    """Returns a basis of the recovered oil space (kernel of the gradients found)."""
    e = [[1 if i == j else 0 for i in range(N)] for j in range(N)]
    grads = []
    V = N - M
    attempts = 0
    while rank(grads, N) < V and attempts < 40 * V:
        attempts += 1
        s0 = [rng.randrange(Q) for _ in range(N)]
        piv = rng.randrange(N)  # shared direction
        others = [j for j in range(N) if j != piv]
        h = [None] * N
        h[piv] = 1
        ok = True
        for a in range(0, len(others), d - 1):
            grp = others[a:a + d - 1]
            while len(grp) < d - 1:  # pad with an already-used direction
                grp.append(next(j for j in others if j not in grp))
            dirs = [e[piv]] + [e[j] for j in grp]
            ker, mons, _ = interpolate(oracle, s0, dirs, M, counter)
            if len(ker) != 1:
                ok = False
                break
            g = ker[0]
            lin = []
            for t in range(d):
                ex = tuple(1 if i == t else 0 for i in range(d))
                lin.append(g[mons.index(ex)])
            if lin[0] == 0:
                ok = False
                break
            iv = inv(lin[0])
            for t, j in enumerate(grp):
                h[j] = mul(iv, lin[t + 1])
        if ok:
            grads.append(h)
    return kernel(grads, N), attempts


def same_space(A, B, N):
    return len(A) == len(B) and rank(A + B, N) == len(A) == rank(A, N)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    N, M = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (8, 3)
    u = UOV(N, M, rng)
    frac = check_public_characterisation(u, rng, 4000)
    dunif = 1.0
    for i in range(1, M + 1):
        dunif *= 1 - Q ** (-i)
    print(f"(q, N, M) = ({Q}, {N}, {M}); bad <=> ker J(s) meets O: verified on 4000 points; "
          f"bad fraction {frac:.4f} (delta_unif = {1 - dunif:.4f})")

    cnt = [0]
    rec, att = recover_oil(u.bad, N, M, rng, cnt)
    print(f"exact oracle:     oil space recovered = {same_space(rec, u.oil_basis(), N)}; "
          f"{att} base points, {cnt[0]} oracle calls")

    noise = random.Random(seed + 1000)
    cnt = [0]
    rec, att = recover_oil(lambda s: u.bad(s) and noise.random() < 0.5, N, M, rng, cnt)
    print(f"one-sided, a=1/2: oil space recovered = {same_space(rec, u.oil_basis(), N)}; "
          f"{att} base points, {cnt[0]} oracle calls")


if __name__ == "__main__":
    main()
