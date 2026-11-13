#!/usr/bin/env python3
"""Toy experiments for lean/docs/security/ompr-shift-algebra.md, section 8 (Theorem T3).

Pure Python, no dependencies.  Three parts:

  A. Lie algebra {(X, Y) : B(s, Xs) = Y P(s)} on larger toy keys than shift_algebra_toy.py,
     over F_4, F_16 and F_256.  Expected dimension: 1, spanned by (I, 0).
  B. The full symmetry group over F_4: all pairs (A, T), A a bijection that is linear or
     Frobenius-semilinear, T likewise, with P∘A = T∘P.  Exhaustive (backtracking on the images
     of the basis vectors).  Observed: for M >= 3 the 3 scalings (lambda I, lambda^2 I) and
     nothing semilinear; for M = 2 (a pencil of two quadrics) there are more pairs.
  C. The rank lemmas behind the proof (Lemma E, Lemma F): for structured matrices A over F_4
     and every lambda in F_16, the rank of  pi∘(Gamma^2 A - lambda)  and of  pi∘(D_X - lambda)
     on symmetric tensors modulo Gamma^2(O) is at least the bound used in the union bound.

Usage: symmetry_toy.py [seed [part ...]]      parts: A B C (default: all)
"""
import random
import sys


class GF:
    """GF(2^k) for k in {2, 4, 8}; elements are ints, addition is XOR."""

    POLY = {2: 0b111, 4: 0b10011, 8: 0x11B}

    def __init__(self, k):
        self.k, self.q = k, 1 << k
        poly = self.POLY[k]
        q = self.q

        def cmul(a, b):
            r = 0
            while b:
                if b & 1:
                    r ^= a
                a <<= 1
                if a & q:
                    a ^= poly
                b >>= 1
            return r

        self.MUL = [[cmul(a, b) for b in range(q)] for a in range(q)]
        self.INV = [0] * q
        for a in range(1, q):
            self.INV[a] = next(b for b in range(1, q) if self.MUL[a][b] == 1)
        # translate tables on bytes: row -> c * row
        self.TR = [bytes(self.MUL[c][b] if b < q else 0 for b in range(256)) for c in range(q)]

    def frob(self, a):
        return self.MUL[a][a]

    # ----- linear algebra on rows stored as bytes -----
    def rank(self, rows, ncols):
        """Rank of a list of rows (lists or bytes of field elements)."""
        TR, INV = self.TR, self.INV
        piv = {}
        r = 0
        for row in rows:
            row = bytes(row)
            x = int.from_bytes(row, "little")
            while x:
                c = ((x & -x).bit_length() - 1) >> 3
                p = piv.get(c)
                if p is None:
                    lead = (x >> (8 * c)) & 255
                    nb = x.to_bytes(ncols, "little").translate(TR[INV[lead]])
                    piv[c] = int.from_bytes(nb, "little")
                    r += 1
                    break
                lead = (x >> (8 * c)) & 255
                x ^= int.from_bytes(p.to_bytes(ncols, "little").translate(TR[lead]), "little")
            if r == ncols:
                break
        return r

    def kernel(self, rows, ncols):
        """Basis of {x : rows x = 0} (lists)."""
        MUL, INV = self.MUL, self.INV
        A = [list(r) for r in rows]
        piv = []
        r = 0
        for c in range(ncols):
            p = next((i for i in range(r, len(A)) if A[i][c]), None)
            if p is None:
                continue
            A[r], A[p] = A[p], A[r]
            iv = INV[A[r][c]]
            A[r] = [MUL[iv][t] for t in A[r]]
            for i in range(len(A)):
                if i != r and A[i][c]:
                    f = A[i][c]
                    A[i] = [a ^ MUL[f][b] for a, b in zip(A[i], A[r])]
            piv.append(c)
            r += 1
            if r == len(A):
                break
        basis = []
        for fc in (c for c in range(ncols) if c not in piv):
            v = [0] * ncols
            v[fc] = 1
            for i, pc in enumerate(piv):
                v[pc] = A[i][fc]
            basis.append(v)
        return basis

    def matvec(self, A, v):
        MUL = self.MUL
        out = []
        for row in A:
            acc = 0
            for a, b in zip(row, v):
                acc ^= MUL[a][b]
            out.append(acc)
        return out

    def matmul(self, A, B):
        MUL = self.MUL
        n, m, p = len(A), len(B), len(B[0])
        return [[self._dot(A[i], [B[k][j] for k in range(m)]) for j in range(p)] for i in range(n)]

    def _dot(self, a, b):
        MUL = self.MUL
        acc = 0
        for x, y in zip(a, b):
            acc ^= MUL[x][y]
        return acc


def toy_key(F, N, M, rng):
    """Public forms of a UOV key: upper triangular N x N matrices Qm[k], vanishing on the oil
    space {(O x, x)}.  Returns (Qm, O)."""
    V = N - M
    q, MUL = F.q, F.MUL
    O = [[rng.randrange(q) for _ in range(M)] for _ in range(V)]
    T = [[1 if i == j else 0 for j in range(N)] for i in range(N)]
    for i in range(V):
        for j in range(M):
            T[i][V + j] = O[i][j]  # T s = (s_v + O s_o, s_o) = central coordinates of s
    Tt = [list(c) for c in zip(*T)]
    Qm = []
    for _ in range(M):
        f = [[rng.randrange(q) if (i <= j and i < V) else 0 for j in range(N)] for i in range(N)]
        g = F.matmul(Tt, F.matmul(f, T))
        # fold to upper triangular
        Qm.append([[g[i][j] if i == j else (g[i][j] ^ g[j][i] if i < j else 0)
                    for j in range(N)] for i in range(N)])
    return Qm, O


def lie_algebra_dim(F, Qm):
    """dim {(X, Y) : B(s, X s) = Y P(s) for all s}."""
    M, N = len(Qm), len(Qm[0])
    nun = N * N + M * M
    Bm = [[[q[i][j] ^ q[j][i] if i != j else 0 for j in range(N)] for i in range(N)] for q in Qm]
    rows = []
    for k in range(M):
        bm = Bm[k]
        for i in range(N):
            for j in range(i, N):
                row = bytearray(nun)
                for a in range(N):
                    row[a * N + j] ^= bm[i][a]
                    if i != j:
                        row[a * N + i] ^= bm[j][a]
                for l in range(M):
                    row[N * N + k * M + l] ^= Qm[l][i][j]
                rows.append(row)
    return nun - F.rank(rows, nun), len(rows), nun


# ---------------------------------------------------------------------------------------------
# Part B: the full group over F_4
# ---------------------------------------------------------------------------------------------

def pack(v):
    x = 0
    for i, a in enumerate(v):
        x |= a << (2 * i)
    return x


def unpack(x, n):
    return [(x >> (2 * i)) & 3 for i in range(n)]


def full_group_F4(F, Qm, verbose=False):
    """All (A, T), A bijective and sigma-semilinear, T sigma-semilinear, P∘A = T∘P, for sigma
    in {id, Frobenius}.  Vectors are packed 2 bits per coordinate, so addition is XOR.
    Returns (list of linear pairs, list of semilinear pairs) as (images of basis under A, T)."""
    M, N = len(Qm), len(Qm[0])
    MUL = F.MUL
    npts = 4 ** N
    # table of P
    Ptab = [0] * npts
    for x in range(npts):
        s = unpack(x, N)
        y = 0
        for k in range(M):
            q = Qm[k]
            acc = 0
            for i in range(N):
                si = s[i]
                if si:
                    t = 0
                    row = q[i]
                    for j in range(i, N):
                        if row[j] and s[j]:
                            t ^= MUL[row[j]][s[j]]
                    acc ^= MUL[si][t]
            y |= acc << (2 * k)
        Ptab[x] = y
    fibre = {}
    for x, y in enumerate(Ptab):
        fibre.setdefault(y, []).append(x)
    nfib = [len(fibre.get(y, ())) for y in range(4 ** M)]
    e = [1 << (2 * i) for i in range(N)]          # basis of F^N
    f = [1 << (2 * i) for i in range(M)]          # basis of F^M
    Pe = [Ptab[e[i]] for i in range(N)]
    Be = {(i, j): Ptab[e[i] ^ e[j]] ^ Pe[i] ^ Pe[j] for i in range(N) for j in range(i + 1, N)}

    def smul_packed(c, x, n):
        return pack([MUL[c][a] for a in unpack(x, n)])

    def frob_packed(x, n):
        return pack([MUL[a][a] for a in unpack(x, n)])

    # candidate T: sigma-semilinear bijections of F^M preserving fibre sizes.  The table of T on
    # span(f_0..f_{i-1}) is extended one basis vector at a time and checked at once.
    def all_T(twist):
        out = []
        mulcol = {}

        def scaled(c, y):
            key = (c, y)
            if key not in mulcol:
                mulcol[key] = smul_packed(c, y, M)
            return mulcol[key]

        def rec(i, tab):
            if i == M:
                if len(set(tab)) == 4 ** M:
                    out.append(tab)
                return
            for col in range(1, 4 ** M):
                if nfib[col] != nfib[f[i]]:
                    continue
                new = list(tab)
                ok = True
                for c in (1, 2, 3):
                    cc = MUL[c][c] if twist else c
                    img = scaled(cc, col)
                    for y in range(4 ** i):
                        z = tab[y] ^ img
                        if nfib[z] != nfib[y | (c << (2 * i))]:
                            ok = False
                            break
                    if not ok:
                        break
                    new.extend(tab[y] ^ img for y in range(4 ** i))
                if ok:
                    rec(i + 1, new)

        rec(0, [0])
        return out

    found = {False: [], True: []}
    for twist in (False, True):
        for Ttab in all_T(twist):
            tP = [Ttab[Pe[i]] for i in range(N)]
            tB = {key: Ttab[val] for key, val in Be.items()}
            S = [fibre.get(tP[i], []) for i in range(N)]
            if any(not s for s in S):
                continue

            def rec(i, imgs, lists):
                # lists[j] for j >= i: candidates for the image of e_j compatible with imgs
                if i == N:
                    # images must be independent: check bijectivity through the span size
                    rows = [unpack(v, N) for v in imgs]
                    if F.rank(rows, N) == N:
                        found[twist].append((list(imgs), Ttab))
                    return
                for v in lists[i]:
                    pv = Ptab[v]
                    new = []
                    ok = True
                    for j in range(i + 1, N):
                        want = tB[(i, j)]
                        lj = [w for w in lists[j] if Ptab[v ^ w] ^ pv ^ Ptab[w] == want]
                        if not lj:
                            ok = False
                            break
                        new.append(lj)
                    if ok:
                        rec(i + 1, imgs + [v], lists[:i + 1] + new)

            rec(0, [], S)
    # verify every pair on all points (linear) or on random points (semilinear)
    for twist in (False, True):
        for imgs, Ttab in found[twist]:
            for x in range(0, npts, max(1, npts // 4096)):
                s = unpack(x, N)
                z = 0
                for i in range(N):
                    c = s[i]
                    if twist:
                        c = MUL[c][c]
                    if c:
                        z ^= smul_packed(c, imgs[i], N)
                assert Ptab[z] == Ttab[Ptab[x]]
    return found[False], found[True]


def is_scaling(imgs, N):
    c = imgs[0] & 3
    return c != 0 and all(imgs[i] == (c << (2 * i)) for i in range(N))


# ---------------------------------------------------------------------------------------------
# Part C: the rank lemmas.  Base field F_4 inside F_16; O = span of the last M unit vectors.
# ---------------------------------------------------------------------------------------------

def monomials(N):
    return [(i, j) for i in range(N) for j in range(i, N)]


def gamma2_matrix(F, A, lie):
    """Matrix (list of columns as dicts) of Gamma^2(A), or of D_A if lie, on the basis
    e_i⊗e_i, e_i·e_j (i < j) of the symmetric tensors."""
    N = len(A)
    MUL = F.MUL
    mons = monomials(N)
    idx = {m: t for t, m in enumerate(mons)}
    cols = []
    for (i, j) in mons:
        col = [0] * len(mons)
        if not lie:
            if i == j:
                for a in range(N):
                    col[idx[(a, a)]] ^= MUL[A[a][i]][A[a][i]]
                    for b in range(a + 1, N):
                        col[idx[(a, b)]] ^= MUL[A[a][i]][A[b][i]]
            else:
                for a in range(N):
                    for b in range(a + 1, N):
                        col[idx[(a, b)]] ^= MUL[A[a][i]][A[b][j]] ^ MUL[A[b][i]][A[a][j]]
        else:
            if i == j:
                for a in range(N):
                    if a != i:
                        col[idx[(min(a, i), max(a, i))]] ^= A[a][i]
            else:
                for a in range(N):
                    if a != j:
                        col[idx[(min(a, j), max(a, j))]] ^= A[a][i]
                    if a != i:
                        col[idx[(min(a, i), max(a, i))]] ^= A[a][j]
        cols.append(col)
    return mons, cols


def delta_rank(F, A, M, lam, lie):
    """rank of pi∘(Phi - lam) : Gamma^2 -> Gamma^2 / Gamma^2(O)."""
    N = len(A)
    V = N - M
    mons, cols = gamma2_matrix(F, A, lie)
    keep = [t for t, (i, j) in enumerate(mons) if i < V]   # not oil-oil
    rows = []
    for t, col in enumerate(cols):
        c = col[:]
        c[t] ^= lam
        rows.append([c[u] for u in keep])
    return F.rank(rows, len(keep))


def rank_of(F, A):
    return F.rank(A, len(A[0]))


def lemma_bounds(F, A, M, lam, lie, sub):
    """The bounds of Lemma E for this A, lambda and O; sub = the subfield F_4 as elements."""
    N = len(A)
    V = N - M
    MUL = F.MUL
    # mu in the base field minimizing rank(A - mu)
    best = None
    for mu in sub:
        Amu = [[A[i][j] ^ (mu if i == j else 0) for j in range(N)] for i in range(N)]
        r = rank_of(F, Amu)
        if best is None or r < best[0]:
            best = (r, mu, Amu)
    r, mu, Amu = best
    if r == N or (mu == 0 and not lie):
        return r, 0
    E = F.kernel(Amu, N)
    e = len(E)
    # e0 = dim E ∩ O: vectors of E with zero vinegar part
    e0 = e - (rank_of(F, [v[:V] for v in E]) if V else 0)
    e1 = e - e0
    if not lie:
        Rm = [[MUL[mu][A[i][j]] ^ (lam if i == j else 0) for j in range(N)] for i in range(N)]
    else:
        Rm = [[A[i][j] ^ ((mu ^ lam) if i == j else 0) for j in range(N)] for i in range(N)]
    rp = rank_of(F, Rm)
    bound = 0
    for m in range(e1 + 1):
        j = min(m, rp)
        bound = max(bound, m * rp - j * (j + 1) // 2 + e0 * max(0, rp - M - m))
    return r, bound


def free_probe(F, A, M, rng, sub, tries=400):
    """Greedy t_1..t_rho with t_j, A t_j independent modulo O; returns rho."""
    N = len(A)
    V = N - M
    span = []
    rho = 0
    while True:
        ok = False
        for _ in range(tries):
            t = [rng.choice(sub) for _ in range(N)]
            at = F.matvec(A, t)
            cand = span + [t[:V], at[:V]]
            if rank_of(F, cand) == len(cand):
                span = cand
                rho += 1
                ok = True
                break
        if not ok:
            return rho


def random_structured(F, N, M, rng, sub, kind):
    """Matrices over the subfield F_4 that are close to scalar, or preserve O, or generic."""
    V = N - M
    nz = [c for c in sub if c]
    mu = rng.choice(nz)
    A = [[mu if i == j else 0 for j in range(N)] for i in range(N)]

    def add_rank_one(w, phi):
        for i in range(N):
            for j in range(N):
                A[i][j] ^= F.MUL[w[i]][phi[j]]

    rv = lambda: [rng.choice(sub) for _ in range(N)]
    if kind == "generic":
        return [[rng.choice(sub) for _ in range(N)] for _ in range(N)]
    if kind == "rank1":
        add_rank_one(rv(), rv())
    elif kind == "rank1-oil":       # image in O
        add_rank_one([0] * V + [rng.choice(sub) for _ in range(M)], rv())
    elif kind == "rank1-oilker":    # image in O, kernel contains O
        add_rank_one([0] * V + [rng.choice(sub) for _ in range(M)],
                     [rng.choice(sub) for _ in range(V)] + [0] * M)
    elif kind == "rank2":
        add_rank_one(rv(), rv())
        add_rank_one(rv(), rv())
    elif kind == "rank3":
        for _ in range(3):
            add_rank_one(rv(), rv())
    elif kind == "oil-block":       # scalar on the vinegar part, generic on O, preserves O
        for i in range(V, N):
            for j in range(V, N):
                A[i][j] = rng.choice(sub)
    elif kind == "diag":
        for i in range(N):
            A[i][i] = rng.choice(nz)
    return A


def check_rank_lemmas(seed, N=7, M=2, trials=12):
    F = GF(4)
    rng = random.Random(seed)
    # the subfield F_4 of F_16: elements with x^4 = x
    sub = [x for x in range(16) if F.MUL[F.MUL[x][x]][F.MUL[x][x]] == x]
    assert len(sub) == 4
    kinds = ["generic", "rank1", "rank1-oil", "rank1-oilker", "rank2", "rank3", "oil-block",
             "diag"]
    stats = {}
    for kind in kinds:
        slack = None
        n = 0
        for _ in range(trials):
            A = random_structured(F, N, M, rng, sub, kind)
            inv = rank_of(F, A) == N
            for lie in (False, True):
                if not lie and not inv:
                    continue
                rho = free_probe(F, A, M, rng, sub)
                for lam in range(16):
                    d = delta_rank(F, A, M, lam, lie)
                    r, bE = lemma_bounds(F, A, M, lam, lie, sub)
                    if r == 0:
                        continue
                    bF = rho * (rho + 1) // 2
                    assert d >= bE, (kind, lie, lam, d, bE, A)
                    assert d >= bF, (kind, lie, lam, d, bF, A)
                    n += 1
                    sl = d - max(bE, bF)
                    slack = sl if slack is None else min(slack, sl)
        stats[kind] = (n, slack)
    return stats


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    parts = [p.upper() for p in sys.argv[2:]] or ["A", "B", "C"]
    rng = random.Random(seed)
    if "A" in parts:
        print("A. Lie algebra B(s, Xs) = Y P(s): dimension of the solution space")
        for (k, sizes, reps) in [(2, [(8, 3), (12, 5), (16, 6)], 3),
                                 (4, [(12, 5), (16, 6), (20, 8)], 2),
                                 (8, [(10, 4), (16, 6), (30, 11)], 2)]:
            F = GF(k)
            for (N, M) in sizes:
                dims = []
                for _ in range(reps):
                    Qm, _ = toy_key(F, N, M, rng)
                    d, neq, nun = lie_algebra_dim(F, Qm)
                    dims.append(d)
                print(f"  F_{F.q}, (N, M) = ({N}, {M}): {neq} equations, {nun} unknowns, "
                      f"dimensions {dims}")
    if "B" in parts:
        print("B. full symmetry group over F_4 (linear and Frobenius-semilinear bijections)")
        F = GF(2)
        for (N, M, reps) in [(5, 2, 6), (6, 2, 6), (6, 3, 10), (7, 3, 10), (8, 3, 4), (8, 4, 6), (9, 4, 2)]:
            res = []
            for _ in range(reps):
                Qm, _ = toy_key(F, N, M, rng)
                lin, semi = full_group_F4(F, Qm)
                extra = [g for g in lin if not is_scaling(g[0], N)]
                res.append((lie_algebra_dim(F, Qm)[0], len(lin), len(extra), len(semi)))
            print(f"  (N, M) = ({N}, {M}): (dim of the Lie algebra, linear pairs, non-scaling "
                  f"among them, semilinear pairs) per key: {res}")
    if "C" in parts:
        print("C. rank lemmas E and F: A over F_4, lambda over F_16, O = last M coordinates")
        for (N, M) in [(6, 2), (7, 2), (7, 3)]:
            stats = check_rank_lemmas(seed, N, M)
            line = ", ".join(f"{k}: {n} ok (min slack {t})" for k, (n, t) in stats.items())
            print(f"  (N, M) = ({N}, {M}): {line}")


if __name__ == "__main__":
    main()
