#!/usr/bin/env python3
"""Toy check of lean/docs/security/pomfrit-lemmap-tight.md (sections 3-6).

A small VOLE-in-the-head response function with the shape of the implementation's KOS check:
4 trees of widths (3, 2, 2, 2) (9 challenge bits), field GF(2^32), 4 witness bit rows per tree,
one hashed mask row, 2 direct masks, check value K(D) = H_c(Q(D)) + D(D) + e(D)*ut in F^2.

E1  attack on the widest-group rule E_1: two prefix groups, the prover commits to the minority
    through ut; the accepting sets are the slices where the majority's blocks are guessed.
E2  ut determines the slope: over all pairs of challenges, one witness slope per forced ut.
E3  kernel extractor (affine responses): the slope read from the kernel of the linear part.
E4  hidden slice: with masks that are affine only on one slice, the kernel test at a base point
    off the slice finds nothing, but the slope is still determined by ut.
"""
import itertools, random, sys
from collections import defaultdict

POLY = (1 << 32) | 0x8D  # x^32 + x^7 + x^3 + x^2 + 1


def mul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        if a >> 32:
            a ^= POLY
        b >>= 1
    return r


def inv(a):
    r, e = 1, (1 << 32) - 2
    while e:
        if e & 1:
            r = mul(r, a)
        a = mul(a, a)
        e >>= 1
    return r


W = (3, 2, 2, 2)
OFF = (0, 3, 5, 7)
NB = 9
LW = 4  # witness rows


def blocks(d):
    return tuple((d >> OFF[i]) & ((1 << W[i]) - 1) for i in range(4))


class Toy:
    def __init__(self, rng, uA, uB, hidden=None):
        self.rng = rng
        self.ebits = [rng.getrandbits(32) | 1 << (31 - k) for k in range(NB)]  # independent
        self.u = [uA, uA, uB, uB]  # trees 0,1: group A (5 bits); trees 2,3: group B (4 bits)
        self.V = [rng.getrandbits(32) for _ in range(LW + 3)]
        self.Um = [rng.getrandbits(32) for _ in range(3)]  # honest mask slopes
        self.c = [rng.getrandbits(32) for _ in range(5)]  # r0, r1, s0, s1, s2
        self.hidden = hidden
        if hidden is not None:  # noise nu(D_A) * lin(D_B), zero on the slice D_A = hidden
            self.nu = {g: (0 if g == hidden else rng.getrandbits(32)) for g in range(32)}
            self.lin = [[rng.getrandbits(32) for _ in range(4)] for _ in range(3)]

    def e(self, d):
        r = 0
        for k in range(NB):
            if d >> k & 1:
                r ^= self.ebits[k]
        return r

    def etree(self, d, i):
        return self.e(d & (((1 << W[i]) - 1) << OFF[i]))

    def resp(self, d):
        q = []
        for j in range(LW):
            x = self.V[j]
            for i in range(4):
                if self.u[i][j]:
                    x ^= self.etree(d, i)
            q.append(x)
        m = [self.V[LW + k] ^ mul(self.Um[k], self.e(d)) for k in range(3)]
        if self.hidden is not None:
            g, db = d & 31, d >> 5
            for k in range(3):
                t = 0
                for b in range(4):
                    if db >> b & 1:
                        t ^= self.lin[k][b]
                m[k] ^= mul(self.nu[g], t)
        return q + [m[0]], m[1:]  # hashed rows, direct masks

    def hash(self, rows):
        r0, r1, s0, s1, s2 = self.c
        def P(s):
            acc = 0
            for x in rows:
                acc = mul(acc, s) ^ x
            return acc
        y0 = P(s0)
        return (mul(r0, y0) ^ P(s1), mul(r1, y0) ^ P(s2))

    def K0(self, d):
        q, dm = self.resp(d)
        h = self.hash(q)
        return (h[0] ^ dm[0], h[1] ^ dm[1])

    def K(self, d, ut):
        k, e = self.K0(d), self.e(d)
        return (k[0] ^ mul(e, ut[0]), k[1] ^ mul(e, ut[1]))

    def ut_of(self, ubits):  # the ut of an honest prover with witness rows ubits
        h = self.hash([int(b) for b in ubits] + [self.Um[0]])
        return (h[0] ^ self.Um[1], h[1] ^ self.Um[2])

    def wslope(self, d0, d1):  # witness-row slope of the secant, None if not bits
        q0, q1 = self.resp(d0)[0], self.resp(d1)[0]
        ie = inv(self.e(d0) ^ self.e(d1))
        s = tuple(mul(q0[j] ^ q1[j], ie) for j in range(LW))
        return s


def level_sets(t, ut):
    ls = defaultdict(list)
    for d in range(1 << NB):
        ls[t.K(d, ut)].append(d)
    return [v for v in ls.values() if len(v) >= 2]


def kernel_slopes(t, ut, base):
    """Slopes of all nonzero kernel elements of the linear part of K at `base` (brute force)."""
    kb = t.K(base, ut)
    out = set()
    for delta in range(1, 1 << NB):
        if t.K(base ^ delta, ut) == kb:
            out.add(t.wslope(base, base ^ delta))
    return out


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    uA, uB = (1, 0, 1, 1), (0, 1, 1, 0)
    bits = lambda u: tuple(int(b) for b in u)
    ok = True

    t = Toy(rng, uA, uB)
    for name, u, fixed in (("B (minority, width 4)", uB, 5), ("A (majority, width 5)", uA, 4)):
        ls = level_sets(t, t.ut_of(u))
        sizes = sorted({len(v) for v in ls})
        slopes = {t.wslope(v[0], v[1]) for v in ls}
        print(f"E1 ut of group {name}: {len(ls)} level sets, sizes {sizes}, slopes {slopes}")
        ok &= sizes == [1 << (NB - fixed)] and slopes == {bits(u)} and len(ls) == 1 << fixed
    print("   E_1 (widest group) outputs A's prefix whatever ut is; with ut of B every accepting"
          " set has B's witness: Pr[chal3 accepted | guess] = 2^-5 = 2^-(width of A)")

    forced = defaultdict(set)
    for d0, d1 in itertools.combinations(range(1 << NB), 2):
        k0, k1 = t.K0(d0), t.K0(d1)
        ie = inv(t.e(d0) ^ t.e(d1))
        forced[(mul(k0[0] ^ k1[0], ie), mul(k0[1] ^ k1[1], ie))].add(t.wslope(d0, d1))
    multi = sum(1 for s in forced.values() if len(s) > 1)
    print(f"E2 {len(forced)} forced ut over all pairs; with more than one witness slope: {multi}")
    ok &= multi == 0

    for name, u in (("A", uA), ("B", uB)):
        s = {kernel_slopes(t, t.ut_of(u), rng.getrandbits(NB)) == {bits(u)} for _ in range(8)}
        print(f"E3 kernel slope at 8 random base points, ut of {name}: correct = {s}")
        ok &= s == {True}
    s = kernel_slopes(t, (rng.getrandbits(32), rng.getrandbits(32)), 0)
    print(f"   random ut: kernel slopes {s} (empty: no accepting set with 2 points)")

    gstar = 19
    th = Toy(rng, uA, uB, hidden=gstar)
    ut = th.ut_of(uB)
    ls = level_sets(th, ut)
    print(f"E4 hidden slice D_A = {gstar}: level sets with >= 2 points: {len(ls)}, sizes "
          f"{sorted(len(v) for v in ls)}, on the slice: {all((d & 31) == gstar for v in ls for d in v)},"
          f" slopes { {th.wslope(v[0], v[1]) for v in ls} }")
    off = [kernel_slopes(th, ut, b) for b in range(1 << NB) if (b & 31) != gstar]
    print(f"   kernel test at the {len(off)} base points off the slice: nonempty = "
          f"{sum(1 for s in off if s)}")
    ok &= len(ls) == 1 and len(ls[0]) == 16 and not any(off)
    print("OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
