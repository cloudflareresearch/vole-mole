#!/usr/bin/env python3
"""Hidden slices with the real CRT tables (lean/docs/security/pomfrit-lemmap-tight.md, sections 6, 6A).

A model of the verifier's KOS response function for FAEST-EM-128f shapes (17 trees of widths
8, 7, ..., 7; GF(2^128); 312 gates; 5 CRT masks) that uses faest-arch-opt's matrices F, G, W_tree,
W_gate, W_crt and the tree moduli, read from lean/VoleMole/Verifier/CrtData.lean. Not modelled:
the GGM trees (per-tree VOLE values are sampled directly), the witness rows beyond NW bit rows,
QuickSilver. VOLEHash is a polynomial hash of the same shape (4 outputs, the last hashed row is
mask 0, 4 direct masks); H5 is BLAKE2b truncated to 5 bits.

R0  the tables' bilinear identity; an honest first message passes on all of S.
R1  the forger of section 6.1 (two label classes, slice hidden among 2^63): the slice is a level
    set, E_1^lin off the slice finds nothing; the decoder finds the slice by linear algebra.
R2  j fixed trees with j different label vectors: gate-bit recovery, candidate sets, search;
    with wrong gates: mask slopes from ut, search that tolerates the wrong gates.
R3  table facts used by the decoder: uniqueness of the effective gate bits for several classes.
R4  wrong gates: the level set shrinks to a subspace; kernel guessing still decodes.
R5  black-box extractors: evaluations of the check value off the slice show no collision.

Usage: slice.py [seed] [--quick] [--j10]
"""
import hashlib, os, random, re, sys, time
from math import log2

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "..", "lean", "VoleMole", "Verifier", "CrtData.lean")


def load_tables():
    t = open(SRC).read()
    out = {}
    for m in re.finditer(r"def (\w+) : Array Nat := #\[(.*?)\]", t, re.S):
        out[m.group(1)] = [int(x, 16) for x in re.findall(r"0x[0-9a-fA-F]+", m.group(2))]
    for m in re.finditer(r"def (\w+) : Nat := (0x[0-9a-fA-F]+)", t):
        out[m.group(1)] = int(m.group(2), 16)
    return out


TAB = load_tables()
MOD = TAB["modulusHex"]
MODULI = TAB["treeModuliHex"]
K = [m.bit_length() - 1 for m in MODULI]          # 8, 7, ..., 7
OFF = [sum(K[:i]) for i in range(17)]
ND = sum(K)                                       # 120
NG = len(TAB["gHex"])                             # 312
NM = 5                                            # masks: 1 hashed (QuickSilver), 4 direct
FROW, GROW = TAB["fHex"], TAB["gHex"]             # per gate: a form on u, a form on Delta'


def cols(rows, ncols):
    return [sum(((rows[k] >> c) & 1) << k for k in range(len(rows))) for c in range(ncols)]


WCRT = cols(TAB["wCrtHex"], ND)                   # e(unit vector c)
WTREE = cols(TAB["wTreeHex"], ND)
WGATE = cols(TAB["wGateHex"], NG)
GCOL = cols(GROW, ND)                             # per challenge bit: the gates it enters


def par(x):
    return bin(x).count("1") & 1


def mul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> 128:
            a ^= MOD
    return r


def inv(a):
    r, e = 1, (1 << 128) - 2
    while e:
        if e & 1:
            r = mul(r, a)
        a = mul(a, a)
        e >>= 1
    return r


def pmulmod(a, b, m):
    k = m.bit_length() - 1
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> k:
            a ^= m
    return r


def clmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
    return r


def pmod(a, m):
    k = m.bit_length() - 1
    while a.bit_length() > k:
        a ^= m << (a.bit_length() - 1 - k)
    return a


def lin(columns, x):
    r, c = 0, 0
    while x:
        if x & 1:
            r ^= columns[c]
        x >>= 1
        c += 1
    return r


def elift(d):
    return lin(WCRT, d)


def gamma(d):
    return lin(GCOL, d)


def block(d, i):
    return (d >> OFF[i]) & ((1 << K[i]) - 1)


def tree_mask(trees):
    return sum(((1 << K[i]) - 1) << OFF[i] for i in trees)


_h5 = {}


def h5(e, lab):
    key = (e, lab)
    v = _h5.get(key)
    if v is None:
        v = hashlib.blake2b(e.to_bytes(2, "little") + lab.to_bytes(16, "little"),
                            digest_size=1).digest()[0] & 31
        _h5[key] = v
    return v


def solve(rows, n):
    """Solve an F_2 system. rows: ints, bit k < n the coefficient of unknown k, bit n the right
    side. Returns (particular solution, list of kernel vectors) or None."""
    piv = {}
    for r in rows:
        while r & ((1 << n) - 1):
            p = (r & -r).bit_length() - 1
            if p in piv:
                r ^= piv[p]
            else:
                piv[p] = r
                break
        else:
            if r:
                return None
    for p in sorted(piv, reverse=True):            # back-substitute
        r = piv[p]
        for q in piv:
            if q > p and (r >> q) & 1:
                r ^= piv[q]
        piv[p] = r
    free = [k for k in range(n) if k not in piv]
    x0 = sum(((piv[p] >> n) & 1) << p for p in piv)
    ker = []
    for f in free:
        v = 1 << f
        for p in piv:
            if (piv[p] >> f) & 1:
                v |= 1 << p
        ker.append(v)
    return x0, ker


class Model:
    """Committed data of a first message. uw[i]: NW witness bits of tree i (as an int);
    lab[i]: the 128 label-row bits of tree i."""
    NW = 8

    def __init__(self, rng, uw, lab):
        self.rng, self.uw, self.lab = rng, uw, lab
        self.Vw = [rng.getrandbits(128) for _ in range(self.NW)]
        self.Vcol = [rng.getrandbits(128) for _ in range(ND)]     # unlifted label columns
        self.um = [[rng.getrandbits(K[i]) for i in range(17)] for _ in range(NM)]
        self.vm = [[rng.getrandbits(K[i]) for i in range(17)] for _ in range(NM)]
        self.cmult = [0] * NM
        self.chal = None
        self.C0 = [lin(self.Vcol, GROW[e]) for e in range(NG)]    # labels at Delta' = 0

    # honest mask slopes: any u with u mod M_i = um[m][i]
    def ubar(self, m, hi=0):
        u = 0
        for i in range(17):
            for b in range(K[i]):
                if (self.um[m][i] >> b) & 1:
                    u ^= WCRT[OFF[i] + b]
        return u ^ self._clmul_mtree(hi)

    @staticmethod
    def _clmul_mtree(hi):
        r, a = 0, TAB["mTreeHex"]
        while hi:
            if hi & 1:
                r ^= a
            hi >>= 1
            a <<= 1
        return r                                    # degree < 128 for hi < 2^8

    def labels(self, d):
        """The verifier's gate labels at Delta' = d."""
        out = list(self.C0)
        for i in range(17):
            gi = gamma(d & tree_mask([i]))
            l = self.lab[i]
            e = 0
            while gi:
                if gi & 1:
                    out[e] ^= l
                gi >>= 1
                e += 1
        return out

    def masks(self, d):
        labs = self.labels(d)
        gam = gamma(d)
        hs = [h5(e, labs[e]) for e in range(NG)]
        out = []
        for m in range(NM):
            q = 0
            for i in range(17):
                r = self.vm[m][i] ^ pmulmod(self.um[m][i], block(d, i), MODULI[i])
                q ^= lin(WTREE, r << OFF[i])
            gbits = sum(((hs[e] >> m) & 1) << e for e in range(NG)) ^ (gam & self.cmult[m])
            out.append(q ^ lin(WGATE, gbits))
        return out

    def rows(self, d):
        """Hashed rows (witness, label, mask 0) and the 4 direct masks."""
        et = [elift(d & tree_mask([i])) for i in range(17)]
        q = []
        for j in range(self.NW):
            x = self.Vw[j]
            for i in range(17):
                if (self.uw[i] >> j) & 1:
                    x ^= et[i]
            q.append(x)
        colv = [self.Vcol[c] ^ (self.lab[_TREE[c]] if (d >> c) & 1 else 0) for c in range(ND)]
        for j in range(128):
            x = 0
            for c in range(ND):
                if (colv[c] >> j) & 1:
                    x ^= WCRT[c]
            q.append(x)
        mk = self.masks(d)
        return q + [mk[0]], mk[1:]

    def hash(self, rows):
        r, s = self.chal[:4], self.chal[4:]
        ys = []
        for sk in s:
            acc = 0
            for x in rows:
                acc = mul(acc, sk) ^ x
            ys.append(acc)
        return [mul(r[i], ys[0]) ^ ys[1 + i] for i in range(4)]

    def K0(self, d):
        q, dm = self.rows(d)
        h = self.hash(q)
        return [h[i] ^ dm[i] for i in range(4)]

    def Kv(self, d, ut):
        k, e = self.K0(d), elift(d)
        return tuple(k[i] ^ mul(e, ut[i]) for i in range(4))

    def slope_rows(self, uwbits, labbits, u0):
        return [(uwbits >> j) & 1 for j in range(self.NW)] + \
               [(labbits >> j) & 1 for j in range(128)] + [u0]

    def ut_of(self, uwbits, labbits, ub):
        h = self.hash(self.slope_rows(uwbits, labbits, ub[0]))
        return [h[i] ^ ub[1 + i] for i in range(4)]


_TREE = [i for i in range(17) for _ in range(K[i])]


def gate_diff(M, e, base, lc):
    return h5(e, base) ^ h5(e, base ^ lc)


def forge(M, C, g, wrong=()):
    """Tune c_mult so that the slice {Delta' = g off C} is a level set for the class C (trees
    with the same witness and label rows). Returns the honest mask slopes. Gates in `wrong` get
    a flipped c_mult bit."""
    lc = M.lab[C[0]]
    base = M.labels(g & ~tree_mask(C))
    ub = [M.ubar(m, M.rng.getrandbits(8)) for m in range(NM)]
    for m in range(NM):
        c = 0
        for e in range(NG):
            c |= (((gate_diff(M, e, base[e], lc) >> m) & 1) ^ par(FROW[e] & ub[m])) << e
        M.cmult[m] = c
    for e in wrong:
        M.cmult[0] ^= 1 << e
    return ub


class Decoder:
    """Finds the slice of a class C from the committed data, chall_1 and ut."""

    def __init__(self, M, C, ut):
        self.M, self.C, self.ut = M, C, ut
        self.cm = tree_mask(C)
        self.cbits = [c for c in range(ND) if (self.cm >> c) & 1]
        self.lc = M.lab[C[0]]
        self.fixed = [i for i in range(17) if i not in C and M.lab[i] != self.lc]
        r = M.chal[:4]
        self.coef = [r[i] ^ 1 for i in range(4)]
        h = M.hash(M.slope_rows(M.uw[C[0]], self.lc, 0))
        self.wc = [h[i] ^ ut[i] for i in range(4)]
        self.cw = [[mul(self.coef[i], WGATE[e]) for e in range(NG)] for i in range(4)]

    def tau(self, m, dl):
        q = 0
        for i in self.C:
            q ^= lin(WTREE, pmulmod(self.M.um[m][i], block(dl, i), MODULI[i]) << OFF[i])
        return q

    def const(self, dl):
        """Lambda(dl; a = 0): 4 field elements."""
        e = elift(dl)
        t = [self.tau(m, dl) for m in range(NM)]
        return [mul(e, self.wc[i]) ^ mul(self.coef[i], t[0]) ^ t[1 + i] for i in range(4)]

    def lam(self, dl, a):
        """Lambda(dl; a): the increment of the check value along dl on a slice whose effective
        gate bits are a[m] (312-bit ints)."""
        gm = gamma(dl)
        mu = [lin(WGATE, gm & a[m]) for m in range(NM)]
        c = self.const(dl)
        return [c[i] ^ mul(self.coef[i], mu[0]) ^ mu[1 + i] for i in range(4)]

    def rand_dirs(self, t):
        rng = self.M.rng
        return [sum(1 << c for c in self.cbits if rng.getrandbits(1)) or (1 << self.cbits[0])
                for _ in range(t)]

    # ---- two label classes: the effective gate bits are affine in g ----
    def two_class(self, dirs):
        M = self.M
        lf = M.lab[self.fixed[0]]
        assert all(M.lab[i] == lf for i in self.fixed)
        gbits = [c for c in range(ND) if (tree_mask(self.fixed) >> c) & 1]
        d0 = [gate_diff(M, e, M.C0[e], self.lc) for e in range(NG)]
        d1 = [gate_diff(M, e, M.C0[e] ^ lf, self.lc) for e in range(NG)]
        a0 = [sum((((d0[e] >> m) & 1)) << e for e in range(NG)) ^ M.cmult[m] for m in range(NM)]
        dd = [sum((((d0[e] ^ d1[e]) >> m) & 1) << e for e in range(NG)) for m in range(NM)]
        rows = []
        for dl in dirs:
            gm = gamma(dl)
            base = self.lam(dl, a0)
            colv = []
            for c in gbits:                          # effect of g_c = 1
                sel = gm & GCOL[c]
                mu = [lin(WGATE, sel & dd[m]) for m in range(NM)]
                colv.append([mul(self.coef[i], mu[0]) ^ mu[1 + i] for i in range(4)])
            for i in range(4):
                for bit in range(128):
                    r = ((base[i] >> bit) & 1) << len(gbits)
                    for k in range(len(gbits)):
                        r |= ((colv[k][i] >> bit) & 1) << k
                    rows.append(r)
        sol = solve(rows, len(gbits))
        if sol is None:
            return None
        x0, ker = sol
        g = sum(1 << gbits[k] for k in range(len(gbits)) if (x0 >> k) & 1)
        return g, len(ker)

    # ---- any number of label classes: recover the effective gate bits, then search ----
    def gate_bits(self, dirs):
        """Solve Lambda(dl; a) = 0 for a. Returns (a, mask of determined bits, dim of solutions)."""
        n = NM * NG
        rows = []
        for dl in dirs:
            gm = gamma(dl)
            c = self.const(dl)
            es = [e for e in range(NG) if (gm >> e) & 1]
            for i in range(4):
                for bit in range(128):
                    r = ((c[i] >> bit) & 1) << n
                    for e in es:
                        if (self.cw[i][e] >> bit) & 1:
                            r |= 1 << e
                        if (WGATE[e] >> bit) & 1:
                            r |= 1 << ((1 + i) * NG + e)
                    rows.append(r)
        sol = solve(rows, n)
        if sol is None:
            return None
        x0, ker = sol
        und = 0
        for v in ker:
            und |= v
        a = [(x0 >> (m * NG)) & ((1 << NG) - 1) for m in range(NM)]
        det = [(~(und >> (m * NG))) & ((1 << NG) - 1) for m in range(NM)]
        return a, det, len(ker)

    # ---- the mask slopes from ut and the per-tree VOLE values of C ----
    def slopes(self):
        """The slopes ubar_m with ubar_m = um[m][i] mod M_i on C and ut = H_c(u_C, ubar_0) + ubar_1..4.
        Returns (list of 5 slopes, dimension of the solution space) or None."""
        M = self.M
        mc = 1
        for i in self.C:
            mc = clmul(mc, MODULI[i])
        w = mc.bit_length() - 1
        nt = 128 - w
        base = [0] * NM
        for m in range(NM):
            for i in self.C:
                base[m] ^= lin(WCRT, M.um[m][i] << OFF[i])
        def resid(t0):
            u0 = base[0] ^ clmul(mc, t0)
            return [pmod(self.wc[i] ^ mul(self.coef[i], u0) ^ base[1 + i], mc) for i in range(4)]
        r0 = resid(0)
        cs = [resid(1 << k) for k in range(nt)]
        rows = []
        for i in range(4):
            for b in range(w):
                r = ((r0[i] >> b) & 1) << nt
                for k in range(nt):
                    r |= (((cs[k][i] ^ r0[i]) >> b) & 1) << k
                rows.append(r)
        sol = solve(rows, nt)
        if sol is None:
            return None
        u0 = base[0] ^ clmul(mc, sol[0])
        return [u0] + [self.wc[i] ^ mul(self.coef[i], u0) for i in range(4)], len(sol[1])

    def search(self, a, det, tol=0, max_nodes=1 << 26):
        """Find g (blocks of the fixed trees) with h5-differences matching the gate bits a on all
        but at most `tol` gates."""
        M, fx = self.M, self.fixed
        j = len(fx)
        want = [sum((((a[m] ^ M.cmult[m]) >> e) & 1) << m for m in range(NM)) for e in range(NG)]
        msk = [sum(((det[m] >> e) & 1) << m for m in range(NM)) for e in range(NG)]
        # candidate sets: per gate, the patterns b (one bit per fixed tree) whose label matches
        pref = []
        sizes = []
        for e in range(NG):
            cand = []
            for b in range(1 << j):
                base = M.C0[e]
                for t in range(j):
                    if (b >> t) & 1:
                        base ^= M.lab[fx[t]]
                if (gate_diff(M, e, base, self.lc) ^ want[e]) & msk[e] == 0:
                    cand.append(b)
            sizes.append(len(cand))
            pref.append([{b & ((1 << t) - 1) for b in cand} for t in range(j + 1)])
        # per tree: block value -> the gate bits gamma^i_e as a 312-bit int
        gb = [[gamma(v << OFF[i]) for v in range(1 << K[i])] for i in fx]
        order = sorted(range(NG), key=lambda e: sizes[e])
        nodes = 0
        sols = []
        stack = [(0, [])]
        while stack:
            t, vals = stack.pop()
            if t == j:
                sols.append(sum(vals[k] << OFF[fx[k]] for k in range(j)))
                continue
            for v in range(1 << K[fx[t]]):
                nodes += 1
                if nodes > max_nodes:
                    return None, nodes, sizes
                vv = vals + [v]
                viol = 0
                for e in order:
                    b = 0
                    for k in range(t + 1):
                        b |= ((gb[k][vv[k]] >> e) & 1) << k
                    if b not in pref[e][t + 1]:
                        viol += 1
                        if viol > tol:
                            break
                if viol <= tol:
                    stack.append((t + 1, vv))
        return sols, nodes, sizes

    def certify(self, g):
        """E_1^lin on the slice of g: log2 of the size of the level set through its base point
        (the kernel of the F_2-linear part of the check value in the directions of C)."""
        M = self.M
        base = g & ~self.cm
        k0 = M.Kv(base, self.ut)
        n = len(self.cbits)
        cols_ = []
        for c in self.cbits:
            k1 = M.Kv(base ^ (1 << c), self.ut)
            cols_.append(sum((k0[i] ^ k1[i]) << (128 * i) for i in range(4)))
        rows = [sum(((cols_[k] >> b) & 1) << k for k in range(n)) for b in range(512)]
        return len(solve(rows, n)[1])


def setup(rng, classes):
    """classes: list of (trees, witness bits, label bits)."""
    uw, lab = [0] * 17, [0] * 17
    for trees, w, l in classes:
        for i in trees:
            uw[i], lab[i] = w, l
    M = Model(rng, uw, lab)
    return M


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    quick = "--quick" in sys.argv
    rng = random.Random(int(args[0]) if args else 1)
    ok = True
    GA, GB = list(range(1, 10)), [0] + list(range(10, 17))

    # R0
    bad = 0
    for _ in range(200):
        u, d = rng.getrandbits(128), rng.getrandbits(ND)
        r = 0
        for i in range(17):
            r |= pmulmod(pmod(u, MODULI[i]), block(d, i), MODULI[i]) << OFF[i]
        g = sum((par(FROW[e] & u) & par(GROW[e] & d)) << e for e in range(NG))
        bad += mul(u, elift(d)) != lin(WTREE, r) ^ lin(WGATE, g)
    w, l = rng.getrandbits(8), rng.getrandbits(128)
    M = setup(rng, [(range(17), w, l)])
    M.chal = [rng.getrandbits(128) for _ in range(9)]
    ub = forge(M, list(range(17)), 0)
    ut = M.ut_of(w, l, ub)
    vals = {M.Kv(rng.getrandbits(ND), ut) for _ in range(6)}
    print(f"R0 bilinear identity on 200 random (u, Delta'): failures {bad}; honest first message:"
          f" {len(vals)} check value on 6 random challenges")
    ok &= bad == 0 and len(vals) == 1

    # R1
    wA, wB, lA, lB = 0x5A, 0xC3, rng.getrandbits(128), rng.getrandbits(128)
    M = setup(rng, [(GA, wA, lA), (GB, wB, lB)])
    M.chal = [rng.getrandbits(128) for _ in range(9)]
    gstar = rng.getrandbits(ND) & tree_mask(GA)
    ub = forge(M, GB, gstar)
    ut = M.ut_of(wB, lB, ub)
    on = {M.Kv(gstar | (rng.getrandbits(ND) & tree_mask(GB)), ut) for _ in range(6)}
    offp = [rng.getrandbits(ND) for _ in range(6)]
    off = {M.Kv(d, ut) for d in offp}
    # E_1^lin at a base point off the slice: no direction of B keeps the check value
    b0 = offp[0]
    k0 = M.Kv(b0, ut)
    lin_off = sum(M.Kv(b0 ^ (1 << c), ut) == k0 for c in range(ND) if (tree_mask(GB) >> c) & 1)
    t0 = time.time()
    D = Decoder(M, GB, ut)
    res = D.two_class(D.rand_dirs(1))
    t1 = time.time() - t0
    cert = D.certify(res[0]) if res else -1
    print(f"R1 two label classes, slice hidden among 2^{sum(K[i] for i in GA)}: on the slice"
          f" {len(on)} check value, off it {len(off)} of 6; E_1^lin off the slice: {lin_off}"
          f" kernel directions")
    print(f"   decoder (512 equations in 63 unknowns): slice found = {res is not None and res[0] == gstar},"
          f" other solutions 2^{res[1] if res else '?'}, {t1:.2f} s; E_1^lin on that slice: level set of"
          f" 2^{cert} points")
    ok &= len(on) == 1 and len(off) == 6 and lin_off == 0 and res is not None \
        and res[0] == gstar and res[1] == 0 and cert == 57
    # the decoder for the wrong class (A free, B fixed) finds no slice
    DA = Decoder(M, GA, ut)
    resA = DA.two_class(DA.rand_dirs(1))
    print(f"   decoder for class A with the same ut: {'no slice' if resA is None else 'a slice?'}")
    ok &= resA is None

    # R3 (before R2: uses the same forger shape)
    print("R3 effective gate bits from Lambda(delta; a) = 0 (1560 unknowns), real tables:")
    for C, nd in ((GB, 16), ([0, 10, 11, 12, 13], 16), ([10, 11, 12, 13], 16), ([10, 11, 12], 16),
                  ([0, 10], 15), ([10], 7)):
        fx = [i for i in range(17) if i not in C]
        labs = {i: rng.getrandbits(128) for i in fx}
        lC, wC = rng.getrandbits(128), 0x0F
        Mc = setup(rng, [(C, wC, lC)] + [([i], 0xF0, labs[i]) for i in fx])
        Mc.chal = [rng.getrandbits(128) for _ in range(9)]
        g = rng.getrandbits(ND) & ~tree_mask(C)
        ubc = forge(Mc, C, g)
        utc = Mc.ut_of(wC, lC, ubc)
        Dc = Decoder(Mc, C, utc)
        r = Dc.gate_bits(Dc.rand_dirs(nd))
        true = [sum((par(FROW[e] & ubc[m])) << e for e in range(NG)) for m in range(NM)]
        if r is None:
            print(f"   class width {sum(K[i] for i in C)}: inconsistent"); ok = False; continue
        a, det, dim = r
        good = all((a[m] ^ true[m]) & det[m] == 0 for m in range(NM))
        ndet = sum(bin(det[m]).count('1') for m in range(NM))
        print(f"   class width {sum(K[i] for i in C):2d}, {nd:2d} directions: solution space dim"
              f" {dim}, determined bits {ndet}/1560, equal to F*ubar there: {good}")
        ok &= good

    # R2
    def multi(j, wrong=0):
        fx = GA[:j] if j <= 9 else GA + GB[1:1 + j - 9]
        C = [i for i in range(17) if i not in fx]
        labs = [rng.getrandbits(128) for _ in fx]
        M = setup(rng, [(C, wB, lB)] + [([fx[k]], wA, labs[k]) for k in range(j)])
        M.chal = [rng.getrandbits(128) for _ in range(9)]
        gstar = rng.getrandbits(ND) & tree_mask(fx)
        ub = forge(M, C, gstar, rng.sample(range(NG), wrong))
        ut = M.ut_of(wB, lB, ub)
        t0 = time.time()
        D = Decoder(M, C, ut)
        if wrong:
            sl, sdim = D.slopes()
            a = [sum(par(FROW[e] & sl[m]) << e for e in range(NG)) for m in range(NM)]
            det, how = [(1 << NG) - 1] * NM, f"slopes from ut (solutions 2^{sdim})"
        else:
            a, det, dim = D.gate_bits(D.rand_dirs(12))
            how = "gate bits from 12 directions"
        t1 = time.time() - t0
        sols, nodes, sizes = D.search(a, det, tol=wrong)
        t2 = time.time() - t0 - t1
        cert = D.certify(sols[0]) if sols else -1
        wC = sum(K[i] for i in C)
        print(f"   {j:2d} fixed trees, {j} label vectors, class width {wC}, {wrong} wrong gates:"
              f" {how}, {t1:.1f} s; candidates per gate {sum(sizes) / NG:.1f} of {1 << j};"
              f" search {nodes} nodes = 2^{log2(nodes):.1f}, {t2:.1f} s; slice found ="
              f" {sols == [gstar]}; level set 2^{cert}")
        return sols == [gstar] and cert == wC - wrong

    print("R2 many label classes among the fixed trees (slice among 2^(7j)):")
    for j in ([3, 5] if quick else [5, 7, 8, 9] + ([10] if "--j10" in sys.argv else [])):
        ok &= multi(j)
    ok &= multi(5 if quick else 9, wrong=2)

    # R4
    M = setup(rng, [(GA, wA, lA), (GB, wB, lB)])
    M.chal = [rng.getrandbits(128) for _ in range(9)]
    gstar = rng.getrandbits(ND) & tree_mask(GA)
    wrong = rng.sample(range(NG), 3)
    ub = forge(M, GB, gstar, wrong)
    ut = M.ut_of(wB, lB, ub)
    D = Decoder(M, GB, ut)
    tries, found = 0, None
    while tries < 200 and found is None:
        tries += 1
        r = D.two_class(D.rand_dirs(1))
        if r is not None and r[1] == 0:
            found = r[0]
    cert = D.certify(found) if found is not None else -1
    print(f"R4 3 wrong gates: slice found = {found == gstar} after {tries} guessed directions"
          f" (expected 2^3); E_1^lin on that slice: level set of 2^{cert} points")
    ok &= found == gstar and cert == 54

    # R5
    n = 60 if quick else 300
    seen = {}
    coll = 0
    for _ in range(n):
        d = rng.getrandbits(ND)
        if (d ^ gstar) & tree_mask(GA) == 0:
            continue
        v = M.Kv(d, ut)
        coll += v in seen
        seen[v] = d
    print(f"R5 {n} evaluations of the check value off the slice: collisions {coll}")
    ok &= coll == 0
    print("OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
