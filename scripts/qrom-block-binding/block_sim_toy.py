#!/usr/bin/env python3
"""Exact toy checks of Q6 Theorem 5 (block representation), written for the review in Q6 §14.

X = Z_2 x {0..3}: N = 8 points, 4 cycles of length 2 under e0. Two keys. Each key k has a public
permutation Q_k of X and a public partition P_k of the cycles into two blocks of B = 4 points;
E_k = Q_k o G_k with G_k acting on each block by an independent uniform permutation. The partitions
are key-dependent. The adversary knows Theta = (Q, P) and only touches the entry e_k = (k, block of
P_k containing cycle 0); queries (forward or inverse) that would touch the other block are no-ops.
That is a legitimate adversary, and the other block registers stay uniform, so they are dropped.

Part A (operator norms, exhaustive). For every stored value G' of the other entry, every query
point, forward and inverse, every character of the response register and several base counts i0:
    || [W, cO_e] ||  <=  2 sqrt2 * sqrt( E_sigma n(sigma) ),   W = sqrt(i0 + n(sigma)), W(bot) = sqrt(i0),
and E_sigma n(sigma) = n_e(e') / (B(B-1)) (Lemma 12.3), for the key-dependent partitions.

Part B (state-vector simulation, random adversaries, forward and inverse queries). Checks
    - the potential:  ||W psi_{t+1}|| <= ||W psi_t|| + 2 sqrt2 sqrt(mu_max)       (steps 1-2, 5),
    - junta:          sum_e ||Q_e psi||^2 <= t                                    (Fact 12.2),
    - step 6:         sqrt(E_real) <= sqrt(M) + sqrt(T2) + sqrt(T3),  M <= <Z'>,
                      T2 <= eps' O_real,  T3 <= eps' O_db,
                      O_real <= |T| + E_real,  O_db <= |T| + M                    (review, refined transfer),
                      sqrt(E_real) <= ((1 + sqrt eps') sqrt<Z'> + 2 sqrt(eps' |T|)) / (1 - sqrt eps').

Part C (Monte Carlo). The Chernoff bound for the exposure count of Lemma 12.4 (pair products of
the indicator vector of a uniform random subset), at toy sizes.

Pure Python. Run: python3 block_sim_toy.py [seeds]
"""
import itertools, math, random, sys

LANE, CYC = 2, 4
NPT = LANE * CYC                       # 8 points, x = 2*c + i
B = 4
DENS = 1.0 / (B * (B - 1))
NPERM = 24
BOT = NPERM


def e0(x):
    return x ^ 1


def make_theta(rng):
    """Public data: Q_k and the block of P_k containing cycle 0 (plus one other cycle)."""
    Q, blocks = [], []
    for _ in range(2):
        q = list(range(NPT))
        rng.shuffle(q)
        Q.append(q)
        other = rng.choice([1, 2, 3])
        blocks.append(sorted([0, 1, 2 * other, 2 * other + 1]))
    return Q, blocks


class Model:
    def __init__(self, rng):
        self.Q, self.blk = make_theta(rng)
        self.Qinv = [[q.index(y) for y in range(NPT)] for q in self.Q]
        self.G = [[dict(zip(b, p)) for p in itertools.permutations(b)] for b in self.blk]
        self.Ginv = [[{v: x for x, v in g.items()} for g in gs] for gs in self.G]
        self.common = [z for z in self.blk[0] if z in self.blk[1]]

    def enc(self, k, s, x):
        return self.Q[k][self.G[k][s][x]]

    def agree_count(self, s0, s1):
        return sum(1 for z in self.common
                   if self.enc(0, s0, z) == self.enc(1, s1, z)
                   and self.enc(0, s0, e0(z)) == self.enc(1, s1, e0(z)))

    def exposure(self, k, s_other):
        """n_e(e') for e = e_k and the other entry e' with value index s_other (Lemma 12.3)."""
        o = 1 - k
        img = {self.Q[k][x] for x in self.blk[k]}
        I = {x for x in self.blk[o] if self.Q[o][x] in img}
        g = self.G[o][s_other]
        return sum(1 for z in self.common if g[z] in I and g[e0(z)] in I)

    def query_value(self, k, s, x, inverse):
        """Response of a query at x under key k, or None if it would leave the allowed entry."""
        if not inverse:
            return self.enc(k, s, x) if x in self.blk[k] else None
        pre = self.Qinv[k][x]
        return self.Ginv[k][s][pre] if pre in self.blk[k] else None


# ---------------------------------------------------------------- Part A: commutator norms

def spectral_norm(C, n, iters=400):
    v = [math.sin(1.0 + 3.7 * i) for i in range(n)]
    lam = 0.0
    for _ in range(iters):
        w = [sum(C[i][j] * v[j] for j in range(n)) for i in range(n)]
        u = [sum(C[i][j] * w[i] for i in range(n)) for j in range(n)]       # C^T C v
        nrm = math.sqrt(sum(a * a for a in u))
        if nrm < 1e-300:
            return 0.0
        lam_new = math.sqrt(nrm / math.sqrt(sum(a * a for a in v)))
        v = [a / nrm for a in u]
        if abs(lam_new - lam) < 1e-13:
            lam = lam_new
            break
        lam = lam_new
    return lam


def part_a(m, verbose=True):
    n = NPERM + 1
    w = [-1.0 / math.sqrt(2 * NPERM)] * NPERM + [1.0 / math.sqrt(2)]
    F = [[(1.0 if i == j else 0.0) - 2 * w[i] * w[j] for j in range(n)] for i in range(n)]
    worst, ok, cnt = 0.0, True, 0
    for k in range(2):
        o = 1 - k
        for s_other in range(NPERM):
            if k == 0:
                nvec = [m.agree_count(s, s_other) for s in range(NPERM)]
            else:
                nvec = [m.agree_count(s_other, s) for s in range(NPERM)]
            mean_n = sum(nvec) / NPERM
            formula = m.exposure(k, s_other) * DENS
            if abs(mean_n - formula) > 1e-12:
                ok = False
                print("FAIL first moment", k, s_other, mean_n, formula)
            bound = 2 * math.sqrt(2) * math.sqrt(mean_n)
            for i0 in (0, 1, 5):
                W = [math.sqrt(i0 + v) for v in nvec] + [math.sqrt(i0)]
                for inverse in (False, True):
                    for x in range(NPT):
                        vals = [m.query_value(k, s, x, inverse) for s in range(NPERM)]
                        if vals[0] is None:
                            continue
                        for chi in range(1, NPT):
                            d = [(-1.0) ** bin(chi & v).count("1") for v in vals] + [1.0]
                            # cO = F D F ; C = W cO - cO W
                            FD = [[F[i][j] * d[j] for j in range(n)] for i in range(n)]
                            cO = [[sum(FD[i][l] * F[l][j] for l in range(n)) for j in range(n)]
                                  for i in range(n)]
                            C = [[(W[i] - W[j]) * cO[i][j] for j in range(n)] for i in range(n)]
                            nrm = spectral_norm(C, n)
                            cnt += 1
                            if nrm > bound + 1e-9:
                                ok = False
                                print("FAIL commutator", k, s_other, i0, inverse, x, chi, nrm, bound)
                            if bound > 0:
                                worst = max(worst, nrm / bound)
    if verbose:
        print(f"part A: {cnt} blocks, max ||[W,cO]|| / (2 sqrt2 sqrt(E n)) = {worst:.4f} "
              f"{'OK' if ok else 'FAIL'}")
    return ok


# ---------------------------------------------------------------- Part B: state simulation

NA = 2 * NPT * NPT                     # adversary register (k, x, y)


def aidx(k, x, y):
    return (k * NPT + x) * NPT + y


def rand_unitary(n, rng):
    q = []
    for _ in range(n):
        v = [complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(n)]
        for u in q:
            c = sum(a.conjugate() * b for a, b in zip(u, v))
            v = [b - c * a for a, b in zip(u, v)]
        nrm = math.sqrt(sum(abs(b) ** 2 for b in v))
        q.append([b / nrm for b in v])
    return q


def apply_adv(psi, U):
    return {o: [sum(Ui[j] * vec[j] for j in range(NA)) for Ui in U] for o, vec in psi.items()}


def query(m, psi, inverse):
    out = {}
    for o, vec in psi.items():
        new = [0j] * NA
        for k in range(2):
            for x in range(NPT):
                v = m.query_value(k, o[k], x, inverse)
                v = 0 if v is None else v
                for y in range(NPT):
                    new[aidx(k, x, y ^ v)] = vec[aidx(k, x, y)]
        out[o] = new
    return out


def target(a):
    """Target read from the adversary register: x0 in cycle 0, t = (a, b), a != b."""
    k, x, y = a // (NPT * NPT), (a // NPT) % NPT, a % NPT
    return k, (y, (y + 1 + x % 7) % NPT)


TARGETS = [target(a) for a in range(NA)]


def opens(m, k, s, x0, t):
    return s != BOT and m.enc(k, s, x0) == t[0] and m.enc(k, s, e0(x0)) == t[1]


def avg_axis(psi, j):
    """P_j: project register j on the uniform vector (purified states, no bot)."""
    acc = {}
    for o, vec in psi.items():
        key = o[1 - j]
        r = acc.setdefault(key, [0j] * NA)
        for i in range(NA):
            r[i] += vec[i]
    return {o: [v / NPERM for v in acc[o[1 - j]]] for o in psi}


def sub(a, b):
    return {o: [x - y for x, y in zip(a[o], b[o])] for o in a}


def compress(psi):
    ext = dict(psi)
    for j in range(2):
        new = {}
        others = sorted({o[1 - j] for o in ext})
        for r in others:
            def key(s):
                return (s, r) if j == 0 else (r, s)
            cols = [list(ext.get(key(s), [0j] * NA)) for s in range(NPERM + 1)]
            for i in range(NA):
                tot = sum(cols[s][i] for s in range(NPERM))
                ip = (cols[BOT][i] - tot / math.sqrt(NPERM)) / math.sqrt(2)
                add = 2 * ip / math.sqrt(2 * NPERM)
                for s in range(NPERM):
                    cols[s][i] += add
                cols[BOT][i] -= 2 * ip / math.sqrt(2)
            for s in range(NPERM + 1):
                new[key(s)] = cols[s]
        ext = new
    return ext


def weight(vec):
    return sum(abs(v) ** 2 for v in vec)


def part_b(m, seed, nq):
    rng = random.Random(seed)
    amp = 1.0 / NPERM
    psi = {(s0, s1): [amp if i == 0 else 0j for i in range(NA)]
           for s0 in range(NPERM) for s1 in range(NPERM)}
    agree = {(s0, s1): m.agree_count(s0, s1) for s0 in range(NPERM) for s1 in range(NPERM)}
    mu_max = max(max(m.exposure(k, s) for s in range(NPERM)) for k in range(2)) * DENS
    ok = True
    wprev = 0.0
    for t in range(nq):
        psi = apply_adv(psi, rand_unitary(NA, rng))
        psi = query(m, psi, rng.random() < 0.5)
        comp = compress(psi)
        wnorm = math.sqrt(sum(agree[o] * weight(v) for o, v in comp.items() if BOT not in o))
        stored = sum(weight(v) * sum(1 for s in o if s != BOT) for o, v in comp.items())
        step = 2 * math.sqrt(2) * math.sqrt(mu_max) if t >= 1 else 0.0
        if wnorm > wprev + step + 1e-9 or stored > t + 1 + 1e-9:
            ok = False
            print("FAIL potential/junta", t, wnorm, wprev, step, stored)
        wprev = wnorm
    psi = apply_adv(psi, rand_unitary(NA, rng))
    comp = compress(psi)
    zexp = sum(agree[o] * weight(v) for o, v in comp.items() if BOT not in o)

    def both(phi):
        return sum(abs(v[i]) ** 2 for o, v in phi.items() for i in range(NA) if v[i] != 0
                   and opens(m, 0, o[0], *TARGETS[i]) and opens(m, 1, o[1], *TARGETS[i]))

    def single(phi, k):
        return sum(abs(v[i]) ** 2 for o, v in phi.items() for i in range(NA) if v[i] != 0
                   and opens(m, k, o[k], *TARGETS[i]))

    P0 = avg_axis(psi, 0)
    Q0 = sub(psi, P0)
    e_real = both(psi)
    M = both(comp)                                    # = || Pi Pi' Q Q' psi ||^2
    T2 = both(P0)
    T3 = both(avg_axis(Q0, 1))
    o_real = single(psi, 0) + single(psi, 1)
    o_db = single(comp, 0) + single(comp, 1)
    epsp = 2 * DENS                                   # sum over keys of the opening density
    lhs = math.sqrt(e_real)
    closed = ((1 + math.sqrt(epsp)) * math.sqrt(zexp) + 2 * math.sqrt(epsp)) / (1 - math.sqrt(epsp))
    checks = [M <= zexp + 1e-9,
              lhs <= math.sqrt(M) + math.sqrt(T2) + math.sqrt(T3) + 1e-9,
              T2 <= DENS * o_real + 1e-9, T3 <= DENS * o_db + 1e-9,
              o_real <= 1 + e_real + 1e-9, o_db <= 1 + M + 1e-9,
              lhs <= closed + 1e-9]
    ok = ok and all(checks)
    print(f"part B seed={seed} q={nq}: E_real={e_real:.5f} M={M:.5f} <Z'>={zexp:.5f} T2={T2:.5f} "
          f"T3={T3:.5f} O_real={o_real:.4f} O_db={o_db:.4f} closed={closed ** 2:.4f} "
          f"{'OK' if ok else 'FAIL ' + str(checks)}")
    return ok


# ---------------------------------------------------------------- Part C: exposure tail

def part_c(rng, trials=20000):
    """beta' has Bp points; I has m of them; the first d/2 pairs {2j, 2j+1} are beta ∩ beta'."""
    Bp, m_, pairs = 1024, 256, 128
    mean_bound = pairs * (m_ / Bp) ** 2                # 8
    counts = []
    pts = list(range(Bp))
    for _ in range(trials):
        S = set(rng.sample(pts, m_))
        counts.append(sum(1 for j in range(pairs) if 2 * j in S and 2 * j + 1 in S))
    emp_mean = sum(counts) / trials
    ok = emp_mean <= mean_bound * 1.02
    line = [f"mean={emp_mean:.3f} (bound {mean_bound})"]
    for delta in (0.5, 1.0, 1.5, 2.0):
        thr = (1 + delta) * mean_bound
        emp = sum(1 for c in counts if c >= thr) / trials
        ch = (math.exp(delta) / (1 + delta) ** (1 + delta)) ** mean_bound
        ok = ok and emp <= ch + 3 * math.sqrt(ch / trials) + 1e-12
        line.append(f"d={delta}: {emp:.5f}<={ch:.5f}")
    print("part C:", "  ".join(line), "OK" if ok else "FAIL")
    return ok


if __name__ == "__main__":
    nseeds = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    good = True
    for seed in range(nseeds):
        m = Model(random.Random(1000 + seed))
        print(f"theta seed={seed}: blocks={m.blk} |common|={len(m.common)}")
        good = part_a(m) and good
        good = part_b(m, seed, 1 + seed % 3) and good
    good = part_c(random.Random(7)) and good
    print("ALL OK" if good else "FAILURE")
    sys.exit(0 if good else 1)
