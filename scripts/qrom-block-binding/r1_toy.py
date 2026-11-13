#!/usr/bin/env python3
"""Toy check of Q6 Theorem 4 (the `multi` event is a real-world event).

Exact state-vector simulation of a tiny ideal cipher: N = 3 points, 3 keys, random adversary
unitaries between forward/inverse queries. Checks, for the final state psi (purified cipher):

  Pr[MULTI in the key-level compressed database]
      <=  sum_{k<k'} || Pi^k Pi^k' Q_k Q_k' psi ||^2                      (union over pairs)
      <=  ( sqrt(E_real) + sqrt(T2) + sqrt(T3) )^2                        (Theorem 4, exact terms)
  T2 <= p N O,   T3 <= p N tau q,   O <= 2 tau q + 2 N p                  (closed forms)
  T3 <= p N O_db,  O <= |T| + E_real,  O_db <= |T| + union                (review, Q6 §14.3)
  sqrt(union) <= ((1 + sqrt(pN)) sqrt(E_real) + 2 sqrt(pN |T|)) / (1 - sqrt(pN))

O_db is the expected number of (target, opening database key) incidences; |T| = 1 here.

where E_real is the real-world expected number of key pairs that both open the adversary's
target (iota, t), read from the adversary's registers at the end. Pure Python, no numpy.
"""
import itertools, math, random, sys

NP = 3                                   # points
PERMS = list(itertools.permutations(range(NP)))
NS = len(PERMS)                          # 6
INV = [tuple(sorted(range(NP), key=lambda i: s[i])) for s in PERMS]
K = 3
ADV = [(k, x, y, w) for k in range(K) for x in range(NP) for y in range(NP) for w in range(2)]
AIDX = {a: i for i, a in enumerate(ADV)}
NA = len(ADV)
ORC = list(itertools.product(range(NS), repeat=K))
P_DENS = 1.0 / (NP * (NP - 1))


def rand_unitary(n, rng):
    m = [[complex(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in range(n)] for _ in range(n)]
    q = []
    for v in m:
        for u in q:
            c = sum(a.conjugate() * b for a, b in zip(u, v))
            v = [b - c * a for a, b in zip(u, v)]
        nrm = math.sqrt(sum(abs(b) ** 2 for b in v))
        q.append([b / nrm for b in v])
    return q


def apply_adv(psi, U):
    out = {}
    for o, vec in psi.items():
        out[o] = [sum(U[i][j] * vec[j] for j in range(NA)) for i in range(NA)]
    return out


def query(psi, inverse):
    out = {}
    for o, vec in psi.items():
        new = [0j] * NA
        for i, (k, x, y, w) in enumerate(ADV):
            s = INV[o[k]] if inverse else PERMS[o[k]]
            new[AIDX[(k, x, (y + s[x]) % NP, w)]] = vec[i]
        out[o] = new
    return out


def target(a):
    k, x, y, w = a
    return x, (y, (y + 1 + w) % NP)      # iota = x0, t = (a, b) with a != b


def opens(sidx, x0, t):
    s = PERMS[sidx]
    return s[x0] == t[0] and s[(x0 + 1) % NP] == t[1]


def avg_axis(psi, j):
    """P_j psi: replace register j by the uniform superposition (projector onto u_j)."""
    acc = {}
    for o, vec in psi.items():
        key = o[:j] + o[j + 1:]
        if key not in acc:
            acc[key] = [0j] * NA
        r = acc[key]
        for i in range(NA):
            r[i] += vec[i]
    return {o: [v / NS for v in acc[o[:j] + o[j + 1:]]] for o in psi}


def sub(a, b):
    return {o: [x - y for x, y in zip(a[o], b[o])] for o in a}


def pair_norm2(phi, k, k2):
    """|| Pi^k Pi^k2 phi ||^2 with the target read from the adversary register."""
    tot = 0.0
    for o, vec in phi.items():
        for i, a in enumerate(ADV):
            if vec[i] != 0:
                x0, t = target(a)
                if opens(o[k], x0, t) and opens(o[k2], x0, t):
                    tot += abs(vec[i]) ** 2
    return tot


def compressed_multi(psi):
    """Exact Pr[>= 2 non-bot database keys open the target] in F^{(x)K} psi."""
    BOT = NS
    ext = {o: list(v) for o, v in psi.items()}
    for j in range(K):
        new = {}
        groups = {}
        for o in ext:
            groups.setdefault(o[:j] + o[j + 1:], []).append(o)
        for key, _ in groups.items():
            cols = [ext.get(key[:j] + (s,) + key[j:], [0j] * NA) for s in range(NS + 1)]
            for i in range(NA):
                v = [c[i] for c in cols]
                # F = 1 - 2|w><w|, w = (bot - u)/sqrt2, u uniform on the NS values
                ip = (v[BOT] - sum(v[:NS]) / math.sqrt(NS)) / math.sqrt(2)
                for s in range(NS):
                    cols[s][i] = v[s] + 2 * ip / math.sqrt(2 * NS)
                cols[BOT][i] = v[BOT] - 2 * ip / math.sqrt(2)
            for s in range(NS + 1):
                new[key[:j] + (s,) + key[j:]] = cols[s]
        ext = new
    pr = 0.0
    for o, vec in ext.items():
        for i, a in enumerate(ADV):
            if vec[i] != 0:
                x0, t = target(a)
                if sum(1 for s in o if s != BOT and opens(s, x0, t)) >= 2:
                    pr += abs(vec[i]) ** 2
    return pr


def run(seed, nq):
    rng = random.Random(seed)
    amp = 1 / math.sqrt(len(ORC))
    psi = {o: [amp if i == 0 else 0j for i in range(NA)] for o in ORC}
    for _ in range(nq):
        psi = apply_adv(psi, rand_unitary(NA, rng))
        psi = query(psi, rng.random() < 0.5)
    psi = apply_adv(psi, rand_unitary(NA, rng))
    lhs = compressed_multi(psi)
    e_real = t2 = t3 = union = 0.0
    P = [avg_axis(psi, j) for j in range(K)]
    Qp = [sub(psi, P[j]) for j in range(K)]
    for k in range(K):
        for k2 in range(k + 1, K):
            e_real += pair_norm2(psi, k, k2)
            t2 += pair_norm2(P[k], k, k2)
            t3 += pair_norm2(avg_axis(Qp[k], k2), k, k2)
            union += pair_norm2(sub(Qp[k], avg_axis(Qp[k], k2)), k, k2)
    o_db = sum(abs(v[i]) ** 2 for k in range(K) for o, v in Qp[k].items()
               for i, a in enumerate(ADV) if opens(o[k], *target(a)))
    eps = P_DENS * K
    refined = ((1 + math.sqrt(eps)) * math.sqrt(e_real) + 2 * math.sqrt(eps)) / (1 - math.sqrt(eps))
    openers = sum(abs(v[i]) ** 2 for o, v in psi.items() for i, a in enumerate(ADV)
                  for k in range(K) if opens(o[k], *target(a)))
    rhs = (math.sqrt(e_real) + math.sqrt(t2) + math.sqrt(t3)) ** 2
    ok = (lhs <= union + 1e-9 and union <= rhs + 1e-9
          and t2 <= P_DENS * K * openers + 1e-9 and t3 <= P_DENS * K * nq + 1e-9
          and openers <= 2 * nq + 2 * K * P_DENS + 1e-9
          and t3 <= P_DENS * K * o_db + 1e-9 and openers <= 1 + e_real + 1e-9
          and o_db <= 1 + union + 1e-9 and math.sqrt(union) <= refined + 1e-9)
    print(f"seed={seed} q={nq}: Pr[MULTI]={lhs:.5f} union={union:.5f} E_real={e_real:.5f} "
          f"T2={t2:.5f} T3={t3:.5f} rhs={rhs:.5f} openers={openers:.4f} O_db={o_db:.4f} {'OK' if ok else 'FAIL'}")
    return ok


if __name__ == "__main__":
    good = all([run(seed, nq) for nq in (0, 1, 2, 3, 5) for seed in range(3)])
    print("ALL OK" if good else "FAILURE")
    sys.exit(0 if good else 1)
