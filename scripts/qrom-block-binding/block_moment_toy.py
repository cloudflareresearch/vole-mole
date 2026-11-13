#!/usr/bin/env python3
"""Toy check of the first-moment formula behind Q6 Theorem 5 (block representation).

X = Z_L x C (lane-0 coordinate mod L, C cycles), e0 adds 1 to the lane-0 coordinate. A key k has a
public permutation Q_k of X and a public partition P_k of the cycles into blocks; the cipher is
E_k = Q_k o G_k with G_k acting on each block by an independent uniform permutation.

For a stored entry e' = (k', beta') with value G' and a fresh entry e = (k, beta), the expected
number of new agreement points over a uniform G in Sym(beta) is exactly

    n_e(e') / (B (B-1)),   n_e(e') = #{ z in beta ∩ beta' : G'(z), G'(z+e0) in I },
    I = beta' ∩ Q_k'^{-1}(Q_k(beta)).

Also checks that Q_k o G_k is uniform on Sym(X) when Q_k is (exhaustively, N = 4).
Pure Python, exhaustive enumeration.
"""
import itertools, random, sys
from fractions import Fraction

L, C = 2, 4
X = [(i, c) for c in range(C) for i in range(L)]
B = L * C // 2


def e0(z):
    return ((z[0] + 1) % L, z[1])


def check(seed):
    rng = random.Random(seed)
    Qk, Qk2 = ({x: y for x, y in zip(X, rng.sample(X, len(X)))} for _ in range(2))
    Qk2inv = {y: x for x, y in Qk2.items()}
    cyc = list(range(C))
    rng.shuffle(cyc)
    beta = [x for x in X if x[1] in cyc[:C // 2]]          # a block of P_k
    rng.shuffle(cyc)
    beta2 = [x for x in X if x[1] in cyc[:C // 2]]         # a block of P_k'
    G2 = dict(zip(beta2, rng.sample(beta2, len(beta2))))   # stored value of e'
    E2 = {z: Qk2[G2[z]] for z in beta2}
    common = [z for z in beta if z in beta2]
    img = {Qk[x] for x in beta}
    I = {x for x in beta2 if Qk2[x] in img}
    assert I == {x for x in beta2 if x in {Qk2inv[y] for y in img}}
    n_exposed = sum(1 for z in common if G2[z] in I and G2[e0(z)] in I)
    total = 0
    cnt = 0
    for perm in itertools.permutations(beta):
        G = dict(zip(beta, perm))
        total += sum(1 for z in common if Qk[G[z]] == E2[z] and Qk[G[e0(z)]] == E2[e0(z)])
        cnt += 1
    lhs = Fraction(total, cnt)
    rhs = Fraction(n_exposed, B * (B - 1))
    ok = lhs == rhs
    print(f"seed={seed}: |common|={len(common)} |I|={len(I)} exposed={n_exposed} "
          f"E[n]={lhs} formula={rhs} {'OK' if ok else 'FAIL'}")
    return ok


def uniformity():
    """N = 4 (two 2-cycles, one block each): {Q o G} hits every permutation equally often."""
    pts = [(i, c) for c in range(2) for i in range(2)]
    blocks = [[p for p in pts if p[1] == c] for c in range(2)]
    counts = {}
    for q in itertools.permutations(pts):
        Q = dict(zip(pts, q))
        for g0 in itertools.permutations(blocks[0]):
            for g1 in itertools.permutations(blocks[1]):
                G = {**dict(zip(blocks[0], g0)), **dict(zip(blocks[1], g1))}
                e = tuple(Q[G[p]] for p in pts)
                counts[e] = counts.get(e, 0) + 1
    ok = len(counts) == 24 and len(set(counts.values())) == 1
    print("uniformity of Q o G:", "OK" if ok else "FAIL")
    return ok


if __name__ == "__main__":
    good = all([check(s) for s in range(12)] + [uniformity()])
    print("ALL OK" if good else "FAILURE")
    sys.exit(0 if good else 1)
