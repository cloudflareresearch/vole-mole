#!/usr/bin/env python3
"""Generate the 16-entry tables of the WebAssembly simd128 AES S-box in src/aes.rs.

GF(2^8) is written as GF(2^4)[t]/(t^2 + at + a); see the comment on `mod hw` there for the
formulas. The script models `i8x16.swizzle` (an index above 15 selects 0) and checks the result
against the S-box for all 256 inputs before printing the tables.
"""
def mul16(x, y):  # GF(16) = GF(2)[z]/(z^4+z+1)
    r = 0
    for b in range(4):
        if (y >> b) & 1: r ^= x << b
    for b in (6, 5, 4):
        if (r >> b) & 1: r ^= 0b10011 << (b - 4)
    return r
inv16 = [0] + [next(y for y in range(1, 16) if mul16(x, y) == 1) for x in range(1, 16)]
def gmul(x, y):  # AES field
    r = 0
    while y:
        if y & 1: r ^= x
        x = (x << 1) ^ (0x11B if x & 0x80 else 0); y >>= 1
    return r
def sbox(x):
    y = next((c for c in range(256) if gmul(x, c) == 1), 0)
    r = 0x63
    for s in range(5): r ^= ((y << s) | (y >> (8 - s))) & 0xFF
    return r
def sboxlin(y):  # linear part of the affine map
    r = 0
    for s in range(5): r ^= ((y << s) | (y >> (8 - s))) & 0xFF
    return r
INF = 0x80
def swz(t, idx): return t[idx] if idx < 16 else 0
def search():
    for a in range(1, 16):
        # t^2 = a t + a irreducible over GF(16)?
        if any(mul16(r, r) ^ mul16(a, r) ^ a == 0 for r in range(16)): continue
        def kmul(x, y):  # elements (i,k) = i*t + k
            (i1, k1), (i2, k2) = x, y
            hh = mul16(i1, i2)  # t^2 coefficient -> a t + a
            return (mul16(i1, k2) ^ mul16(k1, i2) ^ mul16(hh, a), mul16(k1, k2) ^ mul16(hh, a))
        for bi in range(16):
            for bk in range(16):
                beta = (bi, bk)
                pw = [(0, 1)]
                for _ in range(8): pw.append(kmul(pw[-1], beta))
                # AES poly x^8+x^4+x^3+x+1
                s = [0, 0]
                for e in (8, 4, 3, 1, 0): s[0] ^= pw[e][0]; s[1] ^= pw[e][1]
                if s != [0, 0] or beta == (0, 0) or beta == (0, 1): continue
                yield a, kmul, pw
for a, kmul, pw in search():
    def phi(x):
        i = k = 0
        for b in range(8):
            if (x >> b) & 1: i ^= pw[b][0]; k ^= pw[b][1]
        return (i << 4) | k
    if len({phi(x) for x in range(256)}) != 256: continue
    phinv = {phi(x): x for x in range(256)}
    IN_LO = [phi(n) for n in range(16)]; IN_HI = [phi(n << 4) for n in range(16)]
    INV = [INF] + inv16[1:]
    INVA = [INF] + [mul16(a, inv16[k]) for k in range(1, 16)]
    a2inv = inv16[mul16(a, a)]
    c1 = (mul16(1 ^ a, a2inv), 1); c2 = (a2inv, 0)
    def emb(p, c):
        r = kmul((0, p), c); return phinv[(r[0] << 4) | r[1]]
    O1 = [0] + [sboxlin(emb(inv16[u], c1)) for u in range(1, 16)]
    O2 = [0] + [sboxlin(emb(inv16[v], c2)) for v in range(1, 16)]
    ok = True
    for x in range(256):
        y = IN_LO[x & 15] ^ IN_HI[x >> 4]
        i, k = y >> 4, y & 15
        ak = swz(INVA, k); j = i ^ k
        iak = swz(INV, i) ^ ak; jak = swz(INV, j) ^ ak
        io = swz(INV, iak) ^ j; jo = swz(INV, jak) ^ i
        if swz(O1, io) ^ swz(O2, jo) ^ 0x63 != sbox(x): ok = False; break
    if not ok: continue
    def fmt(n, t): print(f"    const {n}: [u8; 16] = [" + ", ".join(f"0x{v:02x}" for v in t) + "];")
    print("// a =", a)
    fmt("IN_LO", IN_LO); fmt("IN_HI", IN_HI); fmt("INV", INV); fmt("INVA", INVA)
    fmt("SB_I", O1); fmt("SB_J", O2)
    fmt("SB2_I", [gmul(2, v) for v in O1]); fmt("SB2_J", [gmul(2, v) for v in O2])
    break
else:
    print("no solution")
