#!/usr/bin/env python3
"""Proof-size model for a VOLEitH proof of knowledge of an ML-DSA-44 signature.

Statement (FIPS 204, Algorithm 8), with pk = (rho, t1) and the message public and the signature
(c~, z, h) secret:

  c = SampleInBall(c~)                         SHAKE256(c~) and rejection sampling
  w' = A z - 2^d t1 c  (mod q)                 linear in (z, c)
  w1 = UseHint(h, w')                          rounding, with at most omega hints
  ||z||_inf < gamma1 - beta
  c~ = SHAKE256(mu || w1Encode(w1), 32)        mu = H(H(pk) || M') is public

The binary VOLEitH costs are calibrated from measurements of the c~ hash alone
(test_mldsa_pok_shake: 7 Keccak-f[1600] permutations). The F_q VOLEitH costs follow
voleith_fq/voleith.hpp, re-parameterized for q = 8380417. Everything else is an estimate; see the
comments at each component.

This model predates the implementation and doesn't account for deriving the witness with a PRG
(see "Derived witnesses" in src/voleith.hpp), which makes each witness bit cost one bit of proof.
The implemented all-binary proof (src/mldsa_pok/relation.hpp, with the local PRG) measures
97,981 bytes, 556 ms to prove, and 67 ms to verify (128f, release, Apple M4 Pro).
"""

import math

# ML-DSA-44
Q = 8380417
LOG_Q = math.log2(Q)
K, L = 4, 4
N = 256
D = 13
TAU_C = 39
GAMMA1 = 2**17
GAMMA2 = (Q - 1) // 88
BETA = 78
OMEGA = 80
W1_BITS = 6  # w1 in [0, 44)
Z_RANGE = 2 * (GAMMA1 - BETA - 1) + 1  # number of values of a coefficient of z
R_RANGE = 6 * GAMMA2 + 1  # w' - alpha w1, generously (hinted coefficients reach +-3 gamma2)

# Measured (release, M4 Pro), proof bytes for the c~ hash with 62144 (degree 9) and 50944
# (degree 16) witness bits.
MEASURED = {
    "128f": {"tau": 17, "points": [(62144, 134976), (50944, 111561)]},
    "128s": {"tau": 11, "points": [(62144, 88144), (50944, 73129)]},
}


def binary_cost(params):
    """(fixed bytes, bytes per witness bit) for binary VOLEitH, fitted to the measurements."""
    (w0, p0), (w1, p1) = MEASURED[params]["points"]
    per_bit = (p0 - p1) / (w0 - w1)
    return p0 - per_bit * w0, per_bit


# Keccak-f[1600] with 4 committed states (degree 16).
BITS_PER_PERM = 4 * 1600
C_TILDE_PERMS = 7  # (64 + 768 + 1) bytes in blocks of 136
SIB_PERMS = 2  # absorb c~ (1), plus one more squeeze block (slack for rejections)


def hash_bits():
    w1_bits = K * N * W1_BITS  # input of the c~ hash, part of the witness
    c_tilde_bits = 256  # output of the c~ hash and input of SampleInBall
    return (C_TILDE_PERMS + SIB_PERMS) * BITS_PER_PERM + w1_bits + c_tilde_bits


def sample_in_ball_bits():
    """Estimate of the SampleInBall circuit, after the hash: tau steps of the Fisher-Yates
    shuffle, each with a one-hot encoding of its index j (two 16-bit one-hots, multiplied), the
    set S of nonzero positions (256 bits), and the signs (256 bits); plus an accept flag and an
    8-bit comparison per stream byte for the rejection sampling."""
    per_step = 32 + 256 + 256
    stream_bytes = 136
    return TAU_C * per_step + stream_bytes * (1 + 8 + 8)


def digits(values, base):
    """Base-`base` digits needed for a range of `values` values. An exact bound that isn't a power
    of the base costs no extra digit: e.g., x = x_lo + b x_hi in [0, B] if x_lo, x_hi in [0, b)
    and V_{[0, B // b - 1]}(x_hi) V_{[0, B % b]}(x_lo) = 0 (degree about 2 b; see `mixed`)."""
    return math.ceil(math.log(values, base) - 1e-9)


def all_binary(params):
    """Everything in binary VOLEitH, with the mod-q linear relation checked by random
    combinations, each an adder tree over all bits of z, c, w1, r (as in the GF(2) ML-KEM
    prototype: about 1.1 carries per non-zero signed digit of the weights)."""
    fixed, per_bit = binary_cost(params)
    z_bits = L * N * math.ceil(math.log2(Z_RANGE))
    r_bits = K * N * math.ceil(math.log2(R_RANGE))
    h_bits = K * N
    c_bits = 2 * N
    w1_bits = K * N * W1_BITS
    weighted_bits = z_bits + r_bits + c_bits + w1_bits
    naf_digits = LOG_Q / 3 + 1  # average number of non-zero NAF digits of a 23-bit weight
    # (modq/modq.hpp now uses sparser representations, about 4.1 digits: see "Recoding" there.)
    checks = math.ceil(128 / LOG_Q)
    carries = checks * (1.1 * weighted_bits * naf_digits + 32)
    bits = hash_bits() + sample_in_ball_bits() + z_bits + r_bits + h_bits + carries
    return fixed + per_bit * bits, {"witness bits": bits, "carries": carries}


def fq_cost(tau_q=16, ext=6):
    """(bytes per committed element, bytes per unit of degree, fixed bytes) of F_q VOLEitH, from
    voleith_fq/voleith.hpp: each element costs a correction for each of tau_q - 1 trees plus the
    witness correction; each degree costs (tau_q - 1 + 1) * ext elements of masks and QuickSilver
    coefficients."""
    elt = LOG_Q * tau_q / 8
    per_degree = tau_q * ext * LOG_Q / 8
    fixed = tau_q * (8 * 16 + 16) + 300  # tree openings, IV, hashes
    return elt, per_degree, fixed


def mixed(params, base=16, link_overhead_bits=4, tau_q=16):
    """Binary VOLEitH for the hashes and SampleInBall; F_q VOLEitH for the arithmetic; and links
    for w1 and c. Linking a bit costs (at least) committing it in F_q (as a 0/1 element), plus
    `link_overhead_bits` binary bits for the consistency check (e.g., edaBit bucketing)."""
    fixed_b, per_bit = binary_cost(params)
    elt, per_degree, fixed_q = fq_cost(tau_q)
    linked_bits = K * N * W1_BITS + 2 * N  # w1, and c as (nonzero, sign)
    binary_bits = hash_bits() + sample_in_ball_bits() + link_overhead_bits * linked_bits
    fq_elements = (
        L * N * digits(Z_RANGE, base)  # z, as digits (z itself is linear in them)
        + K * N * digits(R_RANGE, base)  # w' - alpha w1, as digits
        + K * N  # h, plus sum(h) <= omega (another few digits; ignored)
        + linked_bits
    )
    degree = max(2 * base, 3)
    size = fixed_b + per_bit * binary_bits + fixed_q + elt * fq_elements + per_degree * degree
    return size, {
        "binary bits": binary_bits,
        "F_q elements": fq_elements,
        "linked bits": linked_bits,
        "of which linking": elt * linked_bits + per_bit * link_overhead_bits * linked_bits,
    }


def kb(x):
    return f"{x / 1000:7.0f} KB"


def main():
    print("Hash part only (c~ and SampleInBall Keccak, degree 16):")
    for p in MEASURED:
        fixed, per_bit = binary_cost(p)
        print(f"  {p}: {kb(fixed + per_bit * hash_bits())}  ({per_bit:.3f} B/bit, "
              f"{fixed:.0f} B fixed; {per_bit * BITS_PER_PERM / 1000:.1f} KB per permutation)")
    print()
    print("All binary:")
    for p in MEASURED:
        size, info = all_binary(p)
        print(f"  {p}: {kb(size)}  ({info['witness bits'] / 1e6:.2f} M witness bits, "
              f"{info['carries'] / 1e6:.2f} M of them carries)")
    print()
    for tau_q, depth in ((16, 8), (11, 12)):
        print(f"Binary hashes + F_q arithmetic + links (F_q VOLE: {tau_q} trees of 2^{depth} "
              "leaves, MACs in F_q^6):")
        for p in MEASURED:
            for base in (8, 16, 64, 512):
                size, info = mixed(p, base, tau_q=tau_q)
                print(f"  {p}, digits base {base:3}: {kb(size)}  ({info['F_q elements']} F_q "
                      f"elements, degree {2 * base}; linking {kb(info['of which linking']).strip()})")


if __name__ == "__main__":
    main()
