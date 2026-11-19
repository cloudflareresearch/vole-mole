# Mod-q checks by product-tree sumcheck in the exponent

Status: prototype (branch `proto/sumcheck-modq`). This note describes the protocol that replaces
the binary adders of `src/modq/` (`ModQ`, `Columns`) for the ML-DSA-44 proof of knowledge. It
follows Longfellow's exact mode (`lf/rust/src/runtime/v2/foreign/adapter/exact.rs`), but proves
the two product trees with a GKR-style sumcheck inside the VOLEitH proof instead of a separate
circuit.

## The claims

After the gadget's witness is committed, the verifier derives NUM_CHECKS = 6 random combinations
(see `verify_gadget.hpp`). For the n = `MlDsaModQ::NUM_BITS` = 47,616 committed value bits x_b
(bits of z, c, psi, f, in `ModQ::circuit` order), check k is

    sum_b w_{k,b} x_b = B_k (mod q),   q = 8380417,

with public w_{k,b} = W_{k,j} 2^{t_{j,b}} mod q in [0, q) (nonnegative canonical) and
B_k = A_k + sum_j W_{k,j} offset(j) mod q in [0, q). Each check has soundness error 1/q, so
q^-6 < 2^-137 for the six (unchanged from the adder version).

## 1. Addition in the exponent

Let G = GF(2^128)^* (the field of QuickSilver, modulus x^128 + x^7 + x^2 + x + 1, elements as
16 little-endian bytes: bit j is the coefficient of x^j), of order M = 2^128 - 1, and g a
generator: the least integer >= 2 (as a polynomial) with g^(M/p) != 1 for all nine prime factors
p of M (3, 5, 17, 257, 641, 65537, 274177, 6700417, 67280421310721), as in `exact.rs`.

**Integer form.** With S_k = sum_b w_{k,b} x_b (an integer), the claim is S_k = B_k + q k_k for
an integer k_k. Since 0 <= S_k <= n (q - 1), an honest k_k is in [0, n), so the prover commits
to k_k with kappa = bit_width(n - 1) bits (kappa = 16). Conversely any committed kappa-bit word
is in [0, 2^kappa).

**Packing.** Lanes have width lambda = kappa + 23 (= 39). Claims 3T, 3T + 1, 3T + 2 go to tree
T in {0, 1}, claim 3T + l in lane l. Tree T checks

    prod_b (1 + x_b (g^{E_{T,b}} - 1)) * prod_{l<3, s<kappa} (1 + k_{3T+l,s} (g^{-q 2^{lambda l + s}} - 1))
        = g^{sum_l 2^{lambda l} B_{3T+l}},

with E_{T,b} = sum_l 2^{lambda l} w_{3T+l,b}. Every factor is 1 + x (h - 1) for a committed bit
x, i.e., h^x, so for bits the product is g^{sum_l 2^{lambda l} D_l + RHS} with
D_l = S_{3T+l} - q k_{3T+l} - B_{3T+l}.

**Exactness.** For any bits (honest or not): 0 <= S < n q <= 2^kappa q < 2^lambda, and
0 <= q k + B <= q (2^kappa - 1) + q - 1 < 2^lambda, so |D_l| < 2^lambda. The two sides are equal
in G iff sum_l 2^{lambda l} D_l = 0 (mod M); since |sum_l 2^{lambda l} D_l| < 2^{3 lambda} = 2^117
< M, iff sum_l 2^{lambda l} D_l = 0 over the integers, and since |D_l| < 2^lambda, iff every
D_l = 0 (reduce mod 2^lambda: D_0 = 0, then divide and repeat). So each tree is exactly the three
integer equations S_k = B_k + q k_k, which imply the claims mod q. (Requires
3 (kappa + 23) < 128, i.e. n <= 2^19.) Bits are bits because every witness bit is (derived
witness, `voleith.hpp`).

**Leaf exponents.** Both parties compute g^{E_{T,b}}. A value's bits have weights
W 2^t mod q for shifts t = 0, 1, 2, ...: going from t to t + 1 doubles each lane, and
2w mod q = 2w - q eps with eps in {0, 1}, so g^{E'} = (g^E)^2 * g^{-q sum_l eps_l 2^{lambda l}}:
one squaring and at most one multiplication from an 8-entry table. A repeated shift reuses the
power; the first bit of each value uses fixed-base tables (3 lanes x 3 bytes x 256 entries,
computed once).

## 2. Product trees by sumcheck

Pad each tree with leaves 1 to 2^D leaves, D = ceil(log2(n + 3 kappa)) (= 16), and stack the two
trees: layer d (0 <= d <= D) has 2^{d+1} nodes, node index nu = T 2^d + i with d + 1 bits, and
V_d(nu) = V_{d+1}(2 nu) V_{d+1}(2 nu + 1). V_D is the leaves, V_0 the two roots. Write V_d also
for the multilinear extension in d + 1 variables (variable j = bit j of nu), and in GF(2^k)
eq(z, nu) = prod_j (nu_j ? z_j : 1 + z_j). Then

    V_d(z) = sum_nu eq(z, nu) A_d(nu) B_d(nu),   A_d(nu) = V_{d+1}(2 nu), B_d(nu) = V_{d+1}(2 nu + 1).

**Protocol** (all field elements in GF(2^128); "send" means: committed as 128 witness bits, see
section 3):

1. P sends the quotient bits k (6 kappa bits). V picks tau_0. The claim is
   V_0(tau_0) = (1 + tau_0) R_0 + tau_0 R_1 with R_T the public right-hand side of tree T. Set
   z = (tau_0), c = that claim (public).
2. For d = 0, ..., D - 1 (layer d, point z in F^{d+1}, claim c = V_d(z)): for rounds
   j = 0, ..., d, with the reduced claim c (the claim divided by the eq factors of the bound
   variables, prod_{i<j} (1 + z_i + rho_i)):
   - P sends t_1, t_2, the linear and quadratic coefficients of
     t(X) = sum_{nu_{>j}} eq(z_{>j}, nu_{>j}) A(rho_{<j}, X, nu_{>j}) B(rho_{<j}, X, nu_{>j}).
     The (reduced) round polynomial is s(X) = (1 + z_j + X) t(X) (Gruen's factoring of the eq
     term; in characteristic 2, (1 + z)(1 + X) + z X = 1 + z + X), and s(0) + s(1) = c, i.e.,
     c = (1 + z_j) t(0) + z_j t(1), fixes t_0 = c + z_j (t_1 + t_2). Nothing is divided: the
     factors 1 + z_i + rho_i are simply dropped from the claims.
   - V picks rho_j; c <- t(rho_j) = c + (z_j + rho_j) t_1 + (z_j + rho_j^2) t_2.

   Then c should be A_d(rho) B_d(rho).
   - If d < D - 1: P sends a = A_d(rho), b = B_d(rho). V checks c = a b (one QuickSilver
     constraint of degree 2) and picks tau; next z = (tau, rho_0, ..., rho_d) and
     c = V_{d+1}(z) = a + tau (a + b).
   - If d = D - 1: A_{D-1}(rho) and B_{D-1}(rho) are public linear combinations of committed bits:
     A = sum_nu eq(rho, nu) L(2 nu) with leaves L = 1 + x (h - 1), i.e.
     A = 1 + sum_{leaves 2 nu with a bit} eq(rho, nu) (h_{2 nu} - 1) x_{2 nu} (eq sums to 1 over
     the cube, so padding is free), likewise B. V checks c = A B (degree 2).

So V's checks are D constraints of degree 2, plus linear bookkeeping, all on committed values.
The verifier's work is linear in the leaves (the eq table, the leaf exponents, and one
multiply-accumulate per committed bit); the prover's is linear in the 2^{D+1} leaves
(sum_d 2^{d+1} pairs, about 8 multiplications per pair and round, halving each round).

## 3. Commit order and Fiat-Shamir inside VOLEitH

The witness is derived (`voleith.hpp`, "Derived witnesses"): w = e + G(K), with K committed by
VOLE generation (its correction d_K is in the FAEST part) and e public, one bit per witness bit.
The existing order (relation.hpp) is:

1. `voleith_vole_gen`: VOLE commitment, chal1, the VOLE check, d_K, and e for the witness prefix
   (MuHash and VerifyGadget, which contain all x_b).
2. seed = H(SEED_DST, pk, chal1, vole check proof, d_K, e_prefix) (`check_seed`); the weights
   come from the seed.
3. The answer (formerly: the quotients and carries), e for it, then chal2 = H(..., e, d), and
   QuickSilver.

The answer's committed value is fixed by e_answer and K, and K is fixed (extractably, as for any
VOLEitH witness) before chal1. The prover knows G(K) (the values of `PendingProof::derived`), so
it can compute e for any part of the answer before calling `voleith_prove_commit`, which then
recomputes the same e. So the multi-round protocol needs no change to `voleith.hpp`:

- message 0 = the quotient bits, messages 1, 2, ... = the pairs (t_1, t_2) and (a, b), in protocol
  order; each is a byte-aligned slice of the answer (quotients padded to 12 bytes; 32 bytes per
  pair). Write m_i for e restricted to message i (the masked message).
- h_{-1} = seed; h_i = H(SUMCHECK_DST || h_{i-1} || m_i) (32 bytes); challenge i is the first 16
  bytes of h_i, as an element of GF(2^128). Challenge 0 is tau_0, then each rho and tau in order.
- The verifier reads every m_i from e in the proof, recomputes all h_i before QuickSilver, and
  passes the challenges to the constraints (as part of the instance). The prover runs the
  sumcheck with the same chain, then calls `voleith_prove_commit` with the whole answer.
  e (hence every m_i) is also hashed into chal2, as before.

Why this is sound. This is the seed pattern of step 2, iterated: when challenge i is derived, the
committed values of messages 0..i are fixed (by K, which precedes the seed, and m_0..m_i, which
are hashed into h_i through the chain), and so is everything before them. In the ROM, the
extractor recovers K (hence all committed values) from the VOLE commitment, as in the VOLEitH
soundness proof; relative to the extracted values, the hash chain is the Fiat-Shamir transform of
a public-coin protocol with round-by-round soundness, so a prover making Q queries cheats with
probability at most Q eps_rbr (state-restoration soundness; Canetti et al. 2019, Chiesa et al.
2016), plus the QuickSilver and VOLEitH terms, which are unchanged. Hashing m_i rather than the
plain message is necessary (the verifier only sees m_i) and sufficient (m_i determines the
message given K).

Derived or direct bits make no difference: for a directly committed witness, the value is
d + u with u fixed by the VOLE commitment, and the same chain works with the correction d instead
of e (the prover's pad is then u, `vole_com_data.u_bytes()`); `src/sumcheck/voleith_fs.hpp`
handles both.

Alternatives that don't work. Deriving all of a layer's challenges from one hash of all its
messages isn't even complete: the honest t^{(j)} depends on rho_{j-1}. Deriving them from one hash
before the layer's messages (or any challenge before the message it must follow) is unsound: if
the prover knows rho_j before sending t^{(j)}, it can pick any t^{(j)} with t^{(j)}(rho_j) equal
to the value it needs. And the chain must start from the seed, which binds the statement and the
commitment to the witness prefix, so that the claims themselves are fixed before any challenge
("weak" Fiat-Shamir is the classic failure here). One hash per prover message, chained, is the
standard transform, and it costs 152 short hashes.

## 4. Soundness sketch

Per proof (before multiplying by the number Q of hash queries):

- Projections: a false linear system passes 6 random combinations w.p. q^-6 < 2^-137
  (unchanged, seed after the witness).
- Exactness: the tree equation for bits is equivalent to the integer equations (section 1), no
  error.
- Roots: if (V_0(0), V_0(1)) != (R_0, R_1), the claim at tau_0 is false except w.p. 2^-128.
- Rounds: the reduced protocol is itself a sumcheck that never divides by the eq factors: with
  t_j(X) = sum_{nu_{>j}} eq(z_{>j}, nu_{>j}) A(rho_{<j}, X, nu_{>j}) B(rho_{<j}, X, nu_{>j}), the
  true values satisfy c_j = (1 + z_j) t_j(0) + z_j t_j(1) and c_{j+1} = t_j(rho_j). If the
  reduced claim c_j is false, the prover's t (with t_0 derived from c_j) differs from the true
  t_j, both of degree 2, so c_{j+1} is true w.p. <= 2/2^128.
- Layer ends: a b = c with (a, b) != (a*, b*): a + tau (a + b) = a* + tau (a* + b*) for at most
  one tau, w.p. 2^-128.
- The rest is QuickSilver (D degree-2 constraints among the others; the batching error is
  unchanged) and VOLEitH.

Sum of the sumcheck terms: (1 + 2 D (D + 1) / 2 + (D - 1)) / 2^128 < 2^-119 for D = 16, i.e.,
eps_rbr <= 2 / 2^128 per round, so Q eps_rbr <= Q 2^-127.

## 5. Zero knowledge sketch

No sumcheck message appears in the clear: each is 128 witness bits, so the proof contains only
m_i = message + G(K) (and the existing parts). The simulator of VOLEitH with a derived witness
samples e uniformly (indistinguishable by the PRG assumption, now for a shorter output), derives
every challenge from the simulated e exactly as the verifier does, and simulates QuickSilver,
which is HVZK given that the constraints are satisfiable and the masks cover the degree (the new
constraints have degree 2, i.e., 4 over the derived witness, below the relation's 22). The
honest prover's messages are functions of the witness and public challenges; their only trace is
e. The challenges are public-coin, so the simulation is the same as for the existing seed.

## 6. Size

With n value bits, kappa = bit_width(n - 1), D = ceil(log2(n + 3 kappa)):

    answer bits = 8 ceil(6 kappa / 8) + 128 E,   E = 2 sum_{d<D} (d + 1) + 2 (D - 1) = D (D + 1) + 2 (D - 1)

For n = 47,616: kappa = 16, D = 16, E = 302, answer = 96 + 38,656 = 38,752 bits (4,844 bytes),
versus 328,616 bits (41,077 bytes) for the adders. Constraints: D = 16 instead of
CARRY_BUDGET + 6 COLUMNS = 328,856. (The proof shrinks by somewhat more than the answer, since
the derived witness's key is shorter, see `local_key_bits`.)

Possible further reductions (not done): leaves of 2^r bits each, checked with a degree-2^r
constraint at the bottom (D - r layers), or committing the top r layers directly.

## 7. Implementation and measurements

Code: `src/sumcheck/` (`gf128.hpp`: the field and g; `tree_sumcheck.hpp`: the layered sumcheck,
the Fiat-Shamir `Chain`, the committed-element and leaf linear forms; `exp_modq.hpp`: the packing,
leaf exponents and quotients, with `ModQ`'s Spec and semantics; `voleith_fs.hpp`: the prover's
pads and the verifier's masked bytes, for derived and direct witnesses). Tests:
`tests/sumcheck/test_sumcheck.cpp` (exhaustive and random exactness of the exponent encoding,
including the extreme weights q - 1; VOLEitH proofs of small relations, direct and derived, for
D = 3, 8 and 10, rejecting mutated data bits, wrong quotients, flipped bits anywhere in the
answer, and false claims). The ML-DSA PoK uses it unless `VOLE_MOLE_MLDSA_POK_MODQ_ADDERS` is
defined (`MODQ_SUMCHECK` in `verify_gadget.hpp`); the DST is `MLDSA_POK_SUMCHECK_DST`.

`bench_mldsa_pok` medians (clang release, same machine and tree, 5 repetitions):

| | adders | sumcheck |
|---|---|---|
| proof | 66,951 B | 29,307 B |
| witness | 452,128 bits | 162,264 bits |
| VOLE key (local PRG) | 3,200 bits | 2,536 bits |
| prove | 497 ms | 57 ms |
| verify | 81 ms | 8.0 ms |

(Earlier the adders measured 460 / 61 ms on a quieter machine.) The proof is now the FAEST part
(9,024 B) and e (20,283 B: message hash 1,032 B, signature gadget 14,407 B, checks 4,844 B).

Profile (perf, self time). Prove: the Keccak constraints (the c-tilde and SampleInBall
permutations: `qs_mul` products and segmented Keccak) about 70%, SampleInBall 9%, the sumcheck
about 10% (the clear prover, `encode`, `quotients`, the committed linear forms), the PRG 3%.
Verify: the PRG's `qs_eval` 17%, Keccak about 45%, `ExpModQ::encode` 15% (the leaf exponents,
about 270k multiplications), the sumcheck constraints 8% (`qs_element`: 127 constant
multiplications per element, and the leaf linear forms), SampleInBall 3%.

Further reductions, not done:

- Leaves of 2^r bits: L = prod (1 + c x) has degree 2^r in the bits, the final check A B = c
  degree 2^(r+1) (twice that over the derived witness, at most 22 here, so r <= 2). r = 2 gives
  D = 14 and 236 elements, about 1 KB less, at the cost of the products in the leaf forms.
- `qs_element` by shifts instead of constant multiplications, and the leaf exponents with wider
  fixed-base windows (verifier time).

Open: the soundness and ZK sketches above need full proofs, in particular the state-restoration
bound for the chained hashes together with the extraction of K (the VOLEitH extractor must run
before the first sumcheck challenge, as for the existing check seed).
