# Cryptanalysis of OMPR for UOV, second pass

Companion to `ompr-cryptanalysis.md`, cited as **[OC]**. Same setting: UOV over `F = GF(256)`,
`(N, M) = (119, 45)`, `V = 74`, the oracle `D = derive_preimage`, the games OMPR and OMPR⊕τ of
`uov-assumptions.md` (**[UA]**) §3. Other notes: `uov-open-structure.md` (**[UOS]**),
`uov-open-reductions.md` (**[OR]**), `ompr-shift-algebra.md` (**[SA]**). Notation is that of
[OC]: `𝒪`, `vin`, `L_v`, `G`, `Good`, `Bad`, `δ`, `B`, `ψ`; `δ_u = 1 − ∏_{i ≤ M}(1 − q^{−i})`.

This note does five things.
1. It reviews [OC] (§1). The proofs of L1, K1 and Lemma F are right. Three statements are
   corrected, one of them the forgery baseline.
2. Statistics of goodness of every degree (§2): an exact formula for the character sums of the
   bad set, a proved bound for every fixed statistic, a proved tail bound for Lemma F, and a
   heuristic for the largest statistic of degree `d`.
3. Multi-target attacks (§3). One structured family of targets can be solved jointly: the class
   `F^×·t`. This lowers the cost of **every** forgery by one equation (attack P1). Nothing else
   was found.
4. Quantum attacks (§4).
5. Experiments on toy keys (§5), `scripts/ompr-cryptanalysis/ompr_second.py`.

**Status labels** as in [OC]: *proved*, *Lean*, *heuristic*, *estimate*, *experimental*.
Citations are from memory; the literature was not retrieved.

## 0. Summary

| # | Item | Result at `(119, 45, 256)` | Status | Where |
|---|---|---|---|---|
| R1 | [OC] L1 (law of the answers), K1 (`Q²·2^{−585}`), Lemma F (variance) | confirmed; Lemma F also follows from Theorem H | re-derived; experimental | §1 |
| **P1** | **Class attack.** `P(s) ∈ F·t` is 44 homogeneous quadrics; a solution scales to a preimage of `t` | forgery `2^{138.5}` multiplications (`2^{145.6}` bit operations), not `2^{140.3}`. **New baseline B0′.** Uses no call | proved (algebra; Lean `scaled_preimage`); estimate; experimental (gain `2^{2.2}` to `2^{5.7}` on toy keys) | §3.1 |
| R2 | [OC] F2: `D(0)` and the singular line | costs **two** forgeries, `2^{139.5}`: above B0′ | proved (budget lemma) | §3.2 |
| R3 | [OC] K2: dependent sets of answers | a zero of `P` can be tested for being an oil vector. The right reason: spans of answers meet `𝒪` exactly as often as random subspaces | proved | §1 |
| H | Exact Fourier transform of the bad set | `X(w) = Σ_{T ≠ 0, L*(T) = w} κ(rank T)`, for every key | proved; experimental (exact, six keys) | §2.1 |
| T | **Tail of Lemma F.** Largest bias of a linear character, all `w` at once | `≤ 2^{−148}·ε^{−1/4}` except for a fraction `ε` of keys: `≥ 2^{296}·√ε` answers | proved (uniform `P2`) | §2.2 |
| V | Any statistic fixed before the key block `S`, **of any degree** | root mean square bias `≤ 2^{−296}`; `2^{592}` answers. A family of `K` such statistics: `≤ √(K/ε)·2^{−296}` | proved (uniform `P2`, uniform targets) | §2.3 |
| Q | Quadratic statistics of the whole answer | reduce to quadratic statistics of the vinegar | proved (uniform targets) | §2.4 |
| W | Largest bias over **all** polynomials of degree `≤ d` in the vinegar | about `2^{−300}·√(11·binom(74+d, d))`: `2^{−292.5}` at `d = 2`, `2^{−290}` at `d = 3`, `2^{−243}` at `d = 45`. Answers: `2^{585}`, `2^{580}`, `2^{486}` | heuristic (Gaussian extreme value); experimental | §2.5 |
| M1 | `d` targets jointly, on a flat or by a singular `d`-space | dearer than `d` forgeries for every `d ≥ 2` | estimate | §3.3 |
| M2 | Many targets, one solver | no amortization found; the bound stays `n·Adv^{uov}` | open | §3.4 |
| S2′ | Collinear shifts on top of P1 (replaces [OC] S2) | `2^{138.7}` at τ = 17 against `2^{138.5}`; break-even `τ* ≈ 19`; never more than τ below | estimate | §3.5 |
| Q1 | Quantum forgery: Grover over the guesses of hybrid XL | `2^{113}` multiplications, `2^{120}` gates; `2^{148}`, `2^{124}`, `2^{120}` gates at depth `2^{40}`, `2^{64}`, `2^{96}` | estimate | §4.1 |
| Q2 | Quantum key recovery: Grover on Kipnis–Shamir; on the intersection attack | `2^{144}` gates at depth `2^{130}`; `2^{198}` gates | estimate | §4.2 |
| Q3 | Quantum work on classical answers | no gain over Q1, Q2: no periodic function is available without the key | proved (reduction to [OC] L1); heuristic | §4.3 |

**Answers.**
- **The forgery baseline moves to `2^{138.5}`** multiplications in the reference model
  (`2^{145.6}` bit operations), by P1. This is an attack on the UOV problem in characteristic 2,
  not on OMPR: it makes no call. It is above NIST level 1 (`2^{143}` gates) at `(119, 45)`. For
  uov-Ip `(112, 44)` the same model gives `2^{141.9}` bit operations.
- **Degree-`d` statistics do not help.** No statistic chosen without the key block has a bias
  above `2^{−296}` in root mean square, whatever its degree (proved). For key-dependent choices:
  linear ones are bounded by `2^{−148}` for almost all keys (proved), all polynomials of degree
  `d` by about `2^{−300}·√(11·binom(74+d, d))` (heuristic). `2^{64}` answers show nothing.
- **Multi-target.** The class of one target is the only family we can solve jointly. Uniform
  targets have no other common structure, and a call outside the challenge classes costs a
  forgery (budget lemma). Whether XL can be amortized over many right-hand sides is open, for
  UOV and for MQ alike.
- **Quantum.** The best quantum attack we know is the Grover-hybrid forgery, `≈ 2^{120}` logical
  gates without depth limit. At every depth limit of NIST it costs more than key search on
  AES-128. The oracle adds nothing: its answers are classical.
- **Conjecture of [OC] §6**, restated: the best attack on OMPR is the best forgery attack on
  UOV, which is P1, `≈ 2^{138.5}` multiplications, and makes no call.

---

## 1. Review of [OC]

**Checked and confirmed.**
- **L1.** The vinegar of a call is the first good output of the random oracle on inputs that
  contain the whole target. For distinct targets the inputs are distinct. So the vinegars are
  independent and uniform on `G`, also for adaptive targets. `v ↦ (v, 0) + ι(L_v^{−1}(y − P(v,
  0)))` is a bijection from `G` to the good fibre ([UA] Lemma C), so the answer is uniform on it.
  The proof is complete. It uses the random-oracle model for the vinegar hash and nothing else.
- **K1.** Two answers have proportional vinegars with probability `255/|G|`, and
  `C(Q, 2)·255·256^{−74}/(1 − δ) = Q²·2^{−585.0}` (recomputed: `−1 + 7.994 − 592 + 0.006`).
- **Lemma F.** The grouping by projective points, the values `q − 1` and `−1`, pairwise
  independence of the indicators, and `Σ c² = q^V − q + 1` are right. Theorem H (§2.1) gives the
  same mean and variance by another route, and E8 checks the formula exactly.
- **Lemma G, F3, F5, F6, S3, the counts of K5.** Re-derived; no change.

**Corrections.**
- **R1 (baseline).** [OC] B0 and [SA] §4.1 take the direct forgery as 45 quadrics. It is 44:
  §3.1. Every comparison "against `2^{140.3}`" in [OC] and [SA] should read "against `2^{138.5}`".
  No conclusion of [OC] changes sign: all its attacks were at or above `2^{140.3}`.
- **R2 (F2).** `D(0)` is a call that pays for no challenge target. An adversary that makes it
  must forge twice (§3.2). F2 costs `2·2^{138.5}`, not B0.
- **R3 (K2).** [OC] §2.2 says that a zero of `P` in the span of answers "cannot be recognized"
  as an oil vector. It can: run the polynomial-time recovery of `𝒪` from one oil vector on it
  and test the output. The conclusion stands for another reason. For `r` answers with vinegars
  `v_i`, `span(s_i) ∩ 𝒪 ≠ 0` iff the `v_i` are dependent, and the `v_i` are uniform on `G`: the
  probability is `≈ 256^{−(75 − r)}`, the same as for a uniform `r`-space. **Spans of answers
  are no better than random subspaces for finding oil vectors.** Searching them is the
  Kipnis–Shamir search (`q^{N − 2M} = 2^{232}` trials) in other words.
- **R4 (scope of Lemma F, item 2).** "Choosing the targets does not help" is proved for
  characters in `𝒪^⊥` only. For a statistic that is not a function of the vinegar and a target
  fixed by the adversary, neither Lemma F nor §2 below gives a bound. That case is cGPI, and it
  stays open (§6).
- **R5 (wording).** K1 does not see goodness. A keyless sampler that returns uniform fibre
  points has vinegar collisions at the same rate, up to the factor `1 − δ`.

## 2. Statistics of goodness of degree `d`

`Bad ⊂ F^V` is the set of vinegars `v` with `L_v` singular, `0` included. `L : F^V → F^{M×M}`,
`v ↦ L_v`, is linear. Its adjoint is `L* : F^{M×M} → F^V`, with `v·L*(T) = ⟨T, L_v⟩ =
Σ_{k,j} T_{kj}(L_v)_{kj}`. In public terms `a^t L_v b = ⟨a, B(s, ι(b))⟩` for every `s` with
`vin(s) = v`, so `L*(a b^t)` is the vector `M_a·ι(b)` of [OC] §2.3, read in `𝒪^⊥ ≅ F^V`.
`X(w) = Σ_{v ∈ Bad} ψ(w·v)` as in [OC] Lemma F. "Uniform `S`" means: `L` is a uniform linear
map, as it is for a uniform `P2` ([UA] §1).

### 2.1 Theorem H: the exact Fourier transform of the bad set [proved; experimental]

**Theorem H.** For every key and every `w ∈ F^V`,

    X(w) = Σ_{T ∈ F^{M×M}, L*(T) = w} κ(rank T),
    κ(r) = (−1)^{r−1}·q^{V − rM + r(r−1)/2}·∏_{i=1}^{M−r} (1 − q^{−i})   (r ≥ 1),     κ(0) = δ_u·q^V.

*Proof.* For a matrix `A` with kernel of dimension `n`, `Σ_{j=0}^{n} (−1)^j q^{binom(j,2)}
[n, j]_q = 0` if `n ≥ 1` (the `q`-binomial theorem at `x = 1`). So

    1[A singular] = Σ_{j ≥ 1} (−1)^{j−1} q^{binom(j,2)}·#{U ⊂ ker A : dim U = j}.

For `U` with basis `u_1..u_j`: `1[AU = 0] = q^{−jM} Σ_{a_1..a_j} ψ(Σ a_i^t A u_i) = q^{−jM}
Σ_T ψ(⟨T, A⟩)`, over the `T = Σ a_i u_i^t`, which are the matrices with row space in `U`. A
matrix of rank `r` has its row space in `[M − r, j − r]_q` subspaces of dimension `j`. So
`1[A singular] = Σ_T c(T) ψ(⟨T, A⟩)` with, for `r = rank T ≥ 1` and `j = r + i`,

    c(T) = Σ_{i ≥ 0} (−1)^{r+i−1} q^{binom(r,2) + binom(i,2) + ri − (r+i)M} [M − r, i]_q
         = (−1)^{r−1} q^{binom(r,2) − rM} ∏_{l=0}^{M−r−1} (1 − q^{r−M+l}),

by the `q`-binomial theorem `Σ_i (−1)^i q^{binom(i,2)} [n, i]_q x^i = ∏_{l<n} (1 − x q^l)` at
`x = q^{r−M}`. For `T = 0` the sum starts at `j = 1` and gives `1 − ∏_{l<M}(1 − q^{l−M}) = δ_u`.
Now put `A = L_v` and sum `ψ(w·v)` over `v`: `Σ_v ψ(v·(L*(T) + w))` is `q^V` if `L*(T) = w`
(characteristic 2) and 0 otherwise. ∎

So `c(T)` is the Fourier transform of the indicator of the singular matrices; it depends on
the rank only. Consequences:
- **The relation between `X(w)` and `N₁(w)`**, left open in [OC] §8. The matrices of rank one
  over `w` are the representations `w = M_a·o` of [OC] §2.3, and

      X(w) = κ(1)·N₁(w) + Σ_{r ≥ 2} κ(r)·N_r(w),      κ(1) = q^V(1 − δ_u)/(q^M − 1),

  with `N_r(w)` the number of matrices of rank `r` over `w`. `κ(1)` is the slope measured in
  [OC] E3. The relation is affine in `N₁` up to the terms of higher rank, which alternate.
- **Lemma F again.** For uniform `S` and `T, T′` not proportional, `L*(T)` and `L*(T′)` are
  independent and uniform. This gives `E[X(w)] = 1 − δ_u` and the variance of Lemma F.
- **Sizes at `(74, 45, 256)`.** `κ(1) = 2^{232}`, and `N₁(w)` has mean `2^{120}`: the part of rank
  one has standard deviation `2^{292}`. The part of rank `r` has `2^{292 − 4(r − 1)}`. So `X(w)`
  is, up to `2^{−4}`, a count of `2^{120}` rare events, scaled. This supports the Gaussian
  estimate of [OC] for the largest bias (`≈ 29` standard deviations over `2^{592}` characters).
  It is not a proof: the events are independent only for linearly independent `T`.
- On toy keys the parts of different rank are of the same size and cancel (E8). The dominance
  of rank one needs `q^{M}` large.

### 2.2 Theorem T: a tail bound for Lemma F [proved, uniform `S`]

[OC] §8 asks for a bound on `max_w |X(w)|`. Pairwise independence gives Chebyshev for one `w`,
which is useless over `q^V` characters. The fourth moment can be computed.

**Theorem T.** For uniform `S`,

    E[ Σ_{w ≠ 0} X(w)^4 ]  ≤  B₄ := q^{4V}·η₄ + q^V·( [V, 2]_q·q^6·δ_u² + (q^V − 1)(q² + q + 1)·δ_u + 1 ),

with `η₄ = Σ_{T ≠ 0} c(T)^4 = Σ_{r ≥ 1} #{T of rank r}·(κ(r)/q^V)^4`. So for every `ε > 0`, with
probability `≥ 1 − ε` over the key, `|X(w)| ≤ (B₄/ε)^{1/4}` for all `w ≠ 0` at once.

*Proof.* `X` is real, so `Σ_w X(w)^4 = q^V·#{(v_1..v_4) ∈ Bad^4 : v_1 + v_2 + v_3 + v_4 = 0}`.
Take expectations over the triples `(v_1, v_2, v_3)`, with `v_4` their sum.
- Linearly independent triples, at most `q^{3V}`: `L_{v_1}, L_{v_2}, L_{v_3}` are independent
  and uniform, and `Pr[A, B, C, A + B + C singular] = Σ_T c(T)^4 = δ_u^4 + η₄` (Fourier inversion
  on `F^{M×M}`, Theorem H).
- Triples of rank 2, at most `[V, 2]_q·q^6`: two of the four points are independent, so the
  probability is `≤ δ_u²`.
- Triples of rank 1, `(q^V − 1)(q² + q + 1)`: probability `≤ δ_u`. The zero triple: 1.

The term `w = 0` is `X(0)^4 = |Bad|^4`, and `E|Bad|^4 ≥ (E|Bad|)^4 ≥ δ_u^4·q^{4V}`. Subtract it:
the main terms cancel. The last claim is Markov's inequality. ∎

**At `(74, 45, 256)`** (`ompr_second.py table`): `η₄ = 2^{−728}`, `B₄ = 2^{1776.0}`, dominated by
the triples of rank 2. `|G| ≥ (1 − 2δ_u)·q^V` except with probability `2^{−576}` (Chebyshev on
`|Bad|`). So, except for a fraction `ε + 2^{−576}` of keys, **every** character has

    |c(w)|  ≤  2^{−148.0}·ε^{−1/4}.

| `ε` | largest bias | answers needed (`1/bias²`) |
|---|---|---|
| 1 | `2^{−148}` | `2^{296}` |
| `2^{−64}` | `2^{−132}` | `2^{264}` |
| `2^{−128}` | `2^{−116}` | `2^{232}` |

- This is weaker than the truth (`≈ 2^{−295}`), because a fourth moment bounds the `ℓ⁴` norm of
  the spectrum, not its maximum. It is enough: with `2^{64}` answers, a linear character is
  visible only for a fraction `≤ 2^{−464}` of keys.
- The bound holds for all `w` at once, so it covers a character chosen with the public key.
  Lemma F's variance covers a fixed `w` only.
- Experimental (E9): on six toy sizes the measured mean of `Σ X^4` is 0.02 to 0.42 of `B₄`.
- A sixth moment needs the probability that six points of a 4-space are all bad, to a
  relative precision `q^{−V}`. We did not compute it.

### 2.3 Theorem V: fixed statistics of any degree [proved, uniform `S`, uniform targets]

Work in the hidden coordinates `s = (v, 0) + ι(x)`. A *statistic* is a function `h : F^N → ℂ`,
`|h| ≤ 1`. Call it *fixed* if it is chosen independently of `S` (it may depend on `𝒪` and on
`P1`). Let `γ(v) = q^{−M} Σ_x h(v, x)`. For answers to uniform targets, `(v, x)` is uniform on
`G × F^M`, so `E_D[h] = Σ_{v ∈ G} γ(v)/|G|`. Compare with `E₀[h]`, the mean of `γ` over `v ≠ 0`.

**Theorem V.** For a fixed statistic `h` and uniform `S`,

    E_S[ |G|²·|E_D[h] − E₀[h]|² ]  =  δ_u(1 − δ_u)·Σ_p |Γ_p|²  ≤  δ_u(1 − δ_u)(q − 1)(q^V − 1),

where `p` runs over the projective points of `F^V` and `Γ_p = Σ_{v ∈ p} (γ(v) − γ̄)`.

*Proof.* `Σ_{v ≠ 0}(γ − γ̄) = 0`, so `|G|·(E_D[h] − E₀[h]) = −Σ_{v bad, ≠ 0} (γ(v) − γ̄) =
−Σ_p ξ_p Γ_p` with `ξ_p = 1_bad(p) − δ_u` and `Σ_p Γ_p = 0`. Bad is a cone, and the `ξ_p` are
centred and pairwise independent ([OC] Lemma F). The inequality is Cauchy–Schwarz on each
line. ∎

- **At `(74, 45, 256)`:** the root mean square bias of a fixed statistic is at most
  `√(δ_u(q − 1)/(1 − δ_u))·q^{−V/2} = 2^{−296.0}`. It needs `2^{592}` answers.
- **The degree plays no role.** A character `ψ(g(v))` with `g` of degree `d` has
  `Γ_p = Σ_{λ ≠ 0} ψ(g(λv))`. For `g` homogeneous with `gcd(d, q − 1) = 1` this is `q − 1` or
  `−1` as for a linear form, and the bias is `2^{−300}`. If `(q − 1) | d` the character is
  constant on lines and the bias is `2^{−296}`: the cone factor `√(q − 1)`, and no more.
- **Families.** For `K` fixed statistics, by Chebyshev and a union bound, all biases are
  `≤ √(K/ε)·2^{−296}` except for a fraction `ε` of keys. A family of `2^{128}` statistics has no
  member with bias above `2^{−200}` for all but `2^{−64}` of the keys.
- **What "fixed" excludes.** The adversary knows `P2`, hence a function of `S`. A statistic
  computed from the public key is not fixed. The public forms show the limit of the theorem:
  `ψ(a·P(s))` is not fixed, and its mean over `Bad` is `≈ q^{−59}`, far from that of a fixed
  statistic. (It is useless all the same: its value on an answer is `ψ(a·y)`, known from the
  target.) Theorem T covers key-dependent linear statistics; §2.5 treats the others.
- Fixed targets: a statistic of the vinegar alone has the same law for every target ([OC]
  L1), so the theorem holds for chosen targets. For other statistics see R4.

### 2.4 Lemma Q: quadratic statistics of the answer [proved, uniform targets]

**Lemma Q.** Let `g` be a polynomial of degree `≤ 2` on `F^N`. For answers to uniform targets,
the bias `|E_D[ψ(g)] − E₀[ψ(g)]|` is at most the largest bias of a character `ψ(g′(v))` with
`g′` of degree `≤ 2` on `F^V`.

*Proof.* In hidden coordinates `g(v, x) = g₀(v) + x·(Av + b) + g₂(x)`. Let `2ρ` be the rank of
the polar form of `g₂` and `R` its radical; on `R`, `g₂(x) = (c·x)²`. Then `Σ_x ψ(g₂(x) +
x·u)` is 0 unless `u + c` vanishes on `R`, and then it is `±q^{M − ρ}` with a sign that is a
quadratic character of `u`. So `γ(v) = q^{−ρ}·1_𝒜(v)·ψ(g₁(v))`, with `𝒜` an affine subspace of
`F^V` and `g₁` of degree `≤ 2`. `1_𝒜` is an average of linear characters. So `γ` is `q^{−ρ}`
times an average of characters of degree `≤ 2` of `v`. ∎

So the `x`-part of a statistic only loses. This is why [OC] found the public quadrics
unbiased: their dependence on `x` is all there is.

### 2.5 The largest statistic of degree `d` [heuristic; experimental]

Let `𝒫_d` be the polynomials of degree `≤ d` on `F^V` without constant term:
`binom(V + d, d) − 1` coefficients. For each one, `Y(g) = Σ_{v ≠ 0} ξ(v) ψ(g(v))` has standard
deviation `σ ≤ √(δ_u(q − 1))·q^{V/2}` over the key (Theorem V). An adversary who could choose
`g` with the key would take the largest.

**Heuristic W.** `max_{g ∈ 𝒫_d} |Y(g)| ≈ σ·√(2·ln|𝒫_d|)`, as for independent Gaussians. In the
table `σ = √δ_u·q^{V/2}` (bias `2^{−300}`), and `√(q − 1)` times that for `d = 255`.

| `d` | coefficients | largest bias | answers needed |
|---|---|---|---|
| 1 | 74 | `2^{−295.2}` | `2^{590}` |
| 2 | 2 849 | `2^{−292.5}` | `2^{585}` |
| 3 | 73 149 | `2^{−290.2}` | `2^{580}` |
| 4 | `2^{20.4}` | `2^{−288.0}` | `2^{576}` |
| 16 | `2^{57.6}` | `2^{−269.5}` | `2^{539}` |
| 45 | `2^{110.1}` | `2^{−243.2}` | `2^{486}` |
| 255 | `2^{248.8}` | `2^{−169.9}` | `2^{340}` |

- The bias grows like the square root of the number of coefficients. To be seen with `2^{64}`
  answers it must reach `2^{−32}`, which needs `2^{524}` coefficients. `1_Bad` itself has degree
  `45·255` and correlation 1.
- **Why Gaussian.** By Theorem H, for `g` quadratic of rank `2ρ`,
  `Σ_{v ∈ Bad} ψ(g(v)) = q^{−ρ}·Σ_T ±κ(rank T)`, over the `T` with `L*(T)` in an affine space of
  dimension `2ρ`, the sign a quadratic character of `L*(T)`. A quadratic statistic collects
  `q^{2ρ}` times more matrices than a linear one, with signs, and normalised by `q^{−ρ}`: the
  same variance. To do better the adversary must align the signs on the matrices of rank one
  `a b^t`, that is, know the map `(a, b) ↦ L*(a b^t)`. That map is the key.
- **Experimental (E10).** All `g` of a family at once, by a Walsh–Hadamard transform. The mean
  square is 0.83 to 1.04 of Theorem V. Over `F₄` the largest value is 0.77 to 1.2 of the
  Gaussian extreme value, for degree 1, 2 and 3 alike (table in §5). Over `F₁₆` with
  `(V, M) = (3, 2)` it is 15 standard deviations, for linear and quadratic characters alike:
  there `N₁(w)` has mean below 1 and its law is far from Gaussian. The real parameters have
  mean `2^{120}`.
- **Not proved.** A proof for `d = 2` along the lines of Theorem T needs the Gowers `U³` norm of
  `1_Bad − δ`. The degenerate configurations give `2^{−73}` for the largest quadratic bias
  (`2^{146}` answers) if the `U³` norm of the singular matrices in `F^{M×M}` is below `q^{−10}`.
  We expect `q^{−(3M+8)/8} = q^{−18}` and did not prove it (§6).

### 2.6 What this says about cGPI and GPI

- [UOS] B.7 asked for a public statistic whose law differs between bad and good points by more
  than `2^{−592}`. For statistics of the vinegar: the difference is at most `2^{−288}` in root
  mean square for a fixed statistic (Theorem V, divided by `δ`), at most `2^{−140}` for every
  linear one (Theorem T), and about `2^{−284}` for the best quadratic one (heuristic W).
- These are bounds on single statistics. They do not bound a distinguisher that computes
  something else, and they do not make cGPI or GPI a theorem.

## 3. Multi-target and structured attacks

The adversary of OMPR sees `n` uniform targets. With `Q` calls it must output `Q + 1`
preimages. Can it solve for several targets jointly, more cheaply than one by one?

### 3.1 P1: the class of one target [proved; estimate; experimental]

`P` is homogeneous of degree 2, and every element of `F` has a square root. [OC] and [OR] use
this to say that a call serves a class `F^×·t`. It also serves the forger.

**Attack P1.** Let `t ≠ 0` and `π_t : F^M → F^M/F·t`.
1. Find `s ≠ 0` with `π_t(P(s)) = 0`: **44 homogeneous quadrics** in 119 variables.
2. Then `P(s) = ν·t`. If `ν ≠ 0`, output `ν^{−1/2}·s`.

*Correctness.* `P(ν^{−1/2} s) = ν^{−1}·P(s) = t`. Lean: `scaled_preimage`
(`Spec/PqovScale.lean`). ∎

- **Count.** The forgery problem is a map of projective spaces, `ℙ^{118} → ℙ^{44}`: 44
  conditions. Setting one coordinate of `s` to 1 gives 44 inhomogeneous quadrics in 118
  variables. The direct attack solves 45 in 119. The solution sets have the same dimension, 74;
  the solver has one equation less.
- **Landing.** `ν = 0` means `P(s) = 0`: a fraction `≈ 1/q` of the solutions (E11: 2666 of
  2859 solutions land over `F₁₆`, 0.932 for `15/16`; 1065 of 1067 over `F₂₅₆`).
- **It is [SA] C1 with the shifts replaced by scaling.** C1 takes shifts `λ_a·c` and lands
  with probability `τ/256`. P1 takes `c = t`: the "shifts" `(ν − 1)·t` are reached by scaling,
  all 255 of them, in OMPR and in plain UOV, with no shift list. [SA] §4.1 has the cost of the
  44-equation system (its `U`); it did not take `c` along the target.
- **Cost [estimate],** model of [SA] §4.1 (`ompr_second.py multi`), `log₂` multiplications:

  | Solver | Prep. | direct, 45 eqs | P1, 44 eqs | gain |
  |---|---|---|---|---|
  | XL | plain | 144.1 | 140.3 | `2^{3.7}` |
  | **XL** | **TW** | **140.3** | **138.5** | `2^{1.8}` |
  | F5, ω = 2 | TW | 120.9 | 119.1 | `2^{1.8}` |
  | F5, ω = 2.37 | TW | 139.4 | 136.9 | `2^{2.5}` |
  | F5, ω = 2.81 | TW | 159.4 | 154.9 | `2^{4.6}` |

  In the reference row the forgery costs `2^{138.5}` multiplications, `2^{145.6}` bit
  operations. For uov-Ip `(112, 44)`: `2^{134.8}` and `2^{141.9}`, against `2^{138.5}` and
  `2^{145.6}` for the direct attack.
- **Experimental (E11).** Toy keys, hybrid XL with dense elimination (`c1_toy.c`, `c = h`).
  Every scaled solution is checked against the public map. Work per forgery: table in §5.
  P1 is cheaper than the direct attack on all five keys.
- **Not a break.** `2^{145.6}` bit operations is above the `2^{143}` of NIST level 1. The margin
  of `(119, 45)` over level 1 shrinks from 4.4 bits to 2.6 in this model. For `(112, 44)` the
  model puts P1 one bit below `2^{143}`; the model is rough at that precision ([SA] §4.1).
- **Is it known?** We do not know a reference that counts `M − 1` equations for a forgery
  against a homogeneous map in characteristic 2. It may be folklore. In odd characteristic the
  landing has probability 1/2 (`ν` must be a square). The UOV figures we remember count `M`.
- **Fix, if one is wanted.** None is needed at `(119, 45)`. A scheme whose targets are bound to
  a normal form of the class (say first nonzero coordinate 1) does not change the count
  either: the forger still solves 44 quadrics. The saving is a property of the map.

### 3.2 The budget lemma [proved]

**Lemma B.** An OMPR adversary that makes `c` calls on targets outside the classes of the
challenge targets it answers must output at least `c + 1` preimages that no call paid for.

*Proof.* A call pays for a challenge target only if the answer, rescaled, is a preimage of
it, that is, if the call is in its class (up to the events of [OC] F1, F3). The adversary
outputs `Q + 1` preimages and at most `Q − c` of them are paid. ∎

- Calls on challenge classes return `(t, s)` with `s` uniform on the good fibre of a uniform
  `t`. That is the oracle of A-OMPI ([UA] §3 item 9), which follows from GPI and the UOV
  problem ([UA] Theorem 2). So **the chosen-target power of OMPR is in the calls of Lemma B, and
  each of them costs a forgery.**
- An attack with `c ≥ 1` such calls beats the baseline only if `c + 1` forgeries, with the help
  of `c` chosen answers, cost less than one forgery without help.
- **F2 of [OC]** is `c = 1`: `z₀ = D(0)`. With `z₀` and scaling a forgery is 43 quadrics on a
  space of dimension 73 (`W_c/F·z₀` of [SA] C3, projectively), with no room for Thomae–Wolf:
  the same count as P1 after Thomae–Wolf, `2^{138.5}`. Two are needed: `2^{139.5}`.

### 3.3 M1: several targets at once [estimate]

- **Targets on a flat through 0.** Let `T = span(t_1..t_d)`. `P(s) ∈ T` is `45 − d` homogeneous
  quadrics. A solution has `P(s)` in one of the `d` classes with probability
  `d(q − 1)/(q^d − 1) ≈ d/q^{d−1}`.

  | `d` | one solve | per forgery |
  |---|---|---|
  | 1 (P1) | `2^{138.5}` | `2^{138.5}` |
  | 2 | `2^{134.8}` | `2^{141.8}` |
  | 3 | `2^{129.5}` | `2^{143.9}` |
  | 4 | `2^{128.0}` | `2^{150.0}` |

  Each equation removed saves `2^{1.5}` to `2^{5.3}`; each dimension of `T` costs `2^{8}` in
  landing and brings one more class. Uniform targets are in general position, so `T` holds no
  further target. `d = 1` is the optimum.
- **Affine flats.** Scaling fixes 0. A flat that misses 0 has no scaling: `d + 1` targets on a
  `d`-flat, `45 − d` equations, landing `(d + 1)/q^d`. Worse than the row above.
- **A singular `d`-space modulo `T`.** A subspace `Z` of dimension `d` with `P(Z) ⊂ T` gives
  `P|_Z : F^d → T`, `d` quadrics in `d` unknowns for each target of `T`. `Z` is a solution of
  `binom(d+1, 2)·(45 − d)` quadrics in `d(119 − d)` unknowns: 129 in 234 for `d = 2`, 252 in 348
  for `d = 3`. Thomae–Wolf removes nothing (`234 < 2·129`). In the model: `2^{358}` and `2^{663}`.
  For `d = 1` this is P1.
- **OMPR⊕τ** is the case where the forger chooses the family: [SA] C1, and §3.5.

### 3.4 M2: many right-hand sides [open; heuristic]

- **Generic bound.** Any algorithm that finds a preimage of one of `n` uniform targets with
  probability `ε` finds a preimage of one given target with probability `ε/n` ([UA] §3 item
  1). For `n = 2^{64}` this allows a gain of `2^{64}`. No algorithm we know gains anything, and
  `P` has no symmetry to rerandomize one target into many ([SA] Theorem T3: the scalings only).
- **Enumeration gains `n`.** `W` evaluations hit one of `n` targets with probability
  `W·n·255·2^{−360}`: [OC] F4. In the protocols the targets are hashes, so `n` is bounded by the
  hash queries, not by `Q`: the collision attack on the 360-bit target, `2^{180}`.
- **Hybrid XL does not gain.** After `j` guesses a system has a solution with probability
  `q^{−j}`. The pairs (guess, target) are exchangeable: `n` targets with one guess each are
  `n` systems, as `n` guesses for one target are. The number of solver runs is unchanged.
- **Inside the solver.** For a fixed guess the systems of different targets share their
  quadratic and linear part and differ in 45 constants. The Macaulay matrices differ in
  `45·binom(n + D − 2, D − 2)` entries, not by a matrix of low rank. Deciding "is `c` in the
  image of an overdetermined quadratic map" for many `c` with one precomputation would need
  the equations of the image; for 45 quadrics in 29 variables their degree is about 75 and
  they have about `2^{110}` terms (count of dimensions, generic map). We found no amortization. One
  would lower the cost of plain UOV with many signing keys or messages too.
- **Additivity.** `P(s + u) = P(s) + P(u)` iff `B(s, u) = 0`. A subspace `S₂` on which `B(s, ·)`
  vanishes for all `s` of a space `S₁` has dimension `119 − 45·dim S₁`: 74, 29, 0. So lists
  `P(S₁) + P(S₂)` exist only with `q^{31}` sums for `q^{45}` targets, and testing a sum is an MQ
  problem. No meet-in-the-middle.

### 3.5 S2′: OMPR⊕τ after P1 [estimate]

P1 moves both sides of [SA] §4.1.
- Direct attack on OMPR⊕τ: P1, 44 quadrics, `2^{138.5}`.
- Collinear shifts `λ_a·c` on top: `P(s) ∈ span(h, c)`, 43 homogeneous quadrics. A solution
  `P(s) = αh + βc` scales to the candidate `h + λ_a c` iff `β/α = λ_a`: probability
  `τ/(q + 1)`.
- Break-even `τ*′ = (q + 1)·2^{−step}`, with the step from 44 to 43 equations.

| Solver | Prep. | P1 | step | `τ*′` | C1′ at τ = 17 |
|---|---|---|---|---|---|
| XL | plain | 140.3 | 1.84 | 72 | 142.4 (`+2.1`) |
| **XL** | **TW** | **138.5** | 3.74 | **19** | **138.7** (`+0.2`) |
| F5, ω = 2 | TW | 119.1 | 3.60 | 21 | 119.4 (`+0.3`) |
| F5, ω = 2.37 | TW | 136.9 | 3.99 | 16 | 136.8 (`−0.1`) |
| F5, ω = 2.81 | TW | 154.9 | 3.10 | 30 | 155.7 (`+0.8`) |

- In the reference model 17 collinear shifts are `2^{0.2}` dearer than P1, where [SA] had
  `2^{2.1}` dearer than the 45-equation attack. The sign of the margin is not robust, as [SA]
  said; its size is at most `2^{2.1}` either way in the rows computed.
- The model-free bound is unchanged: at most `τ = 2^{4.1}` below the best attack on OMPR.
- Conjecture A6 stands as stated in [SA] §4.4, with "the best attack on OMPR" now P1 and `τ*`
  between 16 and 72.

## 4. Quantum attacks

The adversary has a quantum computer and classical access to `D` (`Q ≤ 2^{64}` calls). The
verifier and the signer are classical, so superposition queries do not exist.

**Model [estimate].** Logical gates; one multiplication in `F` is counted as `2^{7.1}` gates,
the bit-operation count of [UOS] B.5. Grover over `K` candidates with a test of `g` gates and
depth `d`: `√K·g` gates at depth `√K·d`; under a depth limit `Δ < √K·d` it costs `K·d·g/Δ`. This
ignores reversibility, error correction and memory access, all in the attacker's favour.
NIST's level 1 is key search on AES-128: `2^{170}/Δ` gates for `Δ = 2^{40}, 2^{64}, 2^{96}`.

### 4.1 Q1: forgery

Grover over the guessed variables of hybrid XL (those of Thomae–Wolf included), XL with
Wiedemann inside, one iteration of depth `3T` (`T` the number of monomials).

| Attack | classical | quantum, multiplications | gates | `Δ = 2^{40}` | `Δ = 2^{64}` | `Δ = 2^{96}` |
|---|---|---|---|---|---|---|
| direct, 45 eqs | `2^{140.3}` | `2^{115.6}` (11 guesses, `D = 10`) | `2^{122.7}` | `2^{155.4}` | `2^{131.4}` | `2^{122.7}` |
| **P1**, 44 eqs | `2^{138.5}` | `2^{113.2}` (8 guesses, `D = 12`) | `2^{120.3}` | `2^{148.1}` | `2^{124.1}` | `2^{120.3}` |
| AES-128 key search | | | | `2^{130}` | `2^{106}` | `2^{74}` |

- The quantum optimum guesses more variables than the classical one (8 against 2) and runs XL
  at a lower degree.
- At every depth limit the forgery costs at least `2^{18}` times the AES-128 key search. The
  parameters meet level 1 in NIST's quantum sense, in this model.
- Exhaustive Grover search over `F^{44}` costs `2^{176}`; over a list of `n` targets
  `√(2^{352}/n)`: `2^{144}` at `n = 2^{64}`. The hash collision on the targets costs `2^{120}`
  with as much quantum memory (Brassard–Høyer–Tapp), `2^{180}` classically.
- Not modelled: the quantum algorithms for MQ over `F₂` (Faugère et al.; Bernstein–Yang) as
  they would apply over `F₂₅₆`; a quantum speed-up of the linear algebra.

### 4.2 Q2: key recovery

- **Kipnis–Shamir with Grover.** `q^{N − 2M} = 2^{232}` trials classically, `2^{116}`
  iterations of about `N³` multiplications: `2^{143.8}` gates, at depth `≥ 2^{130}`. Under
  `Δ = 2^{96}`: `2^{178}` gates. This is the cheapest quantum key recovery we know. It is above
  the quantum forgery.
- **Intersection attack.** Its hybrid optimum has no guess (`j = 0`), so Grover has little to
  amplify: `2^{191}` multiplications with two guesses, `2^{198}` gates.

### 4.3 Q3: quantum work on the answers

- **No superposition over `Good`.** Fourier sampling of a uniform superposition over `Good`
  would give `𝒪^⊥` ([OC] §2.8). The adversary has `Q` classical points. Preparing the state
  needs a test of goodness, that is, the key.
- **No hidden period in what can be computed.** `P(s + o) = P(s) + B(s, o)` is not periodic.
  `1_Good` is `𝒪`-periodic and not computable without the key. The answers `D(y)`, as a
  function of `y`, are independent uniform fibre points ([OC] L1): no algebraic relation
  between the answers to related targets. So the "offline Simon" technique (Bonnetain et al.),
  which needs a classically queried function with a period shared with a public one, has
  nothing to work on. *Heuristic*: this excludes the techniques we know, not all.
- **Collisions and statistics.** The data hold a vinegar collision with probability
  `Q²·2^{−585}` ([OC] K1) and a visible bias with probability `≤ 2^{−464}` over the key (Theorem
  T). A quantum computer does not change what the data hold.
- **Oil vectors in spans of answers.** By R3 these spans are random subspaces. The oil vectors
  are a fraction `q^{−29}` of the zeros of `P` in them. Grover finds one in `2^{116}` steps,
  each a forgery-sized problem: above Kipnis–Shamir with Grover.
- **Quantum forgery with calls.** Lemma B is about the game, not about the machine. P1 with
  Grover makes no call.

**Verdict.** Quantum attacks on OMPR are the quantum attacks on UOV. The oracle is classical
and its answers have the law of [OC] L1.

## 5. Experiments

`scripts/ompr-cryptanalysis/ompr_second.py` (pure Python; `scale` builds
`scripts/ompr-shift-algebra/c1_toy.c`, which gained the option `cmode = 1`: the direction `c` is
the target). Keys are those of `ompr_toy.py`.

| # | Experiment | Sizes | Result |
|---|---|---|---|
| E8 | Theorem H as an identity of rationals, every `w` | `F₄` `(V, M)` = (3, 2), (4, 3), (5, 3), (7, 3); `F₁₆` (3, 2), (4, 2) | 0 mismatches in 87 360 characters |
| E9 | `Σ_{w ≠ 0} X(w)^4`, 12 keys per size | `F₄` `V = 4..8`; `F₁₆` `V = 3, 4` | 0.015 to 0.42 of `B₄`; 1.05 to 10.6 times the Gaussian value `3σ⁴(q^V − 1)` |
| E10 | All characters `ψ(g(v))` of a family, 16 keys | `F₄` `V = 4, 6`; `F₁₆` `V = 3`; degree 1, 2, 3 | mean square 0.83 to 1.04 of Theorem V; largest value below |
| E11 | P1 against the direct attack, hybrid XL | `F₁₆` (21, 8), (24, 9), (26, 10); `F₂₅₆` (16, 6), (24, 9) | P1 cheaper by `2^{2.2}` to `2^{5.7}` |

**E10** (`σ²` is the value of Theorem V for the family; "Gauss" is `√(2·ln(2·#g))`):

| Field, `(V, M)` | family | bits | mean `Y²/σ²` | largest `|Y|/σ` | Gauss | largest bias |
|---|---|---|---|---|---|---|
| `F₄`, (4, 3) | linear | 8 | 0.96 | 3.10 | 3.53 | 0.132 |
| `F₄`, (4, 3) | all quadrics | 20 | 1.01 | 5.77 | 5.40 | 0.241 |
| `F₄`, (4, 3) | 10 cubic monomials | 20 | 0.83 | 4.14 | 5.40 | 0.300 |
| `F₄`, (6, 4) | linear | 12 | 1.00 | 5.11 | 4.25 | 0.054 |
| `F₄`, (6, 4) | 10 quadratic monomials | 20 | 1.04 | 5.67 | 5.40 | 0.064 |
| `F₄`, (6, 4) | linear and 4 quadratic monomials | 20 | 1.01 | 5.45 | 5.40 | 0.057 |
| `F₄`, (6, 4) | 10 cubic monomials | 20 | 1.01 | 5.00 | 5.40 | 0.091 |
| `F₁₆`, (3, 2) | linear | 12 | 1.00 | 15.06 | 4.25 | 0.063 |
| `F₁₆`, (3, 2) | 5 quadratic monomials | 20 | 0.96 | 14.68 | 5.40 | 0.062 |

- Cubics over `F₄` are constant on lines (`λ³ = 1`): their variance is the cap of Theorem V,
  `q − 1 = 3` times that of the linear characters. The table shows the cone factor.
- Over `F₁₆` with `(V, M) = (3, 2)` one of the 16 keys has a character with `X(w) = 240`: 15
  representations `w = M_a·o` instead of 0 or 1. The best quadratic character of that key is
  no better than this linear one. Such keys are what Theorem T's fourth moment pays for
  (`B₄^{1/4} = 536` here); the Gaussian estimate is for `N₁` of large mean.
- Over `F₄` a larger family has a larger maximum, at the Gaussian rate. Degree 2 is not special:
  the largest quadratic bias is 1.2 to 1.8 times the largest linear one, for `2^{8}` to `2^{12}`
  times more characters.

**E11** (multiplications per forgery, best number `j` of guesses; dense elimination):

| Field, `(N, M)` | direct | P1 | gain | gain in the model `3T²·binom(n+2, 2)` |
|---|---|---|---|---|
| `F₁₆`, (21, 8) | `2^{29.2}` | `2^{24.9}` | `2^{4.3}` | `2^{4.0}` |
| `F₁₆`, (24, 9) | `2^{32.3}` | `2^{29.3}` | `2^{3.0}` | `2^{2.1}` |
| `F₁₆`, (26, 10) | `2^{34.9}` | `2^{32.4}` | `2^{2.5}` | `2^{3.8}` |
| `F₂₅₆`, (16, 6) | `2^{31.9}` | `2^{26.1}` | `2^{5.7}` | `2^{4.2}` |
| `F₂₅₆`, (24, 9) | `2^{41.9}` | `2^{39.8}` | `2^{2.2}` | `2^{2.0}` |

- Cells with at least 30 forgeries are measured (128 to 509 forgeries). The others, (26, 10)
  direct and both cells of `F₂₅₆` (24, 9), are multiplications per call times `q^j` (direct) or
  `q^{j−1}·q/(q − 1)` (P1), as in [SA] §4.1. Every forgery is checked against the public map.
- The toy solver uses dense elimination, about `T^{2.8}`; the model column is Wiedemann's.
- The gain is the cost ratio of `M` and `M − 1` quadrics in the solver. It moves with the grid
  of degrees, as the step of [SA] does.

**What transfers.** Theorems H, T, V, Lemma Q, Lemma B and the algebra of P1 hold at all
sizes; T and V need a uniform `P2`. The costs of §3 and §4 are estimates in the model of [SA]
§4.1 with its caveats. Heuristic W is tested only where the family has at most `2^{20}` members.

## 6. Open

- cGPI for statistics that are not functions of the vinegar, at targets of the adversary's
  choice (R4).
- A proof of Heuristic W for `d = 2`: the `U³` norm of the singular matrices.
- A sharp tail for Lemma F (the truth is near `2^{−295}`; Theorem T gives `2^{−148}`).
- Amortizing XL over many right-hand sides (§3.4). A positive answer would be an attack on UOV.
- A reference for P1, and its effect in the cost models with Hashimoto's refinement and the
  crossbred algorithm, which [SA] does not model.
- Quantum algorithms for MQ over `F₂₅₆` beyond Grover on the guesses.
- OMPR ⇒ OMPR⊕17 by a reduction: unchanged ([OR] §7, [SA] §7).

## 7. Lean and script

No new Lean. The algebra of P1 is `scaled_preimage` and `qmap_smul` (`Spec/PqovScale.lean`);
S2′ uses `preimage_plane` (`Spec/PqovShift.lean`). Theorems H, T, V, Lemma Q and Lemma B are on
paper. H is checked exactly by E8.

Script: `ompr_second.py [fourier|moment4|degree|scale|quantum|multi|table|all] [seed]`. `all`
omits `scale`. Run it under a memory cap.

## References

Citations are from memory.

- [OC] `ompr-cryptanalysis.md`. [UA], [UOS], [OR], [SA] as there; [TW12], [FNT21], [Beu21],
  [KS98] are listed in [SA] and [UOS].
- G. Brassard, P. Høyer, A. Tapp, *Quantum cryptanalysis of hash and claw-free functions*, 1998.
- X. Bonnetain, A. Hosoyamada, M. Naya-Plasencia, Y. Sasaki, A. Schrottenloher, *Quantum
  attacks without superposition queries: the offline Simon's algorithm*, ASIACRYPT 2019.
- J.-C. Faugère, K. Horan, D. Kahrobaei, M. Kaplan, E. Kashefi, L. Perret, *Fast quantum
  algorithm for solving multivariate quadratic equations*, 2017; D. J. Bernstein, B.-Y. Yang,
  *Asymptotically faster quantum algorithms to solve multivariate quadratic equations*, 2018.
- NIST, *Submission requirements and evaluation criteria for the post-quantum cryptography
  standardization process*, 2016 (security levels, MAXDEPTH).
