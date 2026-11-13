# Cryptanalysis of one-more preimage resistance for UOV (OMPR, OMPR⊕τ)

All three protocols rest on OMPR for UOV over `GF(256)` with `(N, M) = (119, 45)`
(`uov-assumptions.md`, cited as **[UA]**, §3 item 7, with `derive_preimage` as the oracle).
OMPR does not follow from the UOV problem (`uov-open-structure.md`, **[UOS]**, Part A), and
PomFRIT's tight bound needs the shift variant OMPR⊕17 ([UA] §3 item 8; `uov-open-reductions.md`,
**[OR]**, Conjecture A6; `ompr-shift-algebra.md`, **[SA]**). This note is the attack side: what
can an adversary do with the preimage oracle that it cannot do without it?

Two questions.
1. **Key recovery.** Do `q ≤ 2^64` answers of the oracle, on targets of the adversary's choice,
   give the oil space (or anything that inverts `P`) faster than key recovery from `pk` alone?
2. **One more preimage.** Do they give a preimage of an uncalled target faster than a direct
   forgery? And does the shift structure of OMPR⊕τ add anything to [SA] C1?

Notation is that of [UA] §1 and [SA] §1: `F = GF(256)`, `P : F^N → F^M`, `V = N − M = 74`, oil
space `𝒪 = {ι(x)}`, `vin(s)`, `L_v`, `G = G_sk` the good vinegars, `Good`, `Bad`, `δ`, `B` the
polar form, `K_s = ker B(s, ·)`, `D = derive_preimage`, class `[t] = F^×·t`. `ψ` is a nontrivial
additive character of `F`. Costs are in field multiplications unless said otherwise (add 7.1 for
`log₂` bit operations), in the model of [UOS] B.5 and [SA] §4.1.

**Status labels.** *Proved*: full proof here. *Lean*: also machine-checked. *Heuristic*: argument
with a stated unproved hypothesis. *Estimate*: cost figure from the usual model. *Experimental*:
measured on toy keys by `scripts/ompr-cryptanalysis/ompr_toy.py` (§5). Citations are from memory;
the literature was not retrieved again.

**What this note is not.** It is not a proof of OMPR. It is a list of the attacks we could think
of, each with a proof that it fails, a cost, or a measurement. OMPR for UOV has had no outside
cryptanalysis.

**Second pass.** `ompr-cryptanalysis-2.md` (**[OC2]**) reviews this note and treats four of its
open items. Read the two together. Its findings, in short:
- **The forgery baseline is `2^{138.5}`, not `2^{140.3}`** ([OC2] P1): `P(s) ∈ F·t` is 44
  homogeneous quadrics, and a solution scales to a preimage of `t`. Read B0 below as `2^{138.5}`
  multiplications (`2^{145.6}` bit operations). No attack of this note goes below it.
- F2 needs two forgeries (the call `D(0)` pays for no target): `2^{139.5}`, above the baseline.
- K2: zeros of `P` can be tested for being oil vectors; the right statement is that spans of
  answers meet `𝒪` as often as random subspaces do.
- K3: the largest linear bias is `≤ 2^{−148}·ε^{−1/4}` for all but a fraction `ε` of keys
  (proved); a statistic of any degree fixed before the key has bias `≤ 2^{−296}` in root mean
  square (proved); `X(w)` has an exact formula in the matrices `T` with `L*(T) = w`.
- S2: with P1 on both sides, 17 collinear shifts cost `2^{138.7}` against `2^{138.5}`.
- Quantum: Grover-hybrid forgery `≈ 2^{120}` gates; the oracle adds nothing.

## 0. Summary

**The oracle, exactly (§1).** In the random-oracle model for the vinegar hash, the answers to
distinct targets are independent, and the answer to `y` is uniform on the good fibre
`S^G_y = P^{−1}(y) ∩ Good` ([UA] Lemma C, D). So the oracle gives two things and nothing else:
- **(a) fibre points**: uniform solutions of `P(s) = y` for chosen `y`. Their law is fixed by
  `pk` alone, up to (b). They are generic points of public varieties.
- **(b) goodness**: every answer satisfies `B(s, o) ≠ 0` for all oil vectors `o ≠ 0`. This is the
  only dependence on the trapdoor. Its density is `δ ≈ 2^{−8}` per answer.

The vinegar part `vin(s)` of an answer is uniform on `G` **whatever the target** (Lemma L1). So
the choice of targets, adaptive or not, has no effect on anything seen through `𝒪^⊥`.

**Attacks and costs at `(N, M, q) = (119, 45, 256)`.** `Q` is the number of oracle calls, `n` the
number of challenge targets. "No gain" means: not below the baseline of the same goal.

| # | Attack | Uses | Cost or success probability | Status | Where |
|---|---|---|---|---|---|
| B0 | Direct forgery, Thomae–Wolf | `pk` | `2^{140.3}` (`2^{147.4}` bit operations) with 45 equations; **`2^{138.5}` (`2^{145.6}`) with the class attack P1 of [OC2] §3.1. Baseline for forgery** | estimate | [SA] §4.1, [OC2] §3.1 |
| B1 | Intersection attack | `pk` | `2^{194}`. **Baseline for key recovery** | estimate | [UOS] B.5 |
| K1 | Vinegar collision: two answers with proportional vinegars differ by an oil vector | (a) | probability `≤ Q²·2^{−585}`: `2^{−457}` at `Q = 2^64`; needs `2^{292.5}` calls | proved (ideal sampler); Lean `vinegar_reuse`; experimental | §2.1 |
| K2 | Small sets of answers with dependent vinegars (they exist for `r ≥ 9` at `Q = 2^64`) | (a) | not detectable: a zero of `P` in the span of `r` answers is `2^{232}` times more often not an oil vector | proved count; heuristic | §2.2 |
| K3 | First-order statistics of the answers (characters, linear forms) | (b) | bias `2^{−300}` per character; `2^{600}` answers; advantage `≈ 2^{−268}` at `Q = 2^64`. **Works on toy keys** with 2 to 5 times `q^V/δ` answers | variance proved (uniform `P2`); experimental | §2.3 |
| K4 | Goodness as algebra: `f(s) ≠ 0` for the hidden form `f` of degree 45 | (b) | inequations; as equations `f(s)^{255} = 1`, degree 255 in `2^{110}` unknowns | proved (count) | §2.4 |
| K5 | Reconciliation, intersection, Kipnis–Shamir with the answers as side information | (a), (b) | no new equation: a good answer excludes oil vectors from `K_s`. Stays at `2^{194}` | proved (count); estimate | §2.5 |
| K6 | Special targets: `0`, one class, a subspace `T` of targets | (a) | one singular vector; 255 preimages per class; generic points of `{π_T∘P = 0}`. No polynomial of degree `≤ 3` beyond the public ideal on toy keys | proved (genericity); experimental | §2.6 |
| K7 | Differences of preimages of one target | (a) | a zero of `Q_s`, not an oil vector unless K1 | proved | §2.7 |
| K8 | Timing, aborts | side channel | retry count is independent of the answer; abort probability `δ^{255}` | [UA] §2 | §2.8 |
| F1 | Scaling: one call serves a class | (a) | accounted for in the game; one call serves two targets with probability `≤ 255·n²·2^{−360}` | proved | [OR] §3.1, [SA] §4.3 |
| F2 | Singular line through `D(0)` | (a), 1 call | `2^{138.5}` per forgery with scaling, and two forgeries are needed ([OC2] Lemma B): `2^{139.5}`. Does not stack with Thomae–Wolf | proved; estimate | [SA] C3, [OC2] §3.2 |
| F3 | Planes of two answers, isotropic pairs | (a) | a given class is met with probability `Q²·2^{−345}` (`2^{−217}` at `Q = 2^64`); isotropic pair `2^{−233}` | heuristic (Hypothesis X) | §3.2 |
| F4 | Spans of answers, ROS-type combinations | (a) | enumeration: `W` points hit one of `n` targets with probability `W·n·2^{−360}`. Linear combinations fail on the cross terms | heuristic; experimental | §3.3 |
| F5 | Translating a known preimage; `P` on `K_s` | (a) | the UOV problem ([OR] A3); on `K_s`: 45 quadrics in 74 variables without oil space, `2^{144.1}` | proved; estimate | §3.4 |
| F6 | A table of `2^64` preimages of a subspace of targets | (a) | no additivity: needs `B(w, s_τ) = 0`, 45 conditions | proved | §3.5 |
| S1 | OMPR⊕τ: key recovery through the oracle | | **the same oracle**: K1–K8 unchanged | proved (trivial) | §4.1 |
| S2 | OMPR⊕τ: collinear shifts | shifts | `2^{142.4}` at τ = 17 (between `2^{0.7}` below and `2^{2.1}` above B0 over the cost models); never more than `τ = 2^{4.1}` below | [SA] C1 | [SA] §4.1 |
| S3 | OMPR⊕τ: shifts aimed at targets with known preimages | shifts, (a) | `≤ τ·|R|·2^{−360}` per request for a set `R` of reachable targets: the counting factor τ | proved | §4.2 |

**Answers.**
- **Key recovery.** We found no attack that uses the oracle and beats `2^{194}`. The answers
  carry the trapdoor only through goodness, and goodness is seen only at `2^{292}` calls (K1,
  second order) or `2^{600}` (K3, first order). On toy keys K1 and K3 do recover the oil space
  from answers alone, with the predicted number of calls (§5); both numbers grow like `q^{V/2}`
  and `q^V/δ`.
- **One more preimage.** No attack below the direct forgery, `2^{140.3}`. One call (`D(0)`)
  gives the Thomae–Wolf saving by another route (F2) and nothing on top.
- **Shifts.** The oracle of OMPR⊕τ is the oracle of OMPR, so the two games differ only in the
  winning condition. The only structural gain known is [SA] C1, at most `2^{4.1}`.
- **Conjecture A6** ([OR] §4.6, [SA] §4.4) stands, with this evidence added: for `τ ≤ τ*`, the
  best attack on OMPR⊕τ is the best attack on OMPR, **and the best attack on OMPR that we know is
  the direct forgery attack on UOV, which makes no calls**.
- **Not covered here:** algorithms we did not think of; the modelling step "vinegar hash =
  random oracle". Quantum attacks, statistics of higher degree, the tail of Lemma F and
  multi-target attacks are in [OC2]; an amortization of XL over many targets remains open.

---

## 1. What the oracle gives

`D(y)` hashes `y ‖ sk_seed ‖ "pqov-derive-preimage" ‖ ctr` to a vinegar `v`, retries while `L_v`
is singular (at most 255 times), and returns `(v, 0) + ι(L_v^{−1}(y − P(v, 0)))` ([UA] §2,
`ov.c:226-239` after patch 0001). It is a function of `(sk_seed, y)`.

**Lemma L1 (the oracle) [proved; restates [UA] Lemma C, D].** Replace SHAKE256 by a random oracle
and condition on no failure (probability `δ^{255}` per call) and no adversarial query containing
`sk_seed` (`q_v·2^{−256}`). Let `y_1, …, y_Q` be the distinct targets of an adaptive adversary and
`s_i = D(y_i)`. Then:
1. `v_i = vin(s_i)` are independent and uniform on `G`, and independent of the targets.
2. `s_i = (v_i, 0) + ι(x_i)` with `x_i = L_{v_i}^{−1}(y_i − P(v_i, 0))`. So `s_i` is uniform on
   `S^G_{y_i}`, and the answers are independent given the targets.
3. `D(μ·y)` and `D(y)` are independent for `μ ≠ 1`. Rescaled by `1/√μ` ([OR] Lemma S), the 255
   answers on a class are 255 independent uniform points of `S^G_y`. The class of `0` is `{0}`:
   **the adversary gets one zero of `P`**, `z₀ = D(0)`, and no second one.

*Proof.* The vinegars of distinct targets are outputs of the random oracle on distinct inputs.
The first good one is uniform on `G` ([UA] Lemma D). 2 is [UA] Lemma C. 3: `μy ≠ y` for `y ≠ 0`,
and scaling by `1/√μ` maps `S^G_{μy}` onto `S^G_y` because `G` is a cone (Lemma L2). ∎

Experimental (E1): for a toy key over `F₁₆`, with the seed in the role of the random oracle, the
answers to the targets `0`, `c` and `7c` (rescaled) are uniform on the good fibre. Chi-square
3663.8, 3568.6, 3736.9 on 3599 degrees of freedom (standard deviation 84.8); 120 000 answers each;
no bad answer.

**Lemma L2 (goodness) [proved; Lean for the cone].**
1. `Good + 𝒪 = Good`, and `Good` is a cone: `L_{cv} = c·L_v` (Lean `sysMat_smul`,
   `det_sysMat_smul`, `good_smul_iff`).
2. `s` is good iff `B(s, o) ≠ 0` for every `o ∈ 𝒪 ∖ {0}` ([SA] T1.5).
3. `Bad` is the zero set of a form `f` of degree 45, `f(s) = det L_{vin(s)}` ([UOS] B2).

**The keyless sampler.** Let `D°` assign to each `y`, independently, a uniform point of the whole
fibre `P^{−1}(y)`. `D°` is defined by `pk`. An unbounded party computes it without the key.
- For one call on `y`, the statistical distance between `D(y)` and `D°(y)` is
  `β(y) = |P^{−1}(y) ∩ Bad| / |P^{−1}(y)|`.
- `E_y[β(y)]`, weighted by fibre size, is `δ`. Experimental (E2), all `y` of four toy keys:
  `β(y)` is within a factor 1.3 of `δ` for `y ≠ 0`, except on the smallest key (`F₁₆`, `(5, 2)`:
  up to `1.8·δ`). `β(0)` is larger on toy keys because `𝒪 ⊂ P^{−1}(0)` is 0.4% to 6% of that
  fibre. At `(119, 45)` it is `256^{−29}` of it.
- **cGPI.** Call *chosen-target GPI* the assumption that `D` and `D°` are indistinguishable as
  oracles, given `pk`. For uniform targets it is GPI ([UA] §3 item 3, Corollary of Lemma D). It is
  statistically false after a few hundred calls, like GPI.

**Decomposition [proved, trivial].** For every adversary `A` and every event `E`,

    | Pr[A^{D}(pk) ∈ E] − Pr[A^{D°}(pk) ∈ E] |  ≤  Adv^{cgpi}(A′),

with `A′` of the same cost. So an attack that uses the oracle does one of two things:
- it works with `D°`: it uses **fibre points of public varieties** (§2.1–2.2, §2.6–2.7, §3);
- it distinguishes `D` from `D°`: it uses **goodness** (§2.3–2.5).

No reduction follows from this: `D°` is not efficient. It organizes the search.

## 2. Key recovery with the oracle

One oil vector gives `𝒪` in polynomial time ([Péb24a], as recalled in [UOS]). So "the oil space
or a trapdoor-equivalent" means: one nonzero oil vector, or any structure that inverts `P` at
uniform targets.

### 2.1 K1: vinegar collisions [proved; Lean; experimental]

**Lemma K1.** Let `s_i`, `s_j` be good, `λ ∈ F^×`. Then `s_i + λ·s_j ∈ 𝒪` iff
`vin(s_i) = λ·vin(s_j)`. If the targets are not proportional by `λ²`, the oil vector is nonzero.

*Proof.* `vin` is linear with kernel `𝒪`. If `s_i = λ s_j` then `y_i = λ² y_j`. ∎

- Lean: `vinegar_reuse` (`Spec/PqovVinegar.lean`). For the model `Spec.Pqov` of the signer, two
  answers computed with the same vinegar `v`, `det L_v ≠ 0`, on targets `t ≠ t′` differ by a
  nonzero combination of the oil vectors `ō_j`, on which `P` vanishes.
- By L1, a pair of answers has proportional vinegars with probability `255/|G|`. Over `Q` calls:

      Pr[some pair collides]  ≤  C(Q, 2)·255·256^{−74}/(1 − δ)  =  Q²·2^{−585.0}.

  This is `2^{−457}` at `Q = 2^64` and `2^{−545}` at `Q = 2^20`. A collision needs `2^{292.5}` calls.
- The collision is detected by `P(s_i + λ s_j) = 0`, at no cost. A zero of `P` on the line through
  two answers is otherwise an event of probability `255·2^{−360}` per pair (Hypothesis X of [SA]
  §3.3), far below one over `2^{127}` pairs.
- **This is why the vinegar must depend on the whole target, and on nothing else that repeats.**
  `ov_derive_preimage` hashes the target, and its DST keeps it apart from `ov_sign`, whose vinegar
  hash would otherwise collide with it by construction (patch 0001, comment at `ov.c:217-224`).
  A signer that reused one vinegar for two targets would give `𝒪` after two calls.
- Experimental (E5): on toy keys the number of projective vinegar collisions among `n` answers to
  distinct targets is the birthday number `n²/(2(1−δ)·|ℙ(F^V)|)`: 2.4, 1.3, 66.4, 12.8 found per
  run for 2.8, 1.1, 68.7, 11.9 expected. Each is checked to give a nonzero oil vector.

### 2.2 K2: dependent vinegars in larger sets [proved count; heuristic]

- `Σ_{i ∈ I} α_i s_i ∈ 𝒪` iff `Σ α_i·vin(s_i) = 0`. For `|I| = r ≤ 74` this has probability
  `≈ 256^{−(75 − r)}` per set.
- At `Q = 2^64` there are `2^{64r}/r!` sets. The expected number of dependent ones is `2^{−247}`
  for `r = 5` and `2^{29.5}` for `r = 9`. So **dependent 9-sets exist**. (Any 75 answers are
  dependent: `75 + 45 > 119`.)
- They cannot be recognized. The test available without `𝒪` is "`P` has a zero in the span of the
  set". For independent vinegars this happens with probability `≈ 256^{−(46 − r)}`: 45 quadrics
  in `r − 1` projective unknowns, under Hypothesis X. That is `256^{29} = 2^{232}` times more
  likely than a dependent set, for every `r`. (For `r ≤ 5` neither event occurs at `Q = 2^64`.)
- A zero found this way is a second singular vector. It is worth one forgery for the target 0
  ([SA] C3), not an oil vector.
- Searching sparse combinations of answers for oil vectors is searching `F^N` in other
  coordinates: 119 answers span `F^N`.

### 2.3 K3: first-order statistics of goodness [proved variance; experimental]

The answers avoid `Bad`, and `Bad` is a union of cosets of `𝒪`. A statistic that sees this
periodicity finds `𝒪`. The simplest ones are the additive characters `s ↦ ψ(w·s)`, `w ∈ F^N`.

**Lemma F [proved, for a uniform block `S`].** For `w ≠ 0` let `c(w) = E[ψ(w·s)]` over the answer
`s` to a uniform target, and `X(w) = Σ_{v ∈ F^V bad} ψ(w·(v, 0))`.
1. `c(w) = 0` unless `w ∈ 𝒪^⊥`. For `w ∈ 𝒪^⊥`, `c(w) = −X(w)/|G|`.
2. For `w ∈ 𝒪^⊥`, the law of `w·s` is the same **for every target, chosen or not**.
3. If `S = (P1 + P1ᵀ)O + P2` is uniform (uniform `P2`; [UA] §1), then for every fixed `w`

       E[X(w)] = 1 − δ_u,        Var[X(w)] = δ_u(1 − δ_u)·(q^V − q + 1),

   with `δ_u = 1 − ∏_{i ≤ M}(1 − q^{−i})`.

*Proof.* 1: in the coordinates `s = (v, 0) + ι(x)` the answer to a uniform target has `(v, x)`
uniform on `G × F^M` ([UA] Lemma C). `w·s` is a linear form in `(v, x)`; its `x`-part vanishes
iff `w ∈ 𝒪^⊥`, and otherwise the sum over `x` is zero. For `w ∈ 𝒪^⊥`, `Σ_{v ∈ G} ψ = −X(w)`
because the sum over all `v` is zero. 2: by L1.1. 3: `v = 0` is bad and contributes 1. Bad is a
cone (L2), so group the other `v` by projective points `[v]`: `X = 1 + Σ_{[v]} 1_bad([v])·c_{[v]}`
with `c_{[v]} = Σ_{λ ≠ 0} ψ(λ·w·v)`, which is `q − 1` if `w·v = 0` and `−1` otherwise. `L_v =
vᵀS` is uniform for `v ≠ 0`, and for linearly independent `v, v′` the pair `(L_v, L_{v′})` is
uniform. So the indicators `1_bad([v])` have mean `δ_u` and are pairwise independent. Then
`E[X] = 1 + δ_u·Σ_{v ≠ 0} ψ(w·v) = 1 − δ_u`, and `Var[X] = δ_u(1−δ_u)·Σ c²_{[v]}` with
`Σ c² = (q−1)²·(q^{V−1}−1)/(q−1) + q^{V−1} = q^V − q + 1`. ∎

**At `(119, 45)`.** The bias of a character on `𝒪^⊥` has root mean square

    |c(w)|  ≈  √(δ_u/(1 − δ_u))·q^{−V/2}  =  2^{−4.0}·2^{−296}  =  2^{−300}.

- Seeing one such bias needs `2^{600}` answers. With `2^64` answers the advantage of one character
  is about `2^{32 − 300} = 2^{−268}`.
- Choosing the targets does not help (item 2).
- Trying many characters does not help either: the attacker does not know which `w` lie in
  `𝒪^⊥`, and the largest of the `2^{592}` biases is, heuristically, `√(2·ln 2^{592}) ≈ 29` standard
  deviations: `2^{−295}`.
- The sum of all squared biases is `Σ_{w ∈ 𝒪^⊥ ∖ 0} c(w)² = q^V/|G| − 1 = δ/(1−δ)`. This total is
  the collision probability of K1 in other words; it is collected by pairs of answers, at
  `q^{V/2}` calls, not by single characters.

**Which characters are biased [experimental; heuristic].** `w ∈ 𝒪^⊥` is of *rank one* if
`w = M_a·o` for some `a ∈ F^M` and `o ∈ 𝒪` (`M_a` the polar matrix of `a·P`): then
`w·s = ⟨a, B(s, o)⟩`. For a good `s`, `B(s, o) ≠ 0`, so `Pr[w·s = 0]` is lower than `1/q` by about
`q^{−M}`. On toy keys `X(w)` is an increasing, nearly affine function of the number `N₁(w)` of
such representations, with slope `≈ q^V(1−δ_u)/(q^M − 1)` (E3: e.g. `F₄`, `V = 8`, `M = 3`: mean
`X` is `−14.1` for `N₁ = 0` and `+719.2` for `N₁ = 1`; slope 720.0). So the first-order leak of
goodness is the fluctuation of `N₁(w)` around its mean. At `(119, 45)` the mean of `N₁` is
`(q^M − 1)²/((q − 1)·q^V) ≈ 2^{120}`, its fluctuation `≈ 2^{60}` (heuristically), and
`2^{60}·2^{−360} = 2^{−300}` is the root mean square of Lemma F again. Toy keys have `N₁` of
order 1, so their largest biases are several standard deviations (`≈ q^{−M}`); the real
parameters are in the Gaussian regime.

**The attack works on toy keys [experimental].** E4 draws answers to uniform targets, computes
all `q^N` empirical character sums by a Walsh–Hadamard transform, and takes characters in
decreasing order of magnitude until they span `k·V` dimensions over `F₂` (`q = 2^k`). It succeeds
if they all annihilate `𝒪`; then `𝒪` is their common kernel.

| Field | `(N, M)` | `V` | `q^V/δ` | largest bias `b` | answers needed (3 of 3 runs) | in units of `q^V/δ` | of `1/b²` |
|---|---|---|---|---|---|---|---|
| `F₄` | (7, 3) | 4 | 745 | 0.143 | 2 217 | 3.0 | 45 |
| `F₄` | (8, 3) | 5 | 3 449 | 0.067 | 10 182 | 3.0 | 45 |
| `F₄` | (9, 4) | 5 | 3 318 | 0.062 | 8 285 | 2.5 | 32 |
| `F₄` | (10, 4) | 6 | 12 672 | 0.039 | 21 080 | 1.7 | 32 |
| `F₁₆` | (5, 2) | 3 | 65 536 | 0.0042 | 325 834 | 5.0 | 5.7 |

- The grid of sample sizes has steps of `√2`. The threshold is `2` to `5` times `q^V/δ` on all
  five keys.
- So the answers of the oracle **do** determine the oil space statistically, with `Θ(q^V/δ)`
  calls and `q^N` work. On every toy key this is far more than key recovery from `pk`. At
  `(119, 45)`, `q^V/δ = 2^{600}`.
- This answers one item of [UOS] B.7 for linear statistics. The law of a linear form `w·s`
  differs between bad and good points by exactly 0 for `w ∉ 𝒪^⊥`, and by about
  `2^{−300}/δ = 2^{−292}` for `w ∈ 𝒪^⊥`: more than `2^{−592}`, and far below anything usable. A
  form chosen without the key lies in `𝒪^⊥` with probability `256^{−45}`.

**Other low-degree statistics [heuristic].** A statistic `g(s)` separates `D` from `D°` only if it
is correlated with `1_Bad`, a function of `vin(s)`: `|E_Good[g] − E[g]| ≤ δ/(1−δ)·|E_Bad[g] −
E[g]|`. Quadratic characters `ψ(Q(s))` with `Q` in the span of the public forms are exactly
unbiased on `Good` (`P` maps `U(Good)` to the uniform law, [UA] Lemma C), and have bias
`≈ q^{−59}` on `F^N` (a form of rank 118). We know no statistic of degree above one that does
better than Lemma F. [OC2] §2 proves this for statistics fixed before the key (any degree) and
gives a heuristic for the largest one of degree `d`.

### 2.4 K4: goodness as algebra [proved count]

- Each answer gives `f(s) ≠ 0`, with `f = Σ_T c_T·det J(s)_T` and `c` the Plücker vector of `𝒪`
  ([UOS] B2): `C(119, 45) ≈ 2^{110}` unknowns.
- An inequation is not a linear condition on `c`. As an equation over `F` it reads
  `f(s)^{255} = 1`: degree 255 in `c`.
- The bad points would give linear equations `f(s) = 0` on `c`. The oracle returns none, and the
  adversary cannot ask whether a point of its choice is bad: `D` takes targets, not points.
  [UOS] B3 (a badness oracle gives `𝒪` in `2^{36}` calls) does not apply.
- Bad points are not rare: a line through two points contains one with probability about
  `1 − 1/e` (an eigenvalue in `F` of a random matrix; heuristic).
  The adversary can produce them. It cannot tell which they are; that is GPI ([UOS] Part B).

### 2.5 K5: structural attacks with the answers as side information [proved count; estimate]

The structural attacks solve for oil vectors `o`: `P(o) = 0`, `B(o, o′) = 0`.
- **A good answer adds no equation.** It says `B(s, o) ≠ 0` (L2). Reconciliation with the 44
  linear conditions `B(z₀, o) ∈ F·c` is reconciliation with 44 random linear conditions, which is
  free anyway: `𝒪` has dimension 45.
- **Intersection attack [Beu21].** It uses only the polar matrices. Nothing to add: `2^{194}`.
- **Kipnis–Shamir.** A trial succeeds with probability `2^{−232}`. Vectors derived from answers
  (the answers, their differences, kernels `K_s`) are not closer to `𝒪` than random vectors, by
  L1 and L2: `K_s ∩ 𝒪 = 0` for every answer.
- **If the oracle did return a bad point** (it does not), the best system we know costs `2^{262}`
  bit operations, above the intersection attack ([UOS] B.4, system (b)).
- **Partial trapdoors.** A totally singular subspace `Z` of dimension `d` (`P(Z) = 0`) removes `d`
  equations from a forgery at the price of `d(M − d) + d` variables ([SA] C3 is `d = 1`). This
  needs `N − d ≥ (d + 1)(M − d)`: `d = 1`, or `d ≥ 44`. The oracle gives `d = 1` (`z₀`); a second
  singular vector isotropic to `z₀` is a zero of 45 quadrics in 73 variables, a forgery-sized
  problem.

### 2.6 K6: special targets [proved; experimental]

By L1 the adversary can ask for
- one zero `z₀` of `P`;
- 255 independent points of one fibre `S^G_c`;
- any number of points of `X_T = {s : P(s) ∈ T}` for a subspace `T` of targets of dimension `d`:
  a variety of dimension `74 + d` that contains `𝒪`, cut out by the `45 − d` public quadrics
  `π_T ∘ P`.

**Lemma G (genericity) [proved].** Let `g` be a polynomial of degree `e` on `F^N`, and `y` a
target. If `g` does not vanish on all of `S^G_y`, then the answer `s = D(y)` satisfies
`Pr[g(s) = 0] ≤ 46e/(256·(1 − δ))`.

*Proof.* `s` is a rational function of its vinegar `v`: `x = adj(L_v)(y − P(v, 0))/det L_v`, so
`det(L_v)·s` has polynomial coordinates of degree `≤ 46`. Then `h(v) = det(L_v)^e·g(s(v))` is a
polynomial of degree `≤ 46e` on `F^V`, and on `G` it vanishes exactly where `g(s(v))` does. If
`g` does not vanish on all of `S^G_y`, `h` is not the zero function, so its reduction modulo the
`v_i^{256} − v_i` is a nonzero polynomial of degree `≤ 46e`. By Schwartz–Zippel it has at most
`46e·256^{V−1}` zeros, and `v` is uniform on `G`, of size `(1 − δ)·256^V`. ∎

- So for `e ≤ 5` (`46e < 255`), a polynomial that vanishes on all answers of a fibre, or on more
  than the fraction above, vanishes on the whole good fibre:
  it is a property of the public variety, computable (in principle) from `pk`. Points of `X_T`
  bring no low-degree relation that `pk` does not have. The bound is weak for larger `e`.
- Whether the public varieties have unexpected equations of low degree is a question about `pk`.
  Experimental (E6), `F₂₅₆`, keys `(10, 4)` and `(13, 5)`: the polynomials vanishing on the
  answers are exactly those of the public ideal.

  | Answers | degree | found | public ideal |
  |---|---|---|---|
  | random targets | `≤ 2` (and `≤ 3` at `(10, 4)`) | 0 | 0 |
  | one class, rescaled to `c` | `≤ 2`, affine | 4; 5 | `M`: the `P_k − c_k` |
  | one class, the cone | 1; 2; 3 homogeneous | 0; 3 (4); 30 | 0; `M − 1`; `(M−1)·N` |
  | targets in a plane `T` | 2; 3 homogeneous | 2 (3); 20 | `M − 2`; `(M−2)·N` |
  | control: vinegars in a hyperplane | 1 | 1 | 0 |

  The last row is a deliberately broken signer. The test finds its linear relation, which is a
  vector of `𝒪^⊥`.
- A point of `X_T` is, as far as `𝒪` goes, like any point of `F^N`: for every good `s` and every
  `T`, `{o ∈ 𝒪 : B(s, o) ∈ T}` has dimension `d`, whether or not `P(s) ∈ T`.

### 2.7 K7: differences of preimages [proved]

Two preimages `s, s′` of one target (from `D(y)` and `D(μy)`, or from `D(P(s₀))` for a point `s₀`
of the adversary's choice) differ by `e` with `Q_s(e) = P(e) + B(s, e) = 0`.
- `e ∈ 𝒪` iff the vinegars agree: K1.
- By L1 the pair is two independent uniform points of `S^G_y`. The second point is independent of
  the first given `y`, also when the adversary chose the first.
- What the pair gives is [SA] T1.3: preimages of the plane `span(y, B(s, s′))`.

### 2.8 K8: outside the game

- The number of rejected vinegars for a target is visible through timing. Those vinegars are
  hashes of the secret seed and independent of the returned one ([UA] §2).
- `D` fails with probability `δ^{255}` per target. A failure reveals that 255 hidden vinegars are
  bad, nothing else.
- A quantum adversary still gets classical answers. Fourier sampling on a superposition over
  `Good` would give `𝒪^⊥`, but the oracle does not provide one. Quantum attacks are in [OC2] §4.

## 3. One more preimage with the oracle

The adversary must output `Q + 1` preimages for `n` uniform targets after `Q` calls. A call on a
class `[t_j]` pays for `t_j` ([OR] Lemma S). The question is whether calls can pay for more.

### 3.1 The oracle-free baseline

- Direct forgery with Thomae–Wolf: `2^{140.3}` ([SA] §4.1). With `n` targets, exhaustive search
  gains the factor `n` (`2^{360}/n` evaluations), far above. We know no algebraic multi-target
  gain for MQ; one would lower the baseline of OMPR and of plain UOV alike.

### 3.2 F2, F3: lines and planes

- `z₀ = D(0)` and one equation removed: [SA] C3. It costs one call and gives what Thomae–Wolf
  gives without a call. The two do not stack.
- Two answers `s, s′` reach the targets `α²y + β²y′ + αβ·B(s, s′)`. A given class is met with
  probability `≈ 2^{16}·2^{−360}` per pair (Hypothesis X): `Q²·n·2^{−345}` in all, `2^{−217}·n`
  at `Q = 2^64`.
- An isotropic pair (`B(s, s′) = 0`) would give preimages of the whole plane `span(y, y′)`, by the
  Frobenius-linearity of `α ↦ α²`. Probability `Q²·2^{−361}`: `2^{−233}` at `Q = 2^64` ([OR] §3.5).
- The adversary cannot steer `B(s, s′)`: `s′ = D(y′)` is uniform on a fibre whatever `y′` is, and
  `B(s, ·)` is a linear map onto `F^M`.

### 3.3 F4: spans, and ROS-type attacks [heuristic; experimental]

- For a linear trapdoor function, one-more security fails at once: a linear combination of
  answers is a preimage of the same combination of targets. For `P`,

      P(Σ α_i s_i) = Σ α_i²·y_i + Σ_{i<j} α_iα_j·B(s_i, s_j).

  The diagonal part is `F₂`-linear in `α`. The cross terms are not zero and not under the
  adversary's control (L1; Hypothesis X). They are what stands between OMPR and a ROS-type attack.
- The span of `r` answers contains `256^r` points. Hitting one of `n` uncalled targets has
  probability `256^r·n·2^{−360}` if the images are spread like those of random points. The
  attack is then exhaustive search with a cheaper evaluation, not a new attack.
- Experimental (E7), `F₁₆`: the number of target classes covered by the span of `r` answers
  equals that of `r` random points and that of a random map.

  | `(N, M)`, `r` | points | classes | answers | random points | random map |
  |---|---|---|---|---|---|
  | (9, 3), 2 | 17 | 273 | 16.6 | 16.3 | 16.5 |
  | (9, 3), 3 | 273 | 273 | 170.0 | 170.9 | 172.6 |
  | (10, 4), 3 | 273 | 4369 | 263.5 | 264.5 | 264.6 |
  | (10, 4), 4 | 4369 | 4369 | 2761.7 | 2760.8 | 2761.7 |

  Answers on one class cover **fewer** classes (9.0, 164.9, 246.1, 2749.7): for two preimages of
  `c` the points `(1, β)` and `(1, 1/β)` of the span have proportional images.

### 3.4 F5: translation [proved; estimate]

- From a preimage `s` of `y`, a preimage of `y + Δ` is a solution of `Q_s(u) = Δ`. For uniform
  `Δ` this is the UOV problem, tightly ([OR] A3). For `Δ` chosen before the call it is still a
  system with the oil space of `P`; the adversary cannot choose `Δ` after seeing `s` without
  changing the target it must hit.
- Inside `K_s`, `P(s + u) = y + P(u)` ([SA] T1.1): 45 quadrics in 74 variables. `K_s ∩ 𝒪 = 0`
  for an answer, so this system has no oil space, and Thomae–Wolf has no room (`74 < 2·45`):
  `2^{144.1}` in the reference model, above the baseline.

### 3.5 F6: tables [proved]

`2^64` calls can cover a whole subspace `T` of targets of dimension 8. For a new target `t` and a
point `w` with `P(w) = t + τ`, `τ ∈ T`, the table holds a preimage `s_τ` of `τ`, but
`P(w + s_τ) = t + B(w, s_τ)`: additivity needs the 45 conditions `B(w, s_τ) = 0`. The table does
not shorten a forgery. In the game it also costs `2^64` calls that pay for no challenge target.

## 4. The shift variants OMPR⊕τ

### 4.1 S1: the oracle is the same [proved, trivial]

OMPR⊕τ ([UA] §3 item 8) changes how targets are issued and which outputs win. Its oracle is `D`
on arbitrary targets, as in OMPR. So:
- every attack of §2 is the same attack in both games, with the same cost;
- a separation between OMPR and OMPR⊕τ, if there is one, is on the forgery side: a way to produce
  the last preimage that uses the fixed differences between candidates.

This narrows Conjecture A6 to the question treated in [SA] §4.

### 4.2 S3: shifts chosen after the answers [proved]

[SA] §4.3 argues that shifts cannot be aimed at cross terms because they are fixed before `h`.
The shifts of a later request can depend on earlier answers. This does not help:

**Lemma S3.** Let `R ⊂ F^M` be the set of targets for which the adversary holds or can compute a
preimage when it submits the shifts `δ_1..δ_τ` of a request. The request's challenge `h` is
uniform and independent of `R` and of the shifts, so

    Pr[ h ⊕ δ_a ∈ R for some a ]  ≤  τ·|R|·256^{−45}.

- With `R` the image of the span of `r` answers, the lines through `z₀`, or any set of size `W`
  that the adversary can enumerate, the gain over OMPR is the counting factor `τ` of [UA]
  Prop. 8(c), and the attack is exhaustive search.
- Two calls on two candidates of one request give two preimages for one index. Candidates of
  different requests are proportional with probability `≤ 255·τ²·256^{−45}` ([SA] §4.3).

### 4.3 What remains: C1

Collinear shifts ([SA] C1) trade one equation for a landing with probability `τ/256`. At τ = 17
this costs `2^{142.4}` against `2^{140.3}` in the reference model, and between `2^{0.7}` less and
`2^{2.1}` more over the cost models tried; never more than `τ = 2^{4.1}` less. The oracle does not
change this: its one contribution to a forgery is the singular line (F2), which gives the same
saving as Thomae–Wolf and does not stack with C1 beyond `τ*/τ` ([SA] C3).

## 5. Experiments, and how far they extrapolate

`scripts/ompr-cryptanalysis/ompr_toy.py` (pure Python, about four minutes for `all`, under
1 GB). The toy signer is `derive_preimage` with the same hash input layout and retry rule. Keys
have a uniform block `S`, as pqov's keys have for a uniform `P2`.

| # | Experiment | Sizes | Result |
|---|---|---|---|
| E1 | Law of the answer to `0`, `c`, `μc` | `F₁₆`, (5, 2) | uniform on the good fibre (§1) |
| E2 | Bad fraction `β(y)` of every fibre | `F₄` (7, 2), (8, 3); `F₁₆` (5, 2), (6, 2) | `≈ δ` for all `y ≠ 0` (§1) |
| E3 | `X(w)` for all `w`, six keys per size | `F₄`, `F₁₆`, `F₂₅₆`; `V = 2..8` | mean square is 0.95 to 1.01 of Lemma F for `V ≥ 3`; 0.83 for `F₂₅₆`, `V = 2` (§2.3) |
| E4 | Oil space from answers, first order | `F₄` `V = 4..6`, `F₁₆` `V = 3` | succeeds at 2 to 5 times `q^V/δ` answers (§2.3) |
| E5 | Vinegar collisions | `F₁₆` (8, 3), (9, 3); `F₂₅₆` (5, 2), (6, 2) | birthday rate; every collision is an oil vector (§2.1) |
| E6 | Polynomials vanishing on answers | `F₂₅₆` (10, 4), (13, 5) | the public ideal only (§2.6) |
| E7 | Classes covered by spans | `F₁₆` (9, 3), (10, 4) | as for random points (§3.3) |

**What the toys show.**
- The oracle does help key recovery on toy keys, in two ways and no third that we found: K1 with
  `≈ q^{V/2}` calls and K3 with `≈ q^V/δ` calls. On every toy key both need more calls than a
  brute-force key recovery needs operations. So at no size we tried is the oracle the cheapest
  way to the key.
- The forgery-side tests (E7) and the algebraic test (E6) see no difference between answers and
  generic points.

**What transfers to `(119, 45)`.**
- L1, K1, Lemma F, Lemma G and S3 are proved for all sizes. The figures `2^{−457}`, `2^{292.5}`,
  `2^{−300}`, `2^{600}` are evaluations of proved formulas, under two modelling steps: the vinegar
  hash is a random oracle, and `P2` is uniform.
- The cost figures B0, B1, F5, S2 are estimates in the hybrid-XL model of [SA] §4.1, with its
  caveats.

**What does not.**
- E4's constants. On toy keys a few characters have biases of several standard deviations, since
  `N₁(w)` is of order 1 (§2.3). The real parameters have `N₁ ≈ 2^{120}`. The threshold in units of
  `q^V/δ` should grow by a logarithmic factor, not shrink.
- E6 and E7 are at `N ≤ 13`. They test Hypothesis X and the public ideal in low degree; they do
  not test degrees near the operating degree of XL at `(119, 45)`.
- Toy fields `F₄`, `F₁₆` have `δ` of 0.31 and 0.066. The dependence on `δ` is in the formulas.
- No experiment can show the absence of an attack. The list of §0 is what was tried.

## 6. Status of Conjecture A6 and of OMPR

- **OMPR for UOV.** Conjecture (this note): for uov-Ip-pkc keys and `Q ≤ 2^64` calls, the best
  attack on OMPR is the direct forgery attack on the UOV problem, `≈ 2^{140}` multiplications,
  which makes no calls; an adversary of running time `T` gains at most `Q²·2^{−585}` (K1) plus
  what it gains against cGPI from its calls. *Basis:* §1 (the oracle is fibre points and
  goodness), §2 (neither leads to the key below `2^{194}`), §3 (no call pays for two targets).
  *Update:* the direct forgery is P1 of [OC2], `≈ 2^{138.5}` multiplications.
  *Caveats:* no outside cryptanalysis; cGPI is new and its low-advantage distinguishers are
  bounded only for linear statistics; classical only.
- **A6.** Unchanged in substance, sharper in scope. The oracles coincide (S1), shifts chosen
  after answers give the counting factor only (S3), so A6 reduces to the forgery-side statement
  of [SA] §4.4: for `τ ≤ τ*` the best attack on OMPR⊕τ(N, q) is the best attack on OMPR(τN, q), and
  for `τ > τ*` it is cheaper by `τ/τ* ≤ τ` (C1). No reduction is known ([OR] A4, [SA] Theorem R),
  and none is given here.
- **Advice.** Unchanged: U1 as PomFRIT's main statement, U2 under OMPR⊕17, at most 4 bits below
  the direct forgery cost.

## 7. Lean and script

| Statement | Lean | File |
|---|---|---|
| K1: answers with one vinegar on targets `t ≠ t′` differ by a nonzero oil combination, a zero of `P` | `preimageVec_sub_same_vinegar`, `vinegar_reuse` | `Spec/PqovVinegar.lean` |
| L2.1: `L_{cv} = c·L_v`, `det L_{cv} = c^{45}·det L_v`, the good vinegars are a cone | `sysMat_smul`, `det_sysMat_smul`, `good_smul_iff` | `Spec/PqovVinegar.lean` |
| L1.2: an answer is a preimage; the fibre count | `qmap_preimageVec`, `signer_correct`; `card_good_fiber`, `good_coords_bijective` | `Spec/PqovSigner.lean`; [UA] §10 |
| Lines, planes, scaling used in §3 | `preimage_line`, `preimage_plane`, `scaled_preimage` | `Spec/PqovShift.lean`, `Spec/PqovScale.lean` |

The Lean statements are for `Spec.Pqov`, the model of pqov's signer that `lake exe spec_kats`
checks against the C++. Axioms: `propext`, `Classical.choice`, `Quot.sound`. On paper only: L1
(it is [UA] Lemma C and D), Lemma F, Lemma G, S3, and all counts and estimates.

Script: `ompr_toy.py [law|fibre|fourier|attack|collide|annih|span|table|all] [seed]`. `table`
prints the figures of §0 and §2 for `(119, 45)`. Run it under a memory cap; `attack` builds
tables of `q^N ≤ 2^{20}` integers. Counts vary with the seed.

## 8. Open

- cGPI and GPI against statistics of degree above one ([UOS] B.7). *[OC2] §2:* proved for
  fixed statistics of the vinegar; heuristic for key-dependent ones; open for statistics of the
  whole answer at chosen targets.
- Lemma F's tail. *[OC2] Theorem T:* `max_w |c(w)| ≤ 2^{−148}·ε^{−1/4}`, from the fourth
  moment. A sharp bound is open.
- The exact relation between `X(w)` and `N₁(w)`. *[OC2] Theorem H:* `X(w) = Σ κ(rank T)` over
  the matrices `T` with `L*(T) = w`; the rank-one term is `κ(1)·N₁(w)`.
- An algebraic multi-target attack on MQ, and the hardness of `P` on `K_s` (§3.4). *[OC2] §3:*
  the class attack P1 (one equation), nothing beyond it; amortizing XL is open.
- Quantum attacks on OMPR. *[OC2] §4:* estimates; no use of the oracle found.
- OMPR ⇒ OMPR⊕17 by a reduction ([OR] §7, [SA] §7).

## References

Citations are from memory.

- [OC2] `ompr-cryptanalysis-2.md`.
- [UA] `uov-assumptions.md`. [UOS] `uov-open-structure.md`. [OR] `uov-open-reductions.md`.
  [SA] `ompr-shift-algebra.md`. The references [Beu21], [KS98], [TW12], [FNT21], [Péb24a] are
  listed there.
- ROS: C.-P. Schnorr, *Security of blind discrete log signatures against interactive attacks*,
  ICICS 2001; F. Benhamouda, T. Lepoint, J. Loss, M. Orrù, M. Raykova, *On the (in)security of
  ROS*, EUROCRYPT 2021.
