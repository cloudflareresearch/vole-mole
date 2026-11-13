# OMPR versus OMPR⊕τ: what the algebra of the UOV map gives

This note continues `uov-open-reductions.md` (cited as **[OR]**) §4 and `uov-assumptions.md`
(**[UA]**) §6. The question is Conjecture A6 of [OR]: does OMPR ([UA] §3 item 7) imply the
τ-shift variant OMPR⊕τ (item 8; τ = 17 in PomFRIT, `pomfrit.md` §5–§6) with polynomial loss?

[OR] A4 shows that a reduction which is black-box in the adversary **and** in `(P, D)` loses
`τ^{q+1}/2`. That leaves reductions that use the algebra of `P`. This note treats them, and the
opposite question: does the algebra give an attack on OMPR⊕τ that fails for OMPR?

Notation is that of [UA] §1 and [OR] §1: `F = GF(256)`, `P : F^N → F^M`, `(N, M, V) = (119, 45,
74)`, oil space `𝒪`, `D = derive_preimage`, `Good`, `L_v`, class `[t] = F^×·t`, `√μ = μ^{128}`.
The characteristic is 2, so `⊕`, `+` and `−` on vectors are the same operation. `B(s, u) = P(s + u)
+ P(s) + P(u)` is the polar form, `DP_s = B(s, ·)`, `K_s = ker DP_s`.

**Status labels.** *Proved*: full proof here. *Lean*: also machine-checked. *Heuristic*: argument
with a stated unproved hypothesis. *Estimate*: cost figure from the usual hybrid-XL model.
*Experimental*: checked on toy parameters by `scripts/ompr-shift-algebra/shift_algebra_toy.py`.
*Conjecture*: no proof. Citations are from memory. Nothing here changes the protocols.

## 0. Summary

| # | Statement | Status | Where |
|---|---|---|---|
| R | **A4 holds for UOV itself, for every reduction that is black-box in the adversary only.** Such a reduction `R` may use `pk` and the algebra of `P` in any way, and may rewind. Against one explicit adversary it wins OMPR with probability `≤ 2·τ^{−(q+1)} + Adv^{free}_{UOV}(M) + V⁴·2^{−343}`, where `M` is an OMPR^free adversary ([OR] §3.1) of about `R`'s running time. So: a reduction of this kind with loss below `τ^{q+1}/4` **is** an attack on OMPR^free, i.e. it contains a combiner across classes | proved | §2 |
| T1 | Toolbox: polar form, kernel translation, the preimage line through a singular vector (`D(0)` gives one), `P` on the span of two preimages | proved, Lean (`qmap_add_of_polar_eq_zero`, `preimage_line`, `preimage_plane`) | §1 |
| T2 | An affine symmetry `P(As + a) = T(P(s)) + c` shifts targets only by `c = P(a)` with `a ⊥ im A`. If `A` is onto and `rad B = 0`, then `a = 0`, `c = 0`. `rad B = 0` for every key with `δ < 1` and `v ↦ L_v` injective | proved, first part Lean (`affine_symmetry`) | §3.1 |
| T3 | **`P` has no symmetries but the scalings.** For every oil space and all but a fraction `≤ 256^{−976} < 2^{−7800}` of the keys: (G) the only linear pairs `(A, T)`, `A` invertible, with `P∘A = T∘P` are `(λI, λ²I)`; (L) the only infinitesimal pairs `B(s, Xs) = Y·P(s)` are `F·(I, 0)`; (S, A) the same for Frobenius-semilinear and for all additive bijections, with an affine part. So a symmetry pair moves a target only inside its class. Checked: (L) at full size on two keys; the full group on toy keys over `F₄` | proved (model: `P1`, `P2` uniform); identities Lean (`symmetry_polar`, `symmetry_eigen`, `infinitesimal_polar`, …); experimental | §3.1, §8 |
| T4 | A translator for one fixed shift `Δ₀` is worth exactly one equation: `UOV(119, 45) ≤ UOV-projected(119, 44) ∘ Tr_{Δ₀}`, and `Tr_{Δ₀} ≤ UOV(119, 45)`. In the cost model the gap is `≈ 2^{3.7}`. For uniform shifts translation is the UOV problem ([OR] A3) | proved; figure: estimate | §3.2 |
| T5 | The linear span of known preimages gives targets `Σ α_i² y_i + Σ α_iα_j B(s_i, s_j)`. The reduction controls the `y_i`, not the cross terms. On toy keys the cross term of two sampler answers is uniform. With the oil space, translation is linear algebra; without it, every route we checked is an MQ instance or a class | proved identities; heuristic conclusion; experimental | §3.3–3.4 |
| C1 | **Collinear shifts remove one equation.** With shifts `λ_a·c`, a forgery is a solution of 44 of the 45 equations that lands on one of the `τ` points of a line of 256. For `τ ≥ 256` this is a real gain of `≈ 2^{3.7}` (model) over any known attack on OMPR with independent targets. For τ = 17 the landing cost `256/17 = 2^{3.9}` exceeds it: `2^{144.2}` against `2^{144.1}` | reduction proved; costs: estimate | §4.1 |
| C2 | No other structured shift list (subfield lines, `F₂`-subspaces, higher-dimensional `F`-subspaces), and no use of the `D` oracle together with the shifts, gives more than the counting factor τ | heuristic, estimate | §4.2–4.3 |

**Answer.** We found neither a polynomial-loss reduction nor an attack at τ = 17.
- *Reductions.* The obstacle A4 is not an artefact of the generic model. For UOV, a better
  adversary-black-box reduction exists only if OMPR^free fails (R). The algebraic tools at hand
  (T1–T5) give no combiner across classes. What remains is a reduction that is not black-box in
  the adversary.
- *Attacks.* The one structural use of the shifts is C1. It is below break-even at τ = 17 and
  small for every τ. Conjecture A6 of [OR] should be read "up to the factor of §4.1" for
  `τ ≳ 20`.
- *Advice.* Unchanged from [UA] §6: U1 as the main statement, U2 under OMPR⊕17.

---

## 1. Toolbox

`P` is a homogeneous quadratic map without linear or constant terms. For all `s, u ∈ F^N`,
`λ, α, β ∈ F`:

    (P1)  P(s + u) = P(s) + P(u) + B(s, u),   B bilinear, symmetric, B(s, s) = 0;
    (P2)  P(λs) = λ²·P(s);
    (P3)  P(αs + βs′) = α²·P(s) + β²·P(s′) + αβ·B(s, s′).

Lean: `qmap_add`, `polar_sum_left/right` (`Spec/PqovSigner.lean`), `qmap_smul`
(`Spec/PqovScale.lean`), `polar_smul_left/right`, `preimage_plane` (`Spec/PqovShift.lean`).

**Lemma T1 [proved; items 1–3 Lean].** Let `P(s) = y`.
1. *Kernel translation.* If `u ∈ K_s` then `P(s + u) = y + P(u)` (`qmap_add_of_polar_eq_zero`).
2. *Singular line.* If `P(z) = 0` then `P(s + λz) = y + λ·B(s, z)` for all `λ` (`preimage_line`).
   - Oil vectors are singular. So is `z₀ = D(0)`, which is nonzero and not in `𝒪`: its vinegar is
     good, and the vinegar `0` is bad (`L_0 = 0`).
3. *Two preimages.* If also `P(s′) = y` then `P(αs + βs′) = (α + β)²·y + αβ·B(s, s′)`
   (`preimage_plane`, and `α² + β² = (α + β)²`). Two preimages of one target give preimages of
   every point of the plane `span(y, b)`, `b = B(s, s′)`, outside the line `F·b`.
4. *Oil translation.* For `o ∈ 𝒪`, `P(s + o) = y + B(s, o)`. The linear map `𝒪 → F^M`,
   `o ↦ B(s, o)`, is bijective iff `s` is good. So the holder of `𝒪` turns a good preimage of `y`
   into a preimage of any `y + Δ` by solving one linear system.
5. *Good means no oil in the kernel.* `s` is good iff `𝒪 ∩ K_s = {0}` ([UA] §1). Then
   `dim K_s = N − M = 74`.

*Proof.* 1–3 are (P1)–(P3). 4: `P(o) = 0`, and in the coordinates `s = (v, 0) + ι(x)`,
`B(s, ι(x′)) = L_v·x′` because `B` vanishes on `𝒪 × 𝒪`. 5: the kernel of the map in 4 is
`𝒪 ∩ K_s`; for good `s` the rank of `DP_s` is `M`. ∎

All five items are checked on toy keys by the script (part 1).

**The translation equation.** Given `P(s) = y` and a shift `Δ`, a preimage `s + u` of `y + Δ` is a
solution of

    (Tr)  Q_s(u) := P(u) + B(s, u) = Δ.

`Q_s` is the translated map `u ↦ P(s + u) + P(s)`. It is quadratic with linear terms, and it has
the same oil space as `P` in the sense of item 4.

## 2. Theorem R: reductions that are black-box in the adversary only

### 2.1 Statement

**Reductions.** `R` is an OMPR(n, ·) adversary: it gets `pk`, targets `t_1..t_n` and the oracle
`D`. It also has oracle access to an OMPR⊕τ adversary as a next-message function, so it may
rewind it, interleave runs, and choose every `h_k`. `R` is not restricted in how it uses `pk`: it
knows the coefficients of `P` and may compute anything from them. This is the class
"black-box in the adversary". [OR] A4 treats the smaller class that is also black-box in
`(P, D)`.

**The adversary `A**_D`.** It is `A**` of [OR] §4.4, with one change: the forgery for the
candidate `z = h_k ⊕ δ_{k,a_k}` is `D(z)`. In full, for `q ≥ 1` and `q + 1` requests, with private
random functions `S_k`, `G`, `a`:
1. For `k = 1..q+1`: submit the list `δ_k = S_k(h_1..h_{k−1}) ∈ (F^M)^τ`, receive `h_k`. Let
   `H = (h_1..h_{q+1})`.
2. Ask `D` for preimages of the junk targets `(u_1..u_q) = G(H)`. Check the answers with `P`.
   Abort if one is wrong.
3. Output `(k, a_k, D(h_k ⊕ δ_{k,a_k}))` for every `k`, with `a = a(H) ∈ [τ]^{q+1}`.

`A**_D` makes `q` calls and wins OMPR⊕τ(q+1, q) unless one of its `2q + 1` evaluations of `D`
fails: with probability `≥ 1 − (2q+1)·δ^{255}`. It is
efficient given `sk`. A reduction that is black-box in the adversary cannot tell it from an
adversary without `sk`.

**OMPR^free** is [OR] §3.1, in one-more form, with targets on demand: a call is *charged* to
index `j` if its target is in `[t_j]`; `M` wins if it outputs preimages of more distinct indices
than there are charged indices.

**Theorem R [proved].** Let `τ ≥ 7`, `q ≥ 1`. Let `R` be as above, with `c` calls to `D` and `T`
messages to `A**_D`. Then there is an OMPR^free adversary `M` with

    Pr[R^{A**_D} wins OMPR(n, c)]  ≤  2·τ^{−(q+1)} + Adv^{free}_{UOV}(M) + V⁴·2^{−343},

where `V = n + c + (τ + 1)(q + 1)·T`. `M` runs `R` once, requests at most `n + q·T` targets,
makes at most `c + (q + 1)·T` calls, and does `O(V)` further work (lazy sampling, checks).

**Corollary R′ [proved].** Suppose a reduction of this class has loss `L`: for every adversary
`A`, `Adv^{ompr}(R^A) ≥ Adv^{ompr⊕τ}(A)/L`. If `L ≤ τ^{q+1}/4`, then

    Adv^{free}_{UOV}(M) ≥ 1/(2L) − (2q + 1)·δ^{255}/L − V⁴·2^{−343}.

So for UOV: **either OMPR^free is false, or every adversary-black-box reduction from OMPR to
OMPR⊕τ loses more than `τ^{q+1}/4`**, whatever algebra it uses and however it rewinds. For
τ = 17 that is `2^{4.08(q+1) − 2}`.

### 2.2 Proof

`M` plays OMPR^free and runs `R`, simulating `R`'s game and `A**_D`.
- `M` passes `pk` on and gives `R` its first `n` targets. It forwards `R`'s calls to `D`.
- It samples `S_k` and `a` lazily. For `G(H)` at a new `H` it requests `q` new targets of its own
  game. They are uniform, as junk must be.
- It checks `R`'s answers to the junk queries with `P`. If all `q` are right, the run `H` is
  *completed*: `M` stores the `q` answers, draws `a(H)`, calls `D` on the `q + 1` candidates
  `z_k = h_k ⊕ δ_{k,a_k}`, and returns the forgeries.
- When `R` stops with preimages of `c + 1` distinct challenge indices, `M` outputs them and the
  stored junk answers of all completed runs.

The simulation is exact. Let `K` be the number of completed runs.

*Step 1: bad events on values.* They concern only values of `F^M`, not `P`. Call *targets* the
challenge and junk targets.
- (E1) A target is `0`, or two targets lie in one class.
- (E2) A junk value, when revealed, lies in the class of a candidate `h_k ⊕ δ_{k,a}` already in
  play.
- (E3) A list has two equal shifts, or one request of one run has two shifts `a ≠ a′` whose
  candidates both lie in classes of targets: `δ_{k,a} ⊕ δ_{k,a′} = μw ⊕ μ′w′`, `μ, μ′ ≠ 0`.

Targets and lists are uniform values, fresh when revealed. In (E3), the last revealed among
`δ_k`, `w`, `w′` must hit one of at most `255²·V³` values fixed before it (if `w = w′`, then
`μ ≠ μ′` and `w = (δ_{k,a} ⊕ δ_{k,a′})/(μ ⊕ μ′)`). So `Pr[E1 ∨ E2 ∨ E3] ≤ V⁴·2^{−343}`. Assume
none occurs.

*Step 2: the lottery.* Call a candidate *useful* if it lies in the class of a target. By (E3)
each request of each run has at most one useful shift `b_k(H)`. By (E2) it is determined when `R`
sends `h_k`. `a(H)` is drawn after that, uniformly. Let `X_i` be the number of useful forgeries of
the `i`-th completed run, and `Z_j = Σ_{i ≤ j}(X_i − q)`. As in [OR] A4, steps 3–4 (Lean
`rewind_supermartingale`, Ville's inequality):

    Pr[∃ j ≥ 1 : Z_j ≥ 1] ≤ 2·τ^{−(q+1)}.

*Step 3: accounting.* Suppose `R` wins and `Z_K ≤ 0`.
- `M` outputs preimages of `c + 1 + K·q` distinct indices.
- Its calls are `R`'s `c` calls and the `K(q + 1)` candidate calls. By (E1) a call is charged to
  at most one index. A candidate call is charged only if the candidate is useful.
- So at most `c + Σ X_i = c + K·q + Z_K ≤ c + K·q` indices are charged, and `M` wins.

Hence `Pr[R wins] ≤ Pr[∃ j : Z_j ≥ 1] + Adv^{free}(M) + Pr[bad]`. ∎

*Proof of R′.* `(1 − (2q+1)δ^{255})/L ≤ Pr[R^{A**_D} wins]`, and `2τ^{−(q+1)} ≤ 1/(2L)`. ∎

### 2.3 Remarks

- **What changed against A4.** In the generic model, "a fresh forward value hits a target" has
  probability `2^{−360}`. For UOV that step is a computational statement, and it is exactly
  OMPR^free: nobody turns preimages of free targets into a preimage of a challenge or junk
  target. The lottery (steps 1, 2) needs no property of `P`. Scaling ([OR] Lemma S) is built in:
  usefulness is defined on classes.
- **The assumption used is weaker than OMPR^free.** `M`'s free calls are only the non-useful
  candidates `h ⊕ δ_a`: `R` chooses `h` after seeing a uniform list `δ`, and `a` is uniform and
  out of its control. "No combiner from lottery calls" suffices.
- **OMPR alone does not suffice** for this proof: in plain OMPR `M` has made `c + K(q + 1)` calls
  for `c + 1 + Kq` preimages. [OR] B3 shows that OMPR^free does not follow from OMPR by a
  relativizing argument, so we do not expect to remove the term.
- **Scope.** The theorem holds for every efficient `R` run with `A**_D`; `R` may even know the
  description of `A**_D`, but not its random functions or `sk`. What it does not cover is a
  reduction whose guarantee is restricted to adversaries it can inspect (code, or a knowledge
  assumption on how `a_k` is chosen). PomFRIT's `E₁` is of that kind: it reads the shift from the
  prover's commitments (`pomfrit.md` Lemma P), at the cost `Q₃·2^{−71}`.
- **Direction.** R is one-directional. A combiner for lottery calls would not by itself give a
  reduction for all adversaries, since an adversary may choose `a_k` as a function of `h_k`.
- For `q = 0` there is no junk, and guessing loses only τ.

## 3. The algebraic tools as combiners

By Theorem R, an adversary-black-box reduction that beats guessing must turn a preimage `s` of a
candidate `z = h ⊕ δ_a`, which it did not aim at a target, into a preimage of a target, more
cheaply than by a call. This section goes through the algebra of `P` and says what each tool
gives. None gives such a combiner.

### 3.1 Symmetries of `P`

A public pair of maps `(φ, Θ)` with `P ∘ φ = Θ ∘ P` moves preimages of `y` to preimages of `Θ(y)`.
A reduction wants `Θ(y) = y ⊕ Δ`.

**Lemma T2 [proved; Lean `affine_symmetry`].** Let `φ(s) = As + a` and `Θ(y) = Ty + c` with `A`,
`T` linear, and `P(As + a) = T·P(s) + c` for all `s`. Then
1. `c = P(a)`;
2. `B(As, a) = 0` for all `s`;
3. `P ∘ A = T ∘ P`.

If `A` is onto and `rad B = {a : B(·, a) = 0}` is `0`, then `a = 0` and `c = 0`.

*Proof.* `s = 0` gives 1. Then (P1) gives `P(As) + B(As, a) = T·P(s)` for all `s`. Replace `s` by
`λs`, `λ ∉ {0, 1}`: `λ²P(As) + λB(As, a) = λ²T·P(s)`. Subtract `λ²` times the first equation:
`(λ + λ²)·B(As, a) = 0`. ∎

The Lean statement needs only that `A` and `T` are homogeneous of degree 1.

**Lemma T2′ [proved].** If `δ(sk) < 1` and `v ↦ L_v` is injective, then `rad B = 0`.

*Proof.* Let `a = (v, 0) + ι(x) ∈ rad B`. Then `L_v = B((v, 0), ι(·)) = B(a, ι(·)) + B(ι(x), ι(·))
= 0`, so `v = 0` and `a = ι(x)`. For a good `v′`, `0 = B((v′, 0), ι(x)) = L_{v′}·x`, so `x = 0`. ∎

- `v ↦ L_v = vᵀS` fails to be injective with probability `≤ 256^{74 − 2025}` over a uniform `S`
  ([UA] §1). `rad B = 0` is also checkable from `pk` by linear algebra.
- So a translation of the domain never translates targets ([OR] A2 item 3, now for every affine
  pair): **the symmetries of `P` act linearly on targets.**

**Which linear pairs exist?** Only the scalings `(λ·I, λ²·I)`.

**Theorem T3 [proved, §8].** Model `P1`, `P2` as uniform ([UA] §1). For every oil matrix `O`, all
keys but a fraction `≤ 256^{−976}` have the following properties.
- (G) *Group.* If `A ∈ GL_N(F)`, `T ∈ F^{M×M}` and `P ∘ A = T ∘ P`, then `A = λ·I`, `T = λ²·I`.
- (L) *Infinitesimal.* If `B(s, Xs) = Y·P(s)` for all `s`, then `X = λ·I`, `Y = 0`.
- (S) *Frobenius.* No pair of bijective `σ`-semilinear maps, `σ ≠ id`, satisfies
  `P ∘ A = T ∘ P`.
- (A) *Additive and affine.* If `φ(s) = A(s) + a`, `Θ(y) = T(y) + c` with `A`, `T` additive
  (`F₂`-linear), `A` bijective or `T` injective, and `P ∘ φ = Θ ∘ P`, then `a = 0`, `c = 0`,
  `A = λ·I`, `T = λ²·I`.

(G) and (L) are separate statements: neither implies the other over a finite field (§8.1). The
proof is a union bound over `A` (or `X`) by its distance `r` from the scalars, with the count
`256^{M²}` of maps `T` absorbed by a module argument (§8.2–8.4). Characteristic 2 enters in (S),
(A) and in the solution `(I, 0)` of (L), which exists because `B(s, s) = 0` (§8.5).

- *Experimental.* (L) holds for two uniform keys at the real size `(119, 45)` over `F₂₅₆`: the
  system has 321 300 equations in 16 186 unknowns and rank 16 185. The full group of linear and
  semilinear pairs of toy keys over `F₄` with `M ≥ 3` is the three scalings. Toy keys with
  `M = 2` do have more symmetries (§8.7).
- *Not covered.* Maps `φ` that are not additive. One family exists: `φ(s) = γ(P(s))·s`,
  `Θ(y) = γ(y)²·y` for any function `γ : F^M → F`. It stays in the class of the target. Pairs with
  `A` not bijective and `T` not injective exist too (`A` into a singular line, `T = 0`); they
  send every target into a proper subgroup (§8.6).

**Consequence for target re-randomization [proved, given T3].** A reduction that moves preimages
by a public additive or affine pair `(φ, Θ)` with `Θ` injective can re-randomize a target only
inside its class. It cannot produce two targets with a prescribed difference `δ_a ⊕ δ_b`
([OR] §4.6 item 3). The embedding `h = μ·t ⊕ c` aligns a second shift only if
`δ_a ⊕ δ_b ∈ μ·t ⊕ μ′·t′`, the event (E3). The affine-symmetry route to OMPR ⇒ OMPR⊕τ is closed.

### 3.2 Solving the translation equation

`R` holds `s` with `P(s) = y` and wants `u` with `Q_s(u) = P(u) + B(s, u) = Δ`. Public
restrictions of (Tr):

| Restriction of `u` | Equation | What it is |
|---|---|---|
| `u = λs` | `λ²·y = Δ` | the class of `y` only (Lemma S) |
| `u ∈ K_s` (74 dimensions) | `P(u) = Δ` | a preimage of `Δ` under `P` restricted to `K_s` |
| `u = λz`, `P(z) = 0` | `λ·B(s, z) = Δ` | needs `B(s, z) ∈ F·Δ`: 44 linear conditions on `s` |
| `u ∈ 𝒪` | `B(s, u) = Δ` | linear, solvable for good `s`; needs `𝒪` |
| none | `Q_s(u) = Δ` | the UOV problem for the translated map ([OR] §4.3) |

- *Kernel.* `P|_{K_s}` is a system of 45 quadrics in 74 variables. For good `s` it contains no
  oil vector (T1.5), so the trapdoor of `P` is not a trapdoor of `P|_{K_s}`. Even the key holder
  has no linear way to solve it: writing `u = (v, 0) + ι(x)`, the conditions are `L_v·x = Δ +
  P(v, 0)` and `B(s, u) = 0`. For a fixed `v` these are 90 linear equations in the 45 unknowns
  `x`; their consistency is 45 nonlinear conditions on `v`.
- *Singular line.* The only singular vector that `R` can get without solving `P(z) = 0` is
  `z₀ = D(0)` and its multiples, for one call. The direction `B(s, z₀)` is fixed by `s`.

**Lemma T4 (a fixed shift is one equation) [proved].** Fix `Δ₀ ≠ 0` and let
`π : F^M → F^M/F·Δ₀`. Let `Tr` be an algorithm with `P(Tr(s)) = P(s) + Δ₀` for all `s` in a set
`𝒮` closed under scaling.
1. If `π(P(s)) = π(t)` and `s ∈ 𝒮`, then one call to `Tr` and two scalings give a preimage
   of `t`.
2. `π ∘ P` is a quadratic map `F^{119} → F^{44}` that vanishes on `𝒪`. So
   `UOV(119, 45) ≤ UOV-projected(119, 44) ∘ Tr`. Conversely a UOV solver is a translator.

*Proof.* `P(s) = t + μΔ₀`. If `μ = 0` we are done. Otherwise `s₁ = s/√μ` has `P(s₁) = t/μ + Δ₀`,
`s₂ = Tr(s₁)` has `P(s₂) = t/μ`, and `P(√μ·s₂) = t`. ∎

- In the cost model of §4 the 45th equation is worth `≈ 2^{3.7}` (`2^{2.65}` on average over 41
  to 48 equations). So T4 gives no evidence that a fixed-shift translator is hard, and no
  algorithm for one. We know none.
- A reduction needs more than one fixed shift: against `A**_D` the differences
  `δ_{k,a} ⊕ δ_{k,b}` are uniform, and translating a uniform good preimage by a uniform shift
  is the UOV problem ([OR] A3).

### 3.3 The span of known preimages

Let `R` hold preimages `s_i` of `y_i`, `i ≤ r`, from calls and forgeries. By (P1), (P2):

    P(Σ α_i s_i) = Σ α_i²·y_i + Σ_{i<j} α_iα_j·b_{ij},     b_{ij} = B(s_i, s_j).

- `R` chooses the targets of its calls, so it controls the `y_i` of calls. It does not control
  the `b_{ij}`: they are fixed by the answers. For answers `(v_i, 0) + ι(x_i)`,

      b_{12} = B((v₁,0), (v₂,0)) + L_{v₁}L_{v₂}^{−1}(y₂ + P(v₂,0)) + L_{v₂}L_{v₁}^{−1}(y₁ + P(v₁,0)),

  with `v₁`, `v₂` independent uniform good vinegars (ideal sampler, [UA] Lemma D).
- **Hypothesis X [heuristic].** For fixed targets, the cross terms of distinct answers are close
  to uniform and independent on `F^M`. *Experimental* (script, part 3): for toy keys over `F₁₆`
  and fixed `y₁, y₂`, a chi-square test of `b_{12}` against the uniform law on `F²`, 255 degrees
  of freedom (standard deviation 22.6).
  - 40 000 samples: 248.6 and 262.5 for keys `(6, 2)`; 289.9 and 294.2 for keys `(8, 2)`.
  - 300 000 samples: about 320 for four keys `(6, 2)`, a deviation of about 1.5% per cell; 228.8
    and 247.0 for keys `(8, 2)`; 282.0 for a key `(10, 2)` at 200 000 samples.
  - So the law is close to uniform, not equal to it, and the deviation is visible only at the
    smallest size.
- `r = 2`: the reachable targets are `α²y₁ + β²y₂ + αβ·b`. A prescribed `t` outside
  `[y₁] ∪ [y₂]` is reached only if `b ∈ span(y₁, y₂, t)`: probability `≈ 2^{−336}` under X. This
  covers T1.2 (`y₂ = 0`, `s₂ = z₀`) and T1.3 (`y₁ = y₂`).
- General `r`: hitting `t` is a system of 45 quadrics in `r` unknowns with cross terms `b_{ij}`.
  For `r < 45` it has a solution with probability about `256^{r − 45}` under X. For `r ≥ 45` it
  is an MQ instance with random-looking coefficients ([OR] §3.5 item 3). `P` itself is such an
  instance in 119 variables, with an oil space; the span has none that we can see.

So the span of the answers reaches a target outside the called classes only by solving an MQ
system. This is the content of OMPR^free, restated; it is not a proof.

### 3.4 The oil space, and learning translations

- With `𝒪`, (Tr) is linear (T1.4). One oil vector gives `𝒪` in polynomial time ([Péb24a] in
  `uov-open-structure.md`, as we recall it). So a reduction that extracts an oil vector from its
  view breaks the key, and OMPR with it.
- *What the answers tell about `𝒪`.* The answer to a uniform target is a uniform point of `Good`
  ([UA] Lemma C, D). Under GPI ([UA] §3 item 3) it is indistinguishable from a uniform point of
  `F^N`, which `R` can sample itself. For chosen targets the answer is uniform on `S^G_y`; it
  depends on `𝒪` only through `Good`.
- *Differences.* Two preimages of one target differ by a solution `e` of `Q_s(e) = 0`. `R` gets
  such pairs from `D(y)` and `D(μy)` rescaled, or from a forgery and a call on the same target.
  Their vinegars are independent, so `e ∉ 𝒪` (two answers with the same vinegar would differ by
  an oil vector; `D` derives the vinegar from the target). What `e` gives is T1.3: a plane
  through `y` in the direction `B(s, s′)`.
- *Learning a translation by `Δ` at `s`* from the adversary means receiving a second preimage,
  of `y + Δ`. That is a forgery or a call, and it is already counted.

### 3.5 Scaling and shifts

- A forgery for the candidate `z` gives preimages of `[z] = {μh ⊕ μδ_a}`. Scaling does not
  commute with the shift: `μ·(h ⊕ δ_a) = (μh) ⊕ δ_b` needs `(μ + 1)·h = μδ_a ⊕ δ_b`, which a
  uniform `h` avoids ([OR] §4.3).
- For the reduction, usefulness is a property of classes, and one request has at most one useful
  shift (E3). This is why Theorem R has the same bound as A4.
- Homogenizing the shift into the key ([OR] A2) is not available to a reduction: its game fixes
  `P` and `D`.

### 3.6 Verdict on reductions

Every tool either stays inside a class (scaling, symmetries), needs `𝒪` (oil translation), or
restates an MQ problem (kernel, span, full translation). By Theorem R nothing else can help: an
adversary-black-box reduction with loss `L ≤ τ^{q+1}/4` yields an attack on OMPR^free with
advantage about `1/(2L)`.

## 4. The attack side: do shifts help the adversary?

Generically they give the counting factor only: OMPR⊕τ with `N` requests is OMPR with `Nτ`
targets ([UA] Prop. 8(c)). An attack that separates the two must use the fixed differences.

### 4.1 Collinear shifts

**Proposition C1 [proved].** Let request `k` have the shifts `λ_a·c`, `a ≤ τ`, with `c ≠ 0` and
distinct `λ_a ∈ F`. Let `π_c : F^M → F^M/F·c`. Then `s` is a forgery for request `k` iff

    π_c(P(s)) = π_c(h_k)   and   μ(s) ∈ {λ_a},   where P(s) = h_k + μ(s)·c.

- The first condition is the preimage problem for `π_c ∘ P`: 44 quadrics in 119 variables,
  vanishing on `𝒪` (dimension 45).
- If `{λ_a} = F`, which needs `τ ≥ 256`, the second condition is void: OMPR⊕256(N, 0) is at
  most as hard as that 44-equation problem. This is [OR] A2 item 2 read as an attack.
- If `τ < 256`, a solution of the first condition lands with probability `τ/256` (heuristically,
  for a solver that returns an unstructured solution).

**Costs [estimate].** Hybrid XL, the model of `scripts/uov-open-structure/mq_estimates.py`
(script, part 4), field multiplications:

| System | Cost |
|---|---|
| 45 quadrics (direct forgery, [UOS] B.5) | `2^{144.1}` |
| 44 quadrics | `2^{140.3}` |
| 44 quadrics, landing on 17 of 256 points | `2^{140.3}·256/17 = 2^{144.2}` |
| 44 quadrics and the equation `∏_a (μ(s) − λ_a) = 0` of degree 34 | `2^{148.3}` |

- At τ = 17 there is no gain: `2^{144.2}` against `2^{144.1}`. The step from 44 to 45 equations
  is large in this model (`2^{3.7}`; the average step is `2^{2.65}`), so break-even is at
  `τ ≈ 20` here and at `τ ≈ 41` for an average step.
- At `τ ≥ 256` the gain is `≈ 2^{3.7}`. For OMPR with `256·N` independent targets we know no
  gain at all over one target for algebraic solvers. So **for large τ, OMPR⊕τ is easier than
  OMPR with `τN` targets, by a small factor**, in the best attacks we know. This is consistent
  with [UA] Prop. 8(a): for `q = 0` the gain is at most τ.
- Shifts in a `d`-dimensional `F`-subspace remove `d` equations and land with probability
  `τ/256^d`. For τ = 17 this is worse for every `d ≥ 2`.

Two reasons why 17 is safe here: `17 < 256`, so a shift list contains no affine line; and
`256/17` exceeds the worth of one equation.

### 4.2 Other structured lists [heuristic]

- *Subfield line.* `{λc : λ ∈ F₁₆}` has 16 points. `P(s) ∈ h + F₁₆·c` is 89 of the 90
  `F₁₆`-linear conditions of `P(s) = h`, for `P` as a quadratic map over `F₁₆` in 238 variables.
  One equation of 90 over `F₁₆` is worth less than one of 45 over `F`, and the descended system
  is no easier than the original. Over `F` the condition is `μ^{16} = μ`, degree 32, as in the
  last row of the table.
- *`F₂`-subspace of 16 shifts.* It removes 4 of 360 equations over `F₂`. Same conclusion.
- *Shifts of the form `P(u_a)` or `B(u_a, ·)`.* `P(s) = h + P(u_a)` is `Q_{u_a}(s + u_a) = h`: the
  translated problem again.

We found no list for which the candidates are jointly easier than τ independent targets, apart
from §4.1.

### 4.3 Calls and shifts together [heuristic]

An OMPR⊕τ adversary needs one forgery that no call paid for. Its calls give it preimages `s_i`
of chosen `y_i`, and through them the lines and planes of T1 and the span of §3.3.
- A call on a candidate of request `k` pays for request `k`. Its class contains no candidate of
  another request (uniform `h`), and by (E3) no second candidate of use.
- The plane `span(y, B(s, z₀))` or `span(y, B(s, s′))` contains a candidate of another request
  only if the cross term lies in a prescribed 2- or 3-dimensional space: probability
  `≤ τ·2^{−336}` per pair under Hypothesis X. The shifts are fixed before `h`, so they cannot be
  aimed at a cross term.
- Larger spans are MQ instances, as in §3.3, with τ right-hand sides instead of one.

So the calls do not combine with the shifts beyond the factor τ.

### 4.4 Verdict on attacks

- No attack on OMPR⊕17 that fails for OMPR. The one structural effect (C1) is `≤ 2^{3.7}` for
  any τ and absent at τ = 17.
- **Conjecture A6, restated.** For UOV and `τ ≤ 17`, the best attack on OMPR⊕τ(N, q) is the best
  attack on OMPR(τN, q). For `τ ≥ 256` this is false by the factor of C1 in the model, and the
  right comparison is with the map `π_c ∘ P`.

## 5. Where this leaves A6

| Route | Status |
|---|---|
| Reduction, black-box in the adversary and in `(P, D)` | impossible below `τ^{q+1}/2` ([OR] A4) |
| Reduction, black-box in the adversary, any use of `P` | impossible below `τ^{q+1}/4` unless OMPR^free fails (Theorem R) |
| Reduction using a combiner from the algebra of `P` | none found (§3); would break OMPR^free |
| Reduction that is not black-box in the adversary | open; `E₁` of PomFRIT is the known instance, with additive loss `Q₃·2^{−71}` |
| Attack separating OMPR⊕17 from OMPR | none found; C1 is below break-even (§4) |

The loss `τ^{q+1}` is thus an artefact only in the sense that no attack matches it. No proof
technique that treats the adversary as a black box removes it, unless UOV has a combiner that
would also break CT-UF^× ([OR] B2).

## 6. Lean and script

| Statement | Lean | File |
|---|---|---|
| `B(a, c·b) = c·B(a, b)`, `B(c·a, b) = c·B(a, b)` | `polar_smul_right`, `polar_smul_left` | `Spec/PqovShift.lean` |
| T1.1 kernel translation | `qmap_add_of_polar_eq_zero` | `Spec/PqovShift.lean` |
| T1.2 singular line | `preimage_line` | `Spec/PqovShift.lean` |
| (P3), T1.3 | `preimage_plane` | `Spec/PqovShift.lean` |
| T2 affine symmetries | `affine_symmetry` | `Spec/PqovShift.lean` |

All are for `qmap`, the model of pqov's public map that `lake exe spec_kats` checks against the
C++. On paper only: Theorem R (its inequality is [OR]'s `rewind_supermartingale`; the games, the
simulation and the bad events are not mechanized), T1.4–5, T2′, T4, C1.

`scripts/ompr-shift-algebra/shift_algebra_toy.py` (pure Python, about 8 s): the identities of §1
on toy keys over `F₁₆`, including good ⇔ `𝒪 ∩ K_s = 0`, oil translation and `rad B = 0`; the
infinitesimal symmetries; the chi-square test of Hypothesis X (40 000 samples by default; a
fourth argument sets the count); the cost table of §4.1.

## 7. Open

- A reduction OMPR ⇒ OMPR⊕17 that is not black-box in the adversary, or a proof that the natural
  non-black-box classes also fail.
- T3 is proved for additive maps (§8). Open there: pairs `(φ, Θ)` with `φ` not additive, beyond
  `φ(s) = γ(P(s))·s`; pairs with `A` not bijective and `T ≠ 0`; a sharper exceptional fraction
  (the bound `256^{−976}` comes from the matrices at distance 1 from the scalars).
- Hypothesis X for the real sampler; the hardness of `P|_{K_s}` (45 quadrics in 74 variables,
  no oil space).
- Theorem R with the lottery form of the assumption stated as a game, and its relation to
  OMPR^free.
- A multi-target algebraic attack on MQ would change §4.1 for independent targets as well; we
  know none.

## 8. Theorem T3: `P` has no symmetries but the scalings

This section proves Theorem T3 of §3.1. `q = 256`, `N = 119`, `M = 45`, `V = N − M = 74`.

### 8.1 Statements

**Key model.** Fix the oil matrix `O`. Let `W_𝒪` be the space of `M`-tuples of quadratic forms on
`F^N` that vanish on `𝒪`. Its dimension is `M·D`, `D = N(N+1)/2 − M(M+1)/2 = 6105`. The map
`(P1, P2) ↦ P` of pqov's key generation is a linear bijection onto `W_𝒪` ([UA] §1,
`oilSpace_iff_P3Pqov`). So with `P1`, `P2` uniform, **`P` is uniform on `W_𝒪`**. This is the
modelling step (AES-128-CTR of `pk_seed` as a random function); all probabilities below are over
`P`, for a fixed `O`.

**Definitions.** For a matrix `A` over `F` let `r(A) = min_{c ∈ F} rank(A − c·I)`. `A` is scalar
iff `r(A) = 0`. A *pair* is `(A, T)` with `P ∘ A = T ∘ P`. An *infinitesimal pair* is `(X, Y)`
with `B(s, Xs) = Y·P(s)` for all `s`.

**Theorem T3.** Each event has probability at most the stated bound.

| | Event | Bound |
|---|---|---|
| (G) | a pair `(A, T)`, `A ∈ GL_N(F)` not scalar, `T ∈ F^{M×M}` | `ε_lin ≤ 1.01·q^{−977}` |
| (L) | an infinitesimal pair `(X, Y)`, `X ∈ F^{N×N}` not scalar, `Y ∈ F^{M×M}` | `ε_lin` |
| (S) | a pair of `σ`-semilinear maps, `σ ≠ id`, `A` bijective | `ε_semi ≤ 7·q^{−97889}` |
| (I) | `F^N = R ⊕ R′`, `R, R′ ≠ 0`, `B(R, R′) = 0` | `ε_dec ≤ q^{−3049}` |
| (N) | `rad B ≠ 0`, or the values `B(s, u)` do not span `F^M` | `q^{−3211} + q^{−5987}` |

Outside these events (total `≤ q^{−976}`):
- every pair with `A` linear and invertible is `(λI, λ²I)`, `λ ≠ 0`;
- every infinitesimal pair is `(λI, 0)`;
- every pair `(φ, Θ)` of §3.1 (A) is a scaling.

The exact values are computed by `scripts/ompr-shift-algebra/t3_bound.py` (integer arithmetic).

**Group versus infinitesimal.** (L) is the equation of (G) for `A = I + εX`, `T = I + εY` over
the dual numbers `F[ε]/(ε²)` (Lean `infinitesimal_iff_first_order`). Neither implies the other.
- The pairs form the `F`-points of an algebraic group `G_P ⊂ GL_N × GL_M`. (L) says that its Lie
  algebra is the line `F·(I, 0)`. A finite group of pairs is invisible to the Lie algebra. Toy
  keys with `(N, M) = (5, 2)` over `F₄` show it: Lie algebra of dimension 1, 6 or 12 linear
  pairs (§8.7).
- Conversely a group scheme can have a large Lie algebra and few points (`μ₂`, `α₂` in
  characteristic 2). Toy keys with `(N, M) = (6, 2)` have a Lie algebra of dimension 3 and 6 or
  12 linear pairs. The scalings already show the effect: `λ ↦ (λI, λ²I)` has tangent vector
  `(I, 2I) = (I, 0)`. The target component of the Lie algebra does not see the scaling.

So both statements are proved, by the same method.

### 8.2 Symmetric tensors and the counting lemma

Let `Γ = Γ²(F^N)` be the symmetric tensors in `F^N ⊗ F^N`, of dimension `N(N+1)/2 = 7140`. It
is spanned by the squares `s ⊗ s`. Write `s·u = s ⊗ u + u ⊗ s`; these span the alternating
tensors `Alt ⊂ Γ`, and `s·s = 0`.
- An `M`-tuple of quadratic forms is a linear map `P : Γ → F^M`, with `P(s ⊗ s) = P(s)` and
  `P(s·u) = B(s, u)`.
- `P` vanishes on `𝒪` iff it vanishes on `Γ²(𝒪)`. So `W_𝒪 = Hom(Γ/Γ²(𝒪), F^M)`. Let
  `π : Γ → Γ/Γ²(𝒪)`; the target has dimension `D`.
- `P ∘ A = T ∘ P` iff `P ∘ Γ²(A) = T ∘ P`, where `Γ²(A)(s ⊗ s) = As ⊗ As`.
- `B(s, Xs) = Y·P(s)` iff `P ∘ D_X = Y ∘ P`, where `D_X = X ⊗ 1 + 1 ⊗ X`, so
  `D_X(s ⊗ s) = s·Xs`.

For a linear map `Φ` of `Γ` define

    δ(Φ) = min over λ in the algebraic closure of F of  rank( π ∘ (Φ − λ) ),

the rank being that of a map `Γ → Γ/Γ²(𝒪)` after extension of scalars.

**Lemma C (counting) [proved].** For every linear `Φ : Γ → Γ`,

    Pr_P[ ∃ T ∈ F^{M×M} : P ∘ Φ = T ∘ P ]  ≤  q^{−M·(δ(Φ) − M)}.

*Proof.* Fix `T`. Let `P ∈ W_𝒪` with `P ∘ Φ = T ∘ P`. Then `P(Φ^i x) = T^i P(x) = 0` for
`x ∈ Γ²(𝒪)`. So `P` factors through `U = Γ/𝒩`, `𝒩 = Σ_i Φ^i Γ²(𝒪)`. `U` is a module over `F[x]`,
`x` acting as `Φ`, and `P : U → (F^M, T)` is `F[x]`-linear. Such a map is determined by its values
on generators of `U`. By the structure theorem, the least number `g` of generators of `U` is the
number of invariant factors, which is `max_λ dim coker(Φ − λ | U)` over the algebraic closure.
This cokernel is `Γ/((Φ − λ)Γ + 𝒩)`, a quotient of `Γ/((Φ − λ)Γ + Γ²(𝒪))`, of dimension
`D − rank(π ∘ (Φ − λ))`. So `g ≤ D − δ(Φ)`. There are at most `q^{Mg}` maps `P` for each `T`,
and `q^{M²}` maps `T`. Divide by `|W_𝒪| = q^{MD}`. ∎

The lemma replaces the union over `T` by the minimum over `λ`: `λ` plays the role of an
eigenvalue of `T`. The cost of `T` is the term `−M` next to `δ(Φ)`.

### 8.3 Two rank lemmas

Both lemmas hold for every oil space `𝒪` of dimension `M`, every `λ` in the algebraic closure,
and in two cases: `Φ = Γ²(A)` with `A ∈ GL_N(F)` (*group*), and `Φ = D_X` with `X ∈ F^{N×N}`
(*Lie*). Write `Z` for `A` or `X`.

**Lemma E (eigen-probes) [proved].** Let `μ ∈ F` with `E = ker(Z − μ) ≠ 0`. Let
`e₀ = dim(E ∩ 𝒪)` and `e₁ = dim E − e₀`. Let `r′ = rank(μA − λ)` (group) or
`r′ = rank(X + μ − λ)` (Lie). Then for every `0 ≤ m ≤ e₁`, with `j = min(m, r′)`,

    rank(π ∘ (Φ − λ))  ≥  m·r′ − j(j+1)/2 + e₀·max(0, r′ − M − m).

*Proof.* For `k ∈ E` and any `u`: `Γ²(A)(k·u) = Ak·Au = μ·(k·Au)`, so
`(Φ − λ)(k·u) = k·(μA − λ)u`. In the Lie case `D_X(k·u) = Xk·u + k·Xu = k·(X + μ)u`. (The polar
identity behind this is Lean `symmetry_eigen`, `infinitesimal_eigen`.) Let `R` be the image of
`μA − λ`, resp. `X + μ − λ`, of dimension `r′`. Choose `K ⊂ E` with `K ∩ 𝒪 = 0`, `dim K = m`,
and `K₀ = E ∩ 𝒪`. The image of `π ∘ (Φ − λ)` contains `π(K·R + K₀·R)`, where `K·R` is the span
of the `k·ρ`.
- `Alt ∩ Γ²(𝒪) = Alt(𝒪)`, and `Alt ≅ Λ²(F^N)`. Choose `C′` with `F^N = K ⊕ 𝒪 ⊕ C′`. Then `Λ²`
  is the direct sum of `Λ²K`, `K∧𝒪`, `K∧C′`, `Λ²𝒪`, `𝒪∧C′`, `Λ²C′`.
- `K∧R` has no component in `Λ²𝒪`, `𝒪∧C′`, `Λ²C′`. So `π` is injective on `K·R`, and
  `dim K·R = m·r′ − j′(j′+1)/2` with `j′ = dim(K ∩ R) ≤ j`: the kernel of `K ⊗ R → Λ²` is the
  space of symmetric tensors of `K ∩ R`.
- The projection of `Λ²/Λ²𝒪` onto `𝒪∧C′ ≅ 𝒪 ⊗ C′` kills `K·R`. It maps `K₀·R` onto
  `K₀ ⊗ (R + K + 𝒪)/(K + 𝒪)`, of dimension `≥ e₀·(r′ − m − M)`. ∎

**Lemma F (free probes) [proved].** Let `r = r(Z) ≥ M + 2` and `ρ = ⌊(r − M)/2⌋`. Then
`rank(π ∘ (Φ − λ)) ≥ ρ(ρ+1)/2`.

*Proof.* *Existence.* There are `t_1..t_ρ` such that the `2ρ` vectors `t_j`, `Zt_j` are linearly
independent modulo `𝒪`. Choose them one by one. Let `𝒵 = 𝒪 + span(t_i, Zt_i : i < j)`, of
dimension `M + 2j`. A vector `t` is bad iff `t ∈ 𝒵` or `(Z − c)t ∈ 𝒵` for some `c ∈ F`. The set
`(Z − c)^{−1}(𝒵)` has dimension `≤ N − rank(Z − c) + dim 𝒵 ≤ N − r + M + 2j`. So there are at
most `q^{M+2j} + q^{N−r+M+2j+1} < q^N` bad vectors as long as `2j ≤ r − M − 2`.
*Rank.* Extend the `t_j` and `a_j = Zt_j` to a basis adapted to `𝒪`. The monomials in these
vectors are coordinates on `Γ/Γ²(𝒪)`.
- Group: `(Φ − λ)(t_j·t_{j′}) = a_j·a_{j′} − λ·t_j·t_{j′}` and
  `(Φ − λ)(t_j ⊗ t_j) = a_j ⊗ a_j − λ·t_j ⊗ t_j`. The monomial `a_j·a_{j′}`, `j ≤ j′`, occurs in
  one of these `ρ(ρ+1)/2` vectors only.
- Lie: `D_X(t_j·t_{j′}) = a_j·t_{j′} + t_j·a_{j′}` and `D_X(t_j ⊗ t_j) = t_j·a_j`. The monomial
  `t_j·a_{j′}`, `j ≤ j′`, occurs in one of them only. ∎

**The value of `r′`.** Let `r = r(Z) < N`, attained at `μ ∈ F`, so `dim E = N − r`. In the group
case `μ ≠ 0`, because `A` is invertible, and `μA − λ = μ(A − λ/μ)`. For `c ∈ F`,
`rank(Z − c) ≥ r` by definition. For `c ∉ F` of degree `d ≥ 2` over `F`, the eigenspaces of the
`d` conjugates of `c` have equal dimension and are independent of each other and of `E`. So
`dim ker(Z − c) ≤ r/2`. Hence

    r′ ≥ min(r, N − ⌊r/2⌋)   for every λ.

### 8.4 Proof of (G) and (L)

Let `δ_r` be the larger of the two bounds, in the worst case over the position of `𝒪`:
- Lemma E with `r′ = min(r, N − ⌊r/2⌋)`, minimized over `e₀ ∈ [max(0, N − r − V), min(M, N − r)]`
  and maximized over `m ≤ N − r − e₀`;
- Lemma F, `ρ(ρ+1)/2` with `ρ = ⌊(r − M)/2⌋`.

Then `δ(Γ²(A)) ≥ δ_r` and `δ(D_X) ≥ δ_r` for `r = r(A)`, `r = r(X)`. At most `q·R_r` matrices
have `r(·) = r`, where `R_r ≤ 1.01·q^{2Nr − r²}` is the number of `N × N` matrices of rank `r`.
By Lemma C,

    ε_lin = Σ_{r=1}^{N} q·R_r·q^{−M·(δ_r − M)}.

| `r` | 1 | 2 | 10 | 45 | 74 | 102 | 119 |
|---|---|---|---|---|---|---|---|
| `δ_r ≥` | 72 | 141 | 585 | 870 | 1305 | 406 | 703 |
| from | E | E | E | E | E | F | F |
| `log_q` of the count | 238 | 473 | 2281 | 8686 | 12137 | 13873 | 14162 |
| `log_q` of the term | −977 | −3847 | −22019 | −28439 | −44563 | −2372 | −15448 |

- The largest term is `r = 1`: transvections and pseudo-reflections `μI + wφᵀ`. There
  `δ_1 = 72`: `ker φ` contains a subspace `K` of dimension 73 with `K ∩ 𝒪 = 0`, and the tensors
  `k·w`, `k ∈ K`, span a space of dimension `≥ 72` modulo `Γ²(𝒪)`. Each gives `M` conditions on
  `P`, against `238 + M²` parameters for `(A, T)`.
- The second largest is `r = 102`, where the two lemmas meet: Lemma E gives the larger bound
  for `r ≤ 101`, Lemma F for `r ≥ 102`.

For `Z = μI` scalar: `T·P = μ²·P`, resp. `Y·P = 0`, on all values of `P`. These span `F^M`
outside (N), since `B(s, u) = P(s + u) + P(s) + P(u)`. So `T = μ²·I`, resp. `Y = 0`. ∎

**Lemma N [proved].** `Pr[rad B ≠ 0] ≤ q^{N − MV}`, and
`Pr[the values of B do not span F^M] ≤ q^{M − (D − V)}`.

*Proof.* For `a ≠ 0`, extend `a` to a basis adapted to `𝒪`. At least `V` of the vectors
`B(a, e)` are uniform and independent in `F^M`. Union over `a`. For the span: if `h·B = 0` with
`h ≠ 0`, the form `h·P` has no off-diagonal coefficient; there are `D − V` of them outside the
oil block, each uniform. Union over `h` up to scalars. ∎

This is T2′ with an explicit probability and without the condition on `δ(sk)`.

### 8.5 Characteristic 2

**`B(s, s) = 0`.** It gives the solution `(I, 0)` of (L): `B(s, λs) = 0` (Lean `polar_self`,
`scaling_infinitesimal`, `infinitesimal_add_scalar`). In odd characteristic the scalings have the
tangent vector `(I, 2I)`, and `B(s, s) = 2P(s)`. It is also why the squares `s ⊗ s` are not in
the span of the `s·u`: `P` is not determined by `B`. Lemma E uses only `B`. Lemma F and Lemma C
use `Γ`, which carries both.

**Theorem (S): Frobenius-semilinear maps [proved].** Let `σ ≠ id` be a power of the Frobenius
and `F₀` its fixed field, `|F₀| ≤ 16`. Let `A` be a `σ`-semilinear bijection of `F^N` and `T` a
`σ`-semilinear map of `F^M`. `Γ²(A)` is a `σ`-semilinear bijection of `Γ`. The map
`Θ : P ↦ T ∘ P ∘ Γ²(A)^{−1}` is `σ`-semilinear on `Hom_F(Γ, F^M)`, and `(A, T)` is a pair iff
`Θ(P) = P`. The fixed points of a semilinear map form an `F₀`-space whose `F₀`-independent
elements are `F`-independent. So there are at most `|F₀|^{7140·M} ≤ q^{3570·M}` fixed points, and

    ε_semi ≤ 7·q^{N² + M²}·q^{3570·M − 6105·M} = 7·q^{−97889}.  ∎

A key with a semilinear pair is, in suitable coordinates, defined over a subfield up to a linear
map on targets. The bound is small because that is a condition on every coefficient. No rank
lemma is needed: the fixed space of a semilinear map is at most half the space, while the fixed
space of a linear map can be all of it.

**Lemma I (indecomposable) [proved].** `Pr[∃ R, R′ ≠ 0 : F^N = R ⊕ R′, B(R, R′) = 0] ≤ ε_dec`.

*Proof.* Let `a = dim R ≤ N/2`, `b = N − a`. For fixed `(R, R′)` the event has probability
`q^{−M·ρ}`, `ρ = dim π(R·R′)`. As in Lemma E, with `a₀ = dim(R ∩ 𝒪)`, `a₁ = a − a₀`:
`ρ ≥ max(ab − M(M−1)/2, a₁·b + a₀·max(0, b − a₁ − M))`. There are at most
`[N choose a]_q·q^{ab}` pairs. The sum over `a` is `ε_dec`; its largest term is `a = 1`
(`ρ ≥ 73`). ∎

**Proposition A (additive and affine maps) [proved].** Assume none of (G), (S), (I), (N) occurs.
Let `φ(s) = A(s) + a` and `Θ(y) = T(y) + c` with `A`, `T` additive, and `P ∘ φ = Θ ∘ P`. If `A`
is bijective or `T` is injective, then `a = 0`, `c = 0`, `A = λ·I`, `T = λ²·I`.

*Proof.* Write `A = Σ_i A_i ∘ φ^i`, `T = Σ_i T_i ∘ φ^i` with `φ` the coordinatewise Frobenius,
`0 ≤ i < 8`, and `A_i`, `T_i` linear. Both sides of `P(As + a) = T(P(s)) + c` are polynomial
functions of `s` of degree `< 256` in each variable, so their coefficients agree.
- `P(As + a) = Σ_i P(A_iφ^i s) + Σ_{i<j} B(A_iφ^i s, A_jφ^j s) + B(As, a) + P(a)`.
- The monomials `s_a^{2^i}·s_b^{2^j}`, `i < j`, occur only in the cross terms; for `a = b` the
  exponent `2^i + 2^j` has two bits. So `B(A_i u, A_j w) = 0` for all `u`, `w` and `i ≠ j`.
- The monomials `(s_a s_b)^{2^i}`, `a < b`, give `B(A_i u, A_i w) = T_i·B^{σ^i}(u, w)`.
- *`T` injective implies `A` bijective.* If `A(z) = 0` then `T(B(z, u)) = B(Az, Au) = 0`, so
  `z ∈ rad B = 0` (Lean `symmetry_kernel_radical`, for `a = 0`; the polar identity
  `B(As, Au) = T(B(s, u))` holds for affine pairs too, as a second difference).
- *One component.* The images `R_i = im A_i` are pairwise `B`-orthogonal, and `Σ R_i = F^N`
  because `A` is onto. If two of them are nonzero, let `R′` be the sum of all but `R_1 ≠ 0`.
  Neither is `F^N`, since `rad B = 0`. A complement `R″ ⊂ R′` of `R_1` contradicts (I). So
  `A = A_i ∘ φ^i` with `A_i` invertible.
- *`T`.* For `j ≠ i`, `T_j·B^{σ^j}(u, w) = 0`, so `T_j = 0` by (N).
- *`a`.* The terms of degree `2^i` are `B(A_i φ^i s, a)`. So `a ∈ rad B = 0` and
  `c = P(a) = 0`.
- Now `(A, T)` is a `σ^i`-semilinear pair. By (S) `i = 0`, and by (G) it is a scaling. ∎

For `A` linear this is T2 again, with the hypothesis on `A` and `rad B` discharged.

### 8.6 What T3 says about reductions

- A public pair `(φ, Θ)` moves a preimage of `y` to a preimage of `Θ(y)`. For additive or
  affine pairs with `Θ` injective, `Θ(y) = λ²·y`: the pair is Lemma S of [OR] and nothing else.
  In particular `Θ` is never a translation `y ↦ y ⊕ Δ`, `Δ ≠ 0`, and never maps a class to
  another class. This closes the affine-symmetry route of [OR] §4.2 and §4.6 item 3, for all
  keys but a fraction `q^{−976}`.
- *Degenerate pairs.* If `T` is not injective, the pair sends every target into the proper
  subgroup `im T + c`. Example: `A s = ψ(s)·z₀` with `P(z₀) = 0`, `T = 0`. Such a pair gives
  preimages of points that the reduction did not choose. T3 does not classify them.
- *Non-additive `φ`.* `φ(s) = γ(P(s))·s` is a pair with `Θ(y) = γ(y)²·y`, inside classes. We know
  no other, and no proof that there is none. A pair with `φ` of higher degree is not a symmetry
  in the sense of [OR] A2; it is closer to a solver for the translated problem (§3.2).
- *Partial symmetries.* T3 is about identities on all of `F^N`. Maps that satisfy
  `P(φ(s)) = Θ(P(s))` on a subset only are the subject of §3.2–3.4.

### 8.7 Experiments, Lean, scripts

**Lean** (`Spec/PqovSymmetry.lean`, for `qmap`, `polar`; maps are only assumed additive).

| Statement | Lean |
|---|---|
| `B` symmetric, alternating, additive | `polar_comm`, `polar_self`, `polar_add_left/right` |
| the scalings and their tangent `(I, 0)` | `scaling_symmetry`, `scaling_infinitesimal` |
| a pair satisfies `B(As, Au) = T(B(s, u))` | `symmetry_polar` |
| `Ak = μk` ⟹ `μ·B(k, Au) = T(B(k, u))` (Lemma E, group) | `symmetry_eigen` |
| `T` injective ⟹ `ker A ⊂ rad B` | `symmetry_kernel_radical` |
| `B(s, Xu) + B(u, Xs) = Y(B(s, u))` | `infinitesimal_polar` |
| `Xk = μk` ⟹ `B(k, Xu + μu) = Y(B(k, u))` (Lemma E, Lie) | `infinitesimal_eigen` |
| `(X, Y)` infinitesimal iff `(X + c, Y)` is | `infinitesimal_add_scalar` |
| infinitesimal ⟺ first order of the pair `(1 + cX, 1 + cY)` | `infinitesimal_iff_first_order` |

On paper only: Lemma C, the rank counts of Lemmas E and F, the union bound, (S), Lemma I,
Lemma N and Proposition A. They need the structure theorem for `F[x]`-modules, exterior powers
and counts of matrices by rank; we did not mechanize them.

**Scripts** (`scripts/ompr-shift-algebra/`).
- `t3_bound.py`: the bounds of §8.1, exactly. With `-v`, `δ_r` and the term for every `r`.
  For toy parameters the bounds are above 1: the theorem says nothing there.
- `lie_fullsize.c`: (L) at the real size. A uniform key in normal form over `F₂₅₆`, `(N, M) =
  (119, 45)`; incremental elimination on the 321 300 equations in scrambled order. For seeds 1
  and 2 the rank reaches `16 185 = N² + M² − 1` after 16 185 equations (80 to 95 s, 262 MB). So
  for these two keys the infinitesimal pairs are exactly `F·(I, 0)`.
- `symmetry_toy.py` (pure Python, about 2 minutes), part A: (L) on toy keys over `F₄`, `F₁₆`, `F₂₅₆` up to `(N, M) = (30, 11)`:
  dimension 1 in every trial with `M ≥ 3`.
- Part B: the **full group** of linear and Frobenius-semilinear pairs over `F₄`, by exhaustive
  backtracking on the images of the basis (`T` is first restricted to the maps that preserve
  the fibre sizes of `P`).
  - 32 keys with `M ≥ 3`, `(N, M)` from `(6, 3)` to `(9, 4)`: exactly the three scalings, and no
    semilinear pair.
  - 12 keys with `M = 2`, `(5, 2)` and `(6, 2)`: 6 to 18 linear pairs, and for half of the keys
    as many semilinear ones. A pencil of two quadrics is not generic. The Lie algebra has
    dimension 1 for five of the six `(5, 2)` keys and dimension 3 for the `(6, 2)` keys.
- Part C: Lemmas E and F on structured matrices over `F₄` (rank 1 with image in `𝒪`, block
  matrices that preserve `𝒪`, diagonal, generic) and all `λ ∈ F₁₆`: the true rank of
  `π ∘ (Φ − λ)` is never below the bound.

### 8.8 Effect on [OR]

[OR] §4.2 (last consequence), §4.6 item 3 and §7 (last item) say that only the scalings are
known and that their uniqueness is unproved. With T3 the last item of [OR] §7 is settled for
additive and affine maps. A6 itself is unchanged: T3 removes one route to a reduction and gives
no attack.

## References

- [OR] `lean/docs/security/uov-open-reductions.md`. [UA] `lean/docs/security/uov-assumptions.md`.
  [UOS] `lean/docs/security/uov-open-structure.md`, and the references there ([Péb24a], [Beu21],
  [KPG99]).
