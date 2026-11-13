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
| T3 | Infinitesimal symmetries `B(s, Xs) = Y·P(s)`: only `(X, Y) ∈ F·(I, 0)` on toy keys. Conjecture: the only public pairs `(A, T)` with `P∘A = T∘P` are the scalings | experimental; conjecture | §3.1 |
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

**Which linear pairs exist?** The scalings `(λ·I, λ²·I)`. For others:
- *Infinitesimal pairs [experimental].* `A = I + εX`, `T = I + εY` with `ε² = 0` requires
  `B(s, Xs) = Y·P(s)` for all `s`. This is a linear system in `(X, Y)`: `N² + M²` unknowns,
  `M·N(N+1)/2` equations. `(I, 0)` is always a solution, because `B(s, s) = 0`. On toy UOV keys
  over `F₁₆` with `(N, M) = (8, 3), (10, 4), (12, 5)` the solution space has dimension 1 in every
  trial (script, part 2). At full size the system has 16 186 unknowns and 321 300 equations.
- *Frobenius.* `P(s^{2^i})^{2^{-i}}` is the map with the coefficients of `P` twisted by Frobenius.
  The coefficients are uniform bytes, so no twist fixes `P`.
- *Counting.* A pair `(A, T)` imposes `M·N(N+1)/2 = 321 300` conditions on `N² + M² = 16 186`
  parameters.

**Conjecture T3.** For uov-Ip keys, with overwhelming probability, the only linear `(A, T)` with
`A` invertible and `P ∘ A = T ∘ P` are the scalings. We did not prove it ([OR] §7, last item,
stays open); a proof by a union bound over conjugacy classes of `A` looks feasible.

**Consequence for target re-randomization.** With T2 and T3, a reduction can re-randomize a
target only inside its class. It cannot produce two targets with a prescribed difference
`δ_a ⊕ δ_b` ([OR] §4.6 item 3). The embedding `h = μ·t ⊕ c` aligns a second shift only if
`δ_a ⊕ δ_b ∈ μ·t ⊕ μ′·t′`, the event (E3).

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
- Conjecture T3 (no symmetries but scalings), by a union bound.
- Hypothesis X for the real sampler; the hardness of `P|_{K_s}` (45 quadrics in 74 variables,
  no oil space).
- Theorem R with the lottery form of the assumption stated as a game, and its relation to
  OMPR^free.
- A multi-target algebraic attack on MQ would change §4.1 for independent targets as well; we
  know none.

## References

- [OR] `lean/docs/security/uov-open-reductions.md`. [UA] `lean/docs/security/uov-assumptions.md`.
  [UOS] `lean/docs/security/uov-open-structure.md`, and the references there ([Péb24a], [Beu21],
  [KPG99]).
