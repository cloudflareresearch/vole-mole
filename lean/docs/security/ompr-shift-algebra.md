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
| R | **A4 holds for UOV itself, for every reduction that is black-box in the adversary only.** Such a reduction `R` may use `pk` and the algebra of `P` in any way, and may rewind. Against one explicit adversary it wins OMPR with probability `≤ 2·τ^{−(q+1)} + Adv^{free}_{UOV}(M) + V⁴·2^{−343}`, where `M` is an OMPR^free adversary ([OR] §3.1) of about `R`'s running time. So: a reduction of this kind with loss below `τ^{q+1}/4` **is** an attack on OMPR^free, i.e. it contains a combiner across classes | proved; Lean (`thmR`: the games, the simulation, the lottery and the accounting; the bad events `badPr ≤ V⁴·2^{−343}`: `badPr_le_V4`; the statement as here: `thmR_V4`; Corollary R′: `corR'`) | §2 |
| T1 | Toolbox: polar form, kernel translation, the preimage line through a singular vector (`D(0)` gives one), `P` on the span of two preimages | proved, Lean (`qmap_add_of_polar_eq_zero`, `preimage_line`, `preimage_plane`) | §1 |
| T2 | An affine symmetry `P(As + a) = T(P(s)) + c` shifts targets only by `c = P(a)` with `a ⊥ im A`. If `A` is onto and `rad B = 0`, then `a = 0`, `c = 0`. `rad B = 0` for every key with `δ < 1` and `v ↦ L_v` injective | proved; Lean (`affine_symmetry`; with `rad B = 0`: `no_translation`; `rad B = 0` with its count over pqov's keys: `pr_not_radTriv`, `pr_translation_le`) | §3.1 |
| T3 | **`P` has no symmetries but the scalings.** For every oil space and all but a fraction `≤ 256^{−976} < 2^{−7800}` of the keys: (G) the only linear pairs `(A, T)`, `A` invertible, with `P∘A = T∘P` are `(λI, λ²I)`; (L) the only infinitesimal pairs `B(s, Xs) = Y·P(s)` are `F·(I, 0)`; (S, A) the same for Frobenius-semilinear and for all additive bijections, with an affine part. So a symmetry pair moves a target only inside its class. Checked: (L) at full size on two keys; the full group on toy keys over `F₄` | proved (model: `P1`, `P2` uniform); **Lean (`t3`, same model, any `O`): (G), (L), (S) and affine pairs with one Frobenius component, all keys but `256^{−128}`**, by another route (§8.7); identities Lean (`symmetry_polar`, `symmetry_eigen`, `infinitesimal_polar`, …); Lean for any `O`, `P1` and uniform `P2`: no affine pair with `A` onto translates targets, all keys but `256^{−1951} + 256^{−3285}` (`pr_translation_le`), and `(λI, T)` forces `T = λ²I` (`scaling_target`); paper only: the bound `256^{−976}` and (A) for sums of several Frobenius components; experimental | §3.1, §8 |
| T4 | A translator for one fixed shift `Δ₀` is worth exactly one equation: `UOV(119, 45) ≤ UOV-projected(119, 44) ∘ Tr_{Δ₀}`, and `Tr_{Δ₀} ≤ UOV(119, 45)`. In the cost model the gap is `≈ 2^{3.7}`. For uniform shifts translation is the UOV problem ([OR] A3) | proved; figure: estimate | §3.2 |
| T5 | The linear span of known preimages gives targets `Σ α_i² y_i + Σ α_iα_j B(s_i, s_j)`. The reduction controls the `y_i`, not the cross terms. On toy keys the cross term of two sampler answers is uniform. With the oil space, translation is linear algebra; without it, every route we checked is an MQ instance or a class | proved identities; heuristic conclusion; experimental | §3.3–3.4 |
| C1 | **Collinear shifts trade one equation for a landing.** With shifts `λ_a·c`, a forgery is a solution of 44 of the 45 equations whose last coordinate `μ(s)` is one of τ values out of 256. In a hybrid solver this is the direct attack with one equation dropped from the solver and τ guesses saved. Its cost is `τ*/τ` times the direct cost, `τ* = 256·U/H` (`H`: direct; `U`: one solution of the 44 equations). Reference model (XL with Wiedemann, after Thomae–Wolf): `H = 2^{140.3}`, C1 at τ = 17 costs `2^{142.4}`, `τ* ≈ 72`. Over ten model variants `τ*` runs from 11 to 72 and C1 at 17 from `2^{0.7}` below to `2^{2.1}` above the direct attack. For `q = 0` no attack gains more than `τ = 2^{4.1}`. On toy keys the degrees, the call counts, the landing rate `τ/q` and the break-even point are as the model predicts | reduction proved; costs: estimate; experimental | §4.1 |
| C2 | No other structured shift list (subfield lines, `F₂`-subspaces, higher-dimensional `F`-subspaces, curves), and no use of the `D` oracle together with the shifts, gives more than the counting factor τ. One call serves two requests only with probability `≤ 255·τ²·256^{−45}` per pair | heuristic, estimate; last part proved | §4.2–4.3 |
| C3 | **A singular vector lands for free, without shifts.** For `P(z) = 0` (`z₀ = D(0)`: one call) and any `c ≠ 0`, a preimage of any `t` is a zero of 44 quadrics on a 74-dimensional space: the landing on the line `t + F·c` is solved by `s ↦ s + λz`. This is the saving of Thomae–Wolf by another route. The two do not stack at `(119, 45)`, and neither stacks with C1 beyond `τ*/τ` | proved; non-stacking: count of dimensions; experimental (identity) | §4.3 |

**Answer.** We found neither a polynomial-loss reduction nor an attack at τ = 17.
- *Reductions.* The obstacle A4 is not an artefact of the generic model. For UOV, a better
  adversary-black-box reduction exists only if OMPR^free fails (R). The algebraic tools at hand
  (T1–T5) give no combiner across classes. What remains is a reduction that is not black-box in
  the adversary.
- *Attacks.* The one structural use of the shifts is C1. PomFRIT does not choose the shifts: they
  are the tree prefixes of a forger, so collinear lists are allowed (§4). At τ = 17, C1 costs
  `2^{2.1}` more than the direct attack in the reference model. It is `2^{0.7}` cheaper in the
  most favourable variant we tried, and it can never be more than `2^{4.1}` cheaper. Conjecture
  A6 of [OR] should be read "up to the factor `τ/τ*` of §4.1" for `τ > τ*`.
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

**Theorem R [proved; Lean `thmR_V4`, §2.4].** Let `τ ≥ 7`, `q ≥ 1`. Let `R` be as above, with `c` calls to `D` and `T`
messages to `A**_D`. Then there is an OMPR^free adversary `M` with

    Pr[R^{A**_D} wins OMPR(n, c)]  ≤  2·τ^{−(q+1)} + Adv^{free}_{UOV}(M) + V⁴·2^{−343},

where `V = n + c + (τ + 1)(q + 1)·T`. `M` runs `R` once, requests at most `n + q·T` targets,
makes at most `c + (q + 1)·T` calls, and does `O(V)` further work (lazy sampling, checks).

**Corollary R′ [proved; Lean `corR'` from the loss inequality, §2.4].** Suppose a reduction of this class has loss `L`: for every adversary
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

Lean (`badPr_le`, `badNum_le`; §2.4): each value is charged when it is drawn. The union runs over
every shift list that `R` requests, not only the lists of completed runs, so it needs the bound
`T` on the messages: at most `NT = n + q·T` targets and `NL = (q + 1)·T` lists are drawn. The
exact bound is `(NT·cT + NL·cL)/256^{45}` (§2.4). Its main term is
`2·τ²·256²·NL·NT²·2^{−360}`, and it is at most `V⁴·2^{−343}` when `q ≥ 1`.

*Step 2: the lottery.* Call a value *useful* if it lies in the class of a target revealed so
far. When a run `H` is completed, let `b_k(H)` be the first shift `a` of request `k` whose
candidate `h_k ⊕ δ_{k,a}` is useful, if there is one. It is a function of the values revealed
before `a(H)` is drawn, and `a(H)` is then uniform. Call the forgery of request `k` *counted* if
`a_k = b_k(H)`. Let `X_i` be the number of counted forgeries of the `i`-th completed run, and
`Z_j = Σ_{i ≤ j}(X_i − q)`.
- Given the past, `X_i` is dominated by `Bin(q + 1, 1/τ)`. This holds with no condition on the bad
  events: each request has at most one winning shift by definition.
- So, as in [OR] A4, steps 3–4 (Lean `lottery_sum`, `rewind_supermartingale`, `pot_complete`;
  Ville's inequality is `potential_le`):

      Pr[∃ j ≥ 1 : Z_j ≥ 1] ≤ 2·τ^{−(q+1)}          (Lean `lottery_le`).

- By (E3) a forgery that is useful when drawn is counted. By (E2) a candidate that is not useful
  when its run is completed never lies in the class of a target revealed later.

*Step 3: accounting.* Suppose `R` wins and `Z_K ≤ 0`.
- `M` outputs preimages of `c + 1 + K·q` distinct indices.
- Its calls are `R`'s `c` calls and the `K(q + 1)` candidate calls. By (E1) a call is charged to
  at most one index. A candidate call is charged only if its forgery is counted (step 2).
- So at most `c + Σ X_i = c + K·q + Z_K ≤ c + K·q` indices are charged, and `M` wins
  (Lean `free_of_win`, with `lottery_count`).

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

### 2.4 Lean

`VoleMole/Assumptions/TheoremR.lean`; the bad events in `VoleMole/Assumptions/TheoremRBad.lean`;
non-vacuity in `VoleMole/Audit/TheoremR.lean`. Generic in the trapdoor (`UOV.Trapdoor`) and in the
class relation `cls` (any equivalence; for UOV `Links.uovCls`); the bad-event bound is for targets
in `F^m` up to nonzero scalars.

**The model.**
- *OMPR^free*: `advOMPRFree tr cls nT Q` (`fImpl`, `freeExp`, `FreeWin`). The oracles of `advOMPR`
  (`OneMore.specB`): world, labelled targets on demand, `D`. The challenger logs the calls. The
  win is the form of [OR] §3.1's definition: one preimage of a nonzero target with no call in its
  class, at most `nT` targets and `Q` calls. Sanity: `not_freeWin_of_called`.
- *The reduction*: an oracle computation over `specRed`, the oracles of the OMPR experiment plus
  `A**_D` as a stateless next-message function: the shift list after a prefix `h_1..h_{k−1}`, the
  junk targets of a run `H`, the output of `H` given answers to the junk queries. `R` gets `pk`
  and rewinds by choosing its queries.
- *The experiment*: `redExp tr n R` (handler `μR` over the atomic operations `Op`; `prog` maps
  `R`'s queries to them). `A**_D` is §2.1: `S_k` and `a` are values of a lazy random oracle that
  `R` cannot query, junk is drawn lazily, answers are checked with `P` (`valid`), forgeries are
  `D` on the candidates (`cands`). The output of a completed run is memoized; it is a function
  of `H`. Targets are on demand, as in `advOMPR`.
- *`M`*: `redM cls tr.IsPre n R` (handler `μM`, final step `pick`), as in §2.2. It outputs one
  claim whose target has no call in its class.

**The statement** (`thmR`). For `τ ≥ 7`, `q ≥ 1`, `cls` an equivalence, every `R` and all
`c, J, K₀`:

    Pr[R wins OMPR(n, c) in redExp, with ≤ J junk targets drawn and ≤ K₀ runs completed]
      ≤ 2/τ^{q+1} + advOMPRFree(M; n + J, c + (q + 1)·K₀) + badPr.

- `badPr` is the probability, in `M`'s run, of the bad events that the proof uses: a new target
  is `0`, or in the class of an earlier target, or in the class of an earlier candidate that was
  not counted (`MSt.addT`); a forgery is useful but not counted (`MSt.complete`). They are
  implied by (E1), (E2), (E3), with (E2) read for every target revealed on demand, challenge or
  junk.
- For `R` with `T` messages to `A**_D`: `J ≤ q·T` and `K₀ ≤ T` (`jointExp_counts`).

**With the bad events bounded** (`Assumptions/TheoremRBad.lean`). For targets in `F^m` with the
class relation "equal up to a nonzero scalar" (`scls`; `Links.uovCls` is `scls GF256 45`) and a
reduction with at most `T` messages to `A**_D` (`IsQueryBoundP` on the messages; rewinding
included, every message counts):

    badPr ≤ (NT·cT + NL·cL) / |F|^m,      NT = n + q·T,  NL = (q + 1)·T,  Q = |F|,
    cT = 1 + NT·Q + NL·Q + NL·τ²·(Q²·NT + Q),     cL = τ²·(1 + Q²·NT²)          (badPr_le)

and at `GF(256)^{45}`, for `q ≥ 1`, this is at most `V⁴·2^{−343}` (`badNum_le`, `badPr_le_V4`).
So, with no term left implicit (`thmR_num`, `thmR_V4`):

    Pr[R wins OMPR(n, c)] ≤ 2/τ^{q+1} + advOMPRFree(M; n + q·T, c + (q + 1)·T) + V⁴·2^{−343}.

Corollary R′ (`corR'`): if `R` wins with probability `≥ w/L`, where `w` is the OMPR⊕τ advantage of
`A**_D`, and `4L ≤ τ^{q+1}`, then `w/L ≤ 1/(2L) + Adv^{free}(M) + V⁴·2^{−343}`.

The proof of the bound:
- The bad states (`Ebad`): `M`'s flag, or (E3) as a property of the state (`E3`): a cached list
  has two shifts whose difference is `0` or `μ·w − μ'·w'` for targets `w`, `w'` drawn so far.
- A new target makes the state bad only if it lies in `tgtBad` (`draw_mem`): `0`, the classes of
  the targets and of the uncharged calls, and for each cached list and pair of shifts the
  `≤ Q²·|tl| + Q` points that would complete (E3).
- A new list makes the state bad only if two of its shifts differ by an element of `lstBad`
  (`lst_mem`); the difference of two coordinates of a uniform function is uniform
  (`pr_diff_mem`).
- A completion sets `bad` only if (E3) held for the cached lists of the run (`complete_E3`),
  which `prog` queries just before (`lsts_step`).
- The run (`bad_run`): induction on the reduction with the message budget, the invariant `Ival`
  and the potential `Bnd`; one message costs at most `q` target draws and `q + 1` list draws
  (`msg_step`).

**Proved in Lean.**

| Step of §2.2 | Lean |
|---|---|
| The simulation is exact | `proj_step`, `redExp_eqd`; `collapseJ`, `freeExp_redM` |
| Invariant of `M`'s run | `Inv`, `jImpl_inv`, `jointExp_inv` |
| Step 2, one run: `Σ_a θ^{X(a)} ≤ (τ − 1 + θ)^{q+1}` | `lottery_sum` |
| Step 2, the potential `θ^{Z−1}` is a supermartingale | `pot_complete`, `lot_step` |
| Ville's inequality, for a stateful handler | `potential_le` |
| `Pr[∃ j : Z_j ≥ 1] ≤ 2·τ^{−(q+1)}` | `lottery_le` |
| Step 3 | `free_of_win` |
| Theorem R | `thmR` |
| Step 1: `badPr ≤ (NT·cT + NL·cL)/|F|^m`, and `≤ V⁴·2^{−343}` at `GF(256)^{45}` | `badPr_le`, `badPr_le_V4` |
| Theorem R with every term explicit | `thmR_num`, `thmR_V4` |
| Corollary R′ | `corR'` |

**Not mechanized.**
- The claim that `A**_D` wins OMPR⊕τ except when `D` fails (`w ≥ 1 − (2q + 1)·δ^{255}` in
  Corollary R′): `A**_D` is built into `redExp`, not an adversary of a Lean OMPR⊕τ game. `corR'`
  takes `w` as a parameter.

**Corrections found by the formalization.**
- *The lottery was conditioned on the bad events.* The first version of step 2 let `X_i` count the
  useful forgeries and assumed that no bad event occurs. Then `X_i` is dominated by a binomial
  only outside (E3), and a supermartingale cannot be conditioned on an event of the whole run.
  Step 2 now counts a forgery only if its shift is the *first* useful one. This lottery is fair
  unconditionally. (E3) is used once, in step 3: a useful forgery is counted.
- *"`b_k(H)` is determined when `R` sends `h_k`" is not needed.* `b_k(H)` is read when the run is
  completed, before `a(H)` is drawn. (E2) is used only for targets revealed after that.
- *The union bound of step 1 runs over every list that `R` requests.* A list is a fresh value
  when `R` first asks for it, whether or not a run that uses it is completed later, so the count
  of lists is by the messages `T`, not by the completed runs. The note's `V` already counts
  `(τ + 1)(q + 1)·T` values; the mechanized bound confirms `V⁴·2^{−343}` (with room `2^{17}`),
  using `q ≥ 1`.
- The statement and the bound are unchanged.

**Non-vacuity** (`Audit/TheoremR.lean`).
- `Links.uovCls` is an equivalence (`uovCls_equiv`); the theorem is instantiated at PomFRIT's
  trapdoor with τ = 17.
- Every OMPR adversary is a reduction of the class (`liftRed`), and in `redExp` it wins with
  probability exactly `advOMPR` (`redExp_liftRed`, from `liftB_eqd`). So the experiment contains
  the OMPR game of `Assumptions/UOV.lean`.
- The guessing reduction of [UA] Prop. 8(a) is a term of the class (`guessRed`): one run,
  `h_k = t_k − δ_{k,g_k}`, `q` calls for the junk. Its success probability is not mechanized.
- It sends `q + 3` messages to `A**_D` (`guessR_bound`), so `thmR_V4` applies to it with every
  term explicit; `uovCls_eq_scls` puts UOV's class relation in the form of `badPr_le`.

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
- *Lean* (`Assumptions/SymmetryCount.lean`), over pqov's keys `pqovKey O P1 P2` with any `O` and
  `P1` and a uniform `P2`. The proof above without `δ(sk)`: for `a = (v, 0) + ι(x)` in the
  radical, `L_v = 0`, and if `v = 0` then `Σ_j x_j·S_k[i][j] = 0` for all `k, i` (`rad_coords`).
  Both are kernels of surjective maps of the uniform `S`, so `rad B ≠ 0` on `F^{119}` has
  probability `≤ 256^{74−2025} + 256^{45−3330}` (`pr_not_radTriv`). With T2 (`no_translation`):
  a pair with `A` homogeneous and onto and `c ≠ 0` exists with probability
  `≤ 256^{−1951} + 256^{−3285}` (`pr_translation_le`).

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

*Lean.* `t3` (`Assumptions/SymmetryT3.lean`): for every `O`, over uniform `P1` and `P2`, all keys
but a fraction `≤ 256^{−128}` satisfy (G), (L), (S) and (A) for maps `A`, `T` that are
`σ`-semilinear for one `σ`, with the affine part and with `A` bijective or `T` injective. The
proof is not the one of §8.2–8.4; see §8.7. `P1` must be random: for `P1 = 0` the key has
non-scalar pairs for every `P2` (`not_t3Good_p1_zero`).

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

**Which shifts PomFRIT has [from the code].** None of its own.
- The honest Client has one mask `r` per issuance, squeezed from `XOF_seed`
  (`src/pomfrit/pomfrit.cpp:149-160`) and committed as the witness prefix of all 17 trees
  (`:167`, `src/voleith.hpp:234-238`). Its target is `h ⊕ r`: one shift.
- 17 is the number of VOLEitH trees (`src/pomfrit/redeem.hpp:74`). The shift list of A-OMPR⊕17
  appears only in the reduction of U2 (`pomfrit.md` §6.2): it is the list of prefixes `r^{(i)}` of
  the alive trees of a *forger's* commitment (`pomfrit.md` §5, step 4). The forger sets the
  corrections between trees, so it sets the `r^{(i)}` freely. They are fixed before `h`, because
  `chal1` and the prefix correction enter `H_T` (`pomfrit.cpp:96-111`).
- So the list is the adversary's: any 17 points, collinear ones included. No choice of PomFRIT's
  makes it non-collinear, and pqov plays no part (it sees one target per `derive_preimage`).
- A PomFRIT forger pays for distinct prefixes, on top of the algebra. To complete a proof with the
  prefix of a group of trees of total width `w` it needs at least `2^{128−w}` `H₂³` queries
  (`pomfrit.md` §5, steps 4–7). For 17 distinct prefixes this is `2^{120}` or `2^{121}`; for two
  groups, `2^{65}` and `2^{71}`. The cost adds to the cost of §4.1 and is below it, so it does not
  rule C1 out. It is absent from A-OMPR⊕17 itself.

### 4.1 Collinear shifts

**Proposition C1 [proved].** Let request `k` have the shifts `λ_a·c`, `a ≤ τ`, with `c ≠ 0` and
distinct `λ_a ∈ F`. Let `π_c : F^M → F^M/F·c`. Then `s` is a forgery for request `k` iff

    π_c(P(s)) = π_c(h_k)   and   μ(s) ∈ {λ_a},   where P(s) = h_k + μ(s)·c.

- The first condition is the preimage problem for `π_c ∘ P`: 44 quadrics in 119 variables,
  vanishing on `𝒪` (dimension 45).
- If `{λ_a} = F`, which needs `τ ≥ 256`, the second condition is void: OMPR⊕256(N, 0) is at
  most as hard as that 44-equation problem. This is [OR] A2 item 2 read as an attack.
- If `τ < 256`, a solution of the first condition lands with probability `τ/256` (heuristically,
  for a solver that returns an unstructured solution; measured below).

**C1 inside a hybrid solver.** Write `S(n, m)` for the cost of solving `m` quadrics in `n < m`
variables, and `q = 256`. Both attacks fix variables until `n = M − j` are left; `j` of the fixed
values are guesses.

    direct:     H     = min_j  q^j      · S(M − j, M)        one solution of M equations
    C1 at τ:    U·q/τ = min_j  q^j / τ  · S(M − j, M − 1)    U: one solution of the M − 1 equations

- For the same `j` the two solvers see the same number of variables. The `M − 1` equations have
  a solution `q` times as often as the `M` equations, and a solution is a forgery with
  probability `τ/q`. So C1 needs τ times fewer calls, and each call runs a solver with one
  equation less.
- **Break-even.** C1 at τ costs `τ*/τ` times the direct attack, with `τ* = q·U/H = 2^{8 − step}`,
  `step = log₂(H/U)`. C1 gains iff `τ > τ*`, and the gain `τ/τ*` is at most τ.
- In XL the cost `S` depends on `(n, m)` only through the operating degree `D`. Where
  `D(n, M − 1) = D(n, M)` the gain is the full factor τ. Where the degree goes up by one, the
  loss is far more than `τ = 17`. So `τ*` is decided by the grid of degrees near the optimum, and
  it moves in jumps with the parameters.

**Costs [estimate].** `scripts/ompr-shift-algebra/c1_experiments.py estimates`, in `log₂` field
multiplications over `F₂₅₆` for `(N, M) = (119, 45)`; add 7.1 for bit operations. Formulas are
quoted from memory.
- Solver models. *XL*: Wiedemann on the Macaulay matrix, `3·T²·binom(n+2, 2)`, `T = binom(n+D,
  D)`, `D` the first degree with a non-positive coefficient in `(1−t²)^m/(1−t)^{n+1}`. This is the
  model of [UOS] B.5 and, as we remember it, of the UOV specification. *F5, ω*:
  `binom(n+d−1, d)^ω` with `d` from `(1−t²)^m/(1−t)^n` [BFP09].
- Preprocessing of the underdetermined system. *Plain*: fix `N − m` variables. *TW*: Thomae–Wolf
  [TW12] with the guesses of Furue–Nakamura–Takagi [FNT21]: after `k` guesses, `m − a` equations
  in `m − k − a` variables, `a = ⌊(N−k)/(m−k)⌋ − 1`. At `(119, 45)` and `(119, 44)`, `a = 1` for
  `k = 0`. Hashimoto's refinement [Has21] and the crossbred algorithm are not modelled.

| Solver | Prep. | Direct `H` | `U` (44 eqs) | step | `τ*` | C1 at τ = 17 | C1(17) / direct |
|---|---|---|---|---|---|---|---|
| XL | plain | 144.1 | 140.3 | 3.74 | 19.1 | 144.3 | `2^{+0.17}` |
| XL | TW | **140.3** | 138.5 | 1.84 | 71.5 | **142.4** | `2^{+2.07}` |
| F5, ω = 2 | plain | 124.5 | 120.9 | 3.61 | 21.0 | 124.9 | `2^{+0.30}` |
| F5, ω = 2 | TW | 120.9 | 119.1 | 1.84 | 71.5 | 123.0 | `2^{+2.07}` |
| F5, ω = 2.37 | plain | 143.4 | 139.4 | 4.00 | 16.0 | 143.3 | `2^{−0.09}` |
| F5, ω = 2.37 | TW | 139.4 | 136.9 | 2.46 | 46.4 | 140.8 | `2^{+1.45}` |
| F5, ω = 2.81 | plain | 162.3 | 159.4 | 2.88 | 34.7 | 163.4 | `2^{+1.03}` |
| F5, ω = 2.81 | TW | 159.4 | 154.9 | 4.59 | 10.6 | 158.8 | `2^{−0.68}` |

XL with the criterion "coefficient `≤ 1`" (which is what plain XL needs, see the experiments)
gives the same figures as XL. The row in bold is the reference: it is the cheapest realistic
attack, and for `(112, 44)` it gives `2^{138.5}` multiplications, `2^{145.6}` bit operations,
which matches the direct-attack figure we remember from the UOV specification (`≈ 2^{145}`).

- **Direct forgery with Thomae–Wolf costs `2^{140.3}`**, not the `2^{144.1}` of [UOS] B.5, which
  applies no variable reduction. The best forgery attack removes one equation whether or not
  there are shifts.
- **τ = 17 in the reference model: C1 costs `2^{142.4}` against `2^{140.3}`.** It is `2^{2.1}`
  dearer. Break-even is `τ* ≈ 72`.
- **Sensitivity.** `τ* = 2^{8 − step}`, and the step is a property of the degree grid. In the XL
  model it alternates with the parity of the number of equations: 1.84 and 3.74 for 44 and 45
  (script: `m = 36..46`), up to 4.38 for larger `m`. So one equation more or less in the
  preprocessing moves `τ*` between 72 and 19. Its mean over `m = 36..55` is 2.66 (`τ* ≈ 40`); for
  the F5 models the means give `τ*` = 42, 33, 25.
  - Over the eight rows, `τ*` runs from 10.6 to 71.5.
  - C1 at τ = 17 is dearer than the direct attack in six rows, among them all rows of XL and of
    F5 with ω = 2. It is cheaper in two rows. F5 with ω = 2.37, plain: by `2^{0.09}`; but the
    same solver with TW is `2^{4}` cheaper, and there C1 is `2^{1.45}` dearer. F5 with ω = 2.81
    and TW: by `2^{0.68}`; this solver costs `2^{19}` more than the reference.
  - The claim of the earlier version of this note, "`2^{144.2}` against `2^{144.1}`", was the
    row XL/plain. Its margin of `2^{0.17}` is not meaningful. The margin with TW is.
- **Bound that needs no model.** For `q = 0`, OMPR⊕τ loses at most τ against OMPR ([UA]
  Prop. 8(a)). So C1, or any other use of 17 shifts, gains at most `2^{4.09}` on one forgery.
- At `τ ≥ 256` the landing is free and the gain is the step: `2^{1.8}` in the reference model. For
  OMPR with `256·N` independent targets we know no gain at all over one target for algebraic
  solvers. So **for `τ > τ*`, OMPR⊕τ is easier than OMPR with `τN` targets, by the factor
  `τ/τ*`**, in the best attacks we know.
- Shifts in a `d`-dimensional `F`-subspace remove `d` equations and land with probability
  `τ/256^d`. For τ = 17 this is worse for every `d ≥ 2`.
- The landing as an equation, `∏_a (μ(s) − λ_a) = 0` of degree 34 next to the 44 quadrics, is
  worse than both: `2^{148.3}` (`shift_algebra_toy.py`, part 4; XL, plain).

**Experiments [experimental].** `c1_experiments.py toy` builds `c1_toy.c`: toy UOV keys over `F₁₆`
and `F₂₅₆`, the direct attack and C1 by XL with dense elimination, every solution checked
against the public map. Seven keys, 49 pairs (attack, `j`).
- *Degrees.* The smallest degree at which XL decides a system is the model's in all 49 cases, for
  the 45-type and for the projected 44-type systems alike, with the criterion "coefficient
  `≤ 1`": with corank one XL still isolates one candidate point. This differs from "`≤ 0`" in 4
  cases, all with `m = n + 1` or `n ≤ 3`. The projection `π_c` does not disturb semi-regularity.
- *Calls.* Solutions per call are `q^{−j}` (direct) and `q^{−(j−1)}` (C1): e.g. 773 found for
  762.0 expected, 752 for 767.6, 733 for 768.0; C1: 679 for 672.0, 748 for 767.6, 770 for 768.0.
- *Landing.* `μ` is uniform over the solutions of the projected system. Pooled chi-square over
  the 16 batches with `q = 16`: 268.8 on 240 degrees of freedom; 22 further keys: 364.9 on 330.
  For `q = 256`: 229.8, 263.9, 231.7 on 255. Landings in a fixed list of 17 of 256 values: 31,
  30, 4 for 23.4, 27.2, 3.9 expected. Lists of 1, 2, 4, 8 of 16 values behave the same.
- *Break-even.* Work per forgery is multiplications per solution, times `q/τ` for C1. Where a
  batch found fewer than 30 solutions it is multiplications per call times `q^j` (the call
  counts above justify this).

| `q` | `(N, M)` | Direct: best `j`, `D` | C1: best `j`, `D` | `τ*` measured | `τ*`, `T^{2.81}` | `τ*`, `3T²·binom(n+2,2)` |
|---|---|---|---|---|---|---|
| 16 | (21, 8) | 4, 3 | 4, 3 | 0.78 | 1.00 | 1.00 |
| 16 | (24, 9) | 3, 4 | 5, 3 | 1.90 | 2.11 | 3.81 |
| 16 | (26, 10) | 5, 3 | 4, 4 | 3.41 | 2.56 | 1.17 |
| 16 | (29, 11) | 4, 4 | 6, 3 | 1.58 | 1.75 | 4.30 |
| 256 | (16, 6) | 2, 4 | 2, 5 | 4.96 | 5.22 | 3.24 |
| 256 | (24, 9) | 2, 5 | 3, 5 | 56.9 | 56.3 | 67.8 |
| 256 | (29, 11) | 2, 6 | 3, 6 | 59.3 | 60.9 | 75.4 |

  - Dense elimination costs about `T^{2.8}` to `T^{2.9}` here (`T = 35..5005`), so the column
    `T^{2.81}` is the model that fits this solver. It predicts `τ*` within a factor 1.35. The
    Wiedemann formula, which the toy solver does not implement, is within a factor 3.
  - The scaling in τ is exact: the same batch of solutions serves every τ.
  - The toys show both regimes. Over `F₁₆` guesses are cheap, the optimum sits where the degree
    does not move, and C1 gains almost the full τ (`τ* ≈ 1..3`). Over `F₂₅₆` with `M ≥ 9` the
    direct attack is best at `j = 2`, C1 needs `j = 3`, and `τ* ≈ 57..59`. The real parameters
    are of the second kind (`j = 3` against `j = 2` in the reference row, `τ* ≈ 72`).
- *Not tested:* the Thomae–Wolf step, Wiedemann, and sizes where `D > 6`.

### 4.2 Other structured lists [heuristic]

- *Subfield line.* `{λc : λ ∈ F₁₆}` has 16 points. `P(s) ∈ h + F₁₆·c` is 89 of the 90
  `F₁₆`-linear conditions of `P(s) = h`, for `P` as a quadratic map over `F₁₆` in 238 variables.
  One equation of 90 over `F₁₆` is worth less than one of 45 over `F`, and the descended system
  is no easier than the original. Over `F` the condition is `μ^{16} = μ`, degree 32, as in the
  last row of the table.
- *`F₂`-subspace of 16 shifts.* It removes 4 of 360 equations over `F₂`. Same conclusion.
- *Shifts of the form `P(u_a)` or `B(u_a, ·)`.* `P(s) = h + P(u_a)` is `Q_{u_a}(s + u_a) = h`: the
  translated problem again.

- *Why a line.* Any list gives τ times as many forgeries as one target. To use this, one relaxed
  system must contain them all. A list spanning a `d`-flat gives `45 − d` quadrics and a landing
  rate `τ/256^d`. A list on a plane curve of degree `e` gives 43 quadrics, one equation of degree
  `2e` and the rate `τ/256`, which the line beats. So `d = 1` is the best relaxation we see.
- *Choice of `c`.* `π_c ∘ P` runs over the 44-dimensional subspaces of the span of the 45 public
  quadrics. One of them is easier only if it contains special quadrics, e.g. of low rank. For UOV
  none are known (MinRank is not an attack on UOV). The experiments of §4.1 use random `c`.

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

So the calls do not combine with the shifts beyond the factor τ. Two points can be made exact.
(A third, shifts chosen after earlier answers, is Lemma S3 of `ompr-cryptanalysis.md` §4.2.)

**One call, two requests [proved].** Scaling turns a preimage of `y` into preimages of the class
`F^×·y`. A call serves requests `k < k′` in this way only if two candidates are proportional:
`h_{k′} + δ_{k′,b} ∈ F^×·(h_k + δ_{k,a})` for some `a, b`. The right-hand sides and the list
`δ_{k′,·}` are fixed before `h_{k′}`, which is uniform. So this has probability
`≤ 255·τ²·256^{−45}` per pair of requests, whatever the lists.

**Lemma C3 (landing by a singular vector) [proved].** Let `z ≠ 0` with `P(z) = 0`, and `c ≠ 0`.
Let `W_c = {s : B(s, z) ∈ F·c}`, a subspace of dimension `≥ N − M + 1 = 75` that contains `z`.
1. On `W_c`, `π_c ∘ P` is invariant under `s ↦ s + λz`: it is a system of 44 quadrics on
   `W_c/F·z`, of dimension 74 (generically).
2. If `s ∈ W_c`, `π_c(P(s)) = π_c(t)` and `B(s, z) ≠ 0`, then `P(s + λz) = t` for exactly one `λ`.

*Proof.* T1.2: `P(s + λz) = P(s) + λ·B(s, z)`, and `B(s, z) = β·c` on `W_c`. `z ∈ W_c` because
`B(z, z) = 0`. For 2, `P(s) = t + μ·c`, so `λ = μ/β`. ∎

- `z₀ = D(0)` is such a vector (T1.2), for one call. Finding one without the oracle is a forgery
  for the target 0.
- **No shift is used.** With `z₀`, a preimage of *any* target is a zero of 44 quadrics in 74
  variables: the landing on the line `t + F·c` costs nothing. In the model this is `2^{140.3}`:
  `U` of the plain XL row of §4.1, i.e. C1 at τ = 256, obtained for τ = 1. It is also `H` of the
  TW row, and for a reason: both routes spend about `M` of the `N − M` spare variables to remove
  one equation.
- **It does not stack [count of dimensions].** After the 44 linear conditions of `W_c`, 74
  variables are left for 44 quadrics, and Thomae–Wolf needs `2·44`. With guesses ([FNT21]) it
  needs `k ≥ 14`. So the direct attack stays at `H` of the TW rows of §4.1.
- **With C1.** Shifts along `c` and a singular line along `c′`: 43 linear conditions
  `B(s, z) ∈ span(c, c′)`, 43 quadrics in 75 variables, `λ` removes the `c′` component, and the
  `c` component lands with probability `τ/256`. This is `U·256/τ` of the TW rows again. A
  singular line along `c` itself makes the shifts useless.
- Checked on toy keys (`c1_experiments.py line`): `dim W_c = N − M + 1`, and every `s` as in 2
  gives a preimage.

So `D` improves neither side of the comparison of §4.1 beyond what Thomae–Wolf already gives.

### 4.4 Verdict on attacks

- **The shifts are the forger's.** PomFRIT has no shift list to choose (§4, first paragraph).
  A-OMPR⊕17 must be read with adversarial lists, collinear ones included.
- **τ = 17.** No attack on OMPR⊕17 that beats the best attack on OMPR.
  - Reference model (XL with Wiedemann, Thomae–Wolf): direct forgery `2^{140.3}`
    multiplications, C1 `2^{142.4}`. C1 is `2^{2.1}` dearer; break-even is `τ* ≈ 72`.
  - The margin is not robust in sign: `τ*` moves between 11 and 72 with the solver model and
    the preprocessing. It is robust in size: over the variants C1 is between `2^{0.7}` cheaper
    and `2^{2.1}` dearer.
  - Without any model: for `q = 0` at most `2^{4.09}` cheaper ([UA] Prop. 8(a)). The direct
    attack is at `2^{147.4}` bit operations, so this bound leaves `2^{143.3}`.
  - In PomFRIT the forger also needs `2^{120}` `H₂³` queries to use 17 distinct prefixes (§4).
- **Recommendation: no change.** Non-collinear shifts cannot be imposed: the list comes from the
  forger's commitment and is hidden from the verifier. Nothing needs to be imposed either, since
  the effect is within `2^{4.1}` in the worst case and absent in the reference model. For the
  concrete security of U2, take the direct forgery cost of UOV and subtract at most 4 bits.
  U1 does not use shifts and is not affected.
- **Conjecture A6, restated.** For UOV and `τ ≤ τ*`, the best attack on OMPR⊕τ(N, q) is the best
  attack on OMPR(τN, q). For `τ > τ*` it is cheaper by the factor `τ/τ* ≤ τ` of C1, and for
  `τ ≥ 256` the right comparison is with the map `π_c ∘ P`. `τ* = 256·U/H` depends on the cost
  model; at `(119, 45)` it is 72 in the reference model and at least 11 in all variants.

## 5. Where this leaves A6

| Route | Status |
|---|---|
| Reduction, black-box in the adversary and in `(P, D)` | impossible below `τ^{q+1}/2` ([OR] A4) |
| Reduction, black-box in the adversary, any use of `P` | impossible below `τ^{q+1}/4` unless OMPR^free fails (Theorem R) |
| Reduction using a combiner from the algebra of `P` | none found (§3); would break OMPR^free |
| Reduction that is not black-box in the adversary | open; `E₁` of PomFRIT is the known instance, with additive loss `Q₃·2^{−71}` |
| Attack separating OMPR⊕17 from OMPR | none found; C1 is below break-even in the reference model, and within `2^{4.1}` in any (§4) |
| Attack that uses the `D` oracle, on either game | none below the oracle-free attacks (`ompr-cryptanalysis.md`): the games share the oracle; key recovery through it needs `2^{292.5}` calls (vinegar collision) or `2^{600}` (linear statistics); shifts chosen after answers give the factor τ only |

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
| OMPR^free ([OR] §3.1) | `advOMPRFree`, `FreeWin` | `Assumptions/TheoremR.lean` |
| Theorem R (§2.4) | `thmR`; `lottery_le`, `free_of_win`, `redExp_eqd`, `freeExp_redM` | `Assumptions/TheoremR.lean` |
| The class of Theorem R contains OMPR adversaries and the guessing reduction | `redExp_liftRed`, `guessRed` | `Assumptions/TheoremR.lean`, `Audit/TheoremR.lean` |
| Step 1 of §2.2: `badPr ≤ V⁴·2^{−343}` | `badPr_le`, `badPr_le_V4` | `Assumptions/TheoremRBad.lean` |
| Theorem R as stated in §2.1; Corollary R′ | `thmR_V4`, `thmR_num`; `corR'` | `Assumptions/TheoremRBad.lean` |
| The guessing reduction sends `q + 3` messages | `guessR_bound` | `Audit/TheoremR.lean` |
| T2′ and Lemma N over pqov's keys; no affine pair translates targets | `pr_not_radTriv`, `pr_not_spanTriv`, `pr_translation_le` | `Assumptions/SymmetryCount.lean` |
| Theorem T3 over pqov's keys (`P1`, `P2` uniform): only the scalings, all keys but `256^{−128}` | `t3`, `t3Good_of_not_bad`, `pr_badKey`; `tensor_group`, `tensor_lie`; audits `exists_t3Good`, `not_t3Good_p1_zero` | `Assumptions/SymmetryT3.lean`, `SymmetryScalar.lean`, `SymmetryTensor.lean`, `SymmetryProbes.lean`, `Audit/SymmetryT3.lean` |

The rows of `Spec/PqovShift.lean` are for `qmap`, the model of pqov's public map that
`lake exe spec_kats` checks against the C++. Theorem R is generic in the trapdoor and the class
relation (§2.4); its bad-event bound is for targets up to scalars in `F^m` (`badPr_le`). On paper
only: the success of `A**_D` in Corollary R′ (§2.4), T1.4–5, T4, C1, C3 (C3 is `preimage_line`
plus linear algebra), and of T3 the bound `256^{−976}` with its Lemmas C, E, F, Lemma I and
Proposition A for maps with several Frobenius components (§8.7).

`scripts/ompr-shift-algebra/shift_algebra_toy.py` (pure Python, about 8 s): the identities of §1
on toy keys over `F₁₆`, including good ⇔ `𝒪 ∩ K_s = 0`, oil translation and `rad B = 0`; the
infinitesimal symmetries; the chi-square test of Hypothesis X (40 000 samples by default; a
fourth argument sets the count); the cost of the degree-34 landing equation of §4.1.

`scripts/ompr-shift-algebra/c1_experiments.py` (Python; the toy part needs gcc and builds
`c1_toy.c`):
- `estimates` (seconds): the cost table of §4.1 for `(119, 45)` and `(112, 44)`, the cost per
  number of guesses, the step for `m = 36..55`, key-recovery figures, and the `H₂³` cost of
  distinct prefixes;
- `line` (8 s): Lemma C3 on toy keys over `F₁₆`;
- `toy` (about 20 minutes on 24 cores; `toy quick`: 2 minutes): the experiments of §4.1.
  `c1_toy q N M seed jmin jmax solutions seconds` runs one key.
Run them under a memory cap. Peak memory is about 1 GB on 24 cores. Batch sizes follow a time
budget, so the counts quoted in §4.1 vary a little between runs and machines.

## 7. Open

- A reduction OMPR ⇒ OMPR⊕17 that is not black-box in the adversary, or a proof that the natural
  non-black-box classes also fail.
- T3 in Lean with the bound `256^{−976}` (Lemma C, the rank Lemmas E and F, the count of
  matrices by rank), and Proposition A for additive maps with several Frobenius components
  (Lemma I). `t3` has `256^{−128}` and one component (§8.7).
- T3 is proved for additive maps (§8). Open there: pairs `(φ, Θ)` with `φ` not additive, beyond
  `φ(s) = γ(P(s))·s`; pairs with `A` not bijective and `T ≠ 0`; a sharper exceptional fraction
  (the bound `256^{−976}` comes from the matrices at distance 1 from the scalars).
- Hypothesis X for the real sampler; the hardness of `P|_{K_s}` (45 quadrics in 74 variables,
  no oil space). `ompr-cryptanalysis.md` §3.3–3.4: spans of answers cover target classes like
  spans of random points on toy keys; `P|_{K_s}` costs `2^{144.1}` in the reference model.
- Theorem R with the lottery form of the assumption stated as a game, and its relation to
  OMPR^free.
- A multi-target algebraic attack on MQ would change §4.1 for independent targets as well; we
  know none.
- The break-even `τ*` of C1 at `(119, 45)`. It is fixed by the degree grid of the solver, and our
  models place it between 11 and 72. Not modelled: Hashimoto's reduction [Has21], the crossbred
  algorithm, XL with corank above one, and constants of the linear algebra. A reduction that
  removes a second equation from the direct attack and not from C1, or the reverse, changes the
  sign of the margin; none can make the gain exceed τ.
- C1 with Thomae–Wolf on toy keys (the experiments use plain fixing of variables), and at sizes
  where the operating degree exceeds 6.
- C1 and C3 in Lean. Both are short: C1 is a change of coordinates in the target space, C3 is
  `preimage_line` on a subspace.

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

*Lean* (`Assumptions/SymmetryCount.lean`). In the model with `O`, `P1` arbitrary and `P2` uniform
(the model of `Privacy/PqovKeys.lean`), with the weaker bounds that this model gives:
`Pr[rad B ≠ 0 on F^{119}] ≤ 256^{−1951} + 256^{−3285}` (`pr_not_radTriv`) and
`Pr[the values of B do not span F^{45}] ≤ 256^{45−3330}` (`pr_not_spanTriv`: `h·B = 0` gives
`h·S = 0` on the `74·45` coefficients of `S`). The last step of (G) and (L) for scalar `Z` is
`target_unique`: if the values of `B` span, two linear maps that agree on the values of `P` are
equal; so `P(λs) = T(P(s))` forces `T = λ²·I` (`scaling_target`) and `B(s, λs) = Y(P(s))` forces
`Y = 0` (`scaling_infinitesimal_target`).

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

**Lean with the count** (`Assumptions/SymmetryCount.lean`, `Audit/SymmetryCount.lean`; keys
`pqovKey O P1 P2`, any `O` and `P1`, uniform `P2`):

| Statement | Lean |
|---|---|
| T2′: a radical vector has `L_v = 0`, and `S·x = 0` if `v = 0` | `rad_coords`, `not_radTriv_imp` |
| Lemma N, radical: `Pr[rad B ≠ 0] ≤ 256^{−1951} + 256^{−3285}` | `pr_not_radTriv` |
| T2 with T2′: no affine pair with `A` onto translates targets | `no_translation`, `pr_translation_le` |
| Lemma N, span: `Pr[values of B do not span] ≤ 256^{−3285}` | `pr_not_spanTriv` |
| `T` is determined by `A`; scalar `A` gives `T = λ²I`, scalar `X` gives `Y = 0` | `target_unique`, `scaling_target`, `scaling_infinitesimal_target` |
| Non-vacuity: good keys exist for every `O`, `P1`; the scalings satisfy the hypotheses | `exists_good_key`, `scaling_pair_hyps` |

**Lean: `A` and `X` are scalar** (`Assumptions/SymmetryT3.lean`, `SymmetryScalar.lean`,
`SymmetryTensor.lean`, `SymmetryProbes.lean`; `Audit/SymmetryT3.lean`).

*Statement* (`t3`). For every oil matrix `O`, over uniform `P1` and `P2` parts (`P1Part`: the
`124875` bytes of the `P1` block), the key `pqovKey O P1 P2` satisfies `T3Good` except with
probability `≤ 256^{−128} = 2^{−1024}`. `T3Good pk`, for `P = qmap pk` on `F^{119}`:
- if `P(A s + a) = T(P s) + c` for all `s`, with `A`, `T` additive and `σ`-semilinear for a ring
  endomorphism `σ` of `F`, and `A` bijective or `T` injective, then `σ = id`, `a = 0`, `c = 0`,
  `A = λ·I`, `T = λ²·I`, `λ ≠ 0`;
- if `B(s, X s) = Y(P s)` for all `s`, with `X`, `Y` linear, then `X = λ·I`, `Y = 0`.

The ring endomorphisms of `F₂₅₆` are the powers of the Frobenius. So this is (G), (L), (S) and
(A) for maps with one Frobenius component, in the model of §8.1.

*The model.* For fixed `O`, `(P1, P2) ↦ (P1, S)` is a bijection (`sEquiv`), `S = (P1 + P1ᵀ)·O +
P2`. In the coordinates `(v, x)` of the oil space (`adEquiv`), `P(v, x) = P₁(v) + L(v, x)` with
`L(v, x)_k = vᵀ S_k x` (`qmap_emb`). So the vinegar part `P₁` and the tensor `S` are uniform and
independent. **`P1` cannot be fixed**: for `P1 = 0`, `P(v, x) = L(v, x)` is bilinear and
`(v, x) ↦ (v, βx)`, `T = β·I` is a pair for every `P2` (`not_t3Good_p1_zero`). Likewise
`X(v, x) = (0, x)`, `Y = I` is an infinitesimal pair (not in Lean). So T3 does not hold in the
model of `Assumptions/SymmetryCount.lean` (`P1` arbitrary).

*The route.* It is not the one of §8.2–8.4. No module structure, exterior power or count of
matrices by rank is used. Each event is a union over a few vectors and functionals, and a
probability computed by interpolation: the values of a uniform linear map at independent
vectors are uniform and independent (`evHom_surjective`, `bqHom_surjective`).
1. *`A` maps `𝒪` into `𝒪`.* `A(𝒪)` is a space of dimension `M` on which `P` vanishes. If it
   has 18 vectors `z_i`, `z'_j` independent modulo `𝒪`, the 81 values `B(z_i, z'_j)` vanish;
   they are uniform in `P1`: `IsoQ`, `≤ 256^{−1503}` (`pr_isoQ`). Otherwise `A(𝒪) ∩ 𝒪` has
   codimension `≤ 17` in `𝒪` and `L(w, ·)` vanishes on it for some vinegar `w ≠ 0`: `BoxV`. In
   the infinitesimal case `X(𝒪) ⊂ 𝒪` follows from `L(X̄x, x) = 0`: `PairOV` or `BoxV`
   (`ov_eq_zero`).
2. *The tensor.* `A` induces `g₁` on `F^N/𝒪` and `g₂` on `𝒪`, and `L(g₁v, g₂x) = T(L(v, x))`.
   With `g₃ = Tᵀ` the trilinear form `h·L(v, x)` satisfies `ℓ(g₃h, v, x) = ℓ(h, g₁v, g₂x)`. For
   each leg: if the map has three vectors `t_j` with `t_j`, `g t_j` independent (*free
   probes*), the slices of `S` at `g t_j` are functions of those at `t_j`: a `Free` event,
   probability `|slice|^{−3}` against a union over the six vectors and the other two maps
   (`pr_free`). If not, the map is a scalar `c` on a subspace of codimension `≤ 4`
   (`near_scalar`); for a `σ`-semilinear map, `c = 0` or `σ = id`, and `c = 0` contradicts
   surjectivity. This is how (S) is proved: a semilinear bijection of the vinegars always has
   free vectors. On the three subspaces `c₃ = c₁c₂` (else `BoxH`), and a vector
   `w = g u − c u ≠ 0` on one leg gives `ℓ = 0` on `w` times the two subspaces: a `Box` event.
   So `g₁ = α`, `g₂ = β`, `T = αβ` (`tensor_group`); in the infinitesimal case `X₁ = α`,
   `X₂ = β`, `Y = α + β` (`tensor_lie`).
3. *The vinegar part.* With `A(v, 0) = (αv, Cv)`: `L(v, Cv) = (β − α)·P₁(v)`. If `β ≠ α`, the
   polar form of `P₁` is a function of `S` and `C`: `DetQ`, `≤ 256^{−314}` (`pr_detQ`). So
   `β = α` and `L(v, Cv) = 0` for all `v`, which gives `C = 0`: `PairVO` if `C` has rank `≥ 18`,
   `BoxO` otherwise (`vo_eq_zero`). In the infinitesimal case `L(v, Cv) = (α + β)·P₁(v)`, and
   `β = −α = α`.
4. *Affine part, and `T` injective.* As in T2, with the radical trivial by `BoxV` and `BoxO`
   (`rad_trivial`, `adapted_affine`).

| Event | Lean | Bound |
|---|---|---|
| `ℓ = 0` on `w × K × K'`, `w ≠ 0` a vinegar, an oil vector, a functional on targets | `pr_boxV`, `pr_boxO`, `pr_boxH` | `256^{−129}`, `256^{−854}`, `256^{−2349}` |
| free probes, group, on the three legs | `pr_freeV`, `pr_freeO`, `pr_freeH` | `256^{−1325}`, `256^{−2219}`, `256^{−2219}` |
| free probes, infinitesimal | `pr_freeLV`, `pr_freeLO`, `pr_freeLH` | `256^{−1581}`, `256^{−2219}`, `256^{−2219}` |
| `L(v, Cv) = 0`, `L(Cx, x) = 0`, rank `C ≥ 18` | `pr_pairVO`, `pr_pairOV` | `256^{−315}` each |
| a second isotropic space; `P₁` determined by `S` | `pr_isoQ`, `pr_detQ` | `256^{−1503}`, `256^{−314}` |

The sum is `≤ 13·256^{−129} ≤ 256^{−128}` (`pr_badKey`). The largest term is `BoxV`: 74 + 17·45
+ 4·45 parameters against `28·41` conditions. Sharper parameters would lower it; we kept one
box event per leg.

*Audits* (`Audit/SymmetryT3.lean`): good keys exist for every `O` (`exists_t3Good`); the
scalings satisfy the hypotheses (`scaling_group_hyps`, `scaling_inf_hyps`);
`not_t3Good_p1_zero`.

On paper only:
- the bound `256^{−976}` of §8.1, with Lemma C, the rank Lemmas E and F and the counts of
  matrices by rank (Lean: `256^{−128}`, by the route above);
- Lemma I and Proposition A for additive maps `A = Σ_i A_i ∘ φ^i` with several Frobenius
  components. `t3` covers the maps with one component, which is the last step of the proof of
  Proposition A; the reduction to one component (comparison of coefficients of polynomial
  functions, then Lemma I) is not mechanized;
- Lemma N with the bounds `256^{−3211}` and `256^{−5987}` (`P1` random). `t3` does not use it:
  the radical and the span are handled by the box events.

Theorem R (§2) uses no part of T3.

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
- [TW12] Thomae, Wolf, *Solving underdetermined systems of multivariate quadratic equations
  revisited*, PKC 2012. [FNT21] Furue, Nakamura, Takagi, *Improving Thomae–Wolf algorithm for
  solving underdetermined multivariate quadratic polynomial problem*, PQCrypto 2021. [Has21]
  Hashimoto, *An improvement of algorithms to solve under-defined systems of multivariate
  quadratic equations*, 2021. [BFP09] Bettale, Faugère, Perret, *Hybrid approach for solving
  multivariate systems over finite fields*, J. Math. Cryptology 2009. All from memory.
