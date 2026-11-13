import VoleMole.Seed.QROM
import VoleMole.Seed.SimExt

/-!
# Q5: bookkeeping for simulation-extractability against quantum adversaries

Paper proof: `lean/docs/extraction/Q5-qrom-simulation-extractability.md`. As in `Seed/QROM.lean`, nothing
here is quantum-specific: states are vectors, steps are linear maps, and the bad database property
is an idempotent operator.

## Results

* `neutral_le`, `telescope_with_neutral` (paper §4, Lemma P): a step `G` with
  `P G (1 − P) = 0` (it never moves amplitude from `¬P` into `P`) costs nothing in Lemma T's
  telescoping. The simulator's programming steps are such steps once programmed H₂³ points are
  excluded from the bad property.
* `relabel_neutral` (Lemma P, the basis form): a step that moves the amplitude of each basis
  state `τ y` to `y` is neutral as soon as `bad y → bad (τ y)`. Programming moves `(D, T)` to
  `(D, T')` with `T' ⊇ T`, and the bad property only loses disjuncts when the programmed set grows.
* `card_B3_le_guarded` (paper §5, the guarded property `P'`): on a chain with no known tree (every
  tree has a dead leaf, e.g. a punctured simulated chain, possibly reused with a new instance),
  at most one admissible H₂³ answer is accepted, without any KOS or QuickSilver hypothesis;
  otherwise the Q2 bound `max d 1` applies. Either way the count is `≤ max d 1`.
* Numbers (paper §3.1): the main term at `q = 2^{30}` for both simulators, the dead-leaf bound for
  one simulated hidden-leaf commitment, and the vacuity of both available `multi` bounds once the
  simulator's cipher queries (`≈ 2^{48}` at `q_S = 2^{30}`) are counted.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Seed.QSimExt

section Neutral

variable {𝕜 E : Type*} [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]

/-- A step `G` that never moves amplitude from `¬P` into `P` does not increase `‖P ·‖`, provided
`G` and `P` are contractions. -/
theorem neutral_le (P G : E →ₗ[𝕜] E) (hneut : ∀ w, P (G (w - P w)) = 0)
    (hG : ∀ w, ‖G w‖ ≤ ‖w‖) (hP : ∀ w, ‖P w‖ ≤ ‖w‖) (v : E) : ‖P (G v)‖ ≤ ‖P v‖ := by
  have hsplit : G v = G (v - P v) + G (P v) := by rw [← map_add, sub_add_cancel]
  rw [hsplit, map_add, hneut v, zero_add]
  exact (hP _).trans (hG _)

/-- **Lemma T with neutral steps.** Steps are `ψ (s+1) = U s (O s (ψ s))`, where `O s` is either a
query with transition bound `c s` or a neutral step (then `c s = 0` is allowed). This is
`QROM.telescope` with the neutral steps' hypotheses discharged by `neutral_le`. -/
theorem telescope_with_neutral (P : E →ₗ[𝕜] E) (O U : ℕ → E →ₗ[𝕜] E) (ψ : ℕ → E)
    (hψ : ∀ s, ψ (s + 1) = U s (O s (ψ s)))
    (hU : ∀ s v, ‖U s v‖ = ‖v‖) (hcomm : ∀ s v, P (U s v) = U s (P v))
    (hP : ∀ w, ‖P w‖ ≤ ‖w‖) (hO : ∀ s w, ‖O s w‖ ≤ ‖w‖)
    (neutral : ℕ → Prop) (hneut : ∀ s, neutral s → ∀ w, P (O s (w - P w)) = 0)
    (hOP : ∀ s, ¬ neutral s → ∀ v, ‖P (O s (P v))‖ ≤ ‖P v‖)
    (c : ℕ → ℝ) (hc : ∀ s, ¬ neutral s → ‖P (O s (ψ s - P (ψ s)))‖ ≤ c s)
    (hc0 : ∀ s, 0 ≤ c s) (h0 : P (ψ 0) = 0) :
    ∀ T, ‖P (ψ T)‖ ≤ ∑ s ∈ range T, c s := by
  classical
  refine QROM.telescope P O U ψ hψ hU hcomm (fun s v => ?_) c (fun s => ?_) h0
  · by_cases hs : neutral s
    · have := neutral_le P (O s) (hneut s hs) (hO s) hP (P v)
      exact this.trans (hP _)
    · exact hOP s hs v
  · by_cases hs : neutral s
    · rw [hneut s hs]; simpa using hc0 s
    · exact hc s hs

end Neutral

section Relabel

variable {X 𝕜 : Type*} [Ring 𝕜]

/-- The projector "the basis state is bad", on amplitude functions `X → 𝕜`. -/
def badProj (bad : X → Prop) [DecidablePred bad] (v : X → 𝕜) : X → 𝕜 :=
  fun x => if bad x then v x else 0

/-- A relabelling step: the amplitude at `τ y` moves to `y`. -/
def relabel (τ : X → X) (v : X → 𝕜) : X → 𝕜 := fun y => v (τ y)

/-- **Programming is neutral (basis form).** If `bad y → bad (τ y)`, i.e. a state can become bad
only if it was bad before, then `P G (1 − P) = 0`. For the simulator's programming step,
`τ (D, T') = (D, T)`, and `P(D, T') → P(D, T)` because `P` reads `T` only through the set of
programmed points, which it excludes from `B₃`. -/
theorem relabel_neutral (bad : X → Prop) [DecidablePred bad] (τ : X → X)
    (hmono : ∀ y, bad y → bad (τ y)) (v : X → 𝕜) :
    badProj bad (relabel τ (v - badProj bad v)) = 0 := by
  funext y
  simp only [badProj, relabel, Pi.sub_apply, Pi.zero_apply]
  by_cases hy : bad y
  · simp [hy, hmono y hy]
  · simp [hy]

end Relabel

section Guarded

open VoleMole.SeedExtraction VoleMole.Seed.SimExt

variable {ι J F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)]

/-- **No known tree.** If every tree is fixed on the accepting set (each has a dead leaf, which
must be hidden), at most one admissible H₂³ answer is accepted. No KOS or QuickSilver hypothesis is
needed, which is why the punctured simulator's own H₂¹, H₂², H_comb queries are not charged `ε_KOS`,
`ε_QS`, `2^{−128}` (paper §5.2). -/
theorem card_acc_le_one_of_all_fixed {Ch : Type*} {A : Finset (∀ i, B i)}
    (hfix : ∀ i, IsFixed (A : Set (∀ k, B k)) i)
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hacc : ∀ x ∈ Z, acc x → δ x ∈ A) :
    #{x ∈ Z | acc x} ≤ 1 := by
  have hcard : #{x ∈ Z | acc x} ≤ A.card := by
    refine Finset.card_le_card_of_injOn δ (fun x hx => ?_) (hδ.mono fun x hx => ?_)
    · have hx' := Finset.mem_filter.1 hx
      exact hacc x hx'.1 hx'.2
    · exact (Finset.mem_filter.1 hx).1
  exact hcard.trans (card_le_one_of_all_fixed hfix)

/-- **The guarded H₂³ transition.** Either the chain has no known tree and every tree is fixed on
`A`, or the hypotheses of Q2's `card_B3_le` hold (which needs `¬B₁ ∧ ¬B₂ ∧ ¬B_l`). In both cases at
most `max d 1` admissible answers are accepted while the extractor fails. -/
theorem card_B3_le_guarded {Ch : Type*} {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)}
    {known : Finset ι} {u : ι → J → Bool} {Q : J → (∀ i, B i) → F} {uStar : J → F}
    (sat : (J → F) → Prop) (d : J → F) (dzk : ℕ)
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A)
    [Decidable (∃ i ∈ known, sat (fun j => bit (u i j) + d j))]
    (hcase : (∀ i, IsFixed (A : Set (∀ k, B k)) i) ∨
      (Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar ∧
        (sat (uStar + d) ∨ A.card ≤ dzk) ∧ (sat (uStar + d) → ∀ j, uStar j = 0 ∨ uStar j = 1))) :
    #{x ∈ Z | acc x ∧ ¬ ∃ i ∈ known, sat (fun j => bit (u i j) + d j)} ≤ max dzk 1 := by
  rcases hcase with hfix | ⟨h, hclaim3, hbits⟩
  · have h1 := card_acc_le_one_of_all_fixed hfix Z δ hδ acc hclaim1
    have hsub : #{x ∈ Z | acc x ∧ ¬ ∃ i ∈ known, sat (fun j => bit (u i j) + d j)}
        ≤ #{x ∈ Z | acc x} := by
      refine Finset.card_le_card fun x hx => ?_
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.1⟩
    exact (hsub.trans h1).trans (le_max_right _ _)
  · exact QROM.card_B3_le h sat d dzk hclaim3 hbits Z δ hδ acc hclaim1

end Guarded

section Numbers

/-- Main term at `q = 2^{30}` with the punctured simulator (its hash queries enter only through
collision terms): `8·(5q·2^{−64})² = 200·2^{−68} ≤ 2^{−60}`. -/
theorem main_term_punctured_at_2_30 : 8 * (5 * (2 : ℝ) ^ 30 / 2 ^ 64) ^ 2 ≤ 1 / 2 ^ 60 := by
  norm_num

/-- With the unpunctured simulator, each simulated proof adds one H₂² and one H_comb query at full
weight: `8·((5q + 2q_S)·2^{−64})²` at `q = q_S = 2^{30}` is `392·2^{−68} ≤ 2^{−59}`. -/
theorem main_term_unpunctured_at_2_30 :
    8 * ((5 * (2 : ℝ) ^ 30 + 2 * 2 ^ 30) / 2 ^ 64) ^ 2 ≤ 1 / 2 ^ 59 := by
  norm_num

/-- Dead leaf (Lemma D): one uniform simulated hidden-leaf commitment is opened by some key with
probability at most `8·Q_E²·p`, `p = 1/(N(N−1))`. At `Q_E = 2^{48}` this is `≤ 2^{−156}`. -/
theorem dead_leaf_at_2_48 :
    8 * ((2 : ℝ) ^ 48) ^ 2 * (1 / (2 ^ 128 * (2 ^ 128 - 1))) ≤ 1 / 2 ^ 156 := by
  norm_num

/-- The free-iv `multi` bound `(32/9)·Q_E³/(N−1)` is vacuous at `Q_E = 2^{48}`, the total cipher
query count at `q_S = 2^{30}` simulated proofs (`≈ 2^{18}` cipher queries each). -/
theorem multi_free_vacuous_at_2_48 :
    1 ≤ 32 / 9 * ((2 : ℝ) ^ 48) ^ 3 / (2 ^ 128 - 1) := by
  norm_num

/-- Q1 Theorem 5.2 needs `θ = 2e√30·q^{3/2}/2^{64} ≤ 1/2`. At `q = 2^{48}` (and so at the
`≈ 2^{49}` that `q_S = 2^{30}` gives) `θ > 1/2`, so the H₄-based `multi` bound does not apply. -/
theorem theta_gt_half_at_2_48 :
    1 / 2 < 2 * Real.exp 1 * Real.sqrt 30 * ((2 : ℝ) ^ 48 * Real.sqrt (2 ^ 48)) / 2 ^ 64 := by
  have he : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
    linarith
  have hs30 : (5 : ℝ) ≤ Real.sqrt 30 := Real.le_sqrt_of_sq_le (by norm_num)
  have hs48 : Real.sqrt ((2 : ℝ) ^ 48) = 2 ^ 24 := by
    rw [show ((2 : ℝ) ^ 48) = (2 ^ 24) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hs48]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ 48 * 2 ^ 24 := by positivity
  have : (2 : ℝ) * 2 * 5 * ((2 : ℝ) ^ 48 * 2 ^ 24) / 2 ^ 64
      ≤ 2 * Real.exp 1 * Real.sqrt 30 * ((2 : ℝ) ^ 48 * 2 ^ 24) / 2 ^ 64 := by
    gcongr
  refine lt_of_lt_of_le ?_ this
  norm_num

end Numbers

end VoleMole.Seed.QSimExt
