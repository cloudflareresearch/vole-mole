import VoleMole.Prob.Uniform

/-!
# Privacy games: probabilities, closeness, hybrid hops, zero knowledge

The privacy theorems of `VoleMole/Privacy/*` compare two experiments on the executable specs
(`VoleMole/Spec/*`): deterministic functions of a uniformly random tape, read by an arbitrary
distinguisher. This file is their common layer.

* `pr α P`: the probability of `P` under the uniform distribution on the finite type `α`, as a real
  number (`pr_eq_toReal_prU`: it is `Prob.prU`). Advantages are `|pr α P − pr β Q|`.
* `pr_prod`: a product tape averages over its first coordinate. Hence the **hop lemmas**
  `abs_pr_prod_sub_le` and `abs_pr_prod_sub_le'`: if two experiments on `α × β` and `α × β'` (or
  `α × β` and `α' × β`) are `ε`-close for every fixed value of the shared coordinate, they are
  `ε`-close. Nesting them reaches any component of a nested tape; a hybrid step replaces one
  component (one proof's randomness, one commitment), with everything else fixed.
* `Close ε X Y`: the outputs of `X` and `Y` are `ε`-close against every distinguisher (statistical
  distance at most `ε`); `Close.prod_right`, `Close.prod_left` average it.
* `pr_equiv`: a bijective re-parametrisation of the tape does not change a probability (the
  one-time pads and the final swaps of the games).
* Adversaries are deterministic functions of their view. A randomized adversary is a family of
  them indexed by its coins, and the bounds hold for every member; the reductions fix the coins
  (and the simulators'), as usual for concrete-security statements.
* **Zero knowledge** (`ZeroKnowledge R prove sim ε`): for every instance `x` and witness `w` with
  `R x w`, the prover's output under uniform randomness `ρ` and the simulator's output under uniform
  coins, from the instance only, are `ε`-close. `ε = 0` is perfect zero knowledge: equal output
  distributions (`zeroKnowledge_zero_iff`). The distinguisher may depend on `x` and `w`, so it may
  know the whole witness.

The simulator is a function of the instance and its coins. In the random-oracle model it also
programs the oracle; the specs keep their hashes inside the abstract proof system, so here the
programming is part of what the hypothesis abstracts. The hypothesis is the conclusion that the
hybrids of `lean/docs/zk.md` (§5–§6, with the label-row fix) establish per proof; the counting
statements of `ZK/*` (`fiberCard`) have the same shape.
-/

open Finset

namespace VoleMole.Privacy

/-- `n` uniformly random bytes, a component of a random tape. -/
abbrev Coins (n : ℕ) := Fin n → UInt8

/-! ## Probabilities under a uniform tape -/

section Pr

variable {α β α' β' γ : Type*} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']

/-- **The probability of `P` under the uniform distribution on `α`**, as a real number. -/
noncomputable def pr (α : Type*) [Fintype α] (P : α → Prop) : ℝ :=
  haveI := Classical.decPred P
  (#{x | P x} : ℝ) / Fintype.card α

theorem pr_def (P : α → Prop) [DecidablePred P] :
    pr α P = (#{x | P x} : ℝ) / Fintype.card α := by
  unfold pr
  congr

theorem pr_eq_toReal_prU [Nonempty α] (P : α → Prop) : pr α P = (Prob.prU α P).toReal := by
  classical
  rw [pr_def, Prob.prU_eq_card, ENNReal.toReal_div]
  simp

theorem pr_congr {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : pr α P = pr α Q := by
  have : P = Q := funext fun x => propext (h x)
  rw [this]

theorem pr_const [Nonempty α] (P : Prop) [Decidable P] : pr α (fun _ => P) = if P then 1 else 0 := by
  classical
  rw [pr_def]
  by_cases h : P <;> simp [h]

theorem pr_nonneg (P : α → Prop) : 0 ≤ pr α P := by
  classical
  rw [pr_def]; positivity

/-- **Re-parametrising the tape by a bijection does not change a probability.** -/
theorem pr_equiv (e : α ≃ β) (P : β → Prop) : pr α (fun a => P (e a)) = pr β P := by
  classical
  rw [pr_def, pr_def, Fintype.card_congr e]
  congr 2
  exact_mod_cast Finset.card_equiv e (by simp)

/-- A product tape averages over its first coordinate. -/
theorem pr_prod (P : α × β → Prop) :
    pr (α × β) P = (∑ a, pr β (fun b => P (a, b))) / Fintype.card α := by
  classical
  simp only [pr_def]
  rw [Fintype.card_prod, ← Finset.sum_div, div_div, Nat.cast_mul, mul_comm]
  congr 1
  rw [Finset.card_filter, Fintype.sum_prod_type, Nat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_filter, Nat.cast_sum]

/-- An event on the first coordinate has its marginal probability. -/
theorem pr_prod_fst [Nonempty β] (P : α → Prop) : pr (α × β) (fun x => P x.1) = pr α P := by
  classical
  simp only [pr_def]
  rw [Fintype.card_prod, Nat.cast_mul]
  have : (#{x : α × β | P x.1} : ℝ) = #{a | P a} * Fintype.card β := by
    rw [show ({x : α × β | P x.1} : Finset (α × β)) = ({a | P a} : Finset α) ×ˢ univ by
      ext x; simp, Finset.card_product, Finset.card_univ, Nat.cast_mul]
  rw [this, mul_div_mul_right _ _ (by exact_mod_cast Fintype.card_ne_zero)]

/-- An event on the second coordinate has its marginal probability. -/
theorem pr_prod_snd [Nonempty α] (P : β → Prop) : pr (α × β) (fun x => P x.2) = pr β P := by
  rw [← pr_equiv (Equiv.prodComm β α)]
  exact pr_prod_fst P

/-- **Hop lemma (shared first coordinate).** Two experiments on `α × β` and `α × β'` that are
`ε`-close for every fixed first coordinate are `ε`-close. -/
theorem abs_pr_prod_sub_le [Nonempty α] (P : α × β → Prop) (Q : α × β' → Prop) {ε : ℝ}
    (h : ∀ a, |pr β (fun b => P (a, b)) - pr β' (fun b => Q (a, b))| ≤ ε) :
    |pr (α × β) P - pr (α × β') Q| ≤ ε := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, pr_prod, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hα,
    div_le_iff₀ hα]
  calc |∑ a, (pr β (fun b => P (a, b)) - pr β' (fun b => Q (a, b)))|
      ≤ ∑ a, |pr β (fun b => P (a, b)) - pr β' (fun b => Q (a, b))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : α, ε := Finset.sum_le_sum fun a _ => h a
    _ = ε * Fintype.card α := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **Hop lemma (shared second coordinate).** -/
theorem abs_pr_prod_sub_le' [Nonempty β] (P : α × β → Prop) (Q : α' × β → Prop) {ε : ℝ}
    (h : ∀ b, |pr α (fun a => P (a, b)) - pr α' (fun a => Q (a, b))| ≤ ε) :
    |pr (α × β) P - pr (α' × β) Q| ≤ ε := by
  rw [← pr_equiv (Equiv.prodComm β α), ← pr_equiv (Equiv.prodComm β α')]
  exact abs_pr_prod_sub_le _ _ h

end Pr

/-! ## Closeness against every distinguisher -/

section Close

variable {α β α' β' γ δ : Type*} [Fintype α] [Fintype β] [Fintype α'] [Fintype β']

/-- **`ε`-closeness**: the outputs of `X` and `Y`, under uniform tapes, are `ε`-close against every
distinguisher (their statistical distance is at most `ε`). -/
def Close (ε : ℝ) (X : α → γ) (Y : β → γ) : Prop :=
  ∀ D : γ → Prop, |pr α (fun a => D (X a)) - pr β (fun b => D (Y b))| ≤ ε

theorem Close.map {ε : ℝ} {X : α → γ} {Y : β → γ} (h : Close ε X Y) (f : γ → δ) :
    Close ε (fun a => f (X a)) (fun b => f (Y b)) :=
  fun D => h (fun c => D (f c))

theorem Close.congr {ε : ℝ} {X X' : α → γ} {Y Y' : β → γ} (h : Close ε X Y)
    (hX : ∀ a, X' a = X a) (hY : ∀ b, Y' b = Y b) : Close ε X' Y' := by
  intro D
  simpa only [hX, hY] using h D

theorem Close.mono {ε ε' : ℝ} {X : α → γ} {Y : β → γ} (h : Close ε X Y) (hε : ε ≤ ε') :
    Close ε' X Y :=
  fun D => (h D).trans hε

theorem close_self {ε : ℝ} (hε : 0 ≤ ε) (X : α → γ) : Close ε X X :=
  fun D => by simpa using hε

/-- Constant outputs are close. -/
theorem close_const [Nonempty α] [Nonempty β] {ε : ℝ} (hε : 0 ≤ ε) (c : γ) :
    Close ε (fun _ : α => c) (fun _ : β => c) :=
  fun D => by classical simpa [pr_const] using hε

/-- Averaging over a shared first coordinate. -/
theorem Close.prod_right [Nonempty α] {ε : ℝ} {X : α → β → γ} {Y : α → β' → γ}
    (h : ∀ a, Close ε (X a) (Y a)) :
    Close ε (fun x : α × β => X x.1 x.2) (fun x : α × β' => Y x.1 x.2) :=
  fun D => abs_pr_prod_sub_le _ _ fun a => h a D

/-- Averaging over a shared second coordinate. -/
theorem Close.prod_left [Nonempty β] {ε : ℝ} {X : α → β → γ} {Y : α' → β → γ}
    (h : ∀ b, Close ε (fun a => X a b) (fun a => Y a b)) :
    Close ε (fun x : α × β => X x.1 x.2) (fun x : α' × β => Y x.1 x.2) :=
  fun D => abs_pr_prod_sub_le' _ _ fun b => h b D

/-- Unused tape coordinates do not matter. -/
theorem close_prod_fst [Nonempty β] {X : α → γ} : Close 0 (fun x : α × β => X x.1) X :=
  fun D => by rw [pr_prod_fst (fun a => D (X a))]; simp

theorem close_prod_snd [Nonempty α] {X : β → γ} : Close 0 (fun x : α × β => X x.2) X :=
  fun D => by rw [pr_prod_snd (fun b => D (X b))]; simp

theorem Close.trans {ε ε' : ℝ} {X : α → γ} {Y : β → γ} {Z : α' → γ} (h : Close ε X Y)
    (h' : Close ε' Y Z) : Close (ε + ε') X Z :=
  fun D => (abs_sub_le _ _ _).trans (add_le_add (h D) (h' D))

theorem Close.symm {ε : ℝ} {X : α → γ} {Y : β → γ} (h : Close ε X Y) : Close ε Y X :=
  fun D => by rw [abs_sub_comm]; exact h D

/-- A bijective re-parametrisation is `0`-close. -/
theorem close_equiv (e : α ≃ β) (X : β → γ) : Close 0 (fun a => X (e a)) X :=
  fun D => by rw [pr_equiv e (fun b => D (X b))]; simp

end Close

/-! ## Zero knowledge -/

section ZK

variable {I W ρ C O : Type*} [Fintype ρ] [Fintype C]

/-- **Zero knowledge with error `ε`.** For every instance `x` and every witness `w` with `R x w`,
the prover's output `prove x w ρ` under uniform randomness `ρ` and the simulator's output
`sim x c` under uniform coins `c` (a function of the instance only) are `ε`-close against every
distinguisher. `ε = 0` is perfect zero knowledge. -/
def ZeroKnowledge (R : I → W → Prop) (prove : I → W → ρ → O) (sim : I → C → O) (ε : ℝ) : Prop :=
  ∀ x w, R x w → Close ε (prove x w) (sim x)

/-- **Perfect zero knowledge is equality of output distributions.** -/
theorem zeroKnowledge_zero_iff (R : I → W → Prop) (prove : I → W → ρ → O) (sim : I → C → O) :
    ZeroKnowledge R prove sim 0 ↔
      ∀ x w, R x w → ∀ D : O → Prop, pr ρ (fun r => D (prove x w r)) = pr C (fun c => D (sim x c)) := by
  refine forall₄_congr fun x w _ D => ?_
  rw [abs_nonpos_iff, sub_eq_zero]

end ZK

end VoleMole.Privacy
