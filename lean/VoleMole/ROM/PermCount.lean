import VoleMole.ROM.PermModel

/-!
# Two fresh cipher values of a random permutation (counting over permutation tables)

The probabilistic core of the permutation model. `ROM/CipherOpen.lean`'s `prEvent_two_cells_le`
(two fresh cells of a uniform *function* table hit a target set of size `K`: `≤ K·2⁻²⁵⁶`) becomes,
for a uniform table of permutations, `≤ K / ((2¹²⁸ − r)(2¹²⁸ − r − 1)) ≤ K·p²` with
`p = 1/(2¹²⁸ − r − 1)`, where `r` bounds the inputs of the key that must keep their values
(`L0-L2` §3.1: a fresh answer is uniform over at least `2¹²⁸ − q_E` values).

* **`card_sum_mul_le`** (double counting): events `ev j` indexed by targets `j`, each event table
  `σ` with a neighbourhood `nb j σ` of at least `M` tables in which `j` is a target, and `σ`
  recovered from any neighbour and `j`; if every table has at most `K` targets, then
  `Σ_j #ev_j · M ≤ K · |Ω|`.
* **`tau y₁ y₂ a₁ a₂`**: a permutation of the blocks with `y₁ ↦ a₁`, `y₂ ↦ a₂`, fixing every other
  block (two transpositions).
* **`prEvent_perm_two_le`**: the target `j` names two different inputs `z₁ j`, `z₂ j` of the key
  `k σ` and two values `y₁ j`, `y₂ j`; the event `ev j σ` says that `j` is a target of `σ`, the two
  inputs are outside a protected set `X σ` (at most `r` inputs, e.g. the inputs of the records of
  a log prefix under `k σ`) and `σ_{kσ}` maps them to the two values. If changing `σ_{kσ}` on
  inputs outside `X σ` (and nothing else) keeps the key and the targets, then
  `Pr[∃ j, ev j σ] ≤ K / ((2¹²⁸ − r)(2¹²⁸ − r − 1))`. The neighbours are `τ ∘ σ_{kσ}` with
  `τ = tau (y₁ j) (y₂ j) a₁ a₂` for distinct `a₁`, `a₂` outside `σ_{kσ}(X σ)`. No cardinality of
  `PTable` (or of the `2¹²⁸`-element block type) is ever evaluated.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Verifier VoleMole.ZK.Sim VoleMole.ROM

/-! ## Double counting -/

/-- **Double counting with neighbourhoods**: `Σ_j #ev_j · M ≤ K · |Ω|`. -/
theorem card_sum_mul_le {Ω J : Type} [Fintype Ω] [Fintype J]
    (ev : J → Ω → Prop) (T : Ω → Finset J) (nb : J → Ω → Finset Ω) (M K : ℕ)
    (hM : ∀ j σ, ev j σ → M ≤ #(nb j σ))
    (hT : ∀ j σ, ev j σ → ∀ π ∈ nb j σ, j ∈ T π)
    (hu : ∀ j σ σ', ev j σ → ev j σ' → ∀ π ∈ nb j σ, π ∈ nb j σ' → σ = σ')
    (hK : ∀ π, #(T π) ≤ K) :
    ∑ j, #(finOf (ev j)) * M ≤ K * Fintype.card Ω := by
  classical
  have hj : ∀ j, #(finOf (ev j)) * M ≤ #(finOf fun π => j ∈ T π) := by
    intro j
    calc #(finOf (ev j)) * M = ∑ _σ ∈ finOf (ev j), M := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ σ ∈ finOf (ev j), #(nb j σ) := sum_le_sum fun σ hσ => hM j σ (mem_finOf.1 hσ)
      _ = #((finOf (ev j)).biUnion (nb j)) := (card_biUnion fun σ hσ σ' hσ' hne =>
          disjoint_left.2 fun π h1 h2 =>
            hne (hu j σ σ' (mem_finOf.1 hσ) (mem_finOf.1 hσ') π h1 h2)).symm
      _ ≤ #(finOf fun π => j ∈ T π) := card_le_card fun π hπ => by
          obtain ⟨σ, hσ, hπ⟩ := mem_biUnion.1 hπ
          exact mem_finOf.2 (hT j σ (mem_finOf.1 hσ) π hπ)
  have hswap : ∑ j : J, #(finOf fun π => j ∈ T π) = ∑ π : Ω, #(T π) := by
    have e1 : ∀ j : J, #(finOf fun π => j ∈ T π) = ∑ π : Ω, if j ∈ T π then 1 else 0 := by
      intro j
      rw [finOf_eq, card_filter]
      exact sum_congr rfl fun _ _ => by congr
    have e2 : ∀ π : Ω, #(T π) = ∑ j : J, if j ∈ T π then 1 else 0 := by
      intro π
      rw [sum_boole, Nat.cast_id, filter_mem_eq_inter, univ_inter]
    simp only [e1, e2]
    exact sum_comm
  calc ∑ j, #(finOf (ev j)) * M ≤ ∑ j, #(finOf fun π => j ∈ T π) := sum_le_sum fun j _ => hj j
    _ = ∑ π : Ω, #(T π) := hswap
    _ ≤ ∑ _π : Ω, K := sum_le_sum fun π _ => hK π
    _ = K * Fintype.card Ω := by rw [sum_const, card_univ, smul_eq_mul, mul_comm]

/-! ## A permutation moving two given blocks to two given blocks -/

/-- **`y₁ ↦ a₁`, `y₂ ↦ a₂`**, every block outside `{y₁, y₂, a₁, a₂}` fixed. -/
def tau (y₁ y₂ a₁ a₂ : Blk) : Equiv.Perm Blk :=
  Equiv.swap a₂ (Equiv.swap a₁ y₁ y₂) * Equiv.swap a₁ y₁

lemma tau_y₂ (y₁ y₂ a₁ a₂ : Blk) : tau y₁ y₂ a₁ a₂ y₂ = a₂ := by
  simp only [tau, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_right]

lemma tau_y₁ {y₁ y₂ a₁ a₂ : Blk} (hy : y₁ ≠ y₂) (ha : a₁ ≠ a₂) : tau y₁ y₂ a₁ a₂ y₁ = a₁ := by
  simp only [tau, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_right]
  refine Equiv.swap_apply_of_ne_of_ne ha fun h => hy ?_
  have := congrArg (Equiv.swap a₁ y₁) h
  rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
  exact this

lemma tau_fix {y₁ y₂ a₁ a₂ v : Blk} (h1 : v ≠ y₁) (h2 : v ≠ y₂) (h3 : v ≠ a₁) (h4 : v ≠ a₂) :
    tau y₁ y₂ a₁ a₂ v = v := by
  simp only [tau, Equiv.Perm.coe_mul, Function.comp_apply]
  rw [Equiv.swap_apply_of_ne_of_ne h3 h1]
  refine Equiv.swap_apply_of_ne_of_ne h4 ?_
  rw [Equiv.swap_apply_def]
  split_ifs <;> assumption

/-! ## Two fresh values of a uniform permutation table -/

/-- The ordered pairs of distinct blocks outside `S`. (Irreducible: `whnf` of a membership must
never unfold `univ` of the `2¹²⁸` blocks.) -/
@[irreducible] def freePairs (S : Finset Blk) : Finset (Blk × Blk) := (univ \ S).offDiag

lemma mem_freePairs {S : Finset Blk} {a : Blk × Blk} :
    a ∈ freePairs S ↔ a.1 ∉ S ∧ a.2 ∉ S ∧ a.1 ≠ a.2 := by
  unfold freePairs
  rw [mem_offDiag, mem_sdiff, mem_sdiff]
  simp only [mem_univ, true_and]

lemma card_freePairs (S : Finset Blk) :
    #(freePairs S) = (2 ^ 128 - #S) * (2 ^ 128 - #S - 1) := by
  unfold freePairs
  rw [offDiag_card, card_sdiff_of_subset (subset_univ _), card_univ, card_blk, ← Nat.mul_sub_one]

/-- `p` with `n` excluded values: `1/(2¹²⁸ − n)`. -/
noncomputable def pE (n : ℕ) : ℝ≥0∞ := (((2 ^ 128 - n : ℕ) : ℕ) : ℝ≥0∞)⁻¹

lemma inv_two_le_pE (r : ℕ) :
    ((((2 ^ 128 - r) * (2 ^ 128 - r - 1) : ℕ) : ℝ≥0∞))⁻¹ ≤ pE (r + 1) ^ 2 := by
  unfold pE
  rw [← ENNReal.inv_pow]
  refine ENNReal.inv_le_inv.2 ?_
  rw [← Nat.cast_pow]
  refine Nat.cast_le.2 ?_
  rw [sq, show 2 ^ 128 - (r + 1) = 2 ^ 128 - r - 1 by omega]
  exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

/-- **Two fresh values of a uniform permutation table hit one of `K` targets** with probability at
most `K / ((2¹²⁸ − r)(2¹²⁸ − r − 1))`: see the module docstring. -/
theorem prEvent_perm_two_le {J : Type} [Fintype J] (ev : J → PTable → Prop)
    (k : PTable → Blk) (X : PTable → Finset Blk) (T : PTable → Finset J)
    (z₁ z₂ y₁ y₂ : J → Blk) (K r : ℕ)
    (hev : ∀ j σ, ev j σ → j ∈ T σ ∧ z₁ j ≠ z₂ j ∧ z₁ j ∉ X σ ∧ z₂ j ∉ X σ ∧
      σ (k σ) (z₁ j) = y₁ j ∧ σ (k σ) (z₂ j) = y₂ j)
    (hinv : ∀ j σ, ev j σ → ∀ π : PTable, (∀ κ, κ ≠ k σ → π κ = σ κ) →
      (∀ x ∈ X σ, π (k σ) x = σ (k σ) x) → k π = k σ ∧ T π = T σ)
    (hX : ∀ σ, #(X σ) ≤ r) (hK : ∀ σ, #(T σ) ≤ K) :
    Pr{let π ← $ᵗ PTable}[∃ j, ev j π] ≤
      K * ((((2 ^ 128 - r) * (2 ^ 128 - r - 1) : ℕ) : ℝ≥0∞))⁻¹ := by
  set M := (2 ^ 128 - r) * (2 ^ 128 - r - 1) with hMdef
  let A : PTable → Finset (Blk × Blk) := fun σ => freePairs ((X σ).image (σ (k σ)))
  let f : J → PTable → Blk × Blk → PTable := fun j σ a =>
    Function.update σ (k σ) (tau (y₁ j) (y₂ j) a.1 a.2 * σ (k σ))
  let nb : J → PTable → Finset PTable := fun j σ => (A σ).image (f j σ)
  have hf_k : ∀ j σ a, f j σ a (k σ) = tau (y₁ j) (y₂ j) a.1 a.2 * σ (k σ) := fun j σ a =>
    Function.update_self _ _ _
  have hf_ne : ∀ j σ a κ, κ ≠ k σ → f j σ a κ = σ κ := fun j σ a κ hκ =>
    Function.update_of_ne hκ _ _
  have hA : ∀ σ a, a ∈ A σ → a.1 ≠ a.2 ∧ a.1 ∉ (X σ).image (σ (k σ)) ∧
      a.2 ∉ (X σ).image (σ (k σ)) := by
    intro σ a ha
    obtain ⟨h1, h2, h3⟩ := mem_freePairs.1 ha
    exact ⟨h3, h1, h2⟩
  have hy : ∀ j σ, ev j σ → y₁ j ≠ y₂ j := by
    intro j σ hj he
    obtain ⟨-, hz, -, -, h1, h2⟩ := hev j σ hj
    exact hz ((σ (k σ)).injective (h1.trans (he.trans h2.symm)))
  -- The neighbour's values at the two inputs.
  have hF1 : ∀ j σ, ev j σ → ∀ a ∈ A σ, f j σ a (k σ) (z₁ j) = a.1 ∧ f j σ a (k σ) (z₂ j) = a.2 := by
    intro j σ hj a ha
    obtain ⟨-, -, -, -, h1, h2⟩ := hev j σ hj
    rw [hf_k]
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, h1, h2]
    exact ⟨tau_y₁ (hy j σ hj) (hA σ a ha).1, tau_y₂ _ _ _ _⟩
  -- The neighbour keeps the protected inputs.
  have hF3 : ∀ j σ, ev j σ → ∀ a ∈ A σ, ∀ x ∈ X σ, f j σ a (k σ) x = σ (k σ) x := by
    intro j σ hj a ha x hx
    obtain ⟨-, -, hz1, hz2, h1, h2⟩ := hev j σ hj
    rw [hf_k]
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    obtain ⟨-, ha1, ha2⟩ := hA σ a ha
    refine tau_fix ?_ ?_ ?_ ?_
    · rw [← h1]; exact fun h => hz1 ((σ (k σ)).injective h ▸ hx)
    · rw [← h2]; exact fun h => hz2 ((σ (k σ)).injective h ▸ hx)
    · exact fun h => ha1 (mem_image.2 ⟨x, hx, h⟩)
    · exact fun h => ha2 (mem_image.2 ⟨x, hx, h⟩)
  have hinv' : ∀ j σ, ev j σ → ∀ π ∈ nb j σ, k π = k σ ∧ T π = T σ := by
    intro j σ hj π hπ
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hπ
    exact hinv j σ hj _ (fun κ hκ => hf_ne j σ a κ hκ) (hF3 j σ hj a ha)
  have hcount := card_sum_mul_le ev T nb M K
    (fun j σ hj => by
      have hinj : Set.InjOn (f j σ) (A σ) := by
        intro a ha a' ha' he
        have e1 := hF1 j σ hj a ha
        have e2 := hF1 j σ hj a' ha'
        rw [he] at e1
        exact Prod.ext (e1.1.symm.trans e2.1) (e1.2.symm.trans e2.2)
      rw [card_image_of_injOn hinj, card_freePairs]
      have him : #((X σ).image (σ (k σ))) ≤ r := card_image_le.trans (hX σ)
      exact Nat.mul_le_mul (by omega) (by omega))
    (fun j σ hj π hπ => by
      rw [(hinv' j σ hj π hπ).2]
      exact (hev j σ hj).1)
    (fun j σ σ' hj hj' π hπ hπ' => by
      obtain ⟨hk1, -⟩ := hinv' j σ hj π hπ
      obtain ⟨hk2, -⟩ := hinv' j σ' hj' π hπ'
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hπ
      obtain ⟨a', ha', he⟩ := mem_image.1 hπ'
      have hkk : k σ' = k σ := hk2.symm.trans hk1
      have e1 := hF1 j σ hj a ha
      have e2 := hF1 j σ' hj' a' ha'
      rw [he, hkk] at e2
      have haa : a' = a := Prod.ext (e2.1.symm.trans e1.1) (e2.2.symm.trans e1.2)
      subst haa
      funext κ
      by_cases hκ : κ = k σ
      · subst hκ
        have h1 := hf_k j σ a'
        have h2 := hf_k j σ' a'
        rw [he, hkk] at h2
        exact mul_left_cancel (h1.symm.trans h2)
      · have h1 := hf_ne j σ a' κ hκ
        have h2 := hf_ne j σ' a' κ (hkk ▸ hκ)
        rw [he] at h2
        exact h1.symm.trans h2)
    hK
  -- The event is covered by the indexed events.
  have hcov : #(finOf fun π => ∃ j, ev j π) ≤ ∑ j, #(finOf (ev j)) := by
    refine (card_le_card fun π hπ => ?_).trans card_biUnion_le
    obtain ⟨j, hj⟩ := mem_finOf.1 hπ
    exact mem_biUnion.2 ⟨j, mem_univ _, mem_finOf.2 hj⟩
  have hnat : #(finOf fun π => ∃ j, ev j π) * M ≤ K * Fintype.card PTable :=
    (Nat.mul_le_mul_right M hcov).trans (by rw [sum_mul]; exact hcount)
  have hpr : Pr{let π ← $ᵗ PTable}[∃ j, ev j π] =
      (#(finOf fun π => ∃ j, ev j π) : ℝ≥0∞) / Fintype.card PTable := by
    rw [@SampleableType.prEvent_uniformSample _ _ _ (fun π => ∃ j, ev j π)
      (Classical.decPred _), finOf_eq]
  rw [hpr]
  have hN0 : (Fintype.card PTable : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hNt : (Fintype.card PTable : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.div_le_iff hN0 hNt]
  rcases Nat.eq_zero_or_pos M with hM0 | hM0
  · rcases Nat.eq_zero_or_pos K with hK0 | hK0
    · have : finOf (fun π => ∃ j, ev j π) = ∅ := by
        refine eq_empty_of_forall_notMem fun π hπ => ?_
        obtain ⟨j, hj⟩ := mem_finOf.1 hπ
        have := card_pos.2 ⟨j, (hev j π hj).1⟩
        have := hK π
        omega
      rw [this, card_empty, Nat.cast_zero]
      exact zero_le
    · rw [hM0, Nat.cast_zero, ENNReal.inv_zero, ENNReal.mul_top (by exact_mod_cast hK0.ne'),
        ENNReal.top_mul hN0]
      exact le_top
  · have hMne : (M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hM0.ne'
    have hMt : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hcast : (#(finOf fun π => ∃ j, ev j π) : ℝ≥0∞) * M ≤ K * Fintype.card PTable := by
      exact_mod_cast hnat
    calc (#(finOf fun π => ∃ j, ev j π) : ℝ≥0∞)
        = #(finOf fun π => ∃ j, ev j π) * M * (M : ℝ≥0∞)⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hMne hMt, mul_one]
      _ ≤ K * Fintype.card PTable * (M : ℝ≥0∞)⁻¹ := mul_le_mul_of_nonneg_right hcast (by simp)
      _ = K * (M : ℝ≥0∞)⁻¹ * Fintype.card PTable := by ring

end VoleMole.ROM.IC
