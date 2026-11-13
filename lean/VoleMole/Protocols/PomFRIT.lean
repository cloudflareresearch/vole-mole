import VoleMole.SeedExtraction

/-!
# PomFRIT: the combinatorial core of the first-phase ("prefix") extractor

`lean/docs/security/pomfrit.md` §5 (Lemma P) needs a value `E₁(x)` of the witness prefix `r` that is
computable when the target hash `h = H_T(x)` is queried, i.e. before `Δ` exists. The reduction
groups the fully alive trees by their candidate prefix and picks a group `g*` of largest total
challenge width. This file proves the deterministic facts behind the bound on the event that the
finally extracted prefix differs from `g*`'s:

* `card_le_prod_of_fixed`: if every tree outside `G` is fixed on the accepting set `A`, then
  `|A| ≤ ∏_{i ∈ G} |B_i|`.
* `fixed_of_prefix_ne`: under Claim 4's hypotheses (`Claim4Hyp`, with `u*` a bit vector), every
  tree whose candidate differs from `u*` on some prefix row is fixed. So the trees that are not
  fixed all lie in the prefix group of `u*`.
* `card_le_prod_prefix_group`: the two combined.
* `minority_weight_le` (FAEST-EM-128f shapes: one tree of 2⁸ leaves and sixteen of 2⁷): if two
  disjoint groups `S`, `T` have widths `Σ_S ≤ Σ_T`, then `Σ_S ≤ 57`.
* `minority_card_le`: hence `|A| ≤ 2⁵⁷`, so a fresh H₂³ answer lands in `A` with probability at most
  `2⁵⁷/2¹²⁸ = 2⁻⁷¹` (`per_query_bound`).

No `sorry`, no `axiom`.
-/

namespace VoleMole.PomFRIT

open Finset VoleMole.SeedExtraction

section Fixed

/-- If every coordinate outside `G` is constant on `A`, then `A` injects into `Π_{i ∈ G} B_i`. -/
theorem card_le_prod_of_fixed {ι : Type*} [DecidableEq ι] {B : ι → Type*}
    [∀ i, AddCommGroup (B i)] [∀ i, Fintype (B i)] (A : Finset (∀ i, B i)) (G : Finset ι)
    (hfix : ∀ i ∉ G, IsFixed (A : Set (∀ k, B k)) i) :
    A.card ≤ ∏ i ∈ G, Fintype.card (B i) := by
  classical
  let f : (∀ i, B i) → (∀ i : G, B i) := fun Δ i => Δ i
  have hinj : Set.InjOn f (A : Set (∀ i, B i)) := by
    intro Δ hΔ Δ' hΔ' heq
    funext i
    by_cases hi : i ∈ G
    · exact congrFun heq ⟨i, hi⟩
    · exact hfix i hi Δ hΔ Δ' hΔ'
  calc A.card ≤ (Finset.univ : Finset (∀ i : G, B i)).card :=
        Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    _ = ∏ i : G, Fintype.card (B i) := by rw [Finset.card_univ, Fintype.card_pi]
    _ = ∏ i ∈ G, Fintype.card (B i) := Finset.prod_coe_sort G (fun i => Fintype.card (B i))

end Fixed

section Prefix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*} [∀ i, AddCommGroup (B i)]
  {F : Type*} [Field F] {J : Type*}

/-- Under Claim 4's hypotheses, a tree whose candidate differs from `u*` on some row (in
particular on a prefix row) is fixed: a free tree holds `u*` on every row. -/
theorem fixed_of_prefix_ne {e : (∀ i, B i) →+ F} {A : Set (∀ i, B i)} {known : Finset ι}
    {u : ι → J → Bool} {Q : J → (∀ i, B i) → F} {uStar : J → F}
    (h : Claim4Hyp e A known u Q uStar) (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1) {i : ι}
    {j : J} (hne : bit (u i j) ≠ uStar j) : IsFixed A i := by
  by_contra hfree
  exact hne ((free_tree_holds_witness h hbits hfree).2 j)

/-- The prefix group of `u*`: known trees whose candidate agrees with `u*` on every prefix row. -/
noncomputable def prefixGroup (known : Finset ι) (u : ι → J → Bool) (uStar : J → F)
    (prefixRows : Set J) : Finset ι :=
  open Classical in known.filter fun i => ∀ j ∈ prefixRows, bit (u i j) = uStar j

/-- Every tree outside the prefix group of `u*` is fixed on `A`. -/
theorem fixed_outside_prefixGroup {e : (∀ i, B i) →+ F} {A : Set (∀ i, B i)}
    {known : Finset ι} {u : ι → J → Bool} {Q : J → (∀ i, B i) → F} {uStar : J → F}
    (h : Claim4Hyp e A known u Q uStar) (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1)
    (prefixRows : Set J) {i : ι} (hi : i ∉ prefixGroup known u uStar prefixRows) :
    IsFixed A i := by
  classical
  by_cases hk : i ∈ known
  · by_contra hfree
    apply hi
    rw [prefixGroup, Finset.mem_filter]
    exact ⟨hk, fun j _ => (free_tree_holds_witness h hbits hfree).2 j⟩
  · exact h.unknown_fixed i hk

/-- `|A| ≤ ∏` of the tree sizes in the prefix group of `u*`. -/
theorem card_le_prod_prefix_group [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {known : Finset ι} {u : ι → J → Bool}
    {Q : J → (∀ i, B i) → F} {uStar : J → F}
    (h : Claim4Hyp e (A : Set (∀ i, B i)) known u Q uStar)
    (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1) (prefixRows : Set J) :
    A.card ≤ ∏ i ∈ prefixGroup known u uStar prefixRows, Fintype.card (B i) :=
  card_le_prod_of_fixed A _ fun _ hi => fixed_outside_prefixGroup h hbits prefixRows hi

end Prefix

section Widths

/-- Challenge widths of the FAEST-EM-128f `one_tree` BAVC: one tree of `2⁸` leaves and sixteen of
`2⁷` (`L = 256 + 16·128 = 2304`, `n_Δ = 120`). -/
def width (i : Fin 17) : ℕ := if i = 0 then 8 else 7

theorem width_total : ∑ i, width i = 120 := by decide

theorem sum_width (S : Finset (Fin 17)) :
    ∑ i ∈ S, width i = 7 * S.card + if (0 : Fin 17) ∈ S then 1 else 0 := by
  have : ∀ i, width i = 7 + if i = 0 then 1 else 0 := by
    intro i; unfold width; split_ifs <;> rfl
  simp only [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_ite_eq',
    mul_comm]

/-- Two disjoint groups with `Σ_S ≤ Σ_T`: the smaller has total width at most 57. -/
theorem minority_weight_le (S T : Finset (Fin 17)) (hdisj : Disjoint S T)
    (hle : ∑ i ∈ S, width i ≤ ∑ i ∈ T, width i) : ∑ i ∈ S, width i ≤ 57 := by
  have hsum : ∑ i ∈ S, width i + ∑ i ∈ T, width i ≤ 120 := by
    rw [← Finset.sum_union hdisj, ← width_total]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [sum_width] at hle hsum ⊢
  split_ifs at hle hsum ⊢ <;> omega

/-- Trees of size `2^{width i}`: if the free trees lie in a group `S` that is not of largest
width (some disjoint group `T` is at least as wide), then `|A| ≤ 2⁵⁷`. -/
theorem minority_card_le {B : Fin 17 → Type*} [∀ i, AddCommGroup (B i)] [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
    (hB : ∀ i, Fintype.card (B i) = 2 ^ width i) (A : Finset (∀ i, B i))
    (S T : Finset (Fin 17)) (hdisj : Disjoint S T)
    (hle : ∑ i ∈ S, width i ≤ ∑ i ∈ T, width i)
    (hfix : ∀ i ∉ S, IsFixed (A : Set (∀ k, B k)) i) : A.card ≤ 2 ^ 57 := by
  calc A.card ≤ ∏ i ∈ S, Fintype.card (B i) := card_le_prod_of_fixed A S hfix
    _ = 2 ^ ∑ i ∈ S, width i := by simp only [hB, Finset.prod_pow_eq_pow_sum]
    _ ≤ 2 ^ 57 := Nat.pow_le_pow_right (by norm_num) (minority_weight_le S T hdisj hle)

/-- Per fresh uniform 128-bit H₂³ answer: `|A|/2¹²⁸ ≤ 2⁻⁷¹`. -/
theorem per_query_bound (a : ℕ) (ha : a ≤ 2 ^ 57) :
    (a : ℝ) / 2 ^ 128 ≤ (2 : ℝ)⁻¹ ^ 71 := by
  have h1 : (a : ℝ) ≤ 2 ^ 57 := by exact_mod_cast ha
  rw [div_le_iff₀ (by positivity), inv_pow]
  calc (a : ℝ) ≤ 2 ^ 57 := h1
    _ = ((2 : ℝ) ^ 71)⁻¹ * 2 ^ 128 := by norm_num

/-- The reduction's loss at `Q₃ = 2⁵⁰` and `Q₃ = 2⁶⁴` H₂³ queries: `2⁻²¹` and `2⁻⁷`. -/
theorem loss_at_2_50 : (2 : ℝ) ^ 50 * (2 : ℝ)⁻¹ ^ 71 = (2 : ℝ)⁻¹ ^ 21 := by norm_num
theorem loss_at_2_64 : (2 : ℝ) ^ 64 * (2 : ℝ)⁻¹ ^ 71 = (2 : ℝ)⁻¹ ^ 7 := by norm_num

end Widths

end VoleMole.PomFRIT
