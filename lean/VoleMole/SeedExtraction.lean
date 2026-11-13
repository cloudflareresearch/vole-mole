import VoleMole.Extraction.Gates

/-!
# Full-witness extraction from seeds: the linear-algebra core (sketch, "seed PRG as a random oracle")

The seed-based extractor reads, for every tree `i` whose seeds are all determined by the prover's
PRG queries, the corrected small-VOLE value `u^{(i)} ∈ F₂^ℓ`, and outputs the candidate
`w^{(i)} = u^{(i)} + d`. This file formalizes the deterministic parts of the argument:

* **Claim 4** (`free_tree_holds_witness`, `card_le_one_of_all_fixed`): if `Q[j](Δ)` has the
  per-tree form and also the consistent form `V*[j] + u*[j]·Δ` on the accepting set `A`, and `u*`
  is a bit vector, then every tree whose challenge block is not constant on `A` is known and
  holds `u*`; and if every block is constant then `|A| ≤ 1`.
* **Claim 3**, root counting (`card_le_natDegree`): a nonzero polynomial check of degree `≤ d_zk`
  vanishing at the lifted challenges of `A` forces `|A| ≤ d_zk`.
* **The Theorem's per-chain case analysis** (`extraction_cases`, `accepting_card_le`): on a chain
  where Claims 1–3 hold, either the extractor succeeds or at most `max d_zk 1` admissible
  challenges are accepted.

Out of scope: Claims 1–2 (random-oracle and KOS arguments), the probability that the QuickSilver
check polynomial vanishes identically (`ε_zk`), and the union bound over the `Q` chains.

## Model

Challenges are given by their blocks `Δ' = (Δ_i)_i ∈ Π_i B_i`, one per tree. The lift
`e : Π_i B_i →+ F` is the CRT lift `Δ' ↦ Δ = ToField(W_crt · Δ')`, assumed injective, and
`e_i := e ∘ single i` is the lift of block `i`, so `Δ = Σ_i e_i(Δ_i)`. `known` is the set of trees
with no dead leaf: all their seeds are determined by the prover's queries, so the extractor finds
the hidden seed whatever `Δ_i` is. Bits are embedded in `F` as `0, 1`; the field is arbitrary (the
argument does not use characteristic 2).
-/

open Finset Polynomial

set_option linter.unusedSectionVars false

namespace VoleMole.SeedExtraction

variable {ι J F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)]

/-- Bits as field elements. -/
def bit (b : Bool) : F := if b then 1 else 0

/-- Tree `i` is *fixed* if its challenge block `Δ_i` is constant on `A`. -/
def IsFixed (A : Set (∀ i, B i)) (i : ι) : Prop := ∀ Δ ∈ A, ∀ Δ' ∈ A, Δ i = Δ' i

/-- `e_i`, the lift of block `i`. -/
def blockLift (e : (∀ i, B i) →+ F) (i : ι) : B i →+ F := e.comp (AddMonoidHom.single B i)

lemma lift_eq_sum (e : (∀ i, B i) →+ F) (Δ : ∀ i, B i) : e Δ = ∑ i, blockLift e i (Δ i) := by
  conv_lhs => rw [← Finset.univ_sum_single Δ]
  rw [map_sum]
  rfl

/-- The hypotheses of Claim 4 for one chain. -/
structure Claim4Hyp (e : (∀ i, B i) →+ F) (A : Set (∀ i, B i)) (known : Finset ι)
    (u : ι → J → Bool) (Q : J → (∀ i, B i) → F) (uStar : J → F) : Prop where
  /-- `W_crt` is injective, so the lift `Δ' ↦ Δ` is. -/
  lift_inj : Function.Injective e
  /-- The verifier's key on witness row `j`, from the committed data:
  `Q[j](Δ) = V[j] + Σ_{i known} u^{(i)}[j] e_i(Δ) + (constant on A from the other trees)`. -/
  tree_form : ∀ j, ∃ c, ∀ Δ ∈ A, Q j Δ = c + ∑ i ∈ known, bit (u i j) * blockLift e i (Δ i)
  /-- Claim 2 (KOS consistency): `Q[j](Δ) = V*[j] + u*[j]·Δ` on `A`. -/
  consistent : ∀ j, ∃ v, ∀ Δ ∈ A, Q j Δ = v + uStar j * e Δ
  /-- Claim 4 (i): trees with a dead leaf are fixed (condition (a) in the definition of `A`). -/
  unknown_fixed : ∀ i ∉ known, IsFixed A i

/-- The disagreement set `D_j = {i known | u^{(i)}[j] ≠ u*[j]}`. -/
noncomputable def disagreeSet (known : Finset ι) (u : ι → J → Bool) (uStar : J → F) (j : J) :
    Finset ι :=
  open Classical in known.filter fun i => bit (u i j) ≠ uStar j

/-- The key step of Claim 4: `Σ_{i ∈ D_j} e_i(Δ_i - Δ'_i) = 0` for `Δ, Δ' ∈ A`. This is where
both `u^{(i)}[j]` and `u*[j]` being bits is used: the coefficient `u^{(i)}[j] - u*[j]` is `0` off
`D_j` and a common sign `±1` on `D_j`. -/
lemma sum_disagree_eq_zero {e : (∀ i, B i) →+ F} {A : Set (∀ i, B i)} {known : Finset ι}
    {u : ι → J → Bool} {Q : J → (∀ i, B i) → F} {uStar : J → F}
    (h : Claim4Hyp e A known u Q uStar) (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1) (j : J)
    {Δ Δ' : ∀ i, B i} (hΔ : Δ ∈ A) (hΔ' : Δ' ∈ A) :
    ∑ i ∈ disagreeSet known u uStar j, blockLift e i (Δ i - Δ' i) = 0 := by
  classical
  obtain ⟨c, hc⟩ := h.tree_form j
  obtain ⟨v, hv⟩ := h.consistent j
  set d : ι → F := fun i => blockLift e i (Δ i - Δ' i)
  -- Off `known` the blocks are constant on `A`, so their lifts cancel.
  have hunk : ∀ i ∉ known, d i = 0 := fun i hi => by
    simp [d, h.unknown_fixed i hi Δ hΔ Δ' hΔ']
  have hall : e Δ - e Δ' = ∑ i ∈ known, d i := by
    have : e Δ - e Δ' = ∑ i, d i := by
      rw [lift_eq_sum e Δ, lift_eq_sum e Δ', ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (map_sub _ _ _).symm
    rw [this]
    exact (Finset.sum_subset (Finset.subset_univ known) fun i _ hi => hunk i hi).symm
  -- Subtract the two forms of `Q[j](Δ) - Q[j](Δ')`.
  have hrel : ∑ i ∈ known, (bit (u i j) - uStar j) * d i = 0 := by
    have h1 := (hc Δ hΔ).symm.trans (hv Δ hΔ)
    have h2 := (hc Δ' hΔ').symm.trans (hv Δ' hΔ')
    have : ∑ i ∈ known, bit (u i j) * d i = uStar j * (e Δ - e Δ') := by
      simp only [d, map_sub, mul_sub, Finset.sum_sub_distrib]
      linear_combination h1 - h2
    rw [hall, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- The coefficient is a common sign on `D_j` and zero elsewhere.
  obtain ⟨s, hs, hsum⟩ : ∃ s : F, s ≠ 0 ∧
      ∑ i ∈ known, (bit (u i j) - uStar j) * d i =
        s * ∑ i ∈ disagreeSet known u uStar j, d i := by
    rcases hbits j with h0 | h1
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [one_mul, disagreeSet, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      cases u i j <;> simp [bit, h0]
    · refine ⟨-1, neg_ne_zero.2 one_ne_zero, ?_⟩
      rw [disagreeSet, Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      cases u i j <;> simp [bit, h1]
  rw [hsum] at hrel
  exact (mul_eq_zero.1 hrel).resolve_left hs

/-- Trees in `D_j` are fixed: injectivity of the lift turns `Σ_{i ∈ D_j} e_i(Δ_i - Δ'_i) = 0` into
`Δ_i = Δ'_i` for every `i ∈ D_j`. -/
lemma isFixed_of_mem_disagree {e : (∀ i, B i) →+ F} {A : Set (∀ i, B i)} {known : Finset ι}
    {u : ι → J → Bool} {Q : J → (∀ i, B i) → F} {uStar : J → F}
    (h : Claim4Hyp e A known u Q uStar) (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1) {j : J} {i : ι}
    (hi : i ∈ disagreeSet known u uStar j) : IsFixed A i := by
  classical
  intro Δ hΔ Δ' hΔ'
  set D := disagreeSet known u uStar j
  set y : ∀ k, B k := fun k => if k ∈ D then Δ k - Δ' k else 0
  have hy : e y = 0 := by
    rw [lift_eq_sum, ← sum_disagree_eq_zero h hbits j hΔ hΔ', ← Finset.sum_subset
      (Finset.subset_univ D) fun k _ hk => by simp [y, hk]]
    exact Finset.sum_congr rfl fun k hk => by simp [y, show k ∈ D from hk]
  have : y = 0 := h.lift_inj (hy.trans (map_zero e).symm)
  have := congrFun this i
  simp only [y, hi, ite_true, Pi.zero_apply] at this
  exact sub_eq_zero.1 this

/-- **Claim 4 (ii)**: every free tree is known and holds `u*`. -/
theorem free_tree_holds_witness {e : (∀ i, B i) →+ F} {A : Set (∀ i, B i)} {known : Finset ι}
    {u : ι → J → Bool} {Q : J → (∀ i, B i) → F} {uStar : J → F}
    (h : Claim4Hyp e A known u Q uStar) (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1) {i : ι}
    (hfree : ¬IsFixed A i) : i ∈ known ∧ ∀ j, bit (u i j) = uStar j := by
  classical
  have hk : i ∈ known := by
    by_contra hk
    exact hfree (h.unknown_fixed i hk)
  refine ⟨hk, fun j => ?_⟩
  by_contra hne
  exact hfree (isFixed_of_mem_disagree h hbits (j := j)
    (by simp [disagreeSet, hk, hne]))

/-- **Claim 4 (iii)**: if every tree is fixed then `|A| ≤ 1`. -/
theorem card_le_one_of_all_fixed {A : Finset (∀ i, B i)} (hfix : ∀ i, IsFixed (A : Set (∀ k, B k)) i) :
    A.card ≤ 1 :=
  Finset.card_le_one.2 fun Δ hΔ Δ' hΔ' => funext fun i => hfix i Δ hΔ Δ' hΔ'

/-- **Claim 3**, root counting: if a nonzero polynomial of degree `≤ d_zk` vanishes at the lifted
challenge `e(Δ')` for every `Δ' ∈ A`, then `|A| ≤ d_zk`. (In QuickSilver the check polynomial's
top coefficient is the `chall₂`-combination of `f(u* + d)`, so it is nonzero unless
`f(u* + d) = 0` or `chall₂` is bad.) -/
theorem card_le_natDegree [DecidableEq F] {e : (∀ i, B i) →+ F} (he : Function.Injective e)
    {A : Finset (∀ i, B i)} {p : F[X]} (hp : p ≠ 0) (hroot : ∀ Δ ∈ A, p.eval (e Δ) = 0) :
    A.card ≤ p.natDegree := by
  classical
  calc A.card = (A.image e).card := (Finset.card_image_of_injective A he).symm
    _ ≤ p.roots.toFinset.card := by
        refine Finset.card_le_card fun x hx => ?_
        obtain ⟨Δ, hΔ, rfl⟩ := Finset.mem_image.1 hx
        exact Multiset.mem_toFinset.2 ((mem_roots hp).2 (hroot Δ hΔ))
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p

/-- **Per-chain case analysis of the Theorem.** Suppose Claims 2–4's hypotheses hold on the chain,
and Claim 3 holds in the form "`f(u* + d) = 0` (and then `u*` is a bit vector by the
bit-constraints) or `|A| ≤ d_zk`". Then `|A| ≤ d_zk`, or `|A| ≤ 1`, or some known tree's candidate
`w^{(i)} = u^{(i)} + d` satisfies `f`, so the extractor succeeds. -/
theorem extraction_cases {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {known : Finset ι}
    {u : ι → J → Bool} {Q : J → (∀ i, B i) → F} {uStar : J → F}
    (h : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar) (sat : (J → F) → Prop) (d : J → F) (dzk : ℕ)
    (hclaim3 : sat (uStar + d) ∨ A.card ≤ dzk)
    (hbits : sat (uStar + d) → ∀ j, uStar j = 0 ∨ uStar j = 1) :
    A.card ≤ dzk ∨ A.card ≤ 1 ∨ ∃ i ∈ known, sat (fun j => bit (u i j) + d j) := by
  rcases hclaim3 with hsat | hcard
  · by_cases hfix : ∀ i, IsFixed (A : Set (∀ k, B k)) i
    · exact Or.inr (Or.inl (card_le_one_of_all_fixed hfix))
    · push Not at hfix
      obtain ⟨i, hi⟩ := hfix
      obtain ⟨hk, hu⟩ := free_tree_holds_witness h (hbits hsat) hi
      refine Or.inr (Or.inr ⟨i, hk, ?_⟩)
      convert hsat using 1
      funext j
      simp [hu j]
  · exact Or.inl hcard

/-- **Per-chain bound.** Let `Z` be the admissible H₂³ outputs (zero grinding bits), decoded to
blocks by `δ`, injective on `Z`. If every accepted `x ∈ Z` has `δ x ∈ A` (Claim 1), then either the
extractor succeeds or at most `max d_zk 1` admissible outputs are accepted, so a uniform `chall₃`
is accepted with probability at most `max(d_zk, 1)/2^λ ≤ (d_zk + 1)·2^{-λ}`. -/
theorem accepting_card_le {Ch : Type*} {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)}
    {known : Finset ι} {u : ι → J → Bool} {Q : J → (∀ i, B i) → F} {uStar : J → F}
    (h : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar) (sat : (J → F) → Prop) (d : J → F) (dzk : ℕ)
    (hclaim3 : sat (uStar + d) ∨ A.card ≤ dzk)
    (hbits : sat (uStar + d) → ∀ j, uStar j = 0 ∨ uStar j = 1)
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, sat (fun j => bit (u i j) + d j)) ∨ #{x ∈ Z | acc x} ≤ max dzk 1 := by
  have hcard : #{x ∈ Z | acc x} ≤ A.card := by
    refine Finset.card_le_card_of_injOn δ (fun x hx => ?_) (hδ.mono fun x hx => ?_)
    · have hx' := Finset.mem_filter.1 hx
      exact hclaim1 x hx'.1 hx'.2
    · exact (Finset.mem_filter.1 hx).1
  rcases extraction_cases h sat d dzk hclaim3 hbits with h1 | h1 | h1
  · exact Or.inr (hcard.trans (h1.trans (le_max_left _ _)))
  · exact Or.inr (hcard.trans (h1.trans (le_max_right _ _)))
  · exact Or.inl h1

/-! ### Random linear combinations of constraints

PomFRIT redeem, Moussaka redeem and Ratatouille spend do not check the `M` components of
`P(s) = t` separately. They check one combination `Σ_k l_k (P(s) - t)_k = 0` with
`l = H(chall₂ ‖ dst)`. So `f(w) = 0` holds only for the chain's own `l`, and the relation needs
the following lemma, applied to the extracted `w = u* + d`, which is fixed before `chall₂`. -/

/-- If `a ≠ 0`, exactly a `1/|F|` fraction of the coefficient vectors `l ∈ F^M` satisfy
`Σ_k l_k a_k = 0`. -/
theorem card_combination_eq_zero [Fintype F] [DecidableEq F] {M : Type*} [Fintype M]
    [DecidableEq M] (a : M → F) (ha : a ≠ 0) :
    #{l : M → F | ∑ k, l k * a k = 0} * Fintype.card F = Fintype.card (M → F) := by
  let φ : (M → F) →+ F :=
    { toFun := fun l => ∑ k, l k * a k
      map_zero' := by simp
      map_add' := fun l l' => by simp [add_mul, Finset.sum_add_distrib] }
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 ha
  have htop : φ.range = ⊤ := by
    refine eq_top_iff.2 fun x _ => ⟨Pi.single k₀ (x / a k₀), ?_⟩
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [Finset.sum_eq_single k₀ (fun k _ hk => by simp [hk]) (by simp)]
    simp [div_mul_cancel₀ x hk₀]
  have h := VoleMole.Extraction.card_fiber_mul_card_range φ (t := 0) (zero_mem _)
  rw [htop, AddSubgroup.card_top, Nat.card_eq_fintype_card] at h
  exact h

/-- The probability form: if `w` violates some component (`a = P(w) - t ≠ 0`), a uniform `l`
makes the combined constraint pass with probability `1/|F|`, which is `2^{-128}` for
`F = GF(2^128)`. -/
theorem combination_prob [Fintype F] [DecidableEq F] {M : Type*} [Fintype M] [DecidableEq M]
    (a : M → F) (ha : a ≠ 0) :
    (#{l : M → F | ∑ k, l k * a k = 0} : ℝ) / Fintype.card (M → F) = (Fintype.card F : ℝ)⁻¹ := by
  have h := card_combination_eq_zero a ha
  have hF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hMF : (0 : ℝ) < Fintype.card (M → F) := by exact_mod_cast Fintype.card_pos
  rw [div_eq_iff hMF.ne', ← h]
  push_cast
  field_simp

end VoleMole.SeedExtraction
