import VoleMole.SeedExtraction

/-!
# Simulation-extractability (L8): the deterministic core

See `lean/docs/extraction/L8-simulation-extractability.md`. A tree whose leaf family contains a simulated
hidden-leaf commitment has a *pinned* leaf: that leaf is dead in every chain, so the verifier
accepts only challenges whose block `i` equals the simulated `Δ_{s,i}` (Lemma H of the note).
This file proves the combinatorics that the note uses:

* `isFixed_of_pinned`: a pinned tree is fixed on the accepting set (Claim 4 (i) for copied trees,
  whichever simulated proof each tree was copied from);
* `card_le_one_of_all_pinned`: if every tree is pinned (all trees copied, possibly from different
  simulated proofs), the accepting set has at most one element;
* `admissible_card_le_one_of_all_pinned`: the per-`H₂³`-query form: at most one admissible
  `H₂³` output is accepted, so a fresh uniform output is accepted with probability `≤ 2^{-λ}`;
* `claim4Hyp_of_pinned`: in a mixed chain, the copied trees satisfy the base theorem's hypothesis
  `Claim4Hyp.unknown_fixed`, so L5/L6 apply unchanged.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Seed.SimExt

open VoleMole.SeedExtraction

variable {ι J F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)]

/-- The accepting set respects pins: on `A`, every pinned tree `i ∈ D` has block `pin i`. -/
def RespectsPins (A : Set (∀ i, B i)) (D : Finset ι) (pin : ∀ i, B i) : Prop :=
  ∀ Δ ∈ A, ∀ i ∈ D, Δ i = pin i

/-- A pinned tree is fixed on the accepting set. -/
theorem isFixed_of_pinned {A : Set (∀ i, B i)} {D : Finset ι} {pin : ∀ i, B i}
    (h : RespectsPins A D pin) {i : ι} (hi : i ∈ D) : IsFixed A i :=
  fun Δ hΔ Δ' hΔ' => (h Δ hΔ i hi).trans (h Δ' hΔ' i hi).symm

/-- If every tree is pinned, the accepting set is contained in `{pin}`. -/
theorem subset_singleton_of_all_pinned {A : Set (∀ i, B i)} {pin : ∀ i, B i}
    (h : RespectsPins A Finset.univ pin) : A ⊆ {pin} :=
  fun Δ hΔ => funext fun i => h Δ hΔ i (Finset.mem_univ i)

/-- If every tree is pinned, `|A| ≤ 1`. -/
theorem card_le_one_of_all_pinned {A : Finset (∀ i, B i)} {pin : ∀ i, B i}
    (h : RespectsPins (A : Set (∀ i, B i)) Finset.univ pin) : A.card ≤ 1 :=
  card_le_one_of_all_fixed fun i => isFixed_of_pinned h (Finset.mem_univ i)

/-- Per-query form. Let `Z` be the admissible `H₂³` outputs, decoded to blocks by `δ`, injective
on `Z`. If every accepted `x ∈ Z` decodes into `A` and every tree is pinned, at most one
admissible output is accepted. -/
theorem admissible_card_le_one_of_all_pinned {Ch : Type*} {A : Finset (∀ i, B i)}
    {pin : ∀ i, B i} (h : RespectsPins (A : Set (∀ i, B i)) Finset.univ pin)
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hacc : ∀ x ∈ Z, acc x → δ x ∈ A) :
    #{x ∈ Z | acc x} ≤ 1 := by
  have hcard : #{x ∈ Z | acc x} ≤ A.card := by
    refine Finset.card_le_card_of_injOn δ (fun x hx => ?_) (hδ.mono fun x hx => ?_)
    · have hx' := Finset.mem_filter.1 hx
      exact hacc x hx'.1 hx'.2
    · exact (Finset.mem_filter.1 hx).1
  exact hcard.trans (card_le_one_of_all_pinned h)

/-- Mixed chains: if every tree outside `known` is pinned (it was copied from some simulated
proof, or otherwise has a dead leaf), then `Claim4Hyp.unknown_fixed` holds, so the base
theorem's Claim 4 applies to the chain as it is. -/
theorem claim4Hyp_of_pinned {e : (∀ i, B i) →+ F} {A : Set (∀ i, B i)} {known : Finset ι}
    {u : ι → J → Bool} {Q : J → (∀ i, B i) → F} {uStar : J → F} {pin : ∀ i, B i}
    (hinj : Function.Injective e)
    (hform : ∀ j, ∃ c, ∀ Δ ∈ A, Q j Δ = c + ∑ i ∈ known, bit (u i j) * blockLift e i (Δ i))
    (hcons : ∀ j, ∃ v, ∀ Δ ∈ A, Q j Δ = v + uStar j * e Δ)
    (hpin : RespectsPins A (Finset.univ.filter (· ∉ known)) pin) :
    Claim4Hyp e A known u Q uStar :=
  ⟨hinj, hform, hcons, fun i hi => isFixed_of_pinned hpin (by simp [hi])⟩

/-- In a mixed chain, a free tree is a fresh (unpinned) tree, it is known, and it holds `u*`. -/
theorem free_tree_is_fresh {e : (∀ i, B i) →+ F} {A : Set (∀ i, B i)} {known : Finset ι}
    {u : ι → J → Bool} {Q : J → (∀ i, B i) → F} {uStar : J → F} {pin : ∀ i, B i}
    {D : Finset ι} (hD : RespectsPins A D pin) (h : Claim4Hyp e A known u Q uStar)
    (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1) {i : ι} (hfree : ¬IsFixed A i) :
    i ∉ D ∧ i ∈ known ∧ ∀ j, bit (u i j) = uStar j :=
  ⟨fun hi => hfree (isFixed_of_pinned hD hi), free_tree_holds_witness h hbits hfree⟩

end VoleMole.Seed.SimExt
