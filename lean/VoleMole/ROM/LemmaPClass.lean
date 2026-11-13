import VoleMole.ROM.LemmaPDet
import VoleMole.Seed.SliceDecode

/-!
# Lemma P with the class extractor: `2⁵⁰` in place of `2⁵⁷`

`lean/docs/security/pomfrit-lemmap-tight.md` §6A. A *class* is a set of alive trees with the same
witness rows and the same label rows (`key`). Under Claim 4's hypotheses on the witness rows (bit
slopes) and on the label rows (any slopes), an accepting set lies in a slice of **one class**, or
some label slope is not a bit and the set has at most `2^{⌊w/2⌋}` points for the width `w` of its
prefix group. So a prefix group that is split into many classes cannot be completed, however wide
it is, and the default of the first-phase extractor should be the widest class, not the widest
prefix group.

* `clsExt S key p cert`: the extractor `E₁^cls`. Let `i₁` be the least tree of a widest class. If
  that class has width at least 51: if another class of width at least 51 has a different prefix
  and the decoder finds a pair for it (`cert`), output its prefix; otherwise output the prefix of
  `i₁`. If no class has width 51: `majP`, the widest prefix group (Lemma P's `E₁`).
* `class_or_small` (deterministic core): if `cert` is sound (a pair gives `u* = u_C`) and complete
  for level sets of more than `2⁵⁰` points, then `clsExt` is the prefix of the free trees, or the
  accepting set has at most `2⁵⁰` points. The widths `(8, 7, …, 7)` enter through: a class of
  width `≥ 51` has at least 8 trees; three such classes do not exist; a group disjoint from one
  has width `≤ 64`.
* `class_or_small_dec`: the same with `cert` the decoder `Seed.dec` on the KOS check value, from
  `KOSPar` (soundness) and from the affine and two-label structure of the response on the slices
  (completeness). A class of width `≥ 51` that is not the widest has width `≤ 57`, so a subgroup
  of `2⁷` directions meets every level set of more than `2⁵⁰` points.
* `extract_or_class`: `extract_or_major` with `clsExt` and `2⁵⁰`.
* `per_query_bound_cls`, `loss_cls_at_2_64`: `2⁵⁰/2¹²⁸ = 2⁻⁷⁸`; `2⁶⁴·2⁻⁷⁸ = 2⁻¹⁴`.

Not here: the executable verifier's chains (the label rows' tree form and the structure of the CRT
masks for `Verifier`), and the one-more game (`KOSPar` as a bad event at `H₂¹`, the extractor's
evaluations of the check value as queries). `pomfrit_U1_sim` is unchanged.

No `sorry`, no `axiom`.
-/

open Finset

namespace VoleMole.PomFRIT

open VoleMole.SeedExtraction

/-! ## Widths -/

section Widths

/-- A set of trees of total width at least 51 has at least 8 trees. -/
lemma eight_le_card_of_wide {T : Finset (Fin 17)} (h : 51 ≤ ∑ i ∈ T, width i) : 8 ≤ T.card := by
  rw [sum_width] at h
  split_ifs at h <;> omega

lemma card_add_card_le {T T' : Finset (Fin 17)} (hd : Disjoint T T') : T.card + T'.card ≤ 17 := by
  rw [← Finset.card_union_of_disjoint hd]
  exact (Finset.card_le_univ _).trans (by simp)

/-- A set of trees disjoint from one of width at least 51 has width at most 64. -/
lemma width_le_of_disjoint_wide {T T' : Finset (Fin 17)} (hd : Disjoint T T')
    (h : 51 ≤ ∑ i ∈ T', width i) : ∑ i ∈ T, width i ≤ 64 := by
  have h8 := eight_le_card_of_wide h
  have hc := card_add_card_le hd
  rw [sum_width]
  split_ifs <;> omega

/-- There are no three pairwise disjoint sets of trees of width at least 51. -/
lemma not_three_wide {T₁ T₂ T₃ : Finset (Fin 17)} (h12 : Disjoint T₁ T₂) (h13 : Disjoint T₁ T₃)
    (h23 : Disjoint T₂ T₃) (w1 : 51 ≤ ∑ i ∈ T₁, width i) (w2 : 51 ≤ ∑ i ∈ T₂, width i)
    (w3 : 51 ≤ ∑ i ∈ T₃, width i) : False := by
  have a1 := eight_le_card_of_wide w1
  have a2 := eight_le_card_of_wide w2
  have a3 := eight_le_card_of_wide w3
  have hc := card_add_card_le (Finset.disjoint_union_left.2 ⟨h13, h23⟩)
  rw [Finset.card_union_of_disjoint h12] at hc
  omega

end Widths

/-! ## The class extractor -/

section ClassRule

variable {P Kt : Type*} [DecidableEq P] [DecidableEq Kt]

/-- The least tree of a widest group, with its properties. -/
lemma majTree_spec {S : Finset (Fin 17)} {i₀ : Fin 17} (hi₀ : i₀ ∈ S) (key : Fin 17 → Kt) :
    ∃ i₁ ∈ S, majTree S key = some i₁ ∧
      ∀ i' ∈ S, grpW S key (key i') ≤ grpW S key (key i₁) := by
  have hne := majSet_nonempty ⟨i₀, hi₀⟩ key
  have hmem := Finset.min'_mem _ hne
  exact ⟨_, (mem_filter.1 hmem).1, by simp [majTree, hne], (mem_filter.1 hmem).2⟩

/-- The trees of the classes of width at least 51 whose prefix differs from that of `i₁`. -/
def clsCand (S : Finset (Fin 17)) (key : Fin 17 → Kt) (p : Fin 17 → P) (i₁ : Fin 17) :
    Finset (Fin 17) :=
  S.filter fun i => p i ≠ p i₁ ∧ 51 ≤ grpW S key (key i)

/-- **The class extractor `E₁^cls`.** `key i` is the class of tree `i` (its witness and label
rows), `p i` its prefix, `cert i` says that the decoder found a pair for the class of `i`. -/
def clsExt (S : Finset (Fin 17)) (key : Fin 17 → Kt) (p : Fin 17 → P) (cert : Fin 17 → Prop)
    [DecidablePred cert] : Option P :=
  (majTree S key).bind fun i₁ =>
    if 51 ≤ grpW S key (key i₁) then
      if h : (clsCand S key p i₁).Nonempty then
        if cert ((clsCand S key p i₁).min' h) then some (p ((clsCand S key p i₁).min' h))
        else some (p i₁)
      else some (p i₁)
    else majP S p

lemma clsExt_wide {S : Finset (Fin 17)} {key : Fin 17 → Kt} {p : Fin 17 → P}
    {cert : Fin 17 → Prop} [DecidablePred cert] {i₁ : Fin 17} (hmaj : majTree S key = some i₁)
    (hw : 51 ≤ grpW S key (key i₁)) :
    clsExt S key p cert =
      if h : (clsCand S key p i₁).Nonempty then
        if cert ((clsCand S key p i₁).min' h) then some (p ((clsCand S key p i₁).min' h))
        else some (p i₁)
      else some (p i₁) := by
  simp [clsExt, hmaj, hw]

lemma clsExt_narrow {S : Finset (Fin 17)} {key : Fin 17 → Kt} {p : Fin 17 → P}
    {cert : Fin 17 → Prop} [DecidablePred cert] {i₁ : Fin 17} (hmaj : majTree S key = some i₁)
    (hw : ¬51 ≤ grpW S key (key i₁)) : clsExt S key p cert = majP S p := by
  simp [clsExt, hmaj, hw]

variable {F : Type*} [Field F]
variable {B : Fin 17 → Type*} [∀ i, AddCommGroup (B i)] [∀ i, Fintype (B i)]

/-- **Lemma P with classes, deterministic core.** Trees of `2^{width i}` challenges. Claim 4's
hypotheses on the accepting set `A` for the witness rows (`u`, bit slopes `u*`) and for the label
rows (`lab`, any slopes). `key` separates the classes, `p` is a function of the witness rows.
`cert` is sound (`hsound`) and finds every class of width in `[51, 57]` that contains the free
trees of an accepting set of more than `2⁵⁰` points (`hcomplete`). Then for a free tree `i₀`:
**`clsExt` is the prefix of `i₀`, or `|A| ≤ 2⁵⁰`.** -/
theorem class_or_small (hB : ∀ i, Fintype.card (B i) = 2 ^ width i)
    {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {S : Finset (Fin 17)} {J Jl : Type*}
    {u : Fin 17 → J → Bool} {lab : Fin 17 → Jl → Bool} {Q : J → (∀ i, B i) → F}
    {QL : Jl → (∀ i, B i) → F} {uStar : J → F} {lStar : Jl → F}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) S u Q uStar)
    (hKL : Claim4Hyp e (A : Set (∀ k, B k)) S lab QL lStar)
    (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1)
    (key : Fin 17 → Kt) (hkey : ∀ i i', key i = key i' ↔ u i = u i' ∧ lab i = lab i')
    (p : Fin 17 → P) (hp : ∀ i i', u i = u i' → p i = p i')
    (cert : Fin 17 → Prop) [DecidablePred cert]
    (hsound : ∀ i ∈ S, cert i → uStar = fun j => bit (u i j))
    (hcomplete : ∀ i ∈ S, 51 ≤ grpW S key (key i) → grpW S key (key i) ≤ 57 →
      (∀ k ∉ S.filter (fun k => key k = key i), IsFixed (A : Set (∀ k, B k)) k) →
      2 ^ 50 < A.card → cert i)
    {i₀ : Fin 17} (hfree : ¬IsFixed (A : Set (∀ k, B k)) i₀) :
    clsExt S key p cert = some (p i₀) ∨ A.card ≤ 2 ^ 50 := by
  classical
  obtain ⟨hi₀S, hu₀⟩ := free_tree_holds_witness hK hbits hfree
  have hbitinj : ∀ a b : Bool, (bit a : F) = bit b → a = b := by
    intro a b h
    cases a <;> cases b <;> simp_all [bit]
  have hu_of : ∀ i, (∀ j, (bit (u i j) : F) = uStar j) → u i = u i₀ := fun i h =>
    funext fun j => hbitinj _ _ ((h j).trans (hu₀ j).symm)
  have hkp : ∀ i i', key i = key i' → p i = p i' := fun i i' h => hp _ _ ((hkey _ _).1 h).1
  -- Every tree outside the prefix group of `i₀` is fixed.
  have hfix_pg : ∀ i ∉ S.filter (fun i => p i = p i₀), IsFixed (A : Set (∀ k, B k)) i := by
    intro i hi
    by_contra hfr
    obtain ⟨hiS, hui⟩ := free_tree_holds_witness hK hbits hfr
    exact hi (mem_filter.2 ⟨hiS, hp _ _ (hu_of i hui)⟩)
  have hpow : ∀ G : Finset (Fin 17), ∏ i ∈ G, Fintype.card (B i) = 2 ^ ∑ i ∈ G, width i :=
    fun G => by simp only [hB, Finset.prod_pow_eq_pow_sum]
  -- Bit label slopes: `A` is in a slice of the class of `i₀`. Otherwise `|A|²` is at most the
  -- size of the prefix group.
  have hcase : (∀ k ∉ S.filter (fun k => key k = key i₀), IsFixed (A : Set (∀ k, B k)) k) ∨
      A.card ^ 2 ≤ 2 ^ grpW S p (p i₀) := by
    by_cases hlb : ∀ j, lStar j = 0 ∨ lStar j = 1
    · left
      obtain ⟨-, hl₀⟩ := free_tree_holds_witness hKL hlb hfree
      intro k hk
      by_contra hfr
      obtain ⟨hkS, huk⟩ := free_tree_holds_witness hK hbits hfr
      obtain ⟨-, hlk⟩ := free_tree_holds_witness hKL hlb hfr
      exact hk (mem_filter.2 ⟨hkS, (hkey _ _).2 ⟨hu_of k huk,
        funext fun j => hbitinj _ _ ((hlk j).trans (hl₀ j).symm)⟩⟩)
    · right
      push Not at hlb
      obtain ⟨j, h0, h1⟩ := hlb
      have := Seed.card_sq_le_of_nonbit_slope hKL h0 h1 _ hfix_pg
      rwa [hpow] at this
  have hsmall_of_sq : ∀ w, w ≤ 64 → A.card ^ 2 ≤ 2 ^ w → A.card ≤ 2 ^ 50 := by
    intro w hw hsq
    by_contra hgt
    push Not at hgt
    have h1 : (2 ^ 50) ^ 2 < A.card ^ 2 := Nat.pow_lt_pow_left hgt (by norm_num)
    have h2 : (2 : ℕ) ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hw
    exact absurd (h1.trans_le (hsq.trans h2)) (by norm_num)
  have hsmall_cls : (∀ k ∉ S.filter (fun k => key k = key i₀), IsFixed (A : Set (∀ k, B k)) k) →
      grpW S key (key i₀) ≤ 50 → A.card ≤ 2 ^ 50 := fun hfixc hw₀ =>
    calc A.card ≤ ∏ i ∈ S.filter (fun k => key k = key i₀), Fintype.card (B i) :=
          card_le_prod_of_fixed A _ hfixc
      _ = 2 ^ grpW S key (key i₀) := hpow _
      _ ≤ 2 ^ 50 := Nat.pow_le_pow_right (by norm_num) hw₀
  obtain ⟨i₁, hi₁S, hmaj, hmax⟩ := majTree_spec hi₀S key
  by_cases hw : 51 ≤ grpW S key (key i₁)
  · -- A class of width at least 51 exists.
    have hright : p i₀ ≠ p i₁ →
        (∀ hne : (clsCand S key p i₁).Nonempty, ¬cert ((clsCand S key p i₁).min' hne)) →
        A.card ≤ 2 ^ 50 := by
      intro hpe hnc
      rcases hcase with hfixc | hsq
      · by_cases hw₀ : 51 ≤ grpW S key (key i₀)
        · have hne : (clsCand S key p i₁).Nonempty := ⟨i₀, mem_filter.2 ⟨hi₀S, hpe, hw₀⟩⟩
          obtain ⟨hi₂S, hp₂, hw₂⟩ := mem_filter.1 (Finset.min'_mem _ hne)
          have hk12 : key ((clsCand S key p i₁).min' hne) ≠ key i₁ := fun h => hp₂ (hkp _ _ h)
          have hk₂ : key ((clsCand S key p i₁).min' hne) = key i₀ := by
            by_contra hk
            exact not_three_wide (disjoint_groups S key hk12.symm)
              (disjoint_groups S key fun h => hpe (hkp _ _ h).symm) (disjoint_groups S key hk)
              hw hw₂ hw₀
          have hw57 : grpW S key (key ((clsCand S key p i₁).min' hne)) ≤ 57 :=
            minority_weight_le _ _ (disjoint_groups S key hk12) (hmax _ hi₂S)
          by_contra hgt
          push Not at hgt
          exact hnc hne (hcomplete _ hi₂S hw₂ hw57 (by rw [hk₂]; exact hfixc) hgt)
        · exact hsmall_cls hfixc (by omega)
      · refine hsmall_of_sq _ (width_le_of_disjoint_wide ?_ hw) hsq
        exact Finset.disjoint_filter.2 fun i _ h1 h2 => hpe (h1.symm.trans (hkp _ _ h2))
    rw [clsExt_wide hmaj hw]
    split_ifs with hne hcert
    · -- The decoder found a pair: its class holds `u*`.
      obtain ⟨hi₂S, -, -⟩ := mem_filter.1 (Finset.min'_mem _ hne)
      have hs := hsound _ hi₂S hcert
      left
      rw [hp _ _ (hu_of _ fun j => by rw [hs])]
    · by_cases hpe : p i₀ = p i₁
      · left; rw [hpe]
      · exact Or.inr (hright hpe fun hne' => hcert)
    · by_cases hpe : p i₀ = p i₁
      · left; rw [hpe]
      · exact Or.inr (hright hpe fun hne' => absurd hne' hne)
  · -- No class of width 51: the widest prefix group, as in Lemma P.
    rw [clsExt_narrow hmaj hw]
    obtain ⟨ρ, hρ, hle⟩ := majP_spec hi₀S p
    by_cases hmj : p i₀ = ρ
    · left; rw [hρ, hmj]
    · right
      rcases hcase with hfixc | hsq
      · have := hmax i₀ hi₀S
        exact hsmall_cls hfixc (by omega)
      · have := minority_weight_le _ _ (disjoint_groups S p hmj) hle
        exact hsmall_of_sq _ (by unfold grpW; omega) hsq

end ClassRule

/-! ## With the decoder -/

section WithDecoder

open VoleMole.Seed

variable {P Kt : Type*} [DecidableEq P] [DecidableEq Kt]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {B : Fin 17 → Type*} [∀ i, AddCommGroup (B i)] [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]

open Classical in
/-- **Lemma P with classes and the decoder, deterministic core.** The setting of
`class_or_small`, for the KOS check value `K = kosValue c e Q D ũ` of a chain on the challenges
`Sb`. For each tree `i`, with `C i` its class, the decoder `Seed.dec` runs on a subgroup `U₀ i` of
at least `2⁷` directions of `C i`, generators `gen i` in the blocks of the trees `T₁ i`, and base
points `Rs i ⊆ Sb` that cover the slices of `C i`. Hypotheses on the first message and `chall₁`:
* `chall₁` is good for parallelism (`KOSPar`, `card_not_kosPar_le`);
* the witness rows have the tree form on `Sb`;
* the response is affine on the slices of `C i` and two-label in the blocks of `T₁ i`
  (`AffineOn`, `TwoLabelOn`; the gate model: `translateOn_gate_slice`, `twoLabel_gate`).

Then `clsExt`, with `cert i` the decoder's success, is the prefix of every free tree of the
accepting set `A`, or `|A| ≤ 2⁵⁰`. -/
theorem class_or_small_dec (hB : ∀ i, Fintype.card (B i) = 2 ^ width i)
    (h2 : ∀ x : (∀ i, B i), x + x = 0) {T : Finset F} {L ℓ : ℕ} (hℓ : ℓ ≤ L) {c : Ch F T}
    {e : (∀ i, B i) →+ F} {Sb : Set (∀ i, B i)} {A : Finset (∀ i, B i)} {S : Finset (Fin 17)}
    {Jl : Type*} {u : Fin 17 → Fin ℓ → Bool} {lab : Fin 17 → Jl → Bool}
    {Q : (∀ i, B i) → Fin L → F} {D : (∀ i, B i) → Fin 4 → F} {QL : Jl → (∀ i, B i) → F}
    {uStar : Fin ℓ → F} {lStar : Jl → F}
    (hc : KOSPar c (DisjQuads B) e Q D) (ũ h : Fin 4 → F)
    (hAS : (A : Set (∀ i, B i)) ⊆ Sb) (hacc : ∀ Δ ∈ A, kosValue c e Q D ũ Δ = h)
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) S u (fun j Δ => Q Δ (Fin.castLE hℓ j)) uStar)
    (hKL : Claim4Hyp e (A : Set (∀ k, B k)) S lab QL lStar)
    (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1)
    (htree : ∀ j, ∃ c', ∀ Δ ∈ Sb,
      Q Δ (Fin.castLE hℓ j) = c' + ∑ i ∈ S, bit (u i j) * blockLift e i (Δ i))
    (key : Fin 17 → Kt) (hkey : ∀ i i', key i = key i' ↔ u i = u i' ∧ lab i = lab i')
    (p : Fin 17 → P) (hp : ∀ i i', u i = u i' → p i = p i')
    {n : ℕ} (U₀ Rs : Fin 17 → Finset (∀ i, B i)) (gen : Fin 17 → Fin n → ∀ i, B i)
    (T₁ : Fin 17 → Finset (Fin 17))
    (hU : ∀ i ∈ S, (∀ a ∈ U₀ i, ∀ b ∈ U₀ i, a + b ∈ U₀ i) ∧
      (∀ δ ∈ U₀ i, δ ∈ dirs (S.filter fun k => key k = key i)) ∧ 2 ^ 7 ≤ (U₀ i).card)
    (hpts : ∀ i ∈ S, (∀ k, gen i k ∈ dirs (T₁ i)) ∧ (∀ r ∈ Rs i, r ∈ Sb) ∧
      (∀ δ ∈ U₀ i, ∀ r ∈ Rs i, ∀ s, decPt (gen i) r s ∈ Sb ∧ decPt (gen i) r s + δ ∈ Sb) ∧
      ∀ Δ ∈ Sb, ∃ r ∈ Rs i, ∃ s, decPt (gen i) r s ∈ Sb ∧
        ∀ k ∉ S.filter (fun k => key k = key i), decPt (gen i) r s k = Δ k)
    (hresp : ∀ i ∈ S, (∀ x ∈ Sb, ∀ δ ∈ dirs (S.filter fun k => key k = key i), x + δ ∈ Sb) ∧
      (∀ g, AffineOn (Sb ∩ slice (S.filter fun k => key k = key i) g) Q D) ∧
      TwoLabelOn Sb (S.filter fun k => key k = key i) (T₁ i) Q D)
    {i₀ : Fin 17} (hfree : ¬IsFixed (A : Set (∀ k, B k)) i₀) :
    clsExt S key p (fun i =>
        (dec (kosValue c e Q D ũ) ((U₀ i).erase 0) (Rs i) (gen i)).isSome) = some (p i₀) ∨
      A.card ≤ 2 ^ 50 := by
  refine class_or_small hB hK hKL hbits key hkey p hp _ (fun i hi hcert => ?_)
    (fun i hi hw hw57 hfix hgt => ?_) hfree
  · -- Soundness: a pair of the decoder is a certificate.
    obtain ⟨-, hUd, -⟩ := hU i hi
    obtain ⟨-, -, hSb, -⟩ := hpts i hi
    exact dec_cert_sound hℓ hc ũ h hacc hK hbits hfree htree (Finset.filter_subset _ S)
      (uC := u i) (fun k hk j => by rw [((hkey _ _).1 (mem_filter.1 hk).2).1])
      (fun δ hδ => ⟨Finset.ne_of_mem_erase hδ, hUd δ (Finset.mem_of_mem_erase hδ)⟩)
      (fun δ hδ r hr s => hSb δ (Finset.mem_of_mem_erase hδ) r hr s) hcert
  · -- Completeness: `2⁷·|A| > 2⁵⁷ ≥ ∏_{C} |B_i|`.
    obtain ⟨hadd, hUd, hcard⟩ := hU i hi
    obtain ⟨hgen, hRs, -, hcov⟩ := hpts i hi
    obtain ⟨hSbD, haff, htl⟩ := hresp i hi
    refine dec_cert_complete ũ h h2 hAS hacc hfix hSbD haff htl hadd hUd hgen hRs hcov ?_
    have hprod : ∏ k ∈ S.filter (fun k => key k = key i), Fintype.card (B k) ≤ 2 ^ 57 := by
      simp only [hB, Finset.prod_pow_eq_pow_sum]
      exact Nat.pow_le_pow_right (by norm_num) hw57
    calc ∏ k ∈ S.filter (fun k => key k = key i), Fintype.card (B k) ≤ 2 ^ 57 := hprod
      _ = 2 ^ 7 * 2 ^ 50 := by norm_num
      _ < 2 ^ 7 * A.card := Nat.mul_lt_mul_of_pos_left hgt (by norm_num)
      _ ≤ (U₀ i).card * A.card := Nat.mul_le_mul_right _ hcard

end WithDecoder

/-! ## The per-chain step (generic), and the numbers -/

section Generic

variable {F : Type*} [Field F] [CharP F 2] [DecidableEq F]
variable {B : Fin 17 → Type*} [∀ i, AddCommGroup (B i)] [∀ i, Fintype (B i)]
variable {P Kt : Type*} [DecidableEq P] [DecidableEq Kt]

open VoleMole.EndToEnd in
/-- **Lemma P with the class extractor, per chain (generic)**: `extract_or_major` with `clsExt`
in place of `majP` and `2⁵⁰` in place of `2⁵⁷`. Besides `extract_or_major`'s hypotheses: Claim 4's
hypotheses for the label rows (`hKL`), and a certificate predicate that is sound and complete on
this chain (`hsound`, `hcomplete`; for the decoder, `class_or_small_dec`). Either some tree of `S`
has a candidate satisfying `Wit` **whose prefix is the class extractor's output**, or at most
`2⁵⁰` admissible `chal3` are accepted. -/
theorem extract_or_class {Ch : Type*} {ℓ d : ℕ} (hd : 1 ≤ d) (hd50 : d ≤ 2 ^ 50)
    (hB : ∀ i, Fintype.card (B i) = 2 ^ width i)
    {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {S : Finset (Fin 17)} {u : Fin 17 → Fin ℓ → Bool}
    {Q : Fin ℓ → (∀ i, B i) → F} {uStar : Fin ℓ → F}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) S u Q uStar) {Jl : Type*} {lab : Fin 17 → Jl → Bool}
    {QL : Jl → (∀ i, B i) → F} {lStar : Jl → F}
    (hKL : Claim4Hyp e (A : Set (∀ k, B k)) S lab QL lStar) (dc : Fin ℓ → Bool)
    (cs : Arith.System F) (hdeg : ∀ x ∈ cs, x.degree ≤ d) (Wit : (ℕ → F) → Prop)
    (hWbits : ∀ w, Wit w → ∀ j < ℓ, w j = 0 ∨ w j = 1)
    (χ : Fin cs.length → F) (R : Polynomial F) (hR : R.natDegree ≤ d - 1)
    (hacc : ∀ Δ ∈ A, qsCheck cs d χ (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬cs.Holds (extW (uStar + fun j => bit (dc j))) →
      ∑ k, χ k * valVec cs (extW (uStar + fun j => bit (dc j))) k ≠ 0)
    (hcomb : cs.Holds (extW (uStar + fun j => bit (dc j))) →
      Wit (extW (uStar + fun j => bit (dc j))))
    (pf : (ℕ → F) → P)
    (key : Fin 17 → Kt) (hkey : ∀ i i', key i = key i' ↔ u i = u i' ∧ lab i = lab i')
    (cert : Fin 17 → Prop) [DecidablePred cert]
    (hsound : (∀ j, uStar j = 0 ∨ uStar j = 1) → (∃ i₀, ¬IsFixed (A : Set (∀ k, B k)) i₀) →
      ∀ i ∈ S, cert i → uStar = fun j => bit (u i j))
    (hcomplete : ∀ i ∈ S, 51 ≤ grpW S key (key i) → grpW S key (key i) ≤ 57 →
      (∀ k ∉ S.filter (fun k => key k = key i), IsFixed (A : Set (∀ k, B k)) k) →
      2 ^ 50 < A.card → cert i)
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ S, Wit (candidate u dc i) ∧
        clsExt S key (fun i => pf (candidate u dc i)) cert = some (pf (candidate u dc i))) ∨
      #{x ∈ Z | acc x} ≤ 2 ^ 50 := by
  classical
  have hcard : #{x ∈ Z | acc x} ≤ A.card := by
    refine Finset.card_le_card_of_injOn δ (fun x hx => ?_) (hδ.mono fun x hx => ?_)
    · have hx' := Finset.mem_filter.1 hx
      exact hclaim1 x hx'.1 hx'.2
    · exact (Finset.mem_filter.1 hx).1
  have hclaim3 : Wit (extW (uStar + fun j => bit (dc j))) ∨ A.card ≤ d :=
    (claim3_of_system hd hK.lift_inj (fun j => hK.consistent j) dc cs hdeg χ R hR
      (fun Δ hΔ => hacc Δ hΔ) hQS).imp_left hcomb
  rcases hclaim3 with hW | hA
  swap
  · exact Or.inr (hcard.trans (hA.trans hd50))
  have hbits : ∀ j, uStar j = 0 ∨ uStar j = 1 := by
    refine Seed.bits_of_bit_constraints (uStar + fun j => bit (dc j)) uStar (fun j => bit (dc j))
      (fun j => ?_) (fun j => by cases dc j <;> simp [bit]) rfl
    have := hWbits _ hW j j.isLt
    simp only [extW, j.isLt, dite_true] at this
    rcases this with h | h <;> simp [h, CharTwo.add_self_eq_zero]
  by_cases hfix : ∀ i, IsFixed (A : Set (∀ k, B k)) i
  · exact Or.inr (hcard.trans ((card_le_one_of_all_fixed hfix).trans (by norm_num)))
  push Not at hfix
  obtain ⟨i₀, hi₀⟩ := hfix
  obtain ⟨hk₀, hu₀⟩ := free_tree_holds_witness hK hbits hi₀
  have hcand₀ : candidate u dc i₀ = extW (uStar + fun j => bit (dc j)) := by
    unfold candidate
    congr 1
    funext j
    simp [hu₀ j]
  rcases class_or_small hB hK hKL hbits key hkey (fun i => pf (candidate u dc i))
    (fun i i' h => by unfold candidate; rw [h]) cert (hsound hbits ⟨i₀, hi₀⟩) hcomplete hi₀ with
    h | h
  · exact Or.inl ⟨i₀, hk₀, hcand₀ ▸ hW, h⟩
  · exact Or.inr (hcard.trans h)

end Generic

section Numbers

/-- Per fresh uniform 128-bit `H₂³` answer: `|A|/2¹²⁸ ≤ 2⁻⁷⁸` for `|A| ≤ 2⁵⁰`. -/
theorem per_query_bound_cls (a : ℕ) (ha : a ≤ 2 ^ 50) :
    (a : ℝ) / 2 ^ 128 ≤ (2 : ℝ)⁻¹ ^ 78 := by
  have h1 : (a : ℝ) ≤ 2 ^ 50 := by exact_mod_cast ha
  rw [div_le_iff₀ (by positivity), inv_pow]
  calc (a : ℝ) ≤ 2 ^ 50 := h1
    _ = ((2 : ℝ) ^ 78)⁻¹ * 2 ^ 128 := by norm_num

theorem loss_cls_at_2_50 : (2 : ℝ) ^ 50 * (2 : ℝ)⁻¹ ^ 78 = (2 : ℝ)⁻¹ ^ 28 := by norm_num
theorem loss_cls_at_2_64 : (2 : ℝ) ^ 64 * (2 : ℝ)⁻¹ ^ 78 = (2 : ℝ)⁻¹ ^ 14 := by norm_num

end Numbers

end VoleMole.PomFRIT
