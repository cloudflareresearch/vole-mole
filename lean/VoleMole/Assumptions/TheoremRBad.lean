import VoleMole.Assumptions.TheoremR

/-!
# Theorem R: the bad events on values

`lean/docs/security/ompr-shift-algebra.md` §2.2, step 1.
-/

open OracleComp OracleSpec VoleMole.ROM.OneMore
open scoped ENNReal

namespace VoleMole.Assumptions.TheoremR

/-- **Equality up to a nonzero scalar** on `F^m`: the class relation of UOV targets
(`Links.uovCls` is `scls GF256 45`). -/
def scls (F : Type) [Field F] (m : ℕ) (z t : Fin m → F) : Prop := ∃ μ : F, μ ≠ 0 ∧ z = μ • t

/-! ## Counting -/

section Count

/-- Split a function at `a`: the difference `δ a − δ a'` and the other values. -/
def diffEquiv {τ : ℕ} {G : Type} [AddCommGroup G] {a a' : Fin τ} (h : a' ≠ a) :
    (Fin τ → G) ≃ G × ({j // j ≠ a} → G) where
  toFun δ := (δ a - δ a', fun j => δ j.1)
  invFun x j := if hj : j = a then x.1 + x.2 ⟨a', h⟩ else x.2 ⟨j, hj⟩
  left_inv δ := by
    funext j
    by_cases hj : j = a
    · subst hj; simp
    · simp [hj]
  right_inv x := by
    ext j
    · simp [h]
    · simp [j.2]

/-- **The difference of two coordinates of a uniform function is uniform.** -/
theorem pr_diff_mem {τ : ℕ} {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [SampleableType (Fin τ → G)] {a a' : Fin τ} (h : a' ≠ a) (D : Finset G) :
    Pr{let δ ← $ᵗ (Fin τ → G)}[δ a - δ a' ∈ D] = D.card / Fintype.card G := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have h1 : (Finset.univ.filter fun δ : Fin τ → G => δ a - δ a' ∈ D).card =
      D.card * Fintype.card ({j // j ≠ a} → G) := by
    rw [← Finset.card_univ (α := {j // j ≠ a} → G), ← Finset.card_product]
    refine Finset.card_bij (fun δ _ => diffEquiv h δ) ?_ ?_ ?_
    · intro δ hδ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hδ
      simp [diffEquiv, hδ]
    · intro δ₁ _ δ₂ _ e
      exact (diffEquiv h).injective e
    · intro x hx
      refine ⟨(diffEquiv h).symm x, ?_, by simp⟩
      simp only [Finset.mem_product, Finset.mem_univ, and_true] at hx
      have : (diffEquiv h ((diffEquiv h).symm x)).1 = x.1 := by rw [Equiv.apply_symm_apply]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (diffEquiv h ((diffEquiv h).symm x)).1 ∈ D
      rw [this]; exact hx
  have h2 : Fintype.card (Fin τ → G) = Fintype.card G * Fintype.card ({j // j ≠ a} → G) := by
    rw [Fintype.card_congr (diffEquiv h), Fintype.card_prod]
  have hc : (Fintype.card ({j // j ≠ a} → G) : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card ({j // j ≠ a} → G) := Fintype.card_pos
    exact_mod_cast this.ne'
  rw [h1, h2, Nat.cast_mul, Nat.cast_mul]
  exact ENNReal.mul_div_mul_right _ _ hc (ENNReal.natCast_ne_top _)

end Count

/-! ## The bad states -/

section States

variable {DR : Type} {AR : DR → Type} {τ q : ℕ} {X : Type} {F : Type} [Field F] {m : ℕ}
  {S : Type}

local notation "𝕋" => Fin m → F

/-- The shift list cached at the prefix `hs`. -/
def lstAt (c : (specR (WA AR τ q 𝕋)).QueryCache) (hs : List 𝕋) : Option (Fin τ → 𝕋) :=
  c (.inr (.inl hs))

/-- The prefixes whose shift list is cached. -/
def lists (s : JSt AR τ q X 𝕋 S) : Set (List 𝕋) := {hs | lstAt s.2.ro hs ≠ none}

/-- **(E3) as a property of the state**: a cached shift list has two equal shifts, or two shifts
whose difference is `μ·w − μ'·w'` for targets `w`, `w'` drawn so far. Then a prefix exists for
which both candidates are useful. -/
def E3 (s : JSt AR τ q X 𝕋 S) : Prop :=
  ∃ hs δ, lstAt s.2.ro hs = some δ ∧ ∃ a a' : Fin τ, a ≠ a' ∧
    (δ a = δ a' ∨ ∃ w ∈ s.1.tl, ∃ w' ∈ s.1.tl, ∃ μ μ' : F, δ a - δ a' = μ • w - μ' • w')

/-- The bad states: `M`'s flag, or (E3). -/
def Ebad (s : JSt AR τ q X 𝕋 S) : Prop := s.1.bad = true ∨ E3 s

variable [DecidableEq F]

/-- The number of `M`'s calls that may not be charged (the uncounted candidates). -/
def nonchg (s : JSt AR τ q X 𝕋 S) : ℕ := s.1.calls.countP fun z => decide (z ∉ s.1.chg)

variable [Fintype F]

/-- **The values a new target must avoid**: `0`, the classes of the targets and of the uncharged
calls, and for every cached list `δ` and shifts `a, a'` the points that would make (E3) true. -/
def tgtBad (tl calls chg : List 𝕋) (L : Finset (List 𝕋)) (c : (specR (WA AR τ q 𝕋)).QueryCache) :
    Finset 𝕋 :=
  {0} ∪ tl.toFinset.biUnion (fun t' => Finset.univ.image fun μ : F => μ • t') ∪
    (calls.filter fun z => decide (z ∉ chg)).toFinset.biUnion
      (fun z => Finset.univ.image fun μ : F => μ • z) ∪
    L.biUnion fun hs => (Finset.univ : Finset (Fin τ × Fin τ)).biUnion fun p =>
      ((Finset.univ ×ˢ Finset.univ ×ˢ tl.toFinset).image fun x : F × F × 𝕋 =>
          x.1 • ((lstAt c hs).getD 0 p.1 - (lstAt c hs).getD 0 p.2 + x.2.1 • x.2.2)) ∪
        Finset.univ.image fun ν : F => ν • ((lstAt c hs).getD 0 p.1 - (lstAt c hs).getD 0 p.2)

theorem card_tgtBad (tl calls chg : List 𝕋) (L : Finset (List 𝕋))
    (c : (specR (WA AR τ q 𝕋)).QueryCache) :
    (tgtBad tl calls chg L c).card ≤
      1 + tl.length * Fintype.card F +
        calls.countP (fun z => decide (z ∉ chg)) * Fintype.card F +
        L.card * (τ * τ * (Fintype.card F * Fintype.card F * tl.length + Fintype.card F)) := by
  unfold tgtBad
  refine (Finset.card_union_le _ _).trans (add_le_add ((Finset.card_union_le _ _).trans
    (add_le_add ((Finset.card_union_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
  · simp
  · refine (Finset.card_biUnion_le).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (Fintype.card F) fun t _ => ?_).trans ?_
    · exact Finset.card_image_le.trans (by simp)
    · simpa using Nat.mul_le_mul_right _ (List.toFinset_card_le tl)
  · refine (Finset.card_biUnion_le).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (Fintype.card F) fun t _ => ?_).trans ?_
    · exact Finset.card_image_le.trans (by simp)
    · simp only [smul_eq_mul]
      refine Nat.mul_le_mul_right _ ((List.toFinset_card_le _).trans ?_)
      rw [List.countP_eq_length_filter]
  · refine (Finset.card_biUnion_le).trans ?_
    refine (Finset.sum_le_card_nsmul _ _
      (τ * τ * (Fintype.card F * Fintype.card F * tl.length + Fintype.card F))
      fun hs _ => ?_).trans (by simp)
    refine (Finset.card_biUnion_le).trans ?_
    refine (Finset.sum_le_card_nsmul _ _
      (Fintype.card F * Fintype.card F * tl.length + Fintype.card F) fun p _ => ?_).trans
      (by simp)
    refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
    · refine Finset.card_image_le.trans ?_
      simp only [Finset.card_product, Finset.card_univ, ← mul_assoc]
      exact Nat.mul_le_mul_left _ (List.toFinset_card_le tl)
    · exact Finset.card_image_le.trans (by simp)

variable [DecidableRel (scls F m)]

/-- **A new target that makes the state bad lies in `tgtBad`.** The step draws `t`, adds it to the
targets, leaves the cache alone, and sets `bad` as `MSt.addT` does. -/
theorem draw_mem {s s' : JSt AR τ q X 𝕋 S} {t : 𝕋} (L : Finset (List 𝕋))
    (hL : ∀ hs, lstAt s.2.ro hs ≠ none → hs ∈ L)
    (hro : s'.2.ro = s.2.ro) (htl : s'.1.tl = t :: s.1.tl)
    (hbad : s'.1.bad = (s.1.bad || decide (t = 0) ||
      s.1.tl.any (fun t' => decide (scls F m t t')) ||
      s.1.calls.any fun z => decide (scls F m z t) && decide (z ∉ s.1.chg)))
    (hs : ¬ Ebad s) (hs' : Ebad s') : t ∈ tgtBad s.1.tl s.1.calls s.1.chg L s.2.ro := by
  have hb : s.1.bad = false := by
    cases h : s.1.bad
    · rfl
    · exact absurd (Or.inl h) hs
  have hE : ¬ E3 s := fun h => hs (Or.inr h)
  unfold tgtBad
  simp only [Finset.mem_union]
  rcases hs' with hb' | ⟨hs₀, δ, hδ, a, a', hne, hcase⟩
  · rw [hbad, hb] at hb'
    simp only [Bool.false_or, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
      Bool.and_eq_true] at hb'
    rcases hb' with (h0 | ⟨t', ht', μ, -, rfl⟩) | ⟨z, hz, ⟨μ, hμ, rfl⟩, hzc⟩
    · exact Or.inl (Or.inl (Or.inl (by simp [h0])))
    · refine Or.inl (Or.inl (Or.inr ?_))
      exact Finset.mem_biUnion.mpr ⟨t', List.mem_toFinset.mpr ht', Finset.mem_image.mpr
        ⟨μ, Finset.mem_univ _, rfl⟩⟩
    · refine Or.inl (Or.inr ?_)
      refine Finset.mem_biUnion.mpr ⟨μ • t, ?_, Finset.mem_image.mpr
        ⟨μ⁻¹, Finset.mem_univ _, by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]⟩⟩
      exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hz, by simpa using hzc⟩)
  · rw [hro] at hδ
    have hmem : hs₀ ∈ L := hL _ (by rw [hδ]; simp)
    have hg : (lstAt s.2.ro hs₀).getD 0 = δ := by rw [hδ]; rfl
    rw [htl] at hcase
    rcases hcase with heq | ⟨w, hw, w', hw', μ, μ', hd⟩
    · exact absurd ⟨hs₀, δ, hδ, a, a', hne, Or.inl heq⟩ hE
    refine Or.inr (Finset.mem_biUnion.mpr ⟨hs₀, hmem, Finset.mem_biUnion.mpr
      ⟨(a, a'), Finset.mem_univ _, ?_⟩⟩)
    simp only [hg, Finset.mem_union, Finset.mem_image, Finset.mem_product, Finset.mem_univ,
      true_and, List.mem_toFinset, Prod.exists]
    rcases List.mem_cons.mp hw with hwt | hwl <;> rcases List.mem_cons.mp hw' with hwt' | hwl'
    · rw [hwt, hwt'] at hd
      by_cases hμ : μ = μ'
      · subst hμ
        exact absurd ⟨hs₀, δ, hδ, a, a', hne, Or.inl (sub_eq_zero.mp (by rw [hd, sub_self]))⟩ hE
      · refine Or.inr ⟨(μ - μ')⁻¹, ?_⟩
        rw [hd, ← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hμ), one_smul]
    · rw [hwt] at hd
      by_cases hμ : μ = 0
      · subst hμ
        exact absurd ⟨hs₀, δ, hδ, a, a', hne, Or.inr ⟨w', hwl', w', hwl', 0, μ', by
          rw [hd, zero_smul, zero_smul]⟩⟩ hE
      · refine Or.inl ⟨μ⁻¹, μ', w', hwl', ?_⟩
        rw [hd, sub_add_cancel, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    · rw [hwt'] at hd
      by_cases hμ : μ' = 0
      · subst hμ
        exact absurd ⟨hs₀, δ, hδ, a, a', hne, Or.inr ⟨w, hwl, w, hwl, μ, 0, by
          rw [hd, zero_smul, zero_smul]⟩⟩ hE
      · refine Or.inl ⟨-μ'⁻¹, -μ, w, hwl, ?_⟩
        rw [hd, show μ • w - μ' • t + -μ • w = (-μ') • t by module, smul_smul, neg_mul_neg,
          inv_mul_cancel₀ hμ, one_smul]
    · exact absurd ⟨hs₀, δ, hδ, a, a', hne, Or.inr ⟨w, hwl, w', hwl', μ, μ', hd⟩⟩ hE

/-- **The differences a new shift list must avoid** for each pair of its shifts: `0` and
`μ·w − μ'·w'` for targets `w`, `w'`. -/
def lstBad (tl : List 𝕋) : Finset 𝕋 :=
  insert 0 ((Finset.univ ×ˢ Finset.univ ×ˢ tl.toFinset ×ˢ tl.toFinset).image
    fun x : F × F × 𝕋 × 𝕋 => x.1 • x.2.2.1 - x.2.1 • x.2.2.2)

omit [DecidableRel (scls F m)] in
theorem card_lstBad (tl : List 𝕋) :
    (lstBad tl).card ≤ 1 + Fintype.card F * Fintype.card F * (tl.length * tl.length) := by
  unfold lstBad
  refine (Finset.card_insert_le _ _).trans ?_
  rw [add_comm]
  refine Nat.add_le_add_left (Finset.card_image_le.trans ?_) _
  simp only [Finset.card_product, Finset.card_univ, ← mul_assoc]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (List.toFinset_card_le tl))
    (List.toFinset_card_le tl)

omit [DecidableRel (scls F m)] in
/-- **A new shift list that makes the state bad has two shifts with a difference in `lstBad`.** -/
theorem lst_mem [DecidableEq (List 𝕋)] {s s' : JSt AR τ q X 𝕋 S} {hk : List 𝕋}
    {δ : Fin τ → 𝕋} (h1 : s'.1 = s.1)
    (hro : ∀ hs', lstAt s'.2.ro hs' = if hs' = hk then some δ else lstAt s.2.ro hs')
    (hs : ¬ Ebad s) (hs' : Ebad s') : ∃ p : Fin τ × Fin τ, p.2 ≠ p.1 ∧
      δ p.1 - δ p.2 ∈ lstBad s.1.tl := by
  have hb : s.1.bad = false := by
    cases h : s.1.bad
    · rfl
    · exact absurd (Or.inl h) hs
  have hE : ¬ E3 s := fun h => hs (Or.inr h)
  rcases hs' with hb' | ⟨hs₀, δ', hδ, a, a', hne, hcase⟩
  · rw [h1, hb] at hb'; cases hb'
  rw [hro] at hδ
  rw [h1] at hcase
  split_ifs at hδ with he
  · cases hδ
    refine ⟨(a, a'), Ne.symm hne, ?_⟩
    unfold lstBad
    rcases hcase with heq | ⟨w, hw, w', hw', μ, μ', hd⟩
    · exact Finset.mem_insert.mpr (Or.inl (by simp [heq]))
    · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨(μ, μ', w, w'), ?_, hd.symm⟩))
      simp [hw, hw']
  · exact absurd ⟨hs₀, δ', hδ, a, a', hne, hcase⟩ hE

end States

/-! ## The risk of one draw -/

section Risk

variable {DR : Type} {AR : DR → Type} {τ q : ℕ} {X : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m : ℕ} [SampleableType (Fin m → F)] {S : Type} [DecidableRel (scls F m)]

local notation "𝕋" => Fin m → F

/-- **The risk of a target draw.** -/
theorem pr_draw_le {β : Type} (s : JSt AR τ q X 𝕋 S) (g : 𝕋 → β × JSt AR τ q X 𝕋 S)
    (L : Finset (List 𝕋)) (hL : ∀ hs, lstAt s.2.ro hs ≠ none → hs ∈ L)
    (hro : ∀ t, (g t).2.2.ro = s.2.ro) (htl : ∀ t, (g t).2.1.tl = t :: s.1.tl)
    (hbad : ∀ t, (g t).2.1.bad = (s.1.bad || decide (t = 0) ||
      s.1.tl.any (fun t' => decide (scls F m t t')) ||
      s.1.calls.any fun z => decide (scls F m z t) && decide (z ∉ s.1.chg)))
    (hs : ¬ Ebad s) :
    Pr{let z ← g <$> ($ᵗ 𝕋)}[Ebad z.2] ≤
      (tgtBad s.1.tl s.1.calls s.1.chg L s.2.ro).card / Fintype.card 𝕋 := by
  classical
  rw [prEvent_map]
  refine (prEvent_mono _ _ (fun t => t ∈ tgtBad s.1.tl s.1.calls s.1.chg L s.2.ro)
    fun t ht => draw_mem L hL (hro t) (htl t) (hbad t) hs ht).trans (le_of_eq ?_)
  rw [SampleableType.prEvent_uniformSample, Finset.filter_mem_eq_inter, Finset.univ_inter]

omit [SampleableType (Fin m → F)] [DecidableRel (scls F m)] in
/-- **The risk of a shift-list draw.** -/
theorem pr_lst_le [DecidableEq (List 𝕋)] [SampleableType (Fin τ → 𝕋)] {β : Type}
    (s : JSt AR τ q X 𝕋 S) (hs₀ : List 𝕋) (g : (Fin τ → 𝕋) → β × JSt AR τ q X 𝕋 S)
    (h1 : ∀ δ, (g δ).2.1 = s.1)
    (hro : ∀ δ hs', lstAt (g δ).2.2.ro hs' = if hs' = hs₀ then some δ else lstAt s.2.ro hs')
    (hs : ¬ Ebad s) :
    Pr{let z ← g <$> ($ᵗ (Fin τ → 𝕋))}[Ebad z.2] ≤
      (τ * τ * (lstBad s.1.tl).card : ℕ) / Fintype.card 𝕋 := by
  classical
  rw [prEvent_map]
  refine (prEvent_mono _ _ (fun δ => ∃ p : Fin τ × Fin τ, p.2 ≠ p.1 ∧
      δ p.1 - δ p.2 ∈ lstBad s.1.tl) fun δ hδ => lst_mem (h1 δ) (hro δ) hs hδ).trans ?_
  refine (prEvent_exists_le_card_mul _ _ (ε := (lstBad s.1.tl).card / Fintype.card 𝕋)
    fun p => ?_).trans (le_of_eq ?_)
  · by_cases hp : p.2 = p.1
    · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun δ _ h => h.1 hp]
      exact bot_le
    · exact (prEvent_mono _ _ _ fun δ h => h.2).trans (le_of_eq (pr_diff_mem hp _))
  · simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    rw [mul_div_assoc]

end Risk

/-! ## The steps of the joint experiment -/

section Steps

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {τ q : ℕ} [NeZero τ] {X : Type} [DecidableEq X] {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m : ℕ} [SampleableType (Fin m → F)] {S : Type} [DecidableRel (scls F m)]
  {PK : Type} (rel : PK → S → (Fin m → F) → Prop) [∀ pk s t, Decidable (rel pk s t)]
  (pk : PK) (pre : (Fin m → F) → S)

local notation "𝕋" => Fin m → F

/-- How much one stretch of the run may grow the quantities the risks depend on: targets drawn
and remaining (`tl` with `rem`), cached lists, uncharged calls, junk targets, completed runs. -/
structure Dlt (s s' : JSt AR τ q X 𝕋 S) (dt dl dc dj dk : ℕ) : Prop where
  tl : s'.1.tl.length + s'.1.rem ≤ s.1.tl.length + s.1.rem + dt
  rem : s'.1.rem ≤ s.1.rem
  ls : (lists s').encard ≤ (lists s).encard + dl
  nc : nonchg s' ≤ nonchg s + dc
  nj : s'.1.nj ≤ s.1.nj + dj
  K : s'.1.K ≤ s.1.K + dk

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [DecidableEq X] [Field F] [Fintype F]
  [SampleableType (Fin m → F)] [DecidableRel (scls F m)] in
theorem Dlt.trans {s s' s'' : JSt AR τ q X 𝕋 S} {a b c d e a' b' c' d' e' : ℕ}
    (h : Dlt s s' a b c d e) (h' : Dlt s' s'' a' b' c' d' e') :
    Dlt s s'' (a + a') (b + b') (c + c') (d + d') (e + e') where
  tl := by have := h.tl; have := h'.tl; omega
  rem := h'.rem.trans h.rem
  ls := by
    refine h'.ls.trans ?_
    push_cast
    rw [← add_assoc]
    exact add_le_add h.ls le_rfl
  nc := by have := h.nc; have := h'.nc; omega
  nj := by have := h.nj; have := h'.nj; omega
  K := by have := h.K; have := h'.K; omega

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [DecidableEq X] [Field F] [Fintype F]
  [SampleableType (Fin m → F)] [DecidableRel (scls F m)] in
theorem Dlt.mono {s s' : JSt AR τ q X 𝕋 S} {a b c d e a' b' c' d' e' : ℕ}
    (h : Dlt s s' a b c d e) (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hd : d ≤ d')
    (he : e ≤ e') : Dlt s s' a' b' c' d' e' where
  tl := by have := h.tl; omega
  rem := h.rem
  ls := h.ls.trans (add_le_add le_rfl (by exact_mod_cast hb))
  nc := by have := h.nc; omega
  nj := by have := h.nj; omega
  K := by have := h.K; omega

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [DecidableEq X] [Fintype F]
  [SampleableType (Fin m → F)] [DecidableRel (scls F m)] in
/-- A step that changes neither `M`'s state nor the cached lists. -/
theorem same_of {s s' : JSt AR τ q X 𝕋 S} (h1 : s'.1 = s.1)
    (h2 : ∀ hs, lstAt s'.2.ro hs = lstAt s.2.ro hs) :
    (Ebad s' ↔ Ebad s) ∧ Dlt s s' 0 0 0 0 0 := by
  have hl : lists s' = lists s := by ext hs; simp [lists, h2]
  refine ⟨?_, ⟨by simp [h1], by simp [h1], by rw [hl]; simp, by simp [nonchg, h1], by simp [h1],
    by simp [h1]⟩⟩
  simp only [Ebad, E3, h1, h2]

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [DecidableEq X] [Field F] [DecidableEq F] [Fintype F]
  [SampleableType (Fin m → F)] [DecidableRel (scls F m)] in
theorem exists_L (s : JSt AR τ q X 𝕋 S) {NL : ℕ} (h : (lists s).encard ≤ NL) :
    ∃ L : Finset (List 𝕋), (∀ hs, lstAt s.2.ro hs ≠ none → hs ∈ L) ∧ L.card ≤ NL := by
  have hfin : (lists s).Finite := Set.finite_of_encard_le_coe h
  refine ⟨hfin.toFinset, fun hs h => hfin.mem_toFinset.mpr h, ?_⟩
  rw [hfin.encard_eq_coe_toFinset_card] at h
  exact_mod_cast h

/-- The numerator of the risk of a target draw, with at most `NT` targets, `NL` cached lists and
`NC` uncharged calls. -/
def cT (τ Q NT NL NC : ℕ) : ℕ := 1 + NT * Q + NC * Q + NL * (τ * τ * (Q * Q * NT + Q))

/-- The numerator of the risk of a shift-list draw, with at most `NT` targets. -/
def cL (τ Q NT : ℕ) : ℕ := τ * τ * (1 + Q * Q * (NT * NT))

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [DecidableEq X]
  [SampleableType (Fin m → F)] [DecidableRel (scls F m)] in
theorem card_tgtBad_le (s : JSt AR τ q X 𝕋 S) (L : Finset (List 𝕋)) {NT NL NC : ℕ}
    (hT : s.1.tl.length ≤ NT) (hL : L.card ≤ NL) (hC : nonchg s ≤ NC) :
    (tgtBad s.1.tl s.1.calls s.1.chg L s.2.ro).card ≤ cT τ (Fintype.card F) NT NL NC := by
  refine (card_tgtBad _ _ _ _ _).trans ?_
  unfold cT
  have h1 := Nat.mul_le_mul_right (Fintype.card F) hT
  have h2 := Nat.mul_le_mul_right (Fintype.card F) hC
  have h3 : Fintype.card F * Fintype.card F * s.1.tl.length + Fintype.card F ≤
      Fintype.card F * Fintype.card F * NT + Fintype.card F :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ hT) _
  have h4 := Nat.mul_le_mul hL (Nat.mul_le_mul_left (τ * τ) h3)
  unfold nonchg at h2
  omega

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [DecidableEq X]
  [SampleableType (Fin m → F)] [DecidableRel (scls F m)] in
theorem card_lstBad_le (tl : List 𝕋) {NT : ℕ} (hT : tl.length ≤ NT) :
    τ * τ * (lstBad tl).card ≤ cL τ (Fintype.card F) NT := by
  unfold cL
  refine Nat.mul_le_mul_left _ ((card_lstBad tl).trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul hT hT)) _))

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [DecidableEq X] [Fintype F]
  [SampleableType (Fin m → F)] in
/-- **(E3) covers the bad event of a completion**: if a candidate of the run is useful but not
counted, two shifts of one cached list are useful. -/
theorem complete_E3 (s : JSt AR τ q X 𝕋 S) (H : List 𝕋) (δs : List (Fin τ → 𝕋)) (ans : List S)
    (a : Fin (q + 1) → Fin τ) (ss : List S) (hb : s.1.bad = false)
    (hc : ∀ k : Fin (q + 1), lstAt s.2.ro (H.take k) = some (δs.getD k 0))
    (h : (s.1.complete (scls F m) H δs ans a ss).bad = true) : E3 s := by
  simp only [MSt.complete, hb, Bool.false_or, List.any_eq_true, List.mem_finRange, true_and,
    Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨k, hu, hf⟩ := h
  have hsome : (firstU (scls F m) s.1.tl H δs k).isSome := by
    unfold firstU
    exact List.find?_isSome.mpr ⟨a k, List.mem_finRange _, hu⟩
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp hsome
  have hu' := List.find?_some ha'
  have hne : a' ≠ a k := fun e => hf (by rw [ha', e])
  simp only [useful, List.any_eq_true, decide_eq_true_eq] at hu hu'
  obtain ⟨w', hw', μ', -, h2⟩ := hu
  obtain ⟨w, hw, μ, -, h1⟩ := hu'
  refine ⟨H.take k, δs.getD k 0, hc k, a', a k, hne, Or.inr ⟨w, hw, w', hw', μ, μ', ?_⟩⟩
  rw [← h1, ← h2]
  abel

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [DecidableEq X]
  [SampleableType (Fin m → F)] [DecidableEq F] [Fintype F] [DecidableRel (scls F m)] in
theorem pr_le_of_support {β : Type} (mx : ProbComp (β × JSt AR τ q X 𝕋 S)) (ε : ℝ≥0∞)
    (h : ∀ z ∈ support mx, ¬ Ebad z.2) : Pr{let z ← mx}[Ebad z.2] ≤ ε := by
  rw [prEvent_eq_zero_of_forall_mem_support _ _ h]
  exact bot_le

omit [Fintype F] in
/-- The world: nothing changes. -/
theorem step_w (d : DR) (s : JSt AR τ q X 𝕋 S) :
    ∀ z ∈ support ((jImpl (scls F m) rel pk pre (.w d)).run s),
      (Ebad z.2 ↔ Ebad s) ∧ Dlt s z.2 0 0 0 0 0 := by
  intro z hz
  rw [j_w] at hz
  erw [support_map] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  exact same_of rfl fun hs => ro_other _ _ r hr _ (by simp)

omit [∀ d, SampleableType (AR d)] [NeZero τ] [DecidableEq X] [Field F] [Fintype F]
  [SampleableType (Fin m → F)] [DecidableRel (scls F m)] in
theorem lstAt_cacheQuery (c : (specR (WA AR τ q 𝕋)).QueryCache) (hs : List 𝕋) (δ : Fin τ → 𝕋)
    (hs' : List 𝕋) :
    lstAt (c.cacheQuery (.inr (.inl hs)) δ) hs' = if hs' = hs then some δ else lstAt c hs' := by
  by_cases he : hs' = hs
  · subst he
    simp only [↓reduceIte]
    exact QueryCache.cacheQuery_self (spec := specR (WA AR τ q 𝕋)) c (Sum.inr (Sum.inl hs')) δ
  · simp only [he, ↓reduceIte]
    exact QueryCache.cacheQuery_of_ne (spec := specR (WA AR τ q 𝕋)) c
      (t' := Sum.inr (Sum.inl hs')) (t := Sum.inr (Sum.inl hs)) δ (by simpa using he)

omit [Fintype F] in
theorem run_lst_some (hs : List 𝕋) (s : JSt AR τ q X 𝕋 S) (u : Fin τ → 𝕋)
    (hc : lstAt s.2.ro hs = some u) :
    (jImpl (scls F m) rel pk pre (.lst hs)).run s = pure (u, s) := by
  rw [j_lst, randomOracle.run_eq]
  unfold lstAt at hc
  simp only [hc, map_pure]
  rfl

omit [Fintype F] in
theorem run_lst_none (hs : List 𝕋) (s : JSt AR τ q X 𝕋 S) (hc : lstAt s.2.ro hs = none) :
    (jImpl (scls F m) rel pk pre (.lst hs)).run s =
      (fun δ : Fin τ → 𝕋 => (δ, (s.1, { s.2 with ro := s.2.ro.cacheQuery (.inr (.inl hs)) δ }))) <$>
        ($ᵗ (Fin τ → 𝕋)) := by
  rw [j_lst, randomOracle.run_eq]
  unfold lstAt at hc
  simp only [hc, map_bind, map_pure]
  exact (map_eq_bind_pure_comp _ _ _).symm

omit [Fintype F] in
/-- A shift list: `M`'s state is unchanged; the list at `hs` is the answer and is cached; the
other lists are unchanged. -/
theorem step_lst (hs : List 𝕋) (s : JSt AR τ q X 𝕋 S) :
    ∀ z ∈ support ((jImpl (scls F m) rel pk pre (.lst hs)).run s),
      z.2.1 = s.1 ∧ lstAt z.2.2.ro hs = some z.1 ∧
      (∀ hs', hs' ≠ hs → lstAt z.2.2.ro hs' = lstAt s.2.ro hs') ∧
      (∀ v, lstAt s.2.ro hs = some v → z.1 = v) := by
  intro z hz
  cases hc : lstAt s.2.ro hs with
  | some u =>
    rw [run_lst_some rel pk pre hs s u hc, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, hc, fun _ _ => rfl, fun v hv => Option.some.inj hv⟩
  | none =>
    rw [run_lst_none rel pk pre hs s hc] at hz
    erw [support_map] at hz
    obtain ⟨δ, -, rfl⟩ := hz
    refine ⟨rfl, by simp [lstAt_cacheQuery], fun hs' hne => by simp [lstAt_cacheQuery, hne],
      fun v hv => by cases hv⟩

omit [Fintype F] in
theorem step_lst_dlt (hs : List 𝕋) (s : JSt AR τ q X 𝕋 S) :
    ∀ z ∈ support ((jImpl (scls F m) rel pk pre (.lst hs)).run s), Dlt s z.2 0 1 0 0 0 := by
  intro z hz
  obtain ⟨h1, -, h3, -⟩ := step_lst rel pk pre hs s z hz
  have hl : lists z.2 ⊆ insert hs (lists s) := fun hs' h => by
    by_cases he : hs' = hs
    · exact Or.inl he
    · exact Or.inr (by simpa [lists, h3 hs' he] using h)
  refine ⟨by simp [h1], by simp [h1], ?_, by simp [nonchg, h1], by simp [h1], by simp [h1]⟩
  exact (Set.encard_le_encard hl).trans (by simpa using Set.encard_insert_le _ _)

theorem pr_lst (hs : List 𝕋) (s : JSt AR τ q X 𝕋 S) {NT : ℕ} (hs₀ : ¬ Ebad s)
    (hT : s.1.tl.length ≤ NT) :
    Pr{let z ← (jImpl (scls F m) rel pk pre (.lst hs)).run s}[Ebad z.2] ≤
      cL τ (Fintype.card F) NT / Fintype.card 𝕋 := by
  cases hc : lstAt s.2.ro hs with
  | some u =>
    rw [run_lst_some rel pk pre hs s u hc]
    refine pr_le_of_support _ _ fun z hz => ?_
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs₀
  | none =>
    rw [run_lst_none rel pk pre hs s hc]
    refine (pr_lst_le s hs
      (fun δ => (δ, (s.1, { s.2 with ro := s.2.ro.cacheQuery (.inr (.inl hs)) δ })))
      (fun _ => rfl) (fun δ hs' => ?_) hs₀).trans ?_
    · exact lstAt_cacheQuery _ _ _ _
    · exact ENNReal.div_le_div_right (by exact_mod_cast card_lstBad_le _ hT) _

omit [Fintype F] in
/-- A challenge target. -/
theorem step_tgt (x : X) (s : JSt AR τ q X 𝕋 S) :
    ∀ z ∈ support ((jImpl (scls F m) rel pk pre (.tgt x)).run s),
      Dlt s z.2 0 0 0 0 0 ∧ (s.1.rem = 0 → (Ebad z.2 ↔ Ebad s)) ∧
        (s.1.rem ≠ 0 → z.2.1.rem + 1 = s.1.rem) := by
  intro z hz
  by_cases h : s.1.rem = 0
  · rw [j_tgt_zero _ _ _ _ _ _ h] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨(same_of rfl fun _ => rfl).2, fun _ => Iff.rfl, fun h' => absurd h h'⟩
  · rw [j_tgt _ _ _ _ _ _ h] at hz
    erw [support_map] at hz
    obtain ⟨t, -, rfl⟩ := hz
    refine ⟨⟨?_, by simp, by simp [lists, lstAt], ?_, by simp [MSt.addT], by simp [MSt.addT]⟩,
      fun h' => absurd h' h, fun _ => by simp; omega⟩
    · simp [MSt.addT]; omega
    · simp [nonchg, MSt.addT]

theorem pr_tgt (x : X) (s : JSt AR τ q X 𝕋 S) {NT NL NC : ℕ} (hs₀ : ¬ Ebad s)
    (hT : s.1.tl.length ≤ NT) (hL : (lists s).encard ≤ NL) (hC : nonchg s ≤ NC)
    (h : s.1.rem ≠ 0) :
    Pr{let z ← (jImpl (scls F m) rel pk pre (.tgt x)).run s}[Ebad z.2] ≤
      cT τ (Fintype.card F) NT NL NC / Fintype.card 𝕋 := by
  rw [j_tgt _ _ _ _ _ _ h]
  obtain ⟨L, hLs, hLc⟩ := exists_L s hL
  refine (pr_draw_le s _ L hLs (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hs₀).trans ?_
  exact ENNReal.div_le_div_right (by exact_mod_cast card_tgtBad_le s L hT hLc hC) _

omit [Fintype F] in
/-- A junk target. -/
theorem step_junk (H : List 𝕋) (j : ℕ) (s : JSt AR τ q X 𝕋 S) :
    ∀ z ∈ support ((jImpl (scls F m) rel pk pre (.junk H j)).run s), Dlt s z.2 1 0 0 1 0 := by
  intro z hz
  cases h : s.1.tg (.inr (H, j)) with
  | some t =>
    rw [j_junk_some _ _ _ _ _ _ _ t h] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact (same_of rfl fun _ => rfl).2.mono (by omega) le_rfl le_rfl (by omega) le_rfl
  | none =>
    rw [j_junk _ _ _ _ _ _ _ h] at hz
    erw [support_map] at hz
    obtain ⟨t, -, rfl⟩ := hz
    exact ⟨by simp [MSt.addT]; omega, by simp [MSt.addT], by simp [lists, lstAt],
      by simp [nonchg, MSt.addT], by simp, by simp [MSt.addT]⟩

theorem pr_junk (H : List 𝕋) (j : ℕ) (s : JSt AR τ q X 𝕋 S) {NT NL NC : ℕ} (hs₀ : ¬ Ebad s)
    (hT : s.1.tl.length ≤ NT) (hL : (lists s).encard ≤ NL) (hC : nonchg s ≤ NC) :
    Pr{let z ← (jImpl (scls F m) rel pk pre (.junk H j)).run s}[Ebad z.2] ≤
      cT τ (Fintype.card F) NT NL NC / Fintype.card 𝕋 := by
  cases h : s.1.tg (.inr (H, j)) with
  | some t =>
    rw [j_junk_some _ _ _ _ _ _ _ t h]
    refine pr_le_of_support _ _ fun z hz => ?_
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs₀
  | none =>
    rw [j_junk _ _ _ _ _ _ _ h]
    obtain ⟨L, hLs, hLc⟩ := exists_L s hL
    refine (pr_draw_le s _ L hLs (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hs₀).trans ?_
    exact ENNReal.div_le_div_right (by exact_mod_cast card_tgtBad_le s L hT hLc hC) _

omit [Fintype F] in
/-- A call of the reduction: it is charged, so nothing that matters changes. -/
theorem step_inv (t : 𝕋) (s : JSt AR τ q X 𝕋 S) :
    ∀ z ∈ support ((jImpl (scls F m) rel pk pre (.inv t)).run s),
      (Ebad z.2 ↔ Ebad s) ∧ Dlt s z.2 0 0 0 0 0 := by
  intro z hz
  rw [j_inv] at hz
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  refine ⟨by simp [Ebad, E3, lstAt], ⟨by simp, by simp, by simp [lists, lstAt], ?_, by simp,
    by simp⟩⟩
  simp only [nonchg, List.countP_cons, List.mem_cons, true_or, not_true_eq_false,
    decide_false, Bool.false_eq_true, ↓reduceIte, add_zero]
  exact List.countP_mono_left fun z _ h => by simp_all

omit [Fintype F] in
/-- The output of a run. A completion adds at most `q + 1` uncharged calls and one run; it
makes the state bad only if (E3) held, when the lists of the run are the cached ones. -/
theorem step_fin (H : List 𝕋) (δs : List (Fin τ → 𝕋)) (ans : List S) (s : JSt AR τ q X 𝕋 S) :
    ∀ z ∈ support ((jImpl (scls F m) rel pk pre (.fin H δs ans)).run s),
      Dlt s z.2 0 0 (q + 1) 0 1 ∧
      (¬ Ebad s → (∀ k : Fin (q + 1), lstAt s.2.ro (H.take k) = some (δs.getD k 0)) →
        ¬ Ebad z.2) := by
  intro z hz
  have hsame : (Ebad s ↔ Ebad s) ∧ Dlt s s 0 0 0 0 0 := same_of rfl fun _ => rfl
  cases hv : valid (q := q) rel pk (fun k => s.1.tg (.inr k)) H ans with
  | false =>
    rw [j_fin_invalid _ _ _ _ _ _ _ _ hv] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hsame.2.mono le_rfl le_rfl (by omega) le_rfl (by omega), fun h _ => h⟩
  | true =>
    cases ho : s.1.out H with
    | some o =>
      rw [j_fin_some _ _ _ _ _ _ _ _ hv o ho] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hsame.2.mono le_rfl le_rfl (by omega) le_rfl (by omega), fun h _ => h⟩
    | none =>
      rw [j_fin _ _ _ _ _ _ _ _ hv ho] at hz
      erw [support_map] at hz
      obtain ⟨r, hr, rfl⟩ := hz
      have hro : ∀ hs, lstAt r.2 hs = lstAt s.2.ro hs := fun hs =>
        ro_other _ _ r hr _ (by simp)
      have hl : lists (s.1.complete (scls F m) H δs ans r.1 ((cands H δs r.1).map pre),
          { s.2 with ro := r.2, calls := (cands H δs r.1).reverse ++ s.2.calls }) = lists s := by
        ext hs; simp [lists, hro]
      refine ⟨⟨by simp [MSt.complete], by simp [MSt.complete], by rw [hl]; simp, ?_,
        by simp [MSt.complete], by simp [MSt.complete]⟩, fun hs₀ hc => ?_⟩
      · simp only [nonchg, MSt.complete, List.countP_append]
        exact (Nat.add_le_add (List.countP_le_length.trans (by simp [cands]))
          (List.countP_mono_left fun z _ h => by simp_all)).trans (le_of_eq (add_comm _ _))
      · have hb : s.1.bad = false := by
          cases h : s.1.bad
          · rfl
          · exact absurd (Or.inl h) hs₀
        rintro (h | h)
        · exact hs₀ (Or.inr (complete_E3 s H δs ans r.1 _ hb hc h))
        · refine hs₀ (Or.inr ?_)
          obtain ⟨hs, δ, hδ, rest⟩ := h
          refine ⟨hs, δ, by rw [← hro]; exact hδ, ?_⟩
          simpa [MSt.complete] using rest

end Steps

end VoleMole.Assumptions.TheoremR
