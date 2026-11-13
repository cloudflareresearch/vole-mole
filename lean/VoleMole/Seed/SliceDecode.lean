import VoleMole.Seed.KOSUnique

/-!
# Decoding a hidden slice by evaluating the check value

`lean/docs/security/pomfrit-lemmap-tight.md` §6A. A *class* is a set `C` of trees with the same
witness and label rows. `Seed/KOSUnique.lean` shows that two challenges of one slice of a class
with the same check value certify the witness (`slice_collision_sound`). This file gives the
decoder `Dec^cls` that finds such a pair, as a function of the check value `K`, with the number of
points at which it evaluates `K`.

* **The decoder** (`dec`). Data: a set `U` of directions, a set `Rs` of base points and `n`
  generators `gen k`. For `δ ∈ U` and `r ∈ Rs` it evaluates `K` at `r`, `r + δ`, `r + gen k`,
  `r + gen k + δ` (`decPts`, at most `|U|·|Rs|·2(n+1)` points, `card_decPts_le`), forms the affine
  prediction `decPred` of the increment of `K` along `δ` at `r + Σ_{k ∈ s} gen k`, and looks for
  `(δ, r, s)` with prediction `0` (a linear system in `s`; the search itself is not costed here).
  It checks the pair it found with two more evaluations.
* `dec_sound`: every output is a pair `(x, x + δ)` with `δ ∈ U` and `K (x + δ) = K x`. No
  hypothesis.
* `dec_complete`: if the increments of `K` are affine in the generators (`incr_decPt`), and some
  `(δ, r, s)` has `K (x + δ) = K x`, the decoder outputs a pair.
* `dec_congr`, `card_decQ_le`: the output depends on `K` only at the `decQ K` points it evaluates,
  at most `|U|·|Rs|·2(n+1) + 2`.
* **For trees** (`dec_cert_sound`, `dec_cert_complete`). With `K` the KOS check value of a chain:
  an output certifies the class (`slice_collision_sound`; needs `KOSPar`). If the response is
  affine on the slices of `C` (`AffineOn`, §6.2 Lemma S2) and its increments along `C` are affine
  in the blocks of the trees `T₁` (`TwoLabelOn`: these trees carry one label vector), the base
  points cover the slices, and the accepting set `A`, in one slice of `C`, has
  `|U₀|·|A| > ∏_{i ∈ C} |B_i|`, the decoder outputs a pair.
* `twoLabel_gate`: the gate model of `translateOn_gate_slice` satisfies `TwoLabelOn`'s identity,
  for every hash and every `c_mult`.

No `sorry`, no `axiom`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Seed

/-! ## The decoder -/

section Dec

variable {X M : Type*} [AddCommGroup X] [AddCommGroup M] [DecidableEq X] {n : ℕ}

/-- The increment of `K` along `δ` at `x`. -/
def incr (K : X → M) (δ x : X) : M := K (x + δ) - K x

/-- The base point `r + Σ_{k ∈ s} gen k`. -/
def decPt (gen : Fin n → X) (r : X) (s : Finset (Fin n)) : X := r + ∑ k ∈ s, gen k

/-- The affine prediction of the increment along `δ` at `decPt gen r s`, from the increments at
`r` and at `r + gen k`. -/
def decPred (K : X → M) (gen : Fin n → X) (δ r : X) (s : Finset (Fin n)) : M :=
  incr K δ r + ∑ k ∈ s, (incr K δ (r + gen k) - incr K δ r)

/-- The points at which the decoder evaluates `K` before it outputs a pair. -/
def decPts (U Rs : Finset X) (gen : Fin n → X) : Finset X :=
  (U ×ˢ Rs).biUnion fun t =>
    insert t.2 (insert (t.2 + t.1)
      (Finset.univ.biUnion fun k : Fin n => ({t.2 + gen k, t.2 + gen k + t.1} : Finset X)))

lemma card_decPts_le (U Rs : Finset X) (gen : Fin n → X) :
    (decPts U Rs gen).card ≤ U.card * Rs.card * (2 * (n + 1)) := by
  refine Finset.card_biUnion_le.trans ?_
  have hin : ∀ t ∈ U ×ˢ Rs, (insert t.2 (insert (t.2 + t.1)
      (Finset.univ.biUnion fun k : Fin n =>
        ({t.2 + gen k, t.2 + gen k + t.1} : Finset X)))).card ≤ 2 * (n + 1) := by
    intro t _
    have h2 : (Finset.univ.biUnion fun k : Fin n =>
        ({t.2 + gen k, t.2 + gen k + t.1} : Finset X)).card ≤ 2 * n := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ k : Fin n, ({t.2 + gen k, t.2 + gen k + t.1} : Finset X).card
          ≤ ∑ _k : Fin n, 2 := Finset.sum_le_sum fun k _ => Finset.card_le_two
        _ = 2 * n := by simp [mul_comm]
    have h1 := Finset.card_insert_le (t.2 + t.1) (Finset.univ.biUnion fun k : Fin n =>
      ({t.2 + gen k, t.2 + gen k + t.1} : Finset X))
    have h0 := Finset.card_insert_le t.2 (insert (t.2 + t.1) (Finset.univ.biUnion fun k : Fin n =>
      ({t.2 + gen k, t.2 + gen k + t.1} : Finset X)))
    omega
  calc ∑ t ∈ U ×ˢ Rs, (insert t.2 (insert (t.2 + t.1)
        (Finset.univ.biUnion fun k : Fin n =>
          ({t.2 + gen k, t.2 + gen k + t.1} : Finset X)))).card
      ≤ ∑ _t ∈ U ×ˢ Rs, 2 * (n + 1) := Finset.sum_le_sum hin
    _ = U.card * Rs.card * (2 * (n + 1)) := by
        rw [Finset.sum_const, Finset.card_product, smul_eq_mul]

/-- The prediction reads `K` at the points of `decPts` only. -/
lemma decPred_congr {K K' : X → M} {U Rs : Finset X} {gen : Fin n → X}
    (h : ∀ x ∈ decPts U Rs gen, K' x = K x) {δ r : X} (hδ : δ ∈ U) (hr : r ∈ Rs)
    (s : Finset (Fin n)) : decPred K' gen δ r s = decPred K gen δ r s := by
  have hm : ∀ x, x ∈ insert r (insert (r + δ) (Finset.univ.biUnion fun k : Fin n =>
      ({r + gen k, r + gen k + δ} : Finset X))) → K' x = K x := fun x hx =>
    h x (Finset.mem_biUnion.2 ⟨(δ, r), Finset.mem_product.2 ⟨hδ, hr⟩, hx⟩)
  have h1 : K' r = K r := hm r (Finset.mem_insert_self _ _)
  have h2 : K' (r + δ) = K (r + δ) :=
    hm _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h3 : ∀ k, K' (r + gen k) = K (r + gen k) := fun k =>
    hm _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ k, Finset.mem_insert_self _ _⟩)))
  have h4 : ∀ k, K' (r + gen k + δ) = K (r + gen k + δ) := fun k =>
    hm _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ k,
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)))
  simp only [decPred, incr, h1, h2, h3, h4]

/-- The decoder's candidates: a direction, a base point and a set of generators whose predicted
increment is `0`. -/
def decCand (K : X → M) (U Rs : Finset X) (gen : Fin n → X) (t : X × X × Finset (Fin n)) : Prop :=
  t.1 ∈ U ∧ t.2.1 ∈ Rs ∧ decPred K gen t.1 t.2.1 t.2.2 = 0

open Classical in
/-- The decoder for a candidate predicate: take a candidate, evaluate `K` at its two points, and
output them if the values agree. -/
noncomputable def decOf (P : X × X × Finset (Fin n) → Prop) (K : X → M) (gen : Fin n → X) :
    Option (X × X) :=
  if h : ∃ t, P t then
    if K (decPt gen (Classical.choose h).2.1 (Classical.choose h).2.2 + (Classical.choose h).1) =
        K (decPt gen (Classical.choose h).2.1 (Classical.choose h).2.2) then
      some (decPt gen (Classical.choose h).2.1 (Classical.choose h).2.2,
        decPt gen (Classical.choose h).2.1 (Classical.choose h).2.2 + (Classical.choose h).1)
    else none
  else none

/-- **The decoder `Dec^cls`**, as a function of the check value. -/
noncomputable def dec (K : X → M) (U Rs : Finset X) (gen : Fin n → X) : Option (X × X) :=
  decOf (decCand K U Rs gen) K gen

/-- **Soundness, no hypothesis**: an output is a pair `(x, x + δ)`, `δ ∈ U`, `x` a base point,
with the same value of `K`. -/
theorem dec_sound {K : X → M} {U Rs : Finset X} {gen : Fin n → X} {x₀ x₁ : X}
    (h : dec K U Rs gen = some (x₀, x₁)) :
    ∃ δ ∈ U, ∃ r ∈ Rs, ∃ s, x₀ = decPt gen r s ∧ x₁ = x₀ + δ ∧ K x₁ = K x₀ := by
  unfold dec decOf at h
  split_ifs at h with hex hK
  have hc := Classical.choose_spec hex
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, hc.1, _, hc.2.1, _, rfl, rfl, hK⟩

/-- **Completeness**: if the increments along `U` at the base points are the affine predictions,
and some base point has a zero increment along some `δ ∈ U`, the decoder outputs a pair. -/
theorem dec_complete {K : X → M} {U Rs : Finset X} {gen : Fin n → X}
    (hTL : ∀ δ ∈ U, ∀ r ∈ Rs, ∀ s, incr K δ (decPt gen r s) = decPred K gen δ r s)
    (hex : ∃ δ ∈ U, ∃ r ∈ Rs, ∃ s, K (decPt gen r s + δ) = K (decPt gen r s)) :
    (dec K U Rs gen).isSome := by
  obtain ⟨δ, hδ, r, hr, s, hs⟩ := hex
  have hex' : ∃ t, decCand K U Rs gen t :=
    ⟨(δ, r, s), hδ, hr, by rw [← hTL δ hδ r hr s, incr, hs, sub_self]⟩
  have hc := Classical.choose_spec hex'
  have hK : K (decPt gen (Classical.choose hex').2.1 (Classical.choose hex').2.2 +
      (Classical.choose hex').1) =
      K (decPt gen (Classical.choose hex').2.1 (Classical.choose hex').2.2) := by
    have := hTL _ hc.1 _ hc.2.1 (Classical.choose hex').2.2
    rw [hc.2.2, incr] at this
    exact sub_eq_zero.1 this
  unfold dec decOf
  rw [dite_eq_left_of_eq_true (eq_true hex'), ite_eq_left_of_eq_true _ _ (eq_true hK)]
  rfl

open Classical in
/-- All points at which the decoder evaluates `K`: `decPts` and the pair it checks. -/
noncomputable def decQ (K : X → M) (U Rs : Finset X) (gen : Fin n → X) : Finset X :=
  decPts U Rs gen ∪
    if h : ∃ t, decCand K U Rs gen t then
      {decPt gen (Classical.choose h).2.1 (Classical.choose h).2.2,
        decPt gen (Classical.choose h).2.1 (Classical.choose h).2.2 + (Classical.choose h).1}
    else ∅

/-- **The number of evaluations**: at most `|U|·|Rs|·2(n+1) + 2`. -/
theorem card_decQ_le (K : X → M) (U Rs : Finset X) (gen : Fin n → X) :
    (decQ K U Rs gen).card ≤ U.card * Rs.card * (2 * (n + 1)) + 2 := by
  unfold decQ
  refine (Finset.card_union_le _ _).trans (add_le_add (card_decPts_le U Rs gen) ?_)
  split_ifs
  · exact Finset.card_le_two
  · simp

/-- **The decoder reads `K` at `decQ K` only**: a function that agrees with `K` there gives the
same output. -/
theorem dec_congr {K K' : X → M} {U Rs : Finset X} {gen : Fin n → X}
    (h : ∀ x ∈ decQ K U Rs gen, K' x = K x) : dec K' U Rs gen = dec K U Rs gen := by
  have hP : decCand K' U Rs gen = decCand K U Rs gen := by
    funext t
    refine propext (and_congr_right fun h1 => and_congr_right fun h2 => ?_)
    rw [decPred_congr (fun x hx => h x (Finset.mem_union_left _ hx)) h1 h2]
  unfold dec
  rw [hP]
  unfold decOf
  by_cases hex : ∃ t, decCand K U Rs gen t
  · have hsub : ({decPt gen (Classical.choose hex).2.1 (Classical.choose hex).2.2,
        decPt gen (Classical.choose hex).2.1 (Classical.choose hex).2.2 +
          (Classical.choose hex).1} : Finset X) ⊆ decQ K U Rs gen := by
      unfold decQ
      rw [dite_eq_left_of_eq_true (eq_true hex)]
      exact Finset.subset_union_right
    rw [dite_eq_left_of_eq_true (eq_true hex), dite_eq_left_of_eq_true (eq_true hex),
      h _ (hsub (Finset.mem_insert_self _ _)),
      h _ (hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))]
  · rw [dite_eq_right_of_eq_false (eq_false hex), dite_eq_right_of_eq_false (eq_false hex)]

/-- **Affine increments.** If adding a generator changes the increment along `δ` by the same
amount at every base point `r + Σ_{j ∈ s} gen j`, the increment at `decPt gen r s` is the
prediction. -/
lemma incr_decPt {K : X → M} {gen : Fin n → X} {δ r : X}
    (h : ∀ (s : Finset (Fin n)) (k : Fin n),
      incr K δ (r + ∑ j ∈ s, gen j + gen k) - incr K δ (r + ∑ j ∈ s, gen j) =
        incr K δ (r + gen k) - incr K δ r)
    (s : Finset (Fin n)) : incr K δ (decPt gen r s) = decPred K gen δ r s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [decPt, decPred]
  | insert k s hk ih =>
    have hs := h s k
    unfold decPt decPred at ih ⊢
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    have e : r + (gen k + ∑ j ∈ s, gen j) = r + ∑ j ∈ s, gen j + gen k := by abel
    rw [e, sub_eq_iff_eq_add.1 hs, ih]
    abel

end Dec

/-! ## The check value: translations and increments -/

section Value

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {X : Type*} [AddCommGroup X]

/-- The check value commutes with a translation that the response commutes with. -/
lemma kosValue_translate {T : Finset F} {L : ℕ} (c : Ch F T) (e : X →+ F) (Q : X → Fin L → F)
    (D : X → Fin 4 → F) (u : Fin 4 → F) {Δ Δ₂ Δ₃ : X}
    (hQ : Q (Δ + (Δ₃ - Δ₂)) = Q Δ + (Q Δ₃ - Q Δ₂))
    (hD : D (Δ + (Δ₃ - Δ₂)) = D Δ + (D Δ₃ - D Δ₂)) :
    kosValue c e Q D u (Δ + (Δ₃ - Δ₂)) =
      kosValue c e Q D u Δ + (kosValue c e Q D u Δ₃ - kosValue c e Q D u Δ₂) := by
  have hh : kosHashL c (Q Δ + (Q Δ₃ - Q Δ₂), D Δ + (D Δ₃ - D Δ₂)) =
      kosHashL c (Q Δ, D Δ) + (kosHashL c (Q Δ₃, D Δ₃) - kosHashL c (Q Δ₂, D Δ₂)) := by
    rw [← map_sub, ← map_add]; rfl
  simp only [kosValue_eq, hQ, hD, hh, map_add, map_sub, add_smul, sub_smul]
  abel

/-- The increment of the check value: the hash of the increment of the response, plus `e(δ)·ũ`. -/
lemma incr_kosValue {T : Finset F} {L : ℕ} (c : Ch F T) (e : X →+ F) (Q : X → Fin L → F)
    (D : X → Fin 4 → F) (u : Fin 4 → F) (δ x : X) :
    incr (kosValue c e Q D u) δ x =
      kosHashL c (Q (x + δ) - Q x, D (x + δ) - D x) + e δ • u := by
  have hh : kosHashL c (Q (x + δ) - Q x, D (x + δ) - D x) =
      kosHashL c (Q (x + δ), D (x + δ)) - kosHashL c (Q x, D x) := by
    rw [← map_sub]; rfl
  simp only [incr, kosValue_eq, hh, map_add, add_smul]
  abel

/-- The increments of the check value inherit the two-label identity of the response. -/
lemma incr_kosValue_twoLabel {T : Finset F} {L : ℕ} (c : Ch F T) (e : X →+ F)
    (Q : X → Fin L → F) (D : X → Fin 4 → F) (u : Fin 4 → F) {δ x g g' : X}
    (hQ : Q (x + g + g' + δ) - Q (x + g + g') - (Q (x + g + δ) - Q (x + g)) =
      Q (x + g' + δ) - Q (x + g') - (Q (x + δ) - Q x))
    (hD : D (x + g + g' + δ) - D (x + g + g') - (D (x + g + δ) - D (x + g)) =
      D (x + g' + δ) - D (x + g') - (D (x + δ) - D x)) :
    incr (kosValue c e Q D u) δ (x + g + g') - incr (kosValue c e Q D u) δ (x + g) =
      incr (kosValue c e Q D u) δ (x + g') - incr (kosValue c e Q D u) δ x := by
  simp only [incr_kosValue]
  rw [add_sub_add_right_eq_sub, add_sub_add_right_eq_sub, ← map_sub, ← map_sub,
    Prod.mk_sub_mk, Prod.mk_sub_mk, hQ, hD]

end Value

/-! ## Trees: the decoder's output certifies the class, and large level sets are found -/

section TreeDec

open VoleMole.SeedExtraction VoleMole.PomFRIT

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)] {n : ℕ}

/-- The directions of a set `C` of trees: the challenges that vanish outside `C`. -/
def dirs (C : Finset ι) : Set (∀ i, B i) := {δ | ∀ i ∉ C, δ i = 0}

lemma sum_mem_dirs {C : Finset ι} {gen : Fin n → ∀ i, B i} (h : ∀ k, gen k ∈ dirs C)
    (s : Finset (Fin n)) : ∑ k ∈ s, gen k ∈ dirs C := fun i hi => by
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun k _ => h k i hi

/-- **Two labels.** The increments of the response along the directions of `C` are affine in the
blocks of the trees `T₁`: adding `g'` changes the increment by the same amount at `x` and at
`x + g`. The CRT masks have this property when the trees of `C` carry one label vector and those
of `T₁` another (`twoLabel_gate`); the witness and label rows are additive and have it trivially. -/
def TwoLabelOn {L : ℕ} (Sb : Set (∀ i, B i)) (C T₁ : Finset ι) (Q : (∀ i, B i) → Fin L → F)
    (D : (∀ i, B i) → Fin 4 → F) : Prop :=
  ∀ x ∈ Sb, ∀ δ ∈ dirs C, ∀ g ∈ dirs T₁, ∀ g' ∈ dirs T₁,
    Q (x + g + g' + δ) - Q (x + g + g') - (Q (x + g + δ) - Q (x + g)) =
        Q (x + g' + δ) - Q (x + g') - (Q (x + δ) - Q x) ∧
      D (x + g + g' + δ) - D (x + g + g') - (D (x + g + δ) - D (x + g)) =
        D (x + g' + δ) - D (x + g') - (D (x + δ) - D x)

/-- **The decoder's output is a certificate.** Under the hypotheses of `slice_collision_sound`
(`chall₁` good for parallelism, an accepting set with a bit slope and a free tree, the tree form of
the witness rows on `Sb`), if the decoder's directions are nonzero directions of the class `C` and
its points lie in `Sb`, an output of the decoder gives `u* = u_C`. -/
theorem dec_cert_sound [∀ i, DecidableEq (B i)] {T : Finset F} {L ℓ : ℕ} (hℓ : ℓ ≤ L)
    {c : Ch F T} {e : (∀ i, B i) →+ F} {Sb A : Set (∀ i, B i)} {known : Finset ι}
    {u : ι → Fin ℓ → Bool} {Q : (∀ i, B i) → Fin L → F} {D : (∀ i, B i) → Fin 4 → F}
    (hc : KOSPar c (DisjQuads B) e Q D) (ũ h : Fin 4 → F)
    (hacc : ∀ Δ ∈ A, kosValue c e Q D ũ Δ = h) {uStar : Fin ℓ → F}
    (hK : Claim4Hyp e A known u (fun j Δ => Q Δ (Fin.castLE hℓ j)) uStar)
    (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1) {i₀ : ι} (hfree : ¬IsFixed A i₀)
    (htree : ∀ j, ∃ c', ∀ Δ ∈ Sb,
      Q Δ (Fin.castLE hℓ j) = c' + ∑ i ∈ known, bit (u i j) * blockLift e i (Δ i))
    {C : Finset ι} (hC : C ⊆ known) {uC : Fin ℓ → Bool} (huC : ∀ i ∈ C, ∀ j, u i j = uC j)
    {U Rs : Finset (∀ i, B i)} {gen : Fin n → ∀ i, B i}
    (hU : ∀ δ ∈ U, δ ≠ 0 ∧ δ ∈ dirs C)
    (hSb : ∀ δ ∈ U, ∀ r ∈ Rs, ∀ s, decPt gen r s ∈ Sb ∧ decPt gen r s + δ ∈ Sb)
    (hdec : (dec (kosValue c e Q D ũ) U Rs gen).isSome) :
    uStar = fun j => bit (uC j) := by
  obtain ⟨⟨x₀, x₁⟩, hx⟩ := Option.isSome_iff_exists.1 hdec
  obtain ⟨δ, hδ, r, hr, s, rfl, rfl, hcol⟩ := dec_sound hx
  obtain ⟨hne, hdir⟩ := hU δ hδ
  obtain ⟨h0S, h1S⟩ := hSb δ hδ r hr s
  refine slice_collision_sound hℓ hc ũ h hacc hK hbits hfree htree hC huC h0S h1S
    (mem_slice_self C _) (fun i hi => ?_) (fun heq => hne ?_) hcol.symm
  · simp [hdir i hi]
  · simpa using heq

/-- **Large level sets are found.** Let the accepting set `A` lie in one slice of `C` (every tree
outside `C` is fixed on it) and pass the KOS check. Let the response be affine on the slices of
`C` and two-label in the blocks of `T₁`, and let the decoder's data be: a subgroup `U₀` of
directions of `C` (it uses `U₀ \ {0}`), generators in the blocks of `T₁`, base points in `Sb` that
cover every slice of `C`. If `|U₀|·|A| > ∏_{i ∈ C} |B_i|`, the decoder outputs a pair: the level
set of `A`, a coset of a subgroup of the directions of `C`, is too large to miss `U₀`. -/
theorem dec_cert_complete [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)] {T : Finset F} {L : ℕ}
    {c : Ch F T} {e : (∀ i, B i) →+ F} {Sb : Set (∀ i, B i)}
    {Q : (∀ i, B i) → Fin L → F} {D : (∀ i, B i) → Fin 4 → F} (ũ h : Fin 4 → F)
    (h2 : ∀ x : (∀ i, B i), x + x = 0) {A : Finset (∀ i, B i)}
    (hAS : (A : Set (∀ i, B i)) ⊆ Sb) (hacc : ∀ Δ ∈ A, kosValue c e Q D ũ Δ = h)
    {C T₁ : Finset ι} (hfix : ∀ i ∉ C, IsFixed (A : Set (∀ i, B i)) i)
    (hSbD : ∀ x ∈ Sb, ∀ δ ∈ dirs C, x + δ ∈ Sb)
    (haff : ∀ g, AffineOn (Sb ∩ slice C g) Q D) (htl : TwoLabelOn Sb C T₁ Q D)
    {U₀ Rs : Finset (∀ i, B i)} {gen : Fin n → ∀ i, B i}
    (hadd : ∀ a ∈ U₀, ∀ b ∈ U₀, a + b ∈ U₀) (hUd : ∀ δ ∈ U₀, δ ∈ dirs C)
    (hgen : ∀ k, gen k ∈ dirs T₁) (hRs : ∀ r ∈ Rs, r ∈ Sb)
    (hcov : ∀ Δ ∈ Sb, ∃ r ∈ Rs, ∃ s, decPt gen r s ∈ Sb ∧ ∀ i ∉ C, decPt gen r s i = Δ i)
    (hsize : ∏ i ∈ C, Fintype.card (B i) < U₀.card * A.card) :
    (dec (kosValue c e Q D ũ) (U₀.erase 0) Rs gen).isSome := by
  classical
  set K := kosValue c e Q D ũ with hKdef
  have heq2 : ∀ a b : (∀ i, B i), a + b = 0 → a = b := fun a b hab => by
    calc a = a + (b + b) := by rw [h2, add_zero]
      _ = a + b + b := by abel
      _ = b := by rw [hab, zero_add]
  have hApos : 0 < A.card := by
    rcases Nat.eq_zero_or_pos A.card with h' | h'
    · rw [h', mul_zero] at hsize
      exact absurd hsize (Nat.not_lt_zero _)
    · exact h'
  obtain ⟨Δ₀, hΔ₀⟩ := Finset.card_pos.1 hApos
  have hΔ₀S : Δ₀ ∈ Sb := hAS hΔ₀
  -- `K` commutes with translations inside the slice of `Δ₀`.
  have htr : ∀ x ∈ Sb ∩ slice C Δ₀, ∀ y ∈ Sb ∩ slice C Δ₀, ∀ z ∈ Sb ∩ slice C Δ₀,
      K (x + (z - y)) = K x + (K z - K y) := by
    intro x hx y hy z hz
    obtain ⟨-, hQ, hD⟩ := haff Δ₀ x hx y hy z hz
    exact kosValue_translate c e Q D ũ hQ hD
  have hmem : ∀ δ ∈ dirs C, Δ₀ + δ ∈ Sb ∩ slice C Δ₀ := fun δ hδ =>
    ⟨hSbD _ hΔ₀S δ hδ, fun i hi => by simp [hδ i hi]⟩
  have hmem0 : Δ₀ ∈ Sb ∩ slice C Δ₀ := ⟨hΔ₀S, mem_slice_self C Δ₀⟩
  -- The level set through `Δ₀`, as a set of directions.
  let N : Finset (∀ i, B i) := Finset.univ.filter fun δ => δ ∈ dirs C ∧ K (Δ₀ + δ) = K Δ₀
  have hNmem : ∀ δ, δ ∈ N ↔ δ ∈ dirs C ∧ K (Δ₀ + δ) = K Δ₀ := fun δ => by simp [N]
  have hNadd : ∀ a ∈ N, ∀ b ∈ N, a + b ∈ N := by
    intro a ha b hb
    obtain ⟨had, haK⟩ := (hNmem a).1 ha
    obtain ⟨hbd, hbK⟩ := (hNmem b).1 hb
    refine (hNmem _).2 ⟨fun i hi => by simp [had i hi, hbd i hi], ?_⟩
    have := htr (Δ₀ + a) (hmem a had) Δ₀ hmem0 (Δ₀ + b) (hmem b hbd)
    have e1 : Δ₀ + a + (Δ₀ + b - Δ₀) = Δ₀ + (a + b) := by abel
    rw [e1, haK, hbK, sub_self, add_zero] at this
    exact this
  have hAN : A.card ≤ N.card := by
    refine Finset.card_le_card_of_injOn (fun Δ => Δ + Δ₀) (fun Δ hΔ => ?_)
      (fun Δ _ Δ' _ heq => add_right_cancel heq)
    refine Finset.mem_coe.2 ((hNmem _).2 ⟨fun i hi => ?_, ?_⟩)
    · show Δ i + Δ₀ i = 0
      rw [hfix i hi Δ hΔ Δ₀ hΔ₀]
      exact congrFun (h2 Δ₀) i
    · have e1 : Δ₀ + (Δ + Δ₀) = Δ := by rw [add_comm Δ, ← add_assoc, h2, zero_add]
      rw [e1, hacc Δ hΔ, hacc Δ₀ hΔ₀]
  -- Pigeonhole: `U₀ × N` does not inject into the directions of `C`.
  let Dset : Finset (∀ i, B i) := Finset.univ.filter fun δ => δ ∈ dirs C
  have hDmem : ∀ δ, δ ∈ Dset ↔ δ ∈ dirs C := fun δ => by simp [Dset]
  have hD : Dset.card ≤ ∏ i ∈ C, Fintype.card (B i) :=
    card_le_prod_of_fixed Dset C fun i hi Δ hΔ Δ' hΔ' => by
      rw [(hDmem Δ).1 (Finset.mem_coe.1 hΔ) i hi, (hDmem Δ').1 (Finset.mem_coe.1 hΔ') i hi]
  have hlt : Dset.card < (U₀ ×ˢ N).card := by
    rw [Finset.card_product]
    exact hD.trans_lt (hsize.trans_le (Nat.mul_le_mul_left _ hAN))
  obtain ⟨p, hp, q, hq, hpq, hsum⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
    (f := fun t : (∀ i, B i) × (∀ i, B i) => t.1 + t.2) (fun t ht => by
      obtain ⟨h1, h2'⟩ := Finset.mem_product.1 ht
      refine (hDmem _).2 fun i hi => ?_
      show t.1 i + t.2 i = 0
      rw [hUd _ h1 i hi, ((hNmem _).1 h2').1 i hi, add_zero])
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
  obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 hq
  have hsum' : p.1 + p.2 = q.1 + q.2 := hsum
  have e1 : p.1 + q.1 = p.1 + p.2 + (q.1 + p.2) := by
    rw [show p.1 + p.2 + (q.1 + p.2) = p.1 + q.1 + (p.2 + p.2) by abel, h2, add_zero]
  have e2 : p.2 + q.2 = q.1 + q.2 + (q.1 + p.2) := by
    rw [show q.1 + q.2 + (q.1 + p.2) = p.2 + q.2 + (q.1 + q.1) by abel, h2, add_zero]
  have hδ' : p.1 + q.1 = p.2 + q.2 := by rw [e1, hsum', ← e2]
  have hne : p.1 + q.1 ≠ 0 := by
    intro h0
    apply hpq
    exact Prod.ext (heq2 _ _ h0) (heq2 _ _ (hδ' ▸ h0))
  have hδU : p.1 + q.1 ∈ U₀ := hadd _ hp1 _ hq1
  have hδN : p.1 + q.1 ∈ N := hδ' ▸ hNadd _ hp2 _ hq2
  obtain ⟨hδd, hδK⟩ := (hNmem _).1 hδN
  -- A base point of the decoder in the slice of `Δ₀`.
  obtain ⟨r, hr, s, hxS, hxag⟩ := hcov Δ₀ hΔ₀S
  have hx : decPt gen r s ∈ Sb ∩ slice C Δ₀ := ⟨hxS, hxag⟩
  have hcol : K (decPt gen r s + (p.1 + q.1)) = K (decPt gen r s) := by
    have := htr _ hx Δ₀ hmem0 (Δ₀ + (p.1 + q.1)) (hmem _ hδd)
    have e3 : decPt gen r s + (Δ₀ + (p.1 + q.1) - Δ₀) = decPt gen r s + (p.1 + q.1) := by abel
    rw [e3, hδK, sub_self, add_zero] at this
    exact this
  refine dec_complete (fun δ hδ r hr s => incr_decPt (fun s k => ?_) s)
    ⟨_, Finset.mem_erase.2 ⟨hne, hδU⟩, r, hr, s, hcol⟩
  obtain ⟨hQ, hD⟩ := htl r (hRs r hr) δ (hUd δ (Finset.mem_of_mem_erase hδ)) _
    (sum_mem_dirs hgen s) _ (hgen k)
  exact incr_kosValue_twoLabel c e Q D ũ hQ hD

end TreeDec

/-! ## The gate model has two-label increments -/

section GateModel

variable {R : Type*} [AddCommGroup R]

/-- A function of two bits, in characteristic 2: adding `c'` to the second bit changes the
increment in the first bit by the same amount at `b₁` and at `b₁ + c`. -/
lemma twoLabel_bits (hR : ∀ r : R, r + r = 0) (ψ : ZMod 2 → ZMod 2 → R) (b d b₁ c c' : ZMod 2) :
    ψ (b + d) (b₁ + c + c') - ψ b (b₁ + c + c') - (ψ (b + d) (b₁ + c) - ψ b (b₁ + c)) =
      ψ (b + d) (b₁ + c') - ψ b (b₁ + c') - (ψ (b + d) b₁ - ψ b b₁) := by
  have hneg : ∀ r : R, -r = r := fun r => neg_eq_of_add_eq_zero_left (hR r)
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have e1 : (1 : ZMod 2) + 1 = 0 := by decide
  simp only [sub_eq_add_neg, hneg]
  rcases h01 c with rfl | rfl <;> rcases h01 c' with rfl | rfl
  · simp
  · simp
  · simp only [add_zero, hR]
  · have e2 : b₁ + 1 + 1 = b₁ := by rw [add_assoc, e1, add_zero]
    rw [e2]; abel

/-- **The gate terms have two-label increments.** In the gate model of `translateOn_gate_slice`
(tree `i` contributes the bit `γ_i(Δ_i)` to the selection bit and, if set, its label offset `ℓ_i`
to the label), let the trees of `C` have one label offset and those of `T₁`, disjoint from `C`,
another. Then for `δ` in the blocks of `C` and `g`, `g'` in the blocks of `T₁`, the gate term
satisfies `TwoLabelOn`'s identity at every `x`, for every hash `T` and every `c_mult` value. -/
theorem twoLabel_gate {ι Lab : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*}
    [∀ i, AddCommGroup (B i)] [AddCommGroup Lab] (hR : ∀ r : R, r + r = 0)
    (hLab : ∀ l : Lab, l + l = 0) (γ : ∀ i, B i →+ ZMod 2) (ℓs : ι → Lab) (C₀ : Lab) (T : Lab → R)
    (cm : R) (C T₁ : Finset ι) (hdisj : Disjoint C T₁) {ℓ ℓ₁ : Lab} (hℓ : ∀ i ∈ C, ℓs i = ℓ)
    (hℓ₁ : ∀ i ∈ T₁, ℓs i = ℓ₁) (x δ g g' : ∀ i, B i) (hδ : δ ∈ dirs C) (hg : g ∈ dirs T₁)
    (hg' : g' ∈ dirs T₁) :
    let f : (∀ i, B i) → R := fun Δ =>
      T (C₀ + ∑ i, if γ i (Δ i) = 1 then ℓs i else 0) + if ∑ i, γ i (Δ i) = 1 then cm else 0
    f (x + g + g' + δ) - f (x + g + g') - (f (x + g + δ) - f (x + g)) =
      f (x + g' + δ) - f (x + g') - (f (x + δ) - f x) := by
  intro f
  -- The rest of the trees contributes a constant; the two classes contribute one bit each.
  set O : Finset ι := Finset.univ \ (C ∪ T₁) with hO
  let βC : (∀ i, B i) →+ ZMod 2 := ∑ i ∈ C, (γ i).comp (Pi.evalAddMonoidHom B i)
  let β₁ : (∀ i, B i) →+ ZMod 2 := ∑ i ∈ T₁, (γ i).comp (Pi.evalAddMonoidHom B i)
  have hβC : ∀ Δ, βC Δ = ∑ i ∈ C, γ i (Δ i) := fun Δ => by simp [βC]
  have hβ₁ : ∀ Δ, β₁ Δ = ∑ i ∈ T₁, γ i (Δ i) := fun Δ => by simp [β₁]
  let ψ : ZMod 2 → ZMod 2 → R := fun a b =>
    T (C₀ + (∑ i ∈ O, if γ i (x i) = 1 then ℓs i else 0) + (if a = 1 then ℓ else 0) +
      (if b = 1 then ℓ₁ else 0)) +
      if (∑ i ∈ O, γ i (x i)) + a + b = 1 then cm else 0
  -- `f` at a point that agrees with `x` on the other trees.
  have hf : ∀ Δ : ∀ i, B i, (∀ i ∈ O, Δ i = x i) → f Δ = ψ (βC Δ) (β₁ Δ) := by
    intro Δ hΔ
    have hsplit : ∀ φ : ι → ZMod 2, ∑ i, φ i = ∑ i ∈ O, φ i + ∑ i ∈ C, φ i + ∑ i ∈ T₁, φ i := by
      intro φ
      rw [hO, ← Finset.sum_sdiff (Finset.subset_univ (C ∪ T₁)), Finset.sum_union hdisj, add_assoc]
    have hsplitL : ∀ φ : ι → Lab, ∑ i, φ i = ∑ i ∈ O, φ i + ∑ i ∈ C, φ i + ∑ i ∈ T₁, φ i := by
      intro φ
      rw [hO, ← Finset.sum_sdiff (Finset.subset_univ (C ∪ T₁)), Finset.sum_union hdisj, add_assoc]
    have h1 : (∑ i, if γ i (Δ i) = 1 then ℓs i else 0) =
        (∑ i ∈ O, if γ i (x i) = 1 then ℓs i else 0) + (if βC Δ = 1 then ℓ else 0) +
          (if β₁ Δ = 1 then ℓ₁ else 0) := by
      rw [hsplitL, hβC, hβ₁, ← sum_ite_bit hLab, ← sum_ite_bit hLab]
      congr 1
      · congr 1
        · exact Finset.sum_congr rfl fun i hi => by rw [hΔ i hi]
        · exact Finset.sum_congr rfl fun i hi => by rw [hℓ i hi]
      · exact Finset.sum_congr rfl fun i hi => by rw [hℓ₁ i hi]
    have h2 : (∑ i, γ i (Δ i)) = (∑ i ∈ O, γ i (x i)) + βC Δ + β₁ Δ := by
      rw [hsplit, hβC, hβ₁]
      congr 2
      exact Finset.sum_congr rfl fun i hi => by rw [hΔ i hi]
    show T (C₀ + ∑ i, if γ i (Δ i) = 1 then ℓs i else 0) + (if ∑ i, γ i (Δ i) = 1 then cm else 0) =
      ψ (βC Δ) (β₁ Δ)
    rw [h1, h2]
    simp only [ψ, add_assoc]
  have hOC : ∀ i ∈ O, i ∉ C := fun i hi hc =>
    (Finset.mem_sdiff.1 hi).2 (Finset.mem_union_left _ hc)
  have hOT : ∀ i ∈ O, i ∉ T₁ := fun i hi hc =>
    (Finset.mem_sdiff.1 hi).2 (Finset.mem_union_right _ hc)
  -- `δ` does not move `β₁`, and `g`, `g'` do not move `β_C`.
  have hz : ∀ (S S' : Finset ι) (v : ∀ i, B i), Disjoint S S' → v ∈ dirs S' →
      ∑ i ∈ S, γ i (v i) = 0 := fun S S' v hd hv =>
    Finset.sum_eq_zero fun i hi => by
      rw [hv i (Finset.disjoint_left.1 hd hi), map_zero]
  have hδ1 : β₁ δ = 0 := by rw [hβ₁]; exact hz T₁ C δ hdisj.symm hδ
  have hgC : βC g = 0 := by rw [hβC]; exact hz C T₁ g hdisj hg
  have hgC' : βC g' = 0 := by rw [hβC]; exact hz C T₁ g' hdisj hg'
  have hag : ∀ v : ∀ i, B i, (∀ i ∈ O, v i = 0) → ∀ Δ : ∀ i, B i, (∀ i ∈ O, Δ i = x i) →
      ∀ i ∈ O, (Δ + v) i = x i := fun v hv Δ hΔ i hi => by
    rw [Pi.add_apply, hv i hi, add_zero, hΔ i hi]
  have vδ : ∀ i ∈ O, δ i = 0 := fun i hi => hδ i (hOC i hi)
  have vg : ∀ i ∈ O, g i = 0 := fun i hi => hg i (hOT i hi)
  have vg' : ∀ i ∈ O, g' i = 0 := fun i hi => hg' i (hOT i hi)
  have a0 : ∀ i ∈ O, x i = x i := fun _ _ => rfl
  rw [hf _ (hag δ vδ _ (hag g' vg' _ (hag g vg x a0))), hf _ (hag g' vg' _ (hag g vg x a0)),
    hf _ (hag δ vδ _ (hag g vg x a0)), hf _ (hag g vg x a0),
    hf _ (hag δ vδ _ (hag g' vg' x a0)), hf _ (hag g' vg' x a0), hf _ (hag δ vδ x a0), hf x a0]
  simp only [map_add, hδ1, hgC, hgC', add_zero]
  exact twoLabel_bits hR ψ (βC x) (βC δ) (β₁ x) (β₁ g) (β₁ g')

end GateModel

end VoleMole.Seed
