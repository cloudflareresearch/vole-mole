import VoleMole.Assumptions.LazyPerm

/-!
# The lazy random permutation is an eagerly drawn uniform permutation

`LazyPerm.rpImpl` answers permutation queries lazily: a fresh forward answer is uniform on the
unused outputs, a fresh inverse answer uniform on the unused inputs; an other query `i` may read
the permutation forward at one point `pt i`. Here: this is the same as drawing `π` uniformly from
`Equiv.Perm B` up front and answering every query from `π` (`lean/docs/probabilistic-plan.md` §2o,
`lean/docs/security/uov-assumptions.md` §5.4, §5.8).

* **Uniform on a finite set** `unifFin S`; **splitting** it along a function whose fibres over `U`
  all have the same size (`unifFin_split`): `(x, f x)` for `x` uniform on `S` is `y` uniform on
  `U`, then `x` uniform on the fibre over `y`.
* **Permutations extending a table** `extSet L` (`Cons π L`: `π(x) = y` for every record), and the
  uniform one among them, `condPerm L`. A table is `Valid` if some permutation extends it.
* **The forward and inverse splits** (`condPerm_split_fwd`, `condPerm_split_inv`): at an input `b`
  not in a valid table, `π(b)` of `π ← condPerm L` is uniform on the unused outputs (the lazy fresh
  value `unifCompl`), and given `π(b) = y`, `π` is `condPerm (L ++ [(b, y, true)])`. The fibres
  have equal size because composing with the transposition `(y y')` (after `π`; before `π` for
  inverse queries) maps one onto the other. No counting of extensions is needed.
* **The eager handlers** `epImpl π` (answers from `π`; the table a log of the points determined,
  as in `pmImpl`) and `epImpl0 π` (no table).
* **One query** (`ep_step`), then **any computation** by induction (`condPerm_sim_eqd`): from a
  valid table `L`, `π ← condPerm L` followed by the eager run is the lazy run, jointly in output,
  table and other state. No query bound is needed.
* **Headline** (`rp_eqd_eager`, `prEvent_rp_eq_eager`, `rp_eqd_eager0`): from the empty table, the
  lazy permutation is `π ← $ᵗ Equiv.Perm B` answered eagerly; with or without the table, and for
  every event. Any sampler of `Equiv.Perm B` will do, all are uniform (`condPerm_nil`);
  `instSampleablePerm` is one.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.LazyPerm

/-! ## Uniform on a finite set, and splitting it along a function -/

section UnifFin

variable {P : Type} [DecidableEq P] [Inhabited P]

/-- **Uniform on a finite set** (`default` if it is empty). -/
noncomputable def unifFin (S : Finset P) : ProbComp P :=
  if h : S.Nonempty then
    letI := SampleableType.finsetCoe S h
    Subtype.val <$> ($ᵗ S)
  else pure default

/-- The point mass of a uniform element of a nonempty finite set. -/
theorem prEvent_unifFin_eq (S : Finset P) (h : S.Nonempty) (a : P) :
    Pr{let x ← unifFin S}[x = a] = if a ∈ S then (S.card : ℝ≥0∞)⁻¹ else 0 := by
  let := SampleableType.finsetCoe S h
  rw [unifFin, dite_eq_left h, prEvent_map, SampleableType.prEvent_uniformSample, Fintype.card_coe]
  split_ifs with ha
  · have : (Finset.univ.filter fun x : S => x.val = a) = {⟨a, ha⟩} := by
      ext x; simp [Subtype.ext_iff]
    rw [this, Finset.card_singleton]; simp
  · have : (Finset.univ.filter fun x : S => x.val = a) = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro hx; exact ha (hx ▸ x.2)
    rw [this]; simp

omit [DecidableEq P] in
theorem support_unifFin (S : Finset P) (h : S.Nonempty) : ∀ x ∈ support (unifFin S), x ∈ S := by
  intro x hx
  let := SampleableType.finsetCoe S h
  rw [unifFin, dite_eq_left h] at hx
  erw [support_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact y.2

variable {β : Type} [DecidableEq β] [Inhabited β]

/-- **Splitting a uniform element along a function with equal fibres**: if `f` maps `S` into `U`
and all fibres over `U` have the same size, then `(x, f x)` for `x` uniform on `S` is `(x, y)`
for `y` uniform on `U` and then `x` uniform on the fibre over `y`. -/
theorem unifFin_split (S : Finset P) (f : P → β) (U : Finset β) (hS : S.Nonempty)
    (hf : ∀ x ∈ S, f x ∈ U)
    (heq : ∀ y ∈ U, ∀ y' ∈ U, (S.filter (f · = y)).card = (S.filter (f · = y')).card) :
    (unifFin S >>= fun x => pure (x, f x)) =ᵈ
      (unifFin U >>= fun y => (fun x => (x, y)) <$> unifFin (S.filter (f · = y))) := by
  obtain ⟨x₁, hx₁⟩ := hS
  have hU : U.Nonempty := ⟨f x₁, hf x₁ hx₁⟩
  -- every fibre over `U` is nonempty
  have hfib : ∀ y ∈ U, (S.filter (f · = y)).Nonempty := by
    intro y hy
    have h1 : (S.filter (f · = f x₁)).Nonempty := ⟨x₁, by simp [hx₁]⟩
    rw [← Finset.card_pos, heq y hy (f x₁) (hf x₁ hx₁)]
    exact Finset.card_pos.2 h1
  -- `|S| = |U| · c`
  obtain ⟨c, hc⟩ : ∃ c, ∀ y ∈ U, (S.filter (f · = y)).card = c :=
    ⟨_, fun y hy => heq y hy (f x₁) (hf x₁ hx₁)⟩
  have hcard : S.card = U.card * c := by
    rw [Finset.card_eq_sum_card_fiberwise hf, Finset.sum_congr rfl hc, Finset.sum_const,
      smul_eq_mul]
  refine evalDistEq_of_forall_prEvent_eq_output fun ⟨x₀, y₀⟩ => ?_
  have e : (unifFin S >>= fun x => pure (x, f x)) = (fun x => (x, f x)) <$> unifFin S := by
    rw [map_eq_bind_pure_comp]; rfl
  rw [e, prEvent_map, prEvent_bind_eq_mul_of_unique _ _ y₀ _ fun y _ hy => by
    erw [support_map] at hy
    obtain ⟨x, -, hx⟩ := hy
    simpa using (Prod.ext_iff.1 hx).2]
  rw [prEvent_map, prEvent_unifFin_eq U hU y₀]
  by_cases hy₀ : y₀ ∈ U
  · rw [ite_eq_left hy₀]
    have hF := hfib y₀ hy₀
    rw [prEvent_congr (unifFin (S.filter (f · = y₀))) _ (· = x₀) fun x => by
      simp [Prod.ext_iff], prEvent_unifFin_eq _ hF, hc y₀ hy₀]
    by_cases hx : x₀ ∈ S ∧ f x₀ = y₀
    · rw [prEvent_congr _ _ (· = x₀) fun x => ⟨fun h => (Prod.ext_iff.1 h).1,
          fun h => by subst h; rw [hx.2]⟩,
        prEvent_unifFin_eq _ ⟨x₁, hx₁⟩, ite_eq_left hx.1, ite_eq_left (by simp [hx]), hcard, Nat.cast_mul,
        ENNReal.mul_inv (by simp) (by simp)]
    · rw [ite_eq_right (by simpa using hx), mul_zero]
      refine prEvent_eq_zero_of_forall_mem_support _ _ fun x hx' hxe => hx ?_
      obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hxe
      simp only at h1 h2
      subst h1
      exact ⟨support_unifFin S ⟨x₁, hx₁⟩ x hx', h2⟩
  · rw [ite_eq_right hy₀, zero_mul]
    refine prEvent_eq_zero_of_forall_mem_support _ _ fun x hx' hxe => hy₀ ?_
    obtain ⟨-, h2⟩ := Prod.ext_iff.1 hxe
    simp only at h2
    rw [← h2]
    exact hf x (support_unifFin S ⟨x₁, hx₁⟩ x hx')

omit [DecidableEq P] [Inhabited P] [Inhabited β] in
/-- The fibres of the split are nonempty. -/
theorem fib_nonempty (S : Finset P) (f : P → β) (U : Finset β) (hS : S.Nonempty)
    (hf : ∀ x ∈ S, f x ∈ U)
    (heq : ∀ y ∈ U, ∀ y' ∈ U, (S.filter (f · = y)).card = (S.filter (f · = y')).card) :
    ∀ y ∈ U, (S.filter (f · = y)).Nonempty := by
  obtain ⟨x₁, hx₁⟩ := hS
  intro y hy
  have h1 : (S.filter (f · = f x₁)).Nonempty := ⟨x₁, by simp [hx₁]⟩
  rw [← Finset.card_pos, heq y hy (f x₁) (hf x₁ hx₁)]
  exact Finset.card_pos.2 h1

end UnifFin

/-! ## Permutations extending a table -/

section Ext

variable {B : Type} [Fintype B] [DecidableEq B]

/-- **`π` extends the table**: `π(x) = y` for every record `(x, y, _)`. -/
def Cons (π : Equiv.Perm B) (L : PTab B) : Prop := ∀ e ∈ L, π e.1 = e.2.1

instance (L : PTab B) : DecidablePred (Cons · L) := fun π =>
  inferInstanceAs (Decidable (∀ e ∈ L, π e.1 = e.2.1))

/-- The permutations extending the table. -/
def extSet (L : PTab B) : Finset (Equiv.Perm B) := Finset.univ.filter (Cons · L)

/-- **A table is valid** if some permutation extends it. -/
def Valid (L : PTab B) : Prop := (extSet L).Nonempty

/-- **A uniform permutation conditioned on extending the table.** -/
noncomputable def condPerm (L : PTab B) : ProbComp (Equiv.Perm B) := unifFin (extSet L)

omit [Fintype B] [DecidableEq B] in
theorem cons_append (π : Equiv.Perm B) (L : PTab B) (e : B × B × Bool) :
    Cons π (L ++ [e]) ↔ Cons π L ∧ π e.1 = e.2.1 := by
  simp [Cons, or_imp, forall_and]

theorem mem_extSet {π : Equiv.Perm B} {L : PTab B} : π ∈ extSet L ↔ Cons π L := by
  simp [extSet]

theorem valid_nil : Valid ([] : PTab B) := ⟨1, by simp [extSet, Cons]⟩

theorem support_condPerm {L : PTab B} (hL : Valid L) :
    ∀ π ∈ support (condPerm L), Cons π L := fun π hπ =>
  mem_extSet.1 (support_unifFin _ hL π hπ)

omit [Fintype B] in
theorem fwdFind_some' {L : PTab B} {b y : B} (h : fwdFind L b = some y) :
    ∃ e ∈ L, e.1 = b ∧ e.2.1 = y := by
  unfold fwdFind at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, rfl⟩

omit [Fintype B] in
theorem fwdFind_none' {L : PTab B} {b : B} (h : fwdFind L b = none) : ∀ e ∈ L, e.1 ≠ b := by
  unfold fwdFind at h
  intro e he hb
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  exact h e he (by simpa using hb)

omit [Fintype B] in
theorem invFind_some' {L : PTab B} {c x : B} (h : invFind L c = some x) :
    ∃ e ∈ L, e.2.1 = c ∧ e.1 = x := by
  unfold invFind at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, rfl⟩

omit [Fintype B] in
theorem invFind_none' {L : PTab B} {c : B} (h : invFind L c = none) : ∀ e ∈ L, e.2.1 ≠ c := by
  unfold invFind at h
  intro e he hc
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  exact h e he (by simpa using hc)

/-- A fresh value of the lazy permutation is uniform on the unused blocks. -/
theorem unifCompl_eqd_unifFin [SampleableType B] [Inhabited B] (used : List B)
    (h : ∃ y, y ∉ used) : unifCompl used =ᵈ unifFin (Finset.univ.filter (· ∉ used)) := by
  refine evalDistEq_of_forall_prEvent_eq_output fun a => ?_
  rw [prEvent_unifCompl_eq used h, prEvent_unifFin_eq _ (h.elim fun y hy => ⟨y, by simp [hy]⟩)]
  by_cases ha : a ∈ used <;> simp [ha]

theorem support_unifCompl [SampleableType B] (used : List B) (h : ∃ y, y ∉ used) :
    ∀ y ∈ support (unifCompl used), y ∉ used := by
  intro y hy
  let : Nonempty {y // y ∉ used} := ⟨⟨h.choose, h.choose_spec⟩⟩
  let := SampleableType.subtype B (· ∉ used)
  rw [unifCompl, dite_eq_left h] at hy
  erw [support_map] at hy
  obtain ⟨z, -, rfl⟩ := hy
  exact z.2

/-- **Forward split**: at an input `b` outside the table, `π(b)` of a uniform extension is
uniform on the unused outputs, and given `π(b) = y` the permutation is a uniform extension of the
table with `(b, y)`. -/
theorem condPerm_split_fwd [SampleableType B] {L : PTab B} (hL : Valid L) {b : B} (hb : fwdFind L b = none) :
    (condPerm L >>= fun π => pure (π, π b)) =ᵈ
      (unifCompl (L.map fun e => e.2.1) >>= fun y =>
        (fun π => (π, y)) <$> condPerm (L ++ [(b, y, true)])) := by
  obtain ⟨π₀, -⟩ := id hL
  let : Inhabited B := ⟨π₀ b⟩
  have hfib : ∀ y, (extSet L).filter (fun π => π b = y) = extSet (L ++ [(b, y, true)]) := by
    intro y; ext π; simp [mem_extSet, cons_append]
  have hf : ∀ π ∈ extSet L, π b ∈ Finset.univ.filter (· ∉ L.map fun e => e.2.1) := by
    intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_map, not_exists, not_and]
    intro e he hy
    rw [← mem_extSet.1 hπ e he] at hy
    exact fwdFind_none' hb e he (π.injective hy)
  have heq : ∀ y ∈ Finset.univ.filter (· ∉ L.map fun e => e.2.1),
      ∀ y' ∈ Finset.univ.filter (· ∉ L.map fun e => e.2.1),
      ((extSet L).filter (fun π => π b = y)).card = ((extSet L).filter (fun π => π b = y')).card := by
    intro y hy y' hy'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_map, not_exists,
      not_and] at hy hy'
    refine Finset.card_bij' (fun π _ => Equiv.swap y y' * π) (fun π _ => Equiv.swap y y' * π)
      ?_ ?_ (fun π _ => Equiv.swap_mul_self_mul _ _ _) (fun π _ => Equiv.swap_mul_self_mul _ _ _)
    · intro π hπ
      simp only [Finset.mem_filter, mem_extSet] at hπ ⊢
      refine ⟨fun e he => ?_, by simp [hπ.2]⟩
      rw [Equiv.Perm.mul_apply, hπ.1 e he]
      exact Equiv.swap_apply_of_ne_of_ne (fun h => hy e he h) (fun h => hy' e he h)
    · intro π hπ
      simp only [Finset.mem_filter, mem_extSet] at hπ ⊢
      refine ⟨fun e he => ?_, by simp [hπ.2]⟩
      rw [Equiv.Perm.mul_apply, hπ.1 e he]
      exact Equiv.swap_apply_of_ne_of_ne (fun h => hy e he h) (fun h => hy' e he h)
  have := unifFin_split (extSet L) (fun π => π b) _ hL hf heq
  simp only [hfib] at this
  refine this.trans (EvalDistEq.bind_left (unifCompl_eqd_unifFin _ ?_).symm _)
  obtain ⟨π, hπ⟩ := hL
  exact ⟨π b, by simpa using hf π hπ⟩

/-- **Inverse split**: at an output `c` outside the table, `π⁻¹(c)` of a uniform extension is
uniform on the unused inputs, and given `π⁻¹(c) = x` the permutation is a uniform extension of
the table with `(x, c)`. -/
theorem condPerm_split_inv [SampleableType B] {L : PTab B} (hL : Valid L) {c : B}
    (hc : invFind L c = none) :
    (condPerm L >>= fun π => pure (π, π.symm c)) =ᵈ
      (unifCompl (L.map fun e => e.1) >>= fun x =>
        (fun π => (π, x)) <$> condPerm (L ++ [(x, c, false)])) := by
  obtain ⟨π₀, -⟩ := id hL
  let : Inhabited B := ⟨π₀ c⟩
  have hfib : ∀ x, (extSet L).filter (fun π => π.symm c = x) = extSet (L ++ [(x, c, false)]) := by
    intro x; ext π
    simp only [Finset.mem_filter, mem_extSet, cons_append]
    exact and_congr_right fun _ => (Equiv.symm_apply_eq π).trans eq_comm
  have hf : ∀ π ∈ extSet L, π.symm c ∈ Finset.univ.filter (· ∉ L.map fun e => e.1) := by
    intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_map, not_exists, not_and]
    intro e he hx
    have := mem_extSet.1 hπ e he
    rw [hx, Equiv.apply_symm_apply] at this
    exact invFind_none' hc e he this.symm
  have heq : ∀ x ∈ Finset.univ.filter (· ∉ L.map fun e => e.1),
      ∀ x' ∈ Finset.univ.filter (· ∉ L.map fun e => e.1),
      ((extSet L).filter (fun π => π.symm c = x)).card =
        ((extSet L).filter (fun π => π.symm c = x')).card := by
    intro x hx x' hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_map, not_exists,
      not_and] at hx hx'
    refine Finset.card_bij' (fun π _ => π * Equiv.swap x x') (fun π _ => π * Equiv.swap x x')
      ?_ ?_ (fun π _ => Equiv.mul_swap_mul_self _ _ _) (fun π _ => Equiv.mul_swap_mul_self _ _ _)
    · intro π hπ
      simp only [Finset.mem_filter, mem_extSet] at hπ ⊢
      refine ⟨fun e he => ?_, by simp [Equiv.Perm.mul_def, hπ.2]⟩
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (fun h => hx e he h)
        (fun h => hx' e he h), hπ.1 e he]
    · intro π hπ
      simp only [Finset.mem_filter, mem_extSet] at hπ ⊢
      refine ⟨fun e he => ?_, by simp [Equiv.Perm.mul_def, hπ.2]⟩
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (fun h => hx e he h)
        (fun h => hx' e he h), hπ.1 e he]
  have := unifFin_split (extSet L) (fun π => π.symm c) _ hL hf heq
  simp only [hfib] at this
  refine this.trans (EvalDistEq.bind_left (unifCompl_eqd_unifFin _ ?_).symm _)
  obtain ⟨π, hπ⟩ := hL
  exact ⟨π.symm c, by simpa using hf π hπ⟩

/-- **The table stays valid** after a fresh forward value. -/
theorem valid_fwd [SampleableType B] {L : PTab B} (hL : Valid L) {b : B} (hb : fwdFind L b = none) :
    ∀ y ∈ support (unifCompl (L.map fun e => e.2.1)), Valid (L ++ [(b, y, true)]) := by
  intro y hy
  obtain ⟨π, hπ⟩ := OracleComp.support_nonempty (condPerm (L ++ [(b, y, true)]))
  have hmem : (π, y) ∈ support (unifCompl (L.map fun e => e.2.1) >>= fun y =>
      (fun π => (π, y)) <$> condPerm (L ++ [(b, y, true)])) := by
    rw [mem_support_bind_iff]
    refine ⟨y, hy, ?_⟩
    erw [support_map]
    exact ⟨π, hπ, rfl⟩
  rw [← support_eq_of_evalDistEq (condPerm_split_fwd hL hb)] at hmem
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  obtain ⟨π', hπ', rfl, rfl⟩ := hmem
  exact ⟨π, mem_extSet.2 ((cons_append _ _ _).2 ⟨support_condPerm hL _ hπ', rfl⟩)⟩

/-- **The table stays valid** after a fresh inverse value. -/
theorem valid_inv [SampleableType B] {L : PTab B} (hL : Valid L) {c : B} (hc : invFind L c = none) :
    ∀ x ∈ support (unifCompl (L.map fun e => e.1)), Valid (L ++ [(x, c, false)]) := by
  intro x hx
  obtain ⟨π, hπ⟩ := OracleComp.support_nonempty (condPerm (L ++ [(x, c, false)]))
  have hmem : (π, x) ∈ support (unifCompl (L.map fun e => e.1) >>= fun x =>
      (fun π => (π, x)) <$> condPerm (L ++ [(x, c, false)])) := by
    rw [mem_support_bind_iff]
    refine ⟨x, hx, ?_⟩
    erw [support_map]
    exact ⟨π, hπ, rfl⟩
  rw [← support_eq_of_evalDistEq (condPerm_split_inv hL hc)] at hmem
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  obtain ⟨π', hπ', rfl, rfl⟩ := hmem
  exact ⟨π, mem_extSet.2 ((cons_append _ _ _).2 ⟨support_condPerm hL _ hπ', by simp⟩)⟩

end Ext


/-! ## The eager permutation, and the lazy one is it -/

section Eager

variable {ι : Type} {A : ι → Type} {B : Type} [Fintype B] [DecidableEq B] {σ : Type}
  (pt : ι → Option B) (implC : (i : ι) → Option B → StateT σ ProbComp (A i))

/-- **An eager forward step**: answer `π(b)`; record it if `b` is not yet in the table. -/
def fwdE (π : Equiv.Perm B) (b : B) (L : PTab B) : B × PTab B :=
  match fwdFind L b with
  | some _ => (π b, L)
  | none => (π b, L ++ [(b, π b, true)])

/-- **An eager inverse step**: answer `π⁻¹(c)`; record it if `c` is not yet in the table. -/
def invE (π : Equiv.Perm B) (c : B) (L : PTab B) : B × PTab B :=
  match invFind L c with
  | some _ => (π.symm c, L)
  | none => (π.symm c, L ++ [(π.symm c, c, false)])

/-- **The eager permutation `π`, with the table as a log**: the queries are answered from `π`
(`π(b)`, `π⁻¹(c)`, and `π(pt i)` for an other query); the table records the points determined, as
in `pmImpl`. -/
def epImpl (π : Equiv.Perm B) : QueryImpl (specPm A B) (StateT (PTab B × σ) ProbComp)
  | .inl i => StateT.mk fun s => match pt i with
    | none => (fun u => (u.1, (s.1, u.2))) <$> (implC i none).run s.2
    | some b =>
        (fun u => (u.1, ((fwdE π b s.1).2, u.2))) <$> (implC i (some (fwdE π b s.1).1)).run s.2
  | .inr (true, b) => StateT.mk fun s => pure ((fwdE π b s.1).1, ((fwdE π b s.1).2, s.2))
  | .inr (false, c) => StateT.mk fun s => pure ((invE π c s.1).1, ((invE π c s.1).2, s.2))

/-- **The eager permutation `π`**, without a table. -/
def epImpl0 (π : Equiv.Perm B) : QueryImpl (specPm A B) (StateT σ ProbComp)
  | .inl i => implC i ((pt i).map π)
  | .inr (true, b) => pure (π b)
  | .inr (false, c) => pure (π.symm c)

variable [SampleableType B]

/-- **A forward step, eager against lazy**, from a valid table. -/
theorem fwd_step {L : PTab B} (hL : Valid L) (b : B) {γ : Type}
    (G : Equiv.Perm B → B × PTab B → ProbComp γ) :
    (condPerm L >>= fun π => G π (fwdE π b L)) =ᵈ
      (fwdS unifCompl b L >>= fun r => condPerm r.2 >>= fun π => G π r) := by
  cases h : fwdFind L b with
  | some y =>
    have hy : ∀ π ∈ support (condPerm L), fwdE π b L = (y, L) := by
      intro π hπ
      obtain ⟨e, he, rfl, rfl⟩ := fwdFind_some' h
      simp only [fwdE, h, support_condPerm hL π hπ e he]
    simp only [fwdS, h, pure_bind]
    exact EvalDistEq.bind_congr_of_support _ fun π hπ => by rw [hy π hπ]
  | none =>
    have hE : ∀ π : Equiv.Perm B, fwdE π b L = (π b, L ++ [(b, π b, true)]) := by
      intro π; simp only [fwdE, h]
    simp only [hE, fwdS, h]
    have := (condPerm_split_fwd hL h).bind_left fun p => G p.1 (p.2, L ++ [(b, p.2, true)])
    simp only [bind_assoc, pure_bind, bind_map_left] at this
    simpa only [bind_map_left] using this

/-- **An inverse step, eager against lazy**, from a valid table. -/
theorem inv_step {L : PTab B} (hL : Valid L) (c : B) {γ : Type}
    (G : Equiv.Perm B → B × PTab B → ProbComp γ) :
    (condPerm L >>= fun π => G π (invE π c L)) =ᵈ
      (invS unifCompl c L >>= fun r => condPerm r.2 >>= fun π => G π r) := by
  cases h : invFind L c with
  | some x =>
    have hx : ∀ π ∈ support (condPerm L), invE π c L = (x, L) := by
      intro π hπ
      obtain ⟨e, he, rfl, rfl⟩ := invFind_some' h
      have := support_condPerm hL π hπ e he
      simp only [invE, h]
      rw [← this, Equiv.symm_apply_apply]
    simp only [invS, h, pure_bind]
    exact EvalDistEq.bind_congr_of_support _ fun π hπ => by rw [hx π hπ]
  | none =>
    have hE : ∀ π : Equiv.Perm B, invE π c L = (π.symm c, L ++ [(π.symm c, c, false)]) := by
      intro π; simp only [invE, h]
    simp only [hE, invS, h]
    have := (condPerm_split_inv hL h).bind_left fun p => G p.1 (p.2, L ++ [(p.2, c, false)])
    simp only [bind_assoc, pure_bind, bind_map_left] at this
    simpa only [bind_map_left] using this

/-- **One query, eager against lazy**: drawing `π` as a uniform extension of a valid table and
answering eagerly is answering lazily and then drawing `π` as a uniform extension of the new
table. -/
theorem ep_step (t : ι ⊕ (Bool × B)) {L : PTab B} (hL : Valid L) (s : σ) {γ : Type}
    (K : Equiv.Perm B → (specPm A B).Range t × (PTab B × σ) → ProbComp γ) :
    (condPerm L >>= fun π => (epImpl pt implC π t).run (L, s) >>= K π) =ᵈ
      ((rpImpl pt implC t).run (L, s) >>= fun z => condPerm z.2.1 >>= fun π => K π z) := by
  rcases t with i | ⟨_ | _, b⟩
  · simp only [epImpl, rpImpl, pmImpl, StateT.run_mk]
    cases hp : pt i with
    | none =>
      simp only [bind_map_left]
      exact VoleMole.ROM.OneMore.eqd_swap _ _ _
    | some b =>
      dsimp only
      simp only [bind_assoc, bind_map_left]
      refine (fwd_step hL b fun π r => (implC i (some r.1)).run s >>= fun a =>
        K π (a.1, r.2, a.2)).trans (EvalDistEq.bind_right _ fun r => ?_)
      exact VoleMole.ROM.OneMore.eqd_swap _ _ _
  · simp only [epImpl, rpImpl, pmImpl, StateT.run_mk, pure_bind, bind_map_left]
    exact inv_step hL b fun π r => K π (r.1, (r.2, s))
  · simp only [epImpl, rpImpl, pmImpl, StateT.run_mk, pure_bind, bind_map_left]
    exact fwd_step hL b fun π r => K π (r.1, (r.2, s))

omit [Fintype B] in
theorem fwdS_valid [Fintype B] {L : PTab B} (hL : Valid L) (b : B) :
    ∀ r ∈ support (fwdS unifCompl b L), Valid r.2 := by
  intro r hr
  unfold fwdS at hr
  cases h : fwdFind L b with
  | some y => rw [h] at hr; simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hL
  | none =>
    rw [h] at hr; erw [support_map] at hr
    obtain ⟨y, hy, rfl⟩ := hr
    exact valid_fwd hL h y hy

theorem invS_valid {L : PTab B} (hL : Valid L) (c : B) :
    ∀ r ∈ support (invS unifCompl c L), Valid r.2 := by
  intro r hr
  unfold invS at hr
  cases h : invFind L c with
  | some y => rw [h] at hr; simp only [support_pure, Set.mem_singleton_iff] at hr; subst hr; exact hL
  | none =>
    rw [h] at hr; erw [support_map] at hr
    obtain ⟨y, hy, rfl⟩ := hr
    exact valid_inv hL h y hy

/-- **The lazy permutation keeps the table valid.** -/
theorem rp_valid (t : ι ⊕ (Bool × B)) {L : PTab B} (hL : Valid L) (s : σ) :
    ∀ z ∈ support ((rpImpl pt implC t).run (L, s)), Valid z.2.1 := by
  intro z hz
  rcases t with i | ⟨_ | _, b⟩
  · simp only [rpImpl, pmImpl, StateT.run_mk] at hz
    cases hp : pt i with
    | none =>
      rw [hp] at hz; erw [support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz; exact hL
    | some b =>
      rw [hp] at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨r, hr, hz⟩ := hz
      erw [support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact fwdS_valid hL b r hr
  · simp only [rpImpl, pmImpl, StateT.run_mk] at hz; erw [support_map] at hz
    obtain ⟨r, hr, rfl⟩ := hz; exact invS_valid hL b r hr
  · simp only [rpImpl, pmImpl, StateT.run_mk] at hz; erw [support_map] at hz
    obtain ⟨r, hr, rfl⟩ := hz; exact fwdS_valid hL b r hr

/-- **The lazy permutation is a uniform extension of the table, drawn eagerly**: from a valid
table `L`, running a computation against the lazy permutation `rpImpl` is drawing `π` uniformly
among the permutations that extend `L` and running it against `π` (`epImpl`): same joint
distribution of output, table and other state. No query bound is needed. -/
theorem condPerm_sim_eqd {α : Type} (oa : OracleComp (specPm A B) α) :
    ∀ (L : PTab B) (s : σ), Valid L →
      (condPerm L >>= fun π => (simulateQ (epImpl pt implC π) oa).run (L, s)) =ᵈ
        (simulateQ (rpImpl pt implC) oa).run (L, s) := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro L s _
    simp only [simulateQ_pure, StateT.run_pure]
    exact LazyIdeal.eqd_bind_unused _ _
  | query_bind t k ih =>
    intro L s hL
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    refine (ep_step pt implC t hL s fun π z =>
      (simulateQ (epImpl pt implC π) (k z.1)).run z.2).trans ?_
    exact EvalDistEq.bind_congr_of_support _ fun z hz =>
      ih z.1 z.2.1 z.2.2 (rp_valid pt implC t hL s z hz)

/-! ### From the empty table: the uniform permutation -/

omit [SampleableType B] in
/-- **The uniform permutation** (for proofs; never run). -/
noncomputable instance instSampleablePerm : SampleableType (Equiv.Perm B) :=
  SampleableType.ofFintype _

omit [SampleableType B] in
theorem extSet_nil : extSet ([] : PTab B) = Finset.univ := by
  ext π; simp [extSet, Cons]

omit [SampleableType B] in
/-- **With the empty table, the conditioned permutation is the uniform permutation** (for any
sampler of `Equiv.Perm B`: all are uniform). -/
theorem condPerm_nil [SampleableType (Equiv.Perm B)] :
    condPerm ([] : PTab B) =ᵈ ($ᵗ Equiv.Perm B : ProbComp (Equiv.Perm B)) := by
  refine evalDistEq_of_forall_prEvent_eq_output fun π => ?_
  rw [condPerm, prEvent_unifFin_eq _ valid_nil, SampleableType.prEvent_uniformSample_eq_singleton,
    extSet_nil]
  simp

/-- **The lazy permutation is the eager uniform permutation**: for every oracle computation (no
query bound), running it against the lazy random permutation `rpImpl` from the empty table has
the same joint distribution of output, table and other state as drawing `π` uniformly from
`Equiv.Perm B` and running it against `π` (`epImpl`, the table a log of the points determined). -/
theorem rp_eqd_eager [SampleableType (Equiv.Perm B)] {α : Type} (oa : OracleComp (specPm A B) α)
    (s : σ) :
    ((($ᵗ Equiv.Perm B : ProbComp (Equiv.Perm B))) >>= fun π =>
        (simulateQ (epImpl pt implC π) oa).run ([], s)) =ᵈ
      (simulateQ (rpImpl pt implC) oa).run ([], s) :=
  (condPerm_nil.symm.bind_left _).trans (condPerm_sim_eqd pt implC oa [] s valid_nil)

/-- **Every event** has the same probability under the lazy and the eager permutation. -/
theorem prEvent_rp_eq_eager [SampleableType (Equiv.Perm B)] {α : Type}
    (oa : OracleComp (specPm A B) α) (s : σ) (E : α × PTab B × σ → Prop) :
    Pr{let π ← ($ᵗ Equiv.Perm B : ProbComp (Equiv.Perm B))
       let z ← (simulateQ (epImpl pt implC π) oa).run ([], s)}[E z] =
      Pr{let z ← (simulateQ (rpImpl pt implC) oa).run ([], s)}[E z] := by
  have := (rp_eqd_eager pt implC oa s).prEvent_eq E
  rw [map_bind] at this
  exact this

omit [Fintype B] [SampleableType B] in
theorem fwdE_fst (π : Equiv.Perm B) (b : B) (L : PTab B) : (fwdE π b L).1 = π b := by
  unfold fwdE; split <;> rfl

omit [Fintype B] [SampleableType B] in
theorem invE_fst (π : Equiv.Perm B) (c : B) (L : PTab B) : (invE π c L).1 = π.symm c := by
  unfold invE; split <;> rfl

omit [Fintype B] [SampleableType B] in
/-- **The log does not change the answers**: forgetting the table of `epImpl π` gives `epImpl0 π`. -/
theorem epImpl_proj (π : Equiv.Perm B) {α : Type} (oa : OracleComp (specPm A B) α) (L : PTab B)
    (s : σ) :
    (fun z => (z.1, z.2.2)) <$> (simulateQ (epImpl pt implC π) oa).run (L, s) =ᵈ
      (simulateQ (epImpl0 pt implC π) oa).run s := by
  refine LazyIdeal.simulateQ_proj_eqd_inv (epImpl pt implC π) (epImpl0 pt implC π) Prod.snd
    (fun _ => True) (fun _ _ _ _ _ => trivial) (fun q st _ => ?_) oa (L, s) trivial
  rcases q with i | ⟨_ | _, b⟩
  · simp only [epImpl, epImpl0, StateT.run_mk]
    cases hp : pt i with
    | none =>
      simp only [Option.map_none, Functor.map_map]
      exact EvalDistEq.of_forall_prEvent_eq fun p => by rw [prEvent_map]; rfl
    | some b =>
      simp only [Option.map_some, Functor.map_map, fwdE_fst]
      exact EvalDistEq.of_forall_prEvent_eq fun p => by rw [prEvent_map]; rfl
  · simp only [epImpl, epImpl0, StateT.run_mk, map_pure, invE_fst]
    exact EvalDistEq.rfl
  · simp only [epImpl, epImpl0, StateT.run_mk, map_pure, fwdE_fst]
    exact EvalDistEq.rfl

/-- **The lazy permutation is the eager uniform permutation, without the table**: output and
other state of a run against `rpImpl` are those of a run against a uniform `π` (`epImpl0`). -/
theorem rp_eqd_eager0 [SampleableType (Equiv.Perm B)] {α : Type} (oa : OracleComp (specPm A B) α)
    (s : σ) :
    ((($ᵗ Equiv.Perm B : ProbComp (Equiv.Perm B))) >>= fun π =>
        (simulateQ (epImpl0 pt implC π) oa).run s) =ᵈ
      (fun z => (z.1, z.2.2)) <$> (simulateQ (rpImpl pt implC) oa).run ([], s) := by
  refine EvalDistEq.trans ?_ ((rp_eqd_eager pt implC oa s).map _)
  rw [map_bind]
  exact EvalDistEq.bind_right _ fun π => (epImpl_proj pt implC π oa [] s).symm

end Eager

end VoleMole.Assumptions.LazyPerm
