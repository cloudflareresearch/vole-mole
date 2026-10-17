import VoleMole.Privacy.Basic

/-!
# Uniform pushforwards (`lean/docs/zk.md` H5–H7, for the executable prover)

The perfect hybrids re-parametrise the tape: a map `f : α → β` between finite types **pushes
uniform to uniform** (`UPush f`, i.e. `Privacy.Close 0 f id`: under a uniform tape, `f`'s output is
uniform on `β`) if it is a bijection, a projection, a translation of a surjective additive map, or
a composition, product or shear of such maps. The zero-knowledge theorem
(`ZK/IdealSim.lean`) decomposes the ideal-tape prover's proof fields this way.

* `Balanced f`: every fiber has `|α| / |β|` elements; `Balanced.upush`.
* `upush_equiv`, `UPush.comp`, `upush_fst`, `upush_snd`, `UPush.prodMap`, `upush_shear`,
  `upush_shear'` (the second coordinate re-parametrised for each value of the first), `upush_pi`
  (coordinatewise), `upush_addHom` (a surjective additive map plus a constant), `UPush.congr`.
* `UPush.close`: if `f` pushes uniform to uniform, an experiment that reads the tape only through
  `f` is the experiment on a uniform `β`.
-/

open Finset

namespace VoleMole.ZK

open VoleMole.Privacy

variable {α β γ δ ι : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

set_option linter.unusedSectionVars false

/-- `f` pushes the uniform distribution on `α` to the uniform distribution on `β`. -/
def UPush (f : α → β) : Prop := Close 0 f id

/-- Every fiber of `f` has `|α| / |β|` elements. -/
def Balanced (f : α → β) : Prop := ∀ b, Nat.card {a // f a = b} * Nat.card β = Nat.card α

theorem UPush.close {O : Type*} {f : α → β} (h : UPush f) (X : β → O) :
    Close 0 (fun a => X (f a)) X :=
  h.map X

theorem UPush.congr {f g : α → β} (h : UPush f) (hfg : ∀ a, g a = f a) : UPush g :=
  Close.congr h hfg fun _ => rfl

theorem upush_id : UPush (id : α → α) := close_self le_rfl _

theorem upush_equiv (e : α ≃ β) : UPush e :=
  close_equiv e id

theorem UPush.comp {f : α → β} {g : β → γ} (hf : UPush f) (hg : UPush g) : UPush (g ∘ f) := by
  have := ((hf.map g).trans hg).mono (le_of_eq (add_zero 0))
  exact this

theorem upush_fst [Nonempty β] : UPush (Prod.fst : α × β → α) :=
  close_prod_fst (β := β) (X := (id : α → α))

theorem upush_snd [Nonempty α] : UPush (Prod.snd : α × β → β) :=
  close_prod_snd (α := α) (X := (id : β → β))

/-- **Shear.** If `g a` pushes uniform to uniform for every `a`, so does `(a, b) ↦ (a, g a b)`. -/
theorem upush_shear [Nonempty α] {g : α → β → γ} (h : ∀ a, UPush (g a)) :
    UPush (fun x : α × β => (x.1, g x.1 x.2)) := by
  exact Close.prod_right (X := fun a b => (a, g a b)) (Y := fun a (c : γ) => (a, c))
    fun a => (h a).map fun c => (a, c)

/-- **Shear, second coordinate fixed.** -/
theorem upush_shear' [Nonempty β] {g : β → α → γ} (h : ∀ b, UPush (g b)) :
    UPush (fun x : α × β => (g x.2 x.1, x.2)) := by
  exact Close.prod_left (X := fun a b => (g b a, b)) (Y := fun (c : γ) b => (c, b))
    fun b => (h b).map fun c => (c, b)

theorem UPush.prodMap [Nonempty α] [Nonempty δ] {f : α → β} {g : γ → δ} (hf : UPush f)
    (hg : UPush g) : UPush (Prod.map f g) := by
  have h1 : UPush (fun x : α × γ => (x.1, g x.2)) := upush_shear (g := fun _ => g) fun _ => hg
  have h2 : UPush (fun x : α × δ => (f x.1, x.2)) := upush_shear' (g := fun _ => f) fun _ => hf
  have h3 := UPush.comp h1 h2
  intro D
  simpa [Function.comp_def, Prod.map] using h3 D

/-! ## Balanced maps -/

lemma Balanced.card_fiber [DecidableEq β] {f : α → β} (h : Balanced f) (b : β) :
    (#{a | f a = b} : ℝ) * Fintype.card β = Fintype.card α := by
  have := h b
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype] at this
  exact_mod_cast this

theorem Balanced.upush [Nonempty α] {f : α → β} (h : Balanced f) : UPush f := by
  classical
  intro D
  rw [pr_def, pr_def]
  simp only [id]
  rcases isEmpty_or_nonempty β with hβ | hβ
  · have : IsEmpty α := ⟨fun a => hβ.false (f a)⟩
    simp
  obtain ⟨b0⟩ := hβ
  have hβ0 : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos_iff.2 ⟨b0⟩
  have hsum : (#{a | D (f a)} : ℝ) = ∑ b ∈ ({b | D b} : Finset β), (#{a | f a = b} : ℝ) := by
    rw [card_eq_sum_card_fiberwise (f := f) (t := ({b | D b} : Finset β))
      (fun a ha => by simpa using ha)]
    push_cast
    refine sum_congr rfl fun b hb => ?_
    congr 2
    ext a
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hb, h⟩⟩
  have hfib : ∀ b, (#{a | f a = b} : ℝ) = Fintype.card α / Fintype.card β := fun b => by
    rw [eq_div_iff hβ0.ne', h.card_fiber b]
  rw [hsum]
  simp only [hfib, sum_const, nsmul_eq_mul]
  have hα' : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  simp

/-- Coordinatewise maps of balanced maps are balanced. -/
theorem Balanced.pi {n : ℕ} {A B : Fin n → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    {f : ∀ i, A i → B i} (h : ∀ i, Balanced (f i)) :
    Balanced (fun (x : ∀ i, A i) i => f i (x i)) := by
  intro y
  have e : {x : ∀ i, A i // (fun i => f i (x i)) = y} ≃ ∀ i, {a : A i // f i a = y i} :=
    (Equiv.subtypeEquivRight fun x => funext_iff).trans
      (Equiv.subtypePiEquivPi (p := fun i a => f i a = y i))
  rw [Nat.card_congr e, Nat.card_pi, Nat.card_pi, Nat.card_pi, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => h i (y i)

/-- **A surjective additive map plus a constant** is balanced. -/
theorem balanced_addHom [AddCommGroup α] [AddCommGroup β] (f : α →+ β)
    (hf : Function.Surjective f) (k : β) : Balanced (fun a => f a + k) := by
  classical
  have hfib : ∀ b b', #{a | f a = b} = #{a | f a = b'} := fun b b' =>
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf b) (hf b')
  have htot : ∀ b, #{a | f a = b} * Fintype.card β = Fintype.card α := by
    intro b
    have := card_eq_sum_card_fiberwise (s := (univ : Finset α)) (t := (univ : Finset β)) (f := f)
      (fun _ _ => mem_univ _)
    rw [card_univ] at this
    rw [this]
    simp only [Finset.sum_congr rfl fun b' _ => hfib b' b, sum_const, card_univ,
      smul_eq_mul, mul_comm]
  intro b
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  have : (univ.filter fun a => f a + k = b) = univ.filter fun a => f a = b - k := by
    ext a; simp [eq_sub_iff_add_eq]
  rw [this]
  exact htot _

theorem upush_pi {n : ℕ} {A B : Fin n → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, Nonempty (A i)] {f : ∀ i, A i → B i} (h : ∀ i, Balanced (f i)) :
    UPush (fun (x : ∀ i, A i) i => f i (x i)) :=
  (Balanced.pi h).upush

theorem upush_addHom [Nonempty α] [AddCommGroup α] [AddCommGroup β] (f : α →+ β)
    (hf : Function.Surjective f) (k : β) : UPush (fun a => f a + k) :=
  (balanced_addHom f hf k).upush

theorem Balanced.congr {f g : α → β} (h : Balanced f) (hfg : ∀ a, g a = f a) : Balanced g := by
  have : g = f := funext hfg
  rw [this]; exact h

theorem balanced_equiv (e : α ≃ β) : Balanced e := by
  intro b
  have : Nat.card {a // e a = b} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun x y => Subtype.ext (e.injective (x.2.trans y.2.symm))⟩, ⟨⟨e.symm b, by simp⟩⟩⟩
  rw [this, one_mul, Nat.card_congr e]

/-- A balanced map composed with an equivalence on its target is balanced. -/
theorem Balanced.comp_equiv {f : α → β} (h : Balanced f) (e : β ≃ γ) : Balanced (e ∘ f) := by
  intro c
  have e' : {a // (e ∘ f) a = c} ≃ {a // f a = e.symm c} :=
    Equiv.subtypeEquivRight fun a => by simp [Equiv.eq_symm_apply]
  rw [Nat.card_congr e', ← Nat.card_congr e]
  exact h _

/-- A balanced map precomposed with an equivalence is balanced. -/
theorem Balanced.equiv_comp {f : β → γ} (h : Balanced f) (e : α ≃ β) : Balanced (f ∘ e) := by
  intro c
  have e' : {a // (f ∘ e) a = c} ≃ {b // f b = c} :=
    (e.subtypeEquiv fun a => by simp)
  rw [Nat.card_congr e', Nat.card_congr e]
  exact h c

/-- The first projection is balanced. -/
theorem balanced_fst : Balanced (Prod.fst : α × β → α) := by
  intro a
  have e : {x : α × β // x.1 = a} ≃ β :=
    { toFun := fun x => x.1.2, invFun := fun b => ⟨(a, b), rfl⟩,
      left_inv := fun x => by obtain ⟨⟨a', b⟩, h⟩ := x; subst h; rfl,
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, mul_comm]

end VoleMole.ZK
