import VoleMole.Privacy.Basic

/-!
# Hybrid arguments: bad events, guessing and programming a random table

Generic counting lemmas for the hybrid hops of `ZK/Hops.lean`, in the style of
`Privacy/Basic.lean` (uniform tapes, `pr`, `Close`).

* **Bad events.** `pr_mono`, `pr_or_le`, `pr_exists_le_sum` (the union bound over a finite index);
  `abs_pr_sub_le_of_agree` and `Close.of_agree`: two experiments on the same tape that agree
  outside an event `bad` are `pr bad`-close (identical until bad).
* **Composition.** `Close.prod`: closeness of independent coordinates adds up; `Close.pi`: the
  hybrid over `n` independent coordinates costs `n·ε` (e.g. per hidden path of the BAVC).
* **Guessing.** `pr_mem_le`: a uniform `a` lands, through an injective encoding, in a fixed set of
  `q` candidates with probability `≤ q / |α|`; `pr_mem_indep_le`: the same when the candidates
  depend on independent coins (an adversary's queries, made without seeing `a`).
* **A random table, programmed** (the random-oracle step of a hop, eagerly sampled on a finite key
  set `K`). `programAt x u g` is the table `g` with the answers `u i` at the distinct points
  `x i`. `programEquiv`: `(g, u) ↦ (programAt x u g, g ∘ x)` is a bijection (an involution), so
  * `pr_program_eq`: **programming is perfect.** A run that reads a uniform table `g` and its
    answers at the points `x c` (for coins `c`) has the law of the run that reads independent
    uniform answers `u` and the table programmed with them;
  * `abs_pr_hidden_le`: **identical until a programmed point is read.** Against the
    *unprogrammed* table, the run differs only if it reads `g` at one of the points: every run
    that reads `g` only on a set `Q c u g` (`hQ`) is `Pr[∃ i, x c i ∈ Q c u g]`-close.
  * `close_restrict`: in particular a uniform table read at distinct points is uniform there.
  These are the random-oracle hops H1, H2 (grinding) and H6 of `lean/docs/zk.md` §6 on a finite
  key set, with the adversary as a deterministic function of its view and of the table that reads
  the table on a set of at most `q` keys (its queries, `hQ`).
-/

open Finset

namespace VoleMole.Privacy

/-! ## Bad events -/

section Bad

variable {α γ : Type*} [Fintype α]

theorem pr_mono {P Q : α → Prop} (h : ∀ a, P a → Q a) : pr α P ≤ pr α Q := by
  classical
  rw [pr_def, pr_def]
  gcongr
  exact h _

theorem pr_or_le (P Q : α → Prop) : pr α (fun a => P a ∨ Q a) ≤ pr α P + pr α Q := by
  classical
  rw [pr_def, pr_def, pr_def, ← add_div]
  gcongr
  rw [Finset.filter_or]
  exact_mod_cast Finset.card_union_le _ _

/-- **The union bound** over a finite index. -/
theorem pr_exists_le_sum {ι : Type*} [Fintype ι] (P : ι → α → Prop) :
    pr α (fun a => ∃ i, P i a) ≤ ∑ i, pr α (P i) := by
  classical
  simp only [pr_def]
  rw [← Finset.sum_div]
  gcongr
  have : (univ.filter fun a => ∃ i, P i a) = univ.biUnion fun i => univ.filter (P i) := by
    ext a; simp
  rw [this]
  exact_mod_cast Finset.card_biUnion_le

theorem pr_le_one (P : α → Prop) : pr α P ≤ 1 := by
  classical
  rw [pr_def]
  rcases isEmpty_or_nonempty α with h | h
  · simp
  · rw [div_le_one (by exact_mod_cast Fintype.card_pos)]
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_univ (α := α)).le

/-- **Identical until bad**: two events that agree outside `bad` differ in probability by at most
`Pr[bad]`. -/
theorem abs_pr_sub_le_of_agree (P Q bad : α → Prop) (h : ∀ a, ¬ bad a → (P a ↔ Q a)) :
    |pr α P - pr α Q| ≤ pr α bad := by
  have h1 : pr α P ≤ pr α Q + pr α bad :=
    (pr_mono fun a hp => by
      by_cases hb : bad a
      · exact Or.inr hb
      · exact Or.inl ((h a hb).1 hp)).trans (pr_or_le Q bad)
  have h2 : pr α Q ≤ pr α P + pr α bad :=
    (pr_mono fun a hq => by
      by_cases hb : bad a
      · exact Or.inr hb
      · exact Or.inl ((h a hb).2 hq)).trans (pr_or_le P bad)
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Two experiments on the same tape that agree outside `bad` are `Pr[bad]`-close. -/
theorem Close.of_agree {X Y : α → γ} (bad : α → Prop) (h : ∀ a, ¬ bad a → X a = Y a) :
    Close (pr α bad) X Y :=
  fun D => abs_pr_sub_le_of_agree _ _ bad fun a hb => by rw [h a hb]

/-- **Two independent hops** add up: componentwise closeness of independent coordinates. -/
theorem Close.prod {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype β₁]
    [Fintype β₂] [Nonempty α₁] [Nonempty β₂] {ε₁ ε₂ : ℝ} {X₁ : α₁ → γ₁} {Y₁ : β₁ → γ₁}
    {X₂ : α₂ → γ₂} {Y₂ : β₂ → γ₂} (h₁ : Close ε₁ X₁ Y₁) (h₂ : Close ε₂ X₂ Y₂) :
    Close (ε₁ + ε₂) (fun a : α₁ × α₂ => (X₁ a.1, X₂ a.2)) (fun b : β₁ × β₂ => (Y₁ b.1, Y₂ b.2)) := by
  intro D
  have e2 := abs_pr_prod_sub_le (fun a : α₁ × α₂ => D (X₁ a.1, X₂ a.2))
    (fun a : α₁ × β₂ => D (X₁ a.1, Y₂ a.2)) fun a₁ => h₂ fun c => D (X₁ a₁, c)
  have e1 := abs_pr_prod_sub_le' (fun a : α₁ × β₂ => D (X₁ a.1, Y₂ a.2))
    (fun b : β₁ × β₂ => D (Y₁ b.1, Y₂ b.2)) fun b₂ => h₁ fun c => D (c, Y₂ b₂)
  have := abs_sub_le (pr (α₁ × α₂) fun a => D (X₁ a.1, X₂ a.2))
    (pr (α₁ × β₂) fun a => D (X₁ a.1, Y₂ a.2)) (pr (β₁ × β₂) fun b => D (Y₁ b.1, Y₂ b.2))
  linarith

/-- **The hybrid over `n` independent coordinates** (e.g. the `τ` hidden paths): `n·ε`. -/
theorem Close.pi {α β γ : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] {ε : ℝ}
    {X : α → γ} {Y : β → γ} (h : Close ε X Y) :
    ∀ n : ℕ, Close (n * ε) (fun a : Fin n → α => fun i => X (a i))
      (fun b : Fin n → β => fun i => Y (b i))
  | 0 => by
    have h0 : ∀ f g : Fin 0 → γ, f = g := fun f g => funext fun i => i.elim0
    refine (close_const (α := Fin 0 → α) (β := Fin 0 → β) (le_of_eq (by simp))
      (fun i : Fin 0 => i.elim0 : Fin 0 → γ)).congr (fun _ => h0 _ _) fun _ => h0 _ _
  | n + 1 => by
    have hn := h.prod (Close.pi h n)
    let eα := (Fin.consEquiv (fun _ : Fin (n + 1) => α)).symm
    let eβ := (Fin.consEquiv (fun _ : Fin (n + 1) => β)).symm
    let F : γ × (Fin n → γ) → (Fin (n + 1) → γ) := fun c => Fin.cons c.1 c.2
    have e1 := close_equiv eα (fun a : α × (Fin n → α) => F (X a.1, fun i => X (a.2 i)))
    have e2 := close_equiv eβ (fun b : β × (Fin n → β) => F (Y b.1, fun i => Y (b.2 i)))
    refine ((e1.trans ((hn.map F).trans e2.symm)).mono (by push_cast; linarith)).congr
      (fun a => ?_) fun b => ?_
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [eα, F, Fin.tail]
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [eβ, F, Fin.tail]

end Bad

/-! ## Guessing -/

section Guess

variable {α β K : Type*} [Fintype α] [Fintype β]

/-- **A uniform value is in a fixed set of `q` candidates with probability `≤ q / |α|`**, through
an injective encoding. -/
theorem pr_mem_le (enc : α → K) (henc : Function.Injective enc) (S : Finset K) :
    pr α (fun a => enc a ∈ S) ≤ S.card / Fintype.card α := by
  classical
  rw [pr_def]
  gcongr
  exact_mod_cast Finset.card_le_card_of_injOn enc (fun a ha => by simpa using ha)
    (fun a _ b _ h => henc h)

/-- The same when the candidates `S b` are chosen from independent coins `b` (at most `q` of them):
`Pr[enc a ∈ S b] ≤ q / |α|`. -/
theorem pr_mem_indep_le [Nonempty β] (enc : α → K) (henc : Function.Injective enc)
    (S : β → Finset K) {q : ℕ} (hS : ∀ b, (S b).card ≤ q) :
    pr (α × β) (fun p => enc p.1 ∈ S p.2) ≤ q / Fintype.card α := by
  rw [← pr_equiv (Equiv.prodComm β α), pr_prod]
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hβ]
  calc ∑ b, pr α (fun a => enc ((Equiv.prodComm β α) (b, a)).1 ∈ S ((Equiv.prodComm β α) (b, a)).2)
      ≤ ∑ _b : β, (q : ℝ) / Fintype.card α := Finset.sum_le_sum fun b _ =>
        (pr_mem_le enc henc (S b)).trans (by gcongr; exact_mod_cast hS b)
    _ = q / Fintype.card α * Fintype.card β := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

end Guess

/-! ## A random table, programmed at hidden points -/

section Program

variable {K R ι C : Type*}

/-- The table `g` with the answers `u i` at the points `x i` (`g` elsewhere). -/
noncomputable def programAt (x : ι → K) (u : ι → R) (g : K → R) : K → R :=
  Function.extend x u g

lemma programAt_apply_pt {x : ι → K} (hx : Function.Injective x) (u : ι → R) (g : K → R) (i : ι) :
    programAt x u g (x i) = u i :=
  hx.extend_apply u g i

lemma programAt_apply_of_ne {x : ι → K} (u : ι → R) (g : K → R) {k : K} (hk : ∀ i, x i ≠ k) :
    programAt x u g k = g k :=
  Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hk i hi

lemma programAt_comp {x : ι → K} (hx : Function.Injective x) (u : ι → R) (g : K → R) :
    programAt x u g ∘ x = u :=
  funext fun i => programAt_apply_pt hx u g i

lemma programAt_programAt {x : ι → K} (hx : Function.Injective x) (u : ι → R) (g : K → R) :
    programAt x (g ∘ x) (programAt x u g) = g := by
  classical
  funext k
  by_cases hk : ∃ i, x i = k
  · obtain ⟨i, rfl⟩ := hk
    rw [programAt_apply_pt hx]; rfl
  · push Not at hk
    rw [programAt_apply_of_ne _ _ hk, programAt_apply_of_ne _ _ hk]

variable [Fintype K] [DecidableEq K] [Fintype R] [Fintype ι] [DecidableEq ι] [Fintype C]

/-- **Programming as a bijection**: `(g, u) ↦ (programAt x u g, g ∘ x)`, an involution. -/
noncomputable def programEquiv {x : ι → K} (hx : Function.Injective x) :
    (K → R) × (ι → R) ≃ (K → R) × (ι → R) where
  toFun p := (programAt x p.2 p.1, p.1 ∘ x)
  invFun p := (programAt x p.2 p.1, p.1 ∘ x)
  left_inv p := by
    simp only [programAt_comp hx, programAt_programAt hx]
  right_inv p := by
    simp only [programAt_comp hx, programAt_programAt hx]

/-- **A uniform table read at distinct points is uniform there.** -/
theorem close_restrict [Nonempty R] {x : ι → K} (hx : Function.Injective x) :
    Close 0 (fun g : K → R => g ∘ x) (id : (ι → R) → (ι → R)) := by
  intro D
  have h := pr_equiv (programEquiv hx) (fun p : (K → R) × (ι → R) => D p.2)
  have h1 : pr ((K → R) × (ι → R)) (fun p => D ((programEquiv hx p).2)) =
      pr (K → R) (fun g => D (g ∘ x)) :=
    pr_prod_fst (β := ι → R) (fun g : K → R => D (g ∘ x))
  have h2 : pr ((K → R) × (ι → R)) (fun p => D p.2) = pr (ι → R) D := pr_prod_snd D
  rw [h1, h2] at h
  simp [h]

/-- A run on `C × (K → R)` gains an unused answer coordinate. -/
lemma pr_add_answers [Nonempty ι] [Nonempty R] (P : C × (K → R) → Prop) :
    pr (C × ((K → R) × (ι → R))) (fun p => P (p.1, p.2.1)) = pr (C × (K → R)) P := by
  rw [pr_prod, pr_prod]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  exact pr_prod_fst (β := ι → R) (fun g => P (c, g))

/-- **Programming is perfect.** For coins `c` and distinct points `x c i`, a run that reads a
uniform table `g` and its answers `g ∘ x c` has the law of the run that reads independent uniform
answers `u` and the table programmed with them. -/
theorem pr_program_eq [Nonempty ι] [Nonempty R] {x : C → ι → K}
    (hx : ∀ c, Function.Injective (x c)) (A : C → (ι → R) → (K → R) → Prop) :
    pr (C × (K → R)) (fun p => A p.1 (p.2 ∘ x p.1) p.2) =
      pr (C × ((K → R) × (ι → R))) (fun p => A p.1 p.2.2 (programAt (x p.1) p.2.2 p.2.1)) := by
  rw [← pr_add_answers (ι := ι) (fun p : C × (K → R) => A p.1 (p.2 ∘ x p.1) p.2), pr_prod, pr_prod]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← pr_equiv (programEquiv (hx c))]
  simp only [programEquiv, Equiv.coe_fn_mk, programAt_comp (hx c)]

/-- **Identical until a programmed point is read.** If the run `A c u g` reads the table `g` only
on the keys `Q c u g` (`hQ`), then reading the real answers `g ∘ x c` and reading independent
answers `u` (with the unprogrammed table) are at most `Pr[∃ i, x c i ∈ Q c u g]` apart. -/
theorem abs_pr_hidden_le [Nonempty ι] [Nonempty R] {x : C → ι → K}
    (hx : ∀ c, Function.Injective (x c)) (A : C → (ι → R) → (K → R) → Prop)
    (Q : C → (ι → R) → (K → R) → Finset K)
    (hQ : ∀ c u g g', (∀ k ∈ Q c u g, g k = g' k) → (A c u g ↔ A c u g')) :
    |pr (C × (K → R)) (fun p => A p.1 (p.2 ∘ x p.1) p.2) -
        pr (C × ((K → R) × (ι → R))) (fun p => A p.1 p.2.2 p.2.1)| ≤
      pr (C × ((K → R) × (ι → R))) (fun p => ∃ i, x p.1 i ∈ Q p.1 p.2.2 p.2.1) := by
  rw [pr_program_eq hx]
  refine abs_pr_sub_le_of_agree _ _ _ fun p hp => ?_
  push Not at hp
  refine (hQ p.1 p.2.2 p.2.1 _ fun k hk => ?_).symm
  exact (programAt_apply_of_ne _ _ fun i hi => hp i (by rw [hi]; exact hk)).symm

/-- `abs_pr_hidden_le` for a run that does not depend on the coins except through the answers, at
one point `x c` (an injective encoding of the coins): `≤ q / |C|` for runs reading at most `q`
keys. -/
theorem abs_pr_hidden_one_le [Nonempty R] {x : C → K} (hx : Function.Injective x)
    (A : R → (K → R) → Prop) (Q : R → (K → R) → Finset K)
    (hQ : ∀ u g g', (∀ k ∈ Q u g, g k = g' k) → (A u g ↔ A u g')) {q : ℕ}
    (hq : ∀ u g, (Q u g).card ≤ q) :
    |pr (C × (K → R)) (fun p => A (p.2 (x p.1)) p.2) -
        pr (C × ((K → R) × R)) (fun p => A p.2.2 p.2.1)| ≤ q / Fintype.card C := by
  have h := abs_pr_hidden_le (ι := Unit) (R := R) (x := fun c _ => x c)
    (fun c _ _ _ => rfl) (fun _ u g => A (u ()) g) (fun _ u g => Q (u ()) g)
    (fun _ u g g' h => hQ (u ()) g g' h)
  -- Re-index the answers `Unit → R` as `R`.
  let e : (K → R) × (Unit → R) ≃ (K → R) × R := Equiv.prodCongr (Equiv.refl _) (Equiv.funUnique Unit R)
  have h2 : pr (C × ((K → R) × (Unit → R))) (fun p => A (p.2.2 ()) p.2.1) =
      pr (C × ((K → R) × R)) (fun p => A p.2.2 p.2.1) := by
    rw [pr_prod, pr_prod]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    exact pr_equiv e (fun p => A p.2 p.1)
  have h3 : pr (C × ((K → R) × (Unit → R))) (fun p => ∃ i : Unit, x p.1 ∈ Q (p.2.2 ()) p.2.1) ≤
      q / Fintype.card C := by
    have := pr_mem_indep_le (β := (K → R) × (Unit → R)) x hx (fun b => Q (b.2 ()) b.1)
      (fun b => hq _ _)
    refine le_trans (le_of_eq (pr_congr fun p => ?_)) this
    simp
  simp only [Function.comp_apply] at h
  rw [h2] at h
  exact h.trans h3

end Program

end VoleMole.Privacy
