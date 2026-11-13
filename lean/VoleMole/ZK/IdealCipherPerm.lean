import VoleMole.ZK.IdealCipher

/-!
# Puncturing a GGM tree with permutation rows (hop H4 with AES as random permutations)

`ZK/IdealCipher.lean` punctures the GGM tree with the cipher a table of uniform *functions* (the
PRF view). Here every row is a uniform **permutation**: the cipher is a table
`π : K → Equiv.Perm K`, the replacement rows of the secret nodes are independent uniform
permutations, and the distinguisher reads whole permutation rows at `q` keys (so forward and
inverse queries).

* **Guessing a fresh value of a permutation** (`pr_perm_fresh_le`, `pr_perm_reset_le`): if the
  candidates depend on a uniform permutation `σ` only through its values on a set `S` of inputs,
  then `σ x₀` for `x₀ ∉ S` is one of `q` candidates with probability `≤ q / (|K| − |S|)` (double
  counting with the neighbours `swap (σ x₀) b * σ`, `b ∉ σ(S)`).
* **One hop** (`hopP`): replacing node `n` costs `(N + q) / (|K| − s)`, where `s` bounds the inputs
  `rd` at which the rest of the experiment reads the parent's row (the siblings' inputs and what the
  output reads; `x n ∉ rd`): the node's value is the parent's permutation at a fresh input. The
  hybrid over the secret nodes is `punctureP`.
* **The switching term** (`close_evalPts`): independent uniform permutations read at distinct
  points `pts` are `Pr[collision]`-close to independent uniform values, the collision event being
  two points of the same row with equal values (samples without vs. with replacement); with the
  points of each row covered by groups (`hcov`), `≤ Σ_g C(|grp g|, 2) / |K|` (`pr_not_injOn_le`).
* `experP_empty`, `experP_close`: the real experiment, and a fully replaced experiment whose output
  is `ε`-close to `F` of a uniform `h` for every table.
-/

open Finset

namespace VoleMole.ZK.IC

open VoleMole.Privacy

/-! ## A fresh value of a uniform permutation -/

section Fresh

variable {K : Type} [Fintype K] [DecidableEq K]

/-- **A fresh value of a uniform permutation is one of `q` candidates with probability
`≤ q / (|K| − |S|)`**, when the candidates depend on the permutation only through its values on
`S ∌ x₀`. -/
theorem pr_perm_fresh_le (x0 : K) (S : Finset K) (hx0 : x0 ∉ S)
    (T : Equiv.Perm K → Finset K) (hT : ∀ σ σ', (∀ y ∈ S, σ y = σ' y) → T σ = T σ')
    {q : ℕ} (hq : ∀ σ, (T σ).card ≤ q) :
    pr (Equiv.Perm K) (fun σ => σ x0 ∈ T σ) ≤ q / (Fintype.card K - S.card : ℕ) := by
  classical
  set F := (univ : Finset (Equiv.Perm K)).filter (fun σ => σ x0 ∈ T σ) with hFdef
  have hSK : S.card < Fintype.card K :=
    card_lt_card ⟨subset_univ _, fun h => hx0 (h (mem_univ x0))⟩ |>.trans_le (card_univ).le
  set M := Fintype.card K - S.card with hM
  have hM0 : 0 < M := by omega
  let G : Finset (Σ _ : Equiv.Perm K, K) := F.sigma fun σ => univ \ S.image σ
  let H : Finset (Σ _ : Equiv.Perm K, K) := univ.sigma fun π => T π
  let φ : (Σ _ : Equiv.Perm K, K) → (Σ _ : Equiv.Perm K, K) := fun p =>
    ⟨Equiv.swap (p.1 x0) p.2 * p.1, p.1 x0⟩
  have hG : G.card = F.card * M := by
    rw [card_sigma, sum_congr rfl (g := fun _ => M) fun σ _ => by
      rw [card_sdiff_of_subset (subset_univ _), card_univ,
        card_image_of_injective _ σ.injective]]
    rw [sum_const, smul_eq_mul]
  have hH : H.card ≤ q * Fintype.card (Equiv.Perm K) := by
    rw [card_sigma]
    calc ∑ π, (T π).card ≤ ∑ _π : Equiv.Perm K, q := sum_le_sum fun π _ => hq π
      _ = q * Fintype.card (Equiv.Perm K) := by rw [sum_const, card_univ, smul_eq_mul, mul_comm]
  -- The neighbour agrees with `σ` on `S`.
  have hagree : ∀ σ : Equiv.Perm K, ∀ b ∉ S.image σ, ∀ y ∈ S,
      (Equiv.swap (σ x0) b * σ) y = σ y := by
    intro σ b hb y hy
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    refine Equiv.swap_apply_of_ne_of_ne (fun h => hx0 ?_) (fun h => hb (mem_image.2 ⟨y, hy, h⟩))
    rw [σ.injective h] at hy
    exact hy
  have hmaps : ∀ p ∈ G, φ p ∈ H := by
    intro p hp
    obtain ⟨hσ, hb⟩ := mem_sigma.1 hp
    have hb' : p.2 ∉ S.image p.1 := (mem_sdiff.1 hb).2
    refine mem_sigma.2 ⟨mem_univ _, ?_⟩
    show p.1 x0 ∈ T (Equiv.swap (p.1 x0) p.2 * p.1)
    rw [hT _ p.1 (hagree p.1 p.2 hb')]
    exact (mem_filter.1 hσ).2
  have hinj : Set.InjOn φ G := by
    intro p _ p' _ h
    obtain ⟨σ, b⟩ := p
    obtain ⟨σ', b'⟩ := p'
    simp only [φ, Sigma.mk.injEq, heq_eq_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hb : b = b' := by
      have e1 := congrArg (fun π : Equiv.Perm K => π x0) h1
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left, h2] at e1
      exact e1
    subst hb
    rw [h2] at h1
    have := mul_left_cancel h1
    subst this
    rfl
  have hnat : F.card * M ≤ q * Fintype.card (Equiv.Perm K) :=
    hG ▸ (card_le_card_of_injOn φ hmaps hinj).trans hH
  rw [pr_def]
  have hP : (0 : ℝ) < Fintype.card (Equiv.Perm K) := by exact_mod_cast Fintype.card_pos
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  rw [div_le_div_iff₀ hP hMr]
  have : ((#{σ | σ x0 ∈ T σ} : ℕ) : ℝ) = F.card := rfl
  rw [this]
  exact_mod_cast hnat

/-- **The same through a lens**: the coordinate `f a` is a uniform permutation, and the candidates
`T a` depend on it only through its values on `S ∌ x₀` (`set a σ` replaces the coordinate). -/
theorem pr_perm_reset_le {α : Type*} [Fintype α] (f : α → Equiv.Perm K)
    (set : α → Equiv.Perm K → α) (hf : ∀ a σ, f (set a σ) = σ)
    (hss : ∀ a σ σ', set (set a σ) σ' = set a σ') (hsf : ∀ a, set a (f a) = a)
    (x0 : K) (S : Finset K) (hx0 : x0 ∉ S) (T : α → Finset K)
    (hT : ∀ a σ σ', (∀ y ∈ S, σ y = σ' y) → T (set a σ) = T (set a σ'))
    {q : ℕ} (hq : ∀ a, (T a).card ≤ q) :
    pr α (fun a => f a x0 ∈ T a) ≤ q / (Fintype.card K - S.card : ℕ) := by
  classical
  have hnn : (0 : ℝ) ≤ q / (Fintype.card K - S.card : ℕ) := by positivity
  by_cases hα : Nonempty α
  swap
  · rw [not_nonempty_iff] at hα
    rw [pr_def]
    simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      zero_div]
    exact hnn
  obtain ⟨a0⟩ := hα
  let β := {a : α // set a 1 = a}
  have : Nonempty β := ⟨⟨set a0 1, hss _ _ _⟩⟩
  let e : α ≃ Equiv.Perm K × β :=
    { toFun := fun a => (f a, ⟨set a 1, hss _ _ _⟩)
      invFun := fun p => set p.2.1 p.1
      left_inv := fun a => by simp only [hss, hsf]
      right_inv := fun p => by
        obtain ⟨σ, b, hb⟩ := p
        simp only [hf, Prod.mk.injEq, true_and]
        exact Subtype.ext (by simp only [hss]; exact hb) }
  have h1 : pr α (fun a => f a x0 ∈ T a) =
      pr (β × Equiv.Perm K) (fun p => p.2 x0 ∈ T (set p.1.1 p.2)) := by
    rw [← pr_equiv ((Equiv.prodComm _ _).trans e.symm) (fun a => f a x0 ∈ T a)]
    refine pr_congr fun p => ?_
    show f (set p.1.1 p.2) x0 ∈ T (set p.1.1 p.2) ↔ _
    rw [hf]
  rw [h1, pr_prod]
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hβ]
  calc ∑ b : β, pr (Equiv.Perm K) (fun σ => σ x0 ∈ T (set b.1 σ))
      ≤ ∑ _b : β, (q : ℝ) / (Fintype.card K - S.card : ℕ) := sum_le_sum fun b _ =>
        pr_perm_fresh_le x0 S hx0 (fun σ => T (set b.1 σ)) (fun σ σ' h => hT b.1 σ σ' h)
          fun σ => hq _
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

end Fresh

/-! ## Samples without replacement against samples with replacement -/

section Switch

variable {K I : Type} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I] {N : ℕ}

/-- The permutation rows `R` at the points `pts`. -/
def evalPts (pts : I → Fin N × K) (R : Fin N → Equiv.Perm K) : I → K :=
  fun i => R (pts i).1 (pts i).2

/-- Values with no collision inside a row. -/
def InjPts (pts : I → Fin N × K) (a : I → K) : Prop :=
  ∀ i j, (pts i).1 = (pts j).1 → a i = a j → i = j

omit [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I] in
lemma injPts_evalPts {pts : I → Fin N × K} (hpts : Function.Injective pts)
    (R : Fin N → Equiv.Perm K) : InjPts pts (evalPts pts R) := by
  intro i j hn ha
  refine hpts (Prod.ext hn ?_)
  simp only [evalPts] at ha
  rw [hn] at ha
  exact (R (pts j).1).injective ha

omit [DecidableEq I] in
/-- **All collision-free values have equally many permutation rows**: a permutation per row moves
one set of values to the other (`Equiv.Perm.exists_extending_pair`). -/
lemma card_fiber_eq (pts : I → Fin N × K) {a a' : I → K} (ha : InjPts pts a)
    (ha' : InjPts pts a') :
    (univ.filter fun R => evalPts pts R = a).card = (univ.filter fun R => evalPts pts R = a').card := by
  have hτ : ∀ n : Fin N, ∃ τ : Equiv.Perm K, ∀ i : {i // (pts i).1 = n}, τ (a i.1) = a' i.1 := by
    intro n
    refine Equiv.Perm.exists_extending_pair (fun i : {i // (pts i).1 = n} => a i.1)
      (fun i => a' i.1) (fun i j h => Subtype.ext (ha _ _ (i.2.trans j.2.symm) h))
      (fun i j h => Subtype.ext (ha' _ _ (i.2.trans j.2.symm) h))
  choose τ hτ using hτ
  refine card_equiv (Equiv.mulLeft (τ : Fin N → Equiv.Perm K)) fun R => ?_
  simp only [mem_filter, mem_univ, true_and]
  have hev : ∀ i, evalPts pts ((τ : Fin N → Equiv.Perm K) * R) i = τ (pts i).1 (evalPts pts R i) :=
    fun i => rfl
  constructor
  · intro h
    funext i
    rw [Equiv.coe_mulLeft, hev, h]
    exact hτ _ ⟨i, rfl⟩
  · intro h
    funext i
    have e := congrFun h i
    rw [Equiv.coe_mulLeft, hev, ← hτ _ ⟨i, rfl⟩] at e
    exact (τ (pts i).1).injective e

/-- **Uniform permutation rows read at distinct points are `Pr[collision]`-close to uniform
values.** -/
theorem close_evalPts (pts : I → Fin N × K) (hpts : Function.Injective pts) :
    Close (pr (I → K) fun a => ¬ InjPts pts a) (evalPts pts) (id : (I → K) → I → K) := by
  classical
  intro D
  let a0 : I → K := fun i => (pts i).2
  have ha0 : InjPts pts a0 := fun i j hn h => hpts (Prod.ext hn h)
  set c := (univ.filter fun R => evalPts pts R = a0).card with hc
  have hfib : ∀ a : I → K, (univ.filter fun R => evalPts pts R = a).card =
      if InjPts pts a then c else 0 := by
    intro a
    split_ifs with h
    · exact card_fiber_eq pts h ha0
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro R _ e
      exact h (e ▸ injPts_evalPts hpts R)
  -- Counting through the values.
  have hcount : ∀ P : (I → K) → Prop, [DecidablePred P] →
      (univ.filter fun R => P (evalPts pts R)).card =
        c * (univ.filter fun a => P a ∧ InjPts pts a).card := by
    intro P _
    rw [card_eq_sum_card_fiberwise (f := evalPts pts) (t := univ.filter P)
      (fun R hR => by simpa using hR)]
    have hf : ∀ a ∈ univ.filter P, ((univ.filter fun R => P (evalPts pts R)).filter
        fun R => evalPts pts R = a).card = if InjPts pts a then c else 0 := by
      intro a ha
      rw [filter_filter, ← hfib a]
      congr 1
      exact filter_congr fun R _ => ⟨fun h => h.2, fun h => ⟨h ▸ (mem_filter.1 ha).2, h⟩⟩
    rw [sum_congr rfl hf, ← sum_filter, sum_const, smul_eq_mul, filter_filter, mul_comm]
  have hall : Fintype.card (Fin N → Equiv.Perm K) =
      c * (univ.filter fun a : I → K => InjPts pts a).card := by
    have h := hcount (fun _ => True)
    rw [filter_true_of_mem fun _ _ => trivial, card_univ] at h
    simpa only [true_and] using h
  set m := (univ.filter fun a : I → K => InjPts pts a).card with hm
  set M := Fintype.card (I → K) with hMdef
  have hm0 : 0 < m := card_pos.2 ⟨a0, mem_filter.2 ⟨mem_univ _, ha0⟩⟩
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, zero_mul] at hall
      exact absurd hall (Fintype.card_ne_zero)
    · exact h
  set x := (univ.filter fun a => D a ∧ InjPts pts a).card with hx
  set y := (univ.filter fun a => D a ∧ ¬ InjPts pts a).card with hy
  have hxm : x ≤ m := card_le_card fun a ha => mem_filter.2 ⟨mem_univ _, (mem_filter.1 ha).2.2⟩
  have hsplit : (univ.filter fun a : I → K => D a).card = x + y := by
    rw [hx, hy, ← card_union_of_disjoint (disjoint_filter.2 fun a _ h1 h2 => h2.2 h1.2)]
    congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_union]
    tauto
  have hnot : (univ.filter fun a : I → K => ¬ InjPts pts a).card = M - m := by
    rw [hm, hMdef, ← card_compl, compl_filter]
  have hmM : m ≤ M := (card_le_card (subset_univ _)).trans card_univ.le
  have hyM : y ≤ M - m := by
    rw [← hnot]
    exact card_le_card fun a ha => mem_filter.2 ⟨mem_univ _, (mem_filter.1 ha).2.2⟩
  -- The two probabilities.
  have e1 : pr (Fin N → Equiv.Perm K) (fun R => D (evalPts pts R)) = (x : ℝ) / m := by
    rw [pr_def, hcount D, ← hx, hall]
    push_cast
    rw [mul_div_mul_left _ _ (by exact_mod_cast hc0.ne')]
  have e2 : pr (I → K) (fun a => D (id a)) = ((x + y : ℕ) : ℝ) / M := by
    rw [pr_def]
    simp only [id]
    rw [hsplit]
  have e3 : pr (I → K) (fun a => ¬ InjPts pts a) = ((M - m : ℕ) : ℝ) / M := by
    rw [pr_def, hnot]
  rw [e1, e2, e3]
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  have hMr : (0 : ℝ) < M := by exact_mod_cast hm0.trans_le hmM
  have hxr : (x : ℝ) ≤ m := by exact_mod_cast hxm
  have hyr : (y : ℝ) ≤ M - m := by
    have := (Nat.cast_le (α := ℝ)).2 hyM
    rw [Nat.cast_sub hmM] at this
    exact this
  rw [Nat.cast_sub hmM, Nat.cast_add]
  rw [div_sub_div _ _ hmr.ne' hMr.ne', abs_div, abs_of_pos (mul_pos hmr hMr),
    div_le_div_iff₀ (mul_pos hmr hMr) hMr]
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  have hMm : (0 : ℝ) ≤ M - m := by linarith
  have hX : |(x : ℝ) * M - m * (x + y)| ≤ (M - m) * m := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg hx0 hMm, mul_le_mul_of_nonneg_left hyr hmr.le]
    · nlinarith [mul_le_mul_of_nonneg_right hxr hMm, mul_nonneg hmr.le hy0]
  calc |(x : ℝ) * M - m * (x + y)| * M ≤ (M - m) * m * M := mul_le_mul_of_nonneg_right hX hMr.le
    _ = _ := by ring

/-- Collision-free on a set of indices. -/
def InjOnF (a : I → K) (F : Finset I) : Prop := ∀ i ∈ F, ∀ j ∈ F, a i = a j → i = j

/-- **A uniform function has a collision on `F` with probability `≤ C(|F|, 2) / |K|`.** -/
theorem pr_not_injOn_le [Nonempty K] (F : Finset I) :
    pr (I → K) (fun a => ¬ InjOnF a F) ≤ (F.card.choose 2 : ℕ) / Fintype.card K := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    have : ∀ a : I → K, ¬ ¬ InjOnF a ∅ := fun a h => h fun i hi => absurd hi (notMem_empty _)
    rw [pr_def, filter_false_of_mem fun a _ => this a]
    simp
  | insert i F hi ih =>
    have hsub : ∀ a : I → K, ¬ InjOnF a (insert i F) → ¬ InjOnF a F ∨ a i ∈ F.image a := by
      intro a h
      by_contra hc
      push Not at hc
      obtain ⟨h1, h2⟩ := hc
      refine h fun j hj j' hj' e => ?_
      rcases mem_insert.1 hj with hj | hj <;> rcases mem_insert.1 hj' with hj' | hj'
      · rw [hj, hj']
      · exact absurd (mem_image.2 ⟨j', hj', by rw [← e, hj]⟩ : a i ∈ F.image a) h2
      · exact absurd (mem_image.2 ⟨j, hj, by rw [e, hj']⟩ : a i ∈ F.image a) h2
      · exact h1 j hj j' hj' e
    have hguess : pr (I → K) (fun a => a i ∈ F.image a) ≤ F.card / Fintype.card K := by
      refine (pr_mem_reset_le (fun a : I → K => a i) (fun a k => Function.update a i k)
        (fun a k => Function.update_self _ _ _) (fun a k k' => Function.update_idem _ _ _)
        (fun a => Function.update_eq_self _ _) (fun a => F.image a) (fun a k => ?_)
        (fun a => card_image_le)).trans le_rfl
      refine image_congr fun j hj => ?_
      exact Function.update_of_ne (fun e => hi (by rw [← e]; exact hj)) _ _
    calc pr (I → K) (fun a => ¬ InjOnF a (insert i F))
        ≤ pr (I → K) (fun a => ¬ InjOnF a F ∨ a i ∈ F.image a) := pr_mono hsub
      _ ≤ pr (I → K) (fun a => ¬ InjOnF a F) + pr (I → K) (fun a => a i ∈ F.image a) :=
        pr_or_le _ _
      _ ≤ (F.card.choose 2 : ℕ) / Fintype.card K + F.card / Fintype.card K := add_le_add ih hguess
      _ = ((insert i F).card.choose 2 : ℕ) / Fintype.card K := by
        rw [card_insert_of_notMem hi, Nat.choose_succ_succ', Nat.choose_one_right, ← add_div]
        push_cast
        ring

/-- **The switching term**: if every two points of the same row lie in a common group, a collision
inside a row has probability `≤ Σ_g C(|grp g|, 2) / |K|`. -/
theorem pr_not_injPts_le [Nonempty K] (pts : I → Fin N × K) {G : Type} [Fintype G]
    (grp : G → Finset I)
    (hcov : ∀ i j, i ≠ j → (pts i).1 = (pts j).1 → ∃ g, i ∈ grp g ∧ j ∈ grp g) :
    pr (I → K) (fun a => ¬ InjPts pts a) ≤
      (∑ g, (grp g).card.choose 2 : ℕ) / Fintype.card K := by
  have h1 : ∀ a : I → K, ¬ InjPts pts a → ∃ g, ¬ InjOnF a (grp g) := by
    intro a h
    unfold InjPts at h
    push Not at h
    obtain ⟨i, j, hn, ha, hij⟩ := h
    obtain ⟨g, hi, hj⟩ := hcov i j hij hn
    exact ⟨g, fun h' => hij (h' i hi j hj ha)⟩
  refine (pr_mono h1).trans ((pr_exists_le_sum _).trans ?_)
  push_cast
  rw [sum_div]
  exact sum_le_sum fun g _ => by exact_mod_cast pr_not_injOn_le (grp g)

end Switch

/-! ## Changing a replaced parent's row away from its other children's inputs -/

section TreeCongr

variable {K X : Type} {x : ℕ → X} {N : ℕ}

/-- With node `n` and its parent `p` replaced, changing `p`'s row away from the inputs `rd` of its
other children changes no other row and no other node's value. -/
lemma rowAt_congr_par {rep : Finset ℕ} {n : ℕ} (hnr : n ∈ rep) (hN : n < N)
    (hp : (n - 1) / 2 ∈ rep) (rd : Finset X)
    (hsib : ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ∈ rd)
    (E : K → X → K) (R R' : Fin N → X → K) (seed : K)
    (hR : ∀ j : Fin N, j.val ≠ (n - 1) / 2 → R j = R' j)
    (hRp : ∀ (hpN : (n - 1) / 2 < N), ∀ y ∈ rd,
      R ⟨(n - 1) / 2, hpN⟩ y = R' ⟨(n - 1) / 2, hpN⟩ y) :
    ∀ m, (m ≠ (n - 1) / 2 → rowAt x N rep E R seed m = rowAt x N rep E R' seed m) ∧
      (m ≠ n → keyAt x N rep E R seed m = keyAt x N rep E R' seed m) := by
  have hpN : (n - 1) / 2 < N := by omega
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hkey : m ≠ n → keyAt x N rep E R seed m = keyAt x N rep E R' seed m := by
      intro hmn
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rfl
      rw [keyAt_pos (by omega), keyAt_pos (by omega)]
      by_cases hq : (m - 1) / 2 = (n - 1) / 2
      · rw [hq, rowAt_of_mem hp hpN, rowAt_of_mem hp hpN]
        exact hRp hpN _ (hsib m (by omega) hmn hq)
      · rw [(ih _ (by omega)).1 hq]
    refine ⟨fun hmp => ?_, hkey⟩
    rw [rowAt_eq, rowAt_eq]
    split_ifs with h
    · exact hR _ hmp
    · have hmn : m ≠ n := fun e => h ⟨e ▸ hnr, e ▸ hN⟩
      rw [hkey hmn]

end TreeCongr

/-! ## The hop with permutation rows -/

section HopPm

variable {K : Type} [Fintype K] [DecidableEq K] [Nonempty K] {x : ℕ → K} {N : ℕ} {O : Type}

/-- The rows of a family of permutations. -/
def cf {ι : Type*} (R : ι → Equiv.Perm K) : ι → K → K := fun i => ⇑(R i)

omit [Fintype K] [DecidableEq K] [Nonempty K] in
lemma cf_programAt {ι : Type*} (v : ι → K) (u : ι → Equiv.Perm K) (π : K → Equiv.Perm K) :
    cf (programAt v u π) = programAt v (cf u) (cf π) :=
  funext fun k => Function.apply_extend (g := u) (fun σ : Equiv.Perm K => (⇑σ : K → K)) v π k

omit [Fintype K] [DecidableEq K] [Nonempty K] in
lemma cf_update {ι : Type*} [DecidableEq ι] (R : ι → Equiv.Perm K) (i : ι) (σ : Equiv.Perm K) :
    cf (Function.update R i σ) = Function.update (cf R) i ⇑σ := by
  funext j
  by_cases h : j = i
  · subst h; simp [cf]
  · simp [cf, Function.update_of_ne h]

/-- The coins: the root seed and the replacement permutations. -/
abbrev PCoins (K : Type) (N : ℕ) := K × (Fin N → Equiv.Perm K)

/-- **The experiment with permutation rows** and the replaced nodes `rep`: the table is a uniform
permutation per key, `A` sees `Φ` of the rows and reads the table (whole permutations). -/
noncomputable def experPm (x : ℕ → K) (N : ℕ) (rep : Finset ℕ) (Φ : (ℕ → K → K) → O)
    (A : O → (K → Equiv.Perm K) → Prop) : ℝ :=
  pr (PCoins K N × (K → Equiv.Perm K))
    (fun p => A (Φ (rowAt x N rep (cf p.2) (cf p.1.2) p.1.1)) p.2)

/-- The coins with node `n`'s permutation taken from the answer `u`, and the old one moved to the
answer (an involution). -/
def swapRowPm {n : ℕ} (hN : n < N) :
    PCoins K N × ((K → Equiv.Perm K) × (Unit → Equiv.Perm K)) ≃
      PCoins K N × ((K → Equiv.Perm K) × (Unit → Equiv.Perm K)) where
  toFun a := ((a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())), (a.2.1, fun _ => a.1.2 ⟨n, hN⟩))
  invFun a := ((a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())), (a.2.1, fun _ => a.1.2 ⟨n, hN⟩))
  left_inv a := by
    obtain ⟨⟨s, R⟩, g, u⟩ := a
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
  right_inv a := by
    obtain ⟨⟨s, R⟩, g, u⟩ := a
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]

/-- The candidates for the secret value: the values of the non-replaced nodes below `N` and the
keys `A` reads. -/
noncomputable def candsPm (x : ℕ → K) (N : ℕ) (ins : Finset ℕ) (Φ : (ℕ → K → K) → O)
    (Q : O → (K → Equiv.Perm K) → Finset K) (p : PCoins K N × (K → Equiv.Perm K)) : Finset K :=
  ((range N).filter (· ∉ ins)).image (fun m => keyAt x N ins (cf p.2) (cf p.1.2) p.1.1 m) ∪
    Q (Φ (rowAt x N ins (cf p.2) (cf p.1.2) p.1.1)) p.2

omit [Fintype K] [Nonempty K] in
lemma candsPm_card (ins : Finset ℕ) (Φ : (ℕ → K → K) → O) (Q : O → (K → Equiv.Perm K) → Finset K)
    {q : ℕ} (hq : ∀ o G, (Q o G).card ≤ q) (p : PCoins K N × (K → Equiv.Perm K)) :
    (candsPm x N ins Φ Q p).card ≤ N + q := by
  unfold candsPm
  refine (card_union_le _ _).trans (Nat.add_le_add ?_ (hq _ _))
  exact card_image_le.trans ((card_filter_le _ _).trans (card_range N).le)

/-- **The secret value is guessed with probability `≤ (N + q) / (|K| − s)`**: the root seed is
uniform, and a non-root node's value is its parent's permutation at an input outside `rd`, which
is all the rest reads of that permutation. -/
lemma pr_secretPm_mem_cands {rep : Finset ℕ} {n : ℕ} (hN : n < N)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep) (rd : Finset K) {s : ℕ} (hrd : rd.card ≤ s)
    (hs : s < Fintype.card K) (hxn : n ≠ 0 → x n ∉ rd)
    (hsib : n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ∈ rd)
    (Φ : (ℕ → K → K) → O)
    (hΦ : n ≠ 0 → ∀ ρ ρ' : ℕ → K → K, (∀ m, m ≠ (n - 1) / 2 → ρ m = ρ' m) →
      (∀ y ∈ rd, ρ ((n - 1) / 2) y = ρ' ((n - 1) / 2) y) → Φ ρ = Φ ρ')
    (Q : O → (K → Equiv.Perm K) → Finset K) {q : ℕ} (hq : ∀ o G, (Q o G).card ≤ q) :
    pr (PCoins K N × (K → Equiv.Perm K)) (fun p => secretVal (x := x) n hN (p.1.1, cf p.1.2) ∈
      candsPm x N (insert n rep) Φ Q p) ≤ (N + q : ℕ) / (Fintype.card K - s : ℕ) := by
  have hin : n ∈ insert n rep := Finset.mem_insert_self _ _
  have hden : (0 : ℝ) < (Fintype.card K - s : ℕ) := by
    exact_mod_cast (by omega : 0 < Fintype.card K - s)
  by_cases h0 : n = 0
  · subst h0
    have hT : ∀ (p : PCoins K N × (K → Equiv.Perm K)) (k : K),
        candsPm x N (insert 0 rep) Φ Q ((k, p.1.2), p.2) = candsPm x N (insert 0 rep) Φ Q p := by
      intro p k
      have hrow := fun m => (rowAt_seed_indep (x := x) hin hN (cf p.2) (cf p.1.2) k p.1.1 m)
      unfold candsPm
      congr 1
      · refine Finset.image_congr fun m hm => ?_
        have hm' : m ≠ 0 := fun e => (Finset.mem_filter.1 hm).2 (e ▸ hin)
        exact (hrow m).2 hm'
      · simp only
        rw [show rowAt x N (insert 0 rep) (cf p.2) (cf p.1.2) k =
          rowAt x N (insert 0 rep) (cf p.2) (cf p.1.2) p.1.1 from funext fun m => (hrow m).1]
    have h := pr_mem_reset_le (α := PCoins K N × (K → Equiv.Perm K)) (fun p => p.1.1)
      (fun p k => ((k, p.1.2), p.2)) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl)
      (candsPm x N (insert 0 rep) Φ Q) hT (candsPm_card _ Φ Q hq)
    refine (le_of_eq (pr_congr fun p => ?_)).trans (h.trans ?_)
    · simp only [secretVal, ↓reduceIte]
    · exact div_le_div_of_nonneg_left (by positivity) hden (by exact_mod_cast Nat.sub_le _ _)
  · have hp : (n - 1) / 2 ∈ insert n rep := Finset.mem_insert_of_mem (hpar h0)
    have hpN : (n - 1) / 2 < N := by omega
    let pf : Fin N := ⟨(n - 1) / 2, hpN⟩
    let st : PCoins K N × (K → Equiv.Perm K) → Equiv.Perm K → PCoins K N × (K → Equiv.Perm K) :=
      fun p σ => ((p.1.1, Function.update p.1.2 pf σ), p.2)
    have hT : ∀ p σ σ', (∀ y ∈ rd, σ y = σ' y) →
        candsPm x N (insert n rep) Φ Q (st p σ) = candsPm x N (insert n rep) Φ Q (st p σ') := by
      intro p σ σ' hσ
      have hind := rowAt_congr_par (x := x) hin hN hp rd (hsib h0) (cf p.2)
        (cf (Function.update p.1.2 pf σ)) (cf (Function.update p.1.2 pf σ')) p.1.1
        (fun j hj => by
          have : j ≠ pf := fun e => hj (by rw [e])
          simp only [cf, Function.update_of_ne this])
        (fun _ y hy => by simp only [cf, pf, Function.update_self]; exact hσ y hy)
      unfold candsPm
      congr 1
      · refine Finset.image_congr fun m hm => ?_
        have hm' : m ≠ n := fun e => (Finset.mem_filter.1 hm).2 (e ▸ hin)
        exact (hind m).2 hm'
      · simp only [st]
        rw [hΦ h0 _ _ (fun m hm => (hind m).1 hm) (fun y hy => by
          rw [rowAt_of_mem hp hpN, rowAt_of_mem hp hpN]
          simp only [cf, pf, Function.update_self]; exact hσ y hy)]
    have h := pr_perm_reset_le (α := PCoins K N × (K → Equiv.Perm K)) (fun p => p.1.2 pf) st
      (fun p σ => by simp [st]) (fun p σ σ' => by simp [st]) (fun p => by simp [st])
      (x n) rd (hxn h0) (candsPm x N (insert n rep) Φ Q) hT (candsPm_card _ Φ Q hq)
    refine (le_of_eq (pr_congr fun p => ?_)).trans (h.trans ?_)
    · simp only [secretVal, h0, ↓reduceIte]
      rfl
    · exact div_le_div_of_nonneg_left (by positivity) hden
        (by exact_mod_cast Nat.sub_le_sub_left hrd _)

/-- **One hop with permutation rows**: replacing node `n` (its parent replaced, or the root) by an
independent uniform permutation costs `(N + q) / (|K| − s)`, where the rest of the experiment reads
the parent's permutation only at the inputs `rd` (at most `s`, not `x n`; the other children's
inputs among them). -/
theorem hopPm (rep : Finset ℕ) (n : ℕ) (hN : n < N) (hnr : n ∉ rep)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep) (rd : Finset K) {s : ℕ} (hrd : rd.card ≤ s)
    (hs : s < Fintype.card K) (hxn : n ≠ 0 → x n ∉ rd)
    (hsib : n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ∈ rd)
    (Φ : (ℕ → K → K) → O)
    (hΦ : n ≠ 0 → ∀ ρ ρ' : ℕ → K → K, (∀ m, m ≠ (n - 1) / 2 → ρ m = ρ' m) →
      (∀ y ∈ rd, ρ ((n - 1) / 2) y = ρ' ((n - 1) / 2) y) → Φ ρ = Φ ρ')
    (hΦN : ∀ ρ ρ', (∀ m < N, ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → (K → Equiv.Perm K) → Prop) (Q : O → (K → Equiv.Perm K) → Finset K)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) :
    |experPm x N rep Φ A - experPm x N (insert n rep) Φ A| ≤
      (N + q : ℕ) / (Fintype.card K - s : ℕ) := by
  classical
  let v : PCoins K N → K := fun c => secretVal (x := x) n hN (c.1, cf c.2)
  let ins := insert n rep
  -- Programming the table at the secret value is perfect.
  have h1 : experPm x N rep Φ A =
      pr (PCoins K N × ((K → Equiv.Perm K) × (Unit → Equiv.Perm K))) (fun p =>
        A (Φ (rowAt x N rep (cf (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1)) (cf p.1.2) p.1.1))
          (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1)) :=
    pr_program_eq (ι := Unit) (x := fun c _ => v c) (fun _ _ _ _ => rfl)
      (fun c _ g => A (Φ (rowAt x N rep (cf g) (cf c.2) c.1)) g)
  -- The experiment with `n` replaced by the answer.
  let B : PCoins K N × ((K → Equiv.Perm K) × (Unit → Equiv.Perm K)) → Prop := fun p =>
    A (Φ (rowAt x N ins (cf p.2.1) (cf (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ()))) p.1.1)) p.2.1
  have h2 : pr _ B = experPm x N ins Φ A := by
    have e := pr_equiv (swapRowPm (K := K) hN)
      (fun p => A (Φ (rowAt x N ins (cf p.2.1) (cf p.1.2) p.1.1)) p.2.1)
    rw [pr_add_answers (fun p : PCoins K N × (K → Equiv.Perm K) =>
      A (Φ (rowAt x N ins (cf p.2) (cf p.1.2) p.1.1)) p.2)] at e
    exact e
  -- The bad event: the secret value is a candidate.
  let bad : PCoins K N × ((K → Equiv.Perm K) × (Unit → Equiv.Perm K)) → Prop := fun p =>
    v p.1 ∈ candsPm x N ins Φ Q ((p.1.1, Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())), p.2.1)
  have h3 : pr _ bad ≤ (N + q : ℕ) / (Fintype.card K - s : ℕ) := by
    have e := pr_equiv (swapRowPm (K := K) hN)
      (fun p => v p.1 ∈ candsPm x N ins Φ Q (p.1, p.2.1))
    rw [pr_add_answers (fun p : PCoins K N × (K → Equiv.Perm K) =>
      v p.1 ∈ candsPm x N ins Φ Q p)] at e
    have e2 : pr _ bad = pr (PCoins K N × ((K → Equiv.Perm K) × (Unit → Equiv.Perm K)))
        (fun a => (fun p : PCoins K N × ((K → Equiv.Perm K) × (Unit → Equiv.Perm K)) =>
          v p.1 ∈ candsPm x N ins Φ Q (p.1, p.2.1)) (swapRowPm hN a)) :=
      pr_congr fun a => by
        show v a.1 ∈ _ ↔ v (a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())) ∈ _
        rw [show v (a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())) = v a.1 from by
          show secretVal (x := x) n hN (a.1.1, cf (Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ()))) =
            secretVal (x := x) n hN (a.1.1, cf a.1.2)
          rw [cf_update]
          exact secretVal_update hN (a.1.1, cf a.1.2) _]
        rfl
    rw [e2, e]
    exact pr_secretPm_mem_cands hN hpar rd hrd hs hxn hsib Φ hΦ Q hq
  have h4 : ∀ p, ¬ bad p → ((A (Φ (rowAt x N rep (cf (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1))
      (cf p.1.2) p.1.1)) (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1)) ↔ B p) := by
    intro p hp
    have hgood : ∀ m < N, m ∉ ins → keyAt x N ins (cf p.2.1)
        (Function.update (cf p.1.2) ⟨n, hN⟩ (cf p.2.2 ())) p.1.1 m ≠
          secretVal (x := x) n hN (p.1.1, cf p.1.2) := fun m hm hmi e => hp (by
      show v p.1 ∈ candsPm x N ins Φ Q _
      unfold candsPm
      refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨m, Finset.mem_filter.2
        ⟨Finset.mem_range.2 hm, hmi⟩, ?_⟩)
      show keyAt x N ins (cf p.2.1) (cf (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ()))) p.1.1 m = v p.1
      rw [cf_update]
      exact e)
    have hrows := rowAt_program (x := x) hN hnr hpar (cf p.2.1) (p.1.1, cf p.1.2) (cf p.2.2) hgood
    rw [cf_programAt, hΦN _ _ fun m hm => (hrows m hm).1]
    have hnq : v p.1 ∉ Q (Φ (rowAt x N ins (cf p.2.1)
        (cf (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ()))) p.1.1)) p.2.1 :=
      fun h => hp (Finset.mem_union_right _ h)
    show A (Φ (rowAt x N ins (cf p.2.1) (Function.update (cf p.1.2) ⟨n, hN⟩ ⇑(p.2.2 ())) p.1.1))
      (programAt (fun _ : Unit => v p.1) p.2.2 p.2.1) ↔ B p
    rw [← cf_update]
    exact (hQ _ _ _ fun k hk =>
      (programAt_apply_of_ne _ _ fun _ e => hnq (by rw [e]; exact hk)).symm).symm
  rw [h1, ← h2]
  exact (abs_pr_sub_le_of_agree _ _ bad h4).trans h3

/-- **The hybrid over the secret nodes with permutation rows**: for an upward-closed set `sec`,
replacing the permutations of all secret nodes below `N` by independent uniform permutations costs
`|sec| · (N + q) / (|K| − s)`. -/
theorem puncturePm (sec : ℕ → Prop) [DecidablePred sec]
    (hup : ∀ n < N, sec n → n ≠ 0 → sec ((n - 1) / 2))
    (rd : ℕ → Finset K) {s : ℕ} (hrd : ∀ n, (rd n).card ≤ s) (hs : s < Fintype.card K)
    (hxn : ∀ n < N, sec n → n ≠ 0 → x n ∉ rd n)
    (hsib : ∀ n < N, sec n → n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 →
      x m ∈ rd n)
    (Φ : (ℕ → K → K) → O)
    (hΦ : ∀ n < N, sec n → n ≠ 0 → ∀ ρ ρ' : ℕ → K → K, (∀ m, m ≠ (n - 1) / 2 → ρ m = ρ' m) →
      (∀ y ∈ rd n, ρ ((n - 1) / 2) y = ρ' ((n - 1) / 2) y) → Φ ρ = Φ ρ')
    (hΦN : ∀ ρ ρ', (∀ m < N, ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → (K → Equiv.Perm K) → Prop) (Q : O → (K → Equiv.Perm K) → Finset K)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) :
    |experPm x N ∅ Φ A - experPm x N ((range N).filter sec) Φ A| ≤
      ((range N).filter sec).card * ((N + q : ℕ) / (Fintype.card K - s : ℕ)) := by
  have key : ∀ j ≤ N, |experPm x N ∅ Φ A - experPm x N ((range j).filter sec) Φ A| ≤
      ((range j).filter sec).card * ((N + q : ℕ) / (Fintype.card K - s : ℕ)) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with hsj
      · have hnot : j ∉ (range j).filter sec := by simp
        have h := hopPm ((range j).filter sec) j (by omega) hnot (fun h0 => Finset.mem_filter.2
            ⟨Finset.mem_range.2 (by omega), hup j (by omega) hsj h0⟩) (rd j) (hrd j) hs
          (hxn j (by omega) hsj) (hsib j (by omega) hsj) Φ (hΦ j (by omega) hsj) hΦN A Q hQ hq
        rw [Finset.card_insert_of_notMem hnot, Nat.cast_succ, add_mul, one_mul]
        have := abs_sub_le (experPm x N ∅ Φ A) (experPm x N ((range j).filter sec) Φ A)
          (experPm x N (insert j ((range j).filter sec)) Φ A)
        linarith
      · exact ih
  exact key N le_rfl

/-- `A`'s success on `G` of a uniform root seed and a uniform permutation table. -/
noncomputable def realPrPm (G : K → (K → Equiv.Perm K) → O) (A : O → (K → Equiv.Perm K) → Prop) :
    ℝ :=
  pr (K × (K → Equiv.Perm K)) (fun p => A (G p.1 p.2) p.2)

/-- `A`'s success on `F` of a uniform `h` and an independent uniform permutation table. -/
noncomputable def idealPrPm {H : Type} [Fintype H] (F : H → O) (A : O → (K → Equiv.Perm K) → Prop) :
    ℝ :=
  pr (H × (K → Equiv.Perm K)) (fun h => A (F h.1) h.2)

omit [Nonempty K] in
/-- **The real experiment** (nothing replaced) does not read the replacement permutations. -/
theorem experPm_empty (Φ : (ℕ → K → K) → O) (A : O → (K → Equiv.Perm K) → Prop) :
    experPm x N ∅ Φ A = realPrPm (fun s π => Φ (rowAt x N ∅ (cf π) (fun _ _ => s) s)) A := by
  let e : PCoins K N × (K → Equiv.Perm K) ≃ (K × (K → Equiv.Perm K)) × (Fin N → Equiv.Perm K) :=
    { toFun := fun c => ((c.1.1, c.2), c.1.2)
      invFun := fun c => ((c.1.1, c.2), c.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := pr_equiv e (fun c => A (Φ (rowAt x N ∅ (cf c.1.2) (fun _ _ => c.1.1) c.1.1)) c.1.2)
  rw [pr_prod_fst (fun p : K × (K → Equiv.Perm K) =>
    A (Φ (rowAt x N ∅ (cf p.2) (fun _ _ => p.1) p.1)) p.2)] at h
  rw [realPrPm, ← h]
  refine pr_congr fun c => ?_
  show A (Φ (rowAt x N ∅ (cf c.2) (cf c.1.2) c.1.1)) c.2 ↔ _
  rw [rowAt_empty (cf c.2) (cf c.1.2) (fun _ _ => c.1.1) c.1.1]
  exact Iff.rfl

omit [Nonempty K] in
/-- **A fully replaced experiment whose output is `ε`-close to `F` of a uniform `h`, for every
table, is `ε`-close to the ideal experiment.** -/
theorem experPm_close {H : Type} [Fintype H] (rep : Finset ℕ) (Φ : (ℕ → K → K) → O) (F : H → O)
    {ε : ℝ} (hE : ∀ π : K → Equiv.Perm K,
      Close ε (fun c : PCoins K N => Φ (rowAt x N rep (cf π) (cf c.2) c.1)) F)
    (A : O → (K → Equiv.Perm K) → Prop) :
    |experPm x N rep Φ A - idealPrPm F A| ≤ ε :=
  abs_pr_prod_sub_le' (fun p : PCoins K N × (K → Equiv.Perm K) =>
      A (Φ (rowAt x N rep (cf p.2) (cf p.1.2) p.1.1)) p.2)
    (fun h : H × (K → Equiv.Perm K) => A (F h.1) h.2) fun π => hE π fun o => A o π

end HopPm

end VoleMole.ZK.IC
