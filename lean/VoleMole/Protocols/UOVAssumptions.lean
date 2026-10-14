import Mathlib

/-!
# UOV assumptions: combinatorial cores (`lean/docs/security/uov-assumptions.md`)

Deterministic and counting facts used by `lean/docs/security/uov-assumptions.md`.

* §1 `card_good_fiber`, `good_coords_bijective`: the vole-mole preimage sampler `derive_preimage`
  picks a vinegar `v` uniformly from the good set `G` (the vinegars whose oil system `L_v` is
  invertible) and solves for the oil part. For every target `y` there are exactly `|G|` good
  preimages, and `(v, y) ↦ (v, L_v⁻¹(y − …))` is a bijection `G × Y → G × X`. So for a uniform
  target the output is uniform on the good preimages, and for a fixed target it is uniform on that
  target's good preimages (note §2).
* §2 `tv_unif_good`, `tv_unif_good_pow`, `tv_ge_mass_off`: total variation between the uniform
  distribution on a finite set and the uniform distribution on a subset `G` of density `1 − δ` is
  `δ`, and for `q` independent samples it is `1 − (1 − δ)^q`. Every distribution is at total
  variation at least its mass outside `G` from the uniform distribution on `G` (note §3, the
  "1/255" obstacle).
* §3 `singular_prob_bounds`, `singular_prob_bounds_256`: a uniformly random `n × n` matrix over a
  field with `q` elements is singular with probability in `[1/q, 1/(q−1)]`. For `q = 256` this is
  `[2⁻⁸, 1/255]` (the heuristic value of `δ` for uov-Ip).
* §4 `group_gap`: with FAEST-EM-128f tree widths (one 8-bit tree, sixteen 7-bit trees), the
  widths of two complementary prefix groups differ by at least 6. So an adversary that can complete
  with either of two groups uses the narrower one with relative probability at most `2⁻⁶` (note
  §7.4), and `guess_loss` is the `τ^{q+1}` guessing arithmetic.
* §5 `one_more_count`: the pigeonhole step of the one-more reductions.

No `sorry`, no `axiom`.
-/

open Finset

namespace VoleMole.UOVAssumptions

/-! ## 1. Good preimages -/

section Fiber

variable {V X Y : Type*}

/-- For every target `y`, the good preimages `{(v, x) : v ∈ G, f v x = y}` number exactly `|G|`,
when `f v` is a bijection for every good `v`. (`f v x` is the target of the preimage with vinegar
`v` and oil coordinates `x`.) -/
theorem card_good_fiber [Fintype X] [DecidableEq Y] (G : Finset V) (f : V → X → Y)
    (hf : ∀ v ∈ G, Function.Bijective (f v)) (y : Y) :
    ((G ×ˢ (univ : Finset X)).filter (fun p => f p.1 p.2 = y)).card = G.card := by
  classical
  rw [card_filter, sum_product]
  rw [card_eq_sum_ones G]
  refine sum_congr rfl (fun v hv => ?_)
  rw [← card_filter]
  obtain ⟨x₀, hx₀, huniq⟩ := (hf v hv).existsUnique y
  rw [card_eq_one]
  refine ⟨x₀, ?_⟩
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨fun h => huniq x h, fun h => h ▸ hx₀⟩

/-- `(v, x) ↦ (v, f v x)` is a bijection from `G × X` to `G × Y`. Hence a uniform target together
with a uniform good vinegar yields uniform `(v, x)` on `G × X`, i.e. a uniform good preimage. -/
theorem good_coords_bijective (G : Finset V) (f : V → X → Y)
    (hf : ∀ v ∈ G, Function.Bijective (f v)) :
    Function.Bijective (fun p : G × X => ((p.1, f p.1 p.2) : G × Y)) := by
  constructor
  · rintro ⟨v, x⟩ ⟨v', x'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    exact Prod.ext rfl ((hf v v.2).1 h2)
  · rintro ⟨v, y⟩
    obtain ⟨x, hx⟩ := (hf v v.2).2 y
    exact ⟨(v, x), by simp [hx]⟩

end Fiber

/-! ## 2. Total variation between uniform and uniform-on-good -/

section TV

variable {α : Type*} [Fintype α]

/-- One-sided total variation `Σ_a max(μ a − ν a, 0)`. For two probability distributions it equals
the total variation distance (`tv_symm`). -/
noncomputable def tv (μ ν : α → ℝ) : ℝ := ∑ a, max (μ a - ν a) 0

/-- For two functions with the same total mass, the two one-sided sums agree. -/
theorem tv_symm (μ ν : α → ℝ) (h : ∑ a, μ a = ∑ a, ν a) : tv μ ν = tv ν μ := by
  unfold tv
  have key : ∀ a, max (μ a - ν a) 0 - max (ν a - μ a) 0 = μ a - ν a := by
    intro a
    rcases le_total (μ a) (ν a) with hle | hle
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have : ∑ a, (max (μ a - ν a) 0 - max (ν a - μ a) 0) = 0 := by
    simp_rw [key]
    rw [sum_sub_distrib, h, sub_self]
  rw [sum_sub_distrib] at this
  linarith

/-- The uniform distribution on `α`. -/
noncomputable def unif (α : Type*) [Fintype α] : α → ℝ := fun _ => 1 / (Fintype.card α : ℝ)

/-- The uniform distribution on `G ⊆ α`. -/
noncomputable def unifOn [DecidableEq α] (G : Finset α) : α → ℝ := fun a => if a ∈ G then 1 / (G.card : ℝ) else 0

/-- `TV(U(G), U(α)) = 1 − |G|/|α|`, i.e. `δ` for a subset of density `1 − δ`. -/
theorem tv_unif_good [DecidableEq α] (G : Finset α) (hG : G.Nonempty) :
    tv (unifOn G) (unif α) = 1 - (G.card : ℝ) / Fintype.card α := by
  unfold tv unifOn unif
  have hGpos : (0 : ℝ) < G.card := by exact_mod_cast hG.card_pos
  have hcard : (G.card : ℝ) ≤ Fintype.card α := by exact_mod_cast card_le_univ G
  have hαpos : (0 : ℝ) < Fintype.card α := lt_of_lt_of_le hGpos hcard
  have hterm : ∀ a, max ((if a ∈ G then 1 / (G.card : ℝ) else 0) - 1 / (Fintype.card α : ℝ)) 0
      = if a ∈ G then 1 / (G.card : ℝ) - 1 / (Fintype.card α : ℝ) else 0 := by
    intro a
    split_ifs with ha
    · apply max_eq_left
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hGpos hcard
    · apply max_eq_right
      have : 0 ≤ 1 / (Fintype.card α : ℝ) := by positivity
      linarith
  simp_rw [hterm]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul]
  field_simp

/-- `q` independent samples: `TV(U(G)^q, U(β)^q) = 1 − (|G|/|β|)^q`. -/
theorem tv_unif_good_pow {β : Type*} [Fintype β] [DecidableEq β] (G : Finset β)
    (hG : G.Nonempty) (q : ℕ) :
    tv (unifOn (Fintype.piFinset (fun _ : Fin q => G))) (unif (Fin q → β))
      = 1 - ((G.card : ℝ) / Fintype.card β) ^ q := by
  have hne : (Fintype.piFinset (fun _ : Fin q => G)).Nonempty :=
    Fintype.piFinset_nonempty.mpr (fun _ => hG)
  rw [tv_unif_good _ hne, Fintype.card_piFinset, Fintype.card_fun, Fintype.card_fin, prod_const,
    card_univ, Fintype.card_fin, div_pow]
  push_cast
  ring

/-- Any distribution `μ` is at one-sided distance at least its mass outside `G` from `U(G)`. -/
theorem tv_ge_mass_off [DecidableEq α] (μ : α → ℝ) (G : Finset α) :
    ∑ a ∈ univ.filter (fun a => a ∉ G), μ a ≤ tv μ (unifOn G) := by
  unfold tv unifOn
  rw [sum_filter]
  refine sum_le_sum (fun a _ => ?_)
  split_ifs with ha
  · simp
  · simp only [sub_zero]
    exact le_max_left _ _

end TV

/-! ## 3. Singular matrices over a finite field -/

section Singular

/-- `∏ (1 − a_i) ≥ 1 − Σ a_i` for `a_i ∈ [0, 1]`. -/
theorem one_sub_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have hj0 := h0 j (mem_insert_self j s)
    have hj1 := h1 j (mem_insert_self j s)
    have hS : 0 ≤ ∑ i ∈ s, a i := sum_nonneg (fun i hi => h0 i (mem_insert_of_mem hi))
    have hprod : (1 - a j) * (1 - ∑ i ∈ s, a i) ≤ (1 - a j) * ∏ i ∈ s, (1 - a i) :=
      mul_le_mul_of_nonneg_left ih' (by linarith)
    nlinarith

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]

/-- The probability that a uniform `n × n` matrix over `𝔽` is invertible, as a product. -/
theorem prob_invertible_eq (n : ℕ) :
    (Nat.card (GL (Fin n) 𝔽) : ℝ) / (Fintype.card 𝔽 : ℝ) ^ (n * n)
      = ∏ i : Fin n, (1 - (Fintype.card 𝔽 : ℝ) ^ (i : ℕ) / (Fintype.card 𝔽 : ℝ) ^ n) := by
  set q := Fintype.card 𝔽 with hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos
  rw [Matrix.card_GL_field]
  push_cast [Nat.cast_prod]
  have hle : ∀ i : Fin n, q ^ (i : ℕ) ≤ q ^ n := fun i =>
    Nat.pow_le_pow_right Fintype.card_pos (le_of_lt i.2)
  rw [show ((q : ℝ) ^ (n * n)) = ∏ _i : Fin n, (q : ℝ) ^ n by
    rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul]]
  rw [← prod_div_distrib]
  refine prod_congr rfl (fun i _ => ?_)
  rw [Nat.cast_sub (hle i)]
  push_cast
  field_simp

/-- A uniform `n × n` matrix (`n ≥ 1`) over a field with `q ≥ 2` elements is singular with
probability in `[1/q, 1/(q−1)]`. -/
theorem singular_prob_bounds (n : ℕ) (hn : 1 ≤ n) (hq : 2 ≤ Fintype.card 𝔽) :
    1 / (Fintype.card 𝔽 : ℝ)
        ≤ 1 - (Nat.card (GL (Fin n) 𝔽) : ℝ) / (Fintype.card 𝔽 : ℝ) ^ (n * n) ∧
      1 - (Nat.card (GL (Fin n) 𝔽) : ℝ) / (Fintype.card 𝔽 : ℝ) ^ (n * n)
        ≤ 1 / ((Fintype.card 𝔽 : ℝ) - 1) := by
  rw [prob_invertible_eq]
  set q : ℝ := (Fintype.card 𝔽 : ℝ) with hqdef
  have hq2 : (2 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast hq
  have hqpos : 0 < q := by linarith
  have hqn : 0 < q ^ n := pow_pos hqpos n
  set a : Fin n → ℝ := fun i => q ^ (i : ℕ) / q ^ n with ha
  have ha0 : ∀ i, 0 ≤ a i := fun i => by positivity
  have ha1 : ∀ i, a i ≤ 1 := fun i => by
    simp only [ha]
    rw [div_le_one hqn]
    exact pow_le_pow_right₀ (by linarith) (le_of_lt i.2)
  constructor
  · -- the factor at `i = n − 1` is `1 − 1/q`, and all factors lie in `[0, 1]`
    let j : Fin n := ⟨n - 1, by omega⟩
    have hfac : ∏ i : Fin n, (1 - a i) ≤ 1 - a j := by
      rw [← mul_prod_erase univ (fun i => 1 - a i) (mem_univ j)]
      have h1 : ∏ i ∈ univ.erase j, (1 - a i) ≤ 1 :=
        prod_le_one₀ (fun i _ => by linarith [ha1 i]) (fun i _ => by linarith [ha0 i])
      have h2 : 0 ≤ 1 - a j := by linarith [ha1 j]
      nlinarith
    have haj : a j = 1 / q := by
      simp only [ha, j]
      have : n = (n - 1) + 1 := by omega
      conv_rhs => rw [show (1 : ℝ) / q = q ^ (n - 1) / q ^ (n - 1 + 1) by
        rw [pow_succ]; field_simp]
      rw [← this]
    linarith
  · -- union bound plus the geometric sum `Σ_{i<n} q^i = (q^n − 1)/(q − 1)`
    have hu := one_sub_sum_le_prod univ a (fun i _ => ha0 i) (fun i _ => ha1 i)
    have hsum : ∑ i : Fin n, a i = (∑ i ∈ range n, q ^ i) / q ^ n := by
      simp only [ha]
      rw [← sum_div, Fin.sum_univ_eq_sum_range (fun i => q ^ i)]
    have hgeom : (∑ i ∈ range n, q ^ i) * (q - 1) = q ^ n - 1 := geom_sum_mul q n
    have hq1 : 0 < q - 1 := by linarith
    have hbound : (∑ i ∈ range n, q ^ i) / q ^ n ≤ 1 / (q - 1) := by
      rw [div_le_div_iff₀ hqn hq1]
      nlinarith
    linarith

/-- uov-Ip (`m = 45` over `GF(256)`): a uniform `45 × 45` oil system is singular with probability in
`[2⁻⁸, 1/255]`. -/
theorem singular_prob_bounds_256 (h256 : Fintype.card 𝔽 = 256) :
    1 / (256 : ℝ) ≤ 1 - (Nat.card (GL (Fin 45) 𝔽) : ℝ) / (Fintype.card 𝔽 : ℝ) ^ (45 * 45) ∧
      1 - (Nat.card (GL (Fin 45) 𝔽) : ℝ) / (Fintype.card 𝔽 : ℝ) ^ (45 * 45) ≤ 1 / (255 : ℝ) := by
  obtain ⟨h1, h2⟩ := singular_prob_bounds (𝔽 := 𝔽) 45 (by norm_num) (by rw [h256]; norm_num)
  have e : (Fintype.card 𝔽 : ℝ) = 256 := by rw [h256]; norm_num
  constructor
  · calc 1 / (256 : ℝ) = 1 / (Fintype.card 𝔽 : ℝ) := by rw [e]
      _ ≤ _ := h1
  · calc _ ≤ 1 / ((Fintype.card 𝔽 : ℝ) - 1) := h2
      _ = 1 / 255 := by rw [e]; norm_num

end Singular

/-! ## 4. Shift choice in PomFRIT -/

/-- A prefix group made of `b ≤ 1` copies of the 8-bit tree and `a ≤ 16` of the 7-bit trees has
width `8b + 7a`. If it is the narrower of two complementary groups (total width 120), the wider one
is at least 6 bits wider. So, completing with the narrower group is at least `2⁶` times less likely
per `H₂³` query than completing with the wider one (note §7.4). -/
theorem group_gap (a b : ℕ) (hb : b ≤ 1) (ha : a ≤ 16) (hle : 2 * (8 * b + 7 * a) ≤ 120) :
    (120 - (8 * b + 7 * a)) - (8 * b + 7 * a) ≥ 6 := by
  interval_cases b <;> omega

/-- The gap 6 is attained: widths 57 (`b = 1`, `a = 7`) and 63. -/
theorem group_gap_attained : 8 * 1 + 7 * 7 = 57 ∧ 120 - 57 = 63 := by norm_num

/-- Guessing one of `τ` shifts for each of `k` forgeries succeeds with probability `τ^{-k}`; for
`τ = 17` this is at most `2^{-4k}`. -/
theorem guess_loss (k : ℕ) : (1 : ℝ) / 17 ^ k ≤ 1 / 16 ^ k := by
  apply one_div_le_one_div_of_le
  · positivity
  · exact pow_le_pow_left₀ (by norm_num) (by norm_num) k

/-! ## 5. One-more counting -/

/-- If the oracle was called on a set `S` of challenge indices and the forgery is a preimage of a
challenge index `j ∉ S`, the reduction holds preimages of `|S| + 1` distinct challenge indices after
`|S|` calls. If instead `w` calls went to non-challenge targets, it holds `h + 1` challenge
preimages after `h + w` calls, which is "one more" only when `w = 0` (note §6.2). -/
theorem one_more_count {ι : Type*} [DecidableEq ι] (S : Finset ι) (j : ι) (hj : j ∉ S) :
    (insert j S).card = S.card + 1 := card_insert_of_notMem hj

theorem wasted_calls (h w : ℕ) : h + 1 ≥ (h + w) + 1 ↔ w = 0 := by omega

end VoleMole.UOVAssumptions
