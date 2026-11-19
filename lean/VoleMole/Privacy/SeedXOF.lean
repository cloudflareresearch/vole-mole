import VoleMole.Privacy.Hybrid

/-!
# The seed-XOF hop: a fresh secret seed's XOF output is uniform

Every honest Client of the three protocols draws a fresh 32-byte OS seed per request and expands
it with a domain-separated SHAKE128 XOF into its randomness (PomFRIT: `(ρ, refresher, r) =
XOF_seed(DST ‖ seed ‖ dig(pk) ‖ msg)`, `pomfrit.cpp:150-161`; Moussaka: `nf ‖ r ‖ ρ_iss =
SHAKE128(ISSUE_SEED_DST ‖ seed)`, `ρ_red = SHAKE128(REDEEM_SEED_DST ‖ seed')`,
`moussaka.cpp:58-85`; Ratatouille: `nf ‖ r ‖ ρ = SHAKE128(DST ‖ seed)`, `ratatouille.cpp:63-84`).
The privacy games of `Privacy/` draw that randomness uniformly. This file proves the hop between
the two (PomFRIT's G0 → G1, Ratatouille's H1, Moussaka's D7), generically.

## The model

* **The XOF table** `g : K → R`: a uniform table with one cell per key `K` (a seed, or a domain
  and a seed). A cell holds everything the XOF answers at inputs that start with that key: for
  PomFRIT a column `Ctx → R₀` over the contexts `dig(pk) ‖ msg`, for Moussaka and Ratatouille the
  output itself (both domains' outputs are cells of one table keyed by `(domain, seed)`). An
  adversary that queries the XOF at an input reads the cell of the input's key (`RdX f q`: `f`
  reads at most `q` cells, adaptively).
* **The seeds** `c : C` and the **keys** `x c : ι → K` of the `ι` honest requests.
* **A game with XOF access** `W g u t`: the adversary's run reading the table `g`, with the
  requests' cells `u : ι → R` and the rest of the tape `t`.

## The hop

**`abs_pr_seed_le`**: the run with the real cells `u = g ∘ x c` and the run with independent
uniform cells `u` (the table untouched) are

    Pr[x c not injective] + δ

apart, where `δ` bounds, for any fixed set `F` of `q` keys, `Pr_c[∃ i, x c i ∈ F]`. Proof: for
injective keys, programming is perfect and the two runs differ only if the adversary reads a
programmed cell (`abs_pr_hidden_le`), at a key set that does not depend on the seeds; average over
the seeds.

**`abs_pr_seedGame_sub_le`** (the lift into a game): the tape of the real game `ins k u t` is built
from the requests' cells `u` (each request reading its cell at its context `k`, chosen by the
adversary from `g` and `t`) and the rest `t`, such that independent uniform cells give the uniform
tape (`hins`). If the game is `ε`-close in its two worlds **for every XOF table** (every existing
privacy theorem, applied to the adversary at that table), then the game with the seeds is

    ε + 2·(Pr[x c not injective] + δ)

close in its two worlds. The adversary reads at most `q_k` cells to choose the contexts and `q_g`
cells in its run (`hk`, `hg`); `δ` is for `q_k + q_g` keys.

**The bounds** (`pr_bool_not_injective_le`, `pr_bool_exists_mem_le`, `pr_dom_not_injective_le`,
`pr_dom_exists_mem_le`): two seeds on one key each (PomFRIT) give `1/|S|` and `2q/|S|`; two seeds
in each of two domains (Moussaka, Ratatouille, keys `(domain, seed)`) give `2/|S|` and `2q/|S|`:
a query reads one domain, in which it can hit one of two seeds.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy

/-! ## Reads of the XOF table -/

section Reads

variable {K R : Type*}

/-- **`f` reads the XOF table at most at `q` cells** (adaptively: outside the cells `Q g` the table
can change without changing `f`). -/
def RdX {X : Sort*} (f : (K → R) → X) (q : ℕ) : Prop :=
  ∃ Q : (K → R) → Finset K, (∀ g, (Q g).card ≤ q) ∧
    ∀ g g' : K → R, (∀ k ∈ Q g, g k = g' k) → f g' = f g

lemma RdX.mono {X : Sort*} {f : (K → R) → X} {q q' : ℕ} (h : RdX f q) (hq : q ≤ q') :
    RdX f q' := by
  obtain ⟨Q, hQ, hf⟩ := h
  exact ⟨Q, fun g => (hQ g).trans hq, hf⟩

/-- A function that does not read the table. -/
lemma RdX.const {X : Sort*} (x : X) : RdX (fun _ : K → R => x) 0 :=
  ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩

lemma RdX.map {X Y : Sort*} {f : (K → R) → X} {q : ℕ} (h : RdX f q) (m : X → Y) :
    RdX (fun g => m (f g)) q := by
  obtain ⟨Q, hQ, hf⟩ := h
  exact ⟨Q, hQ, fun g g' hg => by show m (f g') = m (f g); rw [hf g g' hg]⟩

/-- **Sequencing**: `F` run on `c`'s output reads what `c` reads and what `F` reads. -/
lemma RdX.bind [DecidableEq K] {X Y : Sort*} {c : (K → R) → X} {F : (K → R) → X → Y} {a b : ℕ}
    (hc : RdX c a) (hF : ∀ x, RdX (fun g => F g x) b) : RdX (fun g => F g (c g)) (a + b) := by
  obtain ⟨Qc, hQc, hc⟩ := hc
  choose QF hQF hF using hF
  refine ⟨fun g => Qc g ∪ QF (c g) g,
    fun g => (card_union_le _ _).trans (add_le_add (hQc g) (hQF _ g)), fun g g' hg => ?_⟩
  have h1 : c g' = c g := hc g g' fun k hk => hg k (mem_union_left _ hk)
  show F g' (c g') = F g (c g)
  rw [h1]
  exact hF (c g) g g' fun k hk => hg k (mem_union_right _ hk)

end Reads

/-! ## The hop -/

section Hop

variable {K R ι C T : Type*} [Fintype K] [DecidableEq K] [Fintype R] [Nonempty R]
  [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype C] [Nonempty C] [Fintype T] [Nonempty T]

/-- A bound for every first coordinate is a bound. -/
lemma pr_le_of_forall_fst {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] {P : α × β → Prop}
    {δ : ℝ} (h : ∀ a, pr β (fun b => P (a, b)) ≤ δ) : pr (α × β) P ≤ δ := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, div_le_iff₀ hα]
  calc ∑ a, pr β (fun b => P (a, b)) ≤ ∑ _a : α, δ := Finset.sum_le_sum fun a _ => h a
    _ = δ * Fintype.card α := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **The seed-XOF hop.** The run `W g u t` reads the XOF table `g` at most at `q` cells (for
every fixed `u`, `t`). Reading the requests' real cells `g ∘ x c` at uniform seeds `c` and reading
independent uniform cells `u` are `Pr[x c not injective] + δ` apart, where `δ` bounds the
probability that the seeds' keys meet a fixed set of `q` keys. -/
theorem abs_pr_seed_le (x : C → ι → K) (W : (K → R) → (ι → R) → T → Prop) {q : ℕ}
    (hW : ∀ u t, RdX (fun g => W g u t) q) {δ : ℝ}
    (hδ : ∀ F : Finset K, F.card ≤ q → pr C (fun c => ∃ i, x c i ∈ F) ≤ δ) :
    |pr (C × (T × (K → R))) (fun z => W z.2.2 (z.2.2 ∘ x z.1) z.2.1) -
        pr (T × ((K → R) × (ι → R))) (fun z => W z.2.1 z.2.2 z.1)| ≤
      pr C (fun c => ¬ Function.Injective (x c)) + δ := by
  classical
  choose Q hQ hW using hW
  set P1 := pr (T × ((K → R) × (ι → R))) (fun z => W z.2.1 z.2.2 z.1) with hP1
  let a : C → ℝ := fun c => pr (T × (K → R)) (fun p => W p.2 (p.2 ∘ x c) p.1)
  let e : C → ℝ := fun c =>
    pr (T × ((K → R) × (ι → R))) (fun p => ∃ i, x c i ∈ Q p.2.2 p.1 p.2.1)
  let nb : C → ℝ := fun c => if ¬ Function.Injective (x c) then 1 else 0
  have hone : ∀ c, |a c - P1| ≤ nb c + e c := by
    intro c
    by_cases hc : Function.Injective (x c)
    · have h := abs_pr_hidden_le (C := T) (x := fun _ => x c) (fun _ => hc)
        (fun t u g => W g u t) (fun t u g => Q u t g)
        (fun t u g g' h => Iff.of_eq (hW u t g g' h).symm)
      have hnb : nb c = 0 := by simp [nb, hc]
      rw [hnb, zero_add]
      exact h
    · have hnb : nb c = 1 := by simp [nb, hc]
      have h0 : 0 ≤ e c := pr_nonneg _
      have ha := pr_le_one (fun p : T × (K → R) => W p.2 (p.2 ∘ x c) p.1)
      have ha0 := pr_nonneg (fun p : T × (K → R) => W p.2 (p.2 ∘ x c) p.1)
      have hb := pr_le_one (fun z : T × ((K → R) × (ι → R)) => W z.2.1 z.2.2 z.1)
      have hb0 := pr_nonneg (fun z : T × ((K → R) × (ι → R)) => W z.2.1 z.2.2 z.1)
      rw [hnb, abs_sub_le_iff]
      constructor <;> linarith
  have hC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hL : pr (C × (T × (K → R))) (fun z => W z.2.2 (z.2.2 ∘ x z.1) z.2.1) =
      (∑ c, a c) / Fintype.card C :=
    pr_prod (fun z : C × (T × (K → R)) => W z.2.2 (z.2.2 ∘ x z.1) z.2.1)
  have hR : P1 = (∑ _c : C, P1) / Fintype.card C := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hnb : (∑ c, nb c) / Fintype.card C = pr C (fun c => ¬ Function.Injective (x c)) := by
    rw [pr_def]
    congr 1
    simp only [nb]
    rw [Finset.sum_boole]
  have he : (∑ c, e c) / Fintype.card C ≤ δ := by
    have h1 : (∑ c, e c) / Fintype.card C =
        pr (C × (T × ((K → R) × (ι → R)))) (fun z => ∃ i, x z.1 i ∈ Q z.2.2.2 z.2.1 z.2.2.1) :=
      (pr_prod (fun z : C × (T × ((K → R) × (ι → R))) =>
        ∃ i, x z.1 i ∈ Q z.2.2.2 z.2.1 z.2.2.1)).symm
    rw [h1, ← pr_equiv (Equiv.prodComm (T × ((K → R) × (ι → R))) C)]
    refine pr_le_of_forall_fst fun b => ?_
    exact le_trans (le_of_eq (pr_congr fun c => Iff.rfl)) (hδ (Q b.2.2 b.1 b.2.1) (hQ _ _ _))
  rw [hL, hR, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hC]
  calc |∑ c, (a c - P1)| / Fintype.card C ≤ (∑ c, (nb c + e c)) / Fintype.card C := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => hone c)
    _ = (∑ c, nb c) / Fintype.card C + (∑ c, e c) / Fintype.card C := by
        rw [Finset.sum_add_distrib, add_div]
    _ ≤ _ := by rw [hnb]; linarith

/-! ## The lift into a game -/

variable {Ω κ : Type*} [Fintype Ω]

/-- **The game with the seeds**: the tape is the seeds `c`, the rest `t` and the XOF table `g`; the
requests read their cells `g ∘ x c` at the contexts `cx g t`, and the game's tape is
`ins (cx g t) (g ∘ x c) t`. -/
def seedGame (G : (K → R) → Ω → Prop) (cx : (K → R) → T → κ) (ins : κ → (ι → R) → T → Ω)
    (x : C → ι → K) (z : C × (T × (K → R))) : Prop :=
  G z.2.2 (ins (cx z.2.2 z.2.1) (z.2.2 ∘ x z.1) z.2.1)

/-- With independent uniform cells, the game is the original game averaged over the XOF table. -/
theorem pr_seedIdeal (G : (K → R) → Ω → Prop) (cx : (K → R) → T → κ)
    (ins : κ → (ι → R) → T → Ω)
    (hins : ∀ (k : T → κ) (P : Ω → Prop),
      pr ((ι → R) × T) (fun z => P (ins (k z.2) z.1 z.2)) = pr Ω P) :
    pr (T × ((K → R) × (ι → R))) (fun z => G z.2.1 (ins (cx z.2.1 z.1) z.2.2 z.1)) =
      pr ((K → R) × Ω) (fun z => G z.1 z.2) := by
  let e : (K → R) × ((ι → R) × T) ≃ T × ((K → R) × (ι → R)) :=
    { toFun := fun z => (z.2.2, (z.1, z.2.1))
      invFun := fun z => (z.2.1, (z.2.2, z.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e, pr_prod, pr_prod]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  exact hins (cx g) (G g)

/-- **The hop in a game**: the game with the seeds and its average over the XOF table. -/
theorem abs_pr_seedGame_le (G : (K → R) → Ω → Prop) (cx : (K → R) → T → κ)
    (ins : κ → (ι → R) → T → Ω)
    (hins : ∀ (k : T → κ) (P : Ω → Prop),
      pr ((ι → R) × T) (fun z => P (ins (k z.2) z.1 z.2)) = pr Ω P)
    (x : C → ι → K) {qk qg : ℕ} (hk : ∀ t, RdX (fun g => cx g t) qk)
    (hg : ∀ ω, RdX (fun g => G g ω) qg) {δ : ℝ}
    (hδ : ∀ F : Finset K, F.card ≤ qk + qg → pr C (fun c => ∃ i, x c i ∈ F) ≤ δ) :
    |pr (C × (T × (K → R))) (seedGame G cx ins x) - pr ((K → R) × Ω) (fun z => G z.1 z.2)| ≤
      pr C (fun c => ¬ Function.Injective (x c)) + δ := by
  have h := abs_pr_seed_le x (fun g u t => G g (ins (cx g t) u t))
    (fun u t => RdX.bind (c := fun g => cx g t) (F := fun g k => G g (ins k u t)) (hk t)
      fun k => hg (ins k u t)) hδ
  rw [pr_seedIdeal G cx ins hins] at h
  exact h

/-- **The seed-XOF hop lifted to a two-world game.** If the game is `ε`-close in worlds `b` and
`b'` for every XOF table, the game with the seeds is `ε + 2·(Pr[x c not injective] + δ)`-close. -/
theorem abs_pr_seedGame_sub_le {β : Type*} (G : (K → R) → β → Ω → Prop)
    (cx : (K → R) → β → T → κ)
    (ins : κ → (ι → R) → T → Ω)
    (hins : ∀ (k : T → κ) (P : Ω → Prop),
      pr ((ι → R) × T) (fun z => P (ins (k z.2) z.1 z.2)) = pr Ω P)
    (x : C → ι → K) {qk qg : ℕ} (hk : ∀ b t, RdX (fun g => cx g b t) qk)
    (hg : ∀ b ω, RdX (fun g => G g b ω) qg) {δ : ℝ}
    (hδ : ∀ F : Finset K, F.card ≤ qk + qg → pr C (fun c => ∃ i, x c i ∈ F) ≤ δ)
    (b b' : β) {ε : ℝ} (hε : ∀ g, |pr Ω (G g b) - pr Ω (G g b')| ≤ ε) :
    |pr (C × (T × (K → R))) (seedGame (fun g => G g b) (fun g => cx g b) ins x) -
        pr (C × (T × (K → R))) (seedGame (fun g => G g b') (fun g => cx g b') ins x)| ≤
      ε + 2 * (pr C (fun c => ¬ Function.Injective (x c)) + δ) := by
  have h0 := abs_pr_seedGame_le (fun g => G g b) (fun g => cx g b) ins hins x (hk b) (hg b) hδ
  have h1 := abs_pr_seedGame_le (fun g => G g b') (fun g => cx g b') ins hins x (hk b') (hg b') hδ
  have hm : |pr ((K → R) × Ω) (fun z => G z.1 b z.2) - pr ((K → R) × Ω) (fun z => G z.1 b' z.2)| ≤
      ε := abs_pr_prod_sub_le _ _ fun g => hε g
  have := abs_sub_le (pr (C × (T × (K → R))) (seedGame (fun g => G g b) (fun g => cx g b) ins x))
    (pr ((K → R) × Ω) (fun z => G z.1 b z.2))
    (pr (C × (T × (K → R))) (seedGame (fun g => G g b') (fun g => cx g b') ins x))
  have := abs_sub_le (pr ((K → R) × Ω) (fun z => G z.1 b z.2))
    (pr ((K → R) × Ω) (fun z => G z.1 b' z.2))
    (pr (C × (T × (K → R))) (seedGame (fun g => G g b') (fun g => cx g b') ins x))
  rw [abs_sub_comm] at h1
  linarith

end Hop

/-! ## Guessing a seed, and seed collisions -/

section Seeds

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

/-- A uniform family's coordinate lands in a fixed set with probability `|G| / |S|`. -/
theorem pr_coord_mem_le (i : ι) (G : Finset S) :
    pr (ι → S) (fun c => c i ∈ G) ≤ G.card / Fintype.card S := by
  rw [← pr_equiv (Equiv.funSplitAt i S).symm]
  have : ∀ w : S × ({j // j ≠ i} → S), (Equiv.funSplitAt i S).symm w i = w.1 := fun w => by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  simp only [this]
  rw [pr_prod_fst (fun s => s ∈ G)]
  exact pr_mem_le id Function.injective_id G

/-- Two coordinates of a uniform family coincide with probability `1 / |S|`. -/
theorem pr_coord_eq_le {i j : ι} (hij : i ≠ j) :
    pr (ι → S) (fun c => c i = c j) ≤ 1 / Fintype.card S := by
  rw [← pr_equiv (Equiv.funSplitAt i S).symm]
  have h1 : ∀ w : S × ({j // j ≠ i} → S), (Equiv.funSplitAt i S).symm w i = w.1 := fun w => by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have h2 : ∀ w : S × ({j // j ≠ i} → S), (Equiv.funSplitAt i S).symm w j = w.2 ⟨j, hij.symm⟩ :=
    fun w => by simp [Equiv.funSplitAt, Equiv.piSplitAt, hij.symm]
  simp only [h1, h2]
  rw [← pr_equiv (Equiv.prodComm ({j // j ≠ i} → S) S)]
  refine pr_le_of_forall_fst fun r => ?_
  have := pr_mem_le (α := S) id Function.injective_id {r ⟨j, hij.symm⟩}
  rw [Finset.card_singleton, Nat.cast_one] at this
  refine le_trans (le_of_eq (pr_congr fun s => ?_)) this
  simp

/-- **Two seeds** (one key each) collide with probability `≤ 1 / |S|`. -/
theorem pr_bool_not_injective_le :
    pr (Bool → S) (fun c => ¬ Function.Injective c) ≤ 1 / Fintype.card S := by
  refine le_trans (pr_mono fun c hc => ?_) (pr_coord_eq_le (i := false) (j := true) (by decide))
  by_contra h
  refine hc fun a b hab => ?_
  cases a <;> cases b
  · rfl
  · exact absurd hab h
  · exact absurd hab.symm h
  · rfl

/-- **Two seeds**: a fixed set of `q` keys contains one of them with probability `≤ 2q / |S|`. -/
theorem pr_bool_exists_mem_le (F : Finset S) {q : ℕ} (hF : F.card ≤ q) :
    pr (Bool → S) (fun c => ∃ i, c i ∈ F) ≤ 2 * q / Fintype.card S := by
  refine (pr_exists_le_sum _).trans ?_
  rw [Fintype.sum_bool]
  have h1 := pr_coord_mem_le (S := S) true F
  have h2 := pr_coord_mem_le (S := S) false F
  have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hq : (F.card : ℝ) ≤ q := by exact_mod_cast hF
  have : (F.card : ℝ) / Fintype.card S ≤ q / Fintype.card S := by gcongr
  rw [mul_div_assoc]
  linarith

/-- The keys of two seeds in each of two domains. -/
def domKey (c : Bool × Bool → S) (i : Bool × Bool) : Bool × S := (i.1, c i)

/-- **Two seeds in each of two domains** (keys `(domain, seed)`): a collision within a domain has
probability `≤ 2 / |S|`. -/
theorem pr_dom_not_injective_le :
    pr (Bool × Bool → S) (fun c => ¬ Function.Injective (domKey c)) ≤ 2 / Fintype.card S := by
  have h0 := pr_coord_eq_le (S := S) (i := (false, false)) (j := (false, true)) (by decide)
  have h1 := pr_coord_eq_le (S := S) (i := (true, false)) (j := (true, true)) (by decide)
  refine le_trans (pr_mono (Q := fun c => c (false, false) = c (false, true) ∨
    c (true, false) = c (true, true)) fun c hc => ?_) ((pr_or_le _ _).trans ?_)
  · by_contra h
    push Not at h
    refine hc ?_
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    simp only [domKey, Prod.mk.injEq] at hab
    obtain ⟨rfl, hab⟩ := hab
    cases a <;> cases b <;> cases b' <;> simp_all
  · rw [show (2 : ℝ) / Fintype.card S = 1 / Fintype.card S + 1 / Fintype.card S by ring]
    exact add_le_add h0 h1

/-- **Two seeds in each of two domains**: a fixed set of `q` keys contains one of the four keys
with probability `≤ 2q / |S|` (a key lies in one domain, where it can hit one of two seeds). -/
theorem pr_dom_exists_mem_le (F : Finset (Bool × S)) {q : ℕ} (hF : F.card ≤ q) :
    pr (Bool × Bool → S) (fun c => ∃ i, domKey c i ∈ F) ≤ 2 * q / Fintype.card S := by
  classical
  let Fd : Bool → Finset S := fun d => (F.filter fun k => k.1 = d).image Prod.snd
  have hmem : ∀ d s, (d, s) ∈ F ↔ s ∈ Fd d := fun d s => by
    simp only [Fd, mem_image, mem_filter]
    constructor
    · intro h
      exact ⟨(d, s), ⟨h, rfl⟩, rfl⟩
    · rintro ⟨⟨d', s'⟩, ⟨h, hd⟩, hs⟩
      simp only at hd hs
      subst hd hs
      exact h
  have hcard : ((Fd false).card : ℝ) + (Fd true).card ≤ q := by
    have e1 : (Fd false).card ≤ (F.filter fun k => k.1 = false).card := card_image_le
    have e2 : (Fd true).card ≤ (F.filter fun k => ¬ k.1 = false).card := by
      refine card_image_le.trans (le_of_eq ?_)
      congr 1
      ext k
      simp
    have e3 := Finset.card_filter_add_card_filter_not (s := F) (fun k => k.1 = false)
    have : (Fd false).card + (Fd true).card ≤ q := by omega
    exact_mod_cast this
  refine (pr_exists_le_sum _).trans ?_
  have hsum : ∀ i : Bool × Bool,
      pr (Bool × Bool → S) (fun c => domKey c i ∈ F) ≤ (Fd i.1).card / Fintype.card S := by
    intro i
    refine le_trans (le_of_eq (pr_congr fun c => ?_)) (pr_coord_mem_le i (Fd i.1))
    exact hmem i.1 (c i)
  have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  calc ∑ i : Bool × Bool, pr (Bool × Bool → S) (fun c => domKey c i ∈ F)
      ≤ ∑ i : Bool × Bool, ((Fd i.1).card : ℝ) / Fintype.card S :=
        Finset.sum_le_sum fun i _ => hsum i
    _ = 2 * (((Fd false).card : ℝ) + (Fd true).card) / Fintype.card S := by
        rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
        ring
    _ ≤ 2 * q / Fintype.card S := by gcongr

/-- **Uniform columns read at fixed points are uniform**: the requests' columns `u i : Ctx → O`,
each read at its context `k i`. -/
theorem pr_cols {Ctx O : Type*} [Fintype Ctx] [DecidableEq Ctx] [Fintype O] [Nonempty O]
    (k : ι → Ctx) (P : (ι → O) → Prop) :
    pr (ι → Ctx → O) (fun u => P (fun i => u i (k i))) = pr (ι → O) P := by
  have h := close_restrict (K := ι × Ctx) (R := O) (x := fun i => (i, k i))
    (fun i j h => (Prod.mk.inj h).1) P
  rw [← pr_equiv (Equiv.curry ι Ctx O)]
  have h0 := abs_nonpos_iff.1 h
  rw [sub_eq_zero] at h0
  exact h0

end Seeds

end VoleMole.Privacy
