import VoleMole.Privacy.ComHide

/-!
# One-wayness of `Com` in a random-table model, for a query-bounded inverter

The theft theorems (`Theft/Ratatouille.lean`, `Theft/Moussaka.lean`) end with `Adv^ow`: the
advantage of an explicit inverter that must open one of the honest Client's commitments. In the
games `Com` is concrete code (the relations evaluate Keccak-p[800,12]) and the inverter is any
function, so some inverter wins with probability `1` (`Audit/Theft.lean`,
`owAdv_one_ratatouille`); the term is a computational assumption there, as `ε_hide` is for the
privacy theorems (`Privacy/ComHide.lean`).

This file is the counterpart of `Privacy/ComHide.lean` for one-wayness: the bound a
random-function model gives for the **standalone** experiment. `Com`'s cells are a uniform table
`g : K → Y`, keyed injectively by `(nf, r)` (`enc`); the inverter reads it by a **decision tree**
with at most `q` queries (`QTree`), sees the commitments and the nullifiers, and outputs a cell and
some auxiliary data; it wins if the cell's value is related to the commitments (`Wn`).

* **`QTree f q`**: `f` is computed from the table by at most `q` adaptive queries. It implies the
  read bound `RdX` of the hiding theorems (`QTree.rdX`), and reading the output cell costs one
  more query (`QTree.read`).
* **`pr_tree_bad`**: a tree with `q` queries outputs a cell whose value satisfies a predicate of
  probability `β` with probability at most `(q + 1)·β` (lazy sampling: `pr_resample`).
* **`owAdvRO_le`**: the inverter wins with probability at most

      Pr[r not injective] + |ι|·(q + 1)/|R| + (q + 1)·β,

  `β` the probability that a uniform cell value wins against given commitments. The first two
  terms are the hop of `ComHide.abs_pr_hideReal_unif_le` (a query at a true cell); the last is a
  preimage found among the cells read.
* **`owAdvColRO_num`** (Ratatouille's form: two commitments, columns over the credit value,
  `|R| = 2¹²⁸`, 256-bit values, 64-bit credits; the inverter picks a commitment, a credit value of
  it, and a cell with a credit value): `≤ (q + 2)·2⁻¹²⁶`. The note's estimate is `q_K·2⁻¹²⁷`
  (`security/ratatouille.md` §2.2); the factor `2` is the column model, in which a query at one
  credit value reads the whole column.
* **`owAdvRO_num`** (Moussaka's form: one commitment, 360-bit values): `≤ (q + 2)·2⁻¹²⁸ +
  (q + 1)·2⁻³⁶⁰`.

**This does not bound `owAdv` of the games** (for the reason in `Privacy/ComHide.lean`): there the
inverter runs the adversary and the extractor, which compute `Com`. It says what the term is in a
model where `Com` is an oracle and the inverter's queries are counted.
-/

open Finset

namespace VoleMole.Theft.ComOW

open VoleMole.Privacy VoleMole.Privacy.ComHide

/-- A bound for every value of the first coordinate is a bound on the product. -/
lemma pr_prod_le' {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] (P : α × β → Prop) {ε : ℝ}
    (h : ∀ a, pr β (fun b => P (a, b)) ≤ ε) : pr (α × β) P ≤ ε := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, div_le_iff₀ hα]
  calc ∑ a, pr β (fun b => P (a, b)) ≤ ∑ _a : α, ε := Finset.sum_le_sum fun a _ => h a
    _ = ε * Fintype.card α := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-! ## Decision trees over a table -/

section Tree

variable {K Y : Type*}

/-- **`f` is computed from the table by at most `q` adaptive queries.** -/
inductive QTree {O : Type*} : ((K → Y) → O) → ℕ → Prop
  | ret (o : O) (q : ℕ) : QTree (fun _ => o) q
  | ask (k : K) (G : Y → (K → Y) → O) (q : ℕ) (h : ∀ v, QTree (G v) q) :
      QTree (fun T => G (T k) T) (q + 1)

lemma QTree.mono {O : Type*} {f : (K → Y) → O} {q : ℕ} (h : QTree f q) :
    ∀ {q' : ℕ}, q ≤ q' → QTree f q' := by
  induction h with
  | ret o q => exact fun _ => .ret o _
  | ask k G q _ ih =>
    intro q' hq
    obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
    exact .ask k G q'' fun v => ih v (by omega)

/-- A function of the output costs no query. -/
lemma QTree.map {O O' : Type*} {f : (K → Y) → O} {q : ℕ} (h : QTree f q) (φ : O → O') :
    QTree (fun T => φ (f T)) q := by
  induction h with
  | ret o q => exact .ret _ _
  | ask k G q _ ih => exact .ask k (fun v T => φ (G v T)) q ih

/-- **Reading the output cell** costs one more query. -/
lemma QTree.read {O O' : Type*} {f : (K → Y) → O} {q : ℕ} (h : QTree f q) (c : O → K)
    (φ : Y → O → O') : QTree (fun T => φ (T (c (f T))) (f T)) (q + 1) := by
  induction h with
  | ret o q => exact (QTree.ask (c o) (fun v _ => φ v o) 0 fun v => .ret _ 0).mono (by omega)
  | ask k G q _ ih => exact .ask k (fun v T => φ (T (c (G v T))) (G v T)) (q + 1) ih

/-- **A decision tree reads the table at its queries** (`RdX`, the read bound of the hiding
theorems). -/
lemma QTree.rdX [DecidableEq K] {O : Type*} {f : (K → Y) → O} {q : ℕ} (h : QTree f q) :
    RdX f q := by
  induction h with
  | ret o q => exact ⟨fun _ => ∅, fun _ => by simp, fun _ _ _ => rfl⟩
  | ask k G q _ ih =>
    choose Q hQ hf using ih
    refine ⟨fun g => insert k (Q (g k) g), fun g => (card_insert_le _ _).trans
      (Nat.succ_le_succ (hQ _ g)), fun g g' hg => ?_⟩
    have hk : g k = g' k := hg k (mem_insert_self _ _)
    simp only
    rw [← hk]
    exact hf (g k) g g' fun j hj => hg j (mem_insert_of_mem hj)

variable [Fintype K] [DecidableEq K] [Fintype Y] [Nonempty Y]

/-- **Resampling one cell**: a uniform table with cell `k` redrawn is a uniform table. -/
theorem pr_resample (k : K) (P : (K → Y) → Prop) :
    pr (K → Y) P = pr (Y × (K → Y)) (fun z => P (Function.update z.2 k z.1)) := by
  let e : Y × (K → Y) ≃ Y × (K → Y) :=
    ⟨fun z => (z.2 k, Function.update z.2 k z.1), fun z => (z.2 k, Function.update z.2 k z.1),
      fun z => by simp, fun z => by simp⟩
  rw [← pr_prod_snd (α := Y) P, ← pr_equiv e]
  rfl

/-- A cell of a uniform table is uniform. -/
theorem pr_cell (a : K) (P : Y → Prop) : pr (K → Y) (fun T => P (T a)) = pr Y P := by
  rw [pr_resample a]
  simp only [Function.update_self]
  exact pr_prod_fst P

/-- The table with the cells of `σ` fixed. -/
def fixAt (σ : K → Option Y) (T : K → Y) : K → Y := fun k => (σ k).getD (T k)

omit [Fintype K] [Fintype Y] [Nonempty Y] in
lemma fixAt_update {σ : K → Option Y} {k : K} (hσ : σ k = none) (T : K → Y) (v : Y) :
    fixAt σ (Function.update T k v) = fixAt (Function.update σ k (some v)) T := by
  funext j
  by_cases hj : j = k
  · subst hj
    simp [fixAt, hσ]
  · simp [fixAt, Function.update_of_ne hj]

/-- **A tree with `q` queries finds a cell with a bad value with probability `≤ (q + 1)·β`**,
`β` the probability that a uniform value is bad (with some cells `σ` fixed and not counted). -/
theorem pr_tree_bad_fix {Bad : Y → Prop} {β : ℝ} (hβ : pr Y Bad ≤ β) {f : (K → Y) → K} {q : ℕ}
    (hf : QTree f q) : ∀ σ : K → Option Y,
      pr (K → Y) (fun T => σ (f (fixAt σ T)) = none ∧ Bad (T (f (fixAt σ T)))) ≤ (q + 1 : ℕ) * β := by
  have hβ0 : 0 ≤ β := le_trans (by unfold pr; positivity) hβ
  induction hf with
  | ret o q =>
    intro σ
    refine (pr_mono (Q := fun T => Bad (T o)) fun T h => h.2).trans ?_
    rw [pr_cell]
    push_cast
    nlinarith
  | ask k G q _ ih =>
    intro σ
    rcases hσ : σ k with _ | v₀
    · rw [pr_resample k]
      refine (pr_mono (Q := fun z : Y × (K → Y) => Bad z.1 ∨
        ((Function.update σ k (some z.1)) (G z.1 (fixAt (Function.update σ k (some z.1)) z.2)) = none ∧
          Bad (z.2 (G z.1 (fixAt (Function.update σ k (some z.1)) z.2)))))
        fun z hz => ?_).trans ((pr_or_le _ _).trans ?_)
      · obtain ⟨v, T⟩ := z
        simp only at hz ⊢
        rw [fixAt_update hσ] at hz
        have hk : fixAt (Function.update σ k (some v)) T k = v := by simp [fixAt]
        rw [hk] at hz
        by_cases ha : G v (fixAt (Function.update σ k (some v)) T) = k
        · left
          have := hz.2
          rwa [ha, Function.update_self] at this
        · right
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne ha]; exact hz.1
          · have := hz.2
            rwa [Function.update_of_ne ha] at this
      · have h1 : pr (Y × (K → Y)) (fun z => Bad z.1) ≤ β := by
          rw [pr_prod_fst (β := K → Y) Bad]; exact hβ
        have h2 := pr_prod_le' (α := Y) (β := K → Y) (fun z =>
          (Function.update σ k (some z.1)) (G z.1 (fixAt (Function.update σ k (some z.1)) z.2)) = none ∧
            Bad (z.2 (G z.1 (fixAt (Function.update σ k (some z.1)) z.2))))
          (ε := (q + 1 : ℕ) * β) fun v => ih v (Function.update σ k (some v))
        push_cast at h2 ⊢
        linarith
    · have e : (fun T : K → Y => σ (G (fixAt σ T k) (fixAt σ T)) = none ∧
          Bad (T (G (fixAt σ T k) (fixAt σ T)))) =
          fun T => σ (G v₀ (fixAt σ T)) = none ∧ Bad (T (G v₀ (fixAt σ T))) := by
        funext T
        have : fixAt σ T k = v₀ := by simp [fixAt, hσ]
        rw [this]
      rw [e]
      refine (ih v₀ σ).trans ?_
      push_cast
      nlinarith

/-- **A tree with `q` queries outputs a cell with a bad value with probability
`≤ (q + 1)·β`.** -/
theorem pr_tree_bad {Bad : Y → Prop} {β : ℝ} (hβ : pr Y Bad ≤ β) {f : (K → Y) → K} {q : ℕ}
    (hf : QTree f q) : pr (K → Y) (fun T => Bad (T (f T))) ≤ (q + 1 : ℕ) * β := by
  have h := pr_tree_bad_fix hβ hf fun _ => none
  refine le_trans (le_of_eq (pr_congr fun T => ?_)) h
  have : fixAt (fun _ => none) T = T := rfl
  simp [this]

end Tree

/-! ## One-wayness -/

section OW

variable {ι N R K Y A : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype N] [Nonempty N]
  [Fintype R] [Nonempty R] [Fintype K] [DecidableEq K] [Fintype Y] [Nonempty Y]

/-- **The one-wayness experiment in the random-table model.** The tape is the nullifiers, the
openings and the commitment table. The inverter `B` sees the table (by queries), the commitments
`g (enc (n i) (r i))` and the nullifiers, and outputs a cell and auxiliary data; it wins if the
cell's value, the commitments and the data are related by `Wn`. -/
def owRealRO (enc : N → R → K) (B : (K → Y) → (ι → Y) → (ι → N) → K × A)
    (Wn : Y → (ι → Y) → A → Prop) (z : (ι → N) × ((ι → R) × (K → Y))) : Prop :=
  Wn (z.2.2 (B z.2.2 (fun i => z.2.2 (enc (z.1 i) (z.2.1 i))) z.1).1)
    (fun i => z.2.2 (enc (z.1 i) (z.2.1 i)))
    (B z.2.2 (fun i => z.2.2 (enc (z.1 i) (z.2.1 i))) z.1).2

/-- **The one-wayness advantage in the random-table model.** -/
noncomputable def owAdvRO (enc : N → R → K) (B : (K → Y) → (ι → Y) → (ι → N) → K × A)
    (Wn : Y → (ι → Y) → A → Prop) : ℝ :=
  pr _ (owRealRO enc B Wn)

/-- **One-wayness in the random-table model.** For an inverter with at most `q` queries:

    Adv ≤ Pr[r not injective] + |ι|·(q + 1)/|R| + (q + 1)·β,

`β` a bound on the probability that a uniform cell value wins against given commitments. -/
theorem owAdvRO_le (enc : N → R → K) (henc : EncInj enc)
    (B : (K → Y) → (ι → Y) → (ι → N) → K × A) (Wn : Y → (ι → Y) → A → Prop) {q : ℕ}
    (hB : ∀ u n, QTree (fun g => B g u n) q) {β : ℝ}
    (hβ : ∀ u, pr Y (fun v => ∃ a, Wn v u a) ≤ β) :
    owAdvRO enc B Wn ≤ pr (ι → R) (fun r => ¬ Function.Injective r) +
      (Fintype.card ι : ℝ) * (q + 1 : ℕ) / Fintype.card R + (q + 1 : ℕ) * β := by
  let D : (K → Y) → (ι → Y) → (ι → N) → Prop := fun g u n => Wn (g (B g u n).1) u (B g u n).2
  have hD : ∀ u n, RdX (fun g => D g u n) (q + 1) := fun u n =>
    ((hB u n).read Prod.fst fun v o => Wn v u o.2).rdX
  have hop := abs_pr_hideReal_unif_le enc henc D hD
  have hideal : pr _ (hideUnifRO D) ≤ (q + 1 : ℕ) * β := by
    refine pr_prod_le' _ fun n => ?_
    rw [← pr_equiv (Equiv.prodComm (ι → Y) (K → Y))]
    refine pr_prod_le' _ fun u => ?_
    refine (pr_mono (Q := fun g : K → Y => ∃ a, Wn (g (B g u n).1) u a) fun g hg => ⟨_, hg⟩).trans ?_
    exact pr_tree_bad (hβ u) ((hB u n).map Prod.fst)
  have hr : owAdvRO enc B Wn = pr _ (hideRealRO enc D) := rfl
  have := (abs_sub_le_iff.1 hop).1
  rw [hr]
  linarith

end OW

/-! ## The two forms -/

section Forms

variable {N R K : Type*} [Fintype N] [Nonempty N] [Fintype R] [Nonempty R] [Fintype K]
  [DecidableEq K]

/-- A uniform value equals a given one with probability `1/|V|`. -/
lemma pr_eq_le {V : Type*} [Fintype V] [Nonempty V] (c : V) :
    pr V (fun v => v = c) ≤ 1 / Fintype.card V := by
  classical
  rw [pr_def]
  gcongr
  rw [Finset.filter_eq' univ c]
  simp

/-- **Ratatouille's form**: two commitments, each a column over the credit value. The inverter
outputs a cell, a credit value `t'` of it, a commitment `b` and a credit value `t` of it, and wins
if the cell's value at `t'` is commitment `b` at `t`:

    Adv ≤ (4 + 2(q + 1))/|R| + (q + 1)·2|Cr|²/|V|. -/
theorem owAdvColRO_le {Cr V : Type*} [Fintype Cr] [DecidableEq Cr] [Nonempty Cr] [Fintype V]
    [Nonempty V] (enc : N → R → K) (henc : EncInj enc)
    (B : (K → Cr → V) → (Bool → Cr → V) → (Bool → N) → K × (Bool × Cr × Cr)) {q : ℕ}
    (hB : ∀ u n, QTree (fun g => B g u n) q) :
    owAdvRO enc B (fun v u a => v a.2.2 = u a.1 a.2.1) ≤
      (4 + 2 * (q + 1 : ℕ)) / Fintype.card R +
        (q + 1 : ℕ) * (2 * (Fintype.card Cr : ℝ) ^ 2 / Fintype.card V) := by
  have hβ : ∀ u : Bool → Cr → V, pr (Cr → V) (fun v => ∃ a : Bool × Cr × Cr,
      v a.2.2 = u a.1 a.2.1) ≤ 2 * (Fintype.card Cr : ℝ) ^ 2 / Fintype.card V := by
    intro u
    refine (pr_exists_le_sum _).trans ?_
    calc ∑ a : Bool × Cr × Cr, pr (Cr → V) (fun v => v a.2.2 = u a.1 a.2.1)
        ≤ ∑ _a : Bool × Cr × Cr, (1 : ℝ) / Fintype.card V :=
          Finset.sum_le_sum fun a _ => by
            rw [pr_cell a.2.2 (fun x => x = u a.1 a.2.1)]
            exact pr_eq_le _
      _ = 2 * (Fintype.card Cr : ℝ) ^ 2 / Fintype.card V := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
          Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring
  have h := owAdvRO_le enc henc B (fun v u a => v a.2.2 = u a.1 a.2.1) hB hβ
  have hi := pr_not_injective_le (ι := Bool) (S := R)
  rw [Fintype.card_bool] at h hi
  have e : (4 + 2 * ((q + 1 : ℕ) : ℝ)) / Fintype.card R =
      ((2 : ℕ) : ℝ) ^ 2 / Fintype.card R + ((2 : ℕ) : ℝ) * (q + 1 : ℕ) / Fintype.card R := by
    push_cast
    ring
  rw [e]
  linarith

/-- **Ratatouille's form, in numbers**: 128-bit openings, 64-bit credit values, 256-bit
commitments, an inverter with `q` queries: `Adv ≤ (4q + 8)·2⁻¹²⁸ = (q + 2)·2⁻¹²⁶`. -/
theorem owAdvColRO_num {Cr V : Type*} [Fintype Cr] [DecidableEq Cr] [Nonempty Cr] [Fintype V]
    [Nonempty V] (hR : Fintype.card R = 2 ^ 128) (hCr : Fintype.card Cr = 2 ^ 64)
    (hV : Fintype.card V = 2 ^ 256) (enc : N → R → K) (henc : EncInj enc)
    (B : (K → Cr → V) → (Bool → Cr → V) → (Bool → N) → K × (Bool × Cr × Cr)) {q : ℕ}
    (hB : ∀ u n, QTree (fun g => B g u n) q) :
    owAdvRO enc B (fun v u a => v a.2.2 = u a.1 a.2.1) ≤ (4 * q + 8 : ℕ) / 2 ^ 128 := by
  have h := owAdvColRO_le enc henc B hB
  rw [hR, hCr, hV] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- **Moussaka's form**: one commitment; the inverter outputs a cell and wins if its value is the
commitment: `Adv ≤ (q + 2)/|R| + (q + 1)/|V|`. -/
theorem owAdvRO_one_le {V : Type*} [Fintype V] [Nonempty V] (enc : N → R → K) (henc : EncInj enc)
    (B : (K → V) → (Unit → V) → (Unit → N) → K × Unit) {q : ℕ}
    (hB : ∀ u n, QTree (fun g => B g u n) q) :
    owAdvRO enc B (fun v u _ => v = u ()) ≤
      (q + 2 : ℕ) / Fintype.card R + (q + 1 : ℕ) * (1 / Fintype.card V) := by
  have hβ : ∀ u : Unit → V, pr V (fun v => ∃ _a : Unit, v = u ()) ≤ 1 / Fintype.card V := by
    intro u
    refine (pr_mono fun v hv => ?_).trans (pr_eq_le (u ()))
    obtain ⟨_, h⟩ := hv
    exact h
  have h := owAdvRO_le enc henc B (fun v u _ => v = u ()) hB hβ
  have hi := pr_not_injective_le (ι := Unit) (S := R)
  rw [Fintype.card_unit] at h hi
  have e : ((q + 2 : ℕ) : ℝ) / Fintype.card R =
      ((1 : ℕ) : ℝ) ^ 2 / Fintype.card R + ((1 : ℕ) : ℝ) * (q + 1 : ℕ) / Fintype.card R := by
    push_cast
    ring
  rw [e]
  linarith

set_option exponentiation.threshold 400 in
/-- **Moussaka's form, in numbers**: 128-bit openings, 360-bit commitments:
`Adv ≤ (q + 2)·2⁻¹²⁸ + (q + 1)·2⁻³⁶⁰`. -/
theorem owAdvRO_num {V : Type*} [Fintype V] [Nonempty V] (hR : Fintype.card R = 2 ^ 128)
    (hV : Fintype.card V = 2 ^ 360) (enc : N → R → K) (henc : EncInj enc)
    (B : (K → V) → (Unit → V) → (Unit → N) → K × Unit) {q : ℕ}
    (hB : ∀ u n, QTree (fun g => B g u n) q) :
    owAdvRO enc B (fun v u _ => v = u ()) ≤
      (q + 2 : ℕ) / 2 ^ 128 + (q + 1 : ℕ) / 2 ^ 360 := by
  have h := owAdvRO_one_le enc henc B hB
  rw [hR, hV] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end Forms

end VoleMole.Theft.ComOW
