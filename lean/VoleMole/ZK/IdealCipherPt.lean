import VoleMole.ZK.IdealCipher

/-!
# Puncturing a GGM tree at points, with an expected charge (hop H4 at points)

`ZK/IdealCipher.lean` (`IC.puncture`) replaces the **rows** of the secret nodes by independent
uniform rows. Its hop for node `n` charges every read of the table at the node's value `v`,
whatever the input: the distinguisher reads whole rows (keys), and its number of keys is a
worst-case budget `q`. So the hybrid costs `|secret|·(N + q)/|K|`.

Here the distinguisher reads the table at **points** `(k, z)` (`Q o G : Finset (K × X)`), and a
secret node's row is replaced only on a set `P ⊆ X` of inputs (`rowAtP`: the replacement row on
`P`, the table at the node's value elsewhere). If `P` contains every input at which the
computation reads a secret row (`hPx`, `hΦP`: for the BAVC, the CTR blocks of the proof's `iv`),
the hop for node `n` changes the view only when the distinguisher reads the table at the node's
value **on `P`**, or another node has the same value. The node's value is uniform and independent
of the replaced experiment, so (`pr_mem_reset_exp`, the expectation form of `pr_mem_reset_le`) the
hop costs

    (N + E[#{k | ∃ z ∈ P, (k, z) ∈ Q}]) / |K|            (`hopPt`),

the expectation taken in the experiment after the hop. A read at an input off `P` is free.

* `rowAtP`, `keyAtP`, `experPt`: rows, values and the experiment with the secret nodes replaced on
  `P` only. With nothing replaced it is `exper ∅` (`experPt_empty`); with all secret nodes
  replaced, if the output reads secret rows only on `P`, it is `exper` of `IC.puncture`'s fully
  replaced experiment (`experPt_full`), so `ZK/HopsH4Ideal.lean`'s last step applies unchanged.
* `puncturePt`: the hybrid over the secret nodes, each hop charged its expectation.
* **`puncturePt_real`**: the charges moved to the **real** experiment. The experiments of the
  hybrid are close, and the charge is a bounded function of the view (`qm`), so each expectation
  is within `qm·S` of the real one, `S` the hybrid's total; solving for `S`:

      |real − fully replaced| ≤ |secret|·(N + E_real[#keys read on P]) / (|K| − |secret|·qm).

  This needs a **consistent** reader (`hQc`: the read set is determined by the values read), so
  that the charge's level sets are events of the view.
* `exP`, `exP_eq_sum_pr` (layer cake), `pr_mem_exp`, `pr_mem_reset_exp`: expectations under a
  uniform tape.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.IC

open VoleMole.Privacy

/-! ## Expectations under a uniform tape -/

section Ex

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **The expectation of `f` under the uniform distribution on `α`** (as `Theft.exU`). -/
noncomputable def exP (α : Type*) [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

lemma exP_nonneg {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) : 0 ≤ exP α f :=
  div_nonneg (Finset.sum_nonneg fun a _ => hf a) (Nat.cast_nonneg _)

lemma exP_mono {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : exP α f ≤ exP α g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (Nat.cast_nonneg _)

lemma exP_const_add [Nonempty α] (c : ℝ) (f : α → ℝ) :
    exP α (fun a => c + f a) = c + exP α f := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [exP]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_div,
    mul_div_cancel_left₀ _ hc]

lemma exP_equiv (e : α ≃ β) (f : β → ℝ) : exP α (fun a => f (e a)) = exP β f := by
  simp only [exP]
  rw [Fintype.card_congr e, Equiv.sum_comp e f]

lemma exP_prod_fst [Nonempty β] (f : α → ℝ) : exP (α × β) (fun p => f p.1) = exP α f := by
  have hb : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [exP]
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  field_simp

/-- A natural number below `B` is the number of `i < B` below it. -/
lemma natCast_eq_sum_range {k B : ℕ} (h : k ≤ B) :
    (k : ℝ) = ∑ i ∈ range B, if i < k then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]
  have : (range B).filter (· < k) = range k := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

/-- **Layer cake**: the expectation of a natural-valued function below `B` is the sum of the
probabilities of its level sets. -/
theorem exP_eq_sum_pr (g : α → ℕ) {B : ℕ} (hg : ∀ a, g a ≤ B) :
    exP α (fun a => (g a : ℝ)) = ∑ i ∈ range B, pr α (fun a => i < g a) := by
  classical
  simp only [exP]
  rw [Finset.sum_congr rfl fun a _ => natCast_eq_sum_range (hg a), Finset.sum_comm,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pr_def, Finset.sum_boole]

/-- **Two laws close on the level sets have close expectations.** -/
theorem exP_sub_le_of_levels {γ : Type*} [Fintype γ] (g : α → ℕ) (g' : γ → ℕ) {B : ℕ}
    (hg : ∀ a, g a ≤ B) (hg' : ∀ c, g' c ≤ B) {δ : ℝ}
    (h : ∀ i < B, |pr α (fun a => i < g a) - pr γ (fun c => i < g' c)| ≤ δ) :
    |exP α (fun a => (g a : ℝ)) - exP γ (fun c => (g' c : ℝ))| ≤ B * δ := by
  rw [exP_eq_sum_pr g hg, exP_eq_sum_pr g' hg', ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ range B, |pr α (fun a => i < g a) - pr γ (fun c => i < g' c)|
      ≤ ∑ _i ∈ range B, δ := Finset.sum_le_sum fun i hi => h i (Finset.mem_range.1 hi)
    _ = B * δ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Ex

/-! ## Guessing a coordinate, in expectation -/

section ResetExp

variable {α β K : Type*} [Fintype α] [Fintype β] [Fintype K] [Nonempty K]

/-- **An independent uniform coordinate lies in a set with probability `E[|set|] / |K|`.** -/
theorem pr_mem_exp (T : β → Finset K) :
    pr (K × β) (fun p => p.1 ∈ T p.2) = exP β (fun b => ((T b).card : ℝ)) / Fintype.card K := by
  classical
  rw [← pr_equiv (Equiv.prodComm β K), pr_prod]
  have hK : (Fintype.card K : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have e : ∀ b, pr K (fun k => (Equiv.prodComm β K (b, k)).1 ∈ T (Equiv.prodComm β K (b, k)).2) =
      ((T b).card : ℝ) / Fintype.card K := fun b => by
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    rw [pr_def, Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp only [e, exP]
  rw [← Finset.sum_div, div_div, div_div, mul_comm]

/-- **A coordinate the candidates do not depend on is guessed with probability
`E[|candidates|] / |K|`** (`pr_mem_reset_le` with an expectation in place of a worst case). -/
theorem pr_mem_reset_exp (f : α → K) (set : α → K → α) (hf : ∀ a k, f (set a k) = k)
    (hss : ∀ a k k', set (set a k) k' = set a k') (hsf : ∀ a, set a (f a) = a)
    (T : α → Finset K) (hT : ∀ a k, T (set a k) = T a) :
    pr α (fun a => f a ∈ T a) ≤ exP α (fun a => ((T a).card : ℝ)) / Fintype.card K := by
  classical
  obtain ⟨k0⟩ := (inferInstance : Nonempty K)
  by_cases hα : Nonempty α
  swap
  · rw [not_nonempty_iff] at hα
    rw [pr_def]
    simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      zero_div]
    exact div_nonneg (exP_nonneg fun _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨a0⟩ := hα
  let γ := {a : α // set a k0 = a}
  have : Nonempty γ := ⟨⟨set a0 k0, hss _ _ _⟩⟩
  let e : α ≃ K × γ :=
    { toFun := fun a => (f a, ⟨set a k0, hss _ _ _⟩)
      invFun := fun p => set p.2.1 p.1
      left_inv := fun a => by simp only [hss, hsf]
      right_inv := fun p => by
        obtain ⟨k, b, hb⟩ := p
        simp only [hf, Prod.mk.injEq, true_and]
        exact Subtype.ext (by simp only [hss]; exact hb) }
  have h1 : pr α (fun a => f a ∈ T a) = pr (K × γ) (fun p => p.1 ∈ T p.2.1) := by
    rw [← pr_equiv e.symm]
    refine pr_congr fun p => ?_
    show f (set p.2.1 p.1) ∈ T (set p.2.1 p.1) ↔ p.1 ∈ T p.2.1
    rw [hf, hT]
  have h2 : exP α (fun a => ((T a).card : ℝ)) = exP γ (fun b => ((T b.1).card : ℝ)) := by
    calc exP α (fun a => ((T a).card : ℝ))
        = exP (K × γ) (fun p => ((T (e.symm p)).card : ℝ)) :=
          (exP_equiv e.symm (fun a => ((T a).card : ℝ))).symm
      _ = exP (K × γ) (fun p => ((T p.2.1).card : ℝ)) := by
          congr 1
          funext p
          show ((T (set p.2.1 p.1)).card : ℝ) = ((T p.2.1).card : ℝ)
          rw [hT]
      _ = exP (γ × K) (fun q => ((T q.1.1).card : ℝ)) :=
          (exP_equiv (Equiv.prodComm γ K) (fun p => ((T p.2.1).card : ℝ))).symm
      _ = exP γ (fun b => ((T b.1).card : ℝ)) := exP_prod_fst (fun b : γ => ((T b.1).card : ℝ))
  rw [h1, h2]
  exact le_of_eq (pr_mem_exp (fun b : γ => T b.1))

end ResetExp

/-! ## Rows replaced on a set of points -/

section TreeP

variable {K X : Type} (x : ℕ → X) (N : ℕ) (P : X → Prop) [DecidablePred P]

/-- The row `r` on `P` and `e` elsewhere. -/
def patchP (r e : X → K) : X → K := fun z => if P z then r z else e z

/-- **The row of node `n`, replaced on `P`**: for a replaced node, `R n` on `P` and the table at
the node's value elsewhere; otherwise the table at the node's value. -/
def rowAtP (rep : Finset ℕ) (E : K → X → K) (R : Fin N → X → K) (seed : K) : ℕ → X → K
  | 0 => if h : 0 ∈ rep ∧ 0 < N then patchP P (R ⟨0, h.2⟩) (E seed) else E seed
  | n + 1 => if h : n + 1 ∈ rep ∧ n + 1 < N then
      patchP P (R ⟨n + 1, h.2⟩) (E (rowAtP rep E R seed (n / 2) (x (n + 1))))
      else E (rowAtP rep E R seed (n / 2) (x (n + 1)))
decreasing_by all_goals omega

/-- **The value of node `n`**: the root seed, or the parent's row at the node's input. -/
def keyAtP (rep : Finset ℕ) (E : K → X → K) (R : Fin N → X → K) (seed : K) : ℕ → K
  | 0 => seed
  | n + 1 => rowAtP x N P rep E R seed (n / 2) (x (n + 1))

variable {x N P}
variable {rep : Finset ℕ} {E : K → X → K} {R : Fin N → X → K} {seed : K}

lemma patchP_of_P {r e : X → K} {z : X} (h : P z) : patchP P r e z = r z := by
  simp only [patchP, h, ↓reduceIte]

lemma rowAtP_eq (rep : Finset ℕ) (E : K → X → K) (R : Fin N → X → K) (seed : K) (n : ℕ) :
    rowAtP x N P rep E R seed n =
      if h : n ∈ rep ∧ n < N then patchP P (R ⟨n, h.2⟩) (E (keyAtP x N P rep E R seed n))
      else E (keyAtP x N P rep E R seed n) := by
  cases n with
  | zero => rw [rowAtP]; rfl
  | succ n => rw [rowAtP]; rfl

lemma rowAtP_of_mem {n : ℕ} (h : n ∈ rep) (hn : n < N) :
    rowAtP x N P rep E R seed n = patchP P (R ⟨n, hn⟩) (E (keyAtP x N P rep E R seed n)) := by
  rw [rowAtP_eq, dite_eq_left_of_eq_true (eq_true ⟨h, hn⟩)]

lemma rowAtP_of_not_mem {n : ℕ} (h : n ∉ rep) :
    rowAtP x N P rep E R seed n = E (keyAtP x N P rep E R seed n) := by
  rw [rowAtP_eq, dite_eq_right_of_eq_false (eq_false fun h' => h h'.1)]

lemma keyAtP_pos {n : ℕ} (hn : n ≠ 0) :
    keyAtP x N P rep E R seed n = rowAtP x N P rep E R seed ((n - 1) / 2) (x n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

/-- The value of a node whose parent is replaced and whose input is in `P`. -/
lemma keyAtP_of_par {n : ℕ} (hn : n ≠ 0) (hp : (n - 1) / 2 ∈ rep) (hN : (n - 1) / 2 < N)
    (hPx : P (x n)) : keyAtP x N P rep E R seed n = R ⟨(n - 1) / 2, hN⟩ (x n) := by
  rw [keyAtP_pos hn, rowAtP_of_mem hp hN, patchP_of_P hPx]

/-- With nothing replaced, `rowAtP` is `rowAt` (and reads no replacement row). -/
lemma rowAtP_empty (E : K → X → K) (R R' : Fin N → X → K) (s : K) :
    rowAtP x N P ∅ E R s = rowAt x N ∅ E R' s := by
  funext m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [rowAtP_of_not_mem (Finset.notMem_empty _), rowAt_of_not_mem (Finset.notMem_empty _)]
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rfl
    · rw [keyAtP_pos (by omega), keyAt_pos (by omega), ih _ (by omega)]

/-- **With all secret nodes replaced, the rows agree with `IC.rowAt`'s fully replaced rows** on
the non-secret nodes, and on `P` for the secret ones (if every input is in `P`). -/
lemma rowAtP_full_agree (sec : ℕ → Prop) [DecidablePred sec] (hPx : ∀ m, P (x m))
    (E : K → X → K) (R : Fin N → X → K) (s : K) :
    ∀ m < N, (¬ sec m → rowAtP x N P ((range N).filter sec) E R s m =
        rowAt x N ((range N).filter sec) E R s m ∧
        keyAtP x N P ((range N).filter sec) E R s m = keyAt x N ((range N).filter sec) E R s m) ∧
      (sec m → ∀ z, P z → rowAtP x N P ((range N).filter sec) E R s m z =
        rowAt x N ((range N).filter sec) E R s m z) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hmem : m ∈ (range N).filter sec ↔ sec m := by simp [hm]
    refine ⟨fun hs => ?_, fun hs z hz => ?_⟩
    · have hnm : m ∉ (range N).filter sec := fun h => hs (hmem.1 h)
      have hkey : keyAtP x N P ((range N).filter sec) E R s m =
          keyAt x N ((range N).filter sec) E R s m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · rfl
        · rw [keyAtP_pos (by omega), keyAt_pos (by omega)]
          have hq : (m - 1) / 2 < N := by omega
          by_cases hsq : sec ((m - 1) / 2)
          · exact (ih _ (by omega) hq).2 hsq _ (hPx m)
          · rw [((ih _ (by omega) hq).1 hsq).1]
      exact ⟨by rw [rowAtP_of_not_mem hnm, rowAt_of_not_mem hnm, hkey], hkey⟩
    · rw [rowAtP_of_mem (hmem.2 hs) hm, rowAt_of_mem (hmem.2 hs) hm, patchP_of_P hz]

end TreeP

/-! ## One hop at points -/

section HopP

variable {K X : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype X] [DecidableEq X]
  {x : ℕ → X} {N : ℕ} {O : Type} {P : X → Prop} [DecidablePred P]

variable (x N P) in
/-- **The experiment with the nodes `rep` replaced on `P`**: `A` sees `Φ` of the rows and reads
the table. -/
noncomputable def experPt (rep : Finset ℕ) (Φ : (ℕ → X → K) → O)
    (A : O → (K → X → K) → Prop) : ℝ :=
  pr (Coins K X N × (K → X → K)) (fun p => A (Φ (rowAtP x N P rep p.2 p.1.2 p.1.1)) p.2)

variable (P) in
/-- **The keys read on `P`**: the keys `k` with some read point `(k, z)`, `z ∈ P`. -/
def qkeys (S : Finset (K × X)) : Finset K := (S.filter fun kz => P kz.2).image Prod.fst

lemma qkeys_card_le (S : Finset (K × X)) :
    (qkeys P S).card ≤ (S.filter fun kz => P kz.2).card := Finset.card_image_le

/-- **The real experiment**, with replacement on points or not: nothing is replaced. -/
theorem experPt_empty (Φ : (ℕ → X → K) → O) (A : O → (K → X → K) → Prop) :
    experPt x N P ∅ Φ A = exper x N ∅ Φ A :=
  pr_congr fun p => by rw [rowAtP_empty (P := P) p.2 p.1.2 p.1.2 p.1.1]

/-- **The fully replaced experiment** at points is `IC.puncture`'s, if `Φ` reads the secret rows
only on `P` and every input is in `P`. -/
theorem experPt_full (sec : ℕ → Prop) [DecidablePred sec] (hPx : ∀ m, P (x m))
    (Φ : (ℕ → X → K) → O)
    (hΦP : ∀ ρ ρ', (∀ m < N, sec m → ∀ z, P z → ρ m z = ρ' m z) →
      (∀ m < N, ¬ sec m → ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → (K → X → K) → Prop) :
    experPt x N P ((range N).filter sec) Φ A = exper x N ((range N).filter sec) Φ A :=
  pr_congr fun p => by
    rw [hΦP _ _ (fun m hm hs => (rowAtP_full_agree sec hPx p.2 p.1.2 p.1.1 m hm).2 hs)
      (fun m hm hs => ((rowAtP_full_agree sec hPx p.2 p.1.2 p.1.1 m hm).1 hs).1)]

/-- An expectation in the real experiment, in `realPr`'s coordinates. -/
theorem exP_empty (Φ : (ℕ → X → K) → O) (f : O → (K → X → K) → ℝ) :
    exP (Coins K X N × (K → X → K)) (fun p => f (Φ (rowAt x N ∅ p.2 p.1.2 p.1.1)) p.2) =
      exP (K × (K → X → K)) (fun p => f (Φ (rowAt x N ∅ p.2 (fun _ _ => p.1) p.1)) p.2) := by
  let e : Coins K X N × (K → X → K) ≃ (K × (K → X → K)) × (Fin N → X → K) :=
    { toFun := fun c => ((c.1.1, c.2), c.1.2)
      invFun := fun c => ((c.1.1, c.2), c.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← exP_prod_fst (β := Fin N → X → K) (fun p : K × (K → X → K) =>
      f (Φ (rowAt x N ∅ p.2 (fun _ _ => p.1) p.1)) p.2),
    ← exP_equiv e]
  congr 1
  funext c
  show f (Φ (rowAt x N ∅ c.2 c.1.2 c.1.1)) c.2 = f (Φ (rowAt x N ∅ c.2 (fun _ _ => c.1.1) c.1.1)) c.2
  rw [rowAt_empty c.2 c.1.2 (fun _ _ => c.1.1) c.1.1]

/-! ### Programming the table at the points of one row -/

variable (P) in
/-- The table `E` with the row at `v` replaced by `r` on `P`. -/
def progP (v : K) (r : X → K) (E : K → X → K) : K → X → K :=
  Function.update E v (patchP P r (E v))

lemma progP_ne {v k : K} (h : k ≠ v) (r : X → K) (E : K → X → K) : progP P v r E k = E k :=
  Function.update_of_ne h _ _

lemma progP_self (v : K) (r : X → K) (E : K → X → K) : progP P v r E v = patchP P r (E v) :=
  Function.update_self _ _ _

variable (P) in
/-- Program the row at `v` on `P` with the answer, and move the old values to the answer (an
involution). -/
def swapP (v : K) : (K → X → K) × (Unit → X → K) ≃ (K → X → K) × (Unit → X → K) where
  toFun a := (progP P v (a.2 ()) a.1, fun _ => patchP P (a.1 v) (a.2 ()))
  invFun a := (progP P v (a.2 ()) a.1, fun _ => patchP P (a.1 v) (a.2 ()))
  left_inv a := by
    obtain ⟨E, u⟩ := a
    refine Prod.ext ?_ (funext fun _ => funext fun z => ?_)
    · simp only [progP, Function.update_self, Function.update_idem]
      refine Function.update_eq_iff.2 ⟨funext fun z => ?_, fun _ _ => rfl⟩
      simp only [patchP]; split_ifs <;> rfl
    · simp only [progP, Function.update_self, patchP]; split_ifs <;> rfl
  right_inv a := by
    obtain ⟨E, u⟩ := a
    refine Prod.ext ?_ (funext fun _ => funext fun z => ?_)
    · simp only [progP, Function.update_self, Function.update_idem]
      refine Function.update_eq_iff.2 ⟨funext fun z => ?_, fun _ _ => rfl⟩
      simp only [patchP]; split_ifs <;> rfl
    · simp only [progP, Function.update_self, patchP]; split_ifs <;> rfl

/-- **Programming a uniform table at the points `{v} × P` with uniform values is perfect.** -/
theorem pr_progP_eq {C : Type} [Fintype C] (v : C → K) (A : C → (K → X → K) → Prop) :
    pr (C × (K → X → K)) (fun p => A p.1 p.2) =
      pr (C × ((K → X → K) × (Unit → X → K))) (fun p => A p.1 (progP P (v p.1) (p.2.2 ()) p.2.1)) := by
  rw [← pr_add_answers (ι := Unit) (fun p : C × (K → X → K) => A p.1 p.2), pr_prod, pr_prod]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  exact (pr_equiv (swapP P (v c)) (fun q => A c q.1)).symm

/-! ### The rows of the programmed and of the replaced experiment -/

lemma keyAtP_secret {rep : Finset ℕ} {n : ℕ} (hN : n < N) (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep)
    (hPx : ∀ m, P (x m)) (E : K → X → K) (c : Coins K X N) :
    keyAtP x N P rep E c.2 c.1 n = secretVal (x := x) n hN c := by
  unfold secretVal
  split_ifs with h0
  · subst h0; rfl
  · exact keyAtP_of_par h0 (hpar h0) _ (hPx n)

/-- **Identical until the secret value is read on `P`**: with the table programmed at node `n`'s
value on `P` by `u`, the experiment with `rep` is the one with `n` also replaced by `u` (on `P`),
unless another node below `N` has the same value. -/
lemma rowAtP_program {rep : Finset ℕ} {n : ℕ} (hN : n < N) (hnr : n ∉ rep)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep) (hPx : ∀ m, P (x m)) (E : K → X → K) (c : Coins K X N)
    (u : X → K)
    (hgood : ∀ m < N, m ≠ n →
      keyAtP x N P (insert n rep) E (Function.update c.2 ⟨n, hN⟩ u) c.1 m ≠
        secretVal (x := x) n hN c) :
    ∀ m < N, rowAtP x N P rep (progP P (secretVal (x := x) n hN c) u E) c.2 c.1 m =
        rowAtP x N P (insert n rep) E (Function.update c.2 ⟨n, hN⟩ u) c.1 m ∧
      keyAtP x N P rep (progP P (secretVal (x := x) n hN c) u E) c.2 c.1 m =
        keyAtP x N P (insert n rep) E (Function.update c.2 ⟨n, hN⟩ u) c.1 m := by
  set v := secretVal (x := x) n hN c
  set G := progP P v u E
  set R' := Function.update c.2 ⟨n, hN⟩ u
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hkey : keyAtP x N P rep G c.2 c.1 m = keyAtP x N P (insert n rep) E R' c.1 m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rfl
      · rw [keyAtP_pos (by omega), keyAtP_pos (by omega), (ih _ (by omega) (by omega)).1]
    refine ⟨?_, hkey⟩
    by_cases hmn : m = n
    · subst hmn
      have hv : keyAtP x N P (insert m rep) E R' c.1 m = v := by
        have h := keyAtP_secret (rep := insert m rep) hN
          (fun h0 => Finset.mem_insert_of_mem (hpar h0)) hPx E (c.1, R')
        rw [h]
        exact secretVal_update hN c u
      rw [rowAtP_of_not_mem hnr, rowAtP_of_mem (Finset.mem_insert_self _ _) hm, hkey, hv]
      simp only [R', G, Function.update_self]
      exact progP_self v u E
    · have hne : keyAtP x N P (insert n rep) E R' c.1 m ≠ v := hgood m hm hmn
      have hG : G (keyAtP x N P (insert n rep) E R' c.1 m) =
          E (keyAtP x N P (insert n rep) E R' c.1 m) := progP_ne hne u E
      by_cases hmr : m ∈ rep
      · rw [rowAtP_of_mem hmr hm, rowAtP_of_mem (Finset.mem_insert_of_mem hmr) hm, hkey, hG]
        simp only [R']
        rw [Function.update_of_ne (fun h => hmn (congrArg Fin.val h))]
      · have hmi : m ∉ insert n rep := by simp [hmn, hmr]
        rw [rowAtP_of_not_mem hmr, rowAtP_of_not_mem hmi, hkey, hG]

/-- With the root replaced on `P` (and every input in `P`), the root seed changes only the root's
row off `P`. -/
lemma rowAtP_seed_indep {rep : Finset ℕ} (h0 : 0 ∈ rep) (h0N : 0 < N) (hPx : ∀ m, P (x m))
    (E : K → X → K) (R : Fin N → X → K) (s s' : K) :
    (∀ z, P z → rowAtP x N P rep E R s 0 z = rowAtP x N P rep E R s' 0 z) ∧
    ∀ m, m ≠ 0 → rowAtP x N P rep E R s m = rowAtP x N P rep E R s' m ∧
      keyAtP x N P rep E R s m = keyAtP x N P rep E R s' m := by
  have hroot : ∀ z, P z → rowAtP x N P rep E R s 0 z = rowAtP x N P rep E R s' 0 z := by
    intro z hz
    rw [rowAtP_of_mem h0 h0N, rowAtP_of_mem h0 h0N, patchP_of_P hz, patchP_of_P hz]
  refine ⟨hroot, fun m => ?_⟩
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hkey : keyAtP x N P rep E R s m = keyAtP x N P rep E R s' m := by
      rw [keyAtP_pos hm, keyAtP_pos hm]
      by_cases hq : (m - 1) / 2 = 0
      · rw [hq]; exact hroot _ (hPx m)
      · rw [(ih _ (by omega) hq).1]
    refine ⟨?_, hkey⟩
    rw [rowAtP_eq, rowAtP_eq, hkey]

/-- With node `n` and its parent `p` replaced on `P` (and every input in `P`), changing `R p` at
`n`'s input changes `p`'s row there, `n`'s row off `P`, and nothing else. -/
lemma rowAtP_point_indep {rep : Finset ℕ} {n : ℕ} (hnr : n ∈ rep) (hN : n < N) (hn0 : n ≠ 0)
    (hp : (n - 1) / 2 ∈ rep)
    (hsib : ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n) (hPx : ∀ m, P (x m))
    (E : K → X → K) (R : Fin N → X → K) (seed : K) (k : K) :
    let R' := Function.update R ⟨(n - 1) / 2, by omega⟩
      (Function.update (R ⟨(n - 1) / 2, by omega⟩) (x n) k)
    ∀ m, (m ≠ n → keyAtP x N P rep E R' seed m = keyAtP x N P rep E R seed m) ∧
      (m ≠ (n - 1) / 2 → m ≠ n → rowAtP x N P rep E R' seed m = rowAtP x N P rep E R seed m) ∧
      (m = (n - 1) / 2 → rowAtP x N P rep E R' seed m =
        Function.update (rowAtP x N P rep E R seed m) (x n) k) ∧
      (m = n → ∀ z, P z → rowAtP x N P rep E R' seed m z = rowAtP x N P rep E R seed m z) := by
  intro R'
  have hpN : (n - 1) / 2 < N := by omega
  have hpn : (n - 1) / 2 ≠ n := by omega
  have hR'p : R' ⟨(n - 1) / 2, hpN⟩ = Function.update (R ⟨(n - 1) / 2, hpN⟩) (x n) k :=
    Function.update_self _ _ _
  have hR'ne : ∀ (m : ℕ) (hm : m < N), m ≠ (n - 1) / 2 → R' ⟨m, hm⟩ = R ⟨m, hm⟩ := fun m hm h =>
    Function.update_of_ne (fun e => h (congrArg Fin.val e)) _ _
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hkey : m ≠ n → keyAtP x N P rep E R' seed m = keyAtP x N P rep E R seed m := by
      intro hmn
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rfl
      rw [keyAtP_pos (by omega), keyAtP_pos (by omega)]
      have ihq := ih ((m - 1) / 2) (by omega)
      by_cases hq : (m - 1) / 2 = (n - 1) / 2
      · rw [ihq.2.2.1 hq, Function.update_of_ne (hsib m (by omega) hmn hq)]
      · by_cases hqn : (m - 1) / 2 = n
        · exact ihq.2.2.2 hqn _ (hPx m)
        · rw [ihq.2.1 hq hqn]
    refine ⟨hkey, fun hmp hmn => ?_, fun hmp => ?_, fun hmn z hz => ?_⟩
    · rw [rowAtP_eq, rowAtP_eq, hkey hmn]
      split_ifs with h
      · rw [hR'ne m h.2 hmp]
      · rfl
    · subst hmp
      rw [rowAtP_of_mem hp hpN, rowAtP_of_mem hp hpN, hkey hpn, hR'p]
      funext z
      by_cases hz : z = x n
      · subst hz; simp only [Function.update_self, patchP_of_P (hPx n)]
      · simp only [patchP, Function.update_of_ne hz]
    · subst hmn
      rw [rowAtP_of_mem hnr hN, rowAtP_of_mem hnr hN, patchP_of_P hz, patchP_of_P hz,
        hR'ne m hN hpn.symm]

/-! ### The bad event -/

variable (x N P) in
/-- **The candidates for the secret value of node `n`** in the experiment with `ins` replaced: the
values of the other nodes below `N` and the keys that `A` reads on `P`. -/
noncomputable def candsPt (ins : Finset ℕ) (n : ℕ) (Φ : (ℕ → X → K) → O)
    (Q : O → (K → X → K) → Finset (K × X)) (p : Coins K X N × (K → X → K)) : Finset K :=
  ((range N).filter (· ≠ n)).image (fun m => keyAtP x N P ins p.2 p.1.2 p.1.1 m) ∪
    qkeys P (Q (Φ (rowAtP x N P ins p.2 p.1.2 p.1.1)) p.2)

lemma candsPt_card (ins : Finset ℕ) (n : ℕ) (Φ : (ℕ → X → K) → O)
    (Q : O → (K → X → K) → Finset (K × X)) (p : Coins K X N × (K → X → K)) :
    ((candsPt x N P ins n Φ Q p).card : ℝ) ≤
      N + (qkeys P (Q (Φ (rowAtP x N P ins p.2 p.1.2 p.1.1)) p.2)).card := by
  have h : (candsPt x N P ins n Φ Q p).card ≤
      N + (qkeys P (Q (Φ (rowAtP x N P ins p.2 p.1.2 p.1.1)) p.2)).card := by
    unfold candsPt
    refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    exact card_image_le.trans ((card_filter_le _ _).trans (card_range N).le)
  exact_mod_cast h

/-- **The secret value is guessed with probability `≤ (N + E[#keys read on P]) / |K|`**, the
expectation in the experiment with `n` replaced. -/
lemma pr_secret_mem_candsPt {rep : Finset ℕ} {n : ℕ} (hN : n < N)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep)
    (hsib : n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (hPx : ∀ m, P (x m)) (Φ : (ℕ → X → K) → O)
    (hΦ : n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (hΦn : ∀ ρ r, (∀ z, P z → r z = ρ n z) → Φ (Function.update ρ n r) = Φ ρ)
    (Q : O → (K → X → K) → Finset (K × X)) :
    pr (Coins K X N × (K → X → K)) (fun p => secretVal (x := x) n hN p.1 ∈
      candsPt x N P (insert n rep) n Φ Q p) ≤
      (N + exP (Coins K X N × (K → X → K)) (fun p =>
        ((qkeys P (Q (Φ (rowAtP x N P (insert n rep) p.2 p.1.2 p.1.1)) p.2)).card : ℝ))) /
        Fintype.card K := by
  set ins := insert n rep
  have hin : n ∈ ins := Finset.mem_insert_self _ _
  have hexp : exP (Coins K X N × (K → X → K)) (fun p => ((candsPt x N P ins n Φ Q p).card : ℝ)) /
      Fintype.card K ≤ (N + exP (Coins K X N × (K → X → K)) (fun p =>
        ((qkeys P (Q (Φ (rowAtP x N P ins p.2 p.1.2 p.1.1)) p.2)).card : ℝ))) /
        Fintype.card K := by
    rw [← exP_const_add]
    exact div_le_div_of_nonneg_right (exP_mono fun p => candsPt_card ins n Φ Q p)
      (Nat.cast_nonneg _)
  refine le_trans ?_ hexp
  by_cases h0 : n = 0
  · subst h0
    refine (le_of_eq (pr_congr fun p => ?_)).trans (pr_mem_reset_exp
      (α := Coins K X N × (K → X → K)) (fun p => p.1.1) (fun p k => ((k, p.1.2), p.2))
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (candsPt x N P ins 0 Φ Q) fun p k => ?_)
    · simp only [secretVal, ↓reduceIte]
    · have hind := rowAtP_seed_indep (x := x) (P := P) hin hN hPx p.2 p.1.2 k p.1.1
      have hrows : rowAtP x N P ins p.2 p.1.2 k = Function.update
          (rowAtP x N P ins p.2 p.1.2 p.1.1) 0 (rowAtP x N P ins p.2 p.1.2 k 0) := by
        funext m
        by_cases hm : m = 0
        · subst hm; rw [Function.update_self]
        · rw [Function.update_of_ne hm, (hind.2 m hm).1]
      unfold candsPt
      congr 1
      · refine Finset.image_congr fun m hm => ?_
        exact (hind.2 m (Finset.mem_filter.1 hm).2).2
      · simp only
        rw [hrows, hΦn _ _ fun z hz => hind.1 z hz]
  · have hp : (n - 1) / 2 ∈ ins := Finset.mem_insert_of_mem (hpar h0)
    have hpN : (n - 1) / 2 < N := by omega
    have hpn : (n - 1) / 2 ≠ n := by omega
    let pf : Fin N := ⟨(n - 1) / 2, hpN⟩
    let st : Coins K X N × (K → X → K) → K → Coins K X N × (K → X → K) := fun p k =>
      ((p.1.1, Function.update p.1.2 pf (Function.update (p.1.2 pf) (x n) k)), p.2)
    have hf : ∀ p k, (st p k).1.2 pf (x n) = k := fun p k => by simp [st]
    have hss : ∀ p k k', st (st p k) k' = st p k' := fun p k k' => by simp [st]
    have hsf : ∀ p, st p (p.1.2 pf (x n)) = p := fun p => by simp [st]
    have hT : ∀ p k, candsPt x N P ins n Φ Q (st p k) = candsPt x N P ins n Φ Q p := by
      intro p k
      have hind := rowAtP_point_indep (x := x) (P := P) hin hN h0 hp (hsib h0) hPx p.2 p.1.2
        p.1.1 k
      unfold candsPt
      congr 1
      · refine Finset.image_congr fun m hm => ?_
        exact (hind m).1 (Finset.mem_filter.1 hm).2
      · simp only [st]
        set ρ := rowAtP x N P ins p.2 p.1.2 p.1.1
        set ρ' := rowAtP x N P ins p.2 (Function.update p.1.2 pf
          (Function.update (p.1.2 pf) (x n) k)) p.1.1
        have hρ : ρ' = Function.update (Function.update ρ ((n - 1) / 2)
            (Function.update (ρ ((n - 1) / 2)) (x n) k)) n (ρ' n) := by
          funext m
          by_cases hmn : m = n
          · subst hmn; rw [Function.update_self]
          · rw [Function.update_of_ne hmn]
            by_cases hm : m = (n - 1) / 2
            · subst hm; rw [Function.update_self]; exact (hind _).2.2.1 rfl
            · rw [Function.update_of_ne hm]; exact (hind m).2.1 hm hmn
        rw [hρ, hΦn _ _ fun z hz => by
          rw [Function.update_of_ne hpn.symm]; exact (hind n).2.2.2 rfl z hz, hΦ h0]
    refine (le_of_eq (pr_congr fun p => ?_)).trans (pr_mem_reset_exp
      (α := Coins K X N × (K → X → K)) (fun p => p.1.2 pf (x n)) st hf hss hsf
      (candsPt x N P ins n Φ Q) hT)
    simp only [secretVal, h0, ↓reduceIte]
    rfl

/-- **One hop at points**: replacing node `n` (its parent replaced, or the root) on `P` costs
`(N + E[#keys A reads on P]) / |K|`, the expectation in the experiment with `n` replaced. -/
theorem hopPt (rep : Finset ℕ) (n : ℕ) (hN : n < N) (hnr : n ∉ rep)
    (hpar : n ≠ 0 → (n - 1) / 2 ∈ rep)
    (hsib : n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (hPx : ∀ m, P (x m)) (Φ : (ℕ → X → K) → O)
    (hΦ : n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (hΦn : ∀ ρ r, (∀ z, P z → r z = ρ n z) → Φ (Function.update ρ n r) = Φ ρ)
    (hΦN : ∀ ρ ρ', (∀ m < N, ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → (K → X → K) → Prop) (Q : O → (K → X → K) → Finset (K × X))
    (hQ : ∀ o G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) → (A o G ↔ A o G')) :
    |experPt x N P rep Φ A - experPt x N P (insert n rep) Φ A| ≤
      (N + exP (Coins K X N × (K → X → K)) (fun p =>
        ((qkeys P (Q (Φ (rowAtP x N P (insert n rep) p.2 p.1.2 p.1.1)) p.2)).card : ℝ))) /
        Fintype.card K := by
  classical
  let v : Coins K X N → K := secretVal (x := x) n hN
  let ins := insert n rep
  have h1 : experPt x N P rep Φ A = pr (Coins K X N × ((K → X → K) × (Unit → X → K))) (fun p =>
      A (Φ (rowAtP x N P rep (progP P (v p.1) (p.2.2 ()) p.2.1) p.1.2 p.1.1))
        (progP P (v p.1) (p.2.2 ()) p.2.1)) :=
    pr_progP_eq (P := P) v (fun c g => A (Φ (rowAtP x N P rep g c.2 c.1)) g)
  let B : Coins K X N × ((K → X → K) × (Unit → X → K)) → Prop := fun p =>
    A (Φ (rowAtP x N P ins p.2.1 (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())) p.1.1)) p.2.1
  have h2 : pr _ B = experPt x N P ins Φ A := by
    have e := pr_equiv (swapRow (K := K) (X := X) hN)
      (fun p => A (Φ (rowAtP x N P ins p.2.1 p.1.2 p.1.1)) p.2.1)
    rw [pr_add_answers (fun p : Coins K X N × (K → X → K) =>
      A (Φ (rowAtP x N P ins p.2 p.1.2 p.1.1)) p.2)] at e
    exact e
  let bad : Coins K X N × ((K → X → K) × (Unit → X → K)) → Prop := fun p =>
    v p.1 ∈ candsPt x N P ins n Φ Q ((p.1.1, Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())), p.2.1)
  have h3 : pr _ bad ≤ (N + exP (Coins K X N × (K → X → K)) (fun p =>
        ((qkeys P (Q (Φ (rowAtP x N P ins p.2 p.1.2 p.1.1)) p.2)).card : ℝ))) /
        Fintype.card K := by
    have e := pr_equiv (swapRow (K := K) (X := X) hN)
      (fun p => v p.1 ∈ candsPt x N P ins n Φ Q (p.1, p.2.1))
    rw [pr_add_answers (fun p : Coins K X N × (K → X → K) =>
      v p.1 ∈ candsPt x N P ins n Φ Q p)] at e
    have e2 : pr _ bad = pr (Coins K X N × ((K → X → K) × (Unit → X → K)))
        (fun a => (fun p : Coins K X N × ((K → X → K) × (Unit → X → K)) =>
          v p.1 ∈ candsPt x N P ins n Φ Q (p.1, p.2.1)) (swapRow hN a)) :=
      pr_congr fun a => by
        show v a.1 ∈ _ ↔ v (a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())) ∈ _
        rw [show v (a.1.1, Function.update a.1.2 ⟨n, hN⟩ (a.2.2 ())) = v a.1 from
          secretVal_update hN a.1 _]
        rfl
    rw [e2, e]
    exact pr_secret_mem_candsPt hN hpar hsib hPx Φ hΦ hΦn Q
  have h4 : ∀ p, ¬ bad p → ((A (Φ (rowAtP x N P rep (progP P (v p.1) (p.2.2 ()) p.2.1)
      p.1.2 p.1.1)) (progP P (v p.1) (p.2.2 ()) p.2.1)) ↔ B p) := by
    intro p hp
    have hgood : ∀ m < N, m ≠ n → keyAtP x N P ins p.2.1
        (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())) p.1.1 m ≠ secretVal (x := x) n hN p.1 :=
      fun m hm hmn e => hp (by
        show v p.1 ∈ candsPt x N P ins n Φ Q _
        unfold candsPt
        exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨m, Finset.mem_filter.2
          ⟨Finset.mem_range.2 hm, hmn⟩, e⟩))
    have hrows := rowAtP_program hN hnr hpar hPx p.2.1 p.1 (p.2.2 ()) hgood
    rw [hΦN _ _ fun m hm => (hrows m hm).1]
    have hnq : v p.1 ∉ qkeys P (Q (Φ (rowAtP x N P ins p.2.1
        (Function.update p.1.2 ⟨n, hN⟩ (p.2.2 ())) p.1.1)) p.2.1) :=
      fun h => hp (Finset.mem_union_right _ h)
    refine (hQ _ _ _ fun kz hkz => ?_).symm
    by_cases hk : kz.1 = v p.1
    · have hPz : ¬ P kz.2 := fun hPz => hnq (Finset.mem_image.2
        ⟨kz, Finset.mem_filter.2 ⟨hkz, hPz⟩, hk⟩)
      rw [hk, progP_self]
      simp only [patchP, hPz, ↓reduceIte]
    · rw [progP_ne hk]
  rw [h1, ← h2]
  exact (abs_pr_sub_le_of_agree _ _ bad h4).trans h3

/-! ## The hybrid over the secret nodes -/

variable (x N P) in
/-- **The charge of the hop for node `j`**: `(N + E[#keys read on P]) / |K|`, the expectation in
the experiment with the secret nodes up to `j` replaced on `P`. -/
noncomputable def chgP (sec : ℕ → Prop) [DecidablePred sec] (Φ : (ℕ → X → K) → O)
    (Q : O → (K → X → K) → Finset (K × X)) (j : ℕ) : ℝ :=
  (N + exP (Coins K X N × (K → X → K)) (fun p =>
    ((qkeys P (Q (Φ (rowAtP x N P ((range (j + 1)).filter sec) p.2 p.1.2 p.1.1)) p.2)).card : ℝ))) /
    Fintype.card K

lemma chgP_nonneg (sec : ℕ → Prop) [DecidablePred sec] (Φ : (ℕ → X → K) → O)
    (Q : O → (K → X → K) → Finset (K × X)) (j : ℕ) : 0 ≤ chgP x N P sec Φ Q j :=
  div_nonneg (add_nonneg (Nat.cast_nonneg _) (exP_nonneg fun _ => Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

/-- **The hybrid over the secret nodes, at points**: for an upward-closed set `sec` of nodes,
replacing the rows of the secret nodes below `j` on `P` costs the sum of their hops' charges. -/
theorem puncturePt (sec : ℕ → Prop) [DecidablePred sec]
    (hup : ∀ n < N, sec n → n ≠ 0 → sec ((n - 1) / 2))
    (hsib : ∀ n < N, sec n → n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (hPx : ∀ m, P (x m)) (Φ : (ℕ → X → K) → O)
    (hΦ : ∀ n < N, sec n → n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (hΦP : ∀ ρ ρ', (∀ m < N, sec m → ∀ z, P z → ρ m z = ρ' m z) →
      (∀ m < N, ¬ sec m → ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → (K → X → K) → Prop) (Q : O → (K → X → K) → Finset (K × X))
    (hQ : ∀ o G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) → (A o G ↔ A o G')) :
    ∀ j ≤ N, |experPt x N P ∅ Φ A - experPt x N P ((range j).filter sec) Φ A| ≤
      ∑ i ∈ (range j).filter sec, chgP x N P sec Φ Q i := by
  have hΦN : ∀ ρ ρ', (∀ m < N, ρ m = ρ' m) → Φ ρ = Φ ρ' := fun ρ ρ' h =>
    hΦP ρ ρ' (fun m hm _ z _ => by rw [h m hm]) fun m hm _ => h m hm
  have hΦn : ∀ n < N, sec n → ∀ ρ r, (∀ z, P z → r z = ρ n z) →
      Φ (Function.update ρ n r) = Φ ρ := fun n hn _ ρ r hr =>
    hΦP _ _ (fun m _ _ z hz => by
      by_cases hmn : m = n
      · subst hmn; rw [Function.update_self, hr z hz]
      · rw [Function.update_of_ne hmn]) fun m _ hs => by
      by_cases hmn : m = n
      · subst hmn; exact absurd (by assumption) hs
      · rw [Function.update_of_ne hmn]
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have ih := ih (by omega)
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with hs
    · have hnot : j ∉ (range j).filter sec := by simp
      have h := hopPt (P := P) ((range j).filter sec) j (by omega) hnot (fun h0 =>
          Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hup j (by omega) hs h0⟩)
        (hsib j (by omega) hs) hPx Φ (hΦ j (by omega) hs) (hΦn j (by omega) hs) hΦN A Q hQ
      have hc : (N + exP (Coins K X N × (K → X → K)) (fun p =>
          ((qkeys P (Q (Φ (rowAtP x N P (insert j ((range j).filter sec)) p.2 p.1.2 p.1.1))
            p.2)).card : ℝ))) / Fintype.card K = chgP x N P sec Φ Q j := by
        rw [chgP, Finset.range_add_one, Finset.filter_insert]
        simp only [hs, ↓reduceIte]
      rw [Finset.sum_insert hnot, ← hc]
      have := abs_sub_le (experPt x N P ∅ Φ A) (experPt x N P ((range j).filter sec) Φ A)
        (experPt x N P (insert j ((range j).filter sec)) Φ A)
      linarith
    · exact ih

/-- **The hybrid at points, charged in the real experiment.** For a **consistent** reader `Q`
(`hQc`: its read set is determined by the values it reads) that reads at most `qm` keys on `P`
(`hqm`), with `|secret|·qm < |K|`:

    |real − fully replaced| ≤ |secret|·(N + E_real[#keys read on P]) / (|K| − |secret|·qm),

`E_real` the expectation in the real experiment (nothing replaced). -/
theorem puncturePt_real (sec : ℕ → Prop) [DecidablePred sec]
    (hup : ∀ n < N, sec n → n ≠ 0 → sec ((n - 1) / 2))
    (hsib : ∀ n < N, sec n → n ≠ 0 → ∀ m, m ≠ 0 → m ≠ n → (m - 1) / 2 = (n - 1) / 2 → x m ≠ x n)
    (hPx : ∀ m, P (x m)) (Φ : (ℕ → X → K) → O)
    (hΦ : ∀ n < N, sec n → n ≠ 0 → ∀ ρ y, Φ (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (x n) y)) = Φ ρ)
    (hΦP : ∀ ρ ρ', (∀ m < N, sec m → ∀ z, P z → ρ m z = ρ' m z) →
      (∀ m < N, ¬ sec m → ρ m = ρ' m) → Φ ρ = Φ ρ')
    (A : O → (K → X → K) → Prop) (Q : O → (K → X → K) → Finset (K × X))
    (hQ : ∀ o G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) → (A o G ↔ A o G'))
    (hQc : ∀ o G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) → Q o G = Q o G')
    {qm : ℕ} (hqm : ∀ o G, (qkeys P (Q o G)).card ≤ qm)
    (hsmall : ((range N).filter sec).card * (qm : ℝ) < Fintype.card K) :
    |exper x N ∅ Φ A - exper x N ((range N).filter sec) Φ A| ≤
      ((range N).filter sec).card * (N + exP (Coins K X N × (K → X → K)) (fun p =>
        ((qkeys P (Q (Φ (rowAt x N ∅ p.2 p.1.2 p.1.1)) p.2)).card : ℝ))) /
        (Fintype.card K - ((range N).filter sec).card * qm) := by
  set S := ∑ i ∈ (range N).filter sec, chgP x N P sec Φ Q i with hSdef
  set E0 := exP (Coins K X N × (K → X → K)) (fun p =>
    ((qkeys P (Q (Φ (rowAt x N ∅ p.2 p.1.2 p.1.1)) p.2)).card : ℝ))
  set s := ((range N).filter sec).card
  have hK : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hch := puncturePt sec hup hsib hPx Φ hΦ hΦP
  -- every level set of the charge is an event of the view
  have hlev : ∀ l : ℕ, ∀ o G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) →
      (l < (qkeys P (Q o G)).card ↔ l < (qkeys P (Q o G')).card) := fun l o G G' h => by
    rw [hQc o G G' h]
  -- each hop's charge is within `qm · S` of the real one
  have hE : ∀ i ∈ (range N).filter sec, chgP x N P sec Φ Q i ≤ (N + E0 + qm * S) / Fintype.card K := by
    intro i hi
    have hiN : i + 1 ≤ N := by have := Finset.mem_range.1 (Finset.mem_filter.1 hi).1; omega
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    have hlevels : ∀ l < qm, |pr (Coins K X N × (K → X → K)) (fun p => l <
          (qkeys P (Q (Φ (rowAtP x N P ((range (i + 1)).filter sec) p.2 p.1.2 p.1.1)) p.2)).card) -
        pr (Coins K X N × (K → X → K)) (fun p =>
          l < (qkeys P (Q (Φ (rowAt x N ∅ p.2 p.1.2 p.1.1)) p.2)).card)| ≤ S := by
      intro l _
      have h := hch (fun o G => l < (qkeys P (Q o G)).card) Q (hlev l) (i + 1) hiN
      rw [experPt_empty] at h
      rw [abs_sub_comm]
      refine h.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => chgP_nonneg _ _ _ _)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨by omega, hj.2⟩
    have h := exP_sub_le_of_levels _ _ (fun p => hqm _ _) (fun p => hqm _ _) hlevels
    have := (le_abs_self _).trans h
    linarith
  have hS : S ≤ s * ((N + E0 + qm * S) / Fintype.card K) := by
    calc S ≤ ∑ _i ∈ (range N).filter sec, (N + E0 + qm * S) / Fintype.card K :=
          Finset.sum_le_sum hE
      _ = s * ((N + E0 + qm * S) / Fintype.card K) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hden : 0 < (Fintype.card K : ℝ) - s * qm := by linarith
  have hS' : S ≤ s * (N + E0) / (Fintype.card K - s * qm) := by
    rw [le_div_iff₀ hden]
    rw [mul_div_assoc', le_div_iff₀ hK] at hS
    nlinarith
  have hfin := hch (A := A) Q hQ N le_rfl
  rw [experPt_empty, experPt_full sec hPx Φ hΦP] at hfin
  exact hfin.trans hS'

end HopP

end VoleMole.ZK.IC
