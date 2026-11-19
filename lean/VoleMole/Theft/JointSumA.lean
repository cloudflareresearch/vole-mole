import VoleMole.Theft.JointLeanSum
import VoleMole.Theft.JointSum

/-!
# The charges of the active slots summed

`real_sim_leN_leanA` (`Theft/JointLeanSum.lean`) charges a slot only if its instance is active
(the slot makes a proof). `exU_sum_nZK_le` (`Theft/JointSum.lean`) bounds the sum of all slots'
charges; there a slot with no `iv` is charged every key the game reader reads, so `U + M` refused
spends would cost `U + M` times the adversary's budget. Here only the **active** slots with no `iv`
(a failed simulation) pay that; an inactive slot costs only `2N·h` through the overlaps of the
others (it has no `iv`, so it may overlap any):

* `sum_cEofA_le`, `sum_c5ofA_le`: the own charges of the active slots;
* **`sum_nZKA_le`**: the weighted counts `nZKA` of all slots in a view;
* **`exU_sum_nZKA_le`**: their expectation over a tape whose `iv`s are blocks of a uniform table at
  inputs that do not read it:

      Σ_i Σ_k w k · E[nZKA i k] ≤ w₀·T₃ + w₁·c_E + w₂·a₅
        + (w₁·(c_E + 2h_E) + w₂·(a₅ + 2h₅))·(N²·2⁻⁶⁴ + E[#dupPairs d])
        + (w₁·a_E + w₂·a₅)·E[#active slots with no iv]
        + 2N·(w₁·h_E + w₂·h₅)·E[#slots with no iv].
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK.IC VoleMole.Verifier VoleMole.Verifier.Bridge

section Count

variable {N : ℕ}

/-- The number of active slots with no `iv`. -/
noncomputable def nNoneA (act : ℕ → Prop) [DecidablePred act] (iv : ℕ → Option ByteArray)
    (N : ℕ) : ℕ :=
  ((range N).filter fun j => act j ∧ iv j = none).card

lemma ind_noneA_sum (act : ℕ → Prop) [DecidablePred act] (iv : ℕ → Option ByteArray) :
    ∑ i ∈ range N, (if act i ∧ iv i = none then 1 else 0) = nNoneA act iv N := by
  rw [Finset.sum_boole]; rfl

/-- **The cipher charges of the active slots.** -/
theorem sum_cEofA_le (act : ℕ → Prop) [DecidablePred act] (iv : ℕ → Option ByteArray)
    (g : Fin N → Bytes 16) (hiv : IvsOf iv g) (Q : Finset (Blk × Blk)) :
    ∑ i ∈ range N, (if act i then cEof (iv i) Q else 0) ≤
      (ptCls Q).card * (1 + (collPairs g).card) + nNoneA act iv N * (Q.image Prod.fst).card := by
  classical
  have hpt : ∀ i : Fin N, (if act i then cEof (iv i) Q else 0) ≤ (qkeys (InY (ba (g i))) Q).card +
      (if act i ∧ iv i = none then 1 else 0) * (Q.image Prod.fst).card := by
    intro i
    by_cases ha : act i
    · rcases hiv i with h | h
      · rw [h]; simp [cEof, ha]
      · rw [h]; simp [cEof, ha]
    · simp [ha]
  calc ∑ i ∈ range N, (if act i then cEof (iv i) Q else 0) =
        ∑ i : Fin N, (if act i then cEof (iv i) Q else 0) :=
        (Fin.sum_univ_eq_sum_range (fun i => if act i then cEof (iv i) Q else 0) N).symm
    _ ≤ ∑ i : Fin N, ((qkeys (InY (ba (g i))) Q).card +
          (if act i ∧ iv i = none then 1 else 0) * (Q.image Prod.fst).card) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = ∑ i : Fin N, (qkeys (InY (ba (g i))) Q).card +
          (∑ i : Fin N, (if act i ∧ iv i = none then 1 else 0)) * (Q.image Prod.fst).card := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (ptCls Q).card * (1 + (collPairs g).card) + nNoneA act iv N * (Q.image Prod.fst).card := by
        refine add_le_add (sum_qkeys_inY_le g Q) (le_of_eq ?_)
        rw [Fin.sum_univ_eq_sum_range (fun i => if act i ∧ iv i = none then 1 else 0) N,
          ind_noneA_sum]

/-- **The `H₅` charges of the active slots.** -/
theorem sum_c5ofA_le (p : Params) (act : ℕ → Prop) [DecidablePred act] (iv : ℕ → Option ByteArray)
    (g : Fin N → Bytes 16) (hiv : IvsOf iv g) (Q5 : Finset (Bytes 37)) :
    ∑ i ∈ range N, (if act i then c5of p CrtGen.tables (iv i) Q5 else 0) ≤
      Q5.card * (1 + (collPairs g).card) + nNoneA act iv N * Q5.card := by
  classical
  -- the slots: active ones keep their `iv`, the others get a block
  set iv' : ℕ → Option ByteArray := fun i =>
    if h : i < N then (if act i then iv i else some (ba (g ⟨i, h⟩))) else none with hiv'
  have hiv'' : IvsOf iv' g := by
    intro j
    simp only [iv', j.isLt, ↓reduceDIte]
    by_cases ha : act j
    · simp only [ha, ↓reduceIte]; exact hiv j
    · simp only [ha, ↓reduceIte]; simp
  have hle : ∀ i ∈ range N, (if act i then c5of p CrtGen.tables (iv i) Q5 else 0) ≤
      c5of p CrtGen.tables (iv' i) Q5 := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    simp only [iv', hi', ↓reduceDIte]
    by_cases ha : act i <;> simp [ha]
  have hnn : nNone iv' N = nNoneA act iv N := by
    unfold nNone nNoneA
    congr 1
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    simp only [iv', hi', ↓reduceDIte]
    by_cases ha : act i <;> simp [ha]
  refine (Finset.sum_le_sum hle).trans ?_
  have := sum_c5of_le p iv' g hiv'' Q5
  rw [hnn] at this
  exact this

end Count

/-! ## The weighted counts of the active slots -/

section Sum

variable {X : Type} {I O Ω : Type*} {p : Params} {N : ℕ}

/-- The active slots of a view. -/
def actAt (act : I → Prop) (xOf : Ω → List O → I) (v : Ω × List O × (Fin N → Tab3) ×
    ShX (Blk → Blk) p X) (i : ℕ) : Prop :=
  act (xOf v.1 (v.2.1.take i))

instance (act : I → Prop) [DecidablePred act] (xOf : Ω → List O → I)
    (v : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X) : DecidablePred (actAt act xOf v) :=
  fun i => inferInstanceAs (Decidable (act (xOf v.1 (v.2.1.take i))))

/-- **The weighted counts of the active slots in a view.** -/
theorem sum_nZKA_le (act : I → Prop) [DecidablePred act] (ivO : X → I → O → Option ByteArray)
    (xOf : Ω → List O → I) (R : GRd Ω O p X N) {a3 a5 aE : ℕ} (hb : R.Bnd a3 a5 aE) {T3 cE : ℕ}
    (hT3 : ∀ ω l gs t, ∑ j, (R.Q3 ω l gs t j).card ≤ T3)
    (hcls : ∀ ω l gs t, (ptCls (R.QE ω l gs t)).card ≤ cE) (h5 hE : ℕ) (w : Fin 3 → ℝ)
    (hw : ∀ k, 0 ≤ w k) (v : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X)
    (g : Fin N → Bytes 16) (hiv : IvsOf (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1) g) :
    ∑ i ∈ range N, ∑ k, w k * (nZKA act ivO xOf R h5 hE i k v : ℝ) ≤
      w 0 * T3 + w 1 * (cE + aE * nNoneA (actAt act xOf v) (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1) N +
          2 * N * hE * nNone (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1) N) +
        w 2 * (a5 + a5 * nNoneA (actAt act xOf v) (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1) N +
          2 * N * h5 * nNone (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1) N) +
        (w 1 * (cE + 2 * hE) + w 2 * (a5 + 2 * h5)) * (collPairs g).card := by
  classical
  set iv := ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1
  set nn := nNone iv N with hnn
  set na := nNoneA (actAt act xOf v) iv N with hna
  set cp := (collPairs g).card with hcp
  set Q := R.QE v.1 v.2.1 v.2.2.1 v.2.2.2
  set Q5 := R.Q5 v.1 v.2.1 v.2.2.1 v.2.2.2
  have eA : ∀ i k, nZKA act ivO xOf R h5 hE i k v =
      if actAt act xOf v i then nZK p ivO xOf R h5 hE i k v else 0 := fun _ _ => by
    unfold nZKA actAt; rfl
  have s3 : ∑ i ∈ range N, (if actAt act xOf v i then n3 R i v else 0) ≤ T3 := by
    refine (Finset.sum_le_sum fun i _ => (by split_ifs <;> omega :
      (if actAt act xOf v i then n3 R i v else 0) ≤ n3 R i v)).trans ?_
    have e : ∑ i ∈ range N, n3 R i v = ∑ j : Fin N, (R.Q3 v.1 v.2.1 v.2.2.1 v.2.2.2 j).card := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => n3 R i v) N]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [n3, j.isLt, ↓reduceDIte]
    rw [e]; exact hT3 _ _ _ _
  have sE : ∑ i ∈ range N, (if actAt act xOf v i then nE ivO (xOf := xOf) R hE i v else 0) ≤
      cE * (1 + cp) + na * aE + hE * (2 * cp + 2 * N * nn) := by
    have e1 : ∀ i, (if actAt act xOf v i then nE ivO (xOf := xOf) R hE i v else 0) ≤
        (if actAt act xOf v i then cEof (iv i) Q else 0) +
          hE * ∑ j ∈ (range N).erase i, ovE (iv i) (iv j) := by
      intro i
      split_ifs
      · simp only [nE, Finset.mul_sum]; exact le_rfl
      · exact Nat.zero_le _
    refine (Finset.sum_le_sum fun i _ => e1 i).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := sum_cEofA_le (actAt act xOf v) iv g hiv Q
    have h2 := sum_ovE_le iv g hiv
    simp only [← hcp, ← hnn, ← hna] at h1 h2
    have h3 : (ptCls Q).card * (1 + cp) ≤ cE * (1 + cp) := Nat.mul_le_mul_right _ (hcls _ _ _ _)
    have h4 : na * (Q.image Prod.fst).card ≤ na * aE := Nat.mul_le_mul_left _ (hb.hE _ _ _ _)
    have h5' := Nat.mul_le_mul_left hE h2
    omega
  have s5 : ∑ i ∈ range N, (if actAt act xOf v i then n5 ivO (xOf := xOf) R h5 i v else 0) ≤
      a5 * (1 + cp) + na * a5 + h5 * (2 * cp + 2 * N * nn) := by
    have e1 : ∀ i, (if actAt act xOf v i then n5 ivO (xOf := xOf) R h5 i v else 0) ≤
        (if actAt act xOf v i then c5of p CrtGen.tables (iv i) Q5 else 0) +
          h5 * ∑ j ∈ (range N).erase i, ov5 (iv i) (iv j) := by
      intro i
      split_ifs
      · simp only [n5, Finset.mul_sum]; exact le_rfl
      · exact Nat.zero_le _
    refine (Finset.sum_le_sum fun i _ => e1 i).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := sum_c5ofA_le p (actAt act xOf v) iv g hiv Q5
    have h2 := sum_ov5_le iv g hiv
    simp only [← hcp, ← hnn, ← hna] at h1 h2
    have h3 : Q5.card * (1 + cp) ≤ a5 * (1 + cp) := Nat.mul_le_mul_right _ (hb.h5 _ _ _ _)
    have h4 : na * Q5.card ≤ na * a5 := Nat.mul_le_mul_left _ (hb.h5 _ _ _ _)
    have h5' := Nat.mul_le_mul_left h5 h2
    omega
  have e : ∑ i ∈ range N, ∑ k, w k * (nZKA act ivO xOf R h5 hE i k v : ℝ) =
      w 0 * (∑ i ∈ range N, (if actAt act xOf v i then n3 R i v else 0) : ℕ) +
        w 1 * (∑ i ∈ range N, (if actAt act xOf v i then nE ivO (xOf := xOf) R hE i v else 0) : ℕ) +
        w 2 * (∑ i ∈ range N, (if actAt act xOf v i then n5 ivO (xOf := xOf) R h5 i v else 0) : ℕ) := by
    simp only [eA, Fin.sum_univ_three, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases ha : actAt act xOf v i
    · simp only [ha, ↓reduceIte, nZK, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · simp only [ha, ↓reduceIte, Nat.cast_zero, mul_zero, add_zero]
  rw [e]
  have r3 : ((∑ i ∈ range N, (if actAt act xOf v i then n3 R i v else 0) : ℕ) : ℝ) ≤ T3 := by
    exact_mod_cast s3
  have rE : ((∑ i ∈ range N, (if actAt act xOf v i then nE ivO (xOf := xOf) R hE i v else 0) : ℕ) :
      ℝ) ≤ cE * (1 + cp) + na * aE + hE * (2 * cp + 2 * N * nn) := by exact_mod_cast sE
  have r5 : ((∑ i ∈ range N, (if actAt act xOf v i then n5 ivO (xOf := xOf) R h5 i v else 0) : ℕ) :
      ℝ) ≤ a5 * (1 + cp) + na * a5 + h5 * (2 * cp + 2 * N * nn) := by exact_mod_cast s5
  have := mul_le_mul_of_nonneg_left r3 (hw 0)
  have := mul_le_mul_of_nonneg_left rE (hw 1)
  have := mul_le_mul_of_nonneg_left r5 (hw 2)
  nlinarith

/-- **The expected weighted counts of the active slots**, for views on a tape
`Z ≃ Ω' × (D → Bytes 16)` whose `iv`s are the table's blocks at inputs `d ω'` (or absent). -/
theorem exU_sum_nZKA_le (act : I → Prop) [DecidablePred act] (ivO : X → I → O → Option ByteArray)
    (xOf : Ω → List O → I) (R : GRd Ω O p X N) {a3 a5 aE : ℕ} (hb : R.Bnd a3 a5 aE) {T3 cE : ℕ}
    (hT3 : ∀ ω l gs t, ∑ j, (R.Q3 ω l gs t j).card ≤ T3)
    (hcls : ∀ ω l gs t, (ptCls (R.QE ω l gs t)).card ≤ cE) (h5 hE : ℕ) (w : Fin 3 → ℝ)
    (hw : ∀ k, 0 ≤ w k) {Z Ω' D : Type*} [Fintype Z] [Nonempty Z] [Fintype Ω'] [Nonempty Ω']
    [Fintype D] [DecidableEq D] (view : Z → Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X)
    (e : Z ≃ Ω' × (D → Bytes 16)) (d : Ω' → Fin N → D)
    (hiv : ∀ z, IvsOf (ivAt ivO xOf (view z).2.2.2.2.2 (view z).1 (view z).2.1)
      (fun j => (e z).2 (d (e z).1 j))) :
    ∑ i ∈ range N, ∑ k, w k * exU Z (fun z => (nZKA act ivO xOf R h5 hE i k (view z) : ℝ)) ≤
      w 0 * T3 + w 1 * cE + w 2 * a5 +
        (w 1 * (cE + 2 * hE) + w 2 * (a5 + 2 * h5)) *
          ((N : ℝ) ^ 2 / 2 ^ 64 + exP Ω' (fun ω' => ((dupPairs (d ω')).card : ℝ))) +
        (w 1 * aE + w 2 * a5) * exU Z (fun z => (nNoneA (actAt act xOf (view z))
          (ivAt ivO xOf (view z).2.2.2.2.2 (view z).1 (view z).2.1) N : ℝ)) +
        2 * N * (w 1 * hE + w 2 * h5) *
          exU Z (fun z => (nNone (ivAt ivO xOf (view z).2.2.2.2.2 (view z).1 (view z).2.1) N : ℝ)) := by
  set A := w 1 * (cE + 2 * hE) + w 2 * (a5 + 2 * h5)
  have hA : 0 ≤ A := by have := hw 1; have := hw 2; positivity
  have e1 : ∑ i ∈ range N, ∑ k, w k * exU Z (fun z => (nZKA act ivO xOf R h5 hE i k (view z) : ℝ)) =
      exU Z (fun z => ∑ i ∈ range N, ∑ k, w k * (nZKA act ivO xOf R h5 hE i k (view z) : ℝ)) := by
    rw [exU_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [exU_sum]
    exact Finset.sum_congr rfl fun k _ => (exU_mul_left _ _).symm
  rw [e1]
  have hpt : ∀ z, ∑ i ∈ range N, ∑ k, w k * (nZKA act ivO xOf R h5 hE i k (view z) : ℝ) ≤
      (w 0 * T3 + w 1 * cE + w 2 * a5) +
        A * ((collPairs (fun j => (e z).2 (d (e z).1 j))).card : ℝ) +
        (w 1 * aE + w 2 * a5) * (nNoneA (actAt act xOf (view z))
          (ivAt ivO xOf (view z).2.2.2.2.2 (view z).1 (view z).2.1) N : ℝ) +
        2 * N * (w 1 * hE + w 2 * h5) *
          (nNone (ivAt ivO xOf (view z).2.2.2.2.2 (view z).1 (view z).2.1) N : ℝ) := by
    intro z
    have := sum_nZKA_le act ivO xOf R hb hT3 hcls h5 hE w hw (view z) _ (hiv z)
    simp only [A]
    nlinarith
  refine (exP_mono hpt).trans ?_
  rw [exP_add, exP_add, exP_add, exP_const, exP_mul_left, exP_mul_left, exP_mul_left]
  have hcp : exP Z (fun z => ((collPairs (fun j => (e z).2 (d (e z).1 j))).card : ℝ)) ≤
      (N : ℝ) ^ 2 / 2 ^ 64 + exP Ω' (fun ω' => ((dupPairs (d ω')).card : ℝ)) := by
    have e2 : exP Z (fun z => ((collPairs (fun j => (e z).2 (d (e z).1 j))).card : ℝ)) =
        exP (Ω' × (D → Bytes 16)) (fun y => ((collPairs (fun j => y.2 (d y.1 j))).card : ℝ)) :=
      exP_equiv e (fun y => ((collPairs (fun j => y.2 (d y.1 j))).card : ℝ))
    rw [e2, exP_prod]
    refine (exP_mono fun ω' => exP_collPairs_tab_le (d ω')).trans (le_of_eq ?_)
    rw [exP_const_add]
  have := mul_le_mul_of_nonneg_left hcp hA
  show _ + _ + (w 1 * aE + w 2 * a5) * exU Z _ + 2 * N * (w 1 * hE + w 2 * h5) * exU Z _ ≤ _
  linarith

end Sum

end VoleMole.Theft
