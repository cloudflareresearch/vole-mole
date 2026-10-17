import VoleMole.ZK.TwoPhaseAd
import VoleMole.ZK.SharedH3

/-!
# One shared `H₃` for the two-phase prover (PomFRIT)

`ZK/SharedH3.lean` for the two-phase run of `ZK/TwoPhaseReadsRO.lean` (`realRO2`, `simRO2`,
`progRO2`):

* **What step 1 reads.** `step1_h3_congr`, `realRun2_h3_congr`: the two-phase run reads `H₃` only at
  its seed input; `realRO2_g3_congr'`, `step1_g3_congr'`: with the record of the random-oracle
  model, only its slice at `ρ`, for every `r` and continuation.
* **`ZK2ARow.rowH`**: `ZK2ARow R` (two-phase zero knowledge with a continuation that reads the
  proof's slice and the shared tables, `zk2_adaptive`) for the tables with `H₃`'s columns in the
  rows, by averaging over the columns.
* **`zk2_shared`**: the two-phase prover that reads its slice off the shared tables at the prefix
  `k`, against a distinguisher blind to its slice argument (the game's), is close to the
  simulator with the error of `ZK2ARow` at `(q_E + qkE, q₅ + qk5, q_E + qkE)`. The continuation
  may read the shared tables anywhere, the prover's column included (in PomFRIT: the other
  session's step 1, when the two sessions' prefixes coincide), which is why the adaptive
  two-phase theorem is used: after the column is re-sampled, a continuation that read it reads
  the proof's own slice.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy

/-! ## Step 1 reads `H₃` only at its seed input -/

section Step1

variable [HasPrg] {Hs Hs' : Hashes}

lemma voleGen_h3_congr (h : Hs.AgreeOff .h3 Hs') (T : CrtTables) (p : Params)
    (mu1 wPrefix rho binder1 : ByteArray)
    (hx : Hs.hash .h3 ((wPrefix ++ mu1 ++ rho).push 3) = Hs'.hash .h3 ((wPrefix ++ mu1 ++ rho).push 3)) :
    Prover.voleGen Hs T p mu1 wPrefix rho binder1 = Prover.voleGen Hs' T p mu1 wPrefix rho binder1 := by
  rw [voleGen_eq_voleGenAt, voleGen_eq_voleGenAt, hx, voleGenAt_agreeOff_h3 h]

/-- **Step 1 reads `H₃` only at its seed input.** -/
lemma step1_h3_congr (h : Hs.AgreeOff .h3 Hs') (T : CrtTables) (st : Statement) (r rho : ByteArray)
    (hx : Hs.hash .h3 ((r ++ mu Hs none st.dst ++ rho).push 3) =
      Hs'.hash .h3 ((r ++ mu Hs none st.dst ++ rho).push 3)) :
    step1 Hs T st r rho = step1 Hs' T st r rho := by
  have hm : mu Hs' none st.dst = mu Hs none st.dst := by
    simp only [mu, h .muDelayed (by decide)]
  unfold step1
  rw [hm]
  exact voleGen_h3_congr h T st.params _ r rho st.binder1 hx

/-- **The two-phase run reads `H₃` only at its seed input.** -/
lemma realRun2_h3_congr (h : Hs.AgreeOff .h3 Hs') (T : CrtTables) (st : Statement) (r : ByteArray)
    (k : Cont2) (rho : ByteArray)
    (hx : Hs.hash .h3 ((r ++ mu Hs none st.dst ++ rho).push 3) =
      Hs'.hash .h3 ((r ++ mu Hs none st.dst ++ rho).push 3)) :
    realRun2 Hs T st r k rho = realRun2 Hs' T st r k rho := by
  unfold realRun2
  rw [step1_h3_congr h T st r rho hx]
  simp only [proveCommit_agreeOff_h3 h]

end Step1

/-- Two seed inputs with the same last `17` bytes' shape have the same `ρ`. -/
lemma eq_of_seed_eq {X Y : ByteArray} {a b : Bytes 16} (h : (X ++ ba a).push 3 = (Y ++ ba b).push 3) :
    a = b := by
  have h1 : X ++ ba a = Y ++ ba b := push_injective 3 h
  have h2 : X.data.toList ++ (ba a).data.toList = Y.data.toList ++ (ba b).data.toList := by
    have := congrArg (fun z : ByteArray => z.data.toList) h1
    simpa [ByteArray.data_append] using this
  have hl : (ba a).data.toList.length = (ba b).data.toList.length := by
    simp only [Array.length_toList]
    exact (size_ba a).trans (size_ba b).symm
  have h3 := (List.append_inj' h2 hl).2
  apply ba_injective
  exact ByteArray.ext (Array.ext' h3)

section RealH3

variable {R : Type} [CipherRow R] {Hb : Hashes} {st : Statement} {r : ByteArray}

/-- The `H₃` answer at step 1's seed input reads the slice only at `ρ`. -/
lemma recH_h3_step1 (ρ : Bytes 16) {G3 G3' : Tab3} (G2 : Tab2G st.params) (G5 : Tab5F)
    (h : G3 ρ = G3' ρ) :
    (recH Hb (st1 st) r G3 G2 G5).hash .h3
        ((r ++ mu (recH Hb (st1 st) r G3 G2 G5) none st.dst ++ ba ρ).push 3) =
      (recH Hb (st1 st) r G3' G2 G5).hash .h3
        ((r ++ mu (recH Hb (st1 st) r G3 G2 G5) none st.dst ++ ba ρ).push 3) := by
  rw [← recHp_eq, recHp_h3, recHp_h3]
  refine withTable_h3_congr _ _ _ fun a ha => ?_
  rw [eq_of_seed_eq ha, h]

/-- **Step 1 on the record of the random-oracle model reads its slice only at `ρ`**, for every `r`. -/
theorem step1_g3_congr' (ρ : Bytes 16) {G3 G3' : Tab3} (s : ShG R st.params) (h : G3 ρ = G3' ρ) :
    @step1 (icPrg (rowFn s.2.2)) (recH Hb (st1 st) r G3 s.1 s.2.1) CrtGen.tables st r (ba ρ) =
      @step1 (icPrg (rowFn s.2.2)) (recH Hb (st1 st) r G3' s.1 s.2.1) CrtGen.tables st r (ba ρ) :=
  @step1_h3_congr (icPrg (rowFn s.2.2)) _ _ (recH_agreeOff_h3 (Hb := Hb) (st := st1 st) (w := r) G3 G3' s.1 s.2.1) _ _ _ _
    (recH_h3_step1 ρ s.1 s.2.1 h)

/-- **The two-phase run reads its slice only at `ρ`**, for every `r` and continuation. -/
theorem realRO2_g3_congr' (K : ShG R st.params → Cont2) (ρ : Bytes 16) {G3 G3' : Tab3}
    (s : ShG R st.params) (h : G3 ρ = G3' ρ) :
    realRO2 Hb st r K ρ G3 s = realRO2 Hb st r K ρ G3' s :=
  @realRun2_h3_congr (icPrg (rowFn s.2.2)) _ _ (recH_agreeOff_h3 (Hb := Hb) (st := st1 st) (w := r) G3 G3' s.1 s.2.1) _ _ _ _ _
    (recH_h3_step1 ρ s.1 s.2.1 h)

end RealH3

/-! ## The two-phase runs and the `H₃` columns -/

section Blind

variable {R : Type} [CipherRow R] (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ)

lemma realRO2_setK (K : ShG (RowH R) st.params → Cont2) (ρ : Bytes 16) (G3 : Tab3)
    (s : ShG (RowH R) st.params) (k : Pre) (g : Tab3) :
    realRO2 Hb st r K ρ G3 (setK s k g) = realRO2 Hb st r (fun s' => K (setK s' k g)) ρ G3 s := rfl

lemma simRO2_setK (K : ShG (RowH R) st.params → Cont2) (c : SimCoins2 st.params)
    (s : ShG (RowH R) st.params) (k : Pre) (g : Tab3) :
    simRO2 Hb st n K c (setK s k g) = simRO2 Hb st n (fun s' => K (setK s' k g)) c s := rfl

lemma progRO2_setK (K : ShG (RowH R) st.params → Cont2) (c : SimCoins2 st.params)
    (s : ShG (RowH R) st.params) (k : Pre) (g : Tab3) :
    progRO2 Hb st n K c (setK s k g) = setK (progRO2 Hb st n (fun s' => K (setK s' k g)) c s) k g :=
  rfl

@[simp] lemma h3At_progRO2 (K : ShG (RowH R) st.params → Cont2) (c : SimCoins2 st.params)
    (s : ShG (RowH R) st.params) (k : Pre) : h3At (progRO2 Hb st n K c s) k = h3At s k := rfl

lemma realRO2_combH (K : ShG (RowH R) st.params → Cont2) (ρ : Bytes 16) (G3 : Tab3)
    (s : ShG R st.params) (H : Blk → H3Row) :
    realRO2 Hb st r K ρ G3 (combH s H) = realRO2 Hb st r (fun s' => K (combH s' H)) ρ G3 s := rfl

lemma simRO2_combH (K : ShG (RowH R) st.params → Cont2) (c : SimCoins2 st.params)
    (s : ShG R st.params) (H : Blk → H3Row) :
    simRO2 Hb st n K c (combH s H) = simRO2 Hb st n (fun s' => K (combH s' H)) c s := rfl

lemma progRO2_combH (K : ShG (RowH R) st.params → Cont2) (c : SimCoins2 st.params)
    (s : ShG R st.params) (H : Blk → H3Row) :
    progRO2 Hb st n K c (combH s H) = combH (progRO2 Hb st n (fun s' => K (combH s' H)) c s) H := rfl

end Blind

/-! ## Two-phase zero knowledge with the `H₃` columns in the rows -/

section RowH

variable {R : Type} [Fintype R] [CipherRow R] {p : Params}

variable {X : Sort*} in
lemma rd5_combH {f : ShG (RowH R) p → X} {q : ℕ} (hf : Rd5 f q) (H : Blk → H3Row) :
    Rd5 (fun s => f (combH s H)) q := by
  obtain ⟨Q, hQc, hQ⟩ := hf
  exact ⟨fun s => Q (combH s H), fun s => hQc _, fun s G5 h => hQ (combH s H) G5 h⟩

variable {X : Sort*} in
lemma rdE_combH {f : ShG (RowH R) p → X} {q : ℕ} (hf : RdE f q) (H : Blk → H3Row) :
    RdE (fun s => f (combH s H)) q := by
  obtain ⟨Q, hQc, hQ⟩ := hf
  refine ⟨fun s => Q (combH s H), fun s => hQc _, fun s E h => ?_⟩
  exact hQ (combH s H) (fun j => (E j, H j)) fun j hj => by
    simp only [combH, splitH, Equiv.coe_fn_symm_mk]
    rw [h j hj]

variable [ZKRow R] [ZK2ARow R]

/-- **Two-phase zero knowledge (adaptive continuation) with the `H₃` columns in the rows**:
`ZK2ARow R`'s theorem, averaged over the columns. -/
noncomputable instance ZK2ARow.rowH : ZK2ARow (RowH R) where
  zk2A Hb st r n K qk3 qk5 qkE hh hHb hp q3 q5 qE D hD := by
    let e1 : (Blk → H3Row) × ((Bytes 16 × Tab3) × ShG R st.params) ≃
        (Bytes 16 × Tab3) × ShG (RowH R) st.params :=
      { toFun := fun b => (b.2.1, combH b.2.2 b.1)
        invFun := fun a => ((splitH a.2).1, (a.1, (splitH a.2).2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let e2 : (Blk → H3Row) × ((SimCoins2 st.params × Tab3) × ShG R st.params) ≃
        (SimCoins2 st.params × Tab3) × ShG (RowH R) st.params :=
      { toFun := fun b => (b.2.1, combH b.2.2 b.1)
        invFun := fun a => ((splitH a.2).1, (a.1, (splitH a.2).2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e1, ← pr_equiv e2]
    refine abs_pr_prod_sub_le _ _ fun H => ?_
    have hh' : Hyp2RA st r n (fun g s => K g (combH s H)) qk3 qk5 qkE :=
      ⟨fun g s => hh.hyp g (combH s H), hh.size, fun g s G2 => hh.h2 g (combH s H) G2,
        fun o1 s => hh.h3 o1 (combH s H), fun o1 g => rd5_combH (hh.h5 o1 g) H,
        fun o1 g => rdE_combH (hh.hE o1 g) H⟩
    exact ZK2ARow.zk2A (R := R) Hb st r n (fun g s => K g (combH s H)) hh' hHb hp
      (fun o G s => D o G (combH s H)) (hD.withH H)

end RowH

/-! ## Two-phase zero knowledge for a prover that reads its slice off the shared tables -/

section Shared

variable {R : Type} [Fintype R] [CipherRow R] [ZKRow R] [ZK2ARow R]

/-- **Two-phase zero knowledge with one shared `H₃`**, the continuation's budgets at each step-1
output (as `Hyp2RA`'s). The real two-phase run reads its slice off
the shared tables at its prefix `k`; its continuation `K` reads the shared tables (`Rd5 K qk5`,
`RdE K qkE`, possibly the column at `k`), the distinguisher's slice argument is not the prover's
(the game's own). Then the real and simulated experiments are close with the error of
`ZK2ARow` at `(q_E + qkE, q₅ + qk5, q_E + qkE)`. -/
theorem zk2_sharedA (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ) (k : Pre)
    (K : ShG (RowH R) st.params → Cont2) {qk5 qkE : ℕ} (hhyp : ∀ s, Hyp2 st r (K s))
    (hsize : r.size = n) (h2 : ∀ (s : ShG (RowH R) st.params) G2, K (G2, s.2) = K s)
    (h5 : ∀ o1, Rd5 (fun s => K s o1) qk5) (hE : ∀ o1, RdE (fun s => K s o1) qkE) (hHb : HashesWF Hb)
    (hp : SmallParams st.params)
    {q3 q5 qE : ℕ} (D : Out2 → Tab3 → ShG (RowH R) st.params → Prop)
    (hD : Budget st.params q3 q5 qE D) :
    |pr ((Bytes 16 × Tab3) × ShG (RowH R) st.params) (fun a =>
        D (realRO2 Hb st r K a.1.1 (h3At a.2 k) a.2) a.1.2 a.2) -
      pr ((SimCoins2 st.params × Tab3) × ShG (RowH R) st.params) (fun a =>
        D (simRO2 Hb st n K a.1.1 a.2) a.1.2 (progRO2 Hb st n K a.1.1 a.2))| ≤
      ZKRow.εz R st.params (qE + qkE) (q5 + qk5) (qE + qkE) := by
  have hh' : Hyp2RA st r n (fun G s => K (setK s k G)) qkE qk5 qkE :=
    ⟨fun _ _ => hhyp _, hsize, fun G s G2 => h2 (setK s k G) G2,
      fun o1 s => rd3_setK (hE o1) s k, fun o1 G => rd5_setK (h5 o1) k G,
      fun o1 G => rdE_setK (hE o1) k G⟩
  have e1 : pr ((Bytes 16 × Tab3) × ShG (RowH R) st.params) (fun a =>
      D (realRO2 Hb st r K a.1.1 (h3At a.2 k) a.2) a.1.2 a.2) =
      pr (Tab3 × ((Bytes 16 × Tab3) × ShG (RowH R) st.params)) (fun b =>
        dCol D k b.1 (realRO2 Hb st r ((fun G s => K (setK s k G)) b.2.1.2) b.2.1.1 b.2.1.2 b.2.2) b.2.1.2 b.2.2) := by
    let e : Tab3 × ((Bytes 16 × Tab3) × ShG (RowH R) st.params) ≃
        (Bytes 16 × Tab3) × (Tab3 × ShG (RowH R) st.params) :=
      { toFun := fun b => ((b.2.1.1, b.1), (b.2.1.2, b.2.2))
        invFun := fun a => (a.1.2, ((a.1.1, a.2.1), a.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e.symm, ← pr_prod_setK (fun _ => k)
      (fun (a : Bytes 16 × Tab3) s => D (realRO2 Hb st r K a.1 (h3At s k) s) a.2 s)]
    refine pr_congr fun b => ?_
    simp only [dCol, e, Equiv.coe_fn_symm_mk, h3At_setK, realRO2_setK]
  have e2 : pr ((SimCoins2 st.params × Tab3) × ShG (RowH R) st.params) (fun a =>
      D (simRO2 Hb st n K a.1.1 a.2) a.1.2 (progRO2 Hb st n K a.1.1 a.2)) =
      pr (Tab3 × ((SimCoins2 st.params × Tab3) × ShG (RowH R) st.params)) (fun b =>
        dCol D k b.1 (simRO2 Hb st n ((fun G s => K (setK s k G)) b.2.1.2) b.2.1.1 b.2.2) b.2.1.2
          (progRO2 Hb st n ((fun G s => K (setK s k G)) b.2.1.2) b.2.1.1 b.2.2)) := by
    let e : Tab3 × ((SimCoins2 st.params × Tab3) × ShG (RowH R) st.params) ≃
        (SimCoins2 st.params × Tab3) × (Tab3 × ShG (RowH R) st.params) :=
      { toFun := fun b => ((b.2.1.1, b.1), (b.2.1.2, b.2.2))
        invFun := fun a => (a.1.2, ((a.1.1, a.2.1), a.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e.symm, ← pr_prod_setK (fun _ => k)
      (fun (a : SimCoins2 st.params × Tab3) s => D (simRO2 Hb st n K a.1 s) a.2 (progRO2 Hb st n K a.1 s))]
    refine pr_congr fun b => ?_
    simp only [dCol, e, Equiv.coe_fn_symm_mk, simRO2_setK, progRO2_setK]
  rw [e1, e2]
  exact abs_pr_prod_sub_le _ _ fun g =>
    ZK2ARow.zk2A (R := RowH R) Hb st r n (fun G s => K (setK s k G)) hh' hHb hp (dCol D k g) (hD.dCol k g)

/-- **Two-phase zero knowledge with one shared `H₃`.** The real two-phase run reads its slice off
the shared tables at its prefix `k`; its continuation `K` reads the shared tables (`Rd5 K qk5`,
`RdE K qkE`, possibly the column at `k`), the distinguisher's slice argument is not the prover's
(the game's own). Then the real and simulated experiments are close with the error of
`ZK2ARow` at `(q_E + qkE, q₅ + qk5, q_E + qkE)`. -/
theorem zk2_shared (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ) (k : Pre)
    (K : ShG (RowH R) st.params → Cont2) {qk5 qkE : ℕ} (hhyp : ∀ s, Hyp2 st r (K s))
    (hsize : r.size = n) (h2 : ∀ (s : ShG (RowH R) st.params) G2, K (G2, s.2) = K s)
    (h5 : Rd5 K qk5) (hE : RdE K qkE) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    {q3 q5 qE : ℕ} (D : Out2 → Tab3 → ShG (RowH R) st.params → Prop)
    (hD : Budget st.params q3 q5 qE D) :
    |pr ((Bytes 16 × Tab3) × ShG (RowH R) st.params) (fun a =>
        D (realRO2 Hb st r K a.1.1 (h3At a.2 k) a.2) a.1.2 a.2) -
      pr ((SimCoins2 st.params × Tab3) × ShG (RowH R) st.params) (fun a =>
        D (simRO2 Hb st n K a.1.1 a.2) a.1.2 (progRO2 Hb st n K a.1.1 a.2))| ≤
      ZKRow.εz R st.params (qE + qkE) (q5 + qk5) (qE + qkE) :=
  zk2_sharedA Hb st r n k K hhyp hsize h2 (fun o1 => h5.map fun c => c o1)
    (fun o1 => hE.map fun c => c o1) hHb hp D hD

end Shared

end VoleMole.ZK.Sim
