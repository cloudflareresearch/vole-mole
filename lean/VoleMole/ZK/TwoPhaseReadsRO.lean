import VoleMole.ZK.TwoPhaseIC
import VoleMole.ZK.ReadsRO

/-!
# Two-phase zero knowledge with the tables visible, as `Privacy.ZeroKnowledgeROS`, and its reads

`zk2_rom_ic_h23_num` (`ZK/TwoPhaseIC.lean`) for one two-phase run, in the form the privacy games
use (`ZK/ReadsRO.lean` for the single-phase prover):

* **The instance** is a base statement and a **continuation that may read the shared tables**
  `K : ShG R p → Cont2` (in a game: the rest of the game up to this proof's instance, e.g. PomFRIT's
  other session). `Hyp2RO st r n K qk5 qkE`: the deterministic hypotheses for every value of the
  continuation, `|r| = n`, the continuation does not read `H₂³` and reads `H₅` at `qk5` and the
  cipher at `qkE` keys.
* **The prover** `realRO2`: the executable two-phase run on the record `recH Hb (st1 st) r G3 G2 G5`
  with the ideal-cipher PRG. **The simulator** `simRO2` (`simRun2`: its coins, and the cipher for
  the verifier's `chal1`) and its programming `progRO2` (`simTab2`). The simulator reads the
  tables (the cipher; the continuation's reads), which `Privacy.ZeroKnowledgeROS` allows; the
  programming changes only `H₂³`.
* **`zk2_ro`**, **`lean_zeroKnowledgeROS2`**: the two-phase Lean prover is `ZeroKnowledgeROS`
  against the distinguishers with budgets `(q₃, q₅, q_E)`, error `εRO q₃ (q₅ + qk5) (q_E + qkE)`.
* **The reads**: step 1 reads `H₅` at its `624` gate inputs and the cipher at its tree's `4607`
  nodes and not `H₂³` (`step1_rd5`, `step1_rdE`, `step1_agreeOff_h23`); the real run reads what step
  1 and the continuation read (`realRO2_rd5`, `realRO2_rdE`; step 2 reads neither); the simulated
  run the cipher at the `4607` nodes of its opening and what the continuation reads (`simRO2_rd5`,
  `simRO2_rdE`); the programming `H₅` at `312`, the cipher at `2·4607` keys, plus the
  continuation's reads (`progRO2_isProg`).
* The prover, the simulator, the programming and their reads are stated for any type of cipher
  rows (`ShG R p`, `ZK/ReadsRO.lean`); **`ZK2Row R`** is the class of row types with `zk2_ro`
  (instances `ZK2Row.fn`, and `ZK2Row.perm` in `ZK/TwoPhasePerm.lean`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## The prover, the simulator, the programming -/

section Defs

variable {R : Type} [CipherRow R] (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ) (K : ShG R st.params → Cont2)

/-- **The real two-phase prover in the ROM and ideal-cipher model**: the executable two-phase run
with randomness `ρ`, the record with its `H₃` slice `G3` and the shared `H₂³`, `H₅` tables, the
ideal-cipher PRG of the shared cipher, and the continuation at the shared tables. -/
noncomputable def realRO2 (ρ : Bytes 16) (G3 : Tab3) (s : ShG R st.params) : Out2 :=
  @realRun2 (icPrg (rowFn s.2.2)) (recH Hb (st1 st) r G3 s.1 s.2.1) CrtGen.tables st r (K s) (ba ρ)

/-- **The simulated two-phase run**: `simRun2` with the continuation at the shared tables (it
reads the cipher for `chal1`). -/
noncomputable def simRO2 (c : SimCoins2 st.params) (s : ShG R st.params) : Out2 :=
  @simRun2 (icPrg (rowFn s.2.2)) Hb st n (K s) c

/-- **The two-phase simulator's programming**: `H₂³` programmed by `simTab2`. -/
noncomputable def progRO2 (c : SimCoins2 st.params) (s : ShG R st.params) : ShG R st.params :=
  (@simTab2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st (K s) s.2.1 (simRO2 Hb st n K c s) c.1.1.2.1 s.1, s.2)

end Defs

/-- **The hypotheses on a two-phase instance with a table-reading continuation**. -/
structure Hyp2RO {R : Type} (st : Statement) (r : ByteArray) (n : ℕ) (K : ShG R st.params → Cont2)
    (qk5 qkE : ℕ) : Prop where
  hyp : ∀ s, Hyp2 st r (K s)
  size : r.size = n
  h2 : ∀ (s : ShG R st.params) (G2 : Tab2G st.params), K (G2, s.2) = K s
  h5 : Rd5 K qk5
  hE : RdE K qkE

lemma Hyp2RO.mono {R : Type} {st : Statement} {r : ByteArray} {n : ℕ} {K : ShG R st.params → Cont2}
    {qk5 qkE qk5' qkE' : ℕ} (h : Hyp2RO st r n K qk5 qkE) (h5 : qk5 ≤ qk5') (hE : qkE ≤ qkE') :
    Hyp2RO st r n K qk5' qkE' :=
  ⟨h.hyp, h.size, h.h2, h.h5.mono h5, h.hE.mono hE⟩

/-! ## Zero knowledge -/

section ZK

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ) (K : Sh st.params → Cont2)

/-- **Two-phase zero knowledge in the ROM and ideal-cipher model, with the tables visible**
(`zk2_rom_ic_h23_num` for a distinguisher with a `Budget` and a continuation that reads the
tables): the real two-phase prover (`realRO2`) and the simulator with its programming
(`simRO2`, `progRO2`) are `εRO q₃ (q₅ + qk5) (q_E + qkE)`-close. -/
theorem zk2_ro {qk5 qkE : ℕ} (hh : Hyp2RO st r n K qk5 qkE) (hHb : HashesWF Hb)
    (hp : SmallParams st.params) {q3 q5 qE : ℕ} (D : Out2 → Tab3 → Sh st.params → Prop)
    (hD : Budget st.params q3 q5 qE D) :
    |pr ((Bytes 16 × Tab3) × Sh st.params) (fun a =>
        D (realRO2 Hb st r K a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((SimCoins2 st.params × Tab3) × Sh st.params) (fun a =>
        D (simRO2 Hb st n K a.1.1 a.2) a.1.2 (progRO2 Hb st n K a.1.1 a.2))| ≤
      εRO q3 (q5 + qk5) (qE + qkE) := by
  choose Q3 hQ3c hQ3 using hD.h3
  choose Q5 hQ5c hQ5 using hD.h5
  choose QE hQEc hQE using hD.hE
  obtain ⟨K', hKf⟩ : ∃ K' : Tab5F → Cipher → Cont2, K = fun s => K' s.2.1 s.2.2 :=
    ⟨fun G5 E => K (fun _ => 0, G5, E), funext fun s => (hh.h2 s fun _ => 0).symm⟩
  subst hKf
  obtain ⟨QK5, hQK5c, hQK5⟩ := hh.h5
  obtain ⟨QKE, hQKEc, hQKE⟩ := hh.hE
  have hr : r.size = n := hh.size
  subst hr
  have key := zk2_rom_ic_h23_num Hb st r K' (fun G5 E => hh.hyp (fun _ => 0, G5, E)) hHb hp
    (fun G5 E => QK5 (fun _ => 0, G5, E))
    (fun G5 G5' E hk => (hQK5 (fun _ => 0, G5, E) G5' hk).symm)
    (fun G5 E => hQK5c _)
    (fun G5 E => QKE (fun _ => 0, G5, E))
    (fun G5 E E' hk => (hQKE (fun _ => 0, G5, E) E' hk).symm)
    (fun G5 E => hQKEc _)
    (fun o G3 G2 G5 E => D o G3 (G2, G5, E))
    (fun o G3 G2 G5 E => Q3 o (G2, G5, E) G3)
    (fun o G3 G3' G2 G5 E hk => Iff.of_eq (hQ3 o (G2, G5, E) G3 G3' hk).symm)
    (fun o G3 G2 G5 E => hQ3c o (G2, G5, E) G3)
    (fun o G3 G2 G5 E => Q5 o G3 (G2, G5, E))
    (fun o G3 G2 G5 G5' E hk => Iff.of_eq (hQ5 o G3 (G2, G5, E) G5' hk).symm)
    (fun o G3 G2 G5 E => hQ5c o G3 (G2, G5, E))
    (fun o G3 G2 G5 E => QE o G3 (G2, G5, E))
    (fun o G3 G2 G5 E E' hk => Iff.of_eq (hQE o G3 (G2, G5, E) E' hk).symm)
    (fun o G3 G2 G5 E => hQEc o G3 (G2, G5, E))
  let e1 : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher ≃
      (Bytes 16 × Tab3) × Sh st.params :=
    { toFun := fun c => ((c.1.1.1, c.1.2.1), (c.1.1.2, c.1.2.2, c.2))
      invFun := fun c => (((c.1.1, c.2.1), (c.1.2, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (SimCoins2 st.params × Vis2 st.params) × Cipher ≃
      (SimCoins2 st.params × Tab3) × Sh st.params :=
    { toFun := fun c => ((c.1.1, c.1.2.1), (c.1.2.2.1, c.1.2.2.2, c.2))
      invFun := fun c => ((c.1.1, (c.1.2, c.2.1, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e1, ← pr_equiv e2]
  refine key.trans (le_of_eq ?_)
  unfold εRO
  push_cast
  ring

/-- `Statement` `st₀` with the `chal1` binder `b` (PomFRIT: `refresher_com`). -/
def stB (st₀ : Statement) (b : ByteArray) : Statement := { st₀ with binder1 := b }

/-- **The two-phase Lean prover is `ZeroKnowledgeROS`** for the instances `(b, K)` (the binder of
`st₀` and a continuation reading the tables at `qk5`, `qkE` keys), against the distinguishers with
budgets `(q₃, q₅, q_E)`, with error `εRO q₃ (q₅ + qk5) (q_E + qkE)`. -/
theorem lean_zeroKnowledgeROS2 (st₀ : Statement) (n qk5 qkE : ℕ) (hHb : HashesWF Hb)
    (hp : SmallParams st₀.params) (q3 q5 qE : ℕ) :
    ZeroKnowledgeROS
      (fun (x : ByteArray × (Sh st₀.params → Cont2)) (r : ByteArray) =>
        Hyp2RO (stB st₀ x.1) r n x.2 qk5 qkE)
      (fun (x : ByteArray × (Sh st₀.params → Cont2)) (r : ByteArray) (ρ : Bytes 16) (G3 : Tab3)
        (s : Sh st₀.params) => realRO2 Hb (stB st₀ x.1) r x.2 ρ G3 s)
      (fun (x : ByteArray × (Sh st₀.params → Cont2)) (c : SimCoins2 st₀.params)
        (s : Sh st₀.params) => simRO2 Hb (stB st₀ x.1) n x.2 c s)
      (fun (x : ByteArray × (Sh st₀.params → Cont2)) (c : SimCoins2 st₀.params)
        (s : Sh st₀.params) => progRO2 Hb (stB st₀ x.1) n x.2 c s)
      (Budget st₀.params q3 q5 qE) (εRO q3 (q5 + qk5) (qE + qkE)) :=
  fun x r hxr D hD => zk2_ro Hb (stB st₀ x.1) r n x.2 hxr hHb hp D hD

end ZK

/-! ## Two-phase zero knowledge for a type of cipher rows -/

section ZK2Row

/-- **Two-phase zero knowledge for a type of cipher rows**: `zk2_ro` for the shared tables
`ShG R p`, with the single-phase error `ZKRow.εz` at the distinguisher's budget plus the
continuation's reads. Function rows: `zk2_ro` (`ZK2Row.fn`); permutation rows:
`ZK/TwoPhasePerm.lean`. -/
class ZK2Row (R : Type) [Fintype R] [CipherRow R] [ZKRow R] where
  /-- `zk2_ro` with this row type. -/
  zk2 : ∀ (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ) (K : ShG R st.params → Cont2)
    {qk5 qkE : ℕ}, Hyp2RO st r n K qk5 qkE → HashesWF Hb → SmallParams st.params →
    ∀ {q3 q5 qE : ℕ} (D : Out2 → Tab3 → ShG R st.params → Prop), Budget st.params q3 q5 qE D →
    |pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        D (realRO2 Hb st r K a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((SimCoins2 st.params × Tab3) × ShG R st.params) (fun a =>
        D (simRO2 Hb st n K a.1.1 a.2) a.1.2 (progRO2 Hb st n K a.1.1 a.2))| ≤
      ZKRow.εz R st.params q3 (q5 + qk5) (qE + qkE)

/-- **Function rows**: `zk2_ro`. -/
instance ZK2Row.fn : ZK2Row (Blk → Blk) where
  zk2 Hb st r n K _ _ hh hHb hp _ _ _ D hD := zk2_ro Hb st r n K hh hHb hp D hD

variable {R : Type} [Fintype R] [CipherRow R] [ZKRow R] [ZK2Row R] (Hb : Hashes)

/-- **The two-phase Lean prover is `ZeroKnowledgeROS` for every row type with `ZK2Row`**
(`lean_zeroKnowledgeROS2`, error `ZKRow.εz R p q₃ (q₅ + qk5) (q_E + qkE)`). -/
theorem lean_zeroKnowledgeROS2G (st₀ : Statement) (n qk5 qkE : ℕ) (hHb : HashesWF Hb)
    (hp : SmallParams st₀.params) (q3 q5 qE : ℕ) :
    ZeroKnowledgeROS
      (fun (x : ByteArray × (ShG R st₀.params → Cont2)) (r : ByteArray) =>
        Hyp2RO (stB st₀ x.1) r n x.2 qk5 qkE)
      (fun (x : ByteArray × (ShG R st₀.params → Cont2)) (r : ByteArray) (ρ : Bytes 16) (G3 : Tab3)
        (s : ShG R st₀.params) => realRO2 Hb (stB st₀ x.1) r x.2 ρ G3 s)
      (fun (x : ByteArray × (ShG R st₀.params → Cont2)) (c : SimCoins2 st₀.params)
        (s : ShG R st₀.params) => simRO2 Hb (stB st₀ x.1) n x.2 c s)
      (fun (x : ByteArray × (ShG R st₀.params → Cont2)) (c : SimCoins2 st₀.params)
        (s : ShG R st₀.params) => progRO2 Hb (stB st₀ x.1) n x.2 c s)
      (Budget st₀.params q3 q5 qE) (ZKRow.εz R st₀.params q3 (q5 + qk5) (qE + qkE)) :=
  fun x r hxr D hD => ZK2Row.zk2 Hb (stB st₀ x.1) r n x.2 hxr hHb hp D hD

end ZK2Row

/-! ## What the two-phase run reads -/

section Reads

variable {R : Type} [CipherRow R] {Hb : Hashes} {st : Statement} {r : ByteArray}

lemma RdE.of_indep {R : Type} {p : Params} {X : Sort*} (f : ShG R p → X) (h : ∀ s E, f (s.1, s.2.1, E) = f s) :
    RdE f 0 :=
  ⟨fun _ => ∅, fun _ => le_rfl, fun s E _ => h s E⟩

lemma Rd5.of_indep {R : Type} {p : Params} {X : Sort*} (f : ShG R p → X) (h : ∀ s G5, f (s.1, G5, s.2.2) = f s) :
    Rd5 f 0 :=
  ⟨fun _ => ∅, fun _ => le_rfl, fun s G5 _ => h s G5⟩

/-- **Step 1 does not read `H₂³`.** -/
lemma step1_agreeOff_h23 [HasPrg] {Hs Hs' : Hashes} (h : Hs.AgreeOff .h23 Hs') (T : CrtTables)
    (st : Statement) (r rho : ByteArray) : step1 Hs T st r rho = step1 Hs' T st r rho := by
  have hmu : VoleMole.Verifier.mu Hs none st.dst = VoleMole.Verifier.mu Hs' none st.dst := by
    simp only [VoleMole.Verifier.mu, h .muDelayed (by decide)]
  unfold step1
  rw [voleGen_eq_voleGenAt, voleGen_eq_voleGenAt, h .h3 (by decide), hmu]
  simp only [voleGenAt, h .h4 (by decide), h .h1 (by decide), h .h5 (by decide), h.chal1 (by decide)]

/-- The root seed of step 1 on the record `recH Hb (st1 st) r G3 …`. -/
def seed1 (Hs : Hashes) (st : Statement) (r rho : ByteArray) : ByteArray :=
  (Hs.hash .h3 ((r ++ (st1 st).mu1 Hs ++ rho).push 3)).extract 0 16

/-- The `iv_pre` of step 1. -/
def ivPre1 (Hs : Hashes) (st : Statement) (r rho : ByteArray) : ByteArray :=
  (Hs.hash .h3 ((r ++ (st1 st).mu1 Hs ++ rho).push 3)).extract 16 32

/-- **The cipher keys step 1 reads**: the rows of its tree's `2L − 1` nodes. -/
noncomputable def step1KeysE (Hb : Hashes) (st : Statement) (r rho : ByteArray) (G3 : Tab3)
    (s : ShG R st.params) : Finset Blk :=
  (range BAVC.numNodes).image fun m => blk 16 (@treeNode (icPrg (rowFn s.2.2))
    (seed1 (recH Hb (st1 st) r G3 s.1 s.2.1) st r rho)
    ((recH Hb (st1 st) r G3 s.1 s.2.1).hash .h4
      ((ivPre1 (recH Hb (st1 st) r G3 s.1 s.2.1) st r rho ++
        (st1 st).mu1 (recH Hb (st1 st) r G3 s.1 s.2.1)).push 4)) m)

/-- **Step 1 reads the cipher at most at `4607` keys** (its tree's nodes). -/
theorem step1_rdE (hHb : HashesWF Hb) (rho : ByteArray) (G3 : Tab3) :
    RdE (fun s : ShG R st.params =>
      @step1 (icPrg (rowFn s.2.2)) (recH Hb (st1 st) r G3 s.1 s.2.1) CrtGen.tables st r rho) 4607 := by
  refine ⟨step1KeysE Hb st r rho G3, fun s => card_image_le.trans (le_of_eq (by
    rw [card_range]; rfl)), fun s E h => ?_⟩
  have hs : (seed1 (recH Hb (st1 st) r G3 s.1 s.2.1) st r rho).size = 16 := by
    rw [seed1, ByteArray.size_extract, recH_wf (st := st1 st) (w := r) hHb G3 s.1 s.2.1]; rfl
  unfold step1
  dsimp only
  rw [@voleGen_eq_voleGenAt (icPrg (rowFn E)), @voleGen_eq_voleGenAt (icPrg (rowFn s.2.2))]
  exact (voleGenAt_ic_congr _ _ _ _ _ _ _ hs fun m hm _ =>
    rowFn_congr (h _ (mem_image.2 ⟨m, mem_range.2 hm, rfl⟩))).symm

/-- **The `H₅` keys step 1 reads**: its `2·312` gate inputs. -/
noncomputable def step1Keys5 (Hb : Hashes) (st : Statement) (r rho : ByteArray) (G3 : Tab3)
    (s : ShG R st.params) : Finset (Bytes 37) :=
  ((@vgIn5 (icPrg (rowFn s.2.2)) (recH Hb (st1 st) r G3 s.1 s.2.1) CrtGen.tables st.params
    ((st1 st).mu1 (recH Hb (st1 st) r G3 s.1 s.2.1)) (seed1 (recH Hb (st1 st) r G3 s.1 s.2.1) st r rho)
    (ivPre1 (recH Hb (st1 st) r G3 s.1 s.2.1) st r rho)).toFinset).image (blk 37)

/-- **Step 1 reads `H₅` at most at `624` keys** (its gate inputs, both labels). -/
theorem step1_rd5 (rho : ByteArray) (G3 : Tab3) :
    Rd5 (fun s : ShG R st.params =>
      @step1 (icPrg (rowFn s.2.2)) (recH Hb (st1 st) r G3 s.1 s.2.1) CrtGen.tables st r rho) 624 := by
  classical
  refine ⟨step1Keys5 Hb st r rho G3, fun s => ?_, fun s G5 h => ?_⟩
  · refine card_image_le.trans ((List.toFinset_card_le _).trans (le_of_eq ?_))
    exact @vgIn5_length (icPrg (rowFn s.2.2)) _ _ _ _ _ _
  have hA := recHp_agreeOff_h5 (Hb := Hb) (st := st1 st) (w := r) (p := st.params) G3 s.1 G5 s.2.1
  have hmu : ∀ G5', (st1 st).mu1 (recH Hb (st1 st) r G3 s.1 G5') = (st1 st).mu1 Hb :=
    fun G5' => recHp_mu1 (p := st.params) (st := st1 st) (w := r) G3 s.1 G5'
  have h3 : ∀ G5', (recH Hb (st1 st) r G3 s.1 G5').hash .h3 = (recH Hb (st1 st) r G3 s.1 s.2.1).hash .h3 :=
    fun G5' => (recHp_h3 (p := st.params) (st := st1 st) (w := r) G3 s.1 G5').trans
      (recHp_h3 (p := st.params) (st := st1 st) (w := r) G3 s.1 s.2.1).symm
  unfold step1
  dsimp only
  rw [@voleGen_eq_voleGenAt (icPrg (rowFn s.2.2)), @voleGen_eq_voleGenAt (icPrg (rowFn s.2.2))]
  rw [show VoleMole.Verifier.mu (recH Hb (st1 st) r G3 s.1 G5) none st.dst = (st1 st).mu1 Hb from
      hmu G5,
    show VoleMole.Verifier.mu (recH Hb (st1 st) r G3 s.1 s.2.1) none st.dst = (st1 st).mu1 Hb from
      hmu s.2.1, h3 G5]
  refine @voleGenAt_h5_congr (icPrg (rowFn s.2.2)) _ _ hA _ _ _ _ _ _ _ fun x hx => ?_
  rw [@vgIn5_agreeOff (icPrg (rowFn s.2.2)) _ _ hA] at hx
  refine withTable_h5_congr _ fun hs => (h _ (mem_image.2 ⟨x, ?_, rfl⟩)).symm
  rw [List.mem_toFinset]
  have hx' : x ∈ @vgIn5 (icPrg (rowFn s.2.2)) (recH Hb (st1 st) r G3 s.1 s.2.1) CrtGen.tables st.params
      ((st1 st).mu1 Hb)
      (((recH Hb (st1 st) r G3 s.1 s.2.1).hash .h3 ((r ++ (st1 st).mu1 Hb ++ rho).push 3)).extract 0 16)
      (((recH Hb (st1 st) r G3 s.1 s.2.1).hash .h3 ((r ++ (st1 st).mu1 Hb ++ rho).push 3)).extract
        16 32) := hx
  simpa only [step1Keys5, seed1, ivPre1, hmu] using hx'

variable {K : ShG R st.params → Cont2}

/-- The real two-phase run, as step 1 and then step 2 for the continuation's choice. -/
lemma realRO2_eq (ρ : Bytes 16) (G3 : Tab3) (s : ShG R st.params) :
    realRO2 Hb st r K ρ G3 s =
      (fun (y : Prover.Pending) (s : ShG R st.params) => (y.proof, y.chal1, (K s (y.proof, y.chal1)).map
        fun x => Prover.proveCommit (recH Hb (st1 st) r G3 s.1 s.2.1) (withInst st x.1) x.2 y))
        (@step1 (icPrg (rowFn s.2.2)) (recH Hb (st1 st) r G3 s.1 s.2.1) CrtGen.tables st r (ba ρ)) s := rfl

/-- **The real two-phase run reads the cipher at most at `4607 + qkE` keys** (step 1 and the
continuation; step 2 does not use the cipher). -/
theorem realRO2_rdE (hHb : HashesWF Hb) {qkE : ℕ} (hK : RdE K qkE) (ρ : Bytes 16) (G3 : Tab3) :
    RdE (realRO2 Hb st r K ρ G3) (4607 + qkE) := by
  have h := (step1_rdE (st := st) (r := r) hHb (ba ρ) G3).bind
    (f := fun (y : Prover.Pending) (s : ShG R st.params) => (y.proof, y.chal1,
      (K s (y.proof, y.chal1)).map fun x =>
        Prover.proveCommit (recH Hb (st1 st) r G3 s.1 s.2.1) (withInst st x.1) x.2 y))
    fun y => by
      simpa using hK.bind (f := fun (k : Cont2) (s : ShG R st.params) => (y.proof, y.chal1,
        (k (y.proof, y.chal1)).map fun x =>
          Prover.proveCommit (recH Hb (st1 st) r G3 s.1 s.2.1) (withInst st x.1) x.2 y))
        fun k => RdE.of_indep _ fun s E => rfl
  exact h

/-- **The real two-phase run reads `H₅` at most at `624 + qk5` keys** (step 1 and the
continuation; step 2 does not read `H₅`). -/
theorem realRO2_rd5 {qk5 : ℕ} (hK : Rd5 K qk5) (ρ : Bytes 16) (G3 : Tab3) :
    Rd5 (realRO2 Hb st r K ρ G3) (624 + qk5) := by
  have h := (step1_rd5 (st := st) (r := r) (Hb := Hb) (ba ρ) G3).bind
    (f := fun (y : Prover.Pending) (s : ShG R st.params) => (y.proof, y.chal1,
      (K s (y.proof, y.chal1)).map fun x =>
        Prover.proveCommit (recH Hb (st1 st) r G3 s.1 s.2.1) (withInst st x.1) x.2 y))
    fun y => by
      simpa using hK.bind (f := fun (k : Cont2) (s : ShG R st.params) => (y.proof, y.chal1,
        (k (y.proof, y.chal1)).map fun x =>
          Prover.proveCommit (recH Hb (st1 st) r G3 s.1 s.2.1) (withInst st x.1) x.2 y))
        fun k => Rd5.of_indep _ fun s G5 => by
          have hA : (recH Hb (st1 st) r G3 s.1 G5).AgreeOff .h5 (recH Hb (st1 st) r G3 s.1 s.2.1) :=
            recHp_agreeOff_h5 (p := st.params) (st := st1 st) (w := r) G3 s.1 G5 s.2.1
          simp only [proveCommit_agreeOff_h5 hA]
  exact h

/-- **The simulated two-phase run reads the cipher only at the reconstruction of its opening.** -/
lemma simRun2_ic_congr {E E' : Cipher} (Hb : Hashes) (st : Statement) (n : ℕ) (k : Cont2)
    (c : SimCoins2 st.params)
    (h : ∀ key ∈ hRd E Hb (st1 st) c.1.1 (deltaOf c.1.1.2.1), E key = E' key) :
    @simRun2 (icPrg E) Hb st n k c = @simRun2 (icPrg E') Hb st n k c := by
  unfold simRun2
  rcases hf : firstHit c.1.1.2.1 with _ | ⟨ctr, δ⟩
  · rfl
  · have hd : deltaOf c.1.1.2.1 = δ := by unfold deltaOf; rw [hf]; rfl
    rw [hd] at h
    simp only [simPhase1, phase1Of, tC1, pubOf_ic_congr Hb (st1 st) c.1.1 δ h]

/-- **The simulated two-phase run reads the cipher at most at `4607 + qkE` keys.** -/
theorem simRO2_rdE {n qkE : ℕ} (hK : RdE K qkE) (c : SimCoins2 st.params) :
    RdE (simRO2 Hb st n K c) (qkE + 4607) := by
  have h := hK.bind (f := fun (k : Cont2) (s : ShG R st.params) => @simRun2 (icPrg (rowFn s.2.2)) Hb st n k c)
    fun k => ⟨fun s => hRd (rowFn s.2.2) Hb (st1 st) c.1.1 (deltaOf c.1.1.2.1),
      fun s => rdKeys_card _ _ _ _, fun s E hE => (simRun2_ic_congr Hb st n k c fun k hk => rowFn_congr (hE k hk)).symm⟩
  exact h

/-- **The simulated two-phase run reads `H₅` only through the continuation.** -/
theorem simRO2_rd5 {n qk5 : ℕ} (hK : Rd5 K qk5) (c : SimCoins2 st.params) :
    Rd5 (simRO2 Hb st n K c) qk5 := by
  have h := hK.bind (f := fun (k : Cont2) (s : ShG R st.params) => @simRun2 (icPrg (rowFn s.2.2)) Hb st n k c)
    fun k => Rd5.of_indep _ fun s G5 => rfl
  exact h.mono (le_of_eq (Nat.add_zero _))

/-- The `H₅` keys the two-phase recomputation reads (the verifier's gate inputs on the final
proof, for the instance picked; at most `312`). -/
noncomputable def progKeys52 (Hb : Hashes) (st : Statement) (k : Cont2) (o : Out2)
    (s : ShG R st.params) : Finset (Bytes 37) :=
  match o.2.2, k (o.1, o.2.1) with
  | some (.ok b), some y =>
    ((@vIn5 (icPrg (rowFn s.2.2)) (rec5 Hb s.2.1) CrtGen.tables (withInst st y.1) b).toFinset).image (blk 37)
  | _, _ => ∅

/-- The cipher keys the two-phase recomputation reads (the reconstruction's nodes, at most
`4607`). -/
noncomputable def progKeysE2 (Hb : Hashes) (st : Statement) (k : Cont2) (o : Out2)
    (s : ShG R st.params) : Finset Blk :=
  match o.2.2, k (o.1, o.2.1) with
  | some (.ok b), some y =>
    rdKeys (rowFn s.2.2) (ivOf (rec5 Hb s.2.1) ⟨st.params, b⟩ ((withInst st y.1).mu1 (rec5 Hb s.2.1)))
      (⟨st.params, b⟩ : Proof).opening (⟨st.params, b⟩ : Proof).delta
  | _, _ => ∅

/-- The programming for a fixed continuation `k`. -/
noncomputable def progK (Hb : Hashes) (st : Statement) (n : ℕ) (k : Cont2) (c : SimCoins2 st.params)
    (s : ShG R st.params) : ShG R st.params :=
  (@simTab2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st k s.2.1 (@simRun2 (icPrg (rowFn s.2.2)) Hb st n k c)
    c.1.1.2.1 s.1, s.2)

/-- **The programming for a fixed continuation reads `H₅` at `312` and the cipher at `2·4607`
keys** (the simulated `chal1`'s reconstruction and the recomputation's). -/
theorem progK_isProg (n : ℕ) (k : Cont2) (c : SimCoins2 st.params) :
    IsProg (progK (R := R) Hb st n k c) 312 (4607 + 4607) := by
  classical
  refine ⟨fun _ => rfl, ⟨fun s => progKeys52 Hb st k (@simRun2 (icPrg (rowFn s.2.2)) Hb st n k c) s,
    fun s => ?_, fun s G5 h => ?_⟩, ?_⟩
  · unfold progKeys52
    dsimp only
    split
    · exact card_image_le.trans ((List.toFinset_card_le _).trans
        (@vIn5_length_le (icPrg (rowFn s.2.2)) _ _ _ _))
    · simp
  · suffices e : @outPre2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st k G5
        (@simRun2 (icPrg (rowFn s.2.2)) Hb st n k c) =
        @outPre2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st k s.2.1 (@simRun2 (icPrg (rowFn s.2.2)) Hb st n k c) by
      simp only [progK, simTab2, e]
    unfold progKeys52 at h
    dsimp only at h
    unfold outPre2
    split
    · rename_i b y hb hy
      rw [hb, hy] at h
      have hmu : (withInst st y.1).mu1 (rec5 Hb G5) = (withInst st y.1).mu1 (rec5 Hb s.2.1) := by
        rw [rec5_mu1, rec5_mu1]
      have h4 : (rec5 Hb G5).hash .h4 = (rec5 Hb s.2.1).hash .h4 := by rw [rec5_h4, rec5_h4]
      have hA : (rec5 Hb G5).AgreeOff .h5 (rec5 Hb s.2.1) := by
        intro k' hk; rw [rec5_agree_ne hk, rec5_agree_ne hk]
      refine @vPre_h5_congr (icPrg (rowFn s.2.2)) _ _ hA _ _ _ fun x hx => ?_
      rw [@vIn5_congr (icPrg (rowFn s.2.2)) _ (withInst st y.1) _ _ hmu h4] at hx
      exact withTable_h5_congr _ fun _ => (h _ (mem_image.2 ⟨x, List.mem_toFinset.2 hx, rfl⟩)).symm
    · rfl
  · have hS : RdE (fun s : ShG R st.params => @simRun2 (icPrg (rowFn s.2.2)) Hb st n k c) 4607 :=
      ⟨fun s => hRd (rowFn s.2.2) Hb (st1 st) c.1.1 (deltaOf c.1.1.2.1),
        fun s => rdKeys_card _ _ _ _, fun s E hE => (simRun2_ic_congr Hb st n k c fun k hk => rowFn_congr (hE k hk)).symm⟩
    have h := RdE.bind hS
      (f := fun (o : Out2) (s : ShG R st.params) =>
        @simTab2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st k s.2.1 o c.1.1.2.1 s.1)
      fun o => ⟨fun s => progKeysE2 Hb st k o s, fun s => by
        unfold progKeysE2
        dsimp only
        split
        · exact rdKeys_card _ _ _ _
        · simp, fun s E h => by
        suffices e : @outPre2 (icPrg (rowFn E)) Hb CrtGen.tables st k s.2.1 o =
            @outPre2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st k s.2.1 o by
          simp only [simTab2, e]
        unfold progKeysE2 at h
        dsimp only at h
        unfold outPre2
        split
        · rename_i b y hb hy
          rw [hb, hy] at h
          exact (vPre_ic_congr (rec5 Hb s.2.1) CrtGen.tables (withInst st y.1) b
            fun k hk => rowFn_congr (h k hk)).symm
        · rfl⟩
    exact h

/-- **The two-phase programming reads `H₅` at `qk5 + 312` and the cipher at `qkE + 2·4607` keys**
(the continuation's reads, then the fixed-continuation programming's). -/
theorem progRO2_isProg {n qk5 qkE : ℕ} (h5 : Rd5 K qk5) (hE : RdE K qkE) (c : SimCoins2 st.params) :
    IsProg (progRO2 Hb st n K c) (qk5 + 312) (qkE + (4607 + 4607)) :=
  ⟨fun _ => rfl,
    h5.bind (f := fun (k : Cont2) (s : ShG R st.params) => (progK Hb st n k c s).1) fun k =>
      (progK_isProg (Hb := Hb) n k c).2.1,
    hE.bind (f := fun (k : Cont2) (s : ShG R st.params) => (progK Hb st n k c s).1) fun k =>
      (progK_isProg (Hb := Hb) n k c).2.2⟩

end Reads

end VoleMole.ZK.Sim
