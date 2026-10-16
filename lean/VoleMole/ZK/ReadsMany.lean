import VoleMole.ZK.AdaptRO
import VoleMole.ZK.TwoPhaseReadsRO

/-!
# Reads of many proofs, and the hybrid over many steps

Generic pieces for the privacy games with many sessions (`Privacy/PomFRITMany.lean`,
`Privacy/MoussakaMany.lean`, `Privacy/RatatouilleMany.lean`; `lean/docs/zk.md` §10.8):

* **Families of readers** (`Rd5.pi`, `RdE.pi`, `SReads.pi`): a family indexed by a finite type,
  read together, reads the union of the members' keys, `|ι|` times the bound; a reader determined
  by a reader reads what it reads (`SReads.of_det`, `Rd5.of_det`, `RdE.of_det`; used instead of
  definitional unfolding wherever that would make the kernel evaluate a prover).
* **Step 1 is a consistent reader** (`step1_cons`, `vgIn5_ic_congr`): a table that agrees with `s`
  on the `624` `H₅` keys and the `4607` cipher keys that step 1 reads at `s` (whatever its `H₂³`)
  has the same keys and the same step-1 output. (`step1_rd5`, `step1_rdE` give the bounds, not the
  consistency `SReads` needs.)
* **The single-phase prover is a consistent reader** (`realRO_sreads`): of `H₅` at `624` keys, the
  cipher at `4607` keys and `H₂³` at the `nGrind = 2³²` grinding points of its own prefix
  (`prove_recH_eq`: the proof reads `H₂³` only there), and of no `H₃` slice but its own.
* **The hybrid over `n` steps** (`abs_sub_le_sum_of_steps`, `abs_sub_le_mul_of_steps`), and
  `noHitProb_le_128` for the numeric bounds.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## Families of readers -/

section Families

variable {R : Type} {p : Params} {ι X : Type*} [Fintype ι]

/-- **A family of `H₅` readers**, read together: the union of their keys. -/
lemma Rd5.pi {f : ι → ShG R p → X} {a : ℕ} (h : ∀ i, Rd5 (f i) a) :
    Rd5 (fun s i => f i s) (Fintype.card ι * a) := by
  classical
  choose Q hQ hf using h
  refine ⟨fun s => univ.biUnion fun i => Q i s, fun s => ?_, fun s G5 hs => funext fun i =>
    hf i s G5 fun k hk => hs k (mem_biUnion.2 ⟨i, mem_univ _, hk⟩)⟩
  refine card_biUnion_le.trans ((sum_le_card_nsmul _ _ a fun i _ => hQ i s).trans ?_)
  simp [card_univ]

/-- **A family of cipher readers**, read together. -/
lemma RdE.pi {f : ι → ShG R p → X} {a : ℕ} (h : ∀ i, RdE (f i) a) :
    RdE (fun s i => f i s) (Fintype.card ι * a) := by
  classical
  choose Q hQ hf using h
  refine ⟨fun s => univ.biUnion fun i => Q i s, fun s => ?_, fun s E hs => funext fun i =>
    hf i s E fun k hk => hs k (mem_biUnion.2 ⟨i, mem_univ _, hk⟩)⟩
  refine card_biUnion_le.trans ((sum_le_card_nsmul _ _ a fun i _ => hQ i s).trans ?_)
  simp [card_univ]

/-- **A family of consistent table readers**, read together: the union of their read sets is
again consistent. -/
lemma SReads.pi {f : ι → Tb R p → X} {a3 a2 a5 aE : ℕ} (h : ∀ i, SReads p (f i) a3 a2 a5 aE) :
    SReads p (fun t i => f i t) (Fintype.card ι * a3) (Fintype.card ι * a2) (Fintype.card ι * a5)
      (Fintype.card ι * aE) := by
  classical
  choose Q hQ hc using h
  let U : Tb R p → RS p := fun t => (univ.biUnion fun i => (Q i t).1,
    univ.biUnion fun i => (Q i t).2.1, univ.biUnion fun i => (Q i t).2.2.1,
    univ.biUnion fun i => (Q i t).2.2.2)
  have hsub : ∀ t t' i, AgT (U t) t t' → AgT (Q i t) t t' := fun t t' i h =>
    ⟨fun k hk => h.1 k (mem_biUnion.2 ⟨i, mem_univ _, hk⟩),
      fun k hk => h.2.1 k (mem_biUnion.2 ⟨i, mem_univ _, hk⟩),
      fun k hk => h.2.2.1 k (mem_biUnion.2 ⟨i, mem_univ _, hk⟩),
      fun k hk => h.2.2.2 k (mem_biUnion.2 ⟨i, mem_univ _, hk⟩)⟩
  refine ⟨U, fun t t' h => ?_, fun t => ?_⟩
  · have e : ∀ i, Q i t' = Q i t ∧ f i t' = f i t := fun i => hQ i t t' (hsub t t' i h)
    refine ⟨?_, funext fun i => (e i).2⟩
    simp only [U, fun i => (e i).1]
  · have b : ∀ (g : ι → ℕ) (a : ℕ), (∀ i, g i ≤ a) → ∑ i, g i ≤ Fintype.card ι * a :=
      fun g a hg => (sum_le_card_nsmul _ _ a fun i _ => hg i).trans (by simp [card_univ])
    exact ⟨card_biUnion_le.trans (b _ _ fun i => (hc i t).1),
      card_biUnion_le.trans (b _ _ fun i => (hc i t).2.1),
      card_biUnion_le.trans (b _ _ fun i => (hc i t).2.2.1),
      card_biUnion_le.trans (b _ _ fun i => (hc i t).2.2.2)⟩

/-- `Rd5.bind` for a reader given as `F s = f (m s) s`. -/
lemma Rd5.bindEq {Y : Type*} {m : ShG R p → Y} {f : Y → ShG R p → X} {F : ShG R p → X} {a b : ℕ}
    (hF : ∀ s, F s = f (m s) s) (hm : Rd5 m a) (hf : ∀ y, Rd5 (f y) b) : Rd5 F (a + b) := by
  have e : F = fun s => f (m s) s := funext hF
  subst e
  exact hm.bind hf

/-- `RdE.bind` for a reader given as `F s = f (m s) s`. -/
lemma RdE.bindEq {Y : Type*} {m : ShG R p → Y} {f : Y → ShG R p → X} {F : ShG R p → X} {a b : ℕ}
    (hF : ∀ s, F s = f (m s) s) (hm : RdE m a) (hf : ∀ y, RdE (f y) b) : RdE F (a + b) := by
  have e : F = fun s => f (m s) s := funext hF
  subst e
  exact hm.bind hf

/-- **A reader determined by a consistent reader** is one, with the same reads. -/
lemma SReads.of_det {Y : Type*} {f : Tb R p → Y} {g : Tb R p → X} {a3 a2 a5 aE : ℕ}
    (hf : SReads p f a3 a2 a5 aE) (hg : ∀ t t', f t' = f t → g t' = g t) : SReads p g a3 a2 a5 aE := by
  obtain ⟨Q, hQ, hc⟩ := hf
  exact ⟨Q, fun t t' h => ⟨(hQ t t' h).1, hg t t' (hQ t t' h).2⟩, hc⟩

/-- An `H₅` reader determined by one. -/
lemma Rd5.of_det {Y : Type*} {f : ShG R p → Y} {g : ShG R p → X} {a : ℕ} (hf : Rd5 f a)
    (hg : ∀ s s', f s' = f s → g s' = g s) : Rd5 g a := by
  obtain ⟨Q, hQ, h⟩ := hf
  exact ⟨Q, hQ, fun s G5 hs => hg s _ (h s G5 hs)⟩

/-- A cipher reader determined by one. -/
lemma RdE.of_det {Y : Type*} {f : ShG R p → Y} {g : ShG R p → X} {a : ℕ} (hf : RdE f a)
    (hg : ∀ s s', f s' = f s → g s' = g s) : RdE g a := by
  obtain ⟨Q, hQ, h⟩ := hf
  exact ⟨Q, hQ, fun s E hs => hg s _ (h s E hs)⟩

end Families

/-! ## Step 1 is a consistent reader of `H₅` and the cipher -/

section Step1

variable {R : Type} [CipherRow R] {Hb : Hashes} {st : Statement} {r : ByteArray}

lemma recH_h3_tables (G3 : Tab3) (G2 G2' : Tab2G st.params) (G5 G5' : Tab5F) :
    (recH Hb (st1 st) r G3 G2 G5).hash .h3 = (recH Hb (st1 st) r G3 G2' G5').hash .h3 := by
  funext x
  simp only [recH, Hashes.withTable, reduceCtorEq, ite_false]

lemma recH_h4_tables (G3 : Tab3) (G2 G2' : Tab2G st.params) (G5 G5' : Tab5F) :
    (recH Hb (st1 st) r G3 G2 G5).hash .h4 = (recH Hb (st1 st) r G3 G2' G5').hash .h4 := by
  rw [recH_hash_ne (by decide) (by decide) (by decide),
    recH_hash_ne (by decide) (by decide) (by decide)]

lemma recH_mu1_tables (G3 : Tab3) (G2 G2' : Tab2G st.params) (G5 G5' : Tab5F) :
    (st1 st).mu1 (recH Hb (st1 st) r G3 G2 G5) = (st1 st).mu1 (recH Hb (st1 st) r G3 G2' G5') := by
  rw [recH_mu1, recH_mu1]

/-- **The sender columns and `u_pre` read the cipher only at the tree's nodes**, so step 1's `H₅`
inputs do too. -/
theorem vgIn5_ic_congr {E E' : Cipher} {seed : ByteArray} (Hs : Hashes) (T : CrtTables) (p : Params)
    (mu1 ivPre : ByteArray) (hs : seed.size = 16)
    (h : NodesAgree E E' seed (Hs.hash .h4 ((ivPre ++ mu1).push 4))) :
    @vgIn5 (icPrg E) Hs T p mu1 seed ivPre = @vgIn5 (icPrg E') Hs T p mu1 seed ivPre := by
  set iv := Hs.hash .h4 ((ivPre ++ mu1).push 4) with hiv
  have hc := commit_ic_congr hs h
  have hk : ∀ i j, i < BAVC.tau → j < 2 ^ BAVC.kOf i →
      leafKey (@BAVC.commit (icPrg E') seed iv).2 i j = @treeNode (icPrg E) seed iv (BAVC.treePos i j) :=
    fun i j hi hj => by
      rw [@leafKey_commit (icPrg E') seed iv hs i j hi hj, treeNode_ic_congr h _ (treePos_lt hi hj)]
  have hus : (Array.range BAVC.tau).map (fun i =>
      @Prover.smallVoleUWords (icPrg E) p iv i (leafKey (@BAVC.commit (icPrg E') seed iv).2 i)) =
      (Array.range BAVC.tau).map (fun i =>
        @Prover.smallVoleUWords (icPrg E') p iv i (leafKey (@BAVC.commit (icPrg E') seed iv).2 i)) :=
    Array.map_congr_left fun i hi => smallVoleUWords_ic_congr _ _ _ _ fun j hj hsz => by
      have hi' := Array.mem_range.1 hi
      rw [hk i j hi' hj] at hsz ⊢
      exact h _ (treePos_lt hi' hj) hsz
  have hcols : @Prover.senderColumns (icPrg E) p iv (leafKey (@BAVC.commit (icPrg E') seed iv).2) =
      @Prover.senderColumns (icPrg E') p iv (leafKey (@BAVC.commit (icPrg E') seed iv).2) := by
    unfold Prover.senderColumns
    refine convertToVoleAt_ic_congr _ _ _ _ _ fun i hi j hj _ hsz => ?_
    rw [hk i j hi hj] at hsz ⊢
    exact h _ (treePos_lt hi hj) hsz
  simp only [vgIn5, vgCols, vgUPre, vgIv, ← hiv, hc, hus, hcols]

omit [CipherRow R] in
/-- Step 1's `H₅` inputs depend on the record only through `H₄`. -/
lemma vgIn5_h4 [HasPrg] {Hs Hs' : Hashes} (h : Hs.hash .h4 = Hs'.hash .h4) (T : CrtTables) (p : Params)
    (mu1 seed ivPre : ByteArray) : vgIn5 Hs T p mu1 seed ivPre = vgIn5 Hs' T p mu1 seed ivPre := by
  simp only [vgIn5, vgCols, vgUPre, vgIv, h]

/-- Step 1's cipher keys do not depend on `H₂³` or `H₅`. -/
lemma step1KeysE_tables (rho : ByteArray) (G3 : Tab3) (G2 G2' : Tab2G st.params) (G5 G5' : Tab5F)
    (E : Blk → R) : step1KeysE Hb st r rho G3 (G2, G5, E) = step1KeysE Hb st r rho G3 (G2', G5', E) := by
  unfold step1KeysE seed1 ivPre1
  rw [recH_h3_tables (Hb := Hb) (st := st) (r := r) G3 G2 G2' G5 G5',
    recH_h4_tables (Hb := Hb) (st := st) (r := r) G3 G2 G2' G5 G5',
    recH_mu1_tables (Hb := Hb) (st := st) (r := r) G3 G2 G2' G5 G5']

/-- Step 1's `H₅` keys do not depend on `H₂³` or `H₅`. -/
lemma step1Keys5_tables (rho : ByteArray) (G3 : Tab3) (G2 G2' : Tab2G st.params) (G5 G5' : Tab5F)
    (E : Blk → R) : step1Keys5 Hb st r rho G3 (G2, G5, E) = step1Keys5 Hb st r rho G3 (G2', G5', E) := by
  unfold step1Keys5 seed1 ivPre1
  dsimp only
  rw [@vgIn5_h4 (icPrg (rowFn E)) _ _ (recH_h4_tables (Hb := Hb) (st := st) (r := r) G3 G2 G2' G5 G5'),
    recH_h3_tables (Hb := Hb) (st := st) (r := r) G3 G2 G2' G5 G5',
    recH_mu1_tables (Hb := Hb) (st := st) (r := r) G3 G2 G2' G5 G5']

/-- **Step 1 changes `H₅` only at its keys** (the body of `step1_rd5`, with the key set
explicit). -/
theorem step1_h5_congr (rho : ByteArray) (G3 : Tab3) (s : ShG R st.params) (G5 : Tab5F)
    (h : ∀ k ∈ step1Keys5 Hb st r rho G3 s, s.2.1 k = G5 k) :
    @step1 (icPrg (rowFn s.2.2)) (recH Hb (st1 st) r G3 s.1 G5) CrtGen.tables st r rho =
      @step1 (icPrg (rowFn s.2.2)) (recH Hb (st1 st) r G3 s.1 s.2.1) CrtGen.tables st r rho := by
  classical
  have hA := recHp_agreeOff_h5 (Hb := Hb) (st := st1 st) (w := r) (p := st.params) G3 s.1 G5 s.2.1
  have hmu : ∀ G5', (st1 st).mu1 (recH Hb (st1 st) r G3 s.1 G5') = (st1 st).mu1 Hb :=
    fun G5' => recHp_mu1 (p := st.params) (st := st1 st) (w := r) G3 s.1 G5'
  have h3 : ∀ G5', (recH Hb (st1 st) r G3 s.1 G5').hash .h3 = (recH Hb (st1 st) r G3 s.1 s.2.1).hash .h3 :=
    fun G5' => (recHp_h3 (p := st.params) (st := st1 st) (w := r) G3 s.1 G5').trans
      (recHp_h3 (p := st.params) (st := st1 st) (w := r) G3 s.1 s.2.1).symm
  unfold step1
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

/-- **Step 1 is a consistent reader of `H₅` and the cipher**: a table that agrees with `s` on
step 1's keys (its `624` gate inputs, its tree's `4607` nodes), whatever its `H₂³`, has the same
keys and the same step-1 output. -/
theorem step1_cons (hHb : HashesWF Hb) (rho : ByteArray) (G3 : Tab3) (s s' : ShG R st.params)
    (h5 : ∀ k ∈ step1Keys5 Hb st r rho G3 s, s.2.1 k = s'.2.1 k)
    (hE : ∀ k ∈ step1KeysE Hb st r rho G3 s, s.2.2 k = s'.2.2 k) :
    step1Keys5 Hb st r rho G3 s' = step1Keys5 Hb st r rho G3 s ∧
      step1KeysE Hb st r rho G3 s' = step1KeysE Hb st r rho G3 s ∧
      @step1 (icPrg (rowFn s'.2.2)) (recH Hb (st1 st) r G3 s'.1 s'.2.1) CrtGen.tables st r rho =
        @step1 (icPrg (rowFn s.2.2)) (recH Hb (st1 st) r G3 s.1 s.2.1) CrtGen.tables st r rho := by
  obtain ⟨G2, G5, E⟩ := s
  obtain ⟨G2', G5', E'⟩ := s'
  have hs : (seed1 (recH Hb (st1 st) r G3 G2 G5) st r rho).size = 16 := by
    rw [seed1, ByteArray.size_extract, recH_wf (st := st1 st) (w := r) hHb G3 G2 G5]; rfl
  have hN : NodesAgree (rowFn E) (rowFn E') (seed1 (recH Hb (st1 st) r G3 G2 G5) st r rho)
      ((recH Hb (st1 st) r G3 G2 G5).hash .h4 ((ivPre1 (recH Hb (st1 st) r G3 G2 G5) st r rho ++
        (st1 st).mu1 (recH Hb (st1 st) r G3 G2 G5)).push 4)) := fun n hn _ =>
    rowFn_congr (hE _ (mem_image.2 ⟨n, mem_range.2 hn, rfl⟩))
  -- the cipher: `(G2, G5, E) → (G2, G5, E')`
  have eE : step1KeysE Hb st r rho G3 (G2, G5, E') = step1KeysE Hb st r rho G3 (G2, G5, E) := by
    unfold step1KeysE
    dsimp only
    refine Finset.image_congr fun n hn => ?_
    exact congrArg (blk 16) (treeNode_ic_congr hN n (mem_range.1 (Finset.mem_coe.1 hn))).symm
  have e5 : step1Keys5 Hb st r rho G3 (G2, G5, E') = step1Keys5 Hb st r rho G3 (G2, G5, E) := by
    unfold step1Keys5
    dsimp only
    rw [vgIn5_ic_congr _ _ _ _ _ hs hN]
  have eS : @step1 (icPrg (rowFn E')) (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r rho =
      @step1 (icPrg (rowFn E)) (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r rho := by
    unfold step1
    rw [@voleGen_eq_voleGenAt (icPrg (rowFn E')), @voleGen_eq_voleGenAt (icPrg (rowFn E))]
    exact (voleGenAt_ic_congr _ _ _ _ _ _ _ hs hN).symm
  -- `H₅`: `(G2, G5, E') → (G2, G5', E')`
  have eS5 : @step1 (icPrg (rowFn E')) (recH Hb (st1 st) r G3 G2 G5') CrtGen.tables st r rho =
      @step1 (icPrg (rowFn E')) (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r rho :=
    step1_h5_congr (s := (G2, G5, E')) rho G3 G5' fun k hk => h5 k (by rw [← e5]; exact hk)
  -- `H₂³`: `(G2, G5', E') → (G2', G5', E')`
  have eS2 : @step1 (icPrg (rowFn E')) (recH Hb (st1 st) r G3 G2' G5') CrtGen.tables st r rho =
      @step1 (icPrg (rowFn E')) (recH Hb (st1 st) r G3 G2 G5') CrtGen.tables st r rho :=
    @step1_agreeOff_h23 (icPrg (rowFn E')) _ _ (recH_agreeOff_h23 (Hb := Hb) (st := st1 st) (w := r)
      G3 G2' G2 G5') CrtGen.tables st r rho
  refine ⟨?_, ?_, ?_⟩
  · rw [step1Keys5_tables rho G3 G2' G2 G5' G5 E', e5]
  · rw [step1KeysE_tables rho G3 G2' G2 G5' G5 E', eE]
  · rw [eS2, eS5, eS]

end Step1

/-! ## The single-phase prover is a consistent reader -/

section Real

variable {R : Type} [CipherRow R] {Hb : Hashes} {st : Statement} {w : ByteArray}

/-- The prover's cipher keys do not depend on `H₂³` or `H₅`. -/
lemma realKeysE_tables (rho : ByteArray) (G3 : Tab3) (G2 G2' : Tab2G st.params) (G5 G5' : Tab5F)
    (E : Blk → R) :
    realKeysE st.params Hb st w rho G3 (G2, G5, E) = realKeysE st.params Hb st w rho G3 (G2', G5', E) := by
  unfold realKeysE rSeed rIv
  simp only [recHp_h3, recHp_h4, recHp_mu1]

/-- The prover's `H₅` keys do not depend on `H₂³` or `H₅`. -/
lemma realKeys5_tables (rho : ByteArray) (G3 : Tab3) (G2 G2' : Tab2G st.params) (G5 G5' : Tab5F)
    (E : Blk → R) :
    realKeys5 st.params Hb st w rho G3 (G2, G5, E) = realKeys5 st.params Hb st w rho G3 (G2', G5', E) := by
  unfold realKeys5 rSeed
  rw [@vgIn5_h4 (icPrg (rowFn E)) (recHp st.params Hb st w G3 G2 G5) (recHp st.params Hb st w G3 G2' G5')
    (by rw [recHp_h4, recHp_h4])]
  simp only [recHp_h3, recHp_mu1]

/-- The prover's tree nodes agree for two cipher tables that agree at its cipher keys. -/
lemma realNodes_agree (s : ShG R st.params) (rho : ByteArray) (G3 : Tab3) (E' : Blk → R)
    (hE : ∀ k ∈ realKeysE st.params Hb st w rho G3 s, s.2.2 k = E' k) :
    NodesAgree (rowFn s.2.2) (rowFn E') (rSeed (recHp st.params Hb st w G3 s.1 s.2.1) st w rho)
      (rIv (recHp st.params Hb st w G3 s.1 s.2.1) st w rho) := fun n hn _ =>
  rowFn_congr (hE _ (mem_image.2 ⟨n, mem_range.2 hn, rfl⟩))

lemma rSeed_size (hHb : HashesWF Hb) (rho : ByteArray) (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5F) :
    (rSeed (recHp st.params Hb st w G3 G2 G5) st w rho).size = 16 := by
  rw [rSeed, ByteArray.size_extract, recHp_eq, recH_wf hHb]; rfl

/-- **The prover's keys under a change of the cipher at its cipher keys.** -/
lemma realKeys_cipher (hHb : HashesWF Hb) (s : ShG R st.params) (rho : ByteArray) (G3 : Tab3)
    (E' : Blk → R) (hE : ∀ k ∈ realKeysE st.params Hb st w rho G3 s, s.2.2 k = E' k) :
    realKeysE st.params Hb st w rho G3 (s.1, s.2.1, E') = realKeysE st.params Hb st w rho G3 s ∧
      realKeys5 st.params Hb st w rho G3 (s.1, s.2.1, E') = realKeys5 st.params Hb st w rho G3 s := by
  have hN := realNodes_agree s rho G3 E' hE
  have hs := rSeed_size (w := w) hHb rho G3 s.1 s.2.1
  refine ⟨?_, ?_⟩
  · unfold realKeysE
    refine Finset.image_congr fun n hn => ?_
    exact congrArg (blk 16) (treeNode_ic_congr hN n (mem_range.1 (Finset.mem_coe.1 hn))).symm
  · unfold realKeys5
    have hN' : NodesAgree (rowFn s.2.2) (rowFn E') (rSeed (recHp st.params Hb st w G3 s.1 s.2.1) st w rho)
        ((recHp st.params Hb st w G3 s.1 s.2.1).hash .h4
          ((((recHp st.params Hb st w G3 s.1 s.2.1).hash .h3 ((w.extract 0 st.params.witnessBytes ++
            st.mu1 Hb ++ rho).push 3)).extract 16 32 ++ st.mu1 Hb).push 4)) := by
      have := hN
      unfold rIv at this
      rwa [recHp_mu1] at this
    rw [vgIn5_ic_congr _ _ _ _ _ hs hN']

/-- **The prover changes the cipher only at its keys** (the body of `realROb_rdE`, with the key
set explicit). -/
theorem realROb_E_congr (hHb : HashesWF Hb) (rho : ByteArray) (G3 : Tab3) (s : ShG R st.params)
    (E : Blk → R) (h : ∀ k ∈ realKeysE st.params Hb st w rho G3 s, s.2.2 k = E k) :
    realROb st.params Hb st w rho G3 (s.1, s.2.1, E) = realROb st.params Hb st w rho G3 s := by
  have hs := rSeed_size (w := w) hHb rho G3 s.1 s.2.1
  unfold realROb Prover.prove
  dsimp only
  rw [@voleGen_eq_voleGenAt (icPrg (rowFn E)), @voleGen_eq_voleGenAt (icPrg (rowFn s.2.2))]
  refine congrArg _ (voleGenAt_ic_congr _ _ _ _ _ _ _ hs fun n hn _ => ?_).symm
  exact rowFn_congr (h _ (mem_image.2 ⟨n, mem_range.2 hn, rfl⟩))

/-- **The prover changes `H₅` only at its keys** (the body of `realROb_rd5`). -/
theorem realROb_h5_congr (rho : ByteArray) (G3 : Tab3) (s : ShG R st.params) (G5 : Tab5F)
    (h : ∀ k ∈ realKeys5 st.params Hb st w rho G3 s, s.2.1 k = G5 k) :
    realROb st.params Hb st w rho G3 (s.1, G5, s.2.2) = realROb st.params Hb st w rho G3 s := by
  classical
  have hA := recHp_agreeOff_h5 (Hb := Hb) (st := st) (w := w) (p := st.params) G3 s.1 G5 s.2.1
  unfold realROb Prover.prove
  dsimp only
  rw [@voleGen_eq_voleGenAt (icPrg (rowFn s.2.2)), @voleGen_eq_voleGenAt (icPrg (rowFn s.2.2)),
    proveCommit_agreeOff_h5 hA, recHp_mu1, recHp_mu1, recHp_h3, recHp_h3]
  refine congrArg _ (@voleGenAt_h5_congr (icPrg (rowFn s.2.2)) _ _ hA _ _ _ _ _ _ _ fun x hx => ?_)
  rw [@vgIn5_agreeOff (icPrg (rowFn s.2.2)) _ _ hA] at hx
  refine withTable_h5_congr _ fun hs => (h _ (mem_image.2 ⟨x, ?_, rfl⟩)).symm
  rw [List.mem_toFinset]
  simpa only [realKeys5, rSeed, recHp_mu1, recHp_h3] using hx

lemma h3_extract_size (hHb : HashesWF Hb) (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5F) (x : ByteArray)
    (a b : ℕ) (hb : b ≤ 32) :
    (((recH Hb st w G3 G2 G5).hash .h3 x).extract a b).size = b - a := by
  rw [ByteArray.size_extract, recH_wf hHb]
  show min b 32 - a = b - a
  rw [Nat.min_eq_left hb]

/-- The prover's root seed is the first half of its slice's answer. -/
lemma rSeed_eq_split (hHb : HashesWF Hb) (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5F) (ρ : Bytes 16) :
    rSeed (recHp st.params Hb st w G3 G2 G5) st w (ba ρ) = ba (splitSeed (G3 ρ)).1 := by
  have h := congrArg (fun x => ba x.1) (recH_h3Seed (Hb := Hb) (st := st) (w := w) G3 G2 G5 ρ)
  simp only [h3Seed] at h
  rw [← h, ba_blk_of_size (h3_extract_size hHb G3 G2 G5 _ 0 16 (by omega))]
  rfl

/-- The prover's `iv_pre` is the second half of its slice's answer. -/
lemma ivPre_eq_split (hHb : HashesWF Hb) (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5F) (ρ : Bytes 16) :
    ((recHp st.params Hb st w G3 G2 G5).hash .h3 ((w.extract 0 st.params.witnessBytes ++ st.mu1 Hb ++
      ba ρ).push 3)).extract 16 32 = ba (splitSeed (G3 ρ)).2 := by
  have h := congrArg (fun x => ba x.2) (recH_h3Seed (Hb := Hb) (st := st) (w := w) G3 G2 G5 ρ)
  simp only [h3Seed, recH_mu1] at h
  rw [← h, ba_blk_of_size (h3_extract_size hHb G3 G2 G5 _ 16 32 (by omega))]
  rfl

lemma rec5_agreeOff (G5 G5' : Tab5F) : (rec5 Hb G5).AgreeOff .h5 (rec5 Hb G5') := fun k hk =>
  (Hb.agreeOff_withTable .h5 enc5 G5 k hk).symm.trans (Hb.agreeOff_withTable .h5 enc5 G5' k hk)

/-- `chal2 ‖ qs_check ‖ ã` does not read `H₅`. -/
lemma realPre_h5 {Hs Hs' : Hashes} (h : Hs.AgreeOff .h5 Hs') (s : Prover.Pending) :
    realPre Hs st s w = realPre Hs' st s w := by
  simp only [realPre, realC2, h.chal2 (by decide), h.muDelayed (by decide) st,
    h.combBytes (fun _ => nofun) st]

/-- **The prover's grinding prefix is read off the prover's `H₅` and cipher keys**: a table that
agrees with `s` there has the same prefix. -/
theorem preRO_cons (hHb : HashesWF Hb) (ρ : Bytes 16) (G3 : Tab3) (s : ShG R st.params)
    (G2' : Tab2G st.params) (G5' : Tab5F) (E' : Blk → R)
    (h5 : ∀ k ∈ realKeys5 st.params Hb st w (ba ρ) G3 s, s.2.1 k = G5' k)
    (hE : ∀ k ∈ realKeysE st.params Hb st w (ba ρ) G3 s, s.2.2 k = E' k) :
    preRO Hb st w ρ G3 (G2', G5', E') = preRO Hb st w ρ G3 s := by
  obtain ⟨G2, G5, E⟩ := s
  have hs : (ba (splitSeed (G3 ρ)).1).size = 16 := size_ba _
  -- the cipher, at `G5'`
  have hN := realNodes_agree (G2, G5, E) (ba ρ) G3 E' hE
  rw [rSeed_eq_split hHb] at hN
  unfold rIv at hN
  rw [recHp_h4, recHp_mu1, ivPre_eq_split hHb] at hN
  have eE : @preR (icPrg (rowFn E')) Hb CrtGen.tables st w G5' (splitSeed (G3 ρ)) =
      @preR (icPrg (rowFn E)) Hb CrtGen.tables st w G5' (splitSeed (G3 ρ)) := by
    unfold preR prePrefix pendAt
    have := voleGenAt_ic_congr (E := rowFn E) (E' := rowFn E') (rec5 Hb G5') CrtGen.tables st.params
      (st.mu1 (rec5 Hb G5')) (w.extract 0 st.params.witnessBytes) (ba (splitSeed (G3 ρ)).2) st.binder1 hs
      (by rw [rec5_h4, rec5_mu1]; exact hN)
    rw [← this]
  -- `H₅`, at `E`
  have e5 : @preR (icPrg (rowFn E)) Hb CrtGen.tables st w G5' (splitSeed (G3 ρ)) =
      @preR (icPrg (rowFn E)) Hb CrtGen.tables st w G5 (splitSeed (G3 ρ)) := by
    unfold preR prePrefix pendAt
    rw [rec5_mu1, rec5_mu1, realPre_h5 (rec5_agreeOff G5' G5)]
    refine congrArg (fun P => realPre (rec5 Hb G5) st P w) ?_
    refine @voleGenAt_h5_congr (icPrg (rowFn E)) _ _ (rec5_agreeOff G5' G5) _ _ _ _ _ _ _ fun x hx => ?_
    refine withTable_h5_congr _ fun hsz => (h5 _ (mem_image.2 ⟨x, ?_, rfl⟩)).symm
    rw [List.mem_toFinset]
    unfold rSeed
    rw [@vgIn5_h4 (icPrg (rowFn E)) (recHp st.params Hb st w G3 G2 G5) (rec5 Hb G5')
      (by rw [recHp_h4, rec5_h4]), recHp_mu1]
    rw [show ((recHp st.params Hb st w G3 G2 G5).hash .h3 ((w.extract 0 st.params.witnessBytes ++
        st.mu1 Hb ++ ba ρ).push 3)).extract 0 16 = ba (splitSeed (G3 ρ)).1 by
      have := rSeed_eq_split (w := w) hHb G3 G2 G5 ρ
      unfold rSeed at this
      rwa [recHp_mu1] at this, ivPre_eq_split hHb]
    exact hx
  show @preR (icPrg (rowFn E')) Hb CrtGen.tables st w G5' (splitSeed (G3 ρ)) =
    @preR (icPrg (rowFn E)) Hb CrtGen.tables st w G5 (splitSeed (G3 ρ))
  rw [eE, e5]

/-- **The prover changes `H₂³` only at the grinding points of its prefix.** -/
theorem realRO_h23_congr {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (ρ : Bytes 16) (G3 : Tab3) (s : ShG R st.params) (G2' : Tab2G st.params)
    (h : ∀ c, s.1 (key2 st.params (preRO Hb st w ρ G3 s) c) = G2' (key2 st.params (preRO Hb st w ρ G3 s) c)) :
    realRO st.params Hb st w ρ G3 (G2', s.2) = realRO st.params Hb st w ρ G3 s := by
  rw [realRO_eq, realRO_eq]
  dsimp only
  rw [@prove_recH_eq (icPrg (rowFn s.2.2)) Hb st w cs hzk hHb hlab,
    @prove_recH_eq (icPrg (rowFn s.2.2)) Hb st w cs hzk hHb hlab]
  have e : G2' ∘ key2 st.params (@preR (icPrg (rowFn s.2.2)) Hb CrtGen.tables st w s.2.1
      (splitSeed (G3 ρ))) = s.1 ∘ key2 st.params (@preR (icPrg (rowFn s.2.2)) Hb CrtGen.tables st w s.2.1
      (splitSeed (G3 ρ))) :=
    funext fun c => (h c).symm
  rw [e]

/-- **The single-phase prover is a consistent reader**: of `H₅` at its `624` gate inputs, of the
cipher at its tree's `4607` nodes, of `H₂³` at the `nGrind` grinding points of its prefix, and of
no slice key (its own `H₃` slice is fixed). -/
theorem realRO_sreads {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (ρ : Bytes 16) (G3 : Tab3) :
    SReads st.params (fun t : Tb R st.params => realRO st.params Hb st w ρ G3 t.2) 0 nGrind 624 4607 := by
  classical
  refine ⟨fun t => (∅, univ.image (key2 st.params (preRO Hb st w ρ G3 t.2)),
    realKeys5 st.params Hb st w (ba ρ) G3 t.2, realKeysE st.params Hb st w (ba ρ) G3 t.2),
    fun t t' h => ?_, fun t => ⟨by simp, ?_, ?_, ?_⟩⟩
  · obtain ⟨-, h2, h5, hE⟩ := h
    obtain ⟨g, G2, G5, E⟩ := t
    obtain ⟨g', G2', G5', E'⟩ := t'
    dsimp only at h2 h5 hE ⊢
    obtain ⟨cE, c5⟩ := realKeys_cipher (w := w) hHb (G2, G5, E) (ba ρ) G3 E' hE
    have kE : realKeysE st.params Hb st w (ba ρ) G3 (G2', G5', E') =
        realKeysE st.params Hb st w (ba ρ) G3 (G2, G5, E) := by
      rw [realKeysE_tables (ba ρ) G3 G2' G2 G5' G5 E', cE]
    have k5 : realKeys5 st.params Hb st w (ba ρ) G3 (G2', G5', E') =
        realKeys5 st.params Hb st w (ba ρ) G3 (G2, G5, E) := by
      rw [realKeys5_tables (ba ρ) G3 G2' G2 G5' G5 E', c5]
    have kP := preRO_cons (w := w) hHb ρ G3 (G2, G5, E) G2' G5' E' h5 hE
    refine ⟨by rw [kE, k5, kP], ?_⟩
    -- the cipher: `(G2', G5', E') → (G2', G5', E)`
    have o1 : realRO st.params Hb st w ρ G3 (G2', G5', E') = realRO st.params Hb st w ρ G3 (G2', G5', E) :=
      realROb_E_congr hHb (ba ρ) G3 (G2', G5', E) E' fun k hk => (hE k (by
        rwa [realKeysE_tables (ba ρ) G3 G2' G2 G5' G5 E] at hk))
    -- `H₅`: `(G2', G5', E) → (G2', G5, E)`
    have o2 : realRO st.params Hb st w ρ G3 (G2', G5', E) = realRO st.params Hb st w ρ G3 (G2', G5, E) :=
      realROb_h5_congr (ba ρ) G3 (G2', G5, E) G5' fun k hk => (h5 k (by
        rwa [realKeys5_tables (ba ρ) G3 G2' G2 G5 G5 E] at hk))
    -- `H₂³`: `(G2', G5, E) → (G2, G5, E)`
    have o3 : realRO st.params Hb st w ρ G3 (G2', G5, E) = realRO st.params Hb st w ρ G3 (G2, G5, E) :=
      realRO_h23_congr hzk hHb hlab ρ G3 (G2, G5, E) G2' fun c =>
        h2 _ (mem_image.2 ⟨c, mem_univ _, rfl⟩)
    rw [o1, o2, o3]
  · exact card_image_le.trans (by rw [card_univ, Fintype.card_fin])
  · refine card_image_le.trans ((List.toFinset_card_le _).trans (le_of_eq ?_))
    exact @vgIn5_length (icPrg (rowFn t.2.2.2)) _ _ _ _ _ _
  · exact card_image_le.trans (le_of_eq (by rw [card_range]; rfl))

end Real

/-- `noHitProb ≤ 2⁻¹²⁸` (from `noHitProb_le`, without evaluating `2^{−2¹⁵}`). -/
lemma noHitProb_le_128 : noHitProb ≤ 1 / 2 ^ 128 := by
  have h1 : (1 / 2 : ℝ) ^ (2 ^ 15) ≤ (1 / 2) ^ 128 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (show 128 ≤ 2 ^ 15 by norm_num)
  have h2 : (1 / 2 : ℝ) ^ 128 = 1 / 2 ^ 128 := by rw [one_div_pow]
  exact noHitProb_le.trans (h1.trans h2.le)

end VoleMole.ZK.Sim

namespace VoleMole.Privacy

/-- **The hybrid argument over `n` steps**: if consecutive hybrids differ by at most `ε k`, the
end points differ by at most `∑ ε k`. -/
theorem abs_sub_le_sum_of_steps (P ε : ℕ → ℝ) (n : ℕ) (h : ∀ k < n, |P k - P (k + 1)| ≤ ε k) :
    |P 0 - P n| ≤ ∑ k ∈ range n, ε k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h1 := ih fun k hk => h k (by omega)
    have h2 := h n (by omega)
    have := abs_sub_le (P 0) (P n) (P (n + 1))
    linarith

/-- **The hybrid argument over `n` steps with a uniform bound**: `n·ε`. -/
theorem abs_sub_le_mul_of_steps (P : ℕ → ℝ) (ε : ℝ) (n : ℕ) (h : ∀ k < n, |P k - P (k + 1)| ≤ ε) :
    |P 0 - P n| ≤ n * ε := by
  have := abs_sub_le_sum_of_steps P (fun _ => ε) n h
  simpa using this

end VoleMole.Privacy

