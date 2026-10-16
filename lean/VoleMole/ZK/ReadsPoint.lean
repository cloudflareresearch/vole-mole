import VoleMole.ZK.ReadsMany

/-!
# Step 1 reads the cipher at points, not rows

`ZK/ReadsMany.lean` (`step1_cons`) shows that step 1 of the prover is a consistent reader of the
cipher **rows** of its tree's `4607` nodes. Every PRG call of step 1 uses the proof's `iv`, so
it reads those rows only at the CTR blocks `ctrBlock iv c t` (`prgR_congr`): a much smaller set of
**points** (key, input). This file restates the congruences at that level:

* `PtsAgree E E' k iv`: the tables agree at key `k` on every CTR block of `iv`;
* `icPrg_congrP`, `treeNode_ic_congrP`, `commit_ic_congrP`, `voleGenAt_ic_congrP`,
  `vgIn5_ic_congrP`: the tree, the commitment, the whole of step 1's VOLE generation and its `H₅`
  inputs depend on the cipher only at the points `(node, ctrBlock iv c t)` of the tree's nodes;
* **`step1_consP`**: a table that agrees with `s` on step 1's `624` `H₅` keys and at the points of
  its tree's nodes (whatever its `H₂³` and its rows elsewhere) has the same keys and the same
  step-1 output.

Two proofs whose `iv`s have different second lanes (`getLE32 iv 4`) read disjoint sets of points
(`lane1_of_ctrBlock_eq`), whatever their keys: this is what makes the honest sessions of the
many-session games interfere only through a key **and** an input collision
(`Privacy/PomFRITLin.lean`).
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## Agreement at the CTR points of an `iv` -/

/-- **The tables agree at key `k` on every CTR block of `iv`.** -/
def PtsAgree (E E' : Cipher) (k : Blk) (iv : ByteArray) : Prop :=
  ∀ c t : UInt32, E k (blk 16 (AES.ctrBlock iv c t)) = E' k (blk 16 (AES.ctrBlock iv c t))

/-- The CTR blocks of `iv`. -/
def InY (iv : ByteArray) (z : Blk) : Prop := ∃ c t : UInt32, z = blk 16 (AES.ctrBlock iv c t)

lemma PtsAgree.of_rows {E E' : Cipher} {k : Blk} (h : E k = E' k) (iv : ByteArray) :
    PtsAgree E E' k iv := fun c t => by rw [h]

lemma PtsAgree.of_inY {E E' : Cipher} {k : Blk} {iv : ByteArray}
    (h : ∀ z, InY iv z → E k z = E' k z) : PtsAgree E E' k iv := fun c t => h _ ⟨c, t, rfl⟩

/-- **The ideal-cipher PRG reads its key's row only at the CTR blocks of its `iv`.** -/
lemma icPrg_congrP {E E' : Cipher} {key iv : ByteArray}
    (h : key.size = 16 → PtsAgree E E' (blk 16 key) iv) (t c : UInt32) (n : ℕ) :
    @HasPrg.prg (icPrg E) key iv t c n = @HasPrg.prg (icPrg E') key iv t c n := by
  show icPrgF E key iv t c n = icPrgF E' key iv t c n
  unfold icPrgF
  split_ifs with hk
  · exact prgR_congr fun j _ => h hk _ _
  · rfl

/-- The CTR blocks of `iv` all have `iv`'s second lane. -/
theorem lane1_of_ctrBlock_eq {iv iv' : ByteArray} {c t c' t' : UInt32}
    (h : blk 16 (AES.ctrBlock iv c t) = blk 16 (AES.ctrBlock iv' c' t')) :
    AES.getLE32 iv 4 = AES.getLE32 iv' 4 := by
  have h' : AES.ctrBlock iv c t = AES.ctrBlock iv' c' t' :=
    blk16_inj (ctrBlock_size _ _ _) (ctrBlock_size _ _ _) h
  have := congrArg (fun b => lanes b 1) h'
  simp only [lanes_ctrBlock] at this
  simp only [Seed.Commitments.ctrInput, lanes] at this
  exact UInt32.toNat_inj.1 (Seed.Commitments.natCast_lane_inj (UInt32.toNat_lt _) (UInt32.toNat_lt _)
    (by simpa using this))

/-! ## The tree, the commitment and step 1 at points -/

section ProverP

variable {E E' : Cipher} {seed iv : ByteArray}

/-- The tables agree at the points of the nodes of the GGM tree from `seed` (computed with `E`). -/
def NodesAgreeP (E E' : Cipher) (seed iv : ByteArray) : Prop :=
  ∀ n < BAVC.numNodes, (@treeNode (icPrg E) seed iv n).size = 16 →
    PtsAgree E E' (blk 16 (@treeNode (icPrg E) seed iv n)) iv

/-- **The tree reads the cipher only at its nodes' points.** -/
theorem treeNode_ic_congrP (h : NodesAgreeP E E' seed iv) :
    ∀ n < BAVC.numNodes, @treeNode (icPrg E) seed iv n = @treeNode (icPrg E') seed iv n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | m
    · rw [@treeNode.eq_1 (icPrg E), @treeNode.eq_1 (icPrg E')]
    · rw [@treeNode.eq_2 (icPrg E), @treeNode.eq_2 (icPrg E'), ← ih (m / 2) (by omega) (by omega)]
      unfold BAVC.children
      rw [icPrg_congrP (h (m / 2) (by omega))]

theorem expandTree_ic_congrP (hs : seed.size = 16) (h : NodesAgreeP E E' seed iv) :
    @BAVC.expandTree (icPrg E) seed iv = @BAVC.expandTree (icPrg E') seed iv := by
  have s1 := (@expandTree_spec (icPrg E) seed iv hs).1
  have s2 := (@expandTree_spec (icPrg E') seed iv hs).1
  refine Array.ext (by rw [s1, s2]) fun i h1 h2 => ?_
  have hi : i < BAVC.numNodes := by rwa [s1] at h1
  rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, @expandTree_get (icPrg E) _ _ _ hi,
    @expandTree_get (icPrg E') _ _ _ hi]
  exact treeNode_ic_congrP h i hi

/-- **The commitment reads the cipher only at the tree's points.** -/
theorem commit_ic_congrP (hs : seed.size = 16) (h : NodesAgreeP E E' seed iv) :
    @BAVC.commit (icPrg E) seed iv = @BAVC.commit (icPrg E') seed iv := by
  unfold BAVC.commit
  dsimp only
  rw [expandTree_ic_congrP hs h, @leavesOf_eq (icPrg E), @leavesOf_eq (icPrg E')]
  simp only [Prod.mk.injEq, BAVC.Leaves.mk.injEq, true_and]
  apply congrArg (List.foldl (· ++ ·) ByteArray.empty)
  refine pieces_congr fun i hi j hj => ?_
  split_ifs
  · rfl
  · have hn := treePos_lt hi hj
    rw [@expandTree_get (icPrg E') _ _ _ hn, ← treeNode_ic_congrP h _ hn]
    exact icPrg_congrP (h _ hn) _ _ _

theorem smallVoleUWords_ic_congrP (p : Params) (iv : ByteArray) (i : ℕ) (key : ℕ → ByteArray)
    (h : ∀ j < 2 ^ BAVC.kOf i, (key j).size = 16 → PtsAgree E E' (blk 16 (key j)) iv) :
    @Prover.smallVoleUWords (icPrg E) p iv i key = @Prover.smallVoleUWords (icPrg E') p iv i key := by
  unfold Prover.smallVoleUWords
  refine List.foldl_ext _ _ _ fun acc j hj => ?_
  simp only [prgWords]
  rw [icPrg_congrP (h j (List.mem_range.1 hj))]

theorem uMaskOf_ic_congrP (p : Params) (T : CrtTables) (us : Array (Array UInt64))
    (h : seed.size = 16 → PtsAgree E E' (blk 16 seed) iv) :
    @Prover.uMaskOf (icPrg E) p T seed iv us = @Prover.uMaskOf (icPrg E') p T seed iv us := by
  unfold Prover.uMaskOf
  rw [icPrg_congrP h]

/-- **The VOLE expansion reads the cipher only at the leaf keys' points.** -/
theorem convertToVoleAt_ic_congrP (p : Params) (dbit : ℕ → Bool) (corr : ℕ → ByteArray)
    (iv : ByteArray) (key : ℕ → ℕ → ByteArray)
    (h : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i, j ≠ BAVC.hiddenIndex dbit i →
      (key i j).size = 16 → PtsAgree E E' (blk 16 (key i j)) iv) :
    @convertToVoleAt (icPrg E) p dbit corr iv key = @convertToVoleAt (icPrg E') p dbit corr iv key := by
  have ht : ∀ i < BAVC.tau, @treeColumns (icPrg E) p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i) =
      @treeColumns (icPrg E') p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i) := by
    intro i hi
    have hp : @prgOuts (icPrg E) p iv i (BAVC.hiddenIndex dbit i) (key i) =
        @prgOuts (icPrg E') p iv i (BAVC.hiddenIndex dbit i) (key i) := by
      unfold prgOuts
      refine Array.map_congr_left fun j hj => ?_
      have hj := Array.mem_range.1 hj
      split_ifs with hjd
      · rfl
      · simp only [prgWords]
        rw [icPrg_congrP (fun hs => h i hi j hj (by simpa using hjd) hs)]
    simp only [treeColumns, hp]
  have htr : ((Array.range BAVC.tau).map fun i =>
      @treeColumns (icPrg E) p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i)) =
      (Array.range BAVC.tau).map fun i =>
        @treeColumns (icPrg E') p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i) :=
    Array.map_congr_left fun i hi => ht i (Array.mem_range.1 hi)
  simp only [convertToVoleAt, htr]

/-- **Step 1 reads the cipher only at its tree's points.** -/
theorem voleGenAt_ic_congrP (Hs : Hashes) (T : CrtTables) (p : Params)
    (mu1 wPrefix ivPre binder1 : ByteArray) (hs : seed.size = 16)
    (h : NodesAgreeP E E' seed (Hs.hash .h4 ((ivPre ++ mu1).push 4))) :
    @voleGenAt (icPrg E) Hs T p mu1 wPrefix seed ivPre binder1 =
      @voleGenAt (icPrg E') Hs T p mu1 wPrefix seed ivPre binder1 := by
  set iv := Hs.hash .h4 ((ivPre ++ mu1).push 4) with hiv
  have hc := commit_ic_congrP hs h
  have hk : ∀ i j, i < BAVC.tau → j < 2 ^ BAVC.kOf i →
      leafKey (@BAVC.commit (icPrg E') seed iv).2 i j = @treeNode (icPrg E) seed iv (BAVC.treePos i j) :=
    fun i j hi hj => by
      rw [@leafKey_commit (icPrg E') seed iv hs i j hi hj, treeNode_ic_congrP h _ (treePos_lt hi hj)]
  have hus : (Array.range BAVC.tau).map (fun i =>
      @Prover.smallVoleUWords (icPrg E) p iv i (leafKey (@BAVC.commit (icPrg E') seed iv).2 i)) =
      (Array.range BAVC.tau).map (fun i =>
        @Prover.smallVoleUWords (icPrg E') p iv i (leafKey (@BAVC.commit (icPrg E') seed iv).2 i)) :=
    Array.map_congr_left fun i hi => smallVoleUWords_ic_congrP _ _ _ _ fun j hj hsz => by
      have hi' := Array.mem_range.1 hi
      rw [hk i j hi' hj] at hsz ⊢
      exact h _ (treePos_lt hi' hj) hsz
  have hcols : @Prover.senderColumns (icPrg E) p iv (leafKey (@BAVC.commit (icPrg E') seed iv).2) =
      @Prover.senderColumns (icPrg E') p iv (leafKey (@BAVC.commit (icPrg E') seed iv).2) := by
    unfold Prover.senderColumns
    refine convertToVoleAt_ic_congrP _ _ _ _ _ fun i hi j hj _ hsz => ?_
    rw [hk i j hi hj] at hsz ⊢
    exact h _ (treePos_lt hi hj) hsz
  have hum : ∀ us, @Prover.uMaskOf (icPrg E) p T seed iv us =
      @Prover.uMaskOf (icPrg E') p T seed iv us := fun us =>
    uMaskOf_ic_congrP p T us fun hsz => by
      have := h 0 (by decide)
      rw [@treeNode.eq_1 (icPrg E)] at this
      exact this hsz
  simp only [voleGenAt, ← hiv, hc, hus, hcols, hum]

/-- **Step 1's `H₅` inputs read the cipher only at the tree's points.** -/
theorem vgIn5_ic_congrP (Hs : Hashes) (T : CrtTables) (p : Params)
    (mu1 ivPre : ByteArray) (hs : seed.size = 16)
    (h : NodesAgreeP E E' seed (Hs.hash .h4 ((ivPre ++ mu1).push 4))) :
    @vgIn5 (icPrg E) Hs T p mu1 seed ivPre = @vgIn5 (icPrg E') Hs T p mu1 seed ivPre := by
  set iv := Hs.hash .h4 ((ivPre ++ mu1).push 4) with hiv
  have hc := commit_ic_congrP hs h
  have hk : ∀ i j, i < BAVC.tau → j < 2 ^ BAVC.kOf i →
      leafKey (@BAVC.commit (icPrg E') seed iv).2 i j = @treeNode (icPrg E) seed iv (BAVC.treePos i j) :=
    fun i j hi hj => by
      rw [@leafKey_commit (icPrg E') seed iv hs i j hi hj, treeNode_ic_congrP h _ (treePos_lt hi hj)]
  have hus : (Array.range BAVC.tau).map (fun i =>
      @Prover.smallVoleUWords (icPrg E) p iv i (leafKey (@BAVC.commit (icPrg E') seed iv).2 i)) =
      (Array.range BAVC.tau).map (fun i =>
        @Prover.smallVoleUWords (icPrg E') p iv i (leafKey (@BAVC.commit (icPrg E') seed iv).2 i)) :=
    Array.map_congr_left fun i hi => smallVoleUWords_ic_congrP _ _ _ _ fun j hj hsz => by
      have hi' := Array.mem_range.1 hi
      rw [hk i j hi' hj] at hsz ⊢
      exact h _ (treePos_lt hi' hj) hsz
  have hcols : @Prover.senderColumns (icPrg E) p iv (leafKey (@BAVC.commit (icPrg E') seed iv).2) =
      @Prover.senderColumns (icPrg E') p iv (leafKey (@BAVC.commit (icPrg E') seed iv).2) := by
    unfold Prover.senderColumns
    refine convertToVoleAt_ic_congrP _ _ _ _ _ fun i hi j hj _ hsz => ?_
    rw [hk i j hi hj] at hsz ⊢
    exact h _ (treePos_lt hi hj) hsz
  simp only [vgIn5, vgCols, vgUPre, vgIv, ← hiv, hc, hus, hcols]

end ProverP

/-! ## Step 1 is a consistent reader of points -/

section Step1P

variable {R : Type} [CipherRow R] {Hb : Hashes} {st : Statement} {r : ByteArray}

/-- **The `iv` of step 1** (it depends on the slice and `H₄`, not on the shared tables). -/
noncomputable def step1Iv (Hb : Hashes) (st : Statement) (r rho : ByteArray) (G3 : Tab3)
    (s : ShG R st.params) : ByteArray :=
  (recH Hb (st1 st) r G3 s.1 s.2.1).hash .h4
    ((ivPre1 (recH Hb (st1 st) r G3 s.1 s.2.1) st r rho ++
      (st1 st).mu1 (recH Hb (st1 st) r G3 s.1 s.2.1)).push 4)

lemma step1Iv_tables (rho : ByteArray) (G3 : Tab3) (s s' : ShG R st.params) :
    step1Iv Hb st r rho G3 s' = step1Iv Hb st r rho G3 s := by
  unfold step1Iv ivPre1
  rw [recH_h3_tables (Hb := Hb) (st := st) (r := r) G3 s'.1 s.1 s'.2.1 s.2.1,
    recH_h4_tables (Hb := Hb) (st := st) (r := r) G3 s'.1 s.1 s'.2.1 s.2.1,
    recH_mu1_tables (Hb := Hb) (st := st) (r := r) G3 s'.1 s.1 s'.2.1 s.2.1]

/-- **Step 1 is a consistent reader of `H₅` and of the cipher's points**: a table that agrees with
`s` on step 1's `624` gate inputs and at the CTR points of its `iv` of its tree's `4607` nodes,
whatever its `H₂³` and its rows elsewhere, has the same keys and the same step-1 output. -/
theorem step1_consP (hHb : HashesWF Hb) (rho : ByteArray) (G3 : Tab3) (s s' : ShG R st.params)
    (h5 : ∀ k ∈ step1Keys5 Hb st r rho G3 s, s.2.1 k = s'.2.1 k)
    (hE : ∀ k ∈ step1KeysE Hb st r rho G3 s,
      PtsAgree (rowFn s.2.2) (rowFn s'.2.2) k (step1Iv Hb st r rho G3 s)) :
    step1Keys5 Hb st r rho G3 s' = step1Keys5 Hb st r rho G3 s ∧
      step1KeysE Hb st r rho G3 s' = step1KeysE Hb st r rho G3 s ∧
      @step1 (icPrg (rowFn s'.2.2)) (recH Hb (st1 st) r G3 s'.1 s'.2.1) CrtGen.tables st r rho =
        @step1 (icPrg (rowFn s.2.2)) (recH Hb (st1 st) r G3 s.1 s.2.1) CrtGen.tables st r rho := by
  obtain ⟨G2, G5, E⟩ := s
  obtain ⟨G2', G5', E'⟩ := s'
  have hs : (seed1 (recH Hb (st1 st) r G3 G2 G5) st r rho).size = 16 := by
    rw [seed1, ByteArray.size_extract, recH_wf (st := st1 st) (w := r) hHb G3 G2 G5]; rfl
  have hN : NodesAgreeP (rowFn E) (rowFn E') (seed1 (recH Hb (st1 st) r G3 G2 G5) st r rho)
      ((recH Hb (st1 st) r G3 G2 G5).hash .h4 ((ivPre1 (recH Hb (st1 st) r G3 G2 G5) st r rho ++
        (st1 st).mu1 (recH Hb (st1 st) r G3 G2 G5)).push 4)) := fun n hn _ =>
    hE _ (mem_image.2 ⟨n, mem_range.2 hn, rfl⟩)
  -- the cipher: `(G2, G5, E) → (G2, G5, E')`
  have eE : step1KeysE Hb st r rho G3 (G2, G5, E') = step1KeysE Hb st r rho G3 (G2, G5, E) := by
    unfold step1KeysE
    dsimp only
    refine Finset.image_congr fun n hn => ?_
    exact congrArg (blk 16) (treeNode_ic_congrP hN n (mem_range.1 (Finset.mem_coe.1 hn))).symm
  have e5 : step1Keys5 Hb st r rho G3 (G2, G5, E') = step1Keys5 Hb st r rho G3 (G2, G5, E) := by
    unfold step1Keys5
    dsimp only
    rw [vgIn5_ic_congrP _ _ _ _ _ hs hN]
  have eS : @step1 (icPrg (rowFn E')) (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r rho =
      @step1 (icPrg (rowFn E)) (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r rho := by
    unfold step1
    rw [@voleGen_eq_voleGenAt (icPrg (rowFn E')), @voleGen_eq_voleGenAt (icPrg (rowFn E))]
    exact (voleGenAt_ic_congrP _ _ _ _ _ _ _ hs hN).symm
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

end Step1P


/-! ## A non-root node of a GGM tree on a uniform cipher is uniform -/

section TreeUniform

/-- With nothing replaced, a node's value reads the cipher only at the inputs of the nodes on
its path. -/
lemma keyAt_congr_cols {K X : Type} {x : ℕ → X} {N : ℕ} (R : Fin N → X → K) (s : K)
    {E E' : K → X → K} :
    ∀ a, (∀ k b, b ≠ 0 → b ≤ a → E k (x b) = E' k (x b)) →
      IC.keyAt x N ∅ E R s a = IC.keyAt x N ∅ E' R s a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro h
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rfl
    · rw [IC.keyAt_pos (by omega), IC.keyAt_pos (by omega),
        IC.rowAt_of_not_mem (Finset.notMem_empty _), IC.rowAt_of_not_mem (Finset.notMem_empty _),
        ih _ (by omega) fun k b hb hba => h k b hb (by omega)]
      exact h _ a (by omega) le_rfl

lemma nN_eq : nN = 4607 := rfl

/-- **Different GGM nodes have different inputs.** -/
theorem xIn_inj (iv : ByteArray) {b m : ℕ} (hb0 : b ≠ 0) (hm0 : m ≠ 0) (hb : b < nN) (hm : m < nN)
    (h : xIn iv b = xIn iv m) : b = m := by
  have h' := blkCtr_inj iv h
  have h1 := zero_add_toUInt32_inj (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)) h'.1
  have h2 := congrArg UInt32.toNat h'.2
  rw [nN_eq] at hb hm
  rw [toNat_toUInt32 (by omega), toNat_toUInt32 (by omega)] at h2
  omega

/-- **A non-root node of the GGM tree from any seed, on a uniform cipher table, takes any given
value with probability `≤ 2⁻¹²⁸`**: its value is the parent's row at its input, and the parent's
value reads the cipher only at other inputs (the column of the node's input is fresh). -/
theorem pr_keyAt_eq_le (iv : ByteArray) (R : Fin nN → Blk → Blk) (seed : Blk) {m : ℕ}
    (hm0 : m ≠ 0) (hm : m < nN) (κ : Blk) :
    pr Cipher (fun E => IC.keyAt (xIn iv) nN ∅ E R seed m = κ) ≤ 1 / 2 ^ 128 := by
  classical
  set x₀ := xIn iv m
  let f : Cipher → Blk := fun E => IC.keyAt (xIn iv) nN ∅ E R seed ((m - 1) / 2)
  have hcol : ∀ E E' : Cipher, (∀ k z, z ≠ x₀ → E k z = E' k z) → f E = f E' := fun E E' h =>
    keyAt_congr_cols R seed _ fun k b hb hba => h k _ fun e =>
      absurd (xIn_inj iv hb hm0 (by omega) hm e) (by omega)
  let set : Cipher → Blk → Cipher := fun E k =>
    Function.update E (f E) (Function.update (E (f E)) x₀ k)
  have hoff : ∀ E k, ∀ k' z, z ≠ x₀ → set E k k' z = E k' z := fun E k k' z hz => by
    simp only [set]
    by_cases hk : k' = f E
    · subst hk; rw [Function.update_self, Function.update_of_ne hz]
    · rw [Function.update_of_ne hk]
  have hfs : ∀ E k, f (set E k) = f E := fun E k => hcol _ _ (hoff E k)
  have hval : ∀ E, IC.keyAt (xIn iv) nN ∅ E R seed m = E (f E) x₀ := fun E => by
    rw [IC.keyAt_pos hm0, IC.rowAt_of_not_mem (Finset.notMem_empty _)]
  have hf : ∀ E k, (fun E => E (f E) x₀) (set E k) = k := fun E k => by
    simp only [hfs, set, Function.update_self]
  have hss : ∀ E k k', set (set E k) k' = set E k' := fun E k k' => by
    simp only [set, hfs, Function.update_self, Function.update_idem]
  have hsf : ∀ E, set E (E (f E) x₀) = E := fun E => by
    simp only [set, Function.update_eq_self]
  have h := IC.pr_mem_reset_le (α := Cipher) (K := Blk) (fun E => E (f E) x₀) set hf hss hsf
    (fun _ => {κ}) (fun _ _ => rfl) (q := 1) (fun _ => (Finset.card_singleton κ).le)
  have e : pr Cipher (fun E => IC.keyAt (xIn iv) nN ∅ E R seed m = κ) =
      pr Cipher (fun E => E (f E) x₀ ∈ ({κ} : Finset Blk)) :=
    pr_congr fun E => by rw [hval, Finset.mem_singleton]
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [card_blk]
  norm_num

/-- **The executable tree on a uniform cipher**: a non-root node of the tree from a 16-byte seed
takes any given value with probability `≤ 2⁻¹²⁸`. -/
theorem pr_treeNode_eq_le (seed iv : ByteArray) (hs : seed.size = 16) {m : ℕ} (hm0 : m ≠ 0)
    (hm : m < nN) (κ : Blk) :
    pr Cipher (fun E => blk 16 (@treeNode (icPrg E) seed iv m) = κ) ≤ 1 / 2 ^ 128 := by
  refine le_trans (le_of_eq (pr_congr fun E => ?_))
    (pr_keyAt_eq_le iv (fun _ _ => 0) (blk 16 seed) hm0 hm κ)
  conv_lhs => rw [← ba_blk_of_size hs]
  rw [← keyAt_ic E iv (fun _ _ => 0) (blk 16 seed) m, blk_ba]

end TreeUniform

end VoleMole.ZK.Sim
