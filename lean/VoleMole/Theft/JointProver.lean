import VoleMole.Theft.JointCharge

/-!
# The real Lean prover is a point reader confined to its `iv`

`real_sim_leN_lean` (`Theft/JointLean.lean`) asks for the later real proofs as table readers
**confined to their `iv`s** (`Conf`): `H₅` keys that are gate inputs of the proof's `iv`, cipher
points at CTR blocks of the proof's `iv`. Here this is proved for the Lean prover `realRO`
(function rows), from the point-level congruences of step 1 (`ZK/ReadsPoint.lean`):

* `ctrPts`: the CTR blocks of an `iv`, as a finite set;
* `realROb_E_congrP`, `realKeys_cipherP`: the prover's output and keys read the cipher only at
  the CTR blocks of its `iv` of its tree's nodes (`realROb_E_congr`, `realKeys_cipher` at points);
* **`realPtRd`**: the prover as a consistent table reader: no slice key, its `624` `H₅` gate
  inputs, the points `(node, CTR block of rIv)` of its `4607` nodes;
* `realRO_ivV`: an output's `iv` is the prover's `rIv` (for an instance with a witness);
* **`realPtRd_conf`**: the reader is confined to the output's `iv`, within `(624, 4607)`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
  VoleMole.Arith

/-- **The CTR blocks of an `iv`**, as a finite set. -/
@[irreducible] noncomputable def ctrPts (iv : ByteArray) : Finset Blk :=
  (univ : Finset Blk).filter (InY iv)

-- (`Finset.univ` of 16-byte blocks: membership needs a deep instance check.)
set_option maxRecDepth 100000 in
lemma mem_ctrPts {iv : ByteArray} {z : Blk} : z ∈ ctrPts iv ↔ InY iv z := by
  unfold ctrPts
  rw [mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- **The points of keys `K` at the CTR blocks of `iv`.** -/
@[irreducible] noncomputable def ptsOf (K : Finset Blk) (iv : ByteArray) : Finset (Blk × Blk) :=
  K ×ˢ ctrPts iv

lemma mem_ptsOf {K : Finset Blk} {iv : ByteArray} {kz : Blk × Blk} :
    kz ∈ ptsOf K iv ↔ kz.1 ∈ K ∧ InY iv kz.2 := by
  unfold ptsOf
  rw [Finset.mem_product, mem_ctrPts]

lemma card_fst_ptsOf_le {K : Finset Blk} {iv : ByteArray} :
    ((ptsOf K iv).image Prod.fst).card ≤ K.card := by
  refine card_le_card fun k hk => ?_
  obtain ⟨kz, hkz, rfl⟩ := mem_image.1 hk
  exact (mem_ptsOf.1 hkz).1

section Prover

variable {Hb : Hashes} {st : Statement} {w : ByteArray}

/-- The prover's tree nodes agree at their points for two cipher tables that agree there. -/
lemma realNodes_agreeP (s : Sh st.params) (rho : ByteArray) (G3 : Tab3) (E' : Cipher)
    (hE : ∀ k ∈ realKeysE st.params Hb st w rho G3 s, ∀ z ∈ ctrPts (rIv (recHp st.params Hb st w G3
      s.1 s.2.1) st w rho), s.2.2 k z = E' k z) :
    NodesAgreeP (rowFn s.2.2) (rowFn E') (rSeed (recHp st.params Hb st w G3 s.1 s.2.1) st w rho)
      (rIv (recHp st.params Hb st w G3 s.1 s.2.1) st w rho) := fun n hn _ c t =>
  hE _ (mem_image.2 ⟨n, mem_range.2 hn, rfl⟩) _ (mem_ctrPts.2 ⟨c, t, rfl⟩)

/-- **The prover reads the cipher only at its nodes' points.** -/
theorem realROb_E_congrP (hHb : HashesWF Hb) (rho : ByteArray) (G3 : Tab3) (s : Sh st.params)
    (E : Cipher) (h : NodesAgreeP (rowFn s.2.2) (rowFn E) (rSeed (recHp st.params Hb st w G3 s.1 s.2.1) st w rho)
      (rIv (recHp st.params Hb st w G3 s.1 s.2.1) st w rho)) :
    realROb st.params Hb st w rho G3 (s.1, s.2.1, E) = realROb st.params Hb st w rho G3 s := by
  have hs := rSeed_size (w := w) hHb rho G3 s.1 s.2.1
  unfold realROb Prover.prove
  dsimp only
  rw [@voleGen_eq_voleGenAt (icPrg (rowFn E)), @voleGen_eq_voleGenAt (icPrg (rowFn s.2.2))]
  exact congrArg _ (voleGenAt_ic_congrP _ _ _ _ _ _ _ hs h).symm

/-- **The prover's keys under a change of the cipher at its nodes' points.** -/
lemma realKeys_cipherP (hHb : HashesWF Hb) (s : Sh st.params) (rho : ByteArray) (G3 : Tab3)
    (E' : Cipher) (hN : NodesAgreeP (rowFn s.2.2) (rowFn E') (rSeed (recHp st.params Hb st w G3 s.1 s.2.1) st w rho)
      (rIv (recHp st.params Hb st w G3 s.1 s.2.1) st w rho)) :
    realKeysE st.params Hb st w rho G3 (s.1, s.2.1, E') = realKeysE st.params Hb st w rho G3 s ∧
      realKeys5 st.params Hb st w rho G3 (s.1, s.2.1, E') = realKeys5 st.params Hb st w rho G3 s := by
  have hs := rSeed_size (w := w) hHb rho G3 s.1 s.2.1
  refine ⟨?_, ?_⟩
  · unfold realKeysE
    refine Finset.image_congr fun n hn => ?_
    exact congrArg (blk 16) (treeNode_ic_congrP hN n (mem_range.1 (Finset.mem_coe.1 hn))).symm
  · unfold realKeys5
    have hN' : NodesAgreeP (rowFn s.2.2) (rowFn E') (rSeed (recHp st.params Hb st w G3 s.1 s.2.1) st w rho)
        ((recHp st.params Hb st w G3 s.1 s.2.1).hash .h4
          ((((recHp st.params Hb st w G3 s.1 s.2.1).hash .h3 ((w.extract 0 st.params.witnessBytes ++
            st.mu1 Hb ++ rho).push 3)).extract 16 32 ++ st.mu1 Hb).push 4)) := by
      have := hN
      unfold rIv at this
      rwa [recHp_mu1] at this
    rw [vgIn5_ic_congrP _ _ _ _ _ hs hN']

/-- The prover's `iv` does not depend on the shared tables. -/
lemma rIv_tables (rho : ByteArray) (G3 : Tab3) (G2 G2' : Tab2G st.params) (G5 G5' : Tab5F) :
    rIv (recHp st.params Hb st w G3 G2 G5) st w rho = rIv (recHp st.params Hb st w G3 G2' G5') st w rho := by
  unfold rIv
  simp only [recHp_h3, recHp_h4, recHp_mu1]

/-- **The real prover reads at points, consistently**: tables with the same `H₂³` that agree with
`s` on its `H₅` gate inputs and at the CTR blocks of its `iv` of its nodes give the same proof and
the same reads. -/
theorem realPt_cons (hHb : HashesWF Hb) (ρ : Bytes 16) (G3 : Tab3) (s s' : Sh st.params)
    (h2 : s'.1 = s.1) (h5 : ∀ k ∈ realKeys5 st.params Hb st w (ba ρ) G3 s, s.2.1 k = s'.2.1 k)
    (hE : ∀ k ∈ realKeysE st.params Hb st w (ba ρ) G3 s, ∀ z ∈ ctrPts (rIv (recHp st.params Hb st w G3
      s.1 s.2.1) st w (ba ρ)), s.2.2 k z = s'.2.2 k z) :
    realRO st.params Hb st w ρ G3 s' = realRO st.params Hb st w ρ G3 s ∧
      realKeys5 st.params Hb st w (ba ρ) G3 s' = realKeys5 st.params Hb st w (ba ρ) G3 s ∧
      ptsOf (realKeysE st.params Hb st w (ba ρ) G3 s')
          (rIv (recHp st.params Hb st w G3 s'.1 s'.2.1) st w (ba ρ)) =
        ptsOf (realKeysE st.params Hb st w (ba ρ) G3 s)
          (rIv (recHp st.params Hb st w G3 s.1 s.2.1) st w (ba ρ)) := by
  have hN := realNodes_agreeP (w := w) s (ba ρ) G3 s'.2.2 hE
  obtain ⟨cE, c5⟩ := realKeys_cipherP (w := w) hHb s (ba ρ) G3 s'.2.2 hN
  have es : s' = (s.1, s'.2.1, s'.2.2) := by rw [← h2]
  -- the cipher: `s → (s.1, s.2.1, E')`
  have o1 : realRO st.params Hb st w ρ G3 (s.1, s.2.1, s'.2.2) = realRO st.params Hb st w ρ G3 s :=
    realROb_E_congrP hHb (ba ρ) G3 s s'.2.2 hN
  -- `H₅`: `(s.1, s.2.1, E') → (s.1, G5', E')`
  have o2 : realRO st.params Hb st w ρ G3 (s.1, s'.2.1, s'.2.2) =
      realRO st.params Hb st w ρ G3 (s.1, s.2.1, s'.2.2) :=
    realROb_h5_congr (ba ρ) G3 (s.1, s.2.1, s'.2.2) s'.2.1 fun k hk => h5 k (by rw [c5] at hk; exact hk)
  have k5 : realKeys5 st.params Hb st w (ba ρ) G3 (s.1, s'.2.1, s'.2.2) =
      realKeys5 st.params Hb st w (ba ρ) G3 s := by
    rw [realKeys5_tables (ba ρ) G3 s.1 s.1 s'.2.1 s.2.1 s'.2.2, c5]
  have kE : realKeysE st.params Hb st w (ba ρ) G3 (s.1, s'.2.1, s'.2.2) =
      realKeysE st.params Hb st w (ba ρ) G3 s := by
    rw [realKeysE_tables (ba ρ) G3 s.1 s.1 s'.2.1 s.2.1 s'.2.2, cE]
  rw [es]
  refine ⟨by rw [o2, o1], k5, ?_⟩
  show ptsOf (realKeysE st.params Hb st w (ba ρ) G3 (s.1, s'.2.1, s'.2.2))
      (rIv (recHp st.params Hb st w G3 s.1 s'.2.1) st w (ba ρ)) = _
  rw [kE, rIv_tables (ba ρ) G3 s.1 s.1 s'.2.1 s.2.1]

variable (Hb st w)

/-- **The real prover as a consistent table point reader**: no slice key, its `H₅` gate inputs,
and the CTR blocks of its `iv` of its tree's nodes. -/
noncomputable def realPtRd (hHb : HashesWF Hb) (ρ : Bytes 16) (G3 : Tab3) :
    TRd (fun (_ : Tab3) (s : Sh st.params) => realRO st.params Hb st w ρ G3 s) where
  Q3 _ _ := ∅
  Q5 _ s := realKeys5 st.params Hb st w (ba ρ) G3 s
  QE _ s := ptsOf (realKeysE st.params Hb st w (ba ρ) G3 s)
    (rIv (recHp st.params Hb st w G3 s.1 s.2.1) st w (ba ρ))
  cons _ s _ s' _ hA := by
    obtain ⟨a, b, c⟩ := realPt_cons hHb ρ G3 s s' hA.1 hA.2.1 fun k hk z hz =>
      hA.2.2 (k, z) (mem_ptsOf.2 ⟨hk, mem_ctrPts.1 hz⟩)
    exact ⟨a, rfl, b, c⟩

lemma realPtRd_QE (hHb : HashesWF Hb) (ρ : Bytes 16) (G3 g : Tab3) (s : Sh st.params) :
    (realPtRd Hb st w hHb ρ G3).QE g s = ptsOf (realKeysE st.params Hb st w (ba ρ) G3 s)
      (rIv (recHp st.params Hb st w G3 s.1 s.2.1) st w (ba ρ)) := rfl

lemma realPtRd_Q5 (hHb : HashesWF Hb) (ρ : Bytes 16) (G3 g : Tab3) (s : Sh st.params) :
    (realPtRd Hb st w hHb ρ G3).Q5 g s = realKeys5 st.params Hb st w (ba ρ) G3 s := rfl

variable {Hb st w}

/-- **An output's `iv` is the prover's `rIv`** (for an instance with a witness). -/
theorem realRO_ivV {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (ρ : Bytes 16) (G3 : Tab3) (s : Sh st.params) {v : ByteArray}
    (h : ivV Hb st (realRO st.params Hb st w ρ G3 s) = some v) :
    v = rIv (recHp st.params Hb st w G3 s.1 s.2.1) st w (ba ρ) := by
  rw [realRO_eq, @prove_recH_eq (icPrg (rowFn s.2.2)) Hb st w cs hzk hHb hlab] at h
  rcases ho : @hyb3 (icPrg (rowFn s.2.2)) (recB Hb st w G3 s.2.1) CrtGen.tables st w
      ((splitSeed (G3 ρ)).2, s.1 ∘ key2 st.params (@preR (icPrg (rowFn s.2.2)) Hb CrtGen.tables st w
        s.2.1 (splitSeed (G3 ρ))))
      (@hiddenOut (icPrg (rowFn s.2.2)) st.params (ivOfPre Hb st (splitSeed (G3 ρ)).2)
        (ba (deltaOf (s.1 ∘ key2 st.params (@preR (icPrg (rowFn s.2.2)) Hb CrtGen.tables st w s.2.1
          (splitSeed (G3 ρ)))))) (splitSeed (G3 ρ)).1) with e | proof
  · rw [ho] at h; cases h
  · rw [ho] at h
    obtain ⟨-, -, hI⟩ := @hyb3_ok_fields (icPrg (rowFn s.2.2)) st w _ CrtGen.tables cs hzk _ _ proof ho
    simp only [ivV, Option.some.injEq] at h
    rw [← h, ivOf, hI]
    unfold rIv
    rw [recHp_h4, recHp_mu1, ivPre_eq_split hHb]

/-- A member of a gate-input list of a 16-byte `iv` is a gate input of it. -/
lemma gate5_of_mem {p : Params} {T : CrtTables} {iv : ByteArray} (hiv : iv.size = 16)
    {cols : Array (Array UInt64)} {off : W128} {b : ByteArray}
    (hb : b ∈ Prover.gateInputsOff p T iv cols off) : Gate5 p T iv (blk 37 b) := by
  obtain ⟨e, he, rfl⟩ := List.mem_iff_getElem.1 hb
  have he' : e < 312 := by have := gateInputsOff_length p T iv cols off; omega
  have hs : ((Prover.gateInputsOff p T iv cols off)[e]'he).size = 37 := by
    rw [← List.getD_eq_getElem _ ByteArray.empty he, gateInputsOff_getD (p := p) (T := T) _ _ _ he',
      ByteArray.size_push, ByteArray.size_append, size_pushLE32, W128.toBytes_size, hiv]
  refine ⟨cols, off, ⟨e, he'⟩, ?_⟩
  unfold enc5
  rw [ba_blk_of_size hs]
  exact (List.getD_eq_getElem _ _ he).symm

/-- The gate inputs of step 1 are gate inputs of its `iv`. -/
lemma realKeys5_gate (hHb : HashesWF Hb) (ρ : Bytes 16) (G3 : Tab3) (s : Sh st.params) {k : Bytes 37}
    (hk : k ∈ realKeys5 st.params Hb st w (ba ρ) G3 s) :
    Gate5 st.params CrtGen.tables (rIv (recHp st.params Hb st w G3 s.1 s.2.1) st w (ba ρ)) k := by
  unfold realKeys5 at hk
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hk
  rw [List.mem_toFinset] at hb
  have hsz : (rIv (recHp st.params Hb st w G3 s.1 s.2.1) st w (ba ρ)).size = 16 :=
    recHp_wf hHb G3 s.1 s.2.1 .h4 _
  have hv : vgIv (recHp st.params Hb st w G3 s.1 s.2.1) (st.mu1 Hb)
      (((recHp st.params Hb st w G3 s.1 s.2.1).hash .h3 ((w.extract 0 st.params.witnessBytes ++
        st.mu1 Hb ++ ba ρ).push 3)).extract 16 32) =
      rIv (recHp st.params Hb st w G3 s.1 s.2.1) st w (ba ρ) := by
    unfold vgIv rIv; rw [recHp_mu1]
  unfold vgIn5 at hb
  rw [hv, List.mem_append] at hb
  rcases hb with hb | hb
  · exact gate5_of_mem hsz hb
  · exact gate5_of_mem hsz hb

lemma realPt_inE {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (ρ : Bytes 16) (G3 : Tab3) (s : Sh st.params) {v : ByteArray}
    (hv : ivV Hb st (realRO st.params Hb st w ρ G3 s) = some v) (kz : Blk × Blk)
    (hkz : kz ∈ ptsOf (realKeysE st.params Hb st w (ba ρ) G3 s)
      (rIv (recHp st.params Hb st w G3 s.1 s.2.1) st w (ba ρ))) : InY v kz.2 := by
  rw [realRO_ivV hzk hHb hlab ρ G3 s hv]
  exact (mem_ptsOf.1 hkz).2

/-- **The real prover's reader is confined to the output's `iv`**, within `(624, 4607)`. -/
theorem realPtRd_conf {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (ρ : Bytes 16) (G3 : Tab3) :
    Conf (realPtRd Hb st w hHb ρ G3) (fun s => ivV Hb st (realRO st.params Hb st w ρ G3 s)) 624 4607 where
  h3 _ _ := rfl
  h5 g s := card_image_le.trans ((List.toFinset_card_le _).trans (le_of_eq
    (@vgIn5_length (icPrg (rowFn s.2.2)) _ _ _ _ _ _)))
  hE g s := card_fst_ptsOf_le.trans (card_image_le.trans (le_of_eq (by rw [card_range]; rfl)))
  in5 g s v hv k hk := by
    rw [realRO_ivV hzk hHb hlab ρ G3 s hv]
    rw [realPtRd_Q5] at hk
    exact realKeys5_gate hHb ρ G3 s hk
  inE g s v hv kz hkz := realPt_inE hzk hHb hlab ρ G3 s hv kz hkz

end Prover

end VoleMole.Theft
