import VoleMole.Theft.JointProg

/-!
# The Lean verifier is a point reader

The game reader of `real_sim_leN_lean` (`GRd`) reads the theft games' event; the event runs the
Lean verifier on the adversary's operation. `ZK/VerifyReadsRO.lean` bounds the verifier's reads by
**keys** (`verRO_rdE`: the reconstruction's `4607` nodes). Here at points, as for the programming
(`Theft/JointProg.lean`):

* **`verify_ic_congrP`**: the verifier reads the cipher only at the CTR blocks of the proof's `iv`
  of the reconstruction's nodes;
* **`verPtRd`**: `verRO` as a consistent table point reader: no slice key, its `≤ 312` `H₅` gate
  inputs, the reconstruction's `≤ 4607` nodes at the CTR blocks of the proof's `iv`; `H₂³` read
  freely (`verPtRd_bnd`: within `(0, 312, 4607)`);
* `verPtRd_inE`: its cipher points are at CTR blocks of the proof's `iv` (so it is charged to a
  slot only if the forged proof's `iv` has the slot's middle bytes).
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK VoleMole.Verifier VoleMole.Verifier.Bridge
  VoleMole.Arith

/-- **The verifier reads the cipher only at the reconstruction's points.** -/
theorem verify_ic_congrP {E E' : Cipher} (Hs : Hashes) (T : CrtTables) (st : Statement)
    (proof : ByteArray)
    (h : RecAgreeP E E' (pfIv Hs st proof) (⟨st.params, proof⟩ : Proof).opening
      (⟨st.params, proof⟩ : Proof).delta) :
    @verify (icPrg E) Hs T st proof = @verify (icPrg E') Hs T st proof := by
  set pf : Proof := ⟨st.params, proof⟩ with hpf
  have hr := reconstruct_ic_congrP h
  simp only [verify, Id.run]
  rw [← hpf]
  rw [show @BAVC.reconstruct (icPrg E') (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta =
    @BAVC.reconstruct (icPrg E) (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta from hr.symm]
  split
  · rfl
  · split
    · rename_i leaves hl
      have hc : @convertToVole (icPrg E) pf (ivOf Hs pf (st.mu1 Hs)) leaves =
          @convertToVole (icPrg E') pf (ivOf Hs pf (st.mu1 Hs)) leaves :=
        convertToVole_ic_congrP h pf rfl hl
      rw [hc]
    · rfl

section RO

variable {p : Params} {Hb : Hashes}

/-- **The cipher points the verifier reads**: the reconstruction's nodes at the CTR blocks of the
proof's `iv`. -/
noncomputable def verPtsE (p : Params) (Hb : Hashes) (st : Statement) (proof : ByteArray)
    (s : Sh p) : Finset (Blk × Blk) :=
  ptsOf (verKeysE (Hb := Hb) st proof s) (pfIv Hb st proof)

lemma verKeys5_eq (st : Statement) (proof : ByteArray) (s : Sh p) :
    verKeys5 (Hb := Hb) st proof s =
      ((@vIn5 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st proof).toFinset).image (blk 37) := by
  unfold verKeys5
  rw [@vIn5_congr (icPrg (rowFn s.2.2)) _ st _ Hb (by simp only [recV_mu1]) (by simp only [recV_h4])]

/-- **The verifier reads at points, consistently.** -/
theorem verPt_cons (st : Statement) (proof : ByteArray) (s s' : Sh p) (h2 : s'.1 = s.1)
    (h5 : ∀ k ∈ verKeys5 (Hb := Hb) st proof s, s.2.1 k = s'.2.1 k)
    (hE : ∀ kz ∈ verPtsE p Hb st proof s, s.2.2 kz.1 kz.2 = s'.2.2 kz.1 kz.2) :
    verRO p Hb st proof s' = verRO p Hb st proof s ∧
      verKeys5 (Hb := Hb) st proof s' = verKeys5 (Hb := Hb) st proof s ∧
      verPtsE p Hb st proof s' = verPtsE p Hb st proof s := by
  have hA : RecAgreeP s.2.2 s'.2.2 (pfIv Hb st proof) (⟨st.params, proof⟩ : Proof).opening
      (⟨st.params, proof⟩ : Proof).delta := by
    intro k hk c t
    refine hE (k, _) ?_
    rw [verPtsE, mem_ptsOf]
    exact ⟨hk, c, t, rfl⟩
  have hA' : RecAgreeP s.2.2 s'.2.2 (pfIv (recV p Hb s'.1 s'.2.1) st proof)
      (⟨st.params, proof⟩ : Proof).opening (⟨st.params, proof⟩ : Proof).delta := by
    simpa only [pfIv, ivOf, recV_h4, recV_mu1] using hA
  have hI : @vIn5 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st proof =
      @vIn5 (icPrg (rowFn s'.2.2)) Hb CrtGen.tables st proof := vIn5_ic_congrP Hb CrtGen.tables st proof hA
  have k5 : verKeys5 (Hb := Hb) st proof s' = verKeys5 (Hb := Hb) st proof s := by
    rw [verKeys5_eq, verKeys5_eq, hI]
  have kE : verKeysE (Hb := Hb) st proof s' = verKeysE (Hb := Hb) st proof s := by
    unfold verKeysE
    exact rdKeys_ic_congrP hA
  refine ⟨?_, k5, by simp only [verPtsE, kE]⟩
  -- first the cipher, then `H₅`
  have o1 : @verify (icPrg (rowFn s'.2.2)) (recV p Hb s'.1 s'.2.1) CrtGen.tables st proof =
      @verify (icPrg (rowFn s.2.2)) (recV p Hb s'.1 s'.2.1) CrtGen.tables st proof :=
    (verify_ic_congrP _ _ _ _ hA').symm
  have o2 : @verify (icPrg (rowFn s.2.2)) (recV p Hb s'.1 s'.2.1) CrtGen.tables st proof =
      @verify (icPrg (rowFn s.2.2)) (recV p Hb s.1 s.2.1) CrtGen.tables st proof := by
    rw [h2]
    have hAg := recV_agreeOff_h5 (Hb := Hb) s.1 s'.2.1 s.2.1
    refine @verify_h5_congr (icPrg (rowFn s.2.2)) _ _ hAg _ _ _ fun x hx => ?_
    rw [@vIn5_congr (icPrg (rowFn s.2.2)) _ st _ Hb (by simp only [recV_mu1])
      (by simp only [recV_h4])] at hx
    refine withTable_h5_congr _ fun _ => (h5 _ ?_).symm
    rw [verKeys5_eq]
    exact mem_image.2 ⟨x, List.mem_toFinset.2 hx, rfl⟩
  show @verify (icPrg (rowFn s'.2.2)) (recV p Hb s'.1 s'.2.1) CrtGen.tables st proof =
    @verify (icPrg (rowFn s.2.2)) (recV p Hb s.1 s.2.1) CrtGen.tables st proof
  rw [o1, o2]

variable (Hb)

/-- **The Lean verifier as a consistent table point reader.** -/
noncomputable def verPtRd (st : Statement) (proof : ByteArray) :
    TRd (fun (_ : Tab3) (s : Sh p) => verRO p Hb st proof s) where
  Q3 _ _ := ∅
  Q5 _ s := verKeys5 (Hb := Hb) st proof s
  QE _ s := verPtsE p Hb st proof s
  cons _ s _ s' _ hA := by
    obtain ⟨a, b, c⟩ := verPt_cons st proof s s' hA.1 hA.2.1 hA.2.2
    exact ⟨a, rfl, b, c⟩

lemma verPtRd_QE (st : Statement) (proof : ByteArray) (g : Tab3) (s : Sh p) :
    (verPtRd (p := p) Hb st proof).QE g s = verPtsE p Hb st proof s := rfl

variable {Hb}

/-- **The verifier's budgets**: no slice key, `312` `H₅` keys, `4607` cipher keys. -/
theorem verPtRd_bnd (st : Statement) (proof : ByteArray) :
    (verPtRd (p := p) Hb st proof).Bnd 0 312 4607 where
  h3 _ _ := le_rfl
  h5 _ s := card_image_le.trans ((List.toFinset_card_le _).trans
    (@vIn5_length_le (icPrg (rowFn s.2.2)) _ _ _ _))
  hE _ _ := card_fst_ptsOf_le.trans (rdKeys_card _ _ _ _)

/-- **The verifier's cipher points are CTR blocks of the proof's `iv`.** -/
theorem verPtRd_inE (st : Statement) (proof : ByteArray) (g : Tab3) (s : Sh p) (kz : Blk × Blk)
    (h : kz ∈ (verPtRd (p := p) Hb st proof).QE g s) : InY (pfIv Hb st proof) kz.2 := by
  rw [verPtRd_QE, verPtsE, mem_ptsOf] at h
  exact h.2

end RO

end VoleMole.Theft
