import VoleMole.ZK.ReadsRO

/-!
# What the Lean verifier reads on the shared tables

`ZK/ReadsRO.lean` bounds what the executable **prover** reads on the shared tables
(`realRO_rd5`: `H₅` at `624` keys, `realRO_rdE`: the cipher at `4607`). Here the same for the
executable **verifier** (`Verifier.verify`), run with the record of the shared tables (`recV`:
`H₂³` and `H₅` the tables, every other hash the base record) and the ideal-cipher PRG of the
shared cipher table (`verRO`):

* **`H₅`** (`verRO_rd5`): at most `nMult = 312` keys, the gate inputs `gateInputs` at its key
  columns (`vIn5`, the same inputs as its grinding-prefix recomputation `vPre`;
  `verify_h5_congr`).
* **The cipher** (`verRO_rdE`): at most `2L − 1 = 4607` keys, the nodes of the BAVC tree it
  reconstructs from the opening (`rdKeys`; `verify_ic_congr`: the reconstruction, the leaves'
  commitments, the VOLE expansion off the hidden leaves).
* **`H₂³`** (`verify_h23_congr`): at the single point `chal3Input` (`chal2 ‖ qs_check ‖ ã ‖ ctr ‖ 11`),
  if it gets there.
* It does not read `H₃` (`verify_agreeOff_h3`).

The constants are those of the simulator's programming, which recomputes the verifier's prefix
(`progRO_isProg`: `312`, `4607`): the verifier reads the same keys, plus one `H₂³` point. A
reduction that runs an honest verification of a real proof therefore reads `624 + 312 = 936`
`H₅` keys and `4607 + 4607 = 9214` cipher keys (`verRO_comp_rd5`, `verRO_comp_rdE` with
`realRO_rd5`, `realRO_rdE`); `Privacy/MoussakaNCRO.lean` uses this for the honest Anchors of
Moussaka's non-colluding mode. The executable definitions are unchanged: everything is about
`Verifier.verify` at the record `recV` and the PRG `icPrg`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## The verifier's reads, for any PRG -/

section Congr

variable [HasPrg] {Hs Hs' : Hashes}

/-- **The verifier reads `H₅` only at `vIn5`**: two records that agree off `H₅`, and on `H₅` at the
verifier's gate inputs, give the same transcript. -/
theorem verify_h5_congr (h : Hs.AgreeOff .h5 Hs') (T : CrtTables) (st : Statement)
    (proof : ByteArray) (h5 : ∀ x ∈ vIn5 Hs T st proof, Hs.hash .h5 x = Hs'.hash .h5 x) :
    verify Hs T st proof = verify Hs' T st proof := by
  have hmu := h.mu1 (by decide) (by decide) st
  have h4 := h .h4 (by decide)
  have h1 := h .h1 (by decide)
  have h23 := h .h23 (by decide)
  unfold vIn5 at h5
  simp only [ivOf, hmu, h4] at h5
  simp only [verify, Id.run, ivOf, hmu, h4]
  split
  · rfl
  · split
    · rename_i leaves hl
      simp only [hl] at h5
      simp only [crtReconstruct, crtReconstructAt, gateHashes, h1, h.chal1 (by decide),
        h.chal2 (by decide), h.muDelayed (by decide) st, h.combBytes (fun _ => nofun) st,
        List.map_congr_left h5, chal3, h23]
      rfl
    · rfl

end Congr

section CongrE

/-- **The verifier reads the cipher only at the reconstruction's reads** of the proof's opening
(the nodes of the tree it rebuilds, `rdKeys`). -/
theorem verify_ic_congr {E E' : Cipher} (Hs : Hashes) (T : CrtTables) (st : Statement)
    (proof : ByteArray)
    (h : ∀ k ∈ rdKeys E (ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs)) (⟨st.params, proof⟩ : Proof).opening
      (⟨st.params, proof⟩ : Proof).delta, E k = E' k) :
    @verify (icPrg E) Hs T st proof = @verify (icPrg E') Hs T st proof := by
  set pf : Proof := ⟨st.params, proof⟩ with hpf
  have hr := reconstruct_ic_congr h
  simp only [verify, Id.run]
  rw [← hpf, ← hr]
  split
  · rfl
  · split
    · rename_i leaves hl
      have hc : @convertToVole (icPrg E) pf (ivOf Hs pf (st.mu1 Hs)) leaves =
          @convertToVole (icPrg E') pf (ivOf Hs pf (st.mu1 Hs)) leaves := by
        unfold convertToVole
        refine convertToVoleAt_ic_congr _ _ _ _ _ fun i hi j hj hjd hs => h _ ?_
        have := @leafKey_mem_rdKeys E (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta i j hi hj hjd
        rw [hl, Option.getD_some] at this
        exact this hs
      rw [hc]
    · rfl

/-- **The verifier reads `H₂³` at one point**: `chal3`'s input `chal2 ‖ qs_check ‖ ã ‖ ctr ‖ 11`
(the recomputed prefix `vPre`, the proof's counter, the domain byte), if the run gets there. A
record that agrees with `Hs` off `H₂³`, and on `H₂³` at that point, gives the same transcript. -/
theorem verify_h23_congr [HasPrg] {Hs Hs' : Hashes} (h : Hs.AgreeOff .h23 Hs') (T : CrtTables)
    (st : Statement) (proof : ByteArray)
    (h23 : Hs.hash .h23 ((vPre Hs T st proof ++ (⟨st.params, proof⟩ : Proof).ctr).push 11) =
      Hs'.hash .h23 ((vPre Hs T st proof ++ (⟨st.params, proof⟩ : Proof).ctr).push 11)) :
    verify Hs T st proof = verify Hs' T st proof := by
  have hmu := h.mu1 (by decide) (by decide) st
  have h4 := h .h4 (by decide)
  have h1 := h .h1 (by decide)
  have h5 := h .h5 (by decide)
  simp only [vPre, vPreP, vPreOf] at h23
  simp only [verify, Id.run, ivOf, hmu, h4] at h23 ⊢
  split
  · rfl
  · split
    · rename_i leaves hl
      simp only [hl] at h23
      simp only [crtReconstruct, crtReconstructAt, gateHashes, h1, h5, h.chal1 (by decide),
        h.chal2 (by decide), h.muDelayed (by decide) st, h.combBytes (fun _ => nofun) st] at h23 ⊢
      split
      · rename_i hc
        simp only [hc, ↓reduceIte]
      · rename_i hc
        simp only [hc, Bool.false_eq_true, ↓reduceIte, chal3, chal3Input] at h23 ⊢
        rw [h23]
    · rfl

/-- **The verifier does not read `H₃`.** -/
theorem verify_agreeOff_h3 [HasPrg] {Hs Hs' : Hashes} (h : Hs.AgreeOff .h3 Hs') (T : CrtTables)
    (st : Statement) : verify Hs T st = verify Hs' T st := by
  funext proof
  have hmu := h.mu1 (by decide) (by decide) st
  have h4 := h .h4 (by decide)
  have h1 := h .h1 (by decide)
  have h5 := h .h5 (by decide)
  have h23 := h .h23 (by decide)
  simp only [verify, Id.run, ivOf, hmu, h4]
  split
  · rfl
  · split
    · rename_i leaves hl
      simp only [crtReconstruct, h1, h5, h.chal1 (by decide), h.chal2 (by decide),
        h.muDelayed (by decide) st, h.combBytes (fun _ => nofun) st, chal3, h23]
      rfl
    · rfl

end CongrE

/-! ## On the shared tables -/

section RO

variable {R : Type} [CipherRow R] (p : Params) (Hb : Hashes)

/-- **The verifier's record on the shared tables**: `H₂³` the table on the grinding points of
parameters `p`, `H₅` the table on every `37`-byte input, the base record `Hb` elsewhere (the
verifier reads no `H₃`). -/
noncomputable def recV (G2 : Tab2G p) (G5 : Tab5F) : Hashes :=
  (Hb.withTable .h23 (enc2 p) G2).withTable .h5 enc5 G5

/-- **The executable verifier on the shared tables**: the record `recV` and the ideal-cipher PRG
of the shared cipher table. -/
noncomputable def verRO (st : Statement) (proof : ByteArray) (s : ShG R p) : Transcript :=
  @verify (icPrg (rowFn s.2.2)) (recV p Hb s.1 s.2.1) CrtGen.tables st proof

variable {p Hb}

lemma recV_agreeOff_h5 (G2 : Tab2G p) (G5 G5' : Tab5F) :
    (recV p Hb G2 G5).AgreeOff .h5 (recV p Hb G2 G5') := by
  intro k hk
  funext x
  simp only [recV, Hashes.withTable, hk, ite_false]

lemma recV_h4 (G2 : Tab2G p) (G5 : Tab5F) : (recV p Hb G2 G5).hash .h4 = Hb.hash .h4 := by
  funext x
  simp only [recV, Hashes.withTable, reduceCtorEq, ite_false]

lemma recV_mu1 (st : Statement) (G2 : Tab2G p) (G5 : Tab5F) : st.mu1 (recV p Hb G2 G5) = st.mu1 Hb := by
  have h1 : (recV p Hb G2 G5).hash .mu = Hb.hash .mu := by
    funext x; simp only [recV, Hashes.withTable, reduceCtorEq, ite_false]
  have h2 : (recV p Hb G2 G5).hash .muDelayed = Hb.hash .muDelayed := by
    funext x; simp only [recV, Hashes.withTable, reduceCtorEq, ite_false]
  simp only [Statement.mu1, VoleMole.Verifier.mu, h1, h2]

/-- The `H₅` keys the verifier reads on the shared tables: its gate inputs (at most `312`). -/
noncomputable def verKeys5 (st : Statement) (proof : ByteArray) (s : ShG R p) : Finset (Bytes 37) :=
  ((@vIn5 (icPrg (rowFn s.2.2)) (recV p Hb s.1 s.2.1) CrtGen.tables st proof).toFinset).image (blk 37)

/-- The cipher keys the verifier reads on the shared tables: the reconstruction's nodes (at most
`4607`). -/
noncomputable def verKeysE (st : Statement) (proof : ByteArray) (s : ShG R p) : Finset Blk :=
  rdKeys (rowFn s.2.2) (ivOf Hb ⟨st.params, proof⟩ (st.mu1 Hb)) (⟨st.params, proof⟩ : Proof).opening
    (⟨st.params, proof⟩ : Proof).delta

/-- **The verifier reads `H₅` at most at `312` keys** (`nMult`: its gate inputs). -/
theorem verRO_rd5 (st : Statement) (proof : ByteArray) : Rd5 (verRO (R := R) p Hb st proof) 312 := by
  classical
  refine ⟨verKeys5 (Hb := Hb) st proof, fun s => card_image_le.trans ((List.toFinset_card_le _).trans
    (@vIn5_length_le (icPrg (rowFn s.2.2)) _ _ _ _)), fun s G5 h => ?_⟩
  have hA := recV_agreeOff_h5 (Hb := Hb) s.1 G5 s.2.1
  unfold verRO
  refine @verify_h5_congr (icPrg (rowFn s.2.2)) _ _ hA _ _ _ fun x hx => ?_
  rw [@vIn5_congr (icPrg (rowFn s.2.2)) _ st _ (recV p Hb s.1 s.2.1) (by simp only [recV_mu1])
    (by simp only [recV_h4])] at hx
  exact withTable_h5_congr _ fun _ => (h _ (mem_image.2 ⟨x, List.mem_toFinset.2 hx, rfl⟩)).symm

/-- **The verifier reads the cipher at most at `4607` keys** (the nodes of the tree it
reconstructs). -/
theorem verRO_rdE (st : Statement) (proof : ByteArray) : RdE (verRO (R := R) p Hb st proof) 4607 := by
  refine ⟨verKeysE (Hb := Hb) st proof, fun s => rdKeys_card _ _ _ _, fun s E h => ?_⟩
  unfold verRO
  refine (verify_ic_congr _ _ _ _ fun k hk => ?_).symm
  simp only [ivOf, recV_mu1, recV_h4] at hk
  exact rowFn_congr (h k hk)

/-- **An honest verification of a real proof** (the proof computed on the tables by `f`, then
verified on them) reads `H₅` at the prover's keys and `312` more. -/
theorem verRO_comp_rd5 {X : Type*} {f : ShG R p → ByteArray} {a : ℕ} (hf : Rd5 f a)
    (st : Statement) (g : Transcript → X) :
    Rd5 (fun s => g (verRO p Hb st (f s) s)) (a + 312) :=
  (hf.bind (f := fun pf s => verRO p Hb st pf s) fun pf => verRO_rd5 st pf).map g

/-- The same for the cipher: the prover's keys and `4607` more. -/
theorem verRO_comp_rdE {X : Type*} {f : ShG R p → ByteArray} {a : ℕ} (hf : RdE f a)
    (st : Statement) (g : Transcript → X) :
    RdE (fun s => g (verRO p Hb st (f s) s)) (a + 4607) :=
  (hf.bind (f := fun pf s => verRO p Hb st pf s) fun pf => verRO_rdE st pf).map g

end RO

end VoleMole.ZK.Sim
