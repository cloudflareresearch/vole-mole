import VoleMole.ZK.ReadsPoint
import VoleMole.Privacy.PomFRITLin

/-!
# The single-phase prover reads the cipher at points

`ZK/ReadsPoint.lean` restates step 1 of the two-phase prover at the level of cipher **points**
`(key, CTR block of the proof's iv)`. The single-phase prover `realROb` (Moussaka's and
Ratatouille's proofs) runs the same VOLE generation (`voleGen_eq_voleGenAt`), so the same holds
for it:

* `ivR`: the proof's `iv`, a function of its `H₃` slice and the base record only (not of the
  shared tables; `rIv_recHp`);
* `rdRO`: the proof's **point read set** on the `(H₅, cipher)` pair `t` (with `H₂³` table `g`):
  its `624` `H₅` keys (`realKeys5`) and the points `(k, z)` with `k` one of its `4607` tree nodes
  (`realKeysE`) and `z` a CTR block of its `iv` (`InY`);
* **`rdRO_cons`**: a pair `t'` that agrees with `t` on `rdRO g t` gives the same read set and the
  same proof (whatever the rows elsewhere). `H₂³` is fixed: it is not split by the lazy sampling
  of `Privacy/MoussakaLin.lean`.

Function rows (`FR = Blk → Blk`) only, as in `Privacy/PomFRITLin.lean`: the read sets patch single
points of a row.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
open VoleMole.Privacy.PomFRIT (FR T5 RdS AgR)

section RealP

variable {Hb : Hashes} {st : Statement} {w : ByteArray}

variable (Hb st w) in
/-- **The proof's `iv`**: `H₄(ivPre ‖ µ₁ ‖ 4)` with `ivPre` from its `H₃` slice; it does not
depend on the shared tables. -/
noncomputable def ivR (rho : ByteArray) (G3 : Tab3) : ByteArray :=
  Hb.hash .h4 ((((Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes))
    G3).hash .h3 ((w.extract 0 st.params.witnessBytes ++ st.mu1 Hb ++ rho).push 3)).extract 16 32 ++
      st.mu1 Hb).push 4)

lemma rIv_recHp (rho : ByteArray) (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5F) :
    rIv (recHp st.params Hb st w G3 G2 G5) st w rho = ivR Hb st w rho G3 := by
  unfold rIv ivR
  simp only [recHp_h3, recHp_h4, recHp_mu1]

/-- The shared tables with `H₂³` table `g` and `(H₅, cipher)` pair `t`. -/
def toSp {p : Params} (g : Tab2G p) (t : T5) : ShG FR p := (g, t.1, t.2)

variable (Hb st w) in
/-- **The proof's point read set** on the `(H₅, cipher)` pair `t`: its `H₅` keys, and the CTR
blocks of its `iv` at its tree's nodes. -/
noncomputable def rdRO (rho : ByteArray) (G3 : Tab3) (g : Tab2G st.params) (t : T5) : RdS :=
  (realKeys5 st.params Hb st w rho G3 (toSp g t),
    fun k z => k ∈ realKeysE st.params Hb st w rho G3 (toSp g t) ∧ InY (ivR Hb st w rho G3) z)

/-- **The single-phase prover is a consistent reader of its points**: a pair `t'` that agrees
with `t` on `rdRO g t` has the same read set and the same proof. -/
theorem rdRO_cons (hHb : HashesWF Hb) (rho : ByteArray) (G3 : Tab3) (g : Tab2G st.params)
    (t t' : T5) (h : AgR (rdRO Hb st w rho G3 g t) t t') :
    rdRO Hb st w rho G3 g t' = rdRO Hb st w rho G3 g t ∧
      realROb st.params Hb st w rho G3 (toSp g t') = realROb st.params Hb st w rho G3 (toSp g t) := by
  obtain ⟨G5, E⟩ := t
  obtain ⟨G5', E'⟩ := t'
  obtain ⟨h5, hE⟩ := h
  dsimp only at h5 hE
  have hs := rSeed_size (w := w) hHb rho G3 g G5
  have hiv := rIv_recHp (Hb := Hb) (st := st) (w := w) rho G3 g G5
  -- the tree's nodes agree at their points
  have hN : NodesAgreeP E E' (rSeed (recHp st.params Hb st w G3 g G5) st w rho)
      (rIv (recHp st.params Hb st w G3 g G5) st w rho) := fun n hn _ c t => by
    refine hE _ _ ⟨mem_image.2 ⟨n, mem_range.2 hn, rfl⟩, ?_⟩
    rw [← hiv]
    exact ⟨c, t, rfl⟩
  have hN0 : NodesAgreeP E E' (rSeed (recHp st.params Hb st w G3 g G5) st w rho) (ivR Hb st w rho G3) := by
    rw [← hiv]; exact hN
  -- the cipher: `(g, G5, E) → (g, G5, E')`
  have eE : realKeysE st.params Hb st w rho G3 (g, G5, E') = realKeysE st.params Hb st w rho G3 (g, G5, E) := by
    unfold realKeysE
    refine Finset.image_congr fun n hn => ?_
    exact congrArg (blk 16) (treeNode_ic_congrP hN n (mem_range.1 (Finset.mem_coe.1 hn))).symm
  have e5 : realKeys5 st.params Hb st w rho G3 (g, G5, E') = realKeys5 st.params Hb st w rho G3 (g, G5, E) := by
    unfold realKeys5
    dsimp only
    have hN5 : NodesAgreeP E E' (rSeed (recHp st.params Hb st w G3 g G5) st w rho)
        ((recHp st.params Hb st w G3 g G5).hash .h4
          ((((recHp st.params Hb st w G3 g G5).hash .h3 ((w.extract 0 st.params.witnessBytes ++
            st.mu1 Hb ++ rho).push 3)).extract 16 32 ++ st.mu1 Hb).push 4)) := by
      convert hN0 using 2
      simp only [ivR, recHp_h3, recHp_h4]
    have hv := vgIn5_ic_congrP (E := E) (E' := E') _ CrtGen.tables st.params (st.mu1 Hb) _ hs hN5
    exact congrArg (fun l => (List.toFinset l).image (blk 37)) hv.symm
  have eP : realROb st.params Hb st w rho G3 (g, G5, E') = realROb st.params Hb st w rho G3 (g, G5, E) := by
    unfold realROb Prover.prove
    dsimp only
    rw [@voleGen_eq_voleGenAt (icPrg (rowFn E')), @voleGen_eq_voleGenAt (icPrg (rowFn E))]
    refine congrArg _ (voleGenAt_ic_congrP (E := E) (E' := E') _ _ _ _ _ _ _ hs ?_).symm
    convert hN0 using 2
    simp only [ivR, recHp_h3, recHp_h4, recHp_mu1]
  -- `H₅`: `(g, G5, E') → (g, G5', E')`
  have eP5 : realROb st.params Hb st w rho G3 (g, G5', E') = realROb st.params Hb st w rho G3 (g, G5, E') :=
    realROb_h5_congr (s := (g, G5, E')) rho G3 G5' fun k hk => h5 k (by show k ∈ realKeys5 st.params Hb st w rho G3 (g, G5, E); rw [← e5]; exact hk)
  have e5' : realKeys5 st.params Hb st w rho G3 (g, G5', E') = realKeys5 st.params Hb st w rho G3 (g, G5, E') :=
    realKeys5_tables rho G3 g g G5' G5 E'
  have eE' : realKeysE st.params Hb st w rho G3 (g, G5', E') = realKeysE st.params Hb st w rho G3 (g, G5, E') :=
    realKeysE_tables rho G3 g g G5' G5 E'
  refine ⟨?_, ?_⟩
  · unfold rdRO toSp
    dsimp only
    rw [e5', e5, eE', eE]
  · show realROb st.params Hb st w rho G3 (g, G5', E') = realROb st.params Hb st w rho G3 (g, G5, E)
    rw [eP5, eP]

end RealP

end VoleMole.ZK.Sim
