import VoleMole.ZK.GrindNum
import VoleMole.ZK.HopsICPerm
import VoleMole.ZK.TwoPhaseIC
import VoleMole.ZK.SimAcceptFull
import VoleMole.Privacy.MoussakaLean
import VoleMole.Privacy.RatatouilleLean
import VoleMole.Privacy.PomFRITLean

/-!
# Completeness in the random-oracle model, without `Δ' ≠ 0` (`lean/docs/zk.md` §10.1)

The completeness theorems of `Verifier/Bridge/Complete.lean` (`verify_prove_tables`,
`*_complete_tables`) assume that the prover returned a proof and that its `Δ' = Δ·W_CRT` is
nonzero. Here both are probabilistic facts about the prover's randomness: in the random-oracle
model of the zero-knowledge theorems (`recH`: `H₃`, `H₂³` and `H₅` uniform tables, the base
record elsewhere; `ρ` uniform), the honest prover's output is accepted by the verifier (with the
same oracle) except with probability `≤ Pr[GrindBad] ≤ 2⁻¹¹³`.

* `hyb3_delta`: in hybrid H2, outside `GrindBad`, the run returns a proof whose `Δ` is the first
  accepted grinding answer (the first half of `hyb3_vPre`).
* `prove_recH_complete`: so, outside `GrindBad` of the answers at the real prover's grinding
  prefix, `Prover.prove` with the record `recH` returns a proof and `verify` accepts it
  (`verify_prove_tables` with `Δ' ≠ 0` from `¬ GrindBad`).
* **`complete_rom`**: `Pr_{ρ, H₂³, H₃, H₅}[the prover fails or verify rejects] ≤ 2⁻¹¹³` for every
  statement and witness with the deterministic hypotheses `ZKHyp` (a satisfying witness of a
  degree-`≤ d` system); the grinding answers at the prover's prefix are uniform, since the prefix
  does not read `H₂³` (`close_restrict`). `complete_rom_ic`: the same with the CTR PRG the ideal
  cipher of a uniform table `E` (the model of `zk_rom_ic_h23`).
* Per relation, for the instances and witnesses of the privacy games (`Privacy/MoussakaLean.lean`,
  `Privacy/RatatouilleLean.lean`, dedicated label rows): `moussakaIssue_complete_rom`,
  `moussakaRedeem_complete_rom`, `ratatouilleIssue_complete_rom`, `ratatouilleSpend_complete_rom`.
* Two phases (PomFRIT's redemption, `realRun2`): `complete2_rom`, for every continuation with the
  two-phase hypotheses `Hyp2`: whenever the continuation continues with an instance, the final
  proof is accepted for that instance, except with probability `≤ 2⁻¹¹³`;
  `pomfritRedeem_complete_rom` for the Lean PomFRIT prover (`leanProver`, with AES, as
  `runHyp2_lean`).

The error is exactly the grinding term: no accepted grinding answer among the `2³²` (the
prover fails, `≤ 2^{−2¹⁵}`) or a first accepted answer with `Δ' = 0` (`Δ = 0`,
`≤ 1/|A| ≤ 2⁻¹¹⁴`; the verifier rejects at `Δ' = 0`). Nothing else is assumed: BAVC and CRT
completeness are theorems (`Bridge.bavcComplete`, `Bridge.crtComplete`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## One proof -/

section One

variable [HasPrg]
set_option linter.unusedSectionVars false

/-- **The `Δ` of the hybrid-H2 run outside `GrindBad`** is the first accepted grinding answer. -/
theorem hyb3_delta {Hs : Hashes} {st : Statement} {w : ByteArray} (hHs : HashesWF Hs)
    {cs : ByteArray → ByteArray → System GF128} (h : ZKHyp CrtGen.tables st w cs)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (x : Bytes 16 × Bytes 16) (g : Grind) (hg : ¬ GrindBad CrtGen.tables g) :
    ∃ proof, hyb3 Hs CrtGen.tables st w (x.2, g)
        (hiddenOut st.params (ivOfPre Hs st x.2) (ba (deltaOf g)) x.1) = .ok proof ∧
      ({ params := st.params, bytes := proof } : Proof).delta = ba (deltaOf g) := by
  set T := CrtGen.tables
  set wP := w.extract 0 st.params.witnessBytes
  have e1 : hyb2 Hs T st w (x.1, x.2, g) = hyb3 Hs T st w (x.2, g)
      (hiddenOut st.params (ivOfPre Hs st x.2) (ba (deltaOf g)) x.1) := by
    rw [hyb2, ← real_fillSib Hs T st w hHs bavcComplete hlab (pendAt Hs T st wP (x.1, x.2)) rfl
      (size_ba _) (size_ba _), fillSib_tapeAt Hs T st wP x.1 x.2 g, pendAt_iv]
    rfl
  rw [← e1]
  obtain ⟨hnone, -⟩ := not_or.1 hg
  obtain ⟨⟨ctr, δ⟩, hf⟩ := Option.ne_none_iff_exists'.1 hnone
  have hd : deltaOf g = δ := by unfold deltaOf; rw [hf]; rfl
  set t := tapeAt Hs T st.params (pendAt Hs T st wP (x.1, x.2)) g with ht
  have hok : hyb2 Hs T st w (x.1, x.2, g) = .ok (simAssemble st.params t.1 ctr δ
      (fieldsOf Hs T st w cs t.1 (hitOf t.1).1 (hitOf t.1).2 t.2).1) := by
    show proveIdeal Hs T st w (t.1, t.2) = _
    rw [proveIdeal_eq_outOf T st w cs Hs h t.1 t.2]
    unfold outOf
    rw [show t.1.2.1 = g from rfl, hf]
  refine ⟨_, hok, ?_⟩
  rw [hd, simAssemble, (fields_assemble st.params _).2.2.2.2.2.2.1]
  exact fit_of_size (size_ba _)

/-- **The real prover with the random-oracle record is accepted outside `GrindBad`** of the
grinding answers at its own prefix. -/
theorem prove_recH_complete {Hb : Hashes} {st : Statement} {w : ByteArray}
    {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (ρ : Bytes 16) (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5F)
    (hg : ¬ GrindBad CrtGen.tables
      (G2 ∘ key2 st.params (preR Hb CrtGen.tables st w G5 (splitSeed (G3 ρ))))) :
    ∃ proof, Prover.prove (recH Hb st w G3 G2 G5) CrtGen.tables st w (ba ρ) = .ok proof ∧
      (verify (recH Hb st w G3 G2 G5) CrtGen.tables st proof).accept = true := by
  have hwf : HashesWF (recB Hb st w G3 G5) := recH_wf hHb G3 _ G5
  obtain ⟨proof, hok, hdel⟩ := hyb3_delta hwf hzk hlab (splitSeed (G3 ρ)) _ hg
  have hiv : ivOfPre (recB Hb st w G3 G5) st = ivOfPre Hb st :=
    recH_ivOfPre (Hb := Hb) (st := st) (w := w) G3 (fun _ => 0) G5
  rw [hiv] at hok
  have hp : Prover.prove (recH Hb st w G3 G2 G5) CrtGen.tables st w (ba ρ) = .ok proof := by
    rw [prove_recH_eq hzk hHb hlab]
    exact hok
  refine ⟨proof, hp, ?_⟩
  obtain ⟨-, hΔ⟩ := not_or.1 hg
  exact verify_prove_tables _ (recH_wf hHb G3 G2 G5) st w (ba ρ) _ proof hp hlab
    (by rw [hdel]; exact hΔ) cs hzk.hvals hzk.hdeg hzk.hd hzk.hd'

/-- The grinding answers at the real prover's prefix are uniform (the prefix does not read
`H₂³`), so they are bad with probability `≤ 2⁻¹¹³`. -/
theorem pr_grindBad_preR (Hb : Hashes) (st : Statement) (w : ByteArray) :
    pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c => GrindBad CrtGen.tables
      (c.1.2 ∘ key2 st.params (preR Hb CrtGen.tables st w c.2.2 (splitSeed (c.2.1 c.1.1))))) ≤
      1 / 2 ^ 113 := by
  refine pr_le_of_snd fun b => pr_le_of_fst fun ρ => ?_
  have h := close_restrict (R := Bytes 16)
    (key2_injective st.params (preR Hb CrtGen.tables st w b.2 (splitSeed (b.1 ρ))))
    (GrindBad CrtGen.tables)
  rw [abs_nonpos_iff, sub_eq_zero] at h
  exact (le_of_eq h).trans grindBad_le_113

/-- **Completeness in the random-oracle model**: over the prover's `ρ` and the tables `H₃`,
`H₂³`, `H₅` of `recH`, the executable prover fails or its proof is rejected by the executable
verifier (with the same oracle) with probability `≤ 2⁻¹¹³`, for every statement and witness with
the deterministic hypotheses `ZKHyp` and label rows that are corrected rows. -/
theorem complete_rom (Hb : Hashes) (st : Statement) (w : ByteArray)
    {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) :
    pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c => ¬ ∃ proof,
        Prover.prove (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1) = .ok proof ∧
        (verify (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st proof).accept = true) ≤
      1 / 2 ^ 113 :=
  (pr_mono fun c hc => by_contra fun hb =>
    hc (prove_recH_complete hzk hHb hlab c.1.1 c.2.1 c.1.2 c.2.2 hb)).trans
    (pr_grindBad_preR Hb st w)

end One

/-- **`complete_rom` in the ideal-cipher model**: with the CTR PRG of the prover and the verifier
the ideal cipher of a uniform table `E` (`icPrg E`, as in `zk_rom_ic_h23`). -/
theorem complete_rom_ic (Hb : Hashes) (st : Statement) (w : ByteArray)
    {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) :
    pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c => ¬ ∃ proof,
        @Prover.prove (icPrg c.2) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes = .ok proof ∧
        (@verify (icPrg c.2) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st
          proof).accept = true) ≤
      1 / 2 ^ 113 :=
  pr_le_of_snd fun E => @complete_rom (icPrg E) Hb st w cs hzk hHb hlab

/-! ## Per relation (the instances of the privacy games, dedicated label rows) -/

section Relations

variable [HasPrg]

/-- **Moussaka issuance: completeness** in the random-oracle model. -/
theorem moussakaIssue_complete_rom (Hb : Hashes) (hHb : HashesWF Hb)
    (x : Spec.Moussaka.IssueInstance) (w : Spec.Bytes) (h : Moussaka.IssueRelW x w) :
    pr ((Bytes 16 × Tab2G (Moussaka.stI x).params) × (Tab3 × Tab5F)) (fun c => ¬ ∃ proof,
        Prover.prove (recH Hb (Moussaka.stI x) (toBA w) c.2.1 c.1.2 c.2.2) CrtGen.tables
          (Moussaka.stI x) (toBA w) (ba c.1.1) = .ok proof ∧
        (verify (recH Hb (Moussaka.stI x) (toBA w) c.2.1 c.1.2 c.2.2) CrtGen.tables
          (Moussaka.stI x) proof).accept = true) ≤ 1 / 2 ^ 113 :=
  complete_rom Hb _ _ (Moussaka.zkHypI x w h) hHb (hlab_of (show 16 ≤ 256 by decide))

/-- **Moussaka redemption: completeness** in the random-oracle model. -/
theorem moussakaRedeem_complete_rom (Hb : Hashes) (hHb : HashesWF Hb)
    (x : Spec.Moussaka.RedeemInstance) (w : Spec.Bytes) (h : Moussaka.RedeemRelW x w) :
    pr ((Bytes 16 × Tab2G (Moussaka.stR x).params) × (Tab3 × Tab5F)) (fun c => ¬ ∃ proof,
        Prover.prove (recH Hb (Moussaka.stR x) (toBA w) c.2.1 c.1.2 c.2.2) CrtGen.tables
          (Moussaka.stR x) (toBA w) (ba c.1.1) = .ok proof ∧
        (verify (recH Hb (Moussaka.stR x) (toBA w) c.2.1 c.1.2 c.2.2) CrtGen.tables
          (Moussaka.stR x) proof).accept = true) ≤ 1 / 2 ^ 113 :=
  complete_rom Hb _ _ (Moussaka.zkHypR x w h) hHb (hlab_of (show 16 ≤ 343 by decide))

/-- **Ratatouille issuance: completeness** in the random-oracle model. -/
theorem ratatouilleIssue_complete_rom (Hb : Hashes) (hHb : HashesWF Hb)
    (x : Spec.Ratatouille.IssueInstance) (w : Spec.Ratatouille.IssueWitness)
    (h : Spec.Ratatouille.IssueRel x w) :
    pr ((Bytes 16 × Tab2G (Ratatouille.stI x).params) × (Tab3 × Tab5F)) (fun c => ¬ ∃ proof,
        Prover.prove (recH Hb (Ratatouille.stI x) (Ratatouille.encI x w) c.2.1 c.1.2 c.2.2)
          CrtGen.tables (Ratatouille.stI x) (Ratatouille.encI x w) (ba c.1.1) = .ok proof ∧
        (verify (recH Hb (Ratatouille.stI x) (Ratatouille.encI x w) c.2.1 c.1.2 c.2.2)
          CrtGen.tables (Ratatouille.stI x) proof).accept = true) ≤ 1 / 2 ^ 113 :=
  complete_rom Hb _ _ (Ratatouille.zkHypI x w h) hHb (hlab_of (show 16 ≤ 240 by decide))

/-- **Ratatouille spend: completeness** in the random-oracle model. -/
theorem ratatouilleSpend_complete_rom (Hb : Hashes) (hHb : HashesWF Hb)
    (x : Spec.Ratatouille.SpendInstance) (w : Spec.Ratatouille.SpendWitness)
    (h : Spec.Ratatouille.SpendRel x w) :
    pr ((Bytes 16 × Tab2G (Ratatouille.stS x).params) × (Tab3 × Tab5F)) (fun c => ¬ ∃ proof,
        Prover.prove (recH Hb (Ratatouille.stS x) (Ratatouille.encS x w) c.2.1 c.1.2 c.2.2)
          CrtGen.tables (Ratatouille.stS x) (Ratatouille.encS x w) (ba c.1.1) = .ok proof ∧
        (verify (recH Hb (Ratatouille.stS x) (Ratatouille.encS x w) c.2.1 c.1.2 c.2.2)
          CrtGen.tables (Ratatouille.stS x) proof).accept = true) ≤ 1 / 2 ^ 113 :=
  complete_rom Hb _ _ (Ratatouille.zkHypS x w h) hHb (hlab_of (show 16 ≤ 847 by decide))

end Relations

/-! ## Two phases -/

section Two

variable [HasPrg]
set_option linter.unusedSectionVars false

/-- **The real two-phase run with the random-oracle record is accepted outside `GrindBad`**: if
the continuation continues with an instance `y`, the final proof is accepted for `y`. -/
theorem realRun2_complete {Hb : Hashes} {st : Statement} {r : ByteArray} {k : Cont2}
    (hh : Hyp2 st r k) (hHb : HashesWF Hb) (ρ : Bytes 16) (G3 : Tab3) (G2 : Tab2G st.params)
    (G5 : Tab5F)
    (hg : ¬ GrindBad CrtGen.tables
      (G2 ∘ key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r k (splitSeed (G3 ρ)))))
    {y : Inst2} {sfx : ByteArray}
    (hk : k ((realRun2 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k (ba ρ)).1,
      (realRun2 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k (ba ρ)).2.1) = some (y, sfx)) :
    ∃ proof, (realRun2 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k (ba ρ)).2.2 =
        some (.ok proof) ∧
      (verify (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables (withInst st y) proof).accept = true := by
  set R := recH Hb (st1 st) r G3 G2 G5 with hR
  set x := splitSeed (G3 ρ)
  set g := G2 ∘ key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r k x)
  have hRwf : HashesWF R := recH_wf (st := st1 st) (w := r) hHb G3 G2 G5
  have hBwf : HashesWF (recB Hb (st1 st) r G3 G5) := recH_wf (st := st1 st) (w := r) hHb G3 _ G5
  have hreal := real_form Hb st r k hHb hh G3 G2 G5 ρ
  obtain ⟨hnone, hΔ⟩ := not_or.1 hg
  obtain ⟨⟨ctr, δ⟩, hf⟩ := Option.ne_none_iff_exists'.1 hnone
  have hd : deltaOf g = δ := by unfold deltaOf; rw [hf]; rfl
  rcases hk1 : k (out1 (recB Hb (st1 st) r G3 G5) CrtGen.tables st r x) with _ | ⟨y0, sfx0⟩
  · have e := hyb2'_none _ st r k hBwf hh x g hk1
    rw [← hreal] at e
    rw [e] at hk
    exact absurd (hk.symm.trans hk1) (by simp)
  · have e := hyb2'_ok _ st r k hBwf hh x g hf hk1
    rw [← hreal] at e
    have hk' := hk
    rw [e] at hk'
    rw [hk1, Option.some.injEq, Prod.mk.injEq] at hk'
    obtain ⟨rfl, rfl⟩ := hk'
    set prf := simAssemble st.params
      (tapeAt (recB Hb (st1 st) r G3 G5) CrtGen.tables st.params
        (pendAt (recB Hb (st1 st) r G3 G5) CrtGen.tables (st1 st) r x) g).1 ctr δ
      (fieldsOf (recB Hb (st1 st) r G3 G5) CrtGen.tables (withInst st y0) (r ++ sfx0) y0.sys
        (tapeAt (recB Hb (st1 st) r G3 G5) CrtGen.tables st.params
          (pendAt (recB Hb (st1 st) r G3 G5) CrtGen.tables (st1 st) r x) g).1 ctr δ
        (tapeAt (recB Hb (st1 st) r G3 G5) CrtGen.tables st.params
          (pendAt (recB Hb (st1 st) r G3 G5) CrtGen.tables (st1 st) r x) g).2).1 with hprf
    refine ⟨prf, by rw [e], ?_⟩
    -- The final proof is step 2 of the real run.
    have hfin : (k ((step1 R CrtGen.tables st r (ba ρ)).proof,
        (step1 R CrtGen.tables st r (ba ρ)).chal1)).map (fun z =>
          Prover.proveCommit R (withInst st z.1) z.2 (step1 R CrtGen.tables st r (ba ρ))) =
        some (.ok prf) := by
      have := congrArg (fun o : Out2 => o.2.2) e
      exact this
    have hk2 : k ((step1 R CrtGen.tables st r (ba ρ)).proof,
        (step1 R CrtGen.tables st r (ba ρ)).chal1) = some (y0, sfx0) := hk
    rw [hk2, Option.map_some, Option.some.injEq] at hfin
    have hdel : ({ params := (withInst st y0).params, bytes := prf } : Proof).delta = ba δ := by
      show ({ params := st.params, bytes := prf } : Proof).delta = ba δ
      rw [hprf, simAssemble, (fields_assemble st.params _).2.2.2.2.2.2.1]
      exact fit_of_size (size_ba _)
    have hz := hh.hk _ _ _ hk2
    exact verify_proveCommit_tables R hRwf (withInst st y0) _ r (ba ρ) st.binder1 sfx0 prf
      (by simp [Statement.mu1]) rfl hfin hh.hlab (by rw [hdel, ← hd]; exact hΔ) y0.sys
      hz.hvals hz.hdeg hz.hd hz.hd'

/-- **Two-phase completeness in the random-oracle model**: over `ρ` and the tables, the
continuation continues with an instance and the final proof is not an accepted proof for it with
probability `≤ 2⁻¹¹³`, for every continuation with the two-phase hypotheses `Hyp2`. -/
theorem complete2_rom (Hb : Hashes) (st : Statement) (r : ByteArray) (k : Cont2)
    (hh : Hyp2 st r k) (hHb : HashesWF Hb) :
    pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c => ∃ y sfx,
        k ((realRun2 (recH Hb (st1 st) r c.2.1 c.1.2 c.2.2) CrtGen.tables st r k (ba c.1.1)).1,
          (realRun2 (recH Hb (st1 st) r c.2.1 c.1.2 c.2.2) CrtGen.tables st r k
            (ba c.1.1)).2.1) = some (y, sfx) ∧
        ¬ ∃ proof, (realRun2 (recH Hb (st1 st) r c.2.1 c.1.2 c.2.2) CrtGen.tables st r k
            (ba c.1.1)).2.2 = some (.ok proof) ∧
          (verify (recH Hb (st1 st) r c.2.1 c.1.2 c.2.2) CrtGen.tables (withInst st y)
            proof).accept = true) ≤ 1 / 2 ^ 113 := by
  refine (pr_mono (Q := fun c => GrindBad CrtGen.tables (c.1.2 ∘ key2 st.params
    (preP (rec5 Hb c.2.2) CrtGen.tables st r k (splitSeed (c.2.1 c.1.1))))) fun c hc => ?_).trans ?_
  · obtain ⟨y, sfx, hk, hn⟩ := hc
    by_contra hb
    exact hn (realRun2_complete hh hHb c.1.1 c.2.1 c.1.2 c.2.2 hb hk)
  · refine pr_le_of_snd fun b => pr_le_of_fst fun ρ => ?_
    have h := close_restrict (R := Bytes 16)
      (key2_injective st.params (preP (rec5 Hb b.2) CrtGen.tables st r k (splitSeed (b.1 ρ))))
      (GrindBad CrtGen.tables)
    rw [abs_nonpos_iff, sub_eq_zero] at h
    exact (le_of_eq h).trans grindBad_le_113

end Two

/-- **PomFRIT redemption: completeness** of the Lean two-phase prover (`leanProver`, dedicated
label rows) in the random-oracle model: for every witness prefix `r` and valid continuation `k`
(the Issuer's: `P(s) = h ⊕ r`), whenever the continuation continues with `(pk, h, s, b₂)`, the
final proof is accepted for the instance `leanInst pk h b₂`, except with probability `≤ 2⁻¹¹³`. -/
theorem pomfritRedeem_complete_rom (Hb : Hashes) (hHb : HashesWF Hb) (r b : Spec.Bytes)
    (k : PomFRIT.Cont) (hr : r.length = Spec.uovM) (hk : PomFRIT.Cont.Valid r k) :
    pr ((Bytes 16 × Tab2G (PomFRIT.leanBase (toBA b)).params) × (Tab3 × Tab5F)) (fun c => ∃ y sfx,
        PomFRIT.contOf k ((realRun2 (recH Hb (st1 (PomFRIT.leanBase (toBA b))) (toBA r) c.2.1 c.1.2
          c.2.2) CrtGen.tables (PomFRIT.leanBase (toBA b)) (toBA r) (PomFRIT.contOf k)
            (ba c.1.1)).1,
          (realRun2 (recH Hb (st1 (PomFRIT.leanBase (toBA b))) (toBA r) c.2.1 c.1.2 c.2.2)
            CrtGen.tables (PomFRIT.leanBase (toBA b)) (toBA r) (PomFRIT.contOf k)
            (ba c.1.1)).2.1) = some (y, sfx) ∧
        ¬ ∃ proof, (realRun2 (recH Hb (st1 (PomFRIT.leanBase (toBA b))) (toBA r) c.2.1 c.1.2 c.2.2)
            CrtGen.tables (PomFRIT.leanBase (toBA b)) (toBA r) (PomFRIT.contOf k)
            (ba c.1.1)).2.2 = some (.ok proof) ∧
          (verify (recH Hb (st1 (PomFRIT.leanBase (toBA b))) (toBA r) c.2.1 c.1.2 c.2.2)
            CrtGen.tables (withInst (PomFRIT.leanBase (toBA b)) y) proof).accept = true) ≤
      1 / 2 ^ 113 := by
  have hh : Hyp2 (PomFRIT.leanBase (toBA b)) (toBA r) (PomFRIT.contOf k) :=
    { hk := (PomFRIT.runHyp2_lean Hb CrtGen.tables hHb bavcComplete maskInvOk_tables r b k hr hk
        fun rho => crtComplete Hb _ _ _ rho _ (hlab_of (show 16 ≤ 164 by decide))).hk
      hr := by rw [size_toBA, hr]; show 45 ≤ 164; decide
      hlr := rfl
      hnm := show 2 - 1 + 4 ≤ 32 by decide }
  exact complete2_rom Hb (PomFRIT.leanBase (toBA b)) (toBA r) (PomFRIT.contOf k) hh hHb

end VoleMole.ZK.Sim
