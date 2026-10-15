import VoleMole.ZK.SimAccept
import VoleMole.ZK.HopsRead

/-!
# The grinding prefix the verifier recomputes from a proof (`lean/docs/zk.md` §5, §10.1)

The simulator in the programmable random-oracle model (`Sim.simulateRO`) programs `H₂³` at the
grinding points of its proof, `chal2 ‖ qs_check ‖ ã ‖ ctr ‖ 11`, with `chal2` and `qs_check`
recomputed from the proof as the verifier does (`programPoints`). Here:

* `vPre Hs T st proof`: that prefix `chal2 ‖ qs_check ‖ ã`, the verifier's steps up to `chal3`
  (without the format and `Δ' ≠ 0` tests, which do not change it). `vPre_eq_verify`: when the
  verifier's run reaches `chal3`, it is the prefix of `programPoints`.
* **`vPre_proveCommit`** (completeness of the recomputation): for a proof of the executable
  prover, with `Δ' ≠ 0`, the recomputed prefix is the prover's own grinding prefix (`realPre`).
  The proof is `Bridge.verify_proveCommit`'s, stopped before `chal3`.
* `vPre` reads neither `H₃` nor `H₂³` (`vPre_agreeOff`), and `H₅` only at the verifier's gate
  inputs `gateInputs` at the key columns (`vIn5`, `vPre_h5_congr`).
-/

open Finset

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK

/-! ## The recomputed prefix -/

section Def

variable (Hs : Hashes) (T : CrtTables) (st : Statement)

/-- The verifier's `chal2 ‖ qs_check ‖ ã` from the proof `pf` and the reconstructed leaves. -/
def vPreOf (pf : Proof) (leaves : BAVC.Leaves) : ByteArray :=
  let c1 := chal1 Hs pf (st.mu1 Hs) (BAVC.check (Hs.hash .h1) leaves.coms) st.binder1
  let crt := crtReconstruct Hs pf T (ivOf Hs pf (st.mu1 Hs))
    (convertToVole pf (ivOf Hs pf (st.mu1 Hs)) leaves)
  let deltaL := crt.deltaLifted.toGF
  let hV := voleHashReceiver st.params c1 crt.rows crt.qMask deltaL pf.voleCheck
  let c2 := chal2 Hs pf c1 hV (st.muDelayed Hs c1) st.binder2
  let cs := constraintKeys st.params (correctedKeys pf crt.rows deltaL) deltaL
    (st.values c1 (st.combBytes Hs c2))
  c2 ++ gfToBytes (qsCheck pf c2 cs crt.qMask deltaL) ++ pf.qsProof

/-- `vPreOf`, after the BAVC reconstruction (empty if the opening is malformed). -/
def vPreP (pf : Proof) : ByteArray :=
  match BAVC.reconstruct (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta with
  | none => ByteArray.empty
  | some leaves => vPreOf Hs T st pf leaves

/-- **The grinding prefix `chal2 ‖ qs_check ‖ ã` the verifier recomputes from a proof.** -/
def vPre (proof : ByteArray) : ByteArray := vPreP Hs T st { params := st.params, bytes := proof }

/-- `vPreOf`, unfolded (for `intro`). -/
lemma vPreOf_iff (pf : Proof) (leaves : BAVC.Leaves) (X : ByteArray) :
    vPreOf Hs T st pf leaves = X ↔
      let c1 := chal1 Hs pf (st.mu1 Hs) (BAVC.check (Hs.hash .h1) leaves.coms) st.binder1
      let crt := crtReconstruct Hs pf T (ivOf Hs pf (st.mu1 Hs))
        (convertToVole pf (ivOf Hs pf (st.mu1 Hs)) leaves)
      let deltaL := crt.deltaLifted.toGF
      let hV := voleHashReceiver st.params c1 crt.rows crt.qMask deltaL pf.voleCheck
      let c2 := chal2 Hs pf c1 hV (st.muDelayed Hs c1) st.binder2
      let cs := constraintKeys st.params (correctedKeys pf crt.rows deltaL) deltaL
        (st.values c1 (st.combBytes Hs c2))
      c2 ++ gfToBytes (qsCheck pf c2 cs crt.qMask deltaL) ++ pf.qsProof = X := Iff.rfl

/-- **When the verifier's run reaches `chal3`, `vPre` is the prefix of `programPoints`** (the
points `simulateRO` programs). -/
theorem vPre_eq_verify (proof : ByteArray) (h : Reaches Hs T st proof) :
    vPre Hs T st proof = (verify Hs T st proof).chal2 ++ (verify Hs T st proof).qsCheck ++
      ({ params := st.params, bytes := proof } : Proof).qsProof := by
  obtain ⟨hf, leaves, hl, hΔ⟩ := h
  obtain ⟨h2, h3, -⟩ := verify_reaches Hs T st proof _ rfl leaves hf hl hΔ
  rw [h2, h3, vPre, vPreP, hl]
  rfl

end Def

/-! ## Completeness of the recomputation -/

/-- **The verifier recomputes the prover's grinding prefix.** If `Prover.proveCommit` (after
`Prover.voleGen`) returns a proof with `Δ' ≠ 0`, the prefix `vPre` recomputed from it is the
prover's `chal2 ‖ qs_check ‖ ã` (`realPre`). Assumed as in `verify_proveCommit`: BAVC and CRT
completeness (proved for the real tables: `bavcComplete`, `crtComplete`). -/
theorem vPre_proveCommit (Hs : Hashes) (hHs : HashesWF Hs) (hbavc : BAVCComplete) (T : CrtTables)
    (st : Statement) (mu1 wPrefix rho binder1 wSuffix proof : ByteArray)
    (hmu : st.mu1 Hs = mu1) (hb1 : st.binder1 = binder1)
    (h : Prover.proveCommit Hs st wSuffix
      (Prover.voleGen Hs T st.params mu1 wPrefix rho binder1) = .ok proof)
    (hcrt : CrtComplete (Hs.hash .h5) T (Prover.voleGen Hs T st.params mu1 wPrefix rho binder1))
    (hΔ : (W128.rowMul (BAVC.deltaBit ({ params := st.params, bytes := proof } : Proof).delta) 120
      T.wCrt).toGF ≠ 0)
    (cs : ByteArray → ByteArray → System GF128)
    (hvals : ∀ c1 lb x, st.values c1 lb x = (cs c1 lb).values x)
    (hdeg : ∀ c1 lb, ∀ e ∈ cs c1 lb, e.degree ≤ st.params.qsDegree)
    (hd : 1 ≤ st.params.qsDegree) (hd' : st.params.qsDegree + 1 < 2 ^ 64) :
    vPre Hs T st proof =
      realPre Hs st (Prover.voleGen Hs T st.params mu1 wPrefix rho binder1) (wPrefix ++ wSuffix) := by
  set p := st.params with hp
  have spec := voleGen_spec Hs T p mu1 wPrefix rho binder1
  have hinv := proveCommit_inv h
  generalize Prover.voleGen Hs T p mu1 wPrefix rho binder1 = s at spec hinv hcrt
  obtain ⟨hsp, hsw, hsiv, hsivp, hstree, hsleaves, hsu, hscorr, hsfiv, hsqs, hsvrows, hsvs, hsvm,
    hsum, hsc1, hsvc, hshv⟩ := spec
  dsimp only at hinv
  unfold CrtComplete at hcrt
  simp only [hsp] at hinv hcrt
  obtain ⟨hw, check, aT, ctr, delta, opening, hqsp, hfind, hproof⟩ := hinv
  obtain ⟨k, hk⟩ := findFirst_some _ _ _ hfind
  obtain ⟨hck, hdelta, h15, hopen⟩ := grindStep_some hk
  subst hck
  set key := leafKey s.leaves with hkey
  set w := s.wPrefix ++ wSuffix with hwdef
  set correction : ByteArray :=
    ⟨(Array.range p.witnessBytes).map fun k => (bytesOfWords s.u).get! k ^^^ w.get! k⟩ with hcorrdef
  set f1 : Prover.Fields :=
    { corrections := s.fields.corrections, cmult := s.fields.cmult,
      voleCheck := s.fields.voleCheck, correction := correction, qsProof := s.fields.qsProof,
      opening := s.fields.opening, delta := s.fields.delta, ivPre := s.fields.ivPre,
      ctr := s.fields.ctr } with hf1
  set pf1 : Proof := { params := p, bytes := Prover.assemble p f1 } with hpf1
  set c2 := chal2 Hs pf1 s.chal1 s.hV (st.muDelayed Hs s.chal1) st.binder2 with hc2
  set ff : Prover.Fields :=
    { corrections := f1.corrections, cmult := f1.cmult, voleCheck := f1.voleCheck,
      correction := f1.correction, qsProof := Prover.gfsToBytes aT, opening := opening,
      delta := delta, ivPre := f1.ivPre, ctr := AES.pushLE32 ByteArray.empty ctr.toUInt32 } with hff
  subst hproof
  set f0 : Prover.Fields := { s.fields with voleCheck := .empty, correction := .empty } with hf0
  obtain ⟨hC, hM, hV, hD, hQ, hO, hDl, hI, hCt, hSz⟩ := fields_assemble p ff
  obtain ⟨hC1, hM1, hV1, hD1, hQ1, -, -, -, -, -⟩ := fields_assemble p f1
  obtain ⟨hC0, hM0, -, -, -, -, -, hI0, -, -⟩ := fields_assemble p f0
  -- Sizes.
  have hd16 : delta.size = 16 := by rw [hdelta]; exact hHs _ _
  have hivs : s.ivPre.size = 16 := by rw [hsivp, ByteArray.size_extract, hHs]; rfl
  have hu : s.u.size = p.colBytes / 8 := by
    rw [hsu, proverU]
    exact (smallVoleUWords_spec p s.iv 0 (key 0) (r := 0) (by
      simp only [Params.colBytes, Params.voleColBlocks, Params.voleRows, Params.nMask]; omega)).1
  have hcsz : ∀ i, (proverCorr p s.iv key i).size = p.correctionBytes := fun i =>
    correctionOf_size p _ _ (by rw [← hsu]; exact hu)
  have hCsz : s.fields.corrections.size = 16 * p.correctionBytes := by
    rw [hscorr, show (List.range (BAVC.tau - 1)).foldl
        (fun acc j => acc ++ proverCorr p s.iv key (j + 1)) ByteArray.empty =
      ((List.range (BAVC.tau - 1)).map fun j => proverCorr p s.iv key (j + 1)).foldl (· ++ ·)
        ByteArray.empty by simp [List.foldl_map], size_foldl_append, List.map_map]
    simp only [Function.comp_def, hcsz, List.map_const', List.length_range, List.sum_replicate,
      smul_eq_mul]
    rfl
  have hvcs : s.fields.voleCheck.size = 64 := by rw [hsvc, gfsToBytes_size, voleHashReceiver_size]
  have hcorrs : correction.size = p.witnessBytes := by simp [correction, ByteArray.size]
  have haTs := qsProve_aT_size hqsp
  -- The fields of the final proof.
  have pfDelta : ({ params := p, bytes := Prover.assemble p ff } : Proof).delta = delta := by
    rw [hDl]; exact fit_of_size hd16
  have pfIv : ({ params := p, bytes := Prover.assemble p ff } : Proof).ivPre = s.ivPre := by
    rw [hI]; show Prover.fit s.fields.ivPre 16 = _; rw [hsfiv]; exact fit_of_size hivs
  have pfOpen : ({ params := p, bytes := Prover.assemble p ff } : Proof).opening =
      Prover.fit opening BAVC.openSize := hO
  have pfCorr : ∀ i, 1 ≤ i → i < BAVC.tau →
      ({ params := p, bytes := Prover.assemble p ff } : Proof).correctionOf i =
        proverCorr p s.iv key i := by
    intro i hi1 hi
    rw [Proof.correctionOf, hC, show ff.corrections = s.fields.corrections from rfl,
      fit_of_size hCsz, hscorr]
    exact correctionOf_concat p (proverCorr p s.iv key) hcsz hi1 hi
  have pfCm : ({ params := p, bytes := Prover.assemble p ff } : Proof).cmult =
      Prover.fit s.fields.cmult (p.nMask * p.nMultBytes) := hM
  have pfVc :
      ({ params := p, bytes := Prover.assemble p ff } : Proof).voleCheck = s.fields.voleCheck := by
    rw [hV]; exact fit_of_size hvcs
  have pfD : ({ params := p, bytes := Prover.assemble p ff } : Proof).correction = correction := by
    rw [hD]; exact fit_of_size hcorrs
  have pfQs :
      ({ params := p, bytes := Prover.assemble p ff } : Proof).qsProof = Prover.gfsToBytes aT := by
    rw [hQ]; exact fit_of_size (by rw [gfsToBytes_size, haTs]; ring)
  have pfCt : ({ params := p, bytes := Prover.assemble p ff } : Proof).ctr =
      AES.pushLE32 ByteArray.empty ctr.toUInt32 := by
    rw [hCt]; exact fit_of_size (pushLE32_size _)
  set pf : Proof := { params := p, bytes := Prover.assemble p ff } with hpfdef
  -- The verifier's run.
  have hiv : ivOf Hs pf (st.mu1 Hs) = s.iv := by rw [hmu, ivOf, pfIv, hsiv]
  obtain ⟨leaves, hrec, hcoms, hkeys⟩ :=
    hbavc s.seed s.iv delta opening (by rw [← hstree, ← hsleaves]; exact hopen)
  rw [← hsleaves] at hcoms hkeys
  have hrec' : BAVC.reconstruct (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta = some leaves := by
    rw [hiv, pfOpen, pfDelta]; exact hrec
  have hv : vPre Hs T st (Prover.assemble p ff) = vPreOf Hs T st pf leaves := by
    show vPreP Hs T st pf = _
    unfold vPreP
    rw [hrec']
  have hpre : realPre Hs st s w = c2 ++ gfToBytes check ++ Prover.gfsToBytes aT := by
    have hq' : Prover.qsProve
        { params := st.params, bytes := Prover.assemble st.params (realF1 st.params s w) }
        (realC2 Hs st s w) (st.values s.chal1 (st.combBytes Hs (realC2 Hs st s w)))
        s.vRows s.vMask s.uMask w = .ok (check, aT) := hqsp
    rw [realPre, hq']
    rfl
  rw [show wPrefix ++ wSuffix = w by rw [hwdef, hsw], hv, hpre]
  apply (vPreOf_iff Hs T st pf leaves _).2
  intro c1 crt deltaL hVv c2v csv
  have hc1 : c1 = s.chal1 := by
    show chal1 Hs pf (st.mu1 Hs) (BAVC.check (Hs.hash .h1) leaves.coms) st.binder1 = s.chal1
    rw [hsc1, hmu, hcoms, hb1]
    simp only [chal1, chal1Input, step1Proof]
    rw [hC, hM, hI, hC0, hM0, hI0]
  have hcols : convertToVole pf (ivOf Hs pf (st.mu1 Hs)) leaves =
      convertToVoleAt p (BAVC.deltaBit delta) (proverCorr p s.iv key) s.iv key := by
    rw [hiv, convertToVole, pfDelta,
      convertToVoleAt_congr_key p _ _ s.iv (key' := key) fun i hi j hj hjd => hkeys i hi j hj hjd]
    exact convertToVoleAt_congr_corr p _ s.iv key pfCorr
  have hcrt' : crt = crtReconstructAt (Hs.hash .h5) p (BAVC.deltaBit delta)
      (Prover.fit s.fields.cmult (p.nMask * p.nMultBytes)) T s.iv
      (convertToVoleAt p (BAVC.deltaBit delta) (proverCorr p s.iv key) s.iv key) := by
    show crtReconstruct Hs pf T (ivOf Hs pf (st.mu1 Hs))
      (convertToVole pf (ivOf Hs pf (st.mu1 Hs)) leaves) = _
    rw [hcols, crtReconstruct, pfDelta, pfCm, hiv]
  have hdl : deltaL = (W128.rowMul (BAVC.deltaBit delta) 120 T.wCrt).toGF := by
    show crt.deltaLifted.toGF = _
    rw [hcrt']; rfl
  have hrows : ∀ r < p.correctionRows,
      crt.rows[r]!.toGF = s.vRows[r]!.toGF + (if wbit s.u r then 1 else 0) * deltaL := by
    intro r hr
    rw [hcrt', hdl, prover_row _ (gateWords ((Prover.gateInputsOff p T s.iv
      (Prover.senderColumns p s.iv key) W128.zero).map (Hs.hash .h5))) _ _ _ ByteArray.empty _ _ _
      hr,
      hsvrows, hsu]
  have hmask : ∀ m < p.nMask,
      crt.qMask[m]!.toGF = s.vMask[m]!.toGF + s.uMask[m]!.toGF * deltaL := by
    intro m hm
    rw [hcrt', hdl]
    exact hcrt _ m hm
  have hrs : crt.rows.size = p.correctionRows := by
    rw [hcrt']; simp only [crtReconstructAt, crtReconstructWith, Array.size_map, Array.size_range]
  have hms : crt.qMask.size = p.nMask := by
    rw [hcrt']; simp only [crtReconstructAt, crtReconstructWith, Array.size_map, Array.size_range]
  have hhV : hVv = s.hV := by
    show voleHashReceiver p c1 crt.rows crt.qMask deltaL pf.voleCheck = s.hV
    rw [hc1, pfVc, hsvc, hshv]
    exact voleHash_complete p s.chal1 s.vRows s.vMask s.uMask crt.rows crt.qMask s.u deltaL _ _
      hrs hsvs hms hsvm hsum hrows hmask
  have hc2v : c2v = c2 := by
    show chal2 Hs pf c1 hVv (st.muDelayed Hs c1) st.binder2 = c2
    rw [hc1, hhV, hc2]
    simp only [chal2, chal2Input]
    rw [hV, hD, hV1, hD1]
  have hΔ' : deltaL ≠ 0 := by rw [hdl, ← pfDelta]; exact hΔ
  -- QuickSilver: the check value is the prover's.
  have hkeys' : correctedKeys pf crt.rows deltaL = Prover.qsKeys p s.vRows w deltaL :=
    correctedKeys_prover pf crt.rows s.vRows s.u w deltaL
      (by
        show p.witnessBits ≤ 64 * s.u.size
        have := correctionRows_lt p; simp only [Params.correctionRows] at this; rw [hu]; omega)
      (fun r hr => hrows r (by
        have hr' : r < p.witnessBits := hr
        simp only [Params.correctionRows]; omega)) pfD
  have hmasks : crt.qMask = Prover.qsMasks p s.vMask s.uMask deltaL := by
    apply Array.ext
    · simp [Prover.qsMasks, hms]
    intro m h1 h2
    have hm : m < p.nMask := by rwa [hms] at h1
    rw [← getElem!_pos crt.qMask m h1]
    simp only [Prover.qsMasks, Array.getElem_map, Array.getElem_range, ← hmask m hm]
    rfl
  have h0 : ∀ i, gfOfBytes pf1.qsProof (16 * i) = 0 := by
    intro i
    rw [hQ1, show f1.qsProof = s.fields.qsProof from rfl, hsqs, fit_empty, gfOfBytes_zeros]
  have hqs := qsProve_complete pf1 c2 _ s.vRows s.vMask s.uMask w hqsp
    (cs s.chal1 (st.combBytes Hs c2))
    (hvals _ _) (hdeg _ _) hd hd' h0 pf rfl pfQs hΔ'
  have hcheck : qsCheck pf c2v (constraintKeys st.params (correctedKeys pf crt.rows deltaL) deltaL
      (st.values c1 (st.combBytes Hs c2v))) crt.qMask deltaL = check := by
    rw [hkeys', hmasks, hc1, hc2v]
    exact hqs
  show c2v ++ gfToBytes (qsCheck pf c2v (constraintKeys st.params (correctedKeys pf crt.rows deltaL)
    deltaL (st.values c1 (st.combBytes Hs c2v))) crt.qMask deltaL) ++ pf.qsProof = _
  rw [hcheck, hc2v, pfQs]

end VoleMole.ZK.Sim
