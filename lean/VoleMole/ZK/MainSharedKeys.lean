import VoleMole.ZK.AdaptRO
import VoleMole.ZK.HopsMainIC

/-!
# The `H₅` keys of a `main`-layout proof, as functions of the proof (`lean/docs/zk.md` §4.2)

With one `H₅` table for several proofs, the candidates for the witness prefix of one proof include
the `H₅` reads of the other proofs. This file writes those reads, and the candidates, as functions
of the **proof bytes** (and the cipher), so that the same event makes sense whether a proof is real
or simulated.

* `vInOff Hs T st b off`: the verifier's gate inputs of the proof `b` with the label offset `off`,
  `iv ‖ e ‖ (L_e(q) ⊕ off) ‖ 5` (`vIn5` is `off = 0`, `vIn5_eq_vInOff`). It reads the cipher at
  the reconstruction's nodes (`vInOff_ic_congr`) and no table.
* `dPre p b`: the first 16 bytes of the proof's witness correction `d`.
* **A simulated proof** (`vInOff_simAssemble`, `dPre_simAssemble`): the inputs are the gate inputs
  at the simulator's `iv` and key columns, `d[0..16)` is the simulator's field. So a candidate of
  `candidatesG` for the witness prefix `r` is `thetaMain d[0..16) r = 0`, or a key of the read set
  that is a gate input at offset `thetaMain d[0..16) r` (`cand_imp`).
* **A real proof** (`prove_reads`, item (i) of `lean/docs/zk.md` §4.2): the executable prover reads
  `H₅` at `vgIn5`, the gate inputs with both labels of its own tags. If it outputs the proof `b`,
  each of them is a verifier's gate input of `b` at offset `0` (the active label) or at offset
  `thetaMain (dPre b) w[0..16)` (the sibling label: on `main` the label offset is
  `d[0..16) ⊕ w[0..16)`). So the real prover's `H₅` read set is a function of its output and its
  witness prefix.
-/

open Finset

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

attribute [local instance] decEqW128

/-! ## The verifier's gate inputs with a label offset -/

section VIn

variable [HasPrg] (Hs : Hashes) (T : CrtTables) (st : Statement)

/-- **The verifier's gate inputs of a proof, with the label offset `off`**:
`iv ‖ e ‖ (L_e(q) ⊕ off) ‖ 5` at the verifier's key columns (none if the opening is malformed). -/
def vInOff (proof : ByteArray) (off : W128) : List ByteArray :=
  let pf : Proof := { params := st.params, bytes := proof }
  match BAVC.reconstruct (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta with
  | none => []
  | some leaves => Prover.gateInputsOff st.params T (ivOf Hs pf (st.mu1 Hs))
      (convertToVole pf (ivOf Hs pf (st.mu1 Hs)) leaves) off

lemma vIn5_eq_vInOff (proof : ByteArray) : vIn5 Hs T st proof = vInOff Hs T st proof W128.zero := by
  unfold vIn5 vInOff
  dsimp only
  rcases BAVC.reconstruct (ivOf Hs { params := st.params, bytes := proof } (st.mu1 Hs))
    (Proof.opening { params := st.params, bytes := proof })
    (Proof.delta { params := st.params, bytes := proof }) with _ | leaves
  · rfl
  · simp only [gateInputs_eq_off]

variable {Hs}

lemma vInOff_congr {Hs' : Hashes} (hmu : st.mu1 Hs = st.mu1 Hs') (h4 : Hs.hash .h4 = Hs'.hash .h4) :
    vInOff Hs T st = vInOff Hs' T st := by
  funext proof off
  simp only [vInOff, ivOf, hmu, h4]

variable (Hs)

/-- On a proof assembled from a shared tape, the verifier's gate inputs are the gate inputs at
the tape's `iv` and key columns. -/
theorem vInOff_simAssemble (s : Shared) (ctr : ℕ) (δ : Bytes 16) (f : SimFields st.params)
    (hf : firstHit s.2.1 = some (ctr, δ)) (off : W128) :
    vInOff Hs T st (simAssemble st.params s ctr δ f) off = Prover.gateInputsOff st.params T
      (pubOf Hs st s δ).iv (qcolsOf st (pubOf Hs st s δ) δ (ba f.1)) off := by
  have hacc := firstHit_accepts hf
  have hoc : openCount (ba δ) ≤ 105 := by
    unfold accepts at hacc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc; exact hacc.2
  set pf : Proof := { params := st.params, bytes := simAssemble st.params s ctr δ f } with hpf
  have pfC : pf.corrections = ba f.1 :=
    (fields_assemble st.params _).1.trans (fit_of_size (size_ba _))
  have pfO : pf.opening = openingOf (ba δ) s.2.2.1 s.2.2.2 :=
    (fields_assemble st.params _).2.2.2.2.2.1.trans (fit_of_size (openingOf_size _ _ _ hoc))
  have pfD : pf.delta = ba δ := (fields_assemble st.params _).2.2.2.2.2.2.1.trans
    (fit_of_size (size_ba _))
  have pfI : pf.ivPre = ba s.1 := (fields_assemble st.params _).2.2.2.2.2.2.2.1.trans
    (fit_of_size (size_ba _))
  have hiv : ivOf Hs pf (st.mu1 Hs) = (pubOf Hs st s δ).iv := by rw [ivOf, pfI]; rfl
  obtain ⟨leaves, hl⟩ := Option.isSome_iff_exists.1
    (reconstruct_openingOf (pubOf Hs st s δ).iv (ba δ) s.2.2.1 s.2.2.2 hoc)
  unfold vInOff
  simp only [← hpf, hiv, pfO, pfD, hl]
  have hP : (pubOf Hs st s δ).leaves = leaves := by
    show (BAVC.reconstruct (pubOf Hs st s δ).iv (openingOf (ba δ) s.2.2.1 s.2.2.2) (ba δ)).getD _ = _
    rw [hl]; rfl
  have hco : pf.correctionOf = fun i =>
      (ba f.1).extract ((i - 1) * st.params.correctionBytes) (i * st.params.correctionBytes) := by
    funext i; rw [Proof.correctionOf, pfC]
  have hq : convertToVole pf (pubOf Hs st s δ).iv leaves =
      qcolsOf st (pubOf Hs st s δ) δ (ba f.1) := by
    rw [qcolsOf, hP, convertToVole, pfD, hco]
  rw [hq]

end VIn

/-- **The verifier's gate inputs read the cipher only at the reconstruction's reads.** -/
theorem vInOff_ic_congr (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (off : W128) {E E' : Cipher}
    (h : ∀ k ∈ rdKeys E (ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs)) (⟨st.params, proof⟩ : Proof).opening
      (⟨st.params, proof⟩ : Proof).delta, E k = E' k) :
    @vInOff (icPrg E) Hs T st proof off = @vInOff (icPrg E') Hs T st proof off := by
  set pf : Proof := ⟨st.params, proof⟩ with hpf
  have hr := reconstruct_ic_congr h
  unfold vInOff
  rcases hl : @BAVC.reconstruct (icPrg E) (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta with _ | leaves
  · simp only [← hpf, ← hr, hl]
  · have hc : @convertToVole (icPrg E) pf (ivOf Hs pf (st.mu1 Hs)) leaves =
        @convertToVole (icPrg E') pf (ivOf Hs pf (st.mu1 Hs)) leaves := by
      unfold convertToVole
      refine convertToVoleAt_ic_congr _ _ _ _ _ fun i hi j hj hjd hs => h _ ?_
      have := @leafKey_mem_rdKeys E (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta i j hi hj hjd
      rw [hl, Option.getD_some] at this
      exact this hs
    simp only [← hpf, ← hr, hl, hc]

/-! ## `d[0..16)` of a proof -/

/-- **The first 16 bytes of a proof's witness correction `d`.** -/
def dPre (p : Params) (proof : ByteArray) : Bytes 16 :=
  fun k => (Proof.correction { params := p, bytes := proof }).get! k

lemma dPre_simAssemble {p : Params} (hw : 16 ≤ p.witnessBytes) (s : Shared) (ctr : ℕ) (δ : Bytes 16)
    (f : SimFields p) : dPre p (simAssemble p s ctr δ f) = pre16 hw f.2.2.2.1 := by
  funext k
  have h : (Proof.correction { params := p, bytes := simAssemble p s ctr δ f }) = ba f.2.2.2.1 :=
    (fields_assemble p _).2.2.2.1.trans (fit_of_size (size_ba _))
  simp only [dPre, h, pre16]
  exact get!_ba _ (by omega)

/-! ## A candidate of a simulated proof, in terms of the proof -/

section Cand

variable [HasPrg] (Hs : Hashes) (T : CrtTables) (st : Statement)

/-- **A candidate of `candidatesG`, in terms of the simulated proof**: `r` is a candidate for the
witness prefix iff the label offset `thetaMain d[0..16) r` is zero, or some key of the read set is
a verifier's gate input of the proof at that offset. -/
theorem cand_imp (hm : MainP st.params) (S : Finset (Bytes 37)) (s : Shared)
    (f : SimFields st.params) {ctr : ℕ} {δ : Bytes 16} (hf : firstHit s.2.1 = some (ctr, δ))
    {r : Bytes 16} (hr : r ∈ candidatesG Hs T st enc5 hm S s f) :
    thetaMain (dPre st.params (simAssemble st.params s ctr δ f)) r = W128.zero ∨
      ∃ k ∈ S, enc5 k ∈ vInOff Hs T st (simAssemble st.params s ctr δ f)
        (thetaMain (dPre st.params (simAssemble st.params s ctr δ f)) r) := by
  have hd : deltaOf s.2.1 = δ := by unfold deltaOf; rw [hf]; rfl
  rw [mem_candidatesG, guessSetG, Finset.mem_insert, Finset.mem_biUnion] at hr
  rw [dPre_simAssemble hm.hw]
  rcases hr with hr | ⟨k, hk, hv⟩
  · exact Or.inl hr
  · refine Or.inr ⟨k, hk, ?_⟩
    unfold guessOfG at hv
    split at hv
    · rename_i hex
      rw [Finset.mem_singleton] at hv
      obtain ⟨e, he⟩ := hex.choose_spec
      rw [← hv, qcolsF, hd] at he
      rw [vInOff_simAssemble Hs T st s ctr δ f hf, he]
      exact getD_mem_of_lt (by rw [gateInputsOff_length]; exact e.isLt)
    · simp at hv

end Cand

/-! ## The real prover's `H₅` reads, in terms of its proof -/

section Real

variable [HasPrg] (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **The executable prover's `H₅` reads are gate inputs of its proof** (`main`'s layout). If the
prover outputs the proof `b`, every `H₅` input it reads (`vgIn5`: both labels of each gate, at its
own tags) is a verifier's gate input of `b` at offset `0`, or at the offset
`thetaMain (dPre b) w[0..16)`. -/
theorem prove_reads {cs : ByteArray → ByteArray → System GF128} (hm : MainP st.params)
    (h : ZKHyp T st w cs) (hHs : HashesWF Hs) (hbavc : BAVCComplete) (rho : ByteArray)
    (hcrt : CrtComplete (Hs.hash .h5) T (Prover.voleGen Hs T st.params (st.mu1 Hs)
      (w.extract 0 st.params.witnessBytes) rho st.binder1))
    {b : ByteArray} (hb : Prover.prove Hs T st w rho = .ok b) :
    ∀ x ∈ vgIn5 Hs T st.params (st.mu1 Hs)
        ((Hs.hash .h3 ((w.extract 0 st.params.witnessBytes ++ st.mu1 Hs ++ rho).push 3)).extract 0 16)
        ((Hs.hash .h3 ((w.extract 0 st.params.witnessBytes ++ st.mu1 Hs ++ rho).push 3)).extract 16 32),
      x ∈ vInOff Hs T st b W128.zero ∨
        x ∈ vInOff Hs T st b (thetaMain (dPre st.params b) (wPre w)) := by
  have hlab := hm.hlab
  rw [prove_eq_proveIdeal Hs T st w rho cs h.q hHs hbavc hcrt hlab, tapeOf_eq_tapeAt] at hb
  set s := Prover.voleGen Hs T st.params (st.mu1 Hs) (w.extract 0 st.params.witnessBytes) rho
    st.binder1 with hs
  set g := realGrind Hs (realPre Hs st s w) with hg
  rcases hf : firstHit g with _ | ⟨ctr, δ⟩
  · unfold proveIdeal tapeAt at hb
    simp only [hf] at hb
    split at hb <;> cases hb
  have hacc := firstHit_accepts hf
  have hoc : openCount (ba δ) ≤ 105 := by
    unfold accepts at hacc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc; exact hacc.2
  obtain ⟨opening, hopen⟩ := Option.isSome_iff_exists.1
    (show (BAVC.openAt s.tree s.leaves.coms (ba δ)).isSome by rw [openAt_isSome]; simpa using hoc)
  obtain ⟨hus, hu0, hcorr, -, hPiv, -, hqcols, -, -, -⟩ :=
    step1_real Hs T st s hs.symm hHs hbavc hlab g ctr (size_ba δ) hopen
  rw [blk_ba] at hPiv hqcols
  set sh : Shared := (blk 16 s.ivPre, g, comsOf s.leaves.coms (ba δ), seedsOf s.tree (ba δ)) with hsh
  set t := realPads Hs T st.params s (ba δ) with ht
  have htape : tapeAt Hs T st.params s g = (sh, t) := by
    unfold tapeAt
    simp only [hf, Option.map_some, Option.getD_some]
    rfl
  rw [htape, proveIdeal_eq_outOf T st w cs Hs h sh t] at hb
  have hfs : firstHit sh.2.1 = some (ctr, δ) := hf
  unfold outOf at hb
  rw [hfs] at hb
  simp only [Except.ok.injEq] at hb
  have hhit : hitOf sh = (ctr, δ) := by unfold hitOf; rw [hfs]; rfl
  rw [hhit] at hb
  subst hb
  set F := (fieldsOf Hs T st w cs sh ctr δ t).1 with hF
  -- The verifier's gate inputs of the proof.
  have hV : ∀ off, vInOff Hs T st (simAssemble st.params sh ctr δ F) off =
      Prover.gateInputsOff st.params T s.iv (convertToVoleAt st.params (BAVC.deltaBit (ba δ))
        (proverCorr st.params s.iv (leafKey s.leaves)) s.iv (leafKey s.leaves)) off := by
    intro off
    rw [vInOff_simAssemble Hs T st sh ctr δ F hfs off, hPiv]
    have : ba F.1 = s.fields.corrections := by
      rw [← hcorr, ← hus, correctionsOf_eq]; rfl
    rw [this, hqcols]
  -- The label offset.
  have hθ : thetaMain (dPre st.params (simAssemble st.params sh ctr δ F)) (wPre w) =
      uPreOf st.params s.u := by
    rw [dPre_simAssemble hm.hw, ← hu0, ← hus]
    exact (uPre_main_dB hm w t).symm
  rw [hV, hV, hθ]
  set qc := convertToVoleAt st.params (BAVC.deltaBit (ba δ))
    (proverCorr st.params s.iv (leafKey s.leaves)) s.iv (leafKey s.leaves) with hqc
  have hq : ∀ c < 120, st.params.colBytes / 8 ≤ (qc[c]!).size :=
    fun _ hc => convertToVoleAt_col_size _ _ _ _ _ hc
  -- The prover's gate inputs, on its tags.
  have spec := voleGen_spec Hs T st.params (st.mu1 Hs) (w.extract 0 st.params.witnessBytes) rho
    st.binder1
  rw [← hs] at spec
  obtain ⟨-, -, -, -, -, -, hsu, -⟩ := spec
  have hcongr : ∀ off, Prover.gateInputsOff st.params T s.iv
      (Prover.senderColumns st.params s.iv (leafKey s.leaves)) off =
      Prover.gateInputsOff st.params T s.iv (tagCols (BAVC.deltaBit (ba δ)) qc s.u) off :=
    fun off => (gateInputsOff_congr _ _ _ off fun c hc k hk => by
      rw [hsu]; exact wbit_tagCols _ _ _ _ hc (by omega)).symm
  intro x hx
  have hx' : x ∈ Prover.gateInputsOff st.params T s.iv
        (Prover.senderColumns st.params s.iv (leafKey s.leaves)) W128.zero ++
      Prover.gateInputsOff st.params T s.iv
        (Prover.senderColumns st.params s.iv (leafKey s.leaves)) (uPreOf st.params s.u) := hx
  rw [hcongr, hcongr, List.mem_append] at hx'
  have key : ∀ off, off = W128.zero ∨ off = uPreOf st.params s.u →
      x ∈ Prover.gateInputsOff st.params T s.iv (tagCols (BAVC.deltaBit (ba δ)) qc s.u) off →
      x ∈ Prover.gateInputsOff st.params T s.iv qc W128.zero ∨
        x ∈ Prover.gateInputsOff st.params T s.iv qc (uPreOf st.params s.u) := by
    intro off hoff hmem
    obtain ⟨e, he, hxe⟩ := List.mem_iff_getElem.1 hmem
    have he' : e < 312 := by rw [gateInputsOff_length] at he; exact he
    rw [← List.getD_eq_getElem _ ByteArray.empty he,
      gateInputsOff_tagCols st.params T hlab s.iv _ qc s.u hq off he'] at hxe
    have hmem' : ∀ o, (Prover.gateInputsOff st.params T s.iv qc o).getD e .empty ∈
        Prover.gateInputsOff st.params T s.iv qc o :=
      fun o => getD_mem_of_lt (by rw [gateInputsOff_length]; exact he')
    rw [← hxe]
    rcases hoff with rfl | rfl <;> split
    · rw [zero_xor']; exact Or.inr (hmem' _)
    · rw [xor_zero']; exact Or.inl (hmem' _)
    · rw [xor_xor_self]; exact Or.inl (hmem' _)
    · rw [xor_zero']; exact Or.inr (hmem' _)
  rcases hx' with hx' | hx'
  · exact key _ (Or.inl rfl) hx'
  · exact key _ (Or.inr rfl) hx'

end Real

end VoleMole.ZK.Sim
