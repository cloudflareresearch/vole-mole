import VoleMole.Assumptions.BlindPomfrit
import VoleMole.ROM.ProverIC
import VoleMole.ZK.CompleteRO

/-!
# The Lean PomFRIT client as oracle computations, and its completeness per table

`lean/docs/security/pomfrit.md` §6.4, G9. Theorem 6 at PomFRIT (`Assumptions/BlindPomfrit.lean`,
`pomfrit_T6`) holds for any client given as oracle computations over the hashes and the cipher
(`PomClient`), up to the client's completeness term `compFail`. Here is the Lean client.

**The client** (`leanClient T lr`). Its coins are a 32-byte seed. Session `k` (message `msgOf k`)
derives its prover randomness `rho` and its `refresher` from the seed as `issue_request_with_seed`
does (`Spec.PomFRIT.expandSeed`, `sessOf`); its witness prefix is `r = 0` (`zeroPre`: the forger of
T6 does not blind, `P(s) = H_T(x) ⊕ 0`). Step 1 is `issue_request`'s `voleith_vole_gen`
(`step1Q` of `ROM/ProverIC.lean`, with `mu₁ = H₂⁴(DST ‖ 12)` queried), the binder
`refresher_com = H_ref(refresher)`; the step-1 signature bytes are step 1's proof. Step 2 is
`finalize_issue`'s `voleith_prove_commit` for the statement with target `h = H_T(x)`
(`pomStmt`, i.e. `pomfritRedeemT` with that target) and witness suffix the Issuer's preimage
(`proveCommitQ`); the signature is `proof ‖ refresher_com ‖ refresher`.

**Agreement with the executable prover** (`eval_start`, `eval_finish`): against complete tables
`g` (hashes) and `E` (cipher), step 1 is `Bridge.pomfritPending` (`Prover.voleGen`) and step 2 is
`Prover.proveCommit`, with the hashes of `g` and the ideal-cipher PRG of `E`.

**Completeness per table** (for any PRG, any hash record with the right output lengths):
* `pom_complete`: if the Issuer's `σ` is a preimage of the target `u` (`relP`), then outside
  `GrindBad` of the `H₂³` answers at step 2's grinding prefix (`ZK.Sim.realGrind`,
  `ZK.Sim.realPre`), step 2 returns a proof and the verifier accepts it for `pomStmt` (from
  `ZK.Sim.proveCommit_eq_proveIdeal`, `ZK.Sim.proveIdeal_eq_outOf` and
  `Bridge.verify_proveCommit_tables`; the witness `0 ‖ σ` satisfies PomFRIT's system,
  `Privacy.PomFRIT.leanInst_holds`).
* `chal1Pre_honest`: the verifier's steps up to `chal1` on an honest final proof return step 1's
  `chal1` (so the verifier's `hash_to_target` input is the client's label).
* `tgtIn_final`: the `hash_to_target` input of the final signature is the client's label (step 2
  keeps `ũ` and `d[0..45)`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.OneMore
  VoleMole.ROM.OneMore.Pomfrit VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
  VoleMole.Arith
open scoped ENNReal

namespace VoleMole.Assumptions.BlindPomfrit

/-! ## The client -/

section Client

/-- The witness prefix `r = 0` (45 bytes). -/
def zeroPre : ByteArray := Prover.zeros 45

/-- **Session `k`'s randomness** from the seed (`issue_request_with_seed`'s `XOF_seed`): `rho`,
`refresher_com = H_ref(refresher)`, `refresher`. -/
def sessOf (pk : UovPk) (κ : Prob.Bytes 32) (k : ℕ) : ByteArray × ByteArray × ByteArray :=
  let e := Spec.PomFRIT.expandSeed (toL pk.digest) (toL (msgOf k)) (toL κ.ba)
  (toBA e.1, toBA (Spec.PomFRIT.commitRefresher e.2.1), toBA e.2.1)

/-- **The statement of step 2**: PomFRIT redemption with the target `u` and the binders. -/
def pomStmt (pk : UovPk) (lr : Bool) (u : TG) (b1 b2 : ByteArray) : Statement :=
  pomfritRedeemT pk (fun _ => encT u) b1 b2 lr

/-- The statement step 1 runs for (no target yet; step 1 reads only its parameters, `mu₁` and
binder). -/
def pomStmt0 (pk : UovPk) (lr : Bool) (b1 b2 : ByteArray) : Statement :=
  pomfritRedeemT pk (fun _ => ByteArray.empty) b1 b2 lr

/-- The client's state between the steps: step 1's pending proof and the binders. -/
abbrev PSt := Prover.Pending × ByteArray × ByteArray

/-- **The Lean PomFRIT client** (`issue_request` / `finalize_issue` with the Lean prover, witness
prefix `0`), as oracle computations over the hashes and the cipher. -/
noncomputable def leanClient (T : CrtTables) (lr : Bool) : PomClient (Prob.Bytes 32) PSt where
  coins := $ᵗ (Prob.Bytes 32)
  start pk κ k := do
    let sd := sessOf pk κ k
    let mu1 ← liftIC (mu1Q (pomStmt0 pk lr sd.2.1 sd.2.2))
    let s ← step1Q T (pomfritParams lr) mu1 zeroPre sd.1 sd.2.1
    pure (s.proof, s.chal1, (s, sd.2.1, sd.2.2))
  finish pk _ _ st u sv := match sv with
    | none => pure ByteArray.empty
    | some σ => do
      let r ← liftIC (proveCommitQ (pomStmt pk lr u st.2.1 st.2.2) (toBA σ) st.1)
      pure ((r.toOption.getD ByteArray.empty) ++ st.2.1 ++ st.2.2)

/-- **The executable step 1 of the client** with the hashes `Hs` (`Bridge.pomfritPending`). -/
def pendOf [HasPrg] (Hs : Hashes) (T : CrtTables) (lr : Bool) (rho b1 : ByteArray) :
    Prover.Pending :=
  pomfritPending Hs T lr zeroPre rho b1

variable (g : Table) (E : CTable) (T : CrtTables) (lr : Bool) (pk : UovPk) (κ : Prob.Bytes 32)

/-- **Per table, the client's step 1 is the executable prover's** (`Prover.voleGen` with the
hashes of `g` and the ideal-cipher PRG of `E`). -/
theorem eval_start (k : ℕ) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) ((leanClient T lr).start pk κ k) =
      let s := @pendOf (icPrg E.cipher) (Hashes.ofTable g) T lr (sessOf pk κ k).1 (sessOf pk κ k).2.1
      (s.proof, s.chal1, (s, (sessOf pk κ k).2.1, (sessOf pk κ k).2.2)) := by
  simp only [leanClient, evalWithAnswerFn_bind, evalWithAnswerFn_liftIC, evalWithAnswerFn_mu1Q,
    eval_step1Q, evalWithAnswerFn_pure]
  rfl

/-- **Per table, the client's step 2 is the executable prover's** (`Prover.proveCommit`). -/
theorem eval_finish (k : ℕ) (st : PSt) (u : TG) (σ : Spec.Bytes) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) ((leanClient T lr).finish pk κ k st u (some σ)) =
      ((Prover.proveCommit (Hashes.ofTable g) (pomStmt pk lr u st.2.1 st.2.2) (toBA σ)
        st.1).toOption.getD ByteArray.empty) ++ st.2.1 ++ st.2.2 := by
  simp only [leanClient, evalWithAnswerFn_bind, evalWithAnswerFn_liftIC, eval_proveCommitQ,
    evalWithAnswerFn_pure]

end Client

/-! ## Completeness per table -/

lemma hashesWF_ofTable (g : Table) : HashesWF (Hashes.ofTable g) := fun _ _ => Prob.Bytes.size_ba _

lemma xorBytes_zero (h : Spec.Bytes) : Spec.xorBytes h (List.replicate h.length 0) = h := by
  induction h with
  | nil => rfl
  | cons a l ih =>
    simp only [Spec.xorBytes, List.length_cons, List.replicate_succ, List.zipWith_cons_cons] at ih ⊢
    rw [ih, UInt8.xor_zero]

lemma size_zeroPre : zeroPre.size = 45 := by simp [zeroPre, Prover.zeros, ByteArray.size]

lemma length_toL_encT (u : TG) : (toL (encT u)).length = 45 := by
  simp only [encT, EndToEnd.SpecRel.toL_toBA, List.length_ofFn]

lemma toBA_toL_eq (b : ByteArray) : toBA (toL b) = b := by
  rw [Privacy.toL_eq]
  cases b
  rfl

section Det

variable [HasPrg]

/-- The system of `pomStmt`. -/
noncomputable def pomSys (pk : UovPk) (u : TG) : ByteArray → ByteArray → System Arith.GF128 :=
  fun _ lb => PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map
    (Privacy.PomFRIT.targetOf (encT u)) (ofArr (combinationOf 45 lb))

omit [HasPrg] in
/-- **The deterministic hypotheses of the zero-knowledge/completeness chain** for `pomStmt` with
the witness `0 ‖ σ`, `σ` a preimage of the target `u`. -/
lemma zkHyp_pom (pk : UovPk) (lr : Bool) (u : TG) (b1 b2 : ByteArray) (σ : Spec.Bytes)
    (hσ : relP pk (some σ) u) :
    ZKHyp CrtGen.tables (pomStmt pk lr u b1 b2) (zeroPre ++ toBA σ) (pomSys pk u) := by
  obtain ⟨σ', hσ', hlen, hev⟩ := hσ
  cases hσ'
  have hw : (zeroPre ++ toBA σ).size = 164 := by
    rw [ByteArray.size_append, size_zeroPre, Privacy.size_toBA, hlen]
  have hz : zeroPre = toBA (List.replicate 45 0) := by
    simp only [zeroPre, Prover.zeros, toBA, List.toArray_replicate]
  refine ⟨fun c1 lb x => ?_, fun _ _ => ?_, ?_, ?_, fun c1 lb => ?_, hw, ?_, ZK.maskInvOk_tables, ?_⟩
  · exact pomfritRedeemT_values pk (fun _ => encT u) b1 b2 lr c1 lb x
  · exact PomFRIT.degree_pomfritRedeemSystem _ _ _ _ _ _ _
  · show 1 ≤ 2; norm_num
  · show 2 + 1 < 2 ^ 64; norm_num
  · have h45 := length_toL_encT u
    have e := Privacy.PomFRIT.leanInst_holds pk.toSpec (toL (encT u)) (List.replicate 45 0) σ b2
      (by simp [Spec.uovM]) h45 hlen (by
        rw [hev]
        have := xorBytes_zero (toL (encT u))
        rw [h45] at this
        exact this.symm) c1 lb
    have hs : ZK.wSlope (pomStmt pk lr u b1 b2).params (zeroPre ++ toBA σ) =
        ZK.wSlope (pomfritParams true) (toBA (List.replicate 45 0) ++ toBA σ) := by
      rw [hz]; funext j; rfl
    rw [hs]
    have ht : toBA (toL (encT u)) = encT u := toBA_toL_eq _
    rw [ht] at e
    exact e
  · show (pomfritParams lr).nMask ≤ 32
    cases lr <;> decide
  · exact ZK.Interp.interpOk_two

omit [HasPrg] in
/-- `Δ'` of a proof whose `Δ` is the first accepted grinding answer `δ`. -/
lemma hΔ_of {p : Params} {proof : ByteArray} {δ : Bytes 16}
    (hd : ({ params := p, bytes := proof } : Proof).delta = ba δ)
    (h : tDL CrtGen.tables δ ≠ 0) :
    (W128.rowMul (BAVC.deltaBit ({ params := p, bytes := proof } : Proof).delta) 120
      CrtGen.tables.wCrt).toGF ≠ 0 := by
  rw [hd]; exact h

variable (Hs : Hashes)

/-- **Completeness of the client per table**: if `σ` is a preimage of `u`, then outside `GrindBad`
of the grinding answers at step 2's prefix, step 2 returns a proof that the verifier accepts. -/
theorem pom_complete (pk : UovPk) (lr : Bool) (rho b1 b2 : ByteArray) (u : TG) (σ : Spec.Bytes)
    (hσ : relP pk (some σ) u) (hHs : HashesWF Hs)
    (hg : ¬ GrindBad CrtGen.tables (realGrind Hs (realPre Hs (pomStmt pk lr u b1 b2)
      (pendOf Hs CrtGen.tables lr rho b1) (zeroPre ++ toBA σ)))) :
    ∃ proof, Prover.proveCommit Hs (pomStmt pk lr u b1 b2) (toBA σ)
        (pendOf Hs CrtGen.tables lr rho b1) = .ok proof ∧
      (verify Hs CrtGen.tables (pomStmt pk lr u b1 b2) proof).accept = true := by
  set st := pomStmt pk lr u b1 b2 with hst
  have hzk := zkHyp_pom pk lr u b1 b2 σ hσ
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows :=
    hlab_of (show 16 ≤ 164 by decide)
  have hpend : pendOf Hs CrtGen.tables lr rho b1 =
      Prover.voleGen Hs CrtGen.tables st.params (st.mu1 Hs) zeroPre rho st.binder1 := rfl
  have e1 := proveCommit_eq_proveIdeal Hs CrtGen.tables st zeroPre (toBA σ) rho (pomSys pk u)
    ⟨hzk.hvals, hzk.hdeg, hzk.hd, hzk.hd', hzk.hsat, hzk.hw, hzk.hI⟩ hHs bavcComplete
    (crtComplete Hs _ _ _ rho _ hlab) hlab
  rw [← hpend] at e1
  set gr := realGrind Hs (realPre Hs st (pendOf Hs CrtGen.tables lr rho b1) (zeroPre ++ toBA σ))
  set t := tapeAt Hs CrtGen.tables st.params (pendOf Hs CrtGen.tables lr rho b1) gr with ht
  obtain ⟨hnone, hΔ⟩ := not_or.1 hg
  obtain ⟨⟨ctr, δ⟩, hf⟩ := Option.ne_none_iff_exists'.1 hnone
  have hd : deltaOf gr = δ := by unfold deltaOf; rw [hf]; rfl
  have hok : Prover.proveCommit Hs st (toBA σ) (pendOf Hs CrtGen.tables lr rho b1) =
      .ok (simAssemble st.params t.1 ctr δ
        (fieldsOf Hs CrtGen.tables st (zeroPre ++ toBA σ) (pomSys pk u) t.1 (hitOf t.1).1
          (hitOf t.1).2 t.2).1) := by
    rw [e1]
    show proveIdeal Hs CrtGen.tables st (zeroPre ++ toBA σ) (t.1, t.2) = _
    rw [proveIdeal_eq_outOf CrtGen.tables st (zeroPre ++ toBA σ) (pomSys pk u) Hs hzk t.1 t.2]
    unfold outOf
    rw [show t.1.2.1 = gr from rfl, hf]
  refine ⟨_, hok, ?_⟩
  refine verify_proveCommit_tables Hs hHs st (st.mu1 Hs) zeroPre rho st.binder1 (toBA σ) _ rfl rfl
    hok hlab (hΔ_of (δ := δ) ?_ (by rw [← hd]; exact hΔ)) (pomSys pk u) hzk.hvals hzk.hdeg hzk.hd hzk.hd'
  rw [simAssemble, (fields_assemble st.params _).2.2.2.2.2.2.1]
  exact fit_of_size (size_ba _)

/-- **The verifier's steps up to `chal1` on an honest final proof return step 1's `chal1`**, for
any statement of step 2 (`st'`) and the statement `st` that fixes step 1's parameters, `mu₁` and
binder. -/
theorem chal1Pre_honest (g : Table) (T : CrtTables) (st st' : Statement)
    (wPrefix rho wSuffix proof : ByteArray)
    (h : Prover.proveCommit (Hashes.ofTable g) st' wSuffix
      (Prover.voleGen (Hashes.ofTable g) T st.params (st.mu1 (Hashes.ofTable g)) wPrefix rho
        st.binder1) = .ok proof) :
    evalWithAnswerFn (QueryImpl.ofFn g) (chal1Pre st proof) =
      some (Prover.voleGen (Hashes.ofTable g) T st.params (st.mu1 (Hashes.ofTable g)) wPrefix rho
        st.binder1).chal1 := by
  set Hs := Hashes.ofTable g with hHsdef
  have hHs : HashesWF Hs := hashesWF_ofTable g
  set p := st.params with hp
  have spec := voleGen_spec Hs T p (st.mu1 Hs) wPrefix rho st.binder1
  have hinv := proveCommit_inv h
  generalize Prover.voleGen Hs T p (st.mu1 Hs) wPrefix rho st.binder1 = s at spec hinv ⊢
  obtain ⟨hsp, -, hsiv, hsivp, hstree, hsleaves, -, -, hsfiv, -, -, -, -, -, hsc1, -, -⟩ := spec
  dsimp only at hinv
  rw [hsp] at hinv
  obtain ⟨-, check, aT, ctr, delta, opening, -, hfind, hproof⟩ := hinv
  obtain ⟨k, hk⟩ := findFirst_some _ _ _ hfind
  obtain ⟨-, hdelta, h15, hopen⟩ := grindStep_some hk
  subst hproof
  set ff : Prover.Fields := { s.fields with
      correction := ⟨(Array.range p.witnessBytes).map fun k =>
        (bytesOfWords s.u).get! k ^^^ (s.wPrefix ++ wSuffix).get! k⟩,
      qsProof := Prover.gfsToBytes aT, opening := opening, delta := delta,
      ctr := AES.pushLE32 ByteArray.empty ctr.toUInt32 } with hff
  obtain ⟨hC, hM, -, -, -, hO, hDl, hI, -, hSz⟩ := fields_assemble p ff
  obtain ⟨hC0, hM0, -, -, -, -, -, hI0, -, -⟩ :=
    fields_assemble p { s.fields with voleCheck := .empty, correction := .empty }
  have hd16 : delta.size = 16 := by rw [hdelta]; exact hHs _ _
  have hivs : s.ivPre.size = 16 := by rw [hsivp, ByteArray.size_extract, hHs]; rfl
  have pfDelta : ({ params := p, bytes := Prover.assemble p ff } : Proof).delta = delta := by
    rw [hDl]; exact fit_of_size hd16
  have pfIv : ({ params := p, bytes := Prover.assemble p ff } : Proof).ivPre = s.ivPre := by
    rw [hI]; show Prover.fit s.fields.ivPre 16 = _; rw [hsfiv]; exact fit_of_size hivs
  obtain ⟨leaves, hrec, hcoms, -⟩ :=
    bavcComplete s.seed s.iv delta opening (by rw [← hstree, ← hsleaves]; exact hopen)
  rw [← hsleaves] at hcoms
  have hfmt : ({ params := p, bytes := Prover.assemble p ff } : Proof).checkFormat = true := by
    show (_ == p.proofBytes && _ == 0) = true
    rw [pfDelta, h15, hSz]
    simp
  have hc1 : chal1 Hs ({ params := p, bytes := Prover.assemble p ff } : Proof) (st.mu1 Hs)
      (BAVC.check (Hs.hash .h1) leaves.coms) st.binder1 = s.chal1 := by
    rw [hsc1, hcoms]
    simp only [chal1, chal1Input, step1Proof]
    rw [hC, hM, hI, hC0, hM0, hI0]
  unfold chal1Pre
  simp only [← hp]
  simp only [hfmt, Bool.not_true, Bool.false_eq_true, ite_false, evalWithAnswerFn_bind,
    evalWithAnswerFn_mu1Q, evalWithAnswerFn_hashQ]
  rw [show (Hashes.ofTable g).hash .h4
      ((({ params := p, bytes := Prover.assemble p ff } : Proof).ivPre ++ st.mu1 Hs).push 4) = s.iv
    by rw [pfIv, hsiv]]
  rw [pfDelta, show ({ params := p, bytes := Prover.assemble p ff } : Proof).opening =
    Prover.fit opening BAVC.openSize from hO, hrec]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_mapM_hashQ, evalWithAnswerFn_hashQ,
    evalWithAnswerFn_pure]
  rw [← hc1]
  rfl

/-- **The `hash_to_target` input of the final signature is the client's label**: step 2 keeps
`ũ` and `d[0..45)` of step 1's proof, and `chal1` and the message are the session's. -/
theorem tgtIn_final (Hs : Hashes) (hHs : HashesWF Hs) (pk : UovPk) (lr : Bool) (k : ℕ)
    (rho b1 b2 : ByteArray) (hb1 : b1.size = 32) (hb2 : b2.size = 32) (st' : Statement)
    (wSuffix proof : ByteArray)
    (h : Prover.proveCommit Hs st' wSuffix (pendOf Hs CrtGen.tables lr rho b1) = .ok proof) :
    tgtIn pk lr (proof ++ b1 ++ b2) (msgOf k) (pendOf Hs CrtGen.tables lr rho b1).chal1 =
      label pk lr k (pendOf Hs CrtGen.tables lr rho b1).proof
        (pendOf Hs CrtGen.tables lr rho b1).chal1 := by
  set s := pendOf Hs CrtGen.tables lr rho b1 with hsdef
  set p := pomfritParams lr
  have hsp : s.params = p := rfl
  obtain ⟨-, check, aT, ctr, delta, opening, -, -, hproof⟩ := proveCommit_inv h
  rw [hsp] at hproof
  have hps : proof.size = p.proofBytes := by
    rw [hproof]; exact (fields_assemble _ _).2.2.2.2.2.2.2.2.2
  have hs1 : s.proof.size = p.proofBytes := Pending_proof_size s
  have hc1 : s.chal1.size = 136 := hHs _ _
  obtain ⟨e0, -, -⟩ := Privacy.PomFRIT.sig_parts hps hb1 hb2
  unfold label
  rw [fit_of_size hs1, fit_of_size hc1]
  unfold tgtIn
  dsimp only
  rw [e0, show s.proof.extract 0 p.proofBytes = s.proof by
    rw [← hs1]; exact ByteArray.extract_zero_size]
  have hv2 : (⟨p, s.proof⟩ : Proof).voleCheck = Prover.fit s.fields.voleCheck 64 :=
    (fields_assemble p s.fields).2.2.1
  have hc2 : (⟨p, s.proof⟩ : Proof).correction = Prover.fit s.fields.correction p.witnessBytes :=
    (fields_assemble p s.fields).2.2.2.1
  have hv1 : (⟨p, proof⟩ : Proof).voleCheck = Prover.fit s.fields.voleCheck 64 := by
    rw [hproof]; exact (fields_assemble p _).2.2.1
  have hcc : (⟨p, proof⟩ : Proof).correction = Prover.fit
      ⟨(Array.range p.witnessBytes).map fun k =>
        (bytesOfWords s.u).get! k ^^^ (s.wPrefix ++ wSuffix).get! k⟩ p.witnessBytes := by
    rw [hproof]; exact (fields_assemble p _).2.2.2.1
  have hwb : 45 ≤ p.witnessBytes := show 45 ≤ 164 by decide
  have hpre : s.fields.correction = ⟨(Array.range zeroPre.size).map fun k =>
      (bytesOfWords s.u).get! k ^^^ zeroPre.get! k⟩ := rfl
  have hcor : (⟨p, proof⟩ : Proof).correction.extract 0 45 =
      (⟨p, s.proof⟩ : Proof).correction.extract 0 45 := by
    rw [hcc, hc2, hpre, Privacy.PomFRIT.fit_extract hwb
      (by rw [Privacy.PomFRIT.size_mk_range_map]; exact hwb),
      Privacy.PomFRIT.fit_extract hwb (by rw [Privacy.PomFRIT.size_mk_range_map, size_zeroPre]),
      extract_range_map _ hwb, extract_range_map _ (le_of_eq size_zeroPre.symm)]
    refine congrArg ByteArray.mk (Array.map_congr_left fun j hj => ?_)
    have hj' := Array.mem_range.1 hj
    rw [get!_append, show s.wPrefix = zeroPre from rfl, size_zeroPre, ite_eq_left (by omega)]
  show toBA (Spec.PomFRIT.targetInput _ _ (toL (⟨p, proof⟩ : Proof).voleCheck)
      (toL ((⟨p, proof⟩ : Proof).correction.extract 0 45)) _) =
    toBA (Spec.PomFRIT.targetInput _ _ (toL (⟨p, s.proof⟩ : Proof).voleCheck)
      (toL ((⟨p, s.proof⟩ : Proof).correction.extract 0 45)) _)
  rw [hcor, hv1, hv2]

end Det

end VoleMole.Assumptions.BlindPomfrit
