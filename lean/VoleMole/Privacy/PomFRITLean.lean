import VoleMole.ZK.TwoPhase
import VoleMole.ZK.Interp
import VoleMole.Privacy.PomFRIT
import VoleMole.Privacy.LeanProver

/-!
# PomFRIT blindness with the executable Lean prover (`security/pomfrit.md` §8.2, `zk.md` §10.1)

`Privacy.PomFRIT.blindness` assumes two-phase zero knowledge (`Privacy.PomFRIT.ZeroKnowledge`) of an
abstract prover. Here the prover is the executable Lean prover (`Verifier/Prover.lean`) with
dedicated label rows, run as PomFRIT runs it: step 1 (`issue_request_with_seed`) with the witness
prefix `r` and the binder `refresher_com`; the Client then hashes the instance `h` from step 1's
output (`hash_to_target` reads `chal1`, `ũ` and `d[0..M)`); step 2 (`finalize_issue`) with the
Signer's response `s` and the binder `refresher`. Its two-phase zero knowledge is derived from
`ZK.Sim.twoPhase_close` (`ZK/TwoPhase.lean`).

* `leanBase b`: the statement step 1 runs for (PomFRIT's parameters with label rows, DST, binder
  `b`); `leanInst pk h b₂`: the instance part (`pomfritRedeem` with the target `h` given), with
  the system it evaluates (`pomfritRedeemSystem`).
* `leanProver Hs T`: the Lean prover as `Spec.PomFRIT.Prover`; `leanSim Hs`: the two-phase
  simulator as `Privacy.PomFRIT.Simulator` (`ZK.Sim.simRun2`: step 1's fields uniform with
  `chal1` the verifier's, step 2's proof `Sim.simulate`'s).
* `runHyp2_lean`: for a valid continuation (`P(s) = h ⊕ r`) the deterministic hypotheses of the
  two-phase theorem hold for every instance it picks (`leanInst_holds`, from
  `Arith.PomFRIT.pomfrit_complete_gf128`: the witness `r ‖ s` satisfies the system for every
  `chal1` and combination, since `h` is fixed once picked; `InterpOk 2` from `ZK/Interp.lean`).
* **`lean_zeroKnowledge`**: `Privacy.PomFRIT.ZeroKnowledge (leanProver Hs T) (leanSim Hs) ε` from
  the two-phase tape hypothesis `TapeHyp2` (`ε`) for every prefix, binder and valid continuation.
* **`blindness_lean`**: the blindness game on the label-row layout (`Spec.PomFRIT.Layout.labelRows`)
  with the Lean prover: `≤ 4ε`.
* `pomfritVerify_complete`: `pomfritVerify` accepts the final signature
  `proof ‖ refresher_com ‖ refresher` (step 2 keeps `ũ` and `d[0..M)`, so the verifier's target is
  the Client's; `Bridge.pomfritRedeem_complete`).

**On `main` this is false**: the label offset is a function of `r` there, the Issuer learns `r`
(`ZK.issuerGuess_eq`), its sibling-label query hits with probability 1
(`ZK.pomfrit_issuer_hits`), and the test of `lean/docs/zk.md` Prop. 4.1 accepts every real proof
(`ZK.pomfrit_attack_test`), all in `ZK/Relations.lean`. With label rows the offset Θ is a separate
uniform pad that step 1 does not reveal (`ZK/TwoPhase.lean`: step 1's fields are uniform).

Remaining hypotheses: the tape hypothesis `TapeHyp2`, `BAVCComplete` and `CrtComplete` for step 1
(both checked by `prover_vectors`), `HashesWF Hs`, and the CRT certificate `maskInvOk T` (proved
for `CrtGen.tables`, `ZK.maskInvOk_tables`).
-/

open Finset

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT

/-! ## The prover and the simulator -/

/-- PomFRIT's DST (`POMFRIT_REDEEM_DST`). -/
def leanDst : ByteArray := toBA (makeDst "pomf" 0 'p' '0')

/-- The statement step 1 runs for: PomFRIT's parameters with dedicated label rows, its DST and
the `chal1` binder `b` (`refresher_com`). -/
def leanBase (b : ByteArray) : Statement :=
  { params := pomfritParams true, dst := leanDst, delayed := true, binder1 := b,
    instEnc := fun _ => .empty, values := fun _ _ _ => [] }

/-- `h` as `M` elements of GF(256). -/
def targetOf (h : ByteArray) : Fin uovM → GF256 := fun k => ⟨fnOf h k.val⟩

/-- PomFRIT's instance part for the key `pk`, the target `h` and the `chal2` binder `b₂`
(`refresher`): `pomfritRedeem` with `h` given, and the system `pomfritRedeemSystem` it
evaluates. -/
def leanInst (pk : UOVKey) (h b₂ : ByteArray) : Inst2 where
  instEnc := fun _ => toBA pk.digest ++ h
  comb := some (45, toBA (makeDst "pomf" 0 'l' '0'))
  values := fun _ lb w =>
    UovEval.pomfritRedeemValues 119 45 pk.map (targetOf h) (combinationOf 45 lb) w
  binder2 := b₂
  sys := fun _ lb =>
    PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map (targetOf h)
      (ofArr (combinationOf 45 lb))

/-- **The Lean prover as PomFRIT's two-phase prover**: step 1 is `ZK.Sim.step1` (`Prover.voleGen`
with `mu₁ = H₂⁴(DST ‖ 12)`); its state keeps the binder; step 2 is `Prover.proveCommit` for
`leanInst` (a failed run gives the empty proof). -/
def leanProver (Hs : Hashes) (T : CrtTables) : Prover (ByteArray × Prover.Pending) where
  voleGen r rho b :=
    let s := step1 Hs T (leanBase (toBA b)) (toBA r) (toBA rho)
    (toL s.proof, toL s.chal1, (toBA b, s))
  proveCommit _ pk h sfx b₂ st :=
    toL ((Prover.proveCommit Hs (withInst (leanBase st.1) (leanInst pk (toBA h) (toBA b₂)))
      (toBA sfx) st.2).toOption.getD .empty)

/-- **The two-phase simulator**: `simRun2`'s step 1, and its step-2 proof as the state. -/
def leanSim (Hs : Hashes) : Simulator (SimCoins2 (pomfritParams true)) Bytes where
  phase1 b c :=
    match firstHit c.1.1.2.1 with
    | none => (toL (ba c.2.1), toL (ba c.2.2), [])
    | some (ctr, delta) =>
      let o := simPhase1 Hs (st1 (leanBase (toBA b))) uovM c.1.1 ctr delta c.1.2
      (toL o.1, toL o.2, toL (simAssemble (pomfritParams true) c.1.1 ctr delta c.1.2))
  phase2 _ _ _ _ σ := σ

-- The label-row layout of `Spec/PomFRITLayout.lean` is the Lean prover's (`pomfritParams true`).
#guard (pomfritParams true).proofBytes == Layout.labelRows.proofBytes &&
  (pomfritParams true).field? "vole_check" ==
    some (Layout.labelRows.offVoleCheck, voleCheckBytes) &&
  ((pomfritParams true).field? "correction").map (·.1) == some Layout.labelRows.offCorrection

/-- The spec's continuation as one on byte arrays, with `leanInst`. -/
def contOf (k : Cont) : Cont2 := fun o =>
  (k (toL o.1, toL o.2)).map fun i => (leanInst i.1 (toBA i.2.1) (toBA i.2.2.2), toBA i.2.2.1)

/-- Two-phase outputs as the spec's. -/
def outOf (o : Out2) : Bytes × Bytes × Option Bytes :=
  (toL o.1, toL o.2.1, o.2.2.map fun e => toL (e.toOption.getD .empty))

lemma realRun_lean (Hs : Hashes) (T : CrtTables) (r b : Bytes) (k : Cont) (ρ : Coins 16) :
    realRun (leanProver Hs T) r b k ρ =
      outOf (realRun2 Hs T (leanBase (toBA b)) (toBA r) (contOf k) (ba ρ)) := by
  simp only [realRun, leanProver, realRun2, outOf, contOf, toBA_ofFn, Option.map_map]
  rfl

lemma simRun_lean (Hs : Hashes) (b : Bytes) (k : Cont) (c : SimCoins2 (pomfritParams true)) :
    simRun (leanSim Hs) b k c = outOf (simRun2 Hs (leanBase (toBA b)) uovM (contOf k) c) := by
  simp only [simRun, leanSim, simRun2, outOf, contOf]
  rcases firstHit c.1.1.2.1 with _ | ⟨ctr, delta⟩
  · simp only [Option.map_map, Function.comp_def, Except.toOption, Option.getD_none, toL,
      ByteArray.toList_empty]
    exact Prod.ext rfl (Prod.ext rfl rfl)
  · simp only [Option.map_map, Function.comp_def, Except.toOption, Option.getD_some]
    rfl

/-! ## The deterministic hypotheses -/

lemma leanInst_values (pk : UOVKey) (h b₂ : ByteArray) (b c1 lb : ByteArray) (x : ℕ → GF128) :
    (withInst (leanBase b) (leanInst pk h b₂)).values c1 lb x =
      ((leanInst pk h b₂).sys c1 lb).values x := by
  show UovEval.pomfritRedeemValues 119 45 pk.map _ _ x = _
  rw [UovEval.pomfritRedeemValues_eq, betaFast_eq]
  rfl

/-- **The witness `r ‖ s` satisfies PomFRIT's system** for the instance `(pk, h)` whenever
`P(s) = h ⊕ r`, for every combination. -/
lemma leanInst_holds (pk : UOVKey) (h r s : Bytes) (b₂ : ByteArray) (hr : r.length = uovM)
    (hh : h.length = uovM) (hs : s.length = uovN) (hev : pk.eval s = xorBytes h r)
    (c1 lb : ByteArray) :
    ((leanInst pk (toBA h) b₂).sys c1 lb).Holds
      (wSlope (pomfritParams true) (toBA r ++ toBA s)) := by
  have hr' : r.length = 45 := hr
  have hh' : h.length = 45 := hh
  have hw : (toBA r ++ toBA s).size = (pomfritParams true).witnessBytes := by
    rw [ByteArray.size_append, size_toBA, size_toBA, hr, hs]; rfl
  rw [wSlope_eq _ _ hw]
  refine PomFRIT.pomfrit_complete_gf128 119 45 pk.map _ _ _ fun k => ?_
  have hk := k.isLt
  -- The witness bytes: `r`, then `s`.
  have hwr : ∀ i < 45, (toBA r ++ toBA s).get! i = r.getD i 0 := fun i hi => by
    rw [get!_append, size_toBA, hr', ite_eq_left hi, toBA_get!]
  have hws : ∀ i, (toBA r ++ toBA s).get! (45 + i) = s.getD i 0 := fun i => by
    rw [get!_append, size_toBA, hr', ite_eq_right (by omega), Nat.add_sub_cancel_left, toBA_get!]
  have hσ : (fun i => (⟨Keccak.witByte (Prover.bitOf (toBA r ++ toBA s)) (PomFRIT.witOffS 45 + i)⟩ :
      GF256)) = fun i => ⟨s.toArray.getD i 0⟩ := by
    funext i
    rw [witByte_bitOf, show PomFRIT.witOffS 45 + i = 45 + i from rfl, hws]
    simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
  rw [hσ, witByte_bitOf, show PomFRIT.witOffR + k.val = k.val from Nat.zero_add _, hwr _ hk]
  have e := congrArg (fun l => l.getD k.val 0) hev
  simp only [UOVKey.eval] at e
  rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _
    (by simp [length_xorBytes, hh', hr'])] at e
  simp only [List.getElem_map, List.getElem_finRange, xorBytes, List.getElem_zipWith] at e
  have e' : (UOV.publicMap 119 45 pk.map (fun i => ⟨s.toArray.getD i 0⟩) k).val =
      h[k.val]'(by omega) ^^^ r[k.val]'(by omega) := e
  rw [e', List.getD_eq_getElem _ _ (by omega)]
  simp only [targetOf, fnOf, size_toBA, hh', hk, ↓reduceDIte]
  congr 1

/-- **The two-phase hypotheses hold for every valid continuation.** -/
lemma runHyp2_lean (Hs : Hashes) (T : CrtTables) (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hT : maskInvOk T = true) (r b : Bytes) (k : Cont) (hr : r.length = uovM)
    (hk : Cont.Valid r k)
    (hcrt : ∀ rho : ByteArray,
      CrtComplete (Hs.hash .h5) T (step1 Hs T (leanBase (toBA b)) (toBA r) rho)) :
    RunHyp2 Hs T (leanBase (toBA b)) (toBA r) (contOf k) where
  hk o x sfx hko := by
    obtain ⟨⟨pk, h, s, b₂⟩, hkv, he⟩ := Option.map_eq_some_iff.1 hko
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hh, hs, hev⟩ := hk _ _ _ _ _ hkv
    exact
      { hvals := leanInst_values pk (toBA h) (toBA b₂) (toBA b)
        hdeg := fun _ _ => PomFRIT.degree_pomfritRedeemSystem _ _ _ _ _ _ _
        hd := show 1 ≤ 2 by decide
        hd' := show 2 + 1 < 2 ^ 64 by decide
        hsat := fun c1 lb => leanInst_holds pk h r s (toBA b₂) hr hh hs hev c1 lb
        hw := by rw [ByteArray.size_append, size_toBA, size_toBA, hr, hs]; rfl
        hI := Interp.interpOk_two }
  hr := by rw [size_toBA, hr]; show 45 ≤ 164; decide
  hnm := show 2 - 1 + 4 ≤ 32 by decide
  hT := hT
  hHs := hHs
  hbavc := hbavc
  hcrt := hcrt
  hlab := show (pomfritParams true).labelRowOffset + 128 ≤ (pomfritParams true).correctionRows by
    decide

/-! ## Zero knowledge and blindness -/

/-- **Two-phase zero knowledge of the Lean prover** (label rows), in the sense of
`Privacy.PomFRIT.ZeroKnowledge`, from the two-phase tape hypothesis. -/
theorem lean_zeroKnowledge (Hs : Hashes) (T : CrtTables) (hHs : HashesWF Hs)
    (hbavc : BAVCComplete) (hT : maskInvOk T = true)
    (hcrt : ∀ (r b : Bytes) (rho : ByteArray),
      CrtComplete (Hs.hash .h5) T (step1 Hs T (leanBase (toBA b)) (toBA r) rho))
    {ε : ℝ} (ht : ∀ r b k, r.length = uovM → Cont.Valid r k →
      TapeHyp2 Hs T (leanBase (toBA b)) (toBA r) (contOf k) ε) :
    ZeroKnowledge (leanProver Hs T) (leanSim Hs) ε := by
  intro r b k hr hk
  have h := twoPhase_close (runHyp2_lean Hs T hHs hbavc hT r b k hr hk (hcrt r b)) (ht r b k hr hk)
  have hsz : (toBA r).size = uovM := by rw [size_toBA, hr]
  rw [hsz] at h
  exact (h.map outOf).congr (fun ρ => realRun_lean Hs T r b k ρ) fun c => simRun_lean Hs b k c

lemma voleGen_length_lean (Hs : Hashes) (T : CrtTables) (r ρ b : Bytes) :
    ((leanProver Hs T).voleGen r ρ b).1.length = Layout.labelRows.proofBytes := by
  show (toL (step1 Hs T (leanBase (toBA b)) (toBA r) (toBA ρ)).proof).length = _
  rw [length_toL, Pending_proof_size]
  show (pomfritParams true).proofBytes = 5579
  decide

/-- **PomFRIT blindness with the Lean prover** (label rows; Theorem B from G1): for every Issuer,
the acceptance probabilities of the two worlds differ by at most `4ε`, where `ε` bounds the
two-phase tape hypothesis of every session. On `main` the corresponding statement is false
(`ZK/Relations.lean`: `pomfrit_issuer_hits`, `pomfrit_attack_test`). -/
theorem blindness_lean (A : Adversary) (Hs : Hashes) (T : CrtTables) (hHs : HashesWF Hs)
    (hbavc : BAVCComplete) (hT : maskInvOk T = true)
    (hcrt : ∀ (r b : Bytes) (rho : ByteArray),
      CrtComplete (Hs.hash .h5) T (step1 Hs T (leanBase (toBA b)) (toBA r) rho))
    {ε : ℝ} (ht : ∀ r b k, r.length = uovM → Cont.Valid r k →
      TapeHyp2 Hs T (leanBase (toBA b)) (toBA r) (contOf k) ε) :
    |pr _ (realGame Layout.labelRows A (leanProver Hs T) false) -
        pr _ (realGame Layout.labelRows A (leanProver Hs T) true)| ≤ 4 * ε :=
  blindness Layout.labelRows A (leanProver Hs T) (leanSim Hs) (voleGen_length_lean Hs T)
    (lean_zeroKnowledge Hs T hHs hbavc hT hcrt ht)

/-! ## Completeness on the final signature -/

lemma sig_parts {P com ref : ByteArray} {n : ℕ} (hP : P.size = n) (hc : com.size = 32)
    (hr : ref.size = 32) :
    (P ++ com ++ ref).extract 0 n = P ∧ (P ++ com ++ ref).extract n (n + 32) = com ∧
      (P ++ com ++ ref).extract (n + 32) (n + 64) = ref := by
  rw [ByteArray.append_assoc]
  refine ⟨ByteArray.extract_append_eq_left hP.symm, ?_, ?_⟩
  · have e := ByteArray.extract_append_size_add' (a := P) (b := com ++ ref) (i := 0) (j := 32)
      hP.symm
    rw [Nat.add_zero] at e
    rw [e, ByteArray.extract_append_eq_left hc.symm]
  · rw [ByteArray.extract_append_size_add' (a := P) (b := com ++ ref) (i := 32) (j := 64) hP.symm,
      ByteArray.extract_append_eq_right hc.symm (by rw [hc, hr])]

lemma size_mk_range_map (n : ℕ) (f : ℕ → UInt8) :
    (⟨(Array.range n).map f⟩ : ByteArray).size = n := by
  simp [ByteArray.size]

/-- The first `n ≤ m` bytes of the `m` fitted bytes of `b`, for `n ≤ b.size`. -/
lemma fit_extract {b : ByteArray} {n m : ℕ} (hn : n ≤ m) (hb : n ≤ b.size) :
    (Prover.fit b m).extract 0 n = b.extract 0 n := by
  rw [Prover.fit, ByteArray.extract_extract]
  simp only [Nat.zero_add]
  rw [Nat.min_eq_left hn, ByteArray.extract_append, Nat.zero_sub, show n - b.size = 0 by omega,
    ByteArray.extract_same, ByteArray.append_empty]

/-- The proof part of a PomFRIT signature. -/
def sigPf (labelRows : Bool) (sig : ByteArray) : Proof :=
  ⟨pomfritParams labelRows, sig.extract 0 (pomfritParams labelRows).proofBytes⟩

/-- `pomfritRedeem` reads the signature through `ũ`, `d[0..M)` and the binders. -/
lemma pomfritRedeem_congr (pk : UovPk) (msg : ByteArray) (labelRows : Bool) {sig sig' : ByteArray}
    (h0 : (sigPf labelRows sig).voleCheck = (sigPf labelRows sig').voleCheck)
    (h1 : (sigPf labelRows sig).correction.extract 0 uovM =
      (sigPf labelRows sig').correction.extract 0 uovM)
    (h2 : sig.extract (pomfritParams labelRows).proofBytes
        ((pomfritParams labelRows).proofBytes + 32) =
      sig'.extract (pomfritParams labelRows).proofBytes
        ((pomfritParams labelRows).proofBytes + 32))
    (h3 : sig.extract ((pomfritParams labelRows).proofBytes + 32)
        ((pomfritParams labelRows).proofBytes + 64) =
      sig'.extract ((pomfritParams labelRows).proofBytes + 32)
        ((pomfritParams labelRows).proofBytes + 64)) :
    pomfritRedeem pk sig msg labelRows = pomfritRedeem pk sig' msg labelRows := by
  simp only [sigPf] at h0 h1
  simp only [pomfritRedeem, pomfritTarget, h0, h1, h2, h3]

/-- **PomFRIT: completeness of `verify` on the final signature** (`pomfrit.cpp:219-237`): the
signature `proof ‖ refresher_com ‖ refresher` that `finalize_issue` outputs (with
`refresher_com = H_ref(refresher)`) passes `pomfritVerify`. Step 2 leaves `ũ` and `d[0..M)`
unchanged, so the target `h` the verifier hashes from the final signature is the one the Client
hashed from step 1's (`Bridge.pomfritRedeem_complete`). Assumed as there: `BAVCComplete`,
`CrtComplete`, `Δ' ≠ 0`. -/
theorem pomfritVerify_complete (Hs : Hashes) (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (T : CrtTables) (pk : UovPk) (msg r rho refresher wSuffix proof : ByteArray)
    (labelRows : Bool) (hr : r.size = uovM) (href : refresher.size = 32)
    (h : Prover.proveCommit Hs (pomfritRedeem pk ((pomfritPending Hs T labelRows r rho
      (toBA (commitRefresher (toL refresher)))).proof ++ toBA (commitRefresher (toL refresher)) ++
      refresher) msg labelRows) wSuffix
      (pomfritPending Hs T labelRows r rho (toBA (commitRefresher (toL refresher)))) = .ok proof)
    (hcrt : CrtComplete (Hs.hash .h5) T (pomfritPending Hs T labelRows r rho
      (toBA (commitRefresher (toL refresher)))))
    (hΔ : (W128.rowMul (BAVC.deltaBit
      ({ params := pomfritParams labelRows, bytes := proof } : Proof).delta) 120 T.wCrt).toGF ≠ 0) :
    (pomfritVerify Hs T pk (proof ++ toBA (commitRefresher (toL refresher)) ++ refresher) msg
      labelRows).accept = true := by
  set com := toBA (commitRefresher (toL refresher)) with hcom
  set s := pomfritPending Hs T labelRows r rho com with hs
  set p := pomfritParams labelRows
  have hcs : com.size = 32 := by rw [hcom, size_toBA, length_commitRefresher]
  obtain ⟨hw, check, aT, ctr, delta, opening, -, -, hproof⟩ := proveCommit_inv h
  have hsp : s.params = p := rfl
  rw [hsp] at hproof
  have hps : proof.size = p.proofBytes := by
    rw [hproof]; exact (fields_assemble _ _).2.2.2.2.2.2.2.2.2
  have hs1 : s.proof.size = p.proofBytes := Pending_proof_size s
  obtain ⟨e0, e1, e2⟩ := sig_parts hps hcs href
  obtain ⟨f0, f1, f2⟩ := sig_parts hs1 hcs href
  have hacc := pomfritRedeem_complete Hs hHs hbavc T pk msg r rho com refresher wSuffix proof
    labelRows hcs h hcrt hΔ
  -- The two signatures give the same statement.
  have hst : pomfritRedeem pk (proof ++ com ++ refresher) msg labelRows =
      pomfritRedeem pk (s.proof ++ com ++ refresher) msg labelRows := by
    have hv2 : (⟨p, s.proof⟩ : Proof).voleCheck = Prover.fit s.fields.voleCheck 64 :=
      (fields_assemble p s.fields).2.2.1
    have hc2 : (⟨p, s.proof⟩ : Proof).correction = Prover.fit s.fields.correction p.witnessBytes :=
      (fields_assemble p s.fields).2.2.2.1
    have hv1 : (⟨p, proof⟩ : Proof).voleCheck = Prover.fit s.fields.voleCheck 64 := by
      rw [hproof]; exact (fields_assemble p _).2.2.1
    have hc1 : (⟨p, proof⟩ : Proof).correction = Prover.fit
        ⟨(Array.range p.witnessBytes).map fun k =>
          (bytesOfWords s.u).get! k ^^^ (s.wPrefix ++ wSuffix).get! k⟩ p.witnessBytes := by
      rw [hproof]; exact (fields_assemble p _).2.2.2.1
    refine pomfritRedeem_congr pk msg labelRows ?_ ?_ (by rw [e1, f1]) (by rw [e2, f2])
    · simp only [sigPf]
      rw [e0, f0, hv1, hv2]
    · simp only [sigPf]
      rw [e0, f0, hc1, hc2]
      have hwb : uovM ≤ p.witnessBytes := show 45 ≤ 164 by decide
      have hpre : s.fields.correction = ⟨(Array.range r.size).map fun k =>
          (bytesOfWords s.u).get! k ^^^ r.get! k⟩ := rfl
      rw [hpre, fit_extract hwb (by rw [size_mk_range_map]; exact hwb),
        fit_extract hwb (by rw [size_mk_range_map, hr]), extract_range_map _ hwb,
        extract_range_map _ (le_of_eq hr.symm)]
      refine congrArg ByteArray.mk (Array.map_congr_left fun j hj => ?_)
      have hj' := Array.mem_range.1 hj
      rw [get!_append, show s.wPrefix = r from rfl, ite_eq_left (by omega)]
  unfold pomfritVerify
  dsimp only
  rw [show (pomfritParams labelRows).proofBytes = p.proofBytes from rfl, e1, e2, e0]
  rw [← hcom]
  have hne : (com != com) = false := by
    show (!(ByteArray.beq com com)) = false
    simp [ByteArray.beq]
  rw [hne, ite_eq_right (by simp), hst]
  exact hacc

end VoleMole.Privacy.PomFRIT
