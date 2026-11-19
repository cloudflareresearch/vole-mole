import VoleMole.Privacy.LeanProver
import VoleMole.Verifier.Bridge.Complete
import VoleMole.ZK.Interp

/-!
# Moussaka with the Lean prover, assembled per relation

`Privacy.Moussaka.anonymity_lean` (`Privacy/LeanProver.lean`) takes the statement builders of the
issuance and redemption proofs and their deterministic hypotheses (`ZKHyp`) as parameters. Here
they are built and proved for the executable statements with dedicated label rows:

* `stI x`: `Verifier.moussakaIssue` with label rows; `stR x`: `Verifier.moussakaRedeem` for the
  spec's keys (the Anchors' public maps as given), with label rows.
* `zkHypI`, `zkHypR`: `ZKHyp` for every well-formed instance and witness (`IssueRelW`,
  `RedeemRelW`): the evaluators are the `Arith/*` systems (`Bridge/Relations.lean`), of degree
  `≤ 9` (`EndToEnd/Degree.lean`); the witness encodings satisfy them for every `chal1` and
  combination (`issue_holds`, `redeem_holds`, from `Arith.Moussaka.issue_complete` and
  `redeem_complete_gf128`: the spec's witness layout, commitment state and committed Keccak
  states are the `Arith` ones); `N_MASK = 12 ≤ 32`, the CRT certificate (`maskInvOk_tables`) and
  interpolation (`ZK.Interp.interpOk_nine`).
* **`anonymity_label_rows`**: Theorem 4(a) with the Lean prover, `≤ 4εI + 4εR + 2εhide`, assuming
  only the tape hypotheses (`TapeHyp`), hiding and `HashesWF` (BAVC and CRT completeness are
  theorems, `Bridge.bavcComplete`, `Bridge.crtComplete`); `anonymity_label_rows_shake` drops
  `HashesWF` for SHAKE and takes the tape hypotheses from the hop hypotheses (`HopHyps`,
  `ZK/Hops.lean`), so each error is the sum `ε_rho + ε_grind + ε_bavc + ε_lab` of the named terms.
-/

open Finset

namespace VoleMole.Privacy.Moussaka

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.EndToEnd
open VoleMole.Spec VoleMole.Spec.Moussaka

/-! ## Byte lists -/

lemma comDst_eq : Spec.Moussaka.comDst = Arith.Moussaka.comDst := by decide

/-- **The commitment state**: `Arith`'s `encode_com_state` of byte functions that agree with the
fields is the spec's `comState`. -/
lemma encodeComState_eq (nf ci cr r : Spec.Bytes) (hnf : nf.length = nfBytes)
    (hci : ci.length = ctxBytes) (hcr : cr.length = ctxBytes) (hr : r.length = rBytes)
    (fnf fci fcr fr : ℕ → UInt8) (hfnf : ∀ i < 24, fnf i = nf.getD i 0)
    (hfci : ∀ i < 16, fci i = ci.getD i 0) (hfcr : ∀ i < 16, fcr i = cr.getD i 0)
    (hfr : ∀ i < 16, fr i = r.getD i 0) :
    Arith.Moussaka.encodeComState fnf fci fcr fr = stateOfBytes (comState nf ci cr r) := by
  have h7 : Spec.Moussaka.comDst.length = 7 := by decide
  simp only [nfBytes, ctxBytes, rBytes] at hnf hci hcr hr
  apply Vector.ext
  intro k hk
  simp only [Arith.Moussaka.encodeComState, stateOfBytes, Vector.getElem_ofFn, comState, getD_app,
    List.length_append, List.length_replicate, h7, hr, hci, hcr, hnf, getD_replicate_zero]
  split_ifs <;> first
    | omega
    | rfl
    | rw [comDst_eq]
    | exact hfr (k - 7) (by omega)
    | exact hfci (k - 32) (by omega)
    | exact hfcr (k - 48) (by omega)
    | exact hfnf (k - 64) (by omega)

/-! ## Bits -/

lemma length_committedStates (S : Keccak.State) : (committedStates S).length = 200 := by
  simp [committedStates]

/-- The committed states, byte by byte. -/
lemma committedStates_getD (S : Keccak.State) {m : ℕ} (hm : m < 100) :
    (committedStates S).getD m 0 = (Keccak.keccakP800Rounds 0 5 S)[m] ∧
      (committedStates S).getD (100 + m) 0 =
        (Keccak.keccakP800Rounds 5 4 (Keccak.keccakP800Rounds 0 5 S))[m] := by
  simp only [committedStates, getD_app, Vector.length_toList, hm, ↓reduceIte, getD_toList _ hm,
    show ¬ 100 + m < 100 by omega, Nat.add_sub_cancel_left, true_and]

/-- `Com` as `Arith`'s, at the spec's state. -/
lemma com_getD (nf ci cr r : Spec.Bytes) (k : Fin 45) :
    (Spec.Moussaka.com nf ci cr r).getD k.val 0 =
      (Keccak.keccakP800 (stateOfBytes (comState nf ci cr r)))[k.val] := by
  rw [Spec.Moussaka.com, List.getD_eq_getElem _ _ (by simp; omega)]
  simp

/-! ## Issuance -/

/-- The issuance statement with dedicated label rows. -/
def stI (x : IssueInstance) : Statement := moussakaIssue (toBA x.t) (toBA x.ctxIss) true

abbrev pI : Params := { witnessBytes := 256, qsDegree := 9, labelRows := true }

lemma length_encodeIssueWitness {nf ci cr r : Spec.Bytes} (hnf : nf.length = nfBytes)
    (hcr : cr.length = ctxBytes) (hr : r.length = rBytes) :
    (encodeIssueWitness nf ci cr r).length = 256 := by
  simp [encodeIssueWitness, length_committedStates, hnf, hcr, hr, rBytes, ctxBytes, nfBytes]

/-- **The issuance witness satisfies the issuance system** (`Arith.Moussaka.issue_complete`). -/
theorem issue_holds (x : IssueInstance) (w : Spec.Bytes) (h : IssueRelW x w) :
    (moussakaIssueSys (toBA x.t) (toBA x.ctxIss)).Holds (wSlope pI (toBA w)) := by
  obtain ⟨⟨nf, r, ctxRed, hnf, hr, hcr, rfl, ht⟩, hci⟩ := h
  have hw : (toBA (encodeIssueWitness nf x.ctxIss ctxRed r)).size = pI.witnessBytes := by
    rw [size_toBA, length_encodeIssueWitness hnf hcr hr]
  rw [wSlope_eq _ _ hw]
  set S := stateOfBytes (comState nf x.ctxIss ctxRed r) with hS
  set w := encodeIssueWitness nf x.ctxIss ctxRed r with hwdef
  set wb := Prover.bitOf (toBA w)
  have hbyte : ∀ i, Keccak.witByte wb i = w.getD i 0 := fun i => by rw [witByte_bitOf, toBA_get!]
  simp only [nfBytes, ctxBytes, rBytes] at hnf hcr hr
  -- The witness layout: `r ‖ ctx_red ‖ nf ‖ s₅ ‖ s₉`.
  have hlen : (r ++ ctxRed ++ nf).length = 56 := by simp [hnf, hcr, hr]
  have hw_r : ∀ i < 16, w.getD i 0 = r.getD i 0 := fun i hi => by
    simp only [hwdef, encodeIssueWitness, getD_app, List.length_append, hr, hcr, hnf,
      show i < 16 by omega, show i < 16 + 16 by omega, show i < 16 + 16 + 24 by omega, ↓reduceIte]
  have hw_cr : ∀ i < 16, w.getD (16 + i) 0 = ctxRed.getD i 0 := fun i hi => by
    simp only [hwdef, encodeIssueWitness, getD_app, List.length_append, hr, hcr, hnf,
      show ¬ 16 + i < 16 by omega, show 16 + i < 16 + 16 by omega,
      show 16 + i < 16 + 16 + 24 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  have hw_nf : ∀ i < 24, w.getD (32 + i) 0 = nf.getD i 0 := fun i hi => by
    simp only [hwdef, encodeIssueWitness, getD_app, List.length_append, hr, hcr, hnf,
      show ¬ 32 + i < 16 + 16 by omega, show 32 + i < 16 + 16 + 24 by omega, ↓reduceIte]
    congr 1; omega
  have hw_st : ∀ m, w.getD (56 + m) 0 = (committedStates S).getD m 0 := fun m => by
    rw [hwdef, encodeIssueWitness, getD_app, hlen, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hE : Arith.Moussaka.encodeComState (Arith.Moussaka.issueNf wb) (fnOf (toBA x.ctxIss))
      (Arith.Moussaka.issueCtxRed wb) (Arith.Moussaka.issueR wb) = S :=
    encodeComState_eq nf x.ctxIss ctxRed r hnf hci hcr hr _ _ _ _
      (fun i hi => by
        simp only [Arith.Moussaka.issueNf, hbyte, Arith.Moussaka.issueOffNf, hw_nf i hi])
      (fun i _ => fnOf_toBA _ _)
      (fun i hi => by
        simp only [Arith.Moussaka.issueCtxRed, hbyte, Arith.Moussaka.issueOffCtxRed, hw_cr i hi])
      (fun i hi => by
        simp only [Arith.Moussaka.issueR, hbyte, Arith.Moussaka.issueOffR, Nat.zero_add, hw_r i hi])
  unfold moussakaIssueSys
  refine Arith.Moussaka.issue_complete _ _ wb (fun i hi => ?_) (fun i hi => ?_) ?_
  · rw [hE, show wb (8 * Arith.Moussaka.issueOffStates + i) = _ from bitOf_toBA w _,
      stateBit_testBit _ hi, show (8 * Arith.Moussaka.issueOffStates + i) / 8 = 56 + i / 8 by
        simp only [Arith.Moussaka.issueOffStates]; omega,
      show (8 * Arith.Moussaka.issueOffStates + i) % 8 = i % 8 by
        simp only [Arith.Moussaka.issueOffStates]; omega,
      hw_st, (committedStates_getD S (show i / 8 < 100 by omega)).1]
  · rw [hE, stateBit_rounds9, show wb (8 * (Arith.Moussaka.issueOffStates + 100) + i) = _ from
      bitOf_toBA w _, stateBit_testBit _ hi,
      show (8 * (Arith.Moussaka.issueOffStates + 100) + i) / 8 = 56 + (100 + i / 8) by
        simp only [Arith.Moussaka.issueOffStates]; omega,
      show (8 * (Arith.Moussaka.issueOffStates + 100) + i) % 8 = i % 8 by
        simp only [Arith.Moussaka.issueOffStates]; omega,
      hw_st, (committedStates_getD S (show i / 8 < 100 by omega)).2]
  · funext k
    show fnOf (toBA x.t) k.val = Arith.Moussaka.com _ _ _ _ k
    rw [Arith.Moussaka.com, hE, fnOf_toBA, ht, com_getD]

/-! ## Redemption -/

abbrev pR : Params := { witnessBytes := 343, qsDegree := 9, labelRows := true }

/-- The redemption statement with dedicated label rows (`Verifier.moussakaRedeem`, with the
Anchors' public maps as the spec's keys give them). -/
def stR (x : RedeemInstance) : Statement where
  params := pR
  dst := toBA (makeDst "mous" 0 'r' '0')
  instEnc := fun _ => toBA x.encode
  comb := some (Arith.Moussaka.M, toBA (makeDst "mous" 0 'l' '0'))
  values := fun _ lb w =>
    UovEval.moussakaRedeemValues (x.anchors.map (·.map)) (fnOf (toBA x.nf)) (fnOf (toBA x.ctxIss))
      (fnOf (toBA x.ctxRed)) (combinationOf Arith.Moussaka.M lb) w

/-- The redemption system, at the combination decoded from the bytes `lb`. -/
def csR (x : RedeemInstance) : ByteArray → ByteArray → System GF128 := fun _ lb =>
  Arith.Moussaka.redeemSystem beta GF256.toBits (x.anchors.map (·.map)) (fnOf (toBA x.nf))
    (fnOf (toBA x.ctxIss)) (fnOf (toBA x.ctxRed)) (ofArr (combinationOf Arith.Moussaka.M lb))

lemma stR_values (x : RedeemInstance) (c1 lb : ByteArray) (y : ℕ → GF128) :
    (stR x).values c1 lb y = (csR x c1 lb).values y := by
  show UovEval.moussakaRedeemValues _ _ _ _ _ y = _
  rw [UovEval.moussakaRedeemValues_eq, Arith.Moussaka.redeemValues_eq, betaFast_eq]
  rfl

lemma length_selector (i : ℕ) : (selector i).length = 8 := by simp [selector, maxAnchors]

lemma one_shift_testBit : ∀ k < 8, ∀ m < 8,
    ((1 : UInt8) <<< k.toUInt8).toNat.testBit m = decide (m = k) := by decide

/-- Bit `v` of the selector of `u` is `v = u` (`u, v < 64`). -/
lemma selector_bit {u v : ℕ} (hu : u < 64) (hv : v < 64) :
    ((selector u).getD (v / 8) 0).toNat.testBit (v % 8) = decide (v = u) := by
  rw [selector, List.getD_eq_getElem _ _ (by simp [maxAnchors]; omega)]
  simp only [List.getElem_map, List.getElem_range]
  split_ifs with h
  · rw [one_shift_testBit _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))]
    by_cases hvu : v = u
    · simp [hvu]
    · simp only [hvu, decide_false, decide_eq_false_iff_not]
      omega
  · simp only [UInt8.toNat_zero, Nat.zero_testBit]
    by_cases hvu : v = u
    · subst hvu; exact absurd rfl h
    · simp [hvu]

lemma length_encodeRedeemWitness {nf ci cr r s : Spec.Bytes} (hr : r.length = rBytes)
    (hs : s.length = uovN) (i : ℕ) : (encodeRedeemWitness nf ci cr r s i).length = 343 := by
  simp [encodeRedeemWitness, length_committedStates, length_selector, hr, hs, rBytes, uovN]

/-- **The redemption witness satisfies the redemption system** for every combination
(`Arith.Moussaka.redeem_complete_gf128`). -/
theorem redeem_holds (x : RedeemInstance) (w : Spec.Bytes) (h : RedeemRelW x w)
    (c1 lb : ByteArray) :
    (csR x c1 lb).Holds (wSlope pR (toBA w)) := by
  obtain ⟨⟨r, s, u, pk, hr, hs, hu, rfl, hev⟩, hlen64, hnf, hci, hcr⟩ := h
  have hw : (toBA (encodeRedeemWitness x.nf x.ctxIss x.ctxRed r s u)).size = pR.witnessBytes := by
    rw [size_toBA, length_encodeRedeemWitness hr hs]
  rw [wSlope_eq _ _ hw]
  set S := stateOfBytes (comState x.nf x.ctxIss x.ctxRed r) with hS
  set w := encodeRedeemWitness x.nf x.ctxIss x.ctxRed r s u with hwdef
  set wb := Prover.bitOf (toBA w)
  have hbyte : ∀ i, Keccak.witByte wb i = w.getD i 0 := fun i => by rw [witByte_bitOf, toBA_get!]
  simp only [rBytes, uovN] at hr hs
  have hlen : (r ++ s).length = 135 := by simp [hr, hs]
  have hlen2 : (r ++ s ++ committedStates S).length = 335 := by
    simp [hr, hs, length_committedStates]
  have hw_r : ∀ i < 16, w.getD i 0 = r.getD i 0 := fun i hi => by
    simp only [hwdef, encodeRedeemWitness, getD_app, List.length_append, hr, hs,
      length_committedStates, show i < 16 by omega, show i < 16 + 119 by omega,
      show i < 16 + 119 + 200 by omega, ↓reduceIte]
  have hw_s : ∀ i < 119, w.getD (16 + i) 0 = s.getD i 0 := fun i hi => by
    simp only [hwdef, encodeRedeemWitness, getD_app, List.length_append, hr, hs,
      length_committedStates, show ¬ 16 + i < 16 by omega, show 16 + i < 16 + 119 by omega,
      show 16 + i < 16 + 119 + 200 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  have hw_st : ∀ m < 200, w.getD (135 + m) 0 = (committedStates S).getD m 0 := fun m hm => by
    rw [hwdef, encodeRedeemWitness, getD_app, hlen2, ite_eq_left (by omega), getD_app, hlen,
      ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hw_b : ∀ m, w.getD (335 + m) 0 = (selector u).getD m 0 := fun m => by
    rw [hwdef, encodeRedeemWitness, getD_app, hlen2, ite_eq_right (by omega),
      Nat.add_sub_cancel_left]
  have hE : Arith.Moussaka.encodeComState (fnOf (toBA x.nf)) (fnOf (toBA x.ctxIss))
      (fnOf (toBA x.ctxRed)) (Arith.Moussaka.redeemR wb) = S :=
    encodeComState_eq x.nf x.ctxIss x.ctxRed r hnf hci hcr hr _ _ _ _
      (fun i _ => fnOf_toBA _ _) (fun i _ => fnOf_toBA _ _) (fun i _ => fnOf_toBA _ _)
      (fun i hi => by
        simp only [Arith.Moussaka.redeemR, hbyte, Arith.Moussaka.redeemOffR, Nat.zero_add,
          hw_r i hi])
  obtain ⟨hu₀, hpk⟩ := List.getElem?_eq_some_iff.1 hu
  refine Arith.Moussaka.redeem_complete_gf128 _ (by simpa [maxAnchors] using hlen64) _ _ _ _ wb
    (fun i hi => ?_) (fun i hi => ?_) u (fun v hv => ?_) (by simpa using hu₀) (fun k => ?_)
  · rw [hE, show wb (8 * Arith.Moussaka.redeemOffStates + i) = _ from bitOf_toBA w _,
      stateBit_testBit _ hi, show (8 * Arith.Moussaka.redeemOffStates + i) / 8 = 135 + i / 8 by
        simp only [Arith.Moussaka.redeemOffStates]; omega,
      show (8 * Arith.Moussaka.redeemOffStates + i) % 8 = i % 8 by
        simp only [Arith.Moussaka.redeemOffStates]; omega,
      hw_st _ (by omega), (committedStates_getD S (show i / 8 < 100 by omega)).1]
  · rw [hE, stateBit_rounds9, show wb (8 * (Arith.Moussaka.redeemOffStates + 100) + i) = _ from
      bitOf_toBA w _, stateBit_testBit _ hi,
      show (8 * (Arith.Moussaka.redeemOffStates + 100) + i) / 8 = 135 + (100 + i / 8) by
        simp only [Arith.Moussaka.redeemOffStates]; omega,
      show (8 * (Arith.Moussaka.redeemOffStates + 100) + i) % 8 = i % 8 by
        simp only [Arith.Moussaka.redeemOffStates]; omega,
      hw_st _ (by omega), (committedStates_getD S (show i / 8 < 100 by omega)).2]
  · have hu64 : u < 64 := by have := hlen64; simp only [maxAnchors] at this; omega
    rw [show wb (Arith.Moussaka.selBit v) = _ from bitOf_toBA w _,
      show Arith.Moussaka.selBit v / 8 = 335 + v / 8 by
        simp only [Arith.Moussaka.selBit, Arith.Moussaka.redeemOffB]; omega,
      show Arith.Moussaka.selBit v % 8 = v % 8 by
        simp only [Arith.Moussaka.selBit, Arith.Moussaka.redeemOffB]; omega,
      hw_b, selector_bit hu64 hv]
  · have e := congrArg (fun l => l.getD k.val 0) hev
    simp only [UOVKey.eval] at e
    rw [List.getD_eq_getElem _ _ (by simp), com_getD] at e
    simp only [List.getElem_map, List.getElem_finRange] at e
    have hA : (x.anchors.map (·.map))[u]'(by simpa using hu₀) = pk.map := by simp [hpk]
    have hσ := publicMap_congr (N := 119) (M := 45) pk.map
      (σ := fun i => ⟨Keccak.witByte wb (Arith.Moussaka.redeemOffS + i)⟩)
      (σ' := fun i => ⟨s.toArray.getD i 0⟩) (fun i hi => by
        simp only [hbyte, show Arith.Moussaka.redeemOffS + i = 16 + i from rfl, hw_s i hi]
        simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]) k
    rw [Arith.Moussaka.com, hE, ← e, hA, hσ]
    rfl

/-! ## The deterministic hypotheses -/

/-- The issuance system. -/
def csI (x : IssueInstance) : ByteArray → ByteArray → System GF128 :=
  fun _ _ => moussakaIssueSys (toBA x.t) (toBA x.ctxIss)

/-- **`ZKHyp` for issuance**, for every well-formed instance and witness. -/
theorem zkHypI (x : IssueInstance) (w : Spec.Bytes) (h : IssueRelW x w) :
    ZKHyp CrtGen.tables (stI x) (toBA w) (csI x) where
  hvals := moussakaIssue_values (toBA x.t) (toBA x.ctxIss) true
  hdeg := fun _ _ => Degree.moussaka_issue_deg _ _
  hd := show 1 ≤ 9 by decide
  hd' := show 9 + 1 < 2 ^ 64 by decide
  hsat := fun _ _ => issue_holds x w h
  hw := by
    obtain ⟨⟨nf, r, ctxRed, hnf, hr, hcr, rfl, -⟩, -⟩ := h
    rw [size_toBA, length_encodeIssueWitness hnf hcr hr]; rfl
  hnm := show 9 - 1 + 4 ≤ 32 by decide
  hT := maskInvOk_tables
  hI := Interp.interpOk_nine

/-- **`ZKHyp` for redemption**, for every well-formed instance and witness. -/
theorem zkHypR (x : RedeemInstance) (w : Spec.Bytes) (h : RedeemRelW x w) :
    ZKHyp CrtGen.tables (stR x) (toBA w) (csR x) where
  hvals := stR_values x
  hdeg := fun _ _ => Degree.moussaka_redeem_deg _ _ _ _ _ _ _
  hd := show 1 ≤ 9 by decide
  hd' := show 9 + 1 < 2 ^ 64 by decide
  hsat := fun c1 lb => redeem_holds x w h c1 lb
  hw := by
    obtain ⟨⟨r, s, u, pk, hr, hs, -, rfl, -⟩, -⟩ := h
    rw [size_toBA, length_encodeRedeemWitness hr hs]; rfl
  hnm := show 9 - 1 + 4 ≤ 32 by decide
  hT := maskInvOk_tables
  hI := Interp.interpOk_nine

/-! ## Issuer hiding and unlinkability with the Lean prover -/

/-- **Moussaka issuer hiding and unlinkability with the Lean prover** (Theorem 4(a)), with the
statements of `Verifier/Relations.lean` (dedicated label rows) and faest-arch-opt's CRT tables:
if the issuance and redemption runs' tapes are `εI`- and `εR`-close to uniform (`TapeHyp`) and
the hiding reductions have advantage `≤ εhide`, the two worlds differ by at most
`4εI + 4εR + 2εhide`. Also assumed: the hash record's output lengths (`anonymity_label_rows_shake`:
none with SHAKE); BAVC and CRT completeness are theorems (`Bridge.bavcComplete`,
`Bridge.crtComplete`). -/
theorem anonymity_label_rows (A : Adversary) (idx : AnchorSet → UOVKey → ℕ) (Hs : Hashes)
    (hHs : HashesWF Hs) {εI εR εhide : ℝ} (hεR : 0 ≤ εR)
    (htI : ∀ x w, IssueRelW x w → TapeHyp Hs CrtGen.tables (stI x) (toBA w) εI)
    (htR : ∀ x w, RedeemRelW x w → TapeHyp Hs CrtGen.tables (stR x) (toBA w) εR)
    (hhide : ∀ b c, hidingAdv A.ci A.cr
      (reduction A idx (leanSim pI) (leanSim pR) b c) ≤ εhide) :
    |pr _ (realGame A idx (leanNIZK Hs CrtGen.tables stI) (leanNIZK Hs CrtGen.tables stR) false) -
        pr _ (realGame A idx (leanNIZK Hs CrtGen.tables stI) (leanNIZK Hs CrtGen.tables stR)
          true)| ≤
      4 * εI + 4 * εR + 2 * εhide :=
  anonymity_lean A idx Hs CrtGen.tables stI stR pI pR (fun _ => rfl) (fun _ => rfl) rfl rfl csI csR
    zkHypI zkHypR hHs bavcComplete
    (fun _ _ _ rho => crtComplete Hs _ _ _ rho _ (hlab_of (show 16 ≤ 256 by decide)))
    (fun _ _ _ rho => crtComplete Hs _ _ _ rho _ (hlab_of (show 16 ≤ 343 by decide)))
    hεR htI htR hhide

/-- **Moussaka issuer hiding and unlinkability with the Lean prover and SHAKE**, with the tape
hypotheses from the hop hypotheses (`HopHyps`, `ZK/Hops.lean`): the issuance and redemption
errors are the sums `ε_rho + ε_grind + ε_bavc + ε_lab` of the named terms (H1, the grinding
answers, BAVC hiding, H6). Only the hop hypotheses and hiding are assumed. -/
theorem anonymity_label_rows_shake (A : Adversary) (idx : AnchorSet → UOVKey → ℕ)
    {εrhoI εgrindI εbavcI εlabI εrhoR εgrindR εbavcR εlabR εhide : ℝ}
    (hεR : 0 ≤ εrhoR + εgrindR + εbavcR + εlabR)
    (htI : ∀ x w, IssueRelW x w →
      HopHyps Hashes.shake CrtGen.tables (stI x) (toBA w) εrhoI εgrindI εbavcI εlabI)
    (htR : ∀ x w, RedeemRelW x w →
      HopHyps Hashes.shake CrtGen.tables (stR x) (toBA w) εrhoR εgrindR εbavcR εlabR)
    (hhide : ∀ b c, hidingAdv A.ci A.cr
      (reduction A idx (leanSim pI) (leanSim pR) b c) ≤ εhide) :
    |pr _ (realGame A idx (leanNIZK Hashes.shake CrtGen.tables stI)
          (leanNIZK Hashes.shake CrtGen.tables stR) false) -
        pr _ (realGame A idx (leanNIZK Hashes.shake CrtGen.tables stI)
          (leanNIZK Hashes.shake CrtGen.tables stR) true)| ≤
      4 * (εrhoI + εgrindI + εbavcI + εlabI) + 4 * (εrhoR + εgrindR + εbavcR + εlabR) +
        2 * εhide :=
  anonymity_label_rows A idx Hashes.shake hashesWF_shake hεR
    (fun x w h => tapeHyp_of_hops _ _ _ _ hashesWF_shake bavcComplete
      (hlab_of (show 16 ≤ 256 by decide)) (htI x w h))
    (fun x w h => tapeHyp_of_hops _ _ _ _ hashesWF_shake bavcComplete
      (hlab_of (show 16 ≤ 343 by decide)) (htR x w h)) hhide

end VoleMole.Privacy.Moussaka
