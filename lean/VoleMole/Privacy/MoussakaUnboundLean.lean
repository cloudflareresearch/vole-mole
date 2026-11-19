import VoleMole.Privacy.MoussakaRO
import VoleMole.Privacy.MoussakaUnbound
import VoleMole.EndToEnd.MoussakaUnboundSpec

/-!
# Unbound Moussaka with the Lean prover: zero knowledge of the two unbound relations

`Privacy/MoussakaLean.lean` and `Privacy/MoussakaRO.lean` build the deterministic hypotheses
(`ZKHyp`) and the random-oracle zero-knowledge theorems (`leanPI_zkRO`, `leanPR_zkRO`) for the
bound relations. This file does the same for the two unbound relations
(`security/moussaka-unbound.md` §2, UF6), per proof:

* `stI x`, `stR x`: `Verifier.moussakaUnboundIssue` and `moussakaUnboundRedeem` for the spec's
  instances, with dedicated label rows; parameters `pI` (232 witness bytes), `pR` (559), both of
  degree 9, so the shared tables are the bound ones (`Moussaka.ShM R`: the `H₂³` prefix length
  depends on the degree only).
* `issue_holds`, `redeem_holds`: the spec's witness encodings (`encodeIssueWitness`,
  `encodeRedeemWitness`: `r ‖ nf_key ‖ …`, the committed states of the `UCom` and `Derive`
  permutations, the one-hot selector) satisfy the `Arith/MoussakaUnbound.lean` systems, for every
  combination (`uIssue_complete`, `uRedeem_complete`).
* `zkHypI`, `zkHypR`: `ZKHyp` for every well-formed instance and witness (`IssueRelW`,
  `RedeemRelW`), with faest-arch-opt's CRT tables and degree-9 interpolation.
* **`leanPI_zkRO`, `leanPR_zkRO`**: `ZeroKnowledgeRO` of the executable Lean prover
  (`ZK.Sim.realROb` with SHAKE) for the two unbound relations, simulator `Moussaka.leanSim`,
  programming `leanProgI`, `leanProgR`, against `Budget`ed distinguishers, error
  `ZKRow.εz R p q₃ q₅ q_E` for every type of cipher rows.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy.MoussakaUnbound

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.EndToEnd VoleMole.EndToEnd.SpecRel
open VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors
  committedStates selector)
open VoleMole.Privacy.Moussaka (committedStates_getD length_committedStates selector_bit
  length_selector leanSim ShM ProverRO)

/-! ## Issuance -/

/-- The unbound issuance statement with dedicated label rows. -/
def stI (x : IssueInstance) : Statement := moussakaUnboundIssue (toBA x.t) (toBA x.ctxIss) true

abbrev pI : Params := { witnessBytes := 232, qsDegree := 9, labelRows := true }

lemma length_encodeIssueWitness {k ci r : Spec.Bytes} (hk : k.length = nfKeyBytes)
    (hr : r.length = rBytes) : (encodeIssueWitness k ci r).length = 232 := by
  simp [encodeIssueWitness, length_committedStates, hk, hr, rBytes, nfKeyBytes]

/-- **The unbound issuance witness satisfies the unbound issuance system**
(`Arith.MoussakaUnbound.uIssue_complete`). -/
theorem issue_holds (x : IssueInstance) (w : Spec.Bytes) (h : IssueRelW x w) :
    (moussakaUnboundIssueSys (toBA x.t) (toBA x.ctxIss)).Holds (wSlope pI (toBA w)) := by
  obtain ⟨⟨k, r, hk, hr, rfl, ht⟩, -⟩ := h
  have hw : (toBA (encodeIssueWitness k x.ctxIss r)).size = pI.witnessBytes := by
    rw [size_toBA, length_encodeIssueWitness hk hr]
  rw [wSlope_eq _ _ hw]
  set S := ucomState k x.ctxIss r with hS
  set w := encodeIssueWitness k x.ctxIss r with hwdef
  set wb := Prover.bitOf (toBA w)
  have hbyte : ∀ i, Keccak.witByte wb i = w.getD i 0 := fun i => by rw [witByte_bitOf, toBA_get!]
  simp only [nfKeyBytes, rBytes] at hk hr
  have hlen : (r ++ k).length = 32 := by simp [hk, hr]
  -- The witness layout: `r ‖ nf_key ‖ s₅ ‖ s₉`.
  have hw_r : ∀ i < 16, w.getD i 0 = r.getD i 0 := fun i hi => by
    simp only [hwdef, encodeIssueWitness, getD_app, List.length_append, hr, hk,
      show i < 16 by omega, show i < 16 + 16 by omega, ↓reduceIte]
  have hw_k : ∀ i < 16, w.getD (16 + i) 0 = k.getD i 0 := fun i hi => by
    simp only [hwdef, encodeIssueWitness, getD_app, List.length_append, hr, hk,
      show ¬ 16 + i < 16 by omega, show 16 + i < 16 + 16 by omega, ↓reduceIte,
      Nat.add_sub_cancel_left]
  have hw_st : ∀ m, w.getD (32 + m) 0 = (committedStates S).getD m 0 := fun m => by
    rw [hwdef, encodeIssueWitness, getD_app, hlen, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hE : Arith.MoussakaUnbound.encodeUnboundComState (Arith.MoussakaUnbound.uIssueK wb)
      (fnOf (toBA x.ctxIss)) (Arith.MoussakaUnbound.uIssueR wb) = S :=
    encodeUnboundComState_congr
      (fun i hi => by
        simp only [Arith.MoussakaUnbound.uIssueK, hbyte, Arith.MoussakaUnbound.uIssueOffK,
          hw_k i hi, fn])
      (fun i _ => fnOf_toBA _ _)
      (fun i hi => by
        simp only [Arith.MoussakaUnbound.uIssueR, hbyte, Arith.MoussakaUnbound.uIssueOffR,
          Nat.zero_add, hw_r i hi, fn])
  unfold moussakaUnboundIssueSys
  refine Arith.MoussakaUnbound.uIssue_complete _ _ wb (fun i hi => ?_) (fun i hi => ?_) ?_
  · rw [hE, show wb (8 * Arith.MoussakaUnbound.uIssueOffStates + i) = _ from bitOf_toBA w _,
      stateBit_testBit _ hi,
      show (8 * Arith.MoussakaUnbound.uIssueOffStates + i) / 8 = 32 + i / 8 by
        simp only [Arith.MoussakaUnbound.uIssueOffStates]; omega,
      show (8 * Arith.MoussakaUnbound.uIssueOffStates + i) % 8 = i % 8 by
        simp only [Arith.MoussakaUnbound.uIssueOffStates]; omega,
      hw_st, (committedStates_getD S (show i / 8 < 100 by omega)).1]
  · rw [hE, stateBit_rounds9,
      show wb (8 * (Arith.MoussakaUnbound.uIssueOffStates + 100) + i) = _ from bitOf_toBA w _,
      stateBit_testBit _ hi,
      show (8 * (Arith.MoussakaUnbound.uIssueOffStates + 100) + i) / 8 = 32 + (100 + i / 8) by
        simp only [Arith.MoussakaUnbound.uIssueOffStates]; omega,
      show (8 * (Arith.MoussakaUnbound.uIssueOffStates + 100) + i) % 8 = i % 8 by
        simp only [Arith.MoussakaUnbound.uIssueOffStates]; omega,
      hw_st, (committedStates_getD S (show i / 8 < 100 by omega)).2]
  · funext j
    show fnOf (toBA x.t) j.val = Arith.MoussakaUnbound.ucom _ _ _ j
    rw [Arith.MoussakaUnbound.ucom, hE, fnOf_toBA, ht, ucom_getD]
    rfl

/-! ## Redemption -/

abbrev pR : Params := { witnessBytes := 559, qsDegree := 9, labelRows := true }

/-- The instance as `hash_redeem_instance` hashes it (the bound redemption's encoding). -/
def toBound (x : RedeemInstance) : Spec.Moussaka.RedeemInstance :=
  ⟨x.anchors, x.nf, x.ctxIss, x.ctxRed, x.challengeDigest⟩

/-- The unbound redemption statement with dedicated label rows
(`Verifier.moussakaUnboundRedeem`, with the Anchors' public maps as the spec's keys give them). -/
def stR (x : RedeemInstance) : Statement where
  params := pR
  dst := toBA (makeDst "mous" 1 'r' '0')
  instEnc := fun _ => toBA (toBound x).encode
  comb := some (Arith.Moussaka.M, toBA (makeDst "mous" 1 'l' '0'))
  values := fun _ lb w =>
    UovEval.moussakaUnboundRedeemValues (x.anchors.map (·.map)) (fnOf (toBA x.nf))
      (fnOf (toBA x.ctxIss)) (fnOf (toBA x.ctxRed)) (combinationOf Arith.Moussaka.M lb) w

/-- The unbound redemption system, at the combination decoded from the bytes `lb`. -/
def csR (x : RedeemInstance) : ByteArray → ByteArray → System GF128 := fun _ lb =>
  Arith.MoussakaUnbound.uRedeemSystem beta GF256.toBits (x.anchors.map (·.map)) (fnOf (toBA x.nf))
    (fnOf (toBA x.ctxIss)) (fnOf (toBA x.ctxRed)) (ofArr (combinationOf Arith.Moussaka.M lb))

lemma stR_values (x : RedeemInstance) (c1 lb : ByteArray) (y : ℕ → GF128) :
    (stR x).values c1 lb y = (csR x c1 lb).values y := by
  show UovEval.moussakaUnboundRedeemValues _ _ _ _ _ y = _
  rw [UovEval.moussakaUnboundRedeemValues_eq, Arith.MoussakaUnbound.uRedeemValues_eq, betaFast_eq]
  rfl

lemma length_encodeRedeemWitness {k ci cr r s : Spec.Bytes} (hk : k.length = nfKeyBytes)
    (hr : r.length = rBytes) (hs : s.length = uovN) (i : ℕ) :
    (encodeRedeemWitness k ci cr r s i).length = 559 := by
  simp [encodeRedeemWitness, length_committedStates, length_selector, hk, hr, hs, rBytes, uovN,
    nfKeyBytes]

/-- **The unbound redemption witness satisfies the unbound redemption system** for every
combination (`Arith.MoussakaUnbound.uRedeem_complete` at `GF128`). -/
theorem redeem_holds (x : RedeemInstance) (w : Spec.Bytes) (h : RedeemRelW x w)
    (c1 lb : ByteArray) :
    (csR x c1 lb).Holds (wSlope pR (toBA w)) := by
  obtain ⟨⟨k, r, s, u, pk, hk, hr, hs, hu, rfl, hev, hnfd⟩, hlen64, hnf, -, -⟩ := h
  have hw : (toBA (encodeRedeemWitness k x.ctxIss x.ctxRed r s u)).size = pR.witnessBytes := by
    rw [size_toBA, length_encodeRedeemWitness hk hr hs]
  rw [wSlope_eq _ _ hw]
  set S := ucomState k x.ctxIss r with hS
  set Sd := deriveState k x.ctxRed with hSd
  set w := encodeRedeemWitness k x.ctxIss x.ctxRed r s u with hwdef
  set wb := Prover.bitOf (toBA w)
  have hbyte : ∀ i, Keccak.witByte wb i = w.getD i 0 := fun i => by rw [witByte_bitOf, toBA_get!]
  simp only [nfKeyBytes, rBytes, uovN] at hk hr hs
  have hl1 : (r ++ k ++ s).length = 151 := by simp [hk, hr, hs]
  have hl2 : (r ++ k ++ s ++ committedStates S).length = 351 := by
    simp [hk, hr, hs, length_committedStates]
  have hl3 : (r ++ k ++ s ++ committedStates S ++ committedStates Sd).length = 551 := by
    simp [hk, hr, hs, length_committedStates]
  have hw_r : ∀ i < 16, w.getD i 0 = r.getD i 0 := fun i hi => by
    simp only [hwdef, encodeRedeemWitness, getD_app, List.length_append, hr, hk, hs,
      length_committedStates, show i < 16 by omega, show i < 16 + 16 by omega,
      show i < 16 + 16 + 119 by omega, show i < 16 + 16 + 119 + 200 by omega,
      show i < 16 + 16 + 119 + 200 + 200 by omega, ↓reduceIte]
  have hw_k : ∀ i < 16, w.getD (16 + i) 0 = k.getD i 0 := fun i hi => by
    simp only [hwdef, encodeRedeemWitness, getD_app, List.length_append, hr, hk, hs,
      length_committedStates, show ¬ 16 + i < 16 by omega, show 16 + i < 16 + 16 by omega,
      show 16 + i < 16 + 16 + 119 by omega, show 16 + i < 16 + 16 + 119 + 200 by omega,
      show 16 + i < 16 + 16 + 119 + 200 + 200 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  have hw_s : ∀ i < 119, w.getD (32 + i) 0 = s.getD i 0 := fun i hi => by
    simp only [hwdef, encodeRedeemWitness, getD_app, List.length_append, hr, hk, hs,
      length_committedStates, show ¬ 32 + i < 16 + 16 by omega,
      show 32 + i < 16 + 16 + 119 by omega, show 32 + i < 16 + 16 + 119 + 200 by omega,
      show 32 + i < 16 + 16 + 119 + 200 + 200 by omega, ↓reduceIte]
    congr 1; omega
  have hw_c : ∀ m < 200, w.getD (151 + m) 0 = (committedStates S).getD m 0 := fun m hm => by
    rw [hwdef, encodeRedeemWitness, getD_app, hl3, ite_eq_left (by omega), getD_app, hl2,
      ite_eq_left (by omega), getD_app, hl1, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hw_d : ∀ m < 200, w.getD (351 + m) 0 = (committedStates Sd).getD m 0 := fun m hm => by
    rw [hwdef, encodeRedeemWitness, getD_app, hl3, ite_eq_left (by omega), getD_app, hl2,
      ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hw_b : ∀ m, w.getD (551 + m) 0 = (selector u).getD m 0 := fun m => by
    rw [hwdef, encodeRedeemWitness, getD_app, hl3, ite_eq_right (by omega),
      Nat.add_sub_cancel_left]
  have hK : ∀ i < 16, Arith.MoussakaUnbound.uRedeemK wb i = fn k i := fun i hi => by
    simp only [Arith.MoussakaUnbound.uRedeemK, hbyte, Arith.MoussakaUnbound.uRedeemOffK,
      hw_k i hi, fn]
  have hR : ∀ i < 16, Arith.MoussakaUnbound.uRedeemR wb i = fn r i := fun i hi => by
    simp only [Arith.MoussakaUnbound.uRedeemR, hbyte, Arith.MoussakaUnbound.uRedeemOffR,
      Nat.zero_add, hw_r i hi, fn]
  have hE : Arith.MoussakaUnbound.encodeUnboundComState (Arith.MoussakaUnbound.uRedeemK wb)
      (fnOf (toBA x.ctxIss)) (Arith.MoussakaUnbound.uRedeemR wb) = S :=
    encodeUnboundComState_congr hK (fun i _ => fnOf_toBA _ _) hR
  have hD : Arith.MoussakaUnbound.encodeDeriveState (Arith.MoussakaUnbound.uRedeemK wb)
      (fnOf (toBA x.ctxRed)) = Sd :=
    encodeDeriveState_congr hK (fun i _ => fnOf_toBA _ _)
  obtain ⟨hu₀, hpk⟩ := List.getElem?_eq_some_iff.1 hu
  have hu₀' : u < (x.anchors.map (·.map)).length := by simpa using hu₀
  have hu64 : u < 64 := by have := hlen64; simp only [maxAnchors] at this; omega
  refine Arith.MoussakaUnbound.uRedeem_complete isEmbedding beta_zero _
    (by simpa [maxAnchors] using hlen64) _ _ _ _ wb (fun i hi => ?_) (fun i hi => ?_)
    (fun i hi => ?_) (fun i hi => ?_) u (fun v hv => ?_) ⟨⟨hu₀', funext fun j => ?_⟩, fun j => ?_⟩
  · rw [hE, show wb (8 * Arith.MoussakaUnbound.uRedeemOffComStates + i) = _ from bitOf_toBA w _,
      stateBit_testBit _ hi,
      show (8 * Arith.MoussakaUnbound.uRedeemOffComStates + i) / 8 = 151 + i / 8 by
        simp only [Arith.MoussakaUnbound.uRedeemOffComStates]; omega,
      show (8 * Arith.MoussakaUnbound.uRedeemOffComStates + i) % 8 = i % 8 by
        simp only [Arith.MoussakaUnbound.uRedeemOffComStates]; omega,
      hw_c _ (by omega), (committedStates_getD S (show i / 8 < 100 by omega)).1]
  · rw [hE, stateBit_rounds9,
      show wb (8 * (Arith.MoussakaUnbound.uRedeemOffComStates + 100) + i) = _ from
        bitOf_toBA w _, stateBit_testBit _ hi,
      show (8 * (Arith.MoussakaUnbound.uRedeemOffComStates + 100) + i) / 8 =
          151 + (100 + i / 8) by
        simp only [Arith.MoussakaUnbound.uRedeemOffComStates]; omega,
      show (8 * (Arith.MoussakaUnbound.uRedeemOffComStates + 100) + i) % 8 = i % 8 by
        simp only [Arith.MoussakaUnbound.uRedeemOffComStates]; omega,
      hw_c _ (by omega), (committedStates_getD S (show i / 8 < 100 by omega)).2]
  · rw [hD, show wb (8 * Arith.MoussakaUnbound.uRedeemOffDeriveStates + i) = _ from
        bitOf_toBA w _, stateBit_testBit _ hi,
      show (8 * Arith.MoussakaUnbound.uRedeemOffDeriveStates + i) / 8 = 351 + i / 8 by
        simp only [Arith.MoussakaUnbound.uRedeemOffDeriveStates]; omega,
      show (8 * Arith.MoussakaUnbound.uRedeemOffDeriveStates + i) % 8 = i % 8 by
        simp only [Arith.MoussakaUnbound.uRedeemOffDeriveStates]; omega,
      hw_d _ (by omega), (committedStates_getD Sd (show i / 8 < 100 by omega)).1]
  · rw [hD, stateBit_rounds9,
      show wb (8 * (Arith.MoussakaUnbound.uRedeemOffDeriveStates + 100) + i) = _ from
        bitOf_toBA w _, stateBit_testBit _ hi,
      show (8 * (Arith.MoussakaUnbound.uRedeemOffDeriveStates + 100) + i) / 8 =
          351 + (100 + i / 8) by
        simp only [Arith.MoussakaUnbound.uRedeemOffDeriveStates]; omega,
      show (8 * (Arith.MoussakaUnbound.uRedeemOffDeriveStates + 100) + i) % 8 = i % 8 by
        simp only [Arith.MoussakaUnbound.uRedeemOffDeriveStates]; omega,
      hw_d _ (by omega), (committedStates_getD Sd (show i / 8 < 100 by omega)).2]
  · rw [show wb (Arith.MoussakaUnbound.uSelBit v) = _ from bitOf_toBA w _,
      show Arith.MoussakaUnbound.uSelBit v / 8 = 551 + v / 8 by
        simp only [Arith.MoussakaUnbound.uSelBit, Arith.MoussakaUnbound.uRedeemOffB]; omega,
      show Arith.MoussakaUnbound.uSelBit v % 8 = v % 8 by
        simp only [Arith.MoussakaUnbound.uSelBit, Arith.MoussakaUnbound.uRedeemOffB]; omega,
      hw_b, selector_bit hu64 hv]
  · -- `P_u(s) = UCom(nf_key, ctx_iss, r)`, component `j`
    have e := congrArg (fun l => l.getD j.val 0) hev
    simp only [UOVKey.eval] at e
    rw [List.getD_eq_getElem _ _ (by simp), ucom_getD k x.ctxIss r j] at e
    simp only [List.getElem_map, List.getElem_finRange] at e
    have hA : (x.anchors.map (·.map))[u]'hu₀' = pk.map := by simp [hpk]
    have hsd : Arith.MoussakaUnbound.uRedeemS GF256.ofBits wb =
        fun i => ⟨Keccak.witByte wb (Arith.MoussakaUnbound.uRedeemOffS + i)⟩ :=
      funext (decode_gf256 wb Arith.MoussakaUnbound.uRedeemOffS)
    have hσ := publicMap_congr (N := 119) (M := 45) pk.map
      (σ := fun i => ⟨Keccak.witByte wb (Arith.MoussakaUnbound.uRedeemOffS + i)⟩)
      (σ' := fun i => ⟨s.toArray.getD i 0⟩) (fun i hi => by
        simp only [hbyte, show Arith.MoussakaUnbound.uRedeemOffS + i = 32 + i from rfl,
          hw_s i hi]
        simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]) j
    rw [hsd, hA, hσ, Arith.MoussakaUnbound.uRedeemTarget, Moussaka.toK_gf256]
    have hmk : ∀ (a : GF256) (b : UInt8), a.val = b → a = ⟨b⟩ := fun a b h => by
      cases a; cases h; rfl
    refine hmk _ _ ?_
    rw [congrFun (ucom_congr hK (fun i _ => fnOf_toBA x.ctxIss i) hR) j]
    exact e
  · -- `nf = Derive(nf_key, ctx_red)`, byte `j`
    rw [fnOf_toBA, hnfd, derive_getD k x.ctxRed j]
    exact (congrFun (derive_congr hK (fun i _ => fnOf_toBA x.ctxRed i)) j).symm

/-! ## The deterministic hypotheses -/

/-- The unbound issuance system. -/
def csI (x : IssueInstance) : ByteArray → ByteArray → System GF128 :=
  fun _ _ => moussakaUnboundIssueSys (toBA x.t) (toBA x.ctxIss)

/-- **`ZKHyp` for unbound issuance**, for every well-formed instance and witness. -/
theorem zkHypI (x : IssueInstance) (w : Spec.Bytes) (h : IssueRelW x w) :
    ZKHyp CrtGen.tables (stI x) (toBA w) (csI x) where
  hvals := moussakaUnboundIssue_values (toBA x.t) (toBA x.ctxIss) true
  hdeg := fun _ _ => Degree.moussaka_unbound_issue_deg _ _
  hd := show 1 ≤ 9 by decide
  hd' := show 9 + 1 < 2 ^ 64 by decide
  hsat := fun _ _ => issue_holds x w h
  hw := by
    obtain ⟨⟨k, r, hk, hr, rfl, -⟩, -⟩ := h
    rw [size_toBA, length_encodeIssueWitness hk hr]; rfl
  hnm := show 9 - 1 + 4 ≤ 32 by decide
  hT := maskInvOk_tables
  hI := Interp.interpOk_nine

/-- **`ZKHyp` for unbound redemption**, for every well-formed instance and witness. -/
theorem zkHypR (x : RedeemInstance) (w : Spec.Bytes) (h : RedeemRelW x w) :
    ZKHyp CrtGen.tables (stR x) (toBA w) (csR x) where
  hvals := stR_values x
  hdeg := fun _ _ => Degree.moussaka_unbound_redeem_deg _ _ _ _ _ _ _
  hd := show 1 ≤ 9 by decide
  hd' := show 9 + 1 < 2 ^ 64 by decide
  hsat := fun c1 lb => redeem_holds x w h c1 lb
  hw := by
    obtain ⟨⟨k, r, s, u, pk, hk, hr, hs, -, rfl, -, -⟩, -⟩ := h
    rw [size_toBA, length_encodeRedeemWitness hk hr hs]; rfl
  hnm := show 9 - 1 + 4 ≤ 32 by decide
  hT := maskInvOk_tables
  hI := Interp.interpOk_nine

/-! ## Zero knowledge in the random-oracle and ideal-cipher model -/

section RO

variable {R : Type} [Fintype R] [CipherRow R]

/-- **The Lean unbound issuance prover in the random-oracle model** (`ZK.Sim.realROb` with SHAKE
for the hashes that are not tables), its output as the spec's proof bytes. -/
noncomputable def leanPI : ProverRO R IssueInstance := fun w x rho g s =>
  toL ((realROb pI Hashes.shake (stI x) (toBA w) (toBA rho) g s).toOption.getD .empty)

/-- The Lean unbound redemption prover in the random-oracle model. -/
noncomputable def leanPR : ProverRO R RedeemInstance := fun w x rho g s =>
  toL ((realROb pR Hashes.shake (stR x) (toBA w) (toBA rho) g s).toOption.getD .empty)

/-- The unbound issuance simulator's programming (`ZK.Sim.progRO`). -/
noncomputable def leanProgI (x : IssueInstance) (c : SimCoins pI) : ShM R → ShM R :=
  progRO pI Hashes.shake (stI x) c

/-- The unbound redemption simulator's programming. -/
noncomputable def leanProgR (x : RedeemInstance) (c : SimCoins pR) : ShM R → ShM R :=
  progRO pR Hashes.shake (stR x) c

omit [Fintype R] in
lemma leanPI_ofFn (w : Bytes) (x : IssueInstance) (ρ : Coins proveSeedBytes) (g : Tab3) (s : ShM R) :
    leanPI w x (List.ofFn ρ) g s =
      toL ((realRO pI Hashes.shake (stI x) (toBA w) ρ g s).toOption.getD .empty) := by
  simp only [leanPI, realRO, toBA_ofFn]

omit [Fintype R] in
lemma leanPR_ofFn (w : Bytes) (x : RedeemInstance) (ρ : Coins proveSeedBytes) (g : Tab3) (s : ShM R) :
    leanPR w x (List.ofFn ρ) g s =
      toL ((realRO pR Hashes.shake (stR x) (toBA w) ρ g s).toOption.getD .empty) := by
  simp only [leanPR, realRO, toBA_ofFn]

/-- **Zero knowledge of the Lean unbound issuance prover in the random-oracle model** (cipher rows
`R`, error `ZKRow.εz R pI`). -/
theorem leanPI_zkRO [ZKRow R] (q3 q5 qE : ℕ) : ZeroKnowledgeRO IssueRelW
    (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPI w x (List.ofFn ρ) g s) (leanSim pI)
    leanProgI (Budget pI q3 q5 qE) (ZKRow.εz R pI q3 q5 qE) := by
  have h := (lean_zeroKnowledgeROG (R := R) Hashes.shake pI stI (fun _ => rfl) rfl
    (fun _ w => toBA w) IssueRelW csI zkHypI hashesWF_shake
    (smallParams_of_le (by decide) (by decide)) q3 q5 qE).transfer
    id (fun _ w => w) (fun _ _ h => h) (fun o => toL (o.toOption.getD .empty))
    (fun D hD => Budget.comp _ hD)
  have e : (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPI w x (List.ofFn ρ) g s) =
      fun x w r g s => toL ((realRO pI Hashes.shake (stI (id x)) (toBA w) r g s).toOption.getD .empty) := by
    funext x w ρ g s
    exact leanPI_ofFn w x ρ g s
  rw [e]
  exact h

/-- **Zero knowledge of the Lean unbound redemption prover in the random-oracle model.** -/
theorem leanPR_zkRO [ZKRow R] (q3 q5 qE : ℕ) : ZeroKnowledgeRO RedeemRelW
    (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPR w x (List.ofFn ρ) g s) (leanSim pR)
    leanProgR (Budget pR q3 q5 qE) (ZKRow.εz R pR q3 q5 qE) := by
  have h := (lean_zeroKnowledgeROG (R := R) Hashes.shake pR stR (fun _ => rfl) rfl
    (fun _ w => toBA w) RedeemRelW csR zkHypR hashesWF_shake
    (smallParams_of_le (by decide) (by decide)) q3 q5 qE).transfer
    id (fun _ w => w) (fun _ _ h => h) (fun o => toL (o.toOption.getD .empty))
    (fun D hD => Budget.comp _ hD)
  have e : (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPR w x (List.ofFn ρ) g s) =
      fun x w r g s => toL ((realRO pR Hashes.shake (stR (id x)) (toBA w) r g s).toOption.getD .empty) := by
    funext x w ρ g s
    exact leanPR_ofFn w x ρ g s
  rw [e]
  exact h

end RO

end VoleMole.Privacy.MoussakaUnbound
