import VoleMole.Verifier.Bridge.Concrete
import VoleMole.Verifier.Relations
import VoleMole.EndToEnd.Concrete

/-!
# Bridge, per relation: acceptance gives `EndToEnd`'s accepting equation for the proved system

`accept_hacc` (`Bridge/Accept.lean`) assumes `hvals`: the statement's executable evaluator,
transported along the field embedding, is `System.values` of a system `cs`. `GF128` is itself a
field (`Arith/GFField.lean`, `instField` keeps `GF.lean`'s `0`, `1`, `+`, `*`; `CharP GF128 2`;
`card_eq`), so the embedding can be the identity (`gfId`), and `hvals` becomes an equation between
two lists over `GF128`. For each relation of `Verifier/Relations.lean` it holds with `cs` the
`Arith/*` system that `EndToEnd/Relations.lean` and `Arith/ConcreteField.lean` are about, at
`β := beta`, `K := GF256` and the verifier's instance data:

* the issue relations' evaluators are the `Arith/*` sharing evaluators, which those files prove
  equal to `System.values` (`Moussaka.issueValues_eq`, `Ratatouille.issueSystem_values`), for any
  `+ * 0 1`, so at `GF128`;
* Moussaka redeem and Ratatouille spend likewise (`Moussaka.redeemValues_eq`,
  `Ratatouille.spendSystem_values`), and PomFRIT redeem is `System.values` already; their
  evaluators use the tabulated `betaFast`, equal to `beta` (`betaFast_eq`), and the cached
  combination coefficients `ofArr (combinationArr n chal2 dst)`, which enter the system unchanged
  as its `l` (`ofArr_combinationArr`: coefficient `k` is bytes `[16k, 16k+16)` of
  `H(chal2 ‖ dst)`).

No parametricity argument is needed: the evaluator and the system live over the same field.

## Main results

* `gfId`, `AcceptEq` (the conclusion of `accept_hacc` at `gfId`, written without `φ`),
  `accept_hacc_GF` (`accept_hacc` at `gfId`; `hvals` as an equation over `GF128`, `|F| = 2¹²⁸`
  and characteristic 2 proved).
* `moussakaIssue_values`, `moussakaRedeem_values`, `ratatouilleIssue_values`,
  `ratatouilleSpend_values`, `pomfritRedeem_values`: `hvals` per relation.
* `moussakaIssue_accept`, `moussakaRedeem_accept`, `ratatouilleIssue_accept`,
  `ratatouilleSpend_accept`, `pomfritRedeem_accept`, `pomfritVerify_accept`: **if the executable
  verifier accepts, `EndToEnd`'s accepting equation holds at that transcript for the relation's
  `Arith/*` system over GF(2¹²⁸)**, the `hacc` of the `*_extract_gf128` theorems
  (`EndToEnd/Concrete.lean`) at that `Δ`, with nothing assumed. On a whole chain of challenges,
  `Bridge/Chain.lean` and `Bridge/ChainRelations.lean` discharge `Claim4Hyp` and `hacc` on all of
  `A`, leaving the random-oracle and probabilistic steps.
* `values_map`, `degree_map`: the same `hvals` for any other embedding `φ` (e.g. `gfK`), with
  `cs` mapped along `φ` by `Expr.map`, so `accept_hacc_K` applies too.
-/

namespace VoleMole.Verifier.Bridge

open VoleMole.Arith VoleMole.Verifier VoleMole.EndToEnd

/-- **The identity embedding**: `GF128` is a field (`GF128.instField`). -/
def gfId : GFEmbedding GF128 where
  toFun := id
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl
  injective := Function.injective_id

/-- The conclusion of `accept_hacc` at `gfId`: the BAVC opening reconstructs, `Δ_lifted ≠ 0`,
`chal3 = Δ`, and `EndToEnd`'s accepting equation `qsCheck (cs c1 c2) d χ m Δ + R(Δ) = 0` holds
with the transcript's `chal2`-weights `χ`, witness MACs `m_j = row_j + d_j·Δ`, `Δ = Δ_lifted` and
`R = maskPoly d q_mask 0 ã check`. -/
def AcceptEq (T : CrtTables) (st : Statement) (proof : ByteArray)
    (cs : ByteArray → ByteArray → System GF128) : Prop :=
  let pf : Proof := { params := st.params, bytes := proof }
  let muI : ByteArray → ByteArray := fun c1 => mu (some (st.instEnc c1)) st.dst
  let mu1 := if st.delayed then mu none st.dst else muI ByteArray.empty
  let iv := ivOf pf mu1
  ∃ leaves, BAVC.reconstruct iv pf.opening pf.delta = some leaves ∧
    let c1 := chal1 pf mu1 (BAVC.check leaves.coms) st.binder1
    let crt := crtReconstruct pf T iv (convertToVole pf iv leaves)
    let deltaL := crt.deltaLifted.toGF
    let hV := voleHashReceiver st.params c1 crt.rows crt.qMask deltaL pf.voleCheck
    let c2 := chal2 pf c1 hV (if st.delayed then muI c1 else ByteArray.empty) st.binder2
    let check := qsCheck pf c2 (constraintKeys st.params (correctedKeys pf crt.rows deltaL) deltaL
      (st.values c1 c2)) crt.qMask deltaL
    deltaL ≠ 0 ∧ chal3 pf c2 check = pf.delta ∧
    EndToEnd.qsCheck (cs c1 c2) st.params.qsDegree
        (Seed.zkCoeff (cs c1 c2).length (gfOfBytes c2 0) (gfOfBytes c2 16) (gfOfBytes c2 32)
          ⟨W128.word c2 48, 0⟩)
        (extW fun j : Fin st.params.witnessBits =>
          crt.rows[(j : ℕ)]!.toGF + SeedExtraction.bit (corrBit pf j) * deltaL)
        deltaL +
      (Seed.maskPoly st.params.qsDegree (fun i => crt.qMask[i]!.toGF) 0
        (fun i => gfOfBytes pf.qsProof (16 * (i - 1))) check).eval deltaL = 0

/-- **`accept_hacc` over `GF128` itself.** `hvals` is now an equation over `GF128`. -/
theorem accept_hacc_GF (T : CrtTables) (st : Statement) (proof : ByteArray)
    (h : (verify T st proof).accept = true) (cs : ByteArray → ByteArray → System GF128)
    (hvals : ∀ c1 c2 x, st.values c1 c2 x = (cs c1 c2).values x)
    (hdeg : ∀ c1 c2, ∀ e ∈ cs c1 c2, e.degree ≤ st.params.qsDegree) :
    AcceptEq T st proof cs :=
  accept_hacc gfId GF128.card_eq T st proof h cs
    (fun c1 c2 x => (List.map_id _).trans (hvals c1 c2 x)) hdeg

/-! ## The evaluators are the systems' values -/

theorem betaFast_eq : betaFast = beta := by
  funext b
  simp [betaFast, betaTab, Array.getD_eq_getD_getElem?, b.isLt]

/-- The cached combination coefficients: `l_k` is bytes `[16k, 16k+16)` of `H(chal2 ‖ dst)`. -/
theorem ofArr_combinationArr {n : ℕ} (chal2 dst : ByteArray) (k : Fin n) :
    ofArr (n := n) (combinationArr n chal2 dst) k =
      gfOfBytes (H (chal2 ++ dst) (16 * n)) (16 * k) := by
  simp [ofArr, combinationArr, Array.getD_eq_getD_getElem?, k.isLt]

/-- Moussaka issuance's system (`chal1`, `chal2` unused). -/
def moussakaIssueSys (t ctxIss : ByteArray) : System GF128 :=
  Moussaka.issueSystem (fun k => fnOf t k.val) (fnOf ctxIss)

/-- Moussaka redemption's system at `l = Combination(chal2, MOUSSAKA_REDEEM_COMBINE_DST)`. -/
def moussakaRedeemSys (anchors : List UovPk) (nf ctxIss ctxRed chal2 : ByteArray) :
    System GF128 :=
  Moussaka.redeemSystem beta GF256.toBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
    (fnOf ctxRed)
    (ofArr (combinationArr Moussaka.M chal2 (toBA (Spec.makeDst "mous" 0 'l' '0'))))

/-- Ratatouille issuance's system. -/
def ratatouilleIssueSys (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray) : System GF128 :=
  Ratatouille.issueSystem (fnOf c) tInit (fnOf ctxIss)

/-- Ratatouille spend's system at `l = Combination(chal2, RATATOUILLE_SPEND_COMBINE_DST)`. -/
def ratatouilleSpendSys (pk : UovPk) (nf : ByteArray) (d : ℕ) (cNext ctxIss chal2 : ByteArray) :
    System GF128 :=
  Ratatouille.spendSystem beta GF256.toBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss)
    (ofArr (combinationArr Ratatouille.uovM chal2 (toBA (Spec.makeDst "rata" 0 'l' '0'))))

/-- PomFRIT redemption's system at `h = hash_to_target(pk, sig, chal1, msg)` and
`l = Combination(chal2, POMFRIT_REDEEM_COMBINE_DST)`. -/
def pomfritRedeemSys (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool)
    (chal1 chal2 : ByteArray) : System GF128 :=
  let hb := pomfritTarget (pomfritParams labelRows) pk.digest chal1 sig msg
  PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map (fun k => ⟨fnOf hb k.val⟩)
    (ofArr (combinationArr 45 chal2 (toBA (Spec.makeDst "pomf" 0 'l' '0'))))

theorem moussakaIssue_values (t ctxIss : ByteArray) (labelRows : Bool) (c1 c2 : ByteArray)
    (x : ℕ → GF128) :
    (moussakaIssue t ctxIss labelRows).values c1 c2 x = (moussakaIssueSys t ctxIss).values x := by
  show Moussaka.issueValues _ _ x = _
  rw [Moussaka.issueValues_eq]
  rfl

theorem moussakaRedeem_values (anchors : List UovPk) (nf ctxIss ctxRed challengeDigest : ByteArray)
    (labelRows : Bool) (c1 c2 : ByteArray) (x : ℕ → GF128) :
    (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows).values c1 c2 x =
      (moussakaRedeemSys anchors nf ctxIss ctxRed c2).values x := by
  show Moussaka.redeemValues _ _ _ _ _ _ _ x = _
  rw [Moussaka.redeemValues_eq, betaFast_eq]
  rfl

theorem ratatouilleIssue_values (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray)
    (labelRows : Bool) (c1 c2 : ByteArray) (x : ℕ → GF128) :
    (ratatouilleIssue c tInit ctxIss labelRows).values c1 c2 x =
      (ratatouilleIssueSys c tInit ctxIss).values x := by
  show Ratatouille.issueValues _ _ _ x = _
  rw [← Ratatouille.issueSystem_values]
  rfl

theorem ratatouilleSpend_values (pk : UovPk) (nf : ByteArray) (d : ℕ) (cNext ctxIss : ByteArray)
    (labelRows : Bool) (c1 c2 : ByteArray) (x : ℕ → GF128) :
    (ratatouilleSpend pk nf d cNext ctxIss labelRows).values c1 c2 x =
      (ratatouilleSpendSys pk nf d cNext ctxIss c2).values x := by
  show Ratatouille.spendValues _ _ _ _ _ _ _ _ x = _
  rw [← Ratatouille.spendSystem_values, betaFast_eq]
  rfl

theorem pomfritRedeem_values (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool)
    (c1 c2 : ByteArray) (x : ℕ → GF128) :
    (pomfritRedeem pk sig msg labelRows).values c1 c2 x =
      (pomfritRedeemSys pk sig msg labelRows c1 c2).values x := by
  unfold pomfritRedeem pomfritRedeemSys
  rw [betaFast_eq]

/-! ## Acceptance, per relation -/

/-- **Moussaka issuance: acceptance gives the accepting equation for `issueSystem`.** -/
theorem moussakaIssue_accept (T : CrtTables) (t ctxIss : ByteArray) (labelRows : Bool)
    (proof : ByteArray) (h : (verify T (moussakaIssue t ctxIss labelRows) proof).accept = true) :
    AcceptEq T (moussakaIssue t ctxIss labelRows) proof fun _ _ => moussakaIssueSys t ctxIss :=
  accept_hacc_GF T _ proof h _ (moussakaIssue_values t ctxIss labelRows)
    fun _ _ => Degree.moussaka_issue_deg _ _

/-- **Moussaka redemption: acceptance gives the accepting equation for `redeemSystem`**, at the
`l` the verifier derives from `chal2`. -/
theorem moussakaRedeem_accept (T : CrtTables) (anchors : List UovPk)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool) (proof : ByteArray)
    (h : (verify T (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      proof).accept = true) :
    AcceptEq T (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) proof
      fun _ c2 => moussakaRedeemSys anchors nf ctxIss ctxRed c2 :=
  accept_hacc_GF T _ proof h _
    (moussakaRedeem_values anchors nf ctxIss ctxRed challengeDigest labelRows)
    fun _ _ => Degree.moussaka_redeem_deg _ _ _ _ _ _ _

/-- **Ratatouille issuance: acceptance gives the accepting equation for `issueSystem`.** -/
theorem ratatouilleIssue_accept (T : CrtTables) (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray)
    (labelRows : Bool) (proof : ByteArray)
    (h : (verify T (ratatouilleIssue c tInit ctxIss labelRows) proof).accept = true) :
    AcceptEq T (ratatouilleIssue c tInit ctxIss labelRows) proof
      fun _ _ => ratatouilleIssueSys c tInit ctxIss :=
  accept_hacc_GF T _ proof h _ (ratatouilleIssue_values c tInit ctxIss labelRows)
    fun _ _ => Degree.ratatouille_issue_deg _ _ _

/-- **Ratatouille spend: acceptance gives the accepting equation for `spendSystem`.** -/
theorem ratatouilleSpend_accept (T : CrtTables) (pk : UovPk) (nf : ByteArray) (d : ℕ)
    (cNext ctxIss : ByteArray) (labelRows : Bool) (proof : ByteArray)
    (h : (verify T (ratatouilleSpend pk nf d cNext ctxIss labelRows) proof).accept = true) :
    AcceptEq T (ratatouilleSpend pk nf d cNext ctxIss labelRows) proof
      fun _ c2 => ratatouilleSpendSys pk nf d cNext ctxIss c2 :=
  accept_hacc_GF T _ proof h _ (ratatouilleSpend_values pk nf d cNext ctxIss labelRows)
    fun _ _ => Degree.ratatouille_spend_deg _ _ _ _ _ _ _ _

/-- **PomFRIT redemption: acceptance gives the accepting equation for `pomfritRedeemSystem`**, at
the target `h` the verifier derives from `chal1` and the `l` it derives from `chal2`. -/
theorem pomfritRedeem_accept (T : CrtTables) (pk : UovPk) (sig msg : ByteArray)
    (labelRows : Bool) (proof : ByteArray)
    (h : (verify T (pomfritRedeem pk sig msg labelRows) proof).accept = true) :
    AcceptEq T (pomfritRedeem pk sig msg labelRows) proof
      (pomfritRedeemSys pk sig msg labelRows) :=
  accept_hacc_GF T _ proof h _ (pomfritRedeem_values pk sig msg labelRows)
    fun _ _ => PomFRIT.degree_pomfritRedeemSystem _ _ _ _ _ _ _

/-- **PomFRIT's `verify`**: acceptance means the refresher commitment matches and the proof
`sig[0 .. proofBytes)` satisfies `pomfritRedeem_accept`. -/
theorem pomfritVerify_accept (T : CrtTables) (pk : UovPk) (sig msg : ByteArray)
    (labelRows : Bool) (h : (pomfritVerify T pk sig msg labelRows).accept = true) :
    let n := (pomfritParams labelRows).proofBytes
    toBA (Spec.PomFRIT.commitRefresher (toL (sig.extract (n + 32) (n + 64)))) =
        sig.extract n (n + 32) ∧
      AcceptEq T (pomfritRedeem pk sig msg labelRows) (sig.extract 0 n)
        (pomfritRedeemSys pk sig msg labelRows) := by
  intro n
  dsimp only [pomfritVerify] at h
  split_ifs at h with hc
  simp only [bne, Bool.not_eq_true, Bool.not_eq_false'] at hc
  exact ⟨(byteArray_beq_iff _ _).1 hc, pomfritRedeem_accept T pk sig msg labelRows _ h⟩

/-! ## Other embeddings -/

theorem degree_map {G H : Type*} (f : G → H) : ∀ e : Expr G, (e.map f).degree = e.degree
  | .wit _ => rfl
  | .const _ => rfl
  | .add a b => by simp only [Expr.map, Expr.degree, degree_map f a, degree_map f b]
  | .mul a b => by simp only [Expr.map, Expr.degree, degree_map f a, degree_map f b]

variable {F : Type*} [Field F]

/-- `hvals` for any embedding `φ`, with the system mapped along `φ`: e.g. `accept_hacc_K` with
`cs c1 c2 := (sys c1 c2).map (Expr.map gfK)` (degrees by `degree_map`). -/
theorem values_map (φ : GFEmbedding F) {values : (ℕ → GF128) → List GF128} {cs : System GF128}
    (h : ∀ x, values x = cs.values x) (x : ℕ → GF128) :
    (values x).map φ = System.values (cs.map (Expr.map φ)) (φ ∘ x) := by
  rw [h, System.values, System.values, List.map_map, List.map_map]
  exact List.map_congr_left fun e _ => (eval_map φ x e).symm

end VoleMole.Verifier.Bridge
