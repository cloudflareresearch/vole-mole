import VoleMole.Prob.ChainRelations
import VoleMole.Verifier.Bridge.Relations
import VoleMole.EndToEnd.MoussakaUnbound
import VoleMole.Spec.MoussakaUnbound

/-!
# The unbound Moussaka relations: statement properties, one chain (`security/moussaka-unbound.md`)

The random-oracle layer for the unbound relations (`ROM/MoussakaUnbound*.lean`) is stated, once,
for **any verifier statement with the properties the bounds use** (`IssueStmt`, `RedeemStmt`):

* the proof parameters of `src/ihat/unbound_issue.hpp` / `unbound_redeem.hpp`: `ℓ/8 = 232`
  (resp. `559`) witness bytes, `QS_DEGREE = 9`, label rows as chosen (`REUSE_CRT_WITNESS = true` on
  `main`, so `labelRows = false` there);
* the proof DSTs `UNBOUND_IHAT_ISSUE_PROOF_DST`, `UNBOUND_IHAT_REDEEM_PROOF_DST`
  (`makeDst "mous" 1 'i' '0'`, `… 'r' '0'`), non-delayed instance binding, and for redemption the
  combination `(M, UNBOUND_IHAT_REDEEM_COMBINE_DST)` (`makeDst "mous" 1 'l' '0'`), `M = 45`;
* the constraint evaluator is `System.values` of the `Arith/MoussakaUnbound.lean` system at the
  instance data (`moussakaUnboundIssueSys`, `moussakaUnboundRedeemSys`,
  `Verifier/Bridge/Relations.lean`).

The instance encoding is not constrained (the adaptive theorems read it through `hinj`).
**The executable verifier's statements have these properties** (`moussakaUnboundIssue_stmt`,
`moussakaUnboundRedeem_stmt`: `rfl` for parameters, DST, binding and combination,
`moussakaUnbound*_values` for the evaluator), so every bound applies to `moussakaUnboundIssue`,
`moussakaUnboundRedeem` of `Verifier/Relations.lean`.

## Results

* `moussakaUnboundIssue_stmt`, `moussakaUnboundRedeem_stmt`: the link to the executable verifier.
* `issue_extract_chain`, `redeem_extract_chain`: `Bridge/ChainRelations.lean`'s
  `moussakaUnbound*_extract_chain` for any statement with the properties: some known tree's
  candidate encodes a witness (`moussakaUnboundIssueWit`, `moussakaUnboundRedeemWit`), or at most 9
  admissible `chal3` are accepted.
* `Prob.moussakaUnboundIssue_chain_prob`, `Prob.moussakaUnboundRedeem_chain_prob`: one chain with
  uniform independent `chal1`, `chal2` (and `l`): failure probability `≤ 2⁻¹⁵⁰ + ε_QS(3816)`
  (issuance), `≤ 2⁻¹⁵⁰ + ε_QS(7929) + 2⁻¹²⁸` (redemption, at most 64 Anchors, with
  `moussaka_unbound_redeem_comb_bad_gf128`); `3816`, `7929` are the constraint counts
  (`uIssueSystem_length`, `uRedeemSystem_length`).
-/

open Finset ENNReal

namespace VoleMole.Unbound

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.EndToEnd
open VoleMole.SeedExtraction

/-! ## The systems and the statement properties -/

/-- `UNBOUND_ISSUE_WITNESS_BYTES = 232`, `QS_DEGREE = 9`. -/
def issueParams (lr : Bool) : Params := { witnessBytes := 232, qsDegree := 9, labelRows := lr }

/-- `UNBOUND_REDEEM_WITNESS_BYTES = 559`, `QS_DEGREE = 9`. -/
def redeemParams (lr : Bool) : Params := { witnessBytes := 559, qsDegree := 9, labelRows := lr }

/-- `UNBOUND_IHAT_ISSUE_PROOF_DST`, `UNBOUND_IHAT_REDEEM_PROOF_DST`,
`UNBOUND_IHAT_REDEEM_COMBINE_DST` (`src/dst.hpp`). -/
def issueDst : ByteArray := toBA (VoleMole.Spec.makeDst "mous" 1 'i' '0')
def redeemDst : ByteArray := toBA (VoleMole.Spec.makeDst "mous" 1 'r' '0')
def combDst : ByteArray := toBA (VoleMole.Spec.makeDst "mous" 1 'l' '0')

/-- **A verifier statement for unbound issuance at `(t, ctx_iss)`**: the properties the bounds
use. (`dst` and `delayed` are used by the adaptive theorems only.) -/
structure IssueStmt (st : Statement) (lr : Bool) (t ctxIss : ByteArray) : Prop where
  params : st.params = issueParams lr
  dst : st.dst = issueDst
  delayed : st.delayed = false
  comb : st.comb = none
  values : ∀ c1 lb x, st.values c1 lb x = (moussakaUnboundIssueSys t ctxIss).values x

/-- **A verifier statement for unbound redemption at `(anchors, nf, ctx_iss, ctx_red)`** (any
`challenge_digest`: it enters only the instance encoding). -/
structure RedeemStmt (st : Statement) (lr : Bool) (anchors : List UovPk)
    (nf ctxIss ctxRed : ByteArray) : Prop where
  params : st.params = redeemParams lr
  dst : st.dst = redeemDst
  delayed : st.delayed = false
  comb : st.comb = some (Moussaka.M, combDst)
  values : ∀ c1 lb x, st.values c1 lb x = (moussakaUnboundRedeemSys anchors nf ctxIss ctxRed lb).values x

/-- **The link**: the executable verifier's unbound issuance statement
(`Verifier/Relations.lean`) has the properties, so every bound applies to it. -/
theorem moussakaUnboundIssue_stmt (t ctxIss : ByteArray) (lr : Bool) :
    IssueStmt (moussakaUnboundIssue t ctxIss lr) lr t ctxIss where
  params := rfl
  dst := rfl
  delayed := rfl
  comb := rfl
  values := moussakaUnboundIssue_values t ctxIss lr

/-- **The link**: the executable verifier's unbound redemption statement has the properties (any
`challenge_digest`). -/
theorem moussakaUnboundRedeem_stmt (anchors : List UovPk) (nf ctxIss ctxRed cd : ByteArray)
    (lr : Bool) :
    RedeemStmt (moussakaUnboundRedeem anchors nf ctxIss ctxRed cd lr) lr anchors nf ctxIss
      ctxRed where
  params := rfl
  dst := rfl
  delayed := rfl
  comb := rfl
  values := moussakaUnboundRedeem_values anchors nf ctxIss ctxRed cd lr

theorem IssueStmt.witnessBytes_le {st : Statement} {lr : Bool} {t ctxIss : ByteArray}
    (h : IssueStmt st lr t ctxIss) : st.params.witnessBytes ≤ 847 := by
  rw [h.params]; simp [issueParams]

theorem IssueStmt.qsDegree_le {st : Statement} {lr : Bool} {t ctxIss : ByteArray}
    (h : IssueStmt st lr t ctxIss) : st.params.qsDegree ≤ 9 := by
  rw [h.params]; simp [issueParams]

theorem RedeemStmt.witnessBytes_le {st : Statement} {lr : Bool} {anchors : List UovPk}
    {nf ctxIss ctxRed : ByteArray} (h : RedeemStmt st lr anchors nf ctxIss ctxRed) :
    st.params.witnessBytes ≤ 847 := by
  rw [h.params]; simp [redeemParams]

theorem RedeemStmt.qsDegree_le {st : Statement} {lr : Bool} {anchors : List UovPk}
    {nf ctxIss ctxRed : ByteArray} (h : RedeemStmt st lr anchors nf ctxIss ctxRed) :
    st.params.qsDegree ≤ 9 := by
  rw [h.params]; simp [redeemParams]

/-! ## From the executable verifier's chains -/

section Chain

variable [VoleMole.Verifier.HasPrg]

noncomputable section

/-- **Unbound issuance, from the executable verifier's chains** (as `moussakaIssue_extract_chain`,
for any statement with `IssueStmt`). -/
theorem issue_extract_chain {Ch : Type*} {st : Statement} {lr : Bool} {t ctxIss : ByteArray}
    (hst : IssueStmt st lr t ctxIss) (ch : Chain)
    (hvals : ∀ x, ch.vals x = (moussakaUnboundIssueSys t ctxIss).values x) {A : Finset Blocks}
    (hA : ∀ Δ ∈ A, ch.OnChain st CrtGen.tables Δ) {S : Set Blocks} (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift CrtGen.tables) (ch.kosQ st CrtGen.tables)
      (ch.kosD st CrtGen.tables))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar,
      (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      ¬(moussakaUnboundIssueSys t ctxIss).Holds (wStar uStar (ch.dc st)) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩ (valVec (moussakaUnboundIssueSys t ctxIss) (wStar uStar (ch.dc st))) ≠ 0)
    (Z : Finset Ch) (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, moussakaUnboundIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)
      (candidate (F := GF128) (ch.u st) (ch.dc st) i)) ∨ #{x ∈ Z | acc x} ≤ 9 := by
  by_cases hA1 : A.card ≤ 1
  · exact Or.inr (few_of_card_le_one hA1 Z δ hδ acc hclaim1 (by norm_num))
  obtain ⟨p, dst, del, b1, b2, ie, cb, vals⟩ := st
  obtain ⟨hp, -, -, -, -⟩ := hst
  dsimp only at hp
  subst hp
  obtain ⟨uStar, R, hR, hK, hacc⟩ := chain_claim4 liftInvOk_tables _ ch _ hvals
    (Degree.moussaka_unbound_issue_deg _ _) hA hAS hkos hL2
  exact moussaka_unbound_issue_extract (F := GF128) _ _ hK _ _ _ _ _ R hR hacc
    (hQS (by omega) uStar hK.consistent) Z δ hδ acc hclaim1

/-- **Unbound redemption, from the executable verifier's chains** (as
`moussakaRedeem_extract_chain`, for any statement with `RedeemStmt`). -/
theorem redeem_extract_chain {Ch : Type*} {st : Statement} {lr : Bool} {anchors : List UovPk}
    {nf ctxIss ctxRed : ByteArray} (hst : RedeemStmt st lr anchors nf ctxIss ctxRed) (ch : Chain)
    (l : Fin Moussaka.M → GF128)
    (hvals : ∀ x, ch.vals x = (moussakaUnboundRedeemSysL anchors nf ctxIss ctxRed l).values x) {A : Finset Blocks}
    (hA : ∀ Δ ∈ A, ch.OnChain st CrtGen.tables Δ) {S : Set Blocks} (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift CrtGen.tables) (ch.kosQ st CrtGen.tables)
      (ch.kosD st CrtGen.tables))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar,
      (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      ¬(moussakaUnboundRedeemSysL anchors nf ctxIss ctxRed l).Holds (wStar uStar (ch.dc st)) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩
        (valVec (moussakaUnboundRedeemSysL anchors nf ctxIss ctxRed l) (wStar uStar (ch.dc st))) ≠ 0)
    (hcomb : 2 ≤ A.card → ∀ uStar,
      (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      (moussakaUnboundRedeemSysL anchors nf ctxIss ctxRed l).Holds (wStar uStar (ch.dc st)) →
      moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed) (wStar uStar (ch.dc st)))
    (Z : Finset Ch) (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
      (fnOf ctxIss) (fnOf ctxRed) (candidate (F := GF128) (ch.u st) (ch.dc st) i)) ∨
      #{x ∈ Z | acc x} ≤ 9 := by
  by_cases hA1 : A.card ≤ 1
  · exact Or.inr (few_of_card_le_one hA1 Z δ hδ acc hclaim1 (by norm_num))
  obtain ⟨p, dst, del, b1, b2, ie, cb, vals⟩ := st
  obtain ⟨hp, -, -, -, -⟩ := hst
  dsimp only at hp
  subst hp
  obtain ⟨uStar, R, hR, hK, hacc⟩ := chain_claim4 liftInvOk_tables _ ch _ hvals
    (Degree.moussaka_unbound_redeem_deg _ _ _ _ _ _ _) hA hAS hkos hL2
  exact moussaka_unbound_redeem_extract (F := GF128) _ _ _ _ _ _ _ _ hK _ _ _ _ _ R hR hacc
    (hQS (by omega) uStar hK.consistent) (hcomb (by omega) uStar hK.consistent) Z δ hδ acc hclaim1

end

end Chain

end VoleMole.Unbound

/-! ## One chain, uniform challenges -/

namespace VoleMole.Prob

variable [VoleMole.Verifier.HasPrg]

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.EndToEnd
open VoleMole.SeedExtraction VoleMole.Unbound

/-- **Unbound issuance, one chain, uniform challenges** (as `moussakaIssue_chain_prob`):
`≤ 2⁻¹⁵⁰ + ε_QS(3816)`. -/
theorem moussakaUnboundIssue_chain_prob {st : Statement} {lr : Bool} {t ctxIss : ByteArray}
    (hst : IssueStmt st lr t ctxIss) (pre : Chain)
    (mid : Bytes 136 → Chain) (ch : Bytes 136 × Bytes 56 → Chain)
    (hpre : ∀ b, Chain.SamePrefix st pre (mid b))
    (hc1 : ∀ b, (mid b).chal1 = b.ba)
    (hmid : ∀ ω, Chain.SameMid st (mid ω.1) (ch ω))
    (hc2 : ∀ ω, (ch ω).chal2 = ω.2.ba)
    (hvals : ∀ ω x, (ch ω).vals x = (moussakaUnboundIssueSys t ctxIss).values x)
    (known : Bytes 136 × Bytes 56 → Finset (Fin BAVC.tau))
    (acc : Bytes 136 × Bytes 56 → Bytes 16 → Prop) [∀ ω, DecidablePred (acc ω)] :
    prU (Bytes 136 × Bytes 56) (fun ω =>
      ChainHyps (onSet st CrtGen.tables (ch ω) chal3Blocks) (known ω) (acc ω) ∧
      ¬((∃ i ∈ known ω, moussakaUnboundIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)
          (candidate (F := GF128) ((ch ω).u st) ((ch ω).dc st) i)) ∨
        #{x ∈ admissible | acc ω x} ≤ 9)) ≤
      (2 ^ 150 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3816) := by
  rw [prU_map_equiv dropUnit]
  refine (chain_prob liftInvOk_tables _ pre mid (ch ∘ dropUnit) hpre hc1 (fun ω => hmid _)
    (fun ω => hc2 _) (fun _ _ => moussakaUnboundIssueSys t ctxIss) 3816
    (fun _ _ => MoussakaUnbound.uIssueSystem_length _ _) (fun _ _ => True)
    (fun _ _ => prU_no_comb _ (by simp))
    chal3Blocks (fun ω A => ChainHyps A (known (dropUnit ω)) (acc (dropUnit ω))) _
    fun ω A hA hAS hkos hQS _ hP => issue_extract_chain hst _
      (hvals _) hA hAS hkos hP.1 hQS admissible deltaBlocks deltaBlocks_injOn _ hP.2).trans ?_
  rw [add_zero]
  gcongr
  exact epsKOS_chal3Blocks_le _ hst.witnessBytes_le hst.qsDegree_le

/-- **Unbound redemption, one chain, uniform challenges** (`l` uniform and independent; as
`moussakaRedeem_chain_prob`): `≤ 2⁻¹⁵⁰ + ε_QS(7929) + 2⁻¹²⁸`. -/
theorem moussakaUnboundRedeem_chain_prob {st : Statement} {lr : Bool} {anchors : List UovPk}
    (hn : anchors.length ≤ 64) {nf ctxIss ctxRed : ByteArray}
    (hst : RedeemStmt st lr anchors nf ctxIss ctxRed) (pre : Chain)
    (mid : Bytes 136 → Chain) (ch : Bytes 136 × Bytes 56 × (Fin Moussaka.M → GF128) → Chain)
    (hpre : ∀ b, Chain.SamePrefix st pre (mid b))
    (hc1 : ∀ b, (mid b).chal1 = b.ba)
    (hmid : ∀ ω, Chain.SameMid st (mid ω.1) (ch ω))
    (hc2 : ∀ ω, (ch ω).chal2 = ω.2.1.ba)
    (hvals : ∀ ω x, (ch ω).vals x = (moussakaUnboundRedeemSysL anchors nf ctxIss ctxRed ω.2.2).values x)
    (known : Bytes 136 × Bytes 56 × (Fin Moussaka.M → GF128) → Finset (Fin BAVC.tau))
    (acc : Bytes 136 × Bytes 56 × (Fin Moussaka.M → GF128) → Bytes 16 → Prop)
    [∀ ω, DecidablePred (acc ω)] :
    prU (Bytes 136 × Bytes 56 × (Fin Moussaka.M → GF128)) (fun ω =>
      ChainHyps (onSet st CrtGen.tables (ch ω) chal3Blocks) (known ω) (acc ω) ∧
      ¬((∃ i ∈ known ω, moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
          (fnOf ctxIss) (fnOf ctxRed)
          (candidate (F := GF128) ((ch ω).u st) ((ch ω).dc st) i)) ∨
        #{x ∈ admissible | acc ω x} ≤ 9)) ≤
      (2 ^ 150 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
        (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  refine (chain_prob liftInvOk_tables _ pre mid ch hpre hc1 hmid hc2
    (fun _ l => moussakaUnboundRedeemSysL anchors nf ctxIss ctxRed l) 7929
    (fun _ _ => MoussakaUnbound.uRedeemSystem_length _ _ _ _ _ _ _)
    (fun _ w => moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
      (fnOf ctxIss) (fnOf ctxRed) w)
    (fun _ w => prU_comb_bad_le _ _ w fun hW =>
      moussaka_unbound_redeem_comb_bad_gf128 _ (by simpa using hn) _ _ _ w hW)
    chal3Blocks (fun ω A => ChainHyps A (known ω) (acc ω)) _
    fun ω A hA hAS hkos hQS hcomb hP => redeem_extract_chain hst _ ω.2.2 (hvals ω) hA hAS hkos
      hP.1 hQS hcomb admissible deltaBlocks deltaBlocks_injOn _ hP.2).trans ?_
  gcongr
  exact epsKOS_chal3Blocks_le _ hst.witnessBytes_le hst.qsDegree_le

end VoleMole.Prob
