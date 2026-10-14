import VoleMole.Verifier.Bridge.Chain

/-!
# Bridge, per relation: extraction from the executable verifier's chains

`EndToEnd/Concrete.lean`'s `*_extract_gf128`, with `Claim4Hyp` and the accepting equation on the
whole accepting set discharged for the executable verifier (`chain_claim4`, at faest-arch-opt's CRT
tables, `liftInvOk_tables`). For a chain `ch` of the relation's statement and a set `A` of
challenges on the chain (`Chain.OnChain`; `onChain_of_accept` puts every accepted proof of the
chain there), the conclusion is that of `*_extract_gf128`: **some known tree's committed corrected
small-VOLE value `u^{(i)} + d` encodes a witness of the relation, or at most `max(d, 1)` admissible
`chal3` are accepted.**

The chain's constraint evaluator is the relation's system (`hvals`); for the combined relations at
a combination vector `l`, and for PomFRIT at a target computed from some `c1`. For a chain of the
executable verifier (`Chain.vals = st.values chal1 chal2`, `onChain_of_accept`) `hvals` is
`*_values`, with `l = Combination(chal2)` (`*Sys = *SysL … (ofArr (combinationArr …))`, by
definition) and `c1 = chal1`; `Prob/ChainRelations.lean` samples `l` independently instead.

Remaining hypotheses (all probabilistic or random-oracle; see `Bridge/Chain.lean`):
* `hkos`: `chal1` is KOS-good for the committed responses on `S ⊇ A` (L3);
* `hL2`: the trees outside `known` (those with a dead leaf) have a fixed block on `A` (L2);
* `hQS` (and `hcomb` for the combined relations): if `|A| ≥ 2`, `chal2` (and `l`) are good for
  `w* = u* + d`, where `u*` is the slope of the committed witness rows on `A` (then unique, the
  canonical slope of L4 §5);
* `hδ`, `hclaim1`: admissible `chal3` decode injectively, accepted ones lie in `A` (L1).
-/

open Finset

namespace VoleMole.Verifier.Bridge

open VoleMole.Arith VoleMole.Verifier VoleMole.EndToEnd VoleMole.SeedExtraction

noncomputable section

/-- With at most one challenge on the chain, at most one admissible `chal3` is accepted. -/
lemma few_of_card_le_one {Ch : Type*} {A : Finset Blocks} (hA1 : A.card ≤ 1) (Z : Finset Ch)
    (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) {n : ℕ} (hn : 1 ≤ n) : #{x ∈ Z | acc x} ≤ n := by
  refine le_trans ?_ (hA1.trans hn)
  refine Finset.card_le_card_of_injOn δ (fun x hx => ?_) (hδ.mono fun x hx => ?_)
  · have hx' := Finset.mem_filter.1 hx
    exact hclaim1 x hx'.1 hx'.2
  · exact (Finset.mem_filter.1 hx).1

/-- **Moussaka issuance, from the executable verifier's chains.** -/
theorem moussakaIssue_extract_chain {Ch : Type*} (t ctxIss : ByteArray) (labelRows : Bool) (ch : Chain)
    (hvals : ∀ x, ch.vals x = (moussakaIssueSys t ctxIss).values x) {A : Finset Blocks}
    (hA : ∀ Δ ∈ A, ch.OnChain (moussakaIssue t ctxIss labelRows) CrtGen.tables Δ) {S : Set Blocks} (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift CrtGen.tables) (ch.kosQ (moussakaIssue t ctxIss labelRows) CrtGen.tables) (ch.kosD (moussakaIssue t ctxIss labelRows) CrtGen.tables))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (moussakaIssue t ctxIss labelRows) CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      ¬(moussakaIssueSys t ctxIss).Holds (wStar uStar (ch.dc (moussakaIssue t ctxIss labelRows))) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32) ⟨W128.word ch.chal2 48, 0⟩ (valVec (moussakaIssueSys t ctxIss) (wStar uStar (ch.dc (moussakaIssue t ctxIss labelRows)))) ≠ 0)
    (Z : Finset Ch) (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, moussakaIssueWit (fun k => fnOf t k.val) (fnOf ctxIss) (candidate (F := GF128) (ch.u (moussakaIssue t ctxIss labelRows)) (ch.dc (moussakaIssue t ctxIss labelRows)) i)) ∨
      #{x ∈ Z | acc x} ≤ 9 := by
  by_cases hA1 : A.card ≤ 1
  · exact Or.inr (few_of_card_le_one hA1 Z δ hδ acc hclaim1 (by norm_num))
  obtain ⟨uStar, R, hR, hK, hacc⟩ := chain_claim4 liftInvOk_tables (moussakaIssue t ctxIss labelRows) ch _ hvals (Degree.moussaka_issue_deg _ _) hA hAS hkos hL2
  exact moussaka_issue_extract_gf128 _ _ hK (ch.dc (moussakaIssue t ctxIss labelRows)) _ _ _ _ R hR hacc
    (hQS (by omega) uStar hK.consistent) Z δ hδ acc hclaim1

/-- **Moussaka redemption, from the executable verifier's chains.** -/
theorem moussakaRedeem_extract_chain {Ch : Type*} (anchors : List UovPk) (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool) (ch : Chain)
    (l : Fin Moussaka.M → GF128) (hvals : ∀ x, ch.vals x = (moussakaRedeemSysL anchors nf ctxIss ctxRed l).values x) {A : Finset Blocks}
    (hA : ∀ Δ ∈ A, ch.OnChain (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) CrtGen.tables Δ) {S : Set Blocks} (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift CrtGen.tables) (ch.kosQ (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) CrtGen.tables) (ch.kosD (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) CrtGen.tables))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      ¬(moussakaRedeemSysL anchors nf ctxIss ctxRed l).Holds (wStar uStar (ch.dc (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows))) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32) ⟨W128.word ch.chal2 48, 0⟩ (valVec (moussakaRedeemSysL anchors nf ctxIss ctxRed l) (wStar uStar (ch.dc (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)))) ≠ 0)
    (hcomb : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      (moussakaRedeemSysL anchors nf ctxIss ctxRed l).Holds (wStar uStar (ch.dc (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows))) → moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss) (fnOf ctxRed) (wStar uStar (ch.dc (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows))))
    (Z : Finset Ch) (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss) (fnOf ctxRed) (candidate (F := GF128) (ch.u (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)) (ch.dc (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)) i)) ∨
      #{x ∈ Z | acc x} ≤ 9 := by
  by_cases hA1 : A.card ≤ 1
  · exact Or.inr (few_of_card_le_one hA1 Z δ hδ acc hclaim1 (by norm_num))
  obtain ⟨uStar, R, hR, hK, hacc⟩ := chain_claim4 liftInvOk_tables (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) ch _ hvals (Degree.moussaka_redeem_deg _ _ _ _ _ _ _) hA hAS hkos hL2
  exact moussaka_redeem_extract_gf128 _ _ _ _ _ hK (ch.dc (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)) _ _ _ _ R hR hacc
    (hQS (by omega) uStar hK.consistent) (hcomb (by omega) uStar hK.consistent) Z δ hδ acc hclaim1

/-- **Ratatouille issuance, from the executable verifier's chains.** -/
theorem ratatouilleIssue_extract_chain {Ch : Type*} (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray) (labelRows : Bool) (ch : Chain)
    (hvals : ∀ x, ch.vals x = (ratatouilleIssueSys c tInit ctxIss).values x) {A : Finset Blocks}
    (hA : ∀ Δ ∈ A, ch.OnChain (ratatouilleIssue c tInit ctxIss labelRows) CrtGen.tables Δ) {S : Set Blocks} (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift CrtGen.tables) (ch.kosQ (ratatouilleIssue c tInit ctxIss labelRows) CrtGen.tables) (ch.kosD (ratatouilleIssue c tInit ctxIss labelRows) CrtGen.tables))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (ratatouilleIssue c tInit ctxIss labelRows) CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      ¬(ratatouilleIssueSys c tInit ctxIss).Holds (wStar uStar (ch.dc (ratatouilleIssue c tInit ctxIss labelRows))) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32) ⟨W128.word ch.chal2 48, 0⟩ (valVec (ratatouilleIssueSys c tInit ctxIss) (wStar uStar (ch.dc (ratatouilleIssue c tInit ctxIss labelRows)))) ≠ 0)
    (Z : Finset Ch) (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, ratatouilleIssueWit (fnOf c) tInit (fnOf ctxIss) (candidate (F := GF128) (ch.u (ratatouilleIssue c tInit ctxIss labelRows)) (ch.dc (ratatouilleIssue c tInit ctxIss labelRows)) i)) ∨
      #{x ∈ Z | acc x} ≤ 9 := by
  by_cases hA1 : A.card ≤ 1
  · exact Or.inr (few_of_card_le_one hA1 Z δ hδ acc hclaim1 (by norm_num))
  obtain ⟨uStar, R, hR, hK, hacc⟩ := chain_claim4 liftInvOk_tables (ratatouilleIssue c tInit ctxIss labelRows) ch _ hvals (Degree.ratatouille_issue_deg _ _ _) hA hAS hkos hL2
  exact ratatouille_issue_extract_gf128 _ _ _ hK (ch.dc (ratatouilleIssue c tInit ctxIss labelRows)) _ _ _ _ R hR hacc
    (hQS (by omega) uStar hK.consistent) Z δ hδ acc hclaim1

/-- **Ratatouille spend, from the executable verifier's chains.** -/
theorem ratatouilleSpend_extract_chain {Ch : Type*} (pk : UovPk) (nf : ByteArray) (d : ℕ) (cNext ctxIss : ByteArray) (labelRows : Bool) (ch : Chain)
    (l : Fin Ratatouille.uovM → GF128) (hvals : ∀ x, ch.vals x = (ratatouilleSpendSysL pk nf d cNext ctxIss l).values x) {A : Finset Blocks}
    (hA : ∀ Δ ∈ A, ch.OnChain (ratatouilleSpend pk nf d cNext ctxIss labelRows) CrtGen.tables Δ) {S : Set Blocks} (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift CrtGen.tables) (ch.kosQ (ratatouilleSpend pk nf d cNext ctxIss labelRows) CrtGen.tables) (ch.kosD (ratatouilleSpend pk nf d cNext ctxIss labelRows) CrtGen.tables))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (ratatouilleSpend pk nf d cNext ctxIss labelRows) CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      ¬(ratatouilleSpendSysL pk nf d cNext ctxIss l).Holds (wStar uStar (ch.dc (ratatouilleSpend pk nf d cNext ctxIss labelRows))) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32) ⟨W128.word ch.chal2 48, 0⟩ (valVec (ratatouilleSpendSysL pk nf d cNext ctxIss l) (wStar uStar (ch.dc (ratatouilleSpend pk nf d cNext ctxIss labelRows)))) ≠ 0)
    (hcomb : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (ratatouilleSpend pk nf d cNext ctxIss labelRows) CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      (ratatouilleSpendSysL pk nf d cNext ctxIss l).Holds (wStar uStar (ch.dc (ratatouilleSpend pk nf d cNext ctxIss labelRows))) → ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss) (wStar uStar (ch.dc (ratatouilleSpend pk nf d cNext ctxIss labelRows))))
    (Z : Finset Ch) (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss) (candidate (F := GF128) (ch.u (ratatouilleSpend pk nf d cNext ctxIss labelRows)) (ch.dc (ratatouilleSpend pk nf d cNext ctxIss labelRows)) i)) ∨
      #{x ∈ Z | acc x} ≤ 9 := by
  by_cases hA1 : A.card ≤ 1
  · exact Or.inr (few_of_card_le_one hA1 Z δ hδ acc hclaim1 (by norm_num))
  obtain ⟨uStar, R, hR, hK, hacc⟩ := chain_claim4 liftInvOk_tables (ratatouilleSpend pk nf d cNext ctxIss labelRows) ch _ hvals (Degree.ratatouille_spend_deg _ _ _ _ _ _ _ _) hA hAS hkos hL2
  exact ratatouille_spend_extract_gf128 _ _ _ _ _ _ hK (ch.dc (ratatouilleSpend pk nf d cNext ctxIss labelRows)) _ _ _ _ R hR hacc
    (hQS (by omega) uStar hK.consistent) (hcomb (by omega) uStar hK.consistent) Z δ hδ acc hclaim1

/-- **PomFRIT redemption, from the executable verifier's chains.** -/
theorem pomfritRedeem_extract_chain {Ch : Type*} (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool) (ch : Chain)
    (c1 : ByteArray) (l : Fin 45 → GF128) (hvals : ∀ x, ch.vals x = (pomfritRedeemSysL pk sig msg labelRows c1 l).values x) {A : Finset Blocks}
    (hA : ∀ Δ ∈ A, ch.OnChain (pomfritRedeem pk sig msg labelRows) CrtGen.tables Δ) {S : Set Blocks} (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift CrtGen.tables) (ch.kosQ (pomfritRedeem pk sig msg labelRows) CrtGen.tables) (ch.kosD (pomfritRedeem pk sig msg labelRows) CrtGen.tables))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (pomfritRedeem pk sig msg labelRows) CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      ¬(pomfritRedeemSysL pk sig msg labelRows c1 l).Holds (wStar uStar (ch.dc (pomfritRedeem pk sig msg labelRows))) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32) ⟨W128.word ch.chal2 48, 0⟩ (valVec (pomfritRedeemSysL pk sig msg labelRows c1 l) (wStar uStar (ch.dc (pomfritRedeem pk sig msg labelRows)))) ≠ 0)
    (hcomb : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw (pomfritRedeem pk sig msg labelRows) CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      (pomfritRedeemSysL pk sig msg labelRows c1 l).Holds (wStar uStar (ch.dc (pomfritRedeem pk sig msg labelRows))) → pomfritWit GF256.ofBits 119 45 pk.map (fun k => ⟨fnOf (pomfritTarget (pomfritParams labelRows) pk.digest c1 sig msg) k.val⟩) (wStar uStar (ch.dc (pomfritRedeem pk sig msg labelRows))))
    (Z : Finset Ch) (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, pomfritWit GF256.ofBits 119 45 pk.map (fun k => ⟨fnOf (pomfritTarget (pomfritParams labelRows) pk.digest c1 sig msg) k.val⟩) (candidate (F := GF128) (ch.u (pomfritRedeem pk sig msg labelRows)) (ch.dc (pomfritRedeem pk sig msg labelRows)) i)) ∨
      #{x ∈ Z | acc x} ≤ 2 := by
  by_cases hA1 : A.card ≤ 1
  · exact Or.inr (few_of_card_le_one hA1 Z δ hδ acc hclaim1 (by norm_num))
  obtain ⟨uStar, R, hR, hK, hacc⟩ := chain_claim4 liftInvOk_tables (pomfritRedeem pk sig msg labelRows) ch _ hvals (PomFRIT.degree_pomfritRedeemSystem _ _ _ _ _ _ _) hA hAS hkos hL2
  exact pomfrit_extract_gf128 119 45 _ _ _ hK (ch.dc (pomfritRedeem pk sig msg labelRows)) _ _ _ _ R hR hacc
    (hQS (by omega) uStar hK.consistent) (hcomb (by omega) uStar hK.consistent) Z δ hδ acc hclaim1

end

end VoleMole.Verifier.Bridge
