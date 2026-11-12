import VoleMole.Prob.ChainRelations
import VoleMole.EndToEnd.MoussakaUnbound
import VoleMole.Spec.MoussakaUnbound

/-!
# The unbound Moussaka relations as verifier statements, one chain (`security/moussaka-unbound.md`)

The random-oracle layer (`ROM/`) is stated for the executable verifier at a `Statement`
(`Verifier/Verify.lean`). The five base relations have theirs in `Verifier/Relations.lean`. For the
two unbound relations of PR #63 this file does not fix a statement. It states **the properties of a
statement that the bounds use** (`IssueStmt`, `RedeemStmt`), and every theorem here and in
`ROM/MoussakaUnbound*.lean` holds for any statement with them:

* the proof parameters of `unbound_issue.hpp` / `unbound_redeem.hpp`: `ℓ/8 = 232` (resp. `559`)
  witness bytes, `QS_DEGREE = 9`, label rows as chosen (`REUSE_CRT_WITNESS = true` on `main`, so
  `labelRows = false` there);
* the proof DSTs `UNBOUND_IHAT_ISSUE_PROOF_DST`, `UNBOUND_IHAT_REDEEM_PROOF_DST`
  (`makeDst "mous" 1 'i' '0'`, `… 'r' '0'`), non-delayed instance binding, and for redemption the
  combination `(M, UNBOUND_IHAT_REDEEM_COMBINE_DST)` (`makeDst "mous" 1 'l' '0'`), `M = 45`;
* the constraint evaluator is `System.values` of the `Arith/MoussakaUnbound.lean` system at the
  verifier's instance data (`issueSys`, `redeemSys`, at `β := beta`, `K := GF256`, with `l` decoded
  from the combination bytes as for the base relations, `combinationOf`).

The instance encoding is not constrained (only the adaptive theorems read it, through `hinj`). So a
statement for the executable verifier (`Verifier/Relations.lean`, extended on another branch) gets
all the bounds from one lemma `IssueStmt (its statement) …`, which is `rfl` for the parameters and
`uIssueValues_eq` / `uRedeemValues_eq` for the evaluator. `refIssue`, `refRedeem` are such
statements (with the sharing evaluators of `Arith/MoussakaUnbound.lean` and the C++ instance
encodings, `UnboundIssueRelation::hash_instance = t ‖ ctx_iss` and `hash_redeem_instance`), so the
hypotheses are satisfiable (`refIssue_stmt`, `refRedeem_stmt`).

## Results

* `issue_extract_chain`, `redeem_extract_chain`: `Bridge/ChainRelations.lean`'s `*_extract_chain`
  for the unbound relations (`chain_claim4` and `EndToEnd/MoussakaUnbound.lean`): some known tree's
  candidate encodes a witness (`moussakaUnboundIssueWit`, `moussakaUnboundRedeemWit`), or at most 9
  admissible `chal3` are accepted.
* `redeem_comb_bad_gf128`: the combination fails for at most a `2⁻¹²⁸` fraction of `l` (at most
  64 Anchors).
* `Prob.moussakaUnboundIssue_chain_prob`, `Prob.moussakaUnboundRedeem_chain_prob`: one chain with
  uniform independent `chal1`, `chal2` (and `l`): failure probability `≤ 2⁻¹⁵⁰ + ε_QS(3816)`
  (issuance), `≤ 2⁻¹⁵⁰ + ε_QS(7929) + 2⁻¹²⁸` (redemption); `3816`, `7929` are the constraint counts
  (`uIssueSystem_length`, `uRedeemSystem_length`).
-/

open Finset ENNReal

namespace VoleMole.Unbound

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.EndToEnd
open VoleMole.SeedExtraction

/-! ## The systems and the statement properties -/

/-- Unbound issuance's system at the instance `(t, ctx_iss)` (no `chal1`, no combination). -/
def issueSys (t ctxIss : ByteArray) : System GF128 :=
  MoussakaUnbound.uIssueSystem (fun k => fnOf t k.val) (fnOf ctxIss)

/-- Unbound redemption's system at a given combination vector `l`. -/
def redeemSysL (anchors : List UovPk) (nf ctxIss ctxRed : ByteArray)
    (l : Fin Moussaka.M → GF128) : System GF128 :=
  MoussakaUnbound.uRedeemSystem beta GF256.toBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
    (fnOf ctxRed) l

/-- Unbound redemption's system at the combination decoded from the bytes
`lb = H_comb(chal2 ‖ UNBOUND_IHAT_REDEEM_COMBINE_DST)`. -/
def redeemSys (anchors : List UovPk) (nf ctxIss ctxRed lb : ByteArray) : System GF128 :=
  redeemSysL anchors nf ctxIss ctxRed (ofArr (combinationOf Moussaka.M lb))

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
  values : ∀ c1 lb x, st.values c1 lb x = (issueSys t ctxIss).values x

/-- **A verifier statement for unbound redemption at `(anchors, nf, ctx_iss, ctx_red)`** (any
`challenge_digest`: it enters only the instance encoding). -/
structure RedeemStmt (st : Statement) (lr : Bool) (anchors : List UovPk)
    (nf ctxIss ctxRed : ByteArray) : Prop where
  params : st.params = redeemParams lr
  dst : st.dst = redeemDst
  delayed : st.delayed = false
  comb : st.comb = some (Moussaka.M, combDst)
  values : ∀ c1 lb x, st.values c1 lb x = (redeemSys anchors nf ctxIss ctxRed lb).values x

/-- A reference statement for unbound issuance: the C++ parameters, DST and instance encoding
(`t ‖ ctx_iss`), the sharing evaluator `uIssueValues`. -/
def refIssue (lr : Bool) (t ctxIss : ByteArray) : Statement where
  params := issueParams lr
  dst := issueDst
  instEnc := fun _ => toBA (VoleMole.Spec.MoussakaUnbound.IssueInstance.encode ⟨toL t, toL ctxIss⟩)
  values := fun _ _ w => MoussakaUnbound.uIssueValues (F := GF128) (fun k => fnOf t k.val)
    (fnOf ctxIss) w

/-- A reference statement for unbound redemption: the C++ parameters, DSTs and instance encoding
(`hash_redeem_instance`, the bound one's), the sharing evaluator `uRedeemValues`. -/
def refRedeem (lr : Bool) (anchors : List UovPk) (nf ctxIss ctxRed cd : ByteArray) : Statement where
  params := redeemParams lr
  dst := redeemDst
  instEnc := fun _ => toBA (VoleMole.Spec.Moussaka.RedeemInstance.encode
    ⟨anchors.map UovPk.toSpec, toL nf, toL ctxIss, toL ctxRed, toL cd⟩)
  comb := some (Moussaka.M, combDst)
  values := fun _ lb w => MoussakaUnbound.uRedeemValues beta GF256.toBits (anchors.map UovPk.map)
    (fnOf nf) (fnOf ctxIss) (fnOf ctxRed) (ofArr (combinationOf Moussaka.M lb)) w

theorem refIssue_stmt (lr : Bool) (t ctxIss : ByteArray) :
    IssueStmt (refIssue lr t ctxIss) lr t ctxIss where
  params := rfl
  dst := rfl
  delayed := rfl
  comb := rfl
  values _ _ x := MoussakaUnbound.uIssueValues_eq _ _ x

theorem refRedeem_stmt (lr : Bool) (anchors : List UovPk) (nf ctxIss ctxRed cd : ByteArray) :
    RedeemStmt (refRedeem lr anchors nf ctxIss ctxRed cd) lr anchors nf ctxIss ctxRed where
  params := rfl
  dst := rfl
  delayed := rfl
  comb := rfl
  values _ _ x := MoussakaUnbound.uRedeemValues_eq _ _ _ _ _ _ _ x

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

/-! ## The combination at GF(2¹²⁸) -/

open Classical in
/-- `moussaka_unbound_redeem_comb_bad` at the concrete fields: for at most 64 Anchors, the
combination holds without a witness for at most a `2⁻¹²⁸` fraction of the `l`. -/
theorem redeem_comb_bad_gf128 (anchors : List (ℕ → GF256)) (hn : anchors.length ≤ 64)
    (nf ctxIss ctxRed : ℕ → UInt8) (w : ℕ → GF128)
    (hw : ¬moussakaUnboundRedeemWit GF256.ofBits anchors nf ctxIss ctxRed w) :
    #{l : Fin Moussaka.M → GF128 |
        (MoussakaUnbound.uRedeemSystem beta GF256.toBits anchors nf ctxIss ctxRed l).Holds w} *
      2 ^ 128 ≤ (2 ^ 128) ^ Moussaka.M := by
  have := moussaka_unbound_redeem_comb_bad Arith.isEmbedding Arith.beta_zero anchors hn nf ctxIss
    ctxRed w hw
  rwa [GF128.card_eq, card_fun_gf128] at this

/-! ## From the executable verifier's chains -/

section Chain

variable [VoleMole.Verifier.HasPrg]

noncomputable section

/-- **Unbound issuance, from the executable verifier's chains** (as `moussakaIssue_extract_chain`,
for any statement with `IssueStmt`). -/
theorem issue_extract_chain {Ch : Type*} {st : Statement} {lr : Bool} {t ctxIss : ByteArray}
    (hst : IssueStmt st lr t ctxIss) (ch : Chain)
    (hvals : ∀ x, ch.vals x = (issueSys t ctxIss).values x) {A : Finset Blocks}
    (hA : ∀ Δ ∈ A, ch.OnChain st CrtGen.tables Δ) {S : Set Blocks} (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift CrtGen.tables) (ch.kosQ st CrtGen.tables)
      (ch.kosD st CrtGen.tables))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar,
      (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      ¬(issueSys t ctxIss).Holds (wStar uStar (ch.dc st)) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩ (valVec (issueSys t ctxIss) (wStar uStar (ch.dc st))) ≠ 0)
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
    (hvals : ∀ x, ch.vals x = (redeemSysL anchors nf ctxIss ctxRed l).values x) {A : Finset Blocks}
    (hA : ∀ Δ ∈ A, ch.OnChain st CrtGen.tables Δ) {S : Set Blocks} (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift CrtGen.tables) (ch.kosQ st CrtGen.tables)
      (ch.kosD st CrtGen.tables))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar,
      (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      ¬(redeemSysL anchors nf ctxIss ctxRed l).Holds (wStar uStar (ch.dc st)) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩
        (valVec (redeemSysL anchors nf ctxIss ctxRed l) (wStar uStar (ch.dc st))) ≠ 0)
    (hcomb : 2 ≤ A.card → ∀ uStar,
      (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      (redeemSysL anchors nf ctxIss ctxRed l).Holds (wStar uStar (ch.dc st)) →
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
    (hvals : ∀ ω x, (ch ω).vals x = (issueSys t ctxIss).values x)
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
    (fun ω => hc2 _) (fun _ _ => issueSys t ctxIss) 3816
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
    (hvals : ∀ ω x, (ch ω).vals x = (redeemSysL anchors nf ctxIss ctxRed ω.2.2).values x)
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
    (fun _ l => redeemSysL anchors nf ctxIss ctxRed l) 7929
    (fun _ _ => MoussakaUnbound.uRedeemSystem_length _ _ _ _ _ _ _)
    (fun _ w => moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
      (fnOf ctxIss) (fnOf ctxRed) w)
    (fun _ w => prU_comb_bad_le _ _ w fun hW =>
      redeem_comb_bad_gf128 _ (by simpa using hn) _ _ _ w hW)
    chal3Blocks (fun ω A => ChainHyps A (known ω) (acc ω)) _
    fun ω A hA hAS hkos hQS hcomb hP => redeem_extract_chain hst _ ω.2.2 (hvals ω) hA hAS hkos
      hP.1 hQS hcomb admissible deltaBlocks deltaBlocks_injOn _ hP.2).trans ?_
  gcongr
  exact epsKOS_chal3Blocks_le _ hst.witnessBytes_le hst.qsDegree_le

end VoleMole.Prob
