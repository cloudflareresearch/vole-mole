import VoleMole.Prob.Challenges
import VoleMole.Verifier.Bridge.ChainRelations

/-!
# The per-chain theorem with uniform challenges (plan M3)

`Bridge/ChainRelations.lean`'s `*_extract_chain` with `hkos`, `hQS`, `hcomb` and `hδ` replaced by
uniform challenges: for one chain of the executable verifier, with the commitments fixed before
`chal1`, `ũ`, `d`, `h_V` fixed before `chal2`, and `chal1`, `chal2`, `l` uniform and independent,

  `Pr[L2 ∧ hclaim1 ∧ ¬(extraction ∨ at most max(d, 1) admissible chal3 accepted)]`
  `≤ ε_KOS + ε_QS(n) + 2⁻¹²⁸ ≤ 2⁻¹⁵⁰ + ε_QS(n) + 2⁻¹²⁸`.

This is the classical "one chain, independent challenges" form of L3 + L4 + L6 (the FAEST spec's
per-round knowledge-soundness bound). What it does not cover, and keeps as hypotheses or as part of
the event:
* L2 (`IsFixed` for the trees with a dead leaf, as a function of the samples) and `hclaim1`
  (accepted admissible `chal3` decode into the chain's challenges): they are conjuncts of the
  event, so the bound says nothing when they fail. `onChain_of_accept` gives `hclaim1` from the
  binding of the leaf commitments and the RO "same chain" step (L1);
* the random-oracle steps: that the verifier's `chal1`, `chal2` are fresh uniform answers on this
  chain, and that `l = H(chal2 ‖ dst)` is uniform and independent of `chal2` (`chal2`, `l` and
  `vals` are `Chain` fields; `onChain_of_accept` ties them to SHAKE), and the union over the
  queries (plan M5).

## The chain family

The samples are `ω = (b₁, b₂, l) : Bytes 136 × Bytes 56 × Λ`. The chain is `ch ω`; what it may
depend on is stated by hypotheses, not by construction (`proof` is one byte string holding data from
all three rounds):
* `Chain.SamePrefix st pre (mid b₁)`: the leaf keys and the proof's `c_i`, `c_mult`, `iv_pre` are
  `pre`'s (fixed before `chal1`); `(mid b₁).chal1 = b₁`;
* `Chain.SameMid st (mid ω.1) (ch ω)`: additionally `chal1`, `ũ`, `d` and `h_V` are those of
  `mid b₁`, a function of `b₁` alone (fixed before `chal2`); `(ch ω).chal2 = b₂`;
* `hvals`: the chain's constraint evaluator is the relation's system at `b₁` and `l`.
Everything else (`ã`, `z`, `ctr`, the trees `known` L2 applies to, which `chal3` are accepted) may
depend on all of `ω`.

## Results

* `chain_prob`: the generic statement, for any system `cs b₁ l` of length `n`, witness predicate
  `Wit b₁` with `Pr_l[cs holds ∧ ¬Wit] ≤ ε_c`, and any deterministic extraction theorem `hdet` of
  the shape of `*_extract_chain`. Proof: if `chal1` is KOS-good, `hQS` and `hcomb` follow from one
  event about the canonical slope `w* = uCanon + d` of `mid b₁` (`forall_slope_of_uCanon`), which
  is fixed before `chal2` and `l`; then union bound and averaging (`Prob/Uniform.lean`).
* `moussakaIssue_chain_prob`, `moussakaRedeem_chain_prob`, `ratatouilleIssue_chain_prob`,
  `ratatouilleSpend_chain_prob`, `pomfritRedeem_chain_prob`: the five relations, with
  `S = deltaBlocks '' admissible` (the `2¹²⁰` admissible `chal3`) and `hδ` discharged
  (`deltaBlocks_injOn`). The issue relations have no `l`: the samples are `(b₁, b₂)` and the bound
  is `2⁻¹⁵⁰ + ε_QS(n)`.
-/

open Finset ENNReal

namespace VoleMole.Verifier.Bridge.Chain

open VoleMole.Arith VoleMole.Verifier

variable (st : Statement) (T : CrtTables)

/-- `ch` has `pre`'s commitments: the leaf keys and the proof's `c_i`, `c_mult` and `iv_pre` (the
`H₂¹` input apart from the leaf commitments, which the keys determine). -/
def SamePrefix (pre ch : Chain) : Prop :=
  ch.keys = pre.keys ∧ (ch.pf st).corrections = (pre.pf st).corrections ∧
    (ch.pf st).cmult = (pre.pf st).cmult ∧ (ch.pf st).ivPre = (pre.pf st).ivPre

/-- `ch'` has `ch`'s data up to `chal2`: the commitments, `chal1`, `ũ`, `d` and `h_V`. -/
def SameMid (ch ch' : Chain) : Prop :=
  SamePrefix st ch ch' ∧ ch'.chal1 = ch.chal1 ∧ (ch'.pf st).voleCheck = (ch.pf st).voleCheck ∧
    (ch'.pf st).correction = (ch.pf st).correction ∧ ch'.hV = ch.hV

variable {st T} {pre ch ch' : Chain}

lemma SamePrefix.resp_eq (h : SamePrefix st pre ch) : ch.resp st T = pre.resp st T := by
  obtain ⟨hk, hc, hm, hi⟩ := h
  funext Δ
  simp only [resp, iv, ivOf, hk, hc, hm, hi]

lemma SamePrefix.kosQ_eq (h : SamePrefix st pre ch) : ch.kosQ st T = pre.kosQ st T := by
  funext Δ k; simp only [kosQ, h.resp_eq]

lemma SamePrefix.kosD_eq (h : SamePrefix st pre ch) : ch.kosD st T = pre.kosD st T := by
  funext Δ k; simp only [kosD, h.resp_eq]

lemma SamePrefix.Qw_eq (h : SamePrefix st pre ch) : ch.Qw st T = pre.Qw st T := by
  funext j Δ; simp only [Qw, h.resp_eq]

lemma SamePrefix.u_eq (h : SamePrefix st pre ch) : ch.u st = pre.u st := by
  obtain ⟨hk, hc, -, hi⟩ := h
  have hcorr : ch.corr st = pre.corr st := by funext i; simp only [corr, hc]
  funext i j
  simp only [u, iv, ivOf, hcorr, hk, hi]

lemma SamePrefix.trans {ch'' : Chain} (h : SamePrefix st pre ch) (h' : SamePrefix st ch ch'') :
    SamePrefix st pre ch'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.trans h.2.2.2⟩

lemma SameMid.kosCh_eq (h : SameMid st ch ch') : ch'.kosCh = ch.kosCh := by
  simp only [kosCh, h.2.1]

lemma SameMid.kosU_eq (h : SameMid st ch ch') : ch'.kosU st = ch.kosU st := by
  funext j; simp only [kosU, h.2.2.1]

lemma SameMid.dc_eq (h : SameMid st ch ch') : ch'.dc st = ch.dc st := by
  funext j; simp only [dc, corrBit, h.2.2.2.1]

lemma SameMid.AV_eq (h : SameMid st ch ch') (S : Finset Blocks) :
    ch'.AV st T S = ch.AV st T S := by
  ext Δ
  rw [mem_AV, mem_AV, h.kosCh_eq, h.1.kosQ_eq, h.1.kosD_eq, h.kosU_eq, h.2.2.2.2]

lemma SameMid.isSlope_iff (h : SameMid st ch ch') {A : Finset Blocks}
    {u : Fin st.params.witnessBits → GF128} : ch'.IsSlope st T A u ↔ ch.IsSlope st T A u := by
  simp only [IsSlope, h.1.Qw_eq]

lemma dite_choose_congr {α : Type*} [Zero α] {p q : α → Prop} (h : p = q)
    [Decidable (∃ u, p u)] [Decidable (∃ u, q u)] :
    (if h : ∃ u, p u then h.choose else 0) = (if h : ∃ u, q u then h.choose else 0) := by
  subst h; congr

lemma SameMid.uCanon_eq (h : SameMid st ch ch') (S : Finset Blocks) :
    ch'.uCanon st T S = ch.uCanon st T S := by
  have hp : ch'.IsSlope st T (ch'.AV st T S) = ch.IsSlope st T (ch.AV st T S) := by
    funext u; rw [h.AV_eq]; exact propext h.isSlope_iff
  classical
  unfold uCanon
  exact dite_choose_congr hp

end VoleMole.Verifier.Bridge.Chain

namespace VoleMole.Prob

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.EndToEnd
open VoleMole.SeedExtraction

/-- The challenges of `S` on the chain: the accepting set `A` of `*_extract_chain`. -/
noncomputable def onSet (st : Statement) (T : CrtTables) (ch : Chain) (S : Finset Blocks) :
    Finset Blocks := by
  classical
  exact S.filter (ch.OnChain st T)

lemma mem_onSet {st : Statement} {T : CrtTables} {ch : Chain} {S : Finset Blocks} {Δ : Blocks} :
    Δ ∈ onSet st T ch S ↔ Δ ∈ S ∧ ch.OnChain st T Δ := by
  classical
  unfold onSet
  rw [Finset.mem_filter]

variable {Λ : Type} [Fintype Λ] [Nonempty Λ]

/-- **The per-chain theorem, generic form.** For a chain family as in the module doc, a system
`cs b₁ l` of length `n` and a witness predicate `Wit b₁` with `Pr_l[cs holds ∧ ¬Wit] ≤ ε_c`, and a
deterministic theorem `hdet` of the shape of `*_extract_chain` (`hkos`, `hQS`, `hcomb` and the
remaining hypotheses `P` give `Good`), uniform `chal1`, `chal2`, `l` give
`Pr[P ∧ ¬Good] ≤ ε_KOS(|S|) + ε_QS(n) + ε_c`, with `A` the challenges of `S` on the chain. -/
theorem chain_prob {T : CrtTables} (hT : liftInvOk T = true) (st : Statement) (pre : Chain)
    (mid : Bytes 136 → Chain) (ch : Bytes 136 × Bytes 56 × Λ → Chain)
    (hpre : ∀ b, Chain.SamePrefix st pre (mid b)) (hc1 : ∀ b, (mid b).chal1 = b.ba)
    (hmid : ∀ ω, Chain.SameMid st (mid ω.1) (ch ω)) (hc2 : ∀ ω, (ch ω).chal2 = ω.2.1.ba)
    (cs : Bytes 136 → Λ → System GF128) (n : ℕ) (hn : ∀ b l, (cs b l).length = n)
    (Wit : Bytes 136 → (ℕ → GF128) → Prop) {εc : ℝ≥0∞}
    (hεc : ∀ b w, prU Λ (fun l => (cs b l).Holds w ∧ ¬Wit b w) ≤ εc)
    (S : Finset Blocks) (P : Bytes 136 × Bytes 56 × Λ → Finset Blocks → Prop)
    (Good : Bytes 136 × Bytes 56 × Λ → Prop)
    (hdet : ∀ ω (A : Finset Blocks), (∀ Δ ∈ A, (ch ω).OnChain st T Δ) →
      (A : Set Blocks) ⊆ S →
      Seed.KOSGood (ch ω).kosCh (S : Set Blocks) (lift T) ((ch ω).kosQ st T)
        ((ch ω).kosD st T) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, (ch ω).Qw st T j Δ = v + uStar j * lift T Δ) →
        ¬(cs ω.1 ω.2.2).Holds (wStar uStar ((ch ω).dc st)) →
        Seed.zkHash _ (gfOfBytes (ch ω).chal2 0) (gfOfBytes (ch ω).chal2 16)
          (gfOfBytes (ch ω).chal2 32) ⟨W128.word (ch ω).chal2 48, 0⟩
          (valVec (cs ω.1 ω.2.2) (wStar uStar ((ch ω).dc st))) ≠ 0) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, (ch ω).Qw st T j Δ = v + uStar j * lift T Δ) →
        (cs ω.1 ω.2.2).Holds (wStar uStar ((ch ω).dc st)) →
        Wit ω.1 (wStar uStar ((ch ω).dc st))) →
      P ω A → Good ω) :
    prU (Bytes 136 × Bytes 56 × Λ) (fun ω => P ω (onSet st T (ch ω) S) ∧ ¬Good ω) ≤
      epsKOS #S (Chain.kosL st) + ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) + εc := by
  classical
  -- The canonical `w* = uCanon + d`, fixed before `chal2` and `l`.
  let wC : Bytes 136 → ℕ → GF128 := fun b => wStar ((mid b).uCanon st T S) ((mid b).dc st)
  let E1 : Bytes 136 → Prop := fun b => ¬Seed.KOSGood (chOf gfId mem_shortKeys b.ba)
    (S : Set Blocks) (lift T) (pre.kosQ st T) (pre.kosD st T)
  let E2 : Bytes 136 × Bytes 56 × Λ → Prop := fun ω => ¬(cs ω.1 ω.2.2).Holds (wC ω.1) ∧
    Seed.zkHash (cs ω.1 ω.2.2).length (gfOfBytes ω.2.1.ba 0) (gfOfBytes ω.2.1.ba 16)
      (gfOfBytes ω.2.1.ba 32) ⟨W128.word ω.2.1.ba 48, 0⟩ (valVec (cs ω.1 ω.2.2) (wC ω.1)) = 0
  let E3 : Bytes 136 × Bytes 56 × Λ → Prop := fun ω =>
    (cs ω.1 ω.2.2).Holds (wC ω.1) ∧ ¬Wit ω.1 (wC ω.1)
  have hsub : ∀ ω, P ω (onSet st T (ch ω) S) ∧ ¬Good ω → E1 ω.1 ∨ E2 ω ∨ E3 ω := by
    rintro ω ⟨hP, hG⟩
    by_contra hno
    simp only [not_or] at hno
    obtain ⟨hE1, hE2, hE3⟩ := hno
    have hm := hmid ω
    have hpm := hpre ω.1
    have hkM : Seed.KOSGood (mid ω.1).kosCh (S : Set Blocks) (lift T) ((mid ω.1).kosQ st T)
        ((mid ω.1).kosD st T) := by
      rw [hpm.kosQ_eq, hpm.kosD_eq, Chain.kosCh, hc1]
      exact not_not.1 hE1
    have hk : Seed.KOSGood (ch ω).kosCh (S : Set Blocks) (lift T) ((ch ω).kosQ st T)
        ((ch ω).kosD st T) := by
      rw [hm.kosCh_eq, hm.1.kosQ_eq, hm.1.kosD_eq]; exact hkM
    have hA : ∀ Δ ∈ onSet st T (ch ω) S, (ch ω).OnChain st T Δ := fun Δ h => (mem_onSet.1 h).2
    have hAS : onSet st T (ch ω) S ⊆ S := fun Δ h => (mem_onSet.1 h).1
    have hAV : onSet st T (ch ω) S ⊆ (mid ω.1).AV st T S := fun Δ h => by
      rw [← hm.AV_eq]; exact Chain.mem_AV_of_onChain st T _ (hA Δ h) (hAS h)
    -- every slope on `A` is the canonical one
    have hslope : ∀ uStar, 2 ≤ (onSet st T (ch ω) S).card →
        (∀ j, ∃ v, ∀ Δ ∈ onSet st T (ch ω) S, (ch ω).Qw st T j Δ = v + uStar j * lift T Δ) →
        wStar uStar ((ch ω).dc st) = wC ω.1 := fun uStar h2 hs => by
      rw [Chain.slope_eq_uCanon hT hkM hAV h2 (hm.isSlope_iff.1 hs), hm.dc_eq]
    refine hG (hdet ω _ hA (Finset.coe_subset.2 hAS) hk (fun h2 uStar hs hnot => ?_)
      (fun h2 uStar hs hH => ?_) hP)
    · rw [hslope uStar h2 hs] at hnot ⊢
      rw [hc2]
      exact fun hz => hE2 ⟨hnot, hz⟩
    · rw [hslope uStar h2 hs] at hH ⊢
      exact not_not.1 fun hW => hE3 ⟨hH, hW⟩
  calc prU (Bytes 136 × Bytes 56 × Λ) (fun ω => P ω (onSet st T (ch ω) S) ∧ ¬Good ω)
      ≤ prU (Bytes 136 × Bytes 56 × Λ) (fun ω => E1 ω.1 ∨ (E2 ω ∨ E3 ω)) := prU_mono hsub
    _ ≤ prU (Bytes 136 × Bytes 56 × Λ) (fun ω => E1 ω.1) +
          prU (Bytes 136 × Bytes 56 × Λ) (fun ω => E2 ω ∨ E3 ω) := prU_or_le _ _
    _ ≤ epsKOS #S (Chain.kosL st) + (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) + εc) :=
        add_le_add (prU_fst_le _ (prU_kos_bad_le hT S _ _)) (prU_prod_le_right _ fun b =>
          prU_qs_comb_bad_le (cs b) (hn b) (Wit b (wC b)) (wC b) (hεc b (wC b)))
    _ = _ := (add_assoc _ _ _).symm

/-! ## The five relations -/

/-- `S` of the per-chain theorems: the blocks of the admissible `chal3`. -/
noncomputable def chal3Blocks : Finset Blocks := by
  classical
  exact admissible.image deltaBlocks

lemma card_chal3Blocks : #chal3Blocks ≤ 2 ^ 120 := by
  classical
  unfold chal3Blocks
  exact (Finset.card_image_le).trans_eq card_admissible

/-- The hypotheses of `*_extract_chain` left in the event: L2 for the trees outside `known`, and
`hclaim1` (accepted admissible `chal3` decode into `A`). -/
def ChainHyps (A : Finset Blocks) (known : Finset (Fin BAVC.tau)) (acc : Bytes 16 → Prop) : Prop :=
  (∀ i ∉ known, IsFixed (A : Set Blocks) i) ∧ ∀ x ∈ admissible, acc x → deltaBlocks x ∈ A

lemma kosL_le (st : Statement) (hw : st.params.witnessBytes ≤ 847) (hd : st.params.qsDegree ≤ 9) :
    Chain.kosL st ≤ 2 ^ 13 := by
  unfold Chain.kosL Params.correctionRows Params.witnessBits
  split <;> omega

lemma epsKOS_chal3Blocks_le (st : Statement) (hw : st.params.witnessBytes ≤ 847)
    (hd : st.params.qsDegree ≤ 9) : epsKOS #chal3Blocks (Chain.kosL st) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
  (epsKOS_mono card_chal3Blocks).trans (epsKOS_le le_rfl (kosL_le st hw hd))

/-- The sample space without `l`, embedded in the one with `l : Unit`. -/
def dropUnit : Bytes 136 × Bytes 56 × Unit ≃ Bytes 136 × Bytes 56 :=
  (Equiv.refl _).prodCongr (Equiv.prodPUnit _)

lemma prU_no_comb (P : Prop) (hP : ¬P) : prU Unit (fun _ => P) ≤ 0 :=
  (prU_congr fun _ => iff_false_intro hP).trans_le (le_of_eq prU_false)

/-- **Moussaka issuance, one chain, uniform challenges.** -/
theorem moussakaIssue_chain_prob (t ctxIss : ByteArray) (labelRows : Bool) (pre : Chain)
    (mid : Bytes 136 → Chain) (ch : Bytes 136 × Bytes 56 → Chain)
    (hpre : ∀ b, Chain.SamePrefix (moussakaIssue t ctxIss labelRows) pre (mid b))
    (hc1 : ∀ b, (mid b).chal1 = b.ba)
    (hmid : ∀ ω, Chain.SameMid (moussakaIssue t ctxIss labelRows) (mid ω.1) (ch ω))
    (hc2 : ∀ ω, (ch ω).chal2 = ω.2.ba)
    (hvals : ∀ ω x, (ch ω).vals x = (moussakaIssueSys t ctxIss).values x)
    (known : Bytes 136 × Bytes 56 → Finset (Fin BAVC.tau))
    (acc : Bytes 136 × Bytes 56 → Bytes 16 → Prop) [∀ ω, DecidablePred (acc ω)] :
    prU (Bytes 136 × Bytes 56) (fun ω =>
      ChainHyps (onSet (moussakaIssue t ctxIss labelRows) CrtGen.tables (ch ω) chal3Blocks)
        (known ω) (acc ω) ∧
      ¬((∃ i ∈ known ω, moussakaIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)
          (candidate (F := GF128) ((ch ω).u (moussakaIssue t ctxIss labelRows))
            ((ch ω).dc (moussakaIssue t ctxIss labelRows)) i)) ∨
        #{x ∈ admissible | acc ω x} ≤ 9)) ≤
      (2 ^ 150 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) := by
  rw [prU_map_equiv dropUnit]
  refine (chain_prob liftInvOk_tables _ pre mid (ch ∘ dropUnit) hpre hc1 (fun ω => hmid _)
    (fun ω => hc2 _) (fun _ _ => moussakaIssueSys t ctxIss) 4008
    (fun _ _ => Moussaka.issueSystem_length _ _) (fun _ _ => True)
    (fun _ _ => prU_no_comb _ (by simp))
    chal3Blocks (fun ω A => ChainHyps A (known (dropUnit ω)) (acc (dropUnit ω))) _
    fun ω A hA hAS hkos hQS _ hP => moussakaIssue_extract_chain t ctxIss labelRows _
      (hvals _) hA hAS hkos hP.1 hQS admissible deltaBlocks deltaBlocks_injOn _ hP.2).trans ?_
  rw [add_zero]
  gcongr
  exact epsKOS_chal3Blocks_le _ (by norm_num [moussakaIssue]) (by norm_num [moussakaIssue])

/-- **Moussaka redemption, one chain, uniform challenges** (`l` uniform and independent). -/
theorem moussakaRedeem_chain_prob (anchors : List UovPk) (hn : anchors.length ≤ 64)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool) (pre : Chain)
    (mid : Bytes 136 → Chain) (ch : Bytes 136 × Bytes 56 × (Fin Moussaka.M → GF128) → Chain)
    (hpre : ∀ b, Chain.SamePrefix
      (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) pre (mid b))
    (hc1 : ∀ b, (mid b).chal1 = b.ba)
    (hmid : ∀ ω, Chain.SameMid
      (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) (mid ω.1) (ch ω))
    (hc2 : ∀ ω, (ch ω).chal2 = ω.2.1.ba)
    (hvals : ∀ ω x, (ch ω).vals x = (moussakaRedeemSysL anchors nf ctxIss ctxRed ω.2.2).values x)
    (known : Bytes 136 × Bytes 56 × (Fin Moussaka.M → GF128) → Finset (Fin BAVC.tau))
    (acc : Bytes 136 × Bytes 56 × (Fin Moussaka.M → GF128) → Bytes 16 → Prop)
    [∀ ω, DecidablePred (acc ω)] :
    prU (Bytes 136 × Bytes 56 × (Fin Moussaka.M → GF128)) (fun ω =>
      ChainHyps (onSet (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
        CrtGen.tables (ch ω) chal3Blocks) (known ω) (acc ω) ∧
      ¬((∃ i ∈ known ω, moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf)
          (fnOf ctxIss) (fnOf ctxRed) (candidate (F := GF128)
            ((ch ω).u (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows))
            ((ch ω).dc (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)) i)) ∨
        #{x ∈ admissible | acc ω x} ≤ 9)) ≤
      (2 ^ 150 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
        (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  refine (chain_prob liftInvOk_tables _ pre mid ch hpre hc1 hmid hc2
    (fun _ l => moussakaRedeemSysL anchors nf ctxIss ctxRed l) 4409
    (fun _ _ => Moussaka.redeemSystem_length _ _ _ _ _ _ _)
    (fun _ w => moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
      (fnOf ctxRed) w)
    (fun _ w => prU_comb_bad_le _ _ w fun hW =>
      moussaka_redeem_comb_bad_gf128 _ (by simpa using hn) _ _ _ w hW)
    chal3Blocks (fun ω A => ChainHyps A (known ω) (acc ω)) _
    fun ω A hA hAS hkos hQS hcomb hP => moussakaRedeem_extract_chain anchors nf ctxIss ctxRed
      challengeDigest labelRows _ ω.2.2 (hvals ω) hA hAS hkos hP.1 hQS hcomb admissible
      deltaBlocks deltaBlocks_injOn _ hP.2).trans ?_
  gcongr
  exact epsKOS_chal3Blocks_le _ (by norm_num [moussakaRedeem]) (by norm_num [moussakaRedeem])

/-- **Ratatouille issuance, one chain, uniform challenges.** -/
theorem ratatouilleIssue_chain_prob (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray)
    (labelRows : Bool) (pre : Chain) (mid : Bytes 136 → Chain)
    (ch : Bytes 136 × Bytes 56 → Chain)
    (hpre : ∀ b, Chain.SamePrefix (ratatouilleIssue c tInit ctxIss labelRows) pre (mid b))
    (hc1 : ∀ b, (mid b).chal1 = b.ba)
    (hmid : ∀ ω, Chain.SameMid (ratatouilleIssue c tInit ctxIss labelRows) (mid ω.1) (ch ω))
    (hc2 : ∀ ω, (ch ω).chal2 = ω.2.ba)
    (hvals : ∀ ω x, (ch ω).vals x = (ratatouilleIssueSys c tInit ctxIss).values x)
    (known : Bytes 136 × Bytes 56 → Finset (Fin BAVC.tau))
    (acc : Bytes 136 × Bytes 56 → Bytes 16 → Prop) [∀ ω, DecidablePred (acc ω)] :
    prU (Bytes 136 × Bytes 56) (fun ω =>
      ChainHyps (onSet (ratatouilleIssue c tInit ctxIss labelRows) CrtGen.tables (ch ω)
        chal3Blocks) (known ω) (acc ω) ∧
      ¬((∃ i ∈ known ω, ratatouilleIssueWit (fnOf c) tInit (fnOf ctxIss)
          (candidate (F := GF128) ((ch ω).u (ratatouilleIssue c tInit ctxIss labelRows))
            ((ch ω).dc (ratatouilleIssue c tInit ctxIss labelRows)) i)) ∨
        #{x ∈ admissible | acc ω x} ≤ 9)) ≤
      (2 ^ 150 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) := by
  rw [prU_map_equiv dropUnit]
  refine (chain_prob liftInvOk_tables _ pre mid (ch ∘ dropUnit) hpre hc1 (fun ω => hmid _)
    (fun ω => hc2 _) (fun _ _ => ratatouilleIssueSys c tInit ctxIss) 3776
    (fun _ _ => Ratatouille.issueSystem_length _ _ _) (fun _ _ => True)
    (fun _ _ => prU_no_comb _ (by simp))
    chal3Blocks (fun ω A => ChainHyps A (known (dropUnit ω)) (acc (dropUnit ω))) _
    fun ω A hA hAS hkos hQS _ hP => ratatouilleIssue_extract_chain c tInit ctxIss labelRows _
      (hvals _) hA hAS hkos hP.1 hQS admissible deltaBlocks deltaBlocks_injOn _ hP.2).trans ?_
  rw [add_zero]
  gcongr
  exact epsKOS_chal3Blocks_le _ (by norm_num [ratatouilleIssue]) (by norm_num [ratatouilleIssue])

/-- **Ratatouille spend, one chain, uniform challenges** (`l` uniform and independent). -/
theorem ratatouilleSpend_chain_prob (pk : UovPk) (nf : ByteArray) (d : ℕ) (hd : d < 2 ^ 64)
    (cNext ctxIss : ByteArray) (labelRows : Bool) (pre : Chain) (mid : Bytes 136 → Chain)
    (ch : Bytes 136 × Bytes 56 × (Fin Ratatouille.uovM → GF128) → Chain)
    (hpre : ∀ b, Chain.SamePrefix (ratatouilleSpend pk nf d cNext ctxIss labelRows) pre (mid b))
    (hc1 : ∀ b, (mid b).chal1 = b.ba)
    (hmid : ∀ ω, Chain.SameMid (ratatouilleSpend pk nf d cNext ctxIss labelRows) (mid ω.1) (ch ω))
    (hc2 : ∀ ω, (ch ω).chal2 = ω.2.1.ba)
    (hvals : ∀ ω x, (ch ω).vals x = (ratatouilleSpendSysL pk nf d cNext ctxIss ω.2.2).values x)
    (known : Bytes 136 × Bytes 56 × (Fin Ratatouille.uovM → GF128) → Finset (Fin BAVC.tau))
    (acc : Bytes 136 × Bytes 56 × (Fin Ratatouille.uovM → GF128) → Bytes 16 → Prop)
    [∀ ω, DecidablePred (acc ω)] :
    prU (Bytes 136 × Bytes 56 × (Fin Ratatouille.uovM → GF128)) (fun ω =>
      ChainHyps (onSet (ratatouilleSpend pk nf d cNext ctxIss labelRows) CrtGen.tables (ch ω)
        chal3Blocks) (known ω) (acc ω) ∧
      ¬((∃ i ∈ known ω, ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext)
          (fnOf ctxIss) (candidate (F := GF128)
            ((ch ω).u (ratatouilleSpend pk nf d cNext ctxIss labelRows))
            ((ch ω).dc (ratatouilleSpend pk nf d cNext ctxIss labelRows)) i)) ∨
        #{x ∈ admissible | acc ω x} ≤ 9)) ≤
      (2 ^ 150 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
        (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  refine (chain_prob liftInvOk_tables _ pre mid ch hpre hc1 hmid hc2
    (fun _ l => ratatouilleSpendSysL pk nf d cNext ctxIss l) 12282
    (fun _ _ => Ratatouille.spendSystem_length _ _ _ _ _ _ _ _)
    (fun _ w => ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss) w)
    (fun _ w => prU_comb_bad_le _ _ w fun hW =>
      ratatouille_spend_comb_bad_gf128 _ _ hd _ _ w hW)
    chal3Blocks (fun ω A => ChainHyps A (known ω) (acc ω)) _
    fun ω A hA hAS hkos hQS hcomb hP => ratatouilleSpend_extract_chain pk nf d cNext ctxIss
      labelRows _ ω.2.2 (hvals ω) hA hAS hkos hP.1 hQS hcomb admissible deltaBlocks
      deltaBlocks_injOn _ hP.2).trans ?_
  gcongr
  exact epsKOS_chal3Blocks_le _ (by norm_num [ratatouilleSpend]) (by norm_num [ratatouilleSpend])

/-- **PomFRIT redemption, one chain, uniform challenges** (`l` uniform and independent; the
target `h = hash_to_target(pk, sig, chal1, msg)` at the sampled `chal1`). -/
theorem pomfritRedeem_chain_prob (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool)
    (pre : Chain) (mid : Bytes 136 → Chain) (ch : Bytes 136 × Bytes 56 × (Fin 45 → GF128) → Chain)
    (hpre : ∀ b, Chain.SamePrefix (pomfritRedeem pk sig msg labelRows) pre (mid b))
    (hc1 : ∀ b, (mid b).chal1 = b.ba)
    (hmid : ∀ ω, Chain.SameMid (pomfritRedeem pk sig msg labelRows) (mid ω.1) (ch ω))
    (hc2 : ∀ ω, (ch ω).chal2 = ω.2.1.ba)
    (hvals : ∀ ω x, (ch ω).vals x = (pomfritRedeemSysL pk sig msg labelRows ω.1.ba ω.2.2).values x)
    (known : Bytes 136 × Bytes 56 × (Fin 45 → GF128) → Finset (Fin BAVC.tau))
    (acc : Bytes 136 × Bytes 56 × (Fin 45 → GF128) → Bytes 16 → Prop)
    [∀ ω, DecidablePred (acc ω)] :
    prU (Bytes 136 × Bytes 56 × (Fin 45 → GF128)) (fun ω =>
      ChainHyps (onSet (pomfritRedeem pk sig msg labelRows) CrtGen.tables (ch ω) chal3Blocks)
        (known ω) (acc ω) ∧
      ¬((∃ i ∈ known ω, pomfritWit GF256.ofBits 119 45 pk.map
          (fun k => ⟨fnOf (pomfritTarget (pomfritParams labelRows) pk.digest ω.1.ba sig msg) k.val⟩)
          (candidate (F := GF128) ((ch ω).u (pomfritRedeem pk sig msg labelRows))
            ((ch ω).dc (pomfritRedeem pk sig msg labelRows)) i)) ∨
        #{x ∈ admissible | acc ω x} ≤ 2)) ≤
      (2 ^ 150 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
        (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  refine (chain_prob liftInvOk_tables _ pre mid ch hpre hc1 hmid hc2
    (fun b l => pomfritRedeemSysL pk sig msg labelRows b.ba l) 1313
    (fun _ _ => PomFRIT.pomfritRedeemSystem_length _ _ _ _ _ _ _)
    (fun b w => pomfritWit GF256.ofBits 119 45 pk.map
      (fun k => ⟨fnOf (pomfritTarget (pomfritParams labelRows) pk.digest b.ba sig msg) k.val⟩) w)
    (fun _ w => prU_comb_bad_le _ _ w fun hW =>
      pomfrit_comb_bad_gf128 _ _ _ _ w hW)
    chal3Blocks (fun ω A => ChainHyps A (known ω) (acc ω)) _
    fun ω A hA hAS hkos hQS hcomb hP => pomfritRedeem_extract_chain pk sig msg labelRows _
      ω.1.ba ω.2.2 (hvals ω) hA hAS hkos hP.1 hQS hcomb admissible deltaBlocks
      deltaBlocks_injOn _ hP.2).trans ?_
  gcongr
  exact epsKOS_chal3Blocks_le _ (by norm_num [pomfritRedeem, pomfritParams])
    (by norm_num [pomfritRedeem, pomfritParams])

end VoleMole.Prob
