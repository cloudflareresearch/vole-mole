import VoleMole.EndToEnd.Relations
import VoleMole.Arith.MoussakaUnbound

/-!
# End to end for the unbound Moussaka relations (`security/moussaka-unbound.md` §2)

The two theorems of `EndToEnd/Relations.lean` for the unbound relations of PR #63, from the same
extraction core (`extract_or_few_zk`), the degree bound `QS_DEGREE = 9` proved here, and the
arithmetization soundness of `Arith/MoussakaUnbound.lean`:

| relation | theorem | `QS_DEGREE` | relation predicate |
| --- | --- | --- | --- |
| unbound Moussaka issue | `moussaka_unbound_issue_extract` | 9 | `uIssueRel` |
| unbound Moussaka redeem | `moussaka_unbound_redeem_extract` | 9 | `uRedeemRel` |

Each concludes: some known tree's candidate `w^{(i)} = u^{(i)} + d` is a bit vector whose decoding
satisfies the relation, or at most 9 admissible `chall₃` are accepted. The hypotheses are those of
the bound theorems (see `EndToEnd/Relations.lean`); `hcomb` for redemption is discharged with
probability `≥ 1 − 1/|F|` over the combination challenge by `moussaka_unbound_redeem_comb_bad`
(needs `|anchors| ≤ MAX_ANCHORS = 64`).
-/

set_option linter.unusedSectionVars false

namespace VoleMole.EndToEnd

open Finset Polynomial
open VoleMole.Seed VoleMole.SeedExtraction
open VoleMole.Arith (Expr System bitF)
open VoleMole.Arith.UOV (IsEmbedding)

/-! ## Degrees -/

namespace Degree

open VoleMole.Arith VoleMole.Arith.MoussakaUnbound

variable {F K : Type*} [Field F]

/-- Every constraint of unbound Moussaka issue has degree `≤ 9`. -/
theorem moussaka_unbound_issue_deg (t : Fin Moussaka.M → UInt8) (ctxIss : ℕ → UInt8) :
    ∀ e ∈ uIssueSystem (F := F) t ctxIss, e.degree ≤ 9 := by
  intro e he
  have hk := keccak_deg (F := F) (uIssuePub ctxIss) uIssueMap uIssueOffStates 360 (by norm_num)
  simp only [uIssueSystem, List.mem_append] at he
  rcases he with (he | he) | he
  · exact bitSystem_deg _ e he
  · exact hk.1 e he
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    have := hk.2 i i.isLt
    simp only [uIssueKeccak, Fin.getElem_fin] at this ⊢
    rw [degree_add']; simp only [Expr.degree]; omega

theorem degree_uPrefixE : ∀ u, (uPrefixE (F := F) u).degree ≤ 1
  | 0 => le_rfl
  | u + 1 => by
      have := degree_uPrefixE u
      simp only [uPrefixE, degree_add', Expr.degree]; omega

theorem uSelectorSystem_deg (n : ℕ) : ∀ e ∈ uSelectorSystem (F := F) n, e.degree ≤ 9 := by
  intro e he
  simp only [uSelectorSystem, List.mem_append, List.mem_map, List.mem_singleton] at he
  rcases he with (⟨u, -, rfl⟩ | ⟨u, -, rfl⟩) | rfl
  · split_ifs <;> simp [degree_bitConstraint_wit, Expr.degree]
  · have := degree_uPrefixE (F := F) u
    simp only [Expr.degree]; omega
  · have := degree_uPrefixE (F := F) 63
    simp only [Expr.degree]; omega

theorem degree_uLqExpr (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (anchors : List (ℕ → K))
    (l : Fin Moussaka.M → F) : (uLqExpr β toBits anchors l).degree ≤ 3 := by
  unfold uLqExpr
  refine degree_foldl_add _ (fun u => ?_) _ _ (by simp [Expr.degree])
  have := UOV.degree_evalCombinedPublicMap β toBits Moussaka.N Moussaka.M anchors[u]
    (fun i => byteLoad β (uRedeemOffS + i)) l (fun i => (UOV.degree_byteLoad β _).le)
  rw [degree_mul']; simp only [Expr.degree]; omega

/-- Every constraint of unbound Moussaka redeem has degree `≤ 9`. -/
theorem moussaka_unbound_redeem_deg [Add K] [Mul K] [Zero K] (β : Fin 8 → F)
    (toBits : K → Fin 8 → Bool) (anchors : List (ℕ → K)) (nf ctxIss ctxRed : ℕ → UInt8)
    (l : Fin Moussaka.M → F) :
    ∀ e ∈ uRedeemSystem β toBits anchors nf ctxIss ctxRed l, e.degree ≤ 9 := by
  intro e he
  have hc := keccak_deg (F := F) (uRedeemComPub ctxIss) uRedeemComMap uRedeemOffComStates 800 le_rfl
  have hd := keccak_deg (F := F) (uRedeemDerivePub ctxRed) uRedeemDeriveMap uRedeemOffDeriveStates
    192 (by norm_num)
  rw [uRedeemSystem] at he
  rcases List.mem_append.1 he with he | he
  rotate_left
  · rw [List.mem_singleton.1 he]
    have h1 : (Moussaka.loutExpr β l (uRedeemComKeccak (F := F) ctxIss).2).degree ≤ 8 :=
      degree_linComb l _ fun k => degree_qsByte β _ _ _ fun i hi => hc.2 i hi
    have h2 := degree_uLqExpr β toBits anchors l
    simp only [uRedeemOutput, degree_add']; omega
  rcases List.mem_append.1 he with he | he
  rcases List.mem_append.1 he with he | he
  rcases List.mem_append.1 he with he | he
  rcases List.mem_append.1 he with he | he
  · exact bitSystem_deg _ e he
  · exact uSelectorSystem_deg _ e he
  · exact hc.1 e he
  · exact hd.1 e he
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    have := hd.2 i i.isLt
    simp only [uRedeemDeriveKeccak, Fin.getElem_fin] at this ⊢
    rw [degree_add']; simp only [Expr.degree]; omega

end Degree

variable {ι F K : Type*} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2] [DecidableEq F]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)]
variable [Add K] [Mul K] [Zero K]

/-! ## Unbound Moussaka issue -/

section UnboundIssue

open VoleMole.Arith.MoussakaUnbound
open VoleMole.Arith.Moussaka (M)

/-- Committed values that encode an unbound issue witness: bits on all `8·232` rows whose
`(nf_key, r)` satisfy `t = UCom(nf_key, ctx_iss, r)`. -/
def moussakaUnboundIssueWit (t : Fin M → UInt8) (ctxIss : ℕ → UInt8) (w : ℕ → F) : Prop :=
  ∃ wb : ℕ → Bool, (∀ i < uIssueWitnessBits, w i = bitF (wb i)) ∧
    uIssueRel t ctxIss (uIssueK wb) (uIssueR wb)

/-- **Unbound Moussaka issue, end to end (deterministic).** No combination challenge: `hcomb` is
`uIssue_sound`. -/
theorem moussaka_unbound_issue_extract {Ch : Type*} (t : Fin M → UInt8) (ctxIss : ℕ → UInt8)
    {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {known : Finset ι}
    {u : ι → Fin uIssueWitnessBits → Bool} {Q : Fin uIssueWitnessBits → (∀ i, B i) → F}
    {uStar : Fin uIssueWitnessBits → F}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar) (dc : Fin uIssueWitnessBits → Bool)
    (r₀ r₁ s t' : F) (R : F[X]) (hR : R.natDegree ≤ 8)
    (hacc : ∀ Δ ∈ A, qsCheck (uIssueSystem (F := F) t ctxIss) 9
      (zkCoeff _ r₀ r₁ s t') (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬(uIssueSystem (F := F) t ctxIss).Holds (wStar uStar dc) →
      zkHash _ r₀ r₁ s t' (valVec (uIssueSystem t ctxIss) (wStar uStar dc)) ≠ 0)
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, moussakaUnboundIssueWit t ctxIss (candidate (F := F) u dc i)) ∨
      #{x ∈ Z | acc x} ≤ 9 :=
  (extract_or_few_zk (d := 9) (by norm_num) hK dc _ (Degree.moussaka_unbound_issue_deg t ctxIss)
    (moussakaUnboundIssueWit t ctxIss)
    (fun w hw => bits_of_exists_bitF w hw) r₀ r₁ s t' R hR hacc hQS
    (fun hw => ⟨_, uIssue_sound t ctxIss _ hw⟩) Z δ hδ acc hclaim1).imp_right
    fun h => h.trans (by norm_num)

end UnboundIssue

/-! ## Unbound Moussaka redeem -/

section UnboundRedeem

open VoleMole.Arith.MoussakaUnbound
open VoleMole.Arith.Moussaka (M)

/-- Committed values that encode an unbound redeem witness: bits on all `8·559` rows, a selector
`e_{u₀}`, and `(nf_key, r, σ)` with `P_{anchors[u₀]}(σ) = UCom(nf_key, ctx_iss, r)` and
`nf = Derive(nf_key, ctx_red)`. -/
def moussakaUnboundRedeemWit (ofByte : (Fin 8 → Bool) → K) (anchors : List (ℕ → K))
    (nf ctxIss ctxRed : ℕ → UInt8) (w : ℕ → F) : Prop :=
  ∃ wb : ℕ → Bool, (∀ i < uRedeemWitnessBits, w i = bitF (wb i)) ∧
    ∃ u₀, (∀ u < 64, wb (uSelBit u) = decide (u = u₀)) ∧
      uRedeemRel ofByte anchors nf ctxIss ctxRed (uRedeemK wb) (uRedeemR wb) (uRedeemS ofByte wb) u₀

theorem moussakaUnboundRedeemWit_bits {ofByte : (Fin 8 → Bool) → K} {anchors : List (ℕ → K)}
    {nf ctxIss ctxRed : ℕ → UInt8} (w : ℕ → F)
    (hw : moussakaUnboundRedeemWit ofByte anchors nf ctxIss ctxRed w) :
    ∀ j < uRedeemWitnessBits, w j = 0 ∨ w j = 1 := by
  obtain ⟨wb, hb, -⟩ := hw
  exact bits_of_exists_bitF (P := fun _ => True) w ⟨wb, hb, trivial⟩

open Classical in
/-- `hcomb` fails rarely (`uRedeem_sound_card`; needs `|anchors| ≤ MAX_ANCHORS = 64`). -/
theorem moussaka_unbound_redeem_comb_bad [Fintype F] {β : Fin 8 → F} {toBits : K → Fin 8 → Bool}
    {ofByte : (Fin 8 → Bool) → K} (hι : IsEmbedding β toBits ofByte) (hβ : β 0 = 1)
    (anchors : List (ℕ → K)) (hn : anchors.length ≤ 64) (nf ctxIss ctxRed : ℕ → UInt8)
    (w : ℕ → F) (hw : ¬moussakaUnboundRedeemWit ofByte anchors nf ctxIss ctxRed w) :
    #{l : Fin M → F | (uRedeemSystem β toBits anchors nf ctxIss ctxRed l).Holds w} *
      Fintype.card F ≤ Fintype.card (Fin M → F) := by
  exact (uRedeem_sound_card hι hβ anchors hn nf ctxIss ctxRed w).resolve_left hw

/-- **Unbound Moussaka redeem, end to end (deterministic).** -/
theorem moussaka_unbound_redeem_extract {Ch : Type*} (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (ofByte : (Fin 8 → Bool) → K) (anchors : List (ℕ → K)) (nf ctxIss ctxRed : ℕ → UInt8)
    (l : Fin M → F)
    {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {known : Finset ι}
    {u : ι → Fin uRedeemWitnessBits → Bool} {Q : Fin uRedeemWitnessBits → (∀ i, B i) → F}
    {uStar : Fin uRedeemWitnessBits → F}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar) (dc : Fin uRedeemWitnessBits → Bool)
    (r₀ r₁ s t : F) (R : F[X]) (hR : R.natDegree ≤ 8)
    (hacc : ∀ Δ ∈ A, qsCheck (uRedeemSystem β toBits anchors nf ctxIss ctxRed l) 9
      (zkCoeff _ r₀ r₁ s t) (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬(uRedeemSystem β toBits anchors nf ctxIss ctxRed l).Holds (wStar uStar dc) →
      zkHash _ r₀ r₁ s t
        (valVec (uRedeemSystem β toBits anchors nf ctxIss ctxRed l) (wStar uStar dc)) ≠ 0)
    (hcomb : (uRedeemSystem β toBits anchors nf ctxIss ctxRed l).Holds (wStar uStar dc) →
      moussakaUnboundRedeemWit ofByte anchors nf ctxIss ctxRed (wStar uStar dc))
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known,
        moussakaUnboundRedeemWit ofByte anchors nf ctxIss ctxRed (candidate (F := F) u dc i)) ∨
      #{x ∈ Z | acc x} ≤ 9 :=
  (extract_or_few_zk (d := 9) (by norm_num) hK dc _
    (Degree.moussaka_unbound_redeem_deg β toBits anchors nf ctxIss ctxRed l)
    (moussakaUnboundRedeemWit ofByte anchors nf ctxIss ctxRed)
    (fun w hw => moussakaUnboundRedeemWit_bits w hw)
    r₀ r₁ s t R hR hacc hQS hcomb Z δ hδ acc hclaim1).imp_right
    fun h => h.trans (by norm_num)

end UnboundRedeem

end VoleMole.EndToEnd
