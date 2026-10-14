import VoleMole.EndToEnd.Core
import VoleMole.EndToEnd.Degree

/-!
# End to end, per relation: extraction yields a witness of the actual relation

One deterministic theorem per relation, joining the extraction core (L5–L6), the QuickSilver
argument for the relation's real constraint system (L4, via `extract_or_few_zk`) and the
arithmetization soundness (L7, `Arith/*`):

| relation | theorem | `QS_DEGREE` | relation predicate |
| --- | --- | --- | --- |
| PomFRIT redeem | `pomfrit_extract` | 2 | `PomFRIT.pomfritRel` |
| Moussaka issue | `moussaka_issue_extract` | 9 | `Moussaka.issueRel` |
| Moussaka redeem | `moussaka_redeem_extract` | 9 | `Moussaka.redeemRel` |
| Ratatouille issue | `ratatouille_issue_extract` | 9 | `Ratatouille.IssueRel` |
| Ratatouille spend | `ratatouille_spend_extract` | 9 | `Ratatouille.SpendRelOf` |

Each concludes: **some known tree's candidate `w^{(i)} = u^{(i)} + d` is a bit vector whose
decoding satisfies the relation, or at most `max(d, 1)` admissible `chall₃` are accepted.**

## Hypotheses, and what discharges them

Common to all five (one chain = an `H₂²` input `y` and the `H₂³` queries extending it):
* `hK : Claim4Hyp e A known u Q u*`. `lift_inj` (W_crt injective, a [test]); `tree_form` (L1
  committed data + L5's per-tree form); `unknown_fixed` (L2: a tree with a dead leaf has a fixed
  block); `consistent` (L3, `claim4Hyp_of_kosGood` on a good `chall₁`; bad with prob. `ε_KOS` per
  `H₂¹` query). `u*` is L4 §5's canonical slope, from L3 on `A_V ⊇ A`, so it is fixed before
  `chall₂`.
* `dc`: the correction `d` in `y` (a bit vector by construction).
* `hacc`: on `A`, the verifier's QuickSilver check value vanishes, with `R` the mask/`ã`/check
  remainder (L4 Prop. 1(1); `R = maskPoly d a b ã z` by L3 on the mask rows, and
  `hR` is `maskPoly_natDegree_le`). Any C++ circuit with the same top coefficient and degree also
  fits: the difference is absorbed into `R`.
* `hQS`: if the chain's system fails at `w*`, `zkHash(chall₂; f(w*)) ≠ 0`. Bad with probability
  `≤ ε_QS(n)` over `chall₂` for each fixed `l` (`card_qs_bad_le`, L4 Prop. 2), `w*` fixed before
  `chall₂` (L4 §5, (H-stmt)).
* `hδ`, `hclaim1`: admissible `chall₃` decode injectively, and accepted ones lie in `A` (L1).

Relations with a combined slot (PomFRIT redeem, Moussaka redeem, Ratatouille spend) also take
* `hcomb`: if the chain's system (built with the chain's `l = H_comb(chall₂ ‖ dst)`) holds at
  `w*`, then `w*` is a witness. Bad with probability `≤ 1/|F|` over `l`, `w*` fixed before
  `chall₂`: `*_comb_bad` (= the relation's `*_sound_card`), plus `q_c·2^{−448}` for `l` not being
  fresh (L4 §6, (H-DS)).

For the issue relations `hcomb` is proved (`*_sound`), since their systems ignore `chall₂`.
Total per `H₂²` query: `ε_QS(n) + 1/|F|` (L4 Prop. 3), or `ε_QS(n)` for the issue relations.

`EndToEnd/Concrete.lean` instantiates all five at the concrete GF(2¹²⁸) (`F := GF128`,
`β := beta`, `K := GF256`), with `hcomb`'s failure bound `2⁻¹²⁸` proved (`*_comb_bad_gf128`);
`Verifier/Bridge/Relations.lean` proves `hacc` at the `Δ` of any transcript the executable verifier
accepts.

The QuickSilver degree bound `hdeg` is proved (`degree_pomfritRedeemSystem`, `EndToEnd/Degree`).
The witness rows are exactly the relation's witness bits (`J = Fin ℓ`, `ℓ = WITNESS_BITS`), each
of which carries a bit constraint (or, for Moussaka's unused selector bits, `b_u = 0`), which is
what L5's `hbits` needs.
-/

set_option linter.unusedSectionVars false

namespace VoleMole.EndToEnd

open Finset Polynomial
open VoleMole.Seed VoleMole.SeedExtraction
open VoleMole.Arith (Expr System bitF)
open VoleMole.Arith.UOV (IsEmbedding)

variable {ι F K : Type*} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2] [DecidableEq F]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)]
variable [Add K] [Mul K] [Zero K]

/-! ## PomFRIT redeem -/

section PomFRIT

open VoleMole.Arith.PomFRIT

/-- Committed values that encode a PomFRIT redeem witness: bits `wb` on all `8(M+N)` rows whose
bytes `(ρ, σ)` satisfy `P(σ) = h + ρ`. -/
def pomfritWit (ofByte : (Fin 8 → Bool) → K) (N M : ℕ) (pk : ℕ → K) (h : Fin M → K)
    (w : ℕ → F) : Prop :=
  ∃ wb : ℕ → Bool, (∀ i < witnessBits N M, w i = bitF (wb i)) ∧
    pomfritRel N M pk h (decodeR ofByte wb M) (decodeS ofByte wb M)

open Classical in
/-- `hcomb` fails rarely: for `w*` fixed before `l`, if `w*` is not a witness, at most a `1/|F|`
fraction of the `l` make the system hold (`pomfrit_sound_card`). -/
theorem pomfrit_comb_bad [Fintype F] {β : Fin 8 → F} {toBits : K → Fin 8 → Bool}
    {ofByte : (Fin 8 → Bool) → K} (hι : IsEmbedding β toBits ofByte) (N M : ℕ) (pk : ℕ → K)
    (h : Fin M → K) (w : ℕ → F) (hw : ¬pomfritWit ofByte N M pk h w) :
    #{l : Fin M → F | (pomfritRedeemSystem β toBits N M pk h l).Holds w} * Fintype.card F ≤
      Fintype.card (Fin M → F) := by
  exact (pomfrit_sound_card hι N M pk h w).resolve_left hw

/-- **PomFRIT redeem, end to end (deterministic).** See the module docstring for the hypotheses.
Either a known tree's candidate encodes `(ρ, σ)` with `P_pk(σ) = h + ρ`, or at most 2 admissible
`chall₃` are accepted. -/
theorem pomfrit_extract {Ch : Type*} (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (ofByte : (Fin 8 → Bool) → K) (N M : ℕ) (pk : ℕ → K) (h : Fin M → K) (l : Fin M → F)
    {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {known : Finset ι}
    {u : ι → Fin (witnessBits N M) → Bool} {Q : Fin (witnessBits N M) → (∀ i, B i) → F}
    {uStar : Fin (witnessBits N M) → F}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar) (dc : Fin (witnessBits N M) → Bool)
    (r₀ r₁ s t : F) (R : F[X]) (hR : R.natDegree ≤ 1)
    (hacc : ∀ Δ ∈ A, qsCheck (pomfritRedeemSystem β toBits N M pk h l) 2
      (zkCoeff _ r₀ r₁ s t) (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬(pomfritRedeemSystem β toBits N M pk h l).Holds (wStar uStar dc) →
      zkHash _ r₀ r₁ s t (valVec (pomfritRedeemSystem β toBits N M pk h l) (wStar uStar dc)) ≠ 0)
    (hcomb : (pomfritRedeemSystem β toBits N M pk h l).Holds (wStar uStar dc) →
      pomfritWit ofByte N M pk h (wStar uStar dc))
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, pomfritWit ofByte N M pk h (candidate (F := F) u dc i)) ∨ #{x ∈ Z | acc x} ≤ 2 :=
  (extract_or_few_zk (d := 2) (by norm_num) hK dc _ (degree_pomfritRedeemSystem β toBits N M pk h l)
    (pomfritWit ofByte N M pk h)
    (fun w hw => bits_of_exists_bitF w hw) r₀ r₁ s t R hR hacc hQS hcomb Z δ hδ acc hclaim1).imp_right
    fun h => h.trans (by norm_num)

end PomFRIT

/-! ## Moussaka issue -/

section MoussakaIssue

open VoleMole.Arith.Moussaka

/-- Committed values that encode a Moussaka issue witness: bits on all 2048 rows whose
`(nf, ctx_red, r)` satisfy `t = Com(nf, ctx_iss, ctx_red, r)`. -/
def moussakaIssueWit (t : Fin M → UInt8) (ctxIss : ℕ → UInt8) (w : ℕ → F) : Prop :=
  ∃ wb : ℕ → Bool, (∀ i < issueWitnessBits, w i = bitF (wb i)) ∧
    issueRel t ctxIss (issueNf wb) (issueCtxRed wb) (issueR wb)

/-- **Moussaka issue, end to end (deterministic).** No combination challenge: `hcomb` is
`issue_sound`. -/
theorem moussaka_issue_extract {Ch : Type*} (t : Fin M → UInt8) (ctxIss : ℕ → UInt8)
    {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {known : Finset ι}
    {u : ι → Fin issueWitnessBits → Bool} {Q : Fin issueWitnessBits → (∀ i, B i) → F}
    {uStar : Fin issueWitnessBits → F}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar) (dc : Fin issueWitnessBits → Bool)
    (r₀ r₁ s t' : F) (R : F[X]) (hR : R.natDegree ≤ 8)
    (hacc : ∀ Δ ∈ A, qsCheck (issueSystem (F := F) t ctxIss) 9
      (zkCoeff _ r₀ r₁ s t') (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬(issueSystem (F := F) t ctxIss).Holds (wStar uStar dc) →
      zkHash _ r₀ r₁ s t' (valVec (issueSystem t ctxIss) (wStar uStar dc)) ≠ 0)
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, moussakaIssueWit t ctxIss (candidate (F := F) u dc i)) ∨ #{x ∈ Z | acc x} ≤ 9 :=
  (extract_or_few_zk (d := 9) (by norm_num) hK dc _ (Degree.moussaka_issue_deg t ctxIss)
    (moussakaIssueWit t ctxIss)
    (fun w hw => bits_of_exists_bitF w hw) r₀ r₁ s t' R hR hacc hQS
    (fun hw => ⟨_, issue_sound t ctxIss _ hw⟩) Z δ hδ acc hclaim1).imp_right
    fun h => h.trans (by norm_num)

end MoussakaIssue

/-! ## Moussaka redeem -/

section MoussakaRedeem

open VoleMole.Arith.Moussaka

/-- Committed values that encode a Moussaka redeem witness: bits on all `8·343` rows, a selector
`e_{u₀}`, and `(r, σ)` with `P_{anchors[u₀]}(σ) = Com(nf, ctx_iss, ctx_red, r)`. -/
def moussakaRedeemWit (ofByte : (Fin 8 → Bool) → K) (anchors : List (ℕ → K))
    (nf ctxIss ctxRed : ℕ → UInt8) (w : ℕ → F) : Prop :=
  ∃ wb : ℕ → Bool, (∀ i < redeemWitnessBits, w i = bitF (wb i)) ∧
    ∃ u₀, (∀ u < 64, wb (selBit u) = decide (u = u₀)) ∧
      redeemRel ofByte anchors nf ctxIss ctxRed (redeemR wb) (redeemS ofByte wb) u₀

theorem moussakaRedeemWit_bits {ofByte : (Fin 8 → Bool) → K} {anchors : List (ℕ → K)}
    {nf ctxIss ctxRed : ℕ → UInt8} (w : ℕ → F)
    (hw : moussakaRedeemWit ofByte anchors nf ctxIss ctxRed w) :
    ∀ j < redeemWitnessBits, w j = 0 ∨ w j = 1 := by
  obtain ⟨wb, hb, -⟩ := hw
  exact bits_of_exists_bitF (P := fun _ => True) w ⟨wb, hb, trivial⟩

open Classical in
/-- `hcomb` fails rarely (`redeem_sound_card`; needs `|anchors| ≤ MAX_ANCHORS = 64`). -/
theorem moussaka_redeem_comb_bad [Fintype F] {β : Fin 8 → F} {toBits : K → Fin 8 → Bool}
    {ofByte : (Fin 8 → Bool) → K} (hι : IsEmbedding β toBits ofByte) (hβ : β 0 = 1)
    (anchors : List (ℕ → K)) (hn : anchors.length ≤ 64) (nf ctxIss ctxRed : ℕ → UInt8)
    (w : ℕ → F) (hw : ¬moussakaRedeemWit ofByte anchors nf ctxIss ctxRed w) :
    #{l : Fin M → F | (redeemSystem β toBits anchors nf ctxIss ctxRed l).Holds w} *
      Fintype.card F ≤ Fintype.card (Fin M → F) := by
  exact (redeem_sound_card hι hβ anchors hn nf ctxIss ctxRed w).resolve_left hw

/-- **Moussaka redeem, end to end (deterministic).** -/
theorem moussaka_redeem_extract {Ch : Type*} (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (ofByte : (Fin 8 → Bool) → K) (anchors : List (ℕ → K)) (nf ctxIss ctxRed : ℕ → UInt8)
    (l : Fin M → F)
    {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {known : Finset ι}
    {u : ι → Fin redeemWitnessBits → Bool} {Q : Fin redeemWitnessBits → (∀ i, B i) → F}
    {uStar : Fin redeemWitnessBits → F}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar) (dc : Fin redeemWitnessBits → Bool)
    (r₀ r₁ s t : F) (R : F[X]) (hR : R.natDegree ≤ 8)
    (hacc : ∀ Δ ∈ A, qsCheck (redeemSystem β toBits anchors nf ctxIss ctxRed l) 9
      (zkCoeff _ r₀ r₁ s t) (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬(redeemSystem β toBits anchors nf ctxIss ctxRed l).Holds (wStar uStar dc) →
      zkHash _ r₀ r₁ s t
        (valVec (redeemSystem β toBits anchors nf ctxIss ctxRed l) (wStar uStar dc)) ≠ 0)
    (hcomb : (redeemSystem β toBits anchors nf ctxIss ctxRed l).Holds (wStar uStar dc) →
      moussakaRedeemWit ofByte anchors nf ctxIss ctxRed (wStar uStar dc))
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, moussakaRedeemWit ofByte anchors nf ctxIss ctxRed (candidate (F := F) u dc i)) ∨
      #{x ∈ Z | acc x} ≤ 9 :=
  (extract_or_few_zk (d := 9) (by norm_num) hK dc _
    (Degree.moussaka_redeem_deg β toBits anchors nf ctxIss ctxRed l)
    (moussakaRedeemWit ofByte anchors nf ctxIss ctxRed)
    (fun w hw => moussakaRedeemWit_bits w hw)
    r₀ r₁ s t R hR hacc hQS hcomb Z δ hδ acc hclaim1).imp_right
    fun h => h.trans (by norm_num)

end MoussakaRedeem

/-! ## Ratatouille issue -/

section RatatouilleIssue

open VoleMole.Arith.Ratatouille

/-- Committed values that encode a Ratatouille issue witness: bits on all `8·240` rows whose
`(nf, r)` satisfy `c = Com(nf, ctx, T_init, r)`. -/
def ratatouilleIssueWit (c : ℕ → UInt8) (tInit : ℕ) (ctx : ℕ → UInt8) (w : ℕ → F) : Prop :=
  ∃ wb : ℕ → Bool, (∀ i < 8 * issueWitnessBytes, w i = bitF (wb i)) ∧
    IssueRel c tInit ctx (bytesAt wb 16) (bytesAt wb 0)

/-- **Ratatouille issue, end to end (deterministic).** No combination challenge: `hcomb` is
`issue_sound`. -/
theorem ratatouille_issue_extract {Ch : Type*} (c : ℕ → UInt8) (tInit : ℕ) (ctx : ℕ → UInt8)
    {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {known : Finset ι}
    {u : ι → Fin (8 * issueWitnessBytes) → Bool}
    {Q : Fin (8 * issueWitnessBytes) → (∀ i, B i) → F} {uStar : Fin (8 * issueWitnessBytes) → F}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar)
    (dc : Fin (8 * issueWitnessBytes) → Bool)
    (r₀ r₁ s t : F) (R : F[X]) (hR : R.natDegree ≤ 8)
    (hacc : ∀ Δ ∈ A, qsCheck (issueSystem (F := F) c tInit ctx) 9
      (zkCoeff _ r₀ r₁ s t) (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬(issueSystem (F := F) c tInit ctx).Holds (wStar uStar dc) →
      zkHash _ r₀ r₁ s t (valVec (issueSystem c tInit ctx) (wStar uStar dc)) ≠ 0)
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, ratatouilleIssueWit c tInit ctx (candidate (F := F) u dc i)) ∨ #{x ∈ Z | acc x} ≤ 9 :=
  (extract_or_few_zk (d := 9) (by norm_num) hK dc _ (Degree.ratatouille_issue_deg c tInit ctx)
    (ratatouilleIssueWit c tInit ctx)
    (fun w hw => bits_of_exists_bitF w hw) r₀ r₁ s t R hR hacc hQS
    (fun hw => ⟨_, issue_sound c tInit ctx _ hw⟩) Z δ hδ acc hclaim1).imp_right
    fun h => h.trans (by norm_num)

end RatatouilleIssue

/-! ## Ratatouille spend -/

section RatatouilleSpend

open VoleMole.Arith.Ratatouille

/-- Committed values that encode a Ratatouille spend witness: bits on all `8·847` rows whose
decoding satisfies `SpendRel` (V1–V4). -/
def ratatouilleSpendWit (ofByte : (Fin 8 → Bool) → K) (pk : ℕ → K) (nf : ℕ → UInt8) (d : ℕ)
    (cNext ctx : ℕ → UInt8) (w : ℕ → F) : Prop :=
  ∃ wb : ℕ → Bool, (∀ i < 8 * spendWitnessBytes, w i = bitF (wb i)) ∧
    SpendRelOf ofByte pk nf d cNext ctx wb

open Classical in
/-- `hcomb` fails rarely (`spend_sound_card`; needs `d < 2⁶⁴`). -/
theorem ratatouille_spend_comb_bad [Fintype F] {β : Fin 8 → F} {toBits : K → Fin 8 → Bool}
    {ofByte : (Fin 8 → Bool) → K} (hι : IsEmbedding β toBits ofByte) (hβ : β 0 = 1)
    (pk : ℕ → K) (nf : ℕ → UInt8) {d : ℕ} (hd : d < 2 ^ 64) (cNext ctx : ℕ → UInt8) (w : ℕ → F)
    (hw : ¬ratatouilleSpendWit ofByte pk nf d cNext ctx w) :
    #{l : Fin uovM → F | (spendSystem β toBits pk nf d cNext ctx l).Holds w} *
      Fintype.card F ≤ Fintype.card (Fin uovM → F) :=
  (spend_sound_card hι hβ pk nf hd cNext ctx w).resolve_left hw

/-- **Ratatouille spend, end to end (deterministic).** -/
theorem ratatouille_spend_extract {Ch : Type*} (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (ofByte : (Fin 8 → Bool) → K) (pk : ℕ → K) (nf : ℕ → UInt8) (d : ℕ) (cNext ctx : ℕ → UInt8)
    (l : Fin uovM → F)
    {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {known : Finset ι}
    {u : ι → Fin (8 * spendWitnessBytes) → Bool}
    {Q : Fin (8 * spendWitnessBytes) → (∀ i, B i) → F} {uStar : Fin (8 * spendWitnessBytes) → F}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar)
    (dc : Fin (8 * spendWitnessBytes) → Bool)
    (r₀ r₁ s t : F) (R : F[X]) (hR : R.natDegree ≤ 8)
    (hacc : ∀ Δ ∈ A, qsCheck (spendSystem β toBits pk nf d cNext ctx l) 9
      (zkCoeff _ r₀ r₁ s t) (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬(spendSystem β toBits pk nf d cNext ctx l).Holds (wStar uStar dc) →
      zkHash _ r₀ r₁ s t (valVec (spendSystem β toBits pk nf d cNext ctx l) (wStar uStar dc)) ≠ 0)
    (hcomb : (spendSystem β toBits pk nf d cNext ctx l).Holds (wStar uStar dc) →
      ratatouilleSpendWit ofByte pk nf d cNext ctx (wStar uStar dc))
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, ratatouilleSpendWit ofByte pk nf d cNext ctx (candidate (F := F) u dc i)) ∨
      #{x ∈ Z | acc x} ≤ 9 :=
  (extract_or_few_zk (d := 9) (by norm_num) hK dc _
    (Degree.ratatouille_spend_deg β toBits pk nf d cNext ctx l)
    (ratatouilleSpendWit ofByte pk nf d cNext ctx)
    (fun w hw => bits_of_exists_bitF w hw) r₀ r₁ s t R hR hacc hQS hcomb Z δ hδ acc hclaim1).imp_right
    fun h => h.trans (by norm_num)

end RatatouilleSpend

end VoleMole.EndToEnd
