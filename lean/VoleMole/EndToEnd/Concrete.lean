import VoleMole.EndToEnd.Relations
import VoleMole.Arith.ConcreteField

/-!
# End to end, per relation, at the concrete GF(2¹²⁸)

`EndToEnd/Relations.lean` at `F := GF128` (`Arith/GFField.lean`'s `Field` and `CharP` instances),
`β := beta`, `K := GF256`, `toBits := GF256.toBits`, `ofByte := GF256.ofBits`, i.e. at the systems
the executable verifier evaluates (`Verifier/Bridge/Relations.lean`):

* `pomfritWit_gf256_iff`, `moussakaRedeemWit_gf256_iff`, `ratatouilleSpendWit_gf256_iff`: the
  witness predicates on the concrete GF(256) are the byte checks of `Arith/Concrete.lean`;
* `*_comb_bad_gf128`: the `hcomb` failure counts with `IsEmbedding beta`, `beta 0 = 1` and `|F|`
  discharged: at most a `2⁻¹²⁸` fraction of the `l`;
* `*_extract_gf128`: the five extraction theorems at these parameters. Their remaining hypotheses
  are those of `EndToEnd/Relations.lean` (`hK`, `hacc` on all of `A`, `hQS`, `hcomb`, `hδ`,
  `hclaim1`): the Δ-structure and random-oracle steps, none of which is about the field or the
  arithmetization. `Verifier/Bridge/Relations.lean` gives `hacc` at the `Δ` of an accepting
  transcript of the executable verifier.
-/

set_option linter.unusedSectionVars false

namespace VoleMole.EndToEnd

open Finset Polynomial
open VoleMole.Seed VoleMole.SeedExtraction
open VoleMole.Arith (Expr System bitF GF128 GF256 beta card_fun_gf128)
open VoleMole.Arith.UOV (publicMap)
open VoleMole.Arith.Keccak (keccakP800)

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2] [DecidableEq F]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)]

/-! ## PomFRIT redeem -/

section PomFRIT

open VoleMole.Arith.PomFRIT

theorem pomfritWit_gf256_iff (N M : ℕ) (pk : ℕ → GF256) (h : Fin M → GF256) (w : ℕ → F) :
    pomfritWit GF256.ofBits N M pk h w ↔
      ∃ wb : ℕ → Bool, (∀ i < witnessBits N M, w i = bitF (wb i)) ∧
        ∀ k : Fin M, (publicMap N M pk (fun i => ⟨Arith.Keccak.witByte wb (witOffS M + i)⟩) k).val =
          (h k).val ^^^ Arith.Keccak.witByte wb (witOffR + k) :=
  exists_congr fun wb => and_congr_right fun _ => pomfritRel_gf256_iff N M pk h wb

open Classical in
theorem pomfrit_comb_bad_gf128 (N M : ℕ) (pk : ℕ → GF256) (h : Fin M → GF256) (w : ℕ → GF128)
    (hw : ¬pomfritWit GF256.ofBits N M pk h w) :
    #{l : Fin M → GF128 | (pomfritRedeemSystem beta GF256.toBits N M pk h l).Holds w} * 2 ^ 128 ≤
      (2 ^ 128) ^ M := by
  have := pomfrit_comb_bad Arith.isEmbedding N M pk h w hw
  rwa [GF128.card_eq, card_fun_gf128] at this

/-- **PomFRIT redeem, end to end, at GF(2¹²⁸).** -/
theorem pomfrit_extract_gf128 {Ch : Type*} (N M : ℕ) (pk : ℕ → GF256) (h : Fin M → GF256)
    (l : Fin M → GF128)
    {e : (∀ i, B i) →+ GF128} {A : Finset (∀ i, B i)} {known : Finset ι}
    {u : ι → Fin (witnessBits N M) → Bool} {Q : Fin (witnessBits N M) → (∀ i, B i) → GF128}
    {uStar : Fin (witnessBits N M) → GF128}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar) (dc : Fin (witnessBits N M) → Bool)
    (r₀ r₁ s t : GF128) (R : GF128[X]) (hR : R.natDegree ≤ 1)
    (hacc : ∀ Δ ∈ A, qsCheck (pomfritRedeemSystem beta GF256.toBits N M pk h l) 2
      (zkCoeff _ r₀ r₁ s t) (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬(pomfritRedeemSystem beta GF256.toBits N M pk h l).Holds (wStar uStar dc) →
      zkHash _ r₀ r₁ s t
        (valVec (pomfritRedeemSystem beta GF256.toBits N M pk h l) (wStar uStar dc)) ≠ 0)
    (hcomb : (pomfritRedeemSystem beta GF256.toBits N M pk h l).Holds (wStar uStar dc) →
      pomfritWit GF256.ofBits N M pk h (wStar uStar dc))
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, pomfritWit GF256.ofBits N M pk h (candidate (F := GF128) u dc i)) ∨
      #{x ∈ Z | acc x} ≤ 2 :=
  pomfrit_extract beta GF256.toBits GF256.ofBits N M pk h l hK dc r₀ r₁ s t R hR hacc hQS hcomb
    Z δ hδ acc hclaim1

end PomFRIT

/-! ## Moussaka -/

section Moussaka

open VoleMole.Arith.Moussaka

/-- **Moussaka issue, end to end, at GF(2¹²⁸).** -/
theorem moussaka_issue_extract_gf128 {Ch : Type*} (t : Fin M → UInt8) (ctxIss : ℕ → UInt8)
    {e : (∀ i, B i) →+ GF128} {A : Finset (∀ i, B i)} {known : Finset ι}
    {u : ι → Fin issueWitnessBits → Bool} {Q : Fin issueWitnessBits → (∀ i, B i) → GF128}
    {uStar : Fin issueWitnessBits → GF128}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar) (dc : Fin issueWitnessBits → Bool)
    (r₀ r₁ s t' : GF128) (R : GF128[X]) (hR : R.natDegree ≤ 8)
    (hacc : ∀ Δ ∈ A, qsCheck (issueSystem (F := GF128) t ctxIss) 9
      (zkCoeff _ r₀ r₁ s t') (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬(issueSystem (F := GF128) t ctxIss).Holds (wStar uStar dc) →
      zkHash _ r₀ r₁ s t' (valVec (issueSystem t ctxIss) (wStar uStar dc)) ≠ 0)
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, moussakaIssueWit t ctxIss (candidate (F := GF128) u dc i)) ∨
      #{x ∈ Z | acc x} ≤ 9 :=
  moussaka_issue_extract t ctxIss hK dc r₀ r₁ s t' R hR hacc hQS Z δ hδ acc hclaim1

theorem moussakaRedeemWit_gf256_iff (anchors : List (ℕ → GF256)) (nf ctxIss ctxRed : ℕ → UInt8)
    (w : ℕ → F) :
    moussakaRedeemWit GF256.ofBits anchors nf ctxIss ctxRed w ↔
      ∃ wb : ℕ → Bool, (∀ i < redeemWitnessBits, w i = bitF (wb i)) ∧
        ∃ u₀, (∀ u < 64, wb (selBit u) = decide (u = u₀)) ∧ ∃ h : u₀ < anchors.length,
          ∀ k : Fin M,
            (publicMap N M anchors[u₀]
              (fun i => ⟨Arith.Keccak.witByte wb (redeemOffS + i)⟩) k).val =
              com nf ctxIss ctxRed (redeemR wb) k :=
  exists_congr fun wb => and_congr_right fun _ => exists_congr fun u₀ =>
    and_congr_right fun _ => redeemRel_gf256_iff anchors nf ctxIss ctxRed _ wb u₀

open Classical in
theorem moussaka_redeem_comb_bad_gf128 (anchors : List (ℕ → GF256)) (hn : anchors.length ≤ 64)
    (nf ctxIss ctxRed : ℕ → UInt8) (w : ℕ → GF128)
    (hw : ¬moussakaRedeemWit GF256.ofBits anchors nf ctxIss ctxRed w) :
    #{l : Fin M → GF128 | (redeemSystem beta GF256.toBits anchors nf ctxIss ctxRed l).Holds w} *
      2 ^ 128 ≤ (2 ^ 128) ^ M := by
  have := moussaka_redeem_comb_bad Arith.isEmbedding Arith.beta_zero anchors hn nf ctxIss ctxRed
    w hw
  rwa [GF128.card_eq, card_fun_gf128] at this

/-- **Moussaka redeem, end to end, at GF(2¹²⁸).** -/
theorem moussaka_redeem_extract_gf128 {Ch : Type*} (anchors : List (ℕ → GF256))
    (nf ctxIss ctxRed : ℕ → UInt8) (l : Fin M → GF128)
    {e : (∀ i, B i) →+ GF128} {A : Finset (∀ i, B i)} {known : Finset ι}
    {u : ι → Fin redeemWitnessBits → Bool} {Q : Fin redeemWitnessBits → (∀ i, B i) → GF128}
    {uStar : Fin redeemWitnessBits → GF128}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar) (dc : Fin redeemWitnessBits → Bool)
    (r₀ r₁ s t : GF128) (R : GF128[X]) (hR : R.natDegree ≤ 8)
    (hacc : ∀ Δ ∈ A, qsCheck (redeemSystem beta GF256.toBits anchors nf ctxIss ctxRed l) 9
      (zkCoeff _ r₀ r₁ s t) (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬(redeemSystem beta GF256.toBits anchors nf ctxIss ctxRed l).Holds (wStar uStar dc) →
      zkHash _ r₀ r₁ s t
        (valVec (redeemSystem beta GF256.toBits anchors nf ctxIss ctxRed l) (wStar uStar dc)) ≠ 0)
    (hcomb : (redeemSystem beta GF256.toBits anchors nf ctxIss ctxRed l).Holds (wStar uStar dc) →
      moussakaRedeemWit GF256.ofBits anchors nf ctxIss ctxRed (wStar uStar dc))
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known,
        moussakaRedeemWit GF256.ofBits anchors nf ctxIss ctxRed (candidate (F := GF128) u dc i)) ∨
      #{x ∈ Z | acc x} ≤ 9 :=
  moussaka_redeem_extract beta GF256.toBits GF256.ofBits anchors nf ctxIss ctxRed l hK dc
    r₀ r₁ s t R hR hacc hQS hcomb Z δ hδ acc hclaim1

end Moussaka

/-! ## Ratatouille -/

section Ratatouille

open VoleMole.Arith.Ratatouille

/-- **Ratatouille issue, end to end, at GF(2¹²⁸).** -/
theorem ratatouille_issue_extract_gf128 {Ch : Type*} (c : ℕ → UInt8) (tInit : ℕ)
    (ctx : ℕ → UInt8)
    {e : (∀ i, B i) →+ GF128} {A : Finset (∀ i, B i)} {known : Finset ι}
    {u : ι → Fin (8 * issueWitnessBytes) → Bool}
    {Q : Fin (8 * issueWitnessBytes) → (∀ i, B i) → GF128}
    {uStar : Fin (8 * issueWitnessBytes) → GF128}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar)
    (dc : Fin (8 * issueWitnessBytes) → Bool)
    (r₀ r₁ s t : GF128) (R : GF128[X]) (hR : R.natDegree ≤ 8)
    (hacc : ∀ Δ ∈ A, qsCheck (issueSystem (F := GF128) c tInit ctx) 9
      (zkCoeff _ r₀ r₁ s t) (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬(issueSystem (F := GF128) c tInit ctx).Holds (wStar uStar dc) →
      zkHash _ r₀ r₁ s t (valVec (issueSystem c tInit ctx) (wStar uStar dc)) ≠ 0)
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, ratatouilleIssueWit c tInit ctx (candidate (F := GF128) u dc i)) ∨
      #{x ∈ Z | acc x} ≤ 9 :=
  ratatouille_issue_extract c tInit ctx hK dc r₀ r₁ s t R hR hacc hQS Z δ hδ acc hclaim1

theorem ratatouilleSpendWit_gf256_iff (pk : ℕ → GF256) (nf : ℕ → UInt8) (d : ℕ)
    (cNext ctx : ℕ → UInt8) (w : ℕ → F) :
    ratatouilleSpendWit GF256.ofBits pk nf d cNext ctx w ↔
      ∃ wb : ℕ → Bool, (∀ i < 8 * spendWitnessBytes, w i = bitF (wb i)) ∧
        (∀ k : Fin uovM,
          (publicMap uovN uovM pk (fun i => ⟨Arith.Keccak.witByte wb (112 + i)⟩) k).val =
            stateByte (keccakP800 (tagState (commit nf ctx (creditAt wb 16) (bytesAt wb 0))
              (creditAt wb 24))) k.1) ∧
        (∀ k < 32, cNext k = commit (bytesAt wb 64) ctx (creditAt wb 88) (bytesAt wb 96) k) ∧
        creditAt wb 16 + creditAt wb 24 = creditAt wb 88 + d ∧ creditAt wb 16 < 2 ^ 64 ∧
        creditAt wb 24 < 2 ^ 64 ∧ creditAt wb 88 < 2 ^ 64 ∧ d < 2 ^ 64 :=
  exists_congr fun wb => and_congr_right fun _ => spendRelOf_gf256_iff pk nf d cNext ctx wb

open Classical in
theorem ratatouille_spend_comb_bad_gf128 (pk : ℕ → GF256) (nf : ℕ → UInt8) {d : ℕ}
    (hd : d < 2 ^ 64) (cNext ctx : ℕ → UInt8) (w : ℕ → GF128)
    (hw : ¬ratatouilleSpendWit GF256.ofBits pk nf d cNext ctx w) :
    #{l : Fin uovM → GF128 | (spendSystem beta GF256.toBits pk nf d cNext ctx l).Holds w} *
      2 ^ 128 ≤ (2 ^ 128) ^ uovM := by
  have := ratatouille_spend_comb_bad Arith.isEmbedding Arith.beta_zero pk nf hd cNext ctx w hw
  rwa [GF128.card_eq, card_fun_gf128] at this

/-- **Ratatouille spend, end to end, at GF(2¹²⁸).** -/
theorem ratatouille_spend_extract_gf128 {Ch : Type*} (pk : ℕ → GF256) (nf : ℕ → UInt8) (d : ℕ)
    (cNext ctx : ℕ → UInt8) (l : Fin uovM → GF128)
    {e : (∀ i, B i) →+ GF128} {A : Finset (∀ i, B i)} {known : Finset ι}
    {u : ι → Fin (8 * spendWitnessBytes) → Bool}
    {Q : Fin (8 * spendWitnessBytes) → (∀ i, B i) → GF128}
    {uStar : Fin (8 * spendWitnessBytes) → GF128}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar)
    (dc : Fin (8 * spendWitnessBytes) → Bool)
    (r₀ r₁ s t : GF128) (R : GF128[X]) (hR : R.natDegree ≤ 8)
    (hacc : ∀ Δ ∈ A, qsCheck (spendSystem beta GF256.toBits pk nf d cNext ctx l) 9
      (zkCoeff _ r₀ r₁ s t) (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬(spendSystem beta GF256.toBits pk nf d cNext ctx l).Holds (wStar uStar dc) →
      zkHash _ r₀ r₁ s t
        (valVec (spendSystem beta GF256.toBits pk nf d cNext ctx l) (wStar uStar dc)) ≠ 0)
    (hcomb : (spendSystem beta GF256.toBits pk nf d cNext ctx l).Holds (wStar uStar dc) →
      ratatouilleSpendWit GF256.ofBits pk nf d cNext ctx (wStar uStar dc))
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known,
        ratatouilleSpendWit GF256.ofBits pk nf d cNext ctx (candidate (F := GF128) u dc i)) ∨
      #{x ∈ Z | acc x} ≤ 9 :=
  ratatouille_spend_extract beta GF256.toBits GF256.ofBits pk nf d cNext ctx l hK dc
    r₀ r₁ s t R hR hacc hQS hcomb Z δ hδ acc hclaim1

end Ratatouille

end VoleMole.EndToEnd
