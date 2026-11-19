import VoleMole.ZK.MainSharedLin4
import VoleMole.Privacy.MoussakaMainFind
import VoleMole.Privacy.MoussakaNCMainLean

/-!
# Moussaka 4(a) and 4(b') on `main`, all tables shared, on the linear joint hop

`anonymity_main_sharedAll` (Theorem 4(a), `Privacy/MoussakaMainSharedAll.lean`) and
`anonymityNC_main` (Theorem 4(b'), `Privacy/MoussakaNCMain.lean`) go through the four-proof joint
hop `main_sharedAll_le`: `15·(εS(q₃, q_E + 8·4607) + Δ23)` per world, `15` on the bad event
`bstar`, and the probability that two real proofs have one prefix. Here both games, unchanged,
go through `main_sharedAll_le4LinJ` (`ZK/MainSharedLin4.lean`), which restates a four-proof game
as a `ZK.Sim.NGame` and applies the linear hop with joint reads (`main_sharedAll_leLinJ`): per
world `8·(εS(q₃ + 4, q_E + 8·4607) + Δ23N(9, 4))`, `1` on `bstar`, no prefix-collision term. The
guess and its `H₅` read set must read `H₃` and the cipher jointly (`ConsJ`: one read set of
`q₃` points and one of `q_E` keys for both); an adversary with separate read sets (`ConsH`) has
joint ones at twice the budgets (`ConsH.consJ`). The
simulated side (hiding, the swap, the abort hop) and the bounds on `bstar` (the (PU) predictors
`predH_c b`, the statistical `pr_bstarNCM_le`) are those of the four-proof theorems: the
all-simulated game and its bad event are the same.

## The bounds

    anonymity_main_sharedLin (4(a)):
      |Pr[W₀] − Pr[W₁]| ≤ 16·(εS(q₃ + 4, q_E + 8·4607) + Δ23N(9, 4))
          + Σ_{b,c} puAdv Com (predH_c b) + 8·noHitProb + 3750·2⁻¹²⁸ + 2·εhide
    anonymityNC_main_lin (4(b')):
      |Pr[W₀] − Pr[W₁]| ≤ 16·(εS(q₃ + 4, q_E + 8·4607) + Δ23N(9, 4))
          + 8·noHitProb + (4·(q₅ + 625) + 626)·2⁻¹²⁸ + 2·(φ false + φ true)

`anonymityNC_main_lean_lin`: the same with `main`'s Lean issuance prover, `+ 4·2⁻¹¹³`;
`unlinkabilityNC_main_lin`: one Anchor, no abort term; `*_find`: at `main`'s `find_issuer` Client.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Privacy.PU

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval
attribute [local irreducible] simulate realRO progRO

/-! ## Joint reads -/

/-- **Separate read sets are joint read sets at the sum of the budgets.** -/
theorem rdTH_pair {X Y : Type*} {f : VisS → H3T → X} {g : VisS → H3T → Y}
    {R : VisS → H3T → Finset (ZK.Sim.Bytes 37)} {q3 qE q3' qE' : ℕ} (hf : RdTH f R q3 qE)
    (hg : RdTH g R q3' qE') : RdTH (fun t T => (f t T, g t T)) R (q3 + q3') (qE + qE') := by
  classical
  obtain ⟨QE, hQEc, hQE⟩ := hf.hE
  obtain ⟨QT, hQTc, hQT⟩ := hf.hT
  obtain ⟨PE, hPEc, hPE⟩ := hg.hE
  obtain ⟨PT, hPTc, hPT⟩ := hg.hT
  refine ⟨fun t T G5 h => ?_, ⟨fun t T => QE t T ∪ PE t T, fun t T => (card_union_le _ _).trans
      (add_le_add (hQEc t T) (hPEc t T)), fun t T E h => ?_⟩,
    ⟨fun t T => QT t T ∪ PT t T, fun t T => (card_union_le _ _).trans
      (add_le_add (hQTc t T) (hPTc t T)), fun t T T' h => ?_⟩⟩
  · show (f _ T, g _ T) = (f t T, g t T)
    rw [hf.h5 t T G5 h, hg.h5 t T G5 h]
  · show (f _ T, g _ T) = (f t T, g t T)
    rw [hQE t T E fun k hk => h k (mem_union_left _ hk),
      hPE t T E fun k hk => h k (mem_union_right _ hk)]
  · show (f t T', g t T') = (f t T, g t T)
    rw [hQT t T T' fun k hk => h k (mem_union_left _ hk),
      hPT t T T' fun k hk => h k (mem_union_right _ hk)]

/-- **Joint consistent reads**: with the requests fixed, the guess and its `H₅` read set read `H₃`
at one set of `q3` points and the cipher at one set of `qE` keys (as the guess and the read set
of one oracle run do), and `H₅` at `R5`. -/
structure AdversaryH.ConsJ (A : AdversaryH) (q3 qE : ℕ) : Prop where
  j : ∀ q₀ q₁ y, RdTH (fun t T => (A.guess q₀ q₁ y t T, A.R5 q₀ q₁ y t T)) (A.R5 q₀ q₁ y) q3 qE

/-- Consistent reads are joint consistent reads at twice the budgets. -/
theorem AdversaryH.ConsH.consJ {A : AdversaryH} {q3 qE : ℕ} (h : A.ConsH q3 qE) :
    A.ConsJ (q3 + q3) (qE + qE) :=
  ⟨fun q₀ q₁ y => rdTH_pair (h.g q₀ q₁ y) (h.r q₀ q₁ y)⟩

/-- **Joint consistent reads** of the non-colluding Moderator. -/
structure AdversaryNCM.ConsJ (A : AdversaryNCM) (q3 qE : ℕ) : Prop where
  j : ∀ y, RdTH (fun t T => (A.guess y t T, A.R5 y t T)) (A.R5 y) q3 qE

/-- Consistent reads are joint consistent reads at twice the budgets. -/
theorem AdversaryNCM.ConsH.consJ {A : AdversaryNCM} {q3 qE : ℕ} (h : A.ConsH q3 qE) :
    A.ConsJ (q3 + q3) (qE + qE) :=
  ⟨fun y => rdTH_pair (h.g y) (h.r y)⟩

/-! ## Theorem 4(a) -/

section Colluding

variable (A : AdversaryH) (idx : Rule)

/-- **The joint hop in each world, linear**: all four proofs at once, all tables shared, no
prefix-collision term. -/
theorem real_sim_sharedLin {q3 qE : ℕ} (hC : A.ConsJ q3 qE) (b : Bool) :
    |realH A idx b - simH A idx b| ≤
      8 * (εS (q3 + 4) (qE + 8 * 4607) + Δ23N 9 4) +
        simAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
          (gameS A.base idx b) (fun v T => bstar Hashes.shake (gameS A.base idx b)
            (fun v => r5H A idx b v T) v) :=
  main_sharedAll_le4LinJ (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
    (gameS A.base idx b) mainP_pIm mainP_pIm mainP_pRm mainP_pRm small_pIm small_pIm small_pRm
    small_pRm hashesWF_shake (gvalidS A.base idx b) (evH A idx b) (r5H A idx b)
    (rdH_of A idx (f := fun y t T => (A.guess y.1 y.2.1 y.2.2 t T, A.R5 y.1 y.2.1 y.2.2 t T))
      (R := fun y t T => A.R5 y.1 y.2.1 y.2.2 t T) (fun y => hC.j y.1 y.2.1 y.2.2) b)

/-- **Theorem 4(a) on `main` (no label rows), all tables shared, on the linear joint hop.** For
the colluding adversary whose guess reads the one `H₃` at `q3` points, the cipher at `qE` keys and
`H₅` at a consistent read set, jointly (`AdversaryH.ConsJ`; `ConsH.consJ` at twice the budgets),

    |Pr[world 0] − Pr[world 1]| ≤ 16·(εS(q3 + 4, qE + 8·4607) + Δ23N(9, 4))
      + Σ_{b, c} puAdv Com (predH_c b) + 8·noHitProb + 3750·2⁻¹²⁸ + 2·εhide.

Compared with `anonymity_main_sharedAll`: `30` becomes `16`, the factor `15` on the (PU) terms
becomes `1`, and the prefix-collision term `2·2⁻¹²⁸` is gone. -/
theorem anonymity_main_sharedLin {q3 qE : ℕ} (hC : A.ConsJ q3 qE) {εhide : ℝ}
    (hhide : ∀ T b a, hidingAdv A.base.toM.int.ci A.base.toM.int.cr (redS23 (A.withH T) idx b a) ≤
      εhide) :
    |realH A idx false - realH A idx true| ≤
      16 * (εS (q3 + 4) (qE + 8 * 4607) + Δ23N 9 4) +
        (puAdv (comM A.base.toM) (predH₀ A idx false) +
          puAdv (comM A.base.toM) (predH₁ A idx false) +
          puAdv (comM A.base.toM) (predH₀ A idx true) +
          puAdv (comM A.base.toM) (predH₁ A idx true) + 8 * noHitProb + 3750 / 2 ^ 128) +
        2 * εhide := by
  have r0 := real_sim_sharedLin A idx hC false
  have r1 := real_sim_sharedLin A idx hC true
  have p0 := simAll_bstar_le A idx false
  have p1 := simAll_bstar_le A idx true
  have h0 := hiding_hopH A idx false (fun T => hhide T false)
  have h1 := hiding_hopH A idx true (fun T => hhide T true)
  have e := idealH_eq A idx
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 h0
  have := abs_sub_le_iff.1 h1
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Colluding

/-- **Theorem 4(a) on `main`, all tables shared, linear joint hop, for `main`'s Client**
(`find_issuer`, the rule `findIdx`): the bound of `anonymity_main_sharedLin`. -/
theorem anonymity_main_sharedLin_find (A : AdversaryH) {q3 qE : ℕ} (hC : A.ConsJ q3 qE)
    {εhide : ℝ}
    (hhide : ∀ T b a, hidingAdv A.base.toM.int.ci A.base.toM.int.cr
      (redS23 (A.withH T) findIdx b a) ≤ εhide) :
    |realH A findIdx false - realH A findIdx true| ≤
      16 * (εS (q3 + 4) (qE + 8 * 4607) + Δ23N 9 4) +
        (puAdv (comM A.base.toM) (predH₀ A findIdx false) +
          puAdv (comM A.base.toM) (predH₁ A findIdx false) +
          puAdv (comM A.base.toM) (predH₀ A findIdx true) +
          puAdv (comM A.base.toM) (predH₁ A findIdx true) + 8 * noHitProb + 3750 / 2 ^ 128) +
        2 * εhide :=
  anonymity_main_sharedLin A findIdx hC hhide

/-! ## Theorem 4(b') -/

section NonColluding

variable (A : AdversaryNCM) (idx : Rule) (PI : NIZK IssueInstance) (sk : Bool → Signer)

/-- **The joint hop in each world of the non-colluding game, linear.** -/
theorem real_sim_NCMLin (hsk : ∀ c, (sk c).Correct (A.pk c)) {q3 qE : ℕ} (hC : A.ConsJ q3 qE)
    (b : Bool) :
    |realNCM A idx PI sk b - simNCM A idx PI sk b| ≤
      8 * (εS (q3 + 4) (qE + 8 * 4607) + Δ23N 9 4) +
        simAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
          (gameNCM A idx PI sk b) (fun v T => bstar Hashes.shake (gameNCM A idx PI sk b)
            (fun v => r5NCM A idx PI sk b v T) v) :=
  main_sharedAll_le4LinJ (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343) Hashes.shake
    (gameNCM A idx PI sk b) mainP_pIm mainP_pIm mainP_pRm mainP_pRm small_pIm small_pIm small_pRm
    small_pRm hashesWF_shake (gvalidNCM A idx PI sk hsk b) (evNCM A idx PI sk b)
    (r5NCM A idx PI sk b)
    (rdH_ofNC A idx PI sk (f := fun y t T => (A.guess y t T, A.R5 y t T))
      (R := fun y t T => A.R5 y t T) hC.j b)

/-- **Theorem 4(b') on `main` (no label rows), all tables shared, on the linear joint hop.** For
the Moderator, the Anchors, the rule and the issuance proof system of `anonymityNC_main`,

    |Pr[W₀] − Pr[W₁]| ≤ 16·(εS(q3 + 4, qE + 8·4607) + Δ23N(9, 4))
        + 8·noHitProb + (4·(q5 + 625) + 626)·2⁻¹²⁸ + 2·(φ false + φ true).

Compared with `anonymityNC_main`: `30` becomes `16`, the factor `15` on the statistical (PU) term
becomes `1`, and the prefix-collision term `2·2⁻¹²⁸` is gone. No assumption on `Com`. -/
theorem anonymityNC_main_lin (hsk : ∀ c, (sk c).Correct (A.pk c)) {f : Bool → Bool → Bool}
    (hidx : RuleNC A.nc idx f) {q3 qE q5 : ℕ}
    (hC : A.ConsJ q3 qE) (h5 : ∀ y t T, (A.R5 y t T).card ≤ q5) :
    |realNCM A idx PI sk false - realNCM A idx PI sk true| ≤
      16 * (εS (q3 + 4) (qE + 8 * 4607) + Δ23N 9 4) +
        (8 * noHitProb + (4 * (q5 + 625) + 626) / 2 ^ 128) +
        2 * (phi A.nc sk false + phi A.nc sk true) := by
  have r0 := real_sim_NCMLin A idx PI sk hsk hC false
  have r1 := real_sim_NCMLin A idx PI sk hsk hC true
  have b0 := pr_bstarNCM_le A idx PI sk hsk h5 false
  have b1 := pr_bstarNCM_le A idx PI sk hsk h5 true
  have g0 := sim_hyb_NCM A idx PI sk f hsk hidx false
  have g1 := sim_hyb_NCM A idx PI sk f hsk hidx true
  have he := hybNCM_eq A PI f
  have hn : (4 * ((q5 : ℝ) + 625) + 626) / 2 ^ 128 =
      2 * ((q5 + 625) / 2 ^ 128) + 313 / 2 ^ 128 +
        (2 * ((q5 + 625) / 2 ^ 128) + 313 / 2 ^ 128) := by
    ring
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1; have := abs_sub_le_iff.1 g0
  have := abs_sub_le_iff.1 g1
  rw [abs_sub_le_iff, hn]
  constructor <;> linarith

/-- **Unlinkability against a non-colluding Moderator on `main`, linear joint hop**: one Anchor
(equal keys and signers), any index rule, the bound of `anonymityNC_main_lin` without the abort
term. -/
theorem unlinkabilityNC_main_lin (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hpk : A.pk false = A.pk true) (hs : sk false = sk true) {q3 qE q5 : ℕ} (hC : A.ConsJ q3 qE)
    (h5 : ∀ y t T, (A.R5 y t T).card ≤ q5) :
    |realNCM A idx PI sk false - realNCM A idx PI sk true| ≤
      16 * (εS (q3 + 4) (qE + 8 * 4607) + Δ23N 9 4) +
        (8 * noHitProb + (4 * (q5 + 625) + 626) / 2 ^ 128) := by
  have hg : goodN A.nc idx PI sk false = goodN A.nc idx PI sk true := by
    funext i
    have hpk' : A.nc.pk false = A.nc.pk true := hpk
    simp only [goodN, okN, tokDN, tokN, respN, hpk', hs]
  have hsim (b : Bool) : simNCM A idx PI sk b =
      hybG A (fun x => goodN A.nc idx PI sk true (issReal A.nc.base PI x)) b := by
    rw [simNCM_eq A idx PI sk hsk b]
    refine pr_congr fun z => ?_
    have e : gNC A idx PI sk z.1.1 = (goodN A.nc idx PI sk true (issReal A.nc.base PI z.1.1.1) &&
        goodN A.nc idx PI sk true (issReal A.nc.base PI z.1.1.2)) := by
      unfold gNC iOf xOf
      rw [hg]
      rfl
    rw [e]
  have r0 := real_sim_NCMLin A idx PI sk hsk hC false
  have r1 := real_sim_NCMLin A idx PI sk hsk hC true
  have b0 := pr_bstarNCM_le A idx PI sk hsk h5 false
  have b1 := pr_bstarNCM_le A idx PI sk hsk h5 true
  have he := hybG_eq A (fun x => goodN A.nc idx PI sk true (issReal A.nc.base PI x))
  rw [← hsim, ← hsim] at he
  have hn : (4 * ((q5 : ℝ) + 625) + 626) / 2 ^ 128 =
      2 * ((q5 + 625) / 2 ^ 128) + 313 / 2 ^ 128 +
        (2 * ((q5 + 625) / 2 ^ 128) + 313 / 2 ^ 128) := by
    ring
  have := abs_sub_le_iff.1 r0; have := abs_sub_le_iff.1 r1
  rw [abs_sub_le_iff, hn]
  constructor <;> linarith

end NonColluding

/-- **Theorem 4(b') on `main`, linear joint hop, for `main`'s Client** (`findIdx`), for Anchor
Sets that contain both issuers' maps (`MoussakaFind.Contains`): the bound of
`anonymityNC_main_lin`. -/
theorem anonymityNC_main_lin_find (A : AdversaryNCM) (PI : NIZK IssueInstance)
    (sk : Bool → Signer) (hsk : ∀ c, (sk c).Correct (A.pk c)) (hK : MoussakaFind.Contains A.nc)
    {q3 qE q5 : ℕ} (hC : A.ConsJ q3 qE) (h5 : ∀ y t T, (A.R5 y t T).card ≤ q5) :
    |realNCM A findIdx PI sk false - realNCM A findIdx PI sk true| ≤
      16 * (εS (q3 + 4) (qE + 8 * 4607) + Δ23N 9 4) +
        (8 * noHitProb + (4 * (q5 + 625) + 626) / 2 ^ 128) +
        2 * (phi A.nc sk false + phi A.nc sk true) :=
  anonymityNC_main_lin A findIdx PI sk hsk (ruleNC_findIdx A.nc hK) hC h5

/-- **Unlinkability against a non-colluding Moderator on `main`, linear joint hop, for `main`'s
Client**: one Anchor, any Anchor Sets, no abort term. -/
theorem unlinkabilityNC_main_lin_find (A : AdversaryNCM) (PI : NIZK IssueInstance)
    (sk : Bool → Signer) (hsk : ∀ c, (sk c).Correct (A.pk c)) (hpk : A.pk false = A.pk true)
    (hs : sk false = sk true) {q3 qE q5 : ℕ} (hC : A.ConsJ q3 qE)
    (h5 : ∀ y t T, (A.R5 y t T).card ≤ q5) :
    |realNCM A findIdx PI sk false - realNCM A findIdx PI sk true| ≤
      16 * (εS (q3 + 4) (qE + 8 * 4607) + Δ23N 9 4) +
        (8 * noHitProb + (4 * (q5 + 625) + 626) / 2 ^ 128) :=
  unlinkabilityNC_main_lin A findIdx PI sk hsk hpk hs hC h5

/-! ## Theorem 4(b') with the Lean issuance prover -/

section Lean

variable [HasPrg] (A : AdversaryNCM) (idx : Rule) (sk : Bool → Signer)

/-- **Theorem 4(b') on `main` with the Lean issuance prover and the Anchors' Lean verifier, all
tables shared, on the linear joint hop.** For the Moderator, the Anchors and the rule of
`anonymityNC_main_lin`, with the issuance proofs `main`'s executable prover on the shared tables
and the Anchors' verdicts `main`'s `issue_response` with the Lean verifier (`realNCML`),

    |Pr[W₀] − Pr[W₁]| ≤ 16·(εS(q₃ + 4, q_E + 8·4607) + Δ23N(9, 4))
        + 8·noHitProb + (4·(q₅ + 625) + 626)·2⁻¹²⁸ + 2·(φ false + φ true) + 4·2⁻¹¹³. -/
theorem anonymityNC_main_lean_lin (hsk : ∀ c, (sk c).Correct (A.pk c))
    {f : Bool → Bool → Bool} (hidx : RuleNC A.nc idx f) {q3 qE q5 : ℕ}
    (hC : A.ConsJ q3 qE) (h5 : ∀ y t T, (A.R5 y t T).card ≤ q5) :
    |realNCML A idx sk false - realNCML A idx sk true| ≤
      16 * (εS (q3 + 4) (qE + 8 * 4607) + Δ23N 9 4) +
        (8 * noHitProb + (4 * (q5 + 625) + 626) / 2 ^ 128) +
        2 * (phi A.nc sk false + phi A.nc sk true) + 4 / 2 ^ 113 := by
  have h := anonymityNC_main_lin A idx PIacc sk hsk hidx hC h5
  have c0 := realNCML_close A idx sk false
  have c1 := realNCML_close A idx sk true
  have := abs_sub_le_iff.1 h; have := abs_sub_le_iff.1 c0; have := abs_sub_le_iff.1 c1
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Lean

end VoleMole.Privacy.Moussaka
