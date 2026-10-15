import VoleMole.Privacy.MoussakaRO
import VoleMole.ZK.CollideRO

/-!
# Moussaka in the random-oracle model: the programming-collision terms, bounded

`anonymityRO_lean` (`Privacy/MoussakaRO.lean`) carries the collision terms `δI₁`, `δL b`, `δR b`:
the probability that a real proof, run on the tables the earlier simulations programmed, differs
from the proof on the original tables. Here they are bounded (`ZK/CollideRO.lean`).

* **`deltaI1_le`**: `δI₁ ≤ noHitProb + 2⁻¹⁰²⁴`. Issuance `1`'s real proof changes only if its
  grinding prefix's block is the one issuance `0`'s simulator programmed (`realRO_ne_tail`); then
  the prefix's `ã` field (`preTail`, the last `128` bytes of the `200`-byte prefix: `preLen =
  72 + 16·(9 − 1)`) is the simulation's tail (`simTail`: its uniform `ã`, unless it produced no
  proof). Issuance `1`'s prefix does not depend on issuance `0`'s coins, so this is
  `≤ noHitProb + 2^(−8·128)` (`pr_simTail_eq_le`).
* **`deltaL_le`, `deltaR_le`**: `δL b ≤ 2⁻¹¹⁰ + εRO(0, 312, 4607) + noHitProb + 2·2⁻¹⁰²⁴` and
  `δR b ≤ … + 3·2⁻¹⁰²⁴`. A redemption's statement is the adversary's choice after it saw the
  simulated requests, so its prefix may depend on their `ã`; the bound is `pr_collide_zk` (a second
  application of zero knowledge, to the distinguisher "the recomputed prefix's tail is among the
  earlier simulations' tails"; the grinding outcome at the real prefix is bad with probability
  `≤ 2⁻¹¹⁰`). If the Client's check at the redemption point fails, no proof is computed and the
  term is `0`.
* **`anonymityRO_lean_num`**: `anonymityRO_lean` with these bounds: the two worlds differ by at most

      8·εRO(q₃, q₅ + 1872, q_E + 13821) + 4·(2⁻¹¹⁰ + εRO(0, 312, 4607)) + 6·noHitProb
        + 12·2⁻¹⁰²⁴ + 2·εhide,

  and `noHitProb ≤ 2^(−2¹⁵)` (`noHitProb_le`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

variable (A : AdversaryRO) (idx : AnchorSet → UOVKey → ℕ)

lemma toL_getD_ne {o o' : Except String ByteArray}
    (h : toL (o.toOption.getD .empty) ≠ toL (o'.toOption.getD .empty)) : o ≠ o' :=
  fun e => h (by rw [e])

lemma hlab_pI : pI.labelRowOffset + 128 ≤ pI.correctionRows := by decide

lemma hlab_pR : pR.labelRowOffset + 128 ≤ pR.correctionRows := by decide

lemma tail_pI : (8 * (16 * (pI.qsDegree - 1)) : ℕ) = 1024 := rfl

lemma tail_pR : (8 * (16 * (pR.qsDegree - 1)) : ℕ) = 1024 := rfl

/-- **The collision term of hop 1**: `δI₁ ≤ noHitProb + 2⁻¹⁰²⁴`. -/
theorem deltaI1_le : deltaI1 A leanProgI leanPI ≤ noHitProb + 1 / 2 ^ 1024 := by
  unfold deltaI1
  refine (pr_mono (Q := fun z => preTail (blk (preLen pI) (preRO Hashes.shake
      (stI (xIOf A z.1.2.1)) (toBA (wIOf A z.1.2.1)) z.2.1.1 z.2.1.2 z.2.2)) ∈
      ({simTail z.1.1.2.1} : Finset ByteArray)) fun z hz => ?_).trans ?_
  · rw [leanPI_ofFn, leanPI_ofFn] at hz
    have h1 := toL_getD_ne hz
    have hL := progRO_progAt Hashes.shake (stI (xIOf A z.1.1.1)) z.1.1.2.1
    have hz' := zkHypI _ _ (issueRelW_of A z.1.2.1)
    have hT : ∀ s, ∀ b ∈ ({simBlk Hashes.shake (stI (xIOf A z.1.1.1)) z.1.1.2.1 s} :
        Finset (Bytes (preLen pI))), preTail b ∈ ({simTail z.1.1.2.1} : Finset ByteArray) := by
      intro s b hb
      rw [Finset.mem_singleton] at hb ⊢
      rw [hb]
      exact preTail_simBlk hashesWF_shake rfl _ _
    exact realRO_ne_tail hz' hashesWF_shake hlab_pI hL hT _ _ _ h1
  · refine pr_le_of_snd fun y => pr_le_of_snd fun r => pr_le_of_fst fun n =>
      pr_le_of_snd fun g => ?_
    have h := pr_simTail_eq_le (p := pI) (preTail (blk (preLen pI) (preRO Hashes.shake
      (stI (xIOf A r.1)) (toBA (wIOf A r.1)) y.1.1 y.1.2 y.2)))
    rw [tail_pI] at h
    refine le_trans (le_of_eq (pr_congr fun c => ?_)) h
    exact Finset.mem_singleton

/-- **A redemption whose Client check fails computes no proof**: its output does not depend on the
tables. -/
lemma redRealRO_out_not_ok (PR : ProverRO RedeemInstance) (x : TRr) (p : RedeemPt)
    (h : redeemOk A.base.ci A.base.cr p.tok p.anchors p.i = false) (u u' : ShM) :
    (redRealRO A PR x).out p u = (redRealRO A PR x).out p u' := by
  unfold redeemOk at h
  simp only [redRealRO, redeemRequestOf]
  split
  · rfl
  · rename_i pk hk
    rw [hk] at h
    have h' : ¬ pk.eval p.tok.s = com p.tok.nf A.base.ci A.base.cr p.tok.r := by simpa using h
    simp only [h', ↓reduceIte]

lemma smallParams_pR : SmallParams pR := smallParams_of_le (by decide) (by decide)

/-- The issuance simulations' programming in a redemption hop, as a programming at two prefix
blocks whose tails are the simulations' tails. -/
lemma progAt_PIOf {α : Type} (γ : (TIs (SimCoins pI) × TIs (SimCoins pI)) × α) :
    ProgAt (PIOf A leanProgI γ) (fun s =>
      {simBlk Hashes.shake (stI (xIOf A γ.1.1.1)) γ.1.1.2.1
          (progRO pI Hashes.shake (stI (xIOf A γ.1.2.1)) γ.1.2.2.1 s)} ∪
        {simBlk Hashes.shake (stI (xIOf A γ.1.2.1)) γ.1.2.2.1 s}) :=
  (progRO_progAt Hashes.shake _ _).comp (progRO_progAt Hashes.shake _ _)

lemma tails_PIOf {α : Type} (γ : (TIs (SimCoins pI) × TIs (SimCoins pI)) × α) (s : ShM) :
    ∀ b ∈ ({simBlk Hashes.shake (stI (xIOf A γ.1.1.1)) γ.1.1.2.1
          (progRO pI Hashes.shake (stI (xIOf A γ.1.2.1)) γ.1.2.2.1 s)} ∪
        {simBlk Hashes.shake (stI (xIOf A γ.1.2.1)) γ.1.2.2.1 s} : Finset (Bytes (preLen pI))),
      preTail b ∈ ({simTail γ.1.1.2.1, simTail γ.1.2.2.1} : Finset ByteArray) := by
  intro b hb
  rcases Finset.mem_union.1 hb with hb | hb <;> rw [Finset.mem_singleton] at hb <;> rw [hb]
  · exact Finset.mem_insert.2 (Or.inl (preTail_simBlk hashesWF_shake rfl _ _))
  · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 (preTail_simBlk hashesWF_shake rfl _ _)))

/-- **The collision term of hop L**: `δL b ≤ 2⁻¹¹⁰ + εRO(0, 312, 4607) + noHitProb + 2·2⁻¹⁰²⁴`. -/
theorem deltaL_le (b : Bool) : deltaL A idx (leanSim pI) leanProgI leanPR b ≤
    1 / 2 ^ 110 + εRO 0 312 4607 + (noHitProb + 2 / 2 ^ 1024) := by
  unfold deltaL
  refine pr_le_of_fst fun γ => ?_
  set p := pt A.base idx b (i₀Of A (leanSim pI) γ) (i₁Of A (leanSim pI) γ) false with hp
  have hnn : 0 ≤ 1 / 2 ^ 110 + εRO 0 312 4607 + (noHitProb + 2 / 2 ^ 1024 : ℝ) := by
    have := pr_nonneg (α := Grind) (fun g => firstHit g = none)
    have := εRO_nonneg' 0 312 4607
    unfold noHitProb; positivity
  cases hok : redeemOk A.base.ci A.base.cr p.tok p.anchors p.i
  · refine le_trans (le_of_eq ?_) hnn
    rw [← pr_false (α := (Coins proveSeedBytes × Tab3) × ShM)]
    exact pr_congr fun a => ⟨fun h => h (redRealRO_out_not_ok A leanPR _ p hok _ _), False.elim⟩
  · have hwf := tokD_wf A.base (i₀ := i₀Of A (leanSim pI) γ) (i₁ := i₁Of A (leanSim pI) γ)
      (issSimOut_wf A (leanSim pI) _) (issSimOut_wf A (leanSim pI) _) (b ^^ false)
    obtain ⟨hrel, hreal, -⟩ := redeem_facts A (leanSim pR) leanPR p hwf.1 hwf.2.1 hwf.2.2 hok
    refine (pr_mono (Q := fun a : (Coins proveSeedBytes × Tab3) × ShM =>
        realRO pR Hashes.shake (stR (xROf A p)) (toBA (wROf A p)) a.1.1 a.1.2
          (PIOf A leanProgI γ a.2) ≠
        realRO pR Hashes.shake (stR (xROf A p)) (toBA (wROf A p)) a.1.1 a.1.2 a.2)
      fun a ha => ?_).trans ?_
    · rw [hreal, hreal] at ha
      intro e
      apply ha
      rw [leanPR_ofFn, leanPR_ofFn, e]
    · refine (pr_collide_zk rfl (zkHypR _ _ hrel) hashesWF_shake smallParams_pR
        (progAt_PIOf A γ) _ (tails_PIOf A γ)).trans ?_
      have hc : (({simTail γ.1.1.2.1, simTail γ.1.2.2.1} : Finset ByteArray).card : ℝ) ≤ 2 := by
        exact_mod_cast Finset.card_le_two
      rw [show (stR (xROf A p)).params = pR from rfl, tail_pR]
      gcongr

/-- **The collision term of hop R**: `δR b ≤ 2⁻¹¹⁰ + εRO(0, 312, 4607) + noHitProb + 3·2⁻¹⁰²⁴`. -/
theorem deltaR_le (b : Bool) :
    deltaR A idx (leanSim pI) leanProgI leanProgR leanPR b ≤
      1 / 2 ^ 110 + εRO 0 312 4607 + (noHitProb + 3 / 2 ^ 1024) := by
  unfold deltaR
  refine pr_le_of_fst fun γ => ?_
  set p := pt A.base idx b (i₀Of A (leanSim pI) γ) (i₁Of A (leanSim pI) γ) true with hp
  have hnn : 0 ≤ 1 / 2 ^ 110 + εRO 0 312 4607 + (noHitProb + 3 / 2 ^ 1024 : ℝ) := by
    have := pr_nonneg (α := Grind) (fun g => firstHit g = none)
    have := εRO_nonneg' 0 312 4607
    unfold noHitProb; positivity
  cases hok : redeemOk A.base.ci A.base.cr p.tok p.anchors p.i
  · refine le_trans (le_of_eq ?_) hnn
    rw [← pr_false (α := (Coins proveSeedBytes × Tab3) × ShM)]
    exact pr_congr fun a => ⟨fun h => h (redRealRO_out_not_ok A leanPR _ p hok _ _), False.elim⟩
  · have hwf := tokD_wf A.base (i₀ := i₀Of A (leanSim pI) γ) (i₁ := i₁Of A (leanSim pI) γ)
      (issSimOut_wf A (leanSim pI) _) (issSimOut_wf A (leanSim pI) _) (b ^^ true)
    obtain ⟨hrel, hreal, -⟩ := redeem_facts A (leanSim pR) leanPR p hwf.1 hwf.2.1 hwf.2.2 hok
    set xL := xROf A (pt A.base idx b (i₀Of A (leanSim pI) γ) (i₁Of A (leanSim pI) γ) false)
    set ok := allOk A.base idx (i₀Of A (leanSim pI) γ) (i₁Of A (leanSim pI) γ)
    have hLi := ProgAt.ite (ok = true) (progRO_progAt Hashes.shake (stR xL) γ.2.1)
    have hL := (progAt_PIOf A γ).comp hLi
    have hT : ∀ s, ∀ b' ∈ ({simBlk Hashes.shake (stI (xIOf A γ.1.1.1)) γ.1.1.2.1
          (progRO pI Hashes.shake (stI (xIOf A γ.1.2.1)) γ.1.2.2.1
            (if ok = true then progRO pR Hashes.shake (stR xL) γ.2.1 s else s))} ∪
        {simBlk Hashes.shake (stI (xIOf A γ.1.2.1)) γ.1.2.2.1
          (if ok = true then progRO pR Hashes.shake (stR xL) γ.2.1 s else s)} ∪
        (if ok = true then {simBlk Hashes.shake (stR xL) γ.2.1 s} else ∅) :
          Finset (Bytes (preLen pI))),
        preTail b' ∈ ({simTail γ.2.1, simTail γ.1.1.2.1, simTail γ.1.2.2.1} : Finset ByteArray) := by
      intro s b' hb
      rcases Finset.mem_union.1 hb with hb | hb
      · exact Finset.mem_insert.2 (Or.inr (tails_PIOf A γ _ b' hb))
      · by_cases hc : ok = true
        · simp only [hc, ↓reduceIte] at hb
          have hb' : b' = simBlk Hashes.shake (stR xL) γ.2.1 s := Finset.mem_singleton.1 hb
          rw [hb']
          exact Finset.mem_insert.2 (Or.inl (preTail_simBlk hashesWF_shake rfl _ _))
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hb
          exact absurd hb (Finset.notMem_empty _)
    refine (pr_mono (Q := fun a : (Coins proveSeedBytes × Tab3) × ShM =>
        realRO pR Hashes.shake (stR (xROf A p)) (toBA (wROf A p)) a.1.1 a.1.2
          (LR A idx (leanSim pI) leanProgI leanProgR b γ a.2) ≠
        realRO pR Hashes.shake (stR (xROf A p)) (toBA (wROf A p)) a.1.1 a.1.2 a.2)
      fun a ha => ?_).trans ?_
    · rw [hreal, hreal] at ha
      intro e
      apply ha
      rw [leanPR_ofFn, leanPR_ofFn, e]
    · refine (pr_collide_zk rfl (zkHypR _ _ hrel) hashesWF_shake smallParams_pR hL _ hT).trans ?_
      have hc : (({simTail γ.2.1, simTail γ.1.1.2.1, simTail γ.1.2.2.1} :
          Finset ByteArray).card : ℝ) ≤ 3 := by
        exact_mod_cast Finset.card_le_three
      rw [show (stR (xROf A p)).params = pR from rfl, tail_pR]
      gcongr

/-- **Theorem 4(a) with the Lean prover, in the random-oracle and ideal-cipher model, with every
term explicit.** As `anonymityRO_lean`, with the programming-collision terms bounded: the two
worlds differ by at most

    8·εRO(q₃, q₅ + 1872, q_E + 13821) + 4·(2⁻¹¹⁰ + εRO(0, 312, 4607)) + 6·noHitProb
      + 12·2⁻¹⁰²⁴ + 2·εhide,

`εRO q₃ q₅ q_E = q₃·2⁻¹²⁸ + 2⁻¹¹⁰ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸` and
`noHitProb ≤ 2^(−2¹⁵)` (`noHitProb_le`). -/
theorem anonymityRO_lean_num (A : AdversaryRO) (idx : AnchorSet → UOVKey → ℕ) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b c, hidingAdv A.base.ci A.base.cr
      (reductionRO A idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRO A idx leanPI leanPR false) - pr _ (realGameRO A idx leanPI leanPR true)| ≤
      8 * εRO q3 (q5 + 1872) (qE + 13821) + 4 * (1 / 2 ^ 110 + εRO 0 312 4607) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  refine (anonymityRO_lean A idx hA hhide).trans (le_trans (add_le_add (add_le_add (add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (deltaI1_le A) (by norm_num)))
    (add_le_add (deltaL_le A idx false) (deltaL_le A idx true)))
    (add_le_add (deltaR_le A idx false) (deltaR_le A idx true))) le_rfl) (le_of_eq ?_))
  generalize (2 : ℝ) ^ 1024 = K
  ring

end VoleMole.Privacy.Moussaka
