import VoleMole.Privacy.RatatouilleRO
import VoleMole.ZK.CollideRO

/-!
# Ratatouille in the random-oracle model: the programming-collision terms, bounded

`unlinkabilityRO_lean` (`Privacy/RatatouilleRO.lean`) carries the collision terms `δI₁`, `δS₁`,
`δS₂`. As for Moussaka (`Privacy/MoussakaDelta.lean`, `ZK/CollideRO.lean`):

* **`deltaI1R_le`**: `δI₁ ≤ noHitProb + 2⁻¹⁰²⁴` (issuance `1`'s prefix does not depend on
  issuance `0`'s simulated `ã`, the last `128` bytes of the `200`-byte prefix programmed);
* **`deltaS1R_le`, `deltaS2R_le`**: `δS₁ ≤ 2⁻¹¹⁰ + εRO(0, 312, 4607) + noHitProb + 2·2⁻¹⁰²⁴`,
  `δS₂ ≤ … + 3·2⁻¹⁰²⁴` (`pr_collide_zk`: the spend statements are the Issuer's choices after the
  simulated requests);
* **`unlinkabilityRO_lean_num`**: any two worlds differ by at most

      8·εRO(q₃, q₅ + 1872, q_E + 13821) + 4·(2⁻¹¹⁰ + εRO(0, 312, 4607)) + 6·noHitProb
        + 12·2⁻¹⁰²⁴ + 2·εhide.

**Cipher rows.** Everything here is stated for every type of cipher rows `R` (the shared
tables `ZK.Sim.ShG R p`, `ZK/ReadsRO.lean`) with `ZKRow R`; `unlinkabilityRO_lean_numG` is the generic
Lean-prover bound and `unlinkabilityRO_lean_num` its instance at function rows (`Blk → Blk`, the PRF
view); `Privacy/PermRO.lean` instantiates it at permutation rows (AES as uniformly random
permutations, the adversary reading whole rows: forward and inverse queries).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

variable {Z : Sizes} {R : Type} [Fintype R] [Nonempty R] [CipherRow R]
  (A : AdversaryRO R Sizes.labelRows)

lemma hlab_pI : pI.labelRowOffset + 128 ≤ pI.correctionRows := by decide

lemma hlab_pS : pS.labelRowOffset + 128 ≤ pS.correctionRows := by decide

lemma tail_pI : (8 * (16 * (pI.qsDegree - 1)) : ℕ) = 1024 := rfl

lemma tail_pS : (8 * (16 * (pS.qsDegree - 1)) : ℕ) = 1024 := rfl

lemma smallParams_pS : SmallParams pS := smallParams_of_le (by decide) (by decide)

lemma vecOf_ne {n : ℕ} {o o' : Except String ByteArray} (h : vecOf n o ≠ vecOf n o') : o ≠ o' :=
  fun e => h (by rw [e])

lemma leanPIR_vec (x : IssueInstance) (w : IssueWitness) (ρ : Coins 16) (g : Tab3) (s : ShR R) :
    leanPIR x w (vec ρ) g s = vecOf _ (realRO pI Hashes.shake (stI x) (encI x w) ρ g s) := by
  simp only [leanPIR, realRO, bOf_vec]

lemma leanPSR_vec (x : SpendInstance) (w : SpendWitness) (ρ : Coins 16) (g : Tab3) (s : ShR R) :
    leanPSR x w (vec ρ) g s = vecOf _ (realRO pS Hashes.shake (stS x) (encS x w) ρ g s) := by
  simp only [leanPSR, realRO, bOf_vec]

lemma nonneg_bound [ZKRow R] (k : ℝ) (hk : 0 ≤ k) :
    0 ≤ 1 / 2 ^ 110 + ZKRow.εz R pS 0 312 4607 + (noHitProb + k / 2 ^ 1024 : ℝ) := by
  have := pr_nonneg (α := Grind) (fun g => firstHit g = none)
  have := ZKRow.εz_nonneg (R := R) pS 0 312 4607
  unfold noHitProb; positivity

/-- **The collision term of hop 1**: `δI₁ ≤ noHitProb + 2⁻¹⁰²⁴`. -/
theorem deltaI1R_le : deltaI1R A leanProgIR leanPIR ≤ noHitProb + 1 / 2 ^ 1024 := by
  unfold deltaI1R
  by_cases hT : A.tInit = 0
  · -- Nothing is proved.
    refine le_trans (le_of_eq ?_) (add_nonneg (pr_nonneg _) (by positivity))
    rw [← pr_false (α := (TIsR (SimCoins pI) × (NRR × (TRe × TRe))) × ((Coins 16 × Tab3) × ShR R))]
    exact pr_congr fun z => ⟨fun h => h (by rw [issRealR_out_zero hT, issRealR_out_zero hT]),
      False.elim⟩
  refine (pr_mono (Q := fun z => preTail (blk (preLen pI) (preRO Hashes.shake
      (stI (xIOf A z.1.2.1)) (encI (xIOf A z.1.2.1) ⟨vec z.1.2.1.1, vec z.1.2.1.2⟩) z.2.1.1 z.2.1.2
        z.2.2)) ∈ ({simTail z.1.1.2.1} : Finset ByteArray)) fun z hz => ?_).trans ?_
  · rw [issRealR_out_ne hT, issRealR_out_ne hT] at hz
    simp only [PIR, hT, ↓reduceIte, leanPIR_vec] at hz
    have h1 := vecOf_ne fun e => hz (by rw [e])
    have hL := progRO_progAt (R := R) Hashes.shake (stI (xIOf A z.1.1.1)) z.1.1.2.1
    have hz' := zkHypI (xIOf A z.1.2.1) ⟨vec z.1.2.1.1, vec z.1.2.1.2⟩ rfl
    have hT' : ∀ s : ShR R, ∀ b ∈ ({simBlk Hashes.shake (stI (xIOf A z.1.1.1)) z.1.1.2.1 s} :
        Finset (ZK.Sim.Bytes (preLen pI))), preTail b ∈ ({simTail z.1.1.2.1} : Finset ByteArray) := by
      intro s b hb
      rw [Finset.mem_singleton] at hb ⊢
      rw [hb]
      exact preTail_simBlk hashesWF_shake rfl _ _
    exact realRO_ne_tail hz' hashesWF_shake hlab_pI hL hT' _ _ _ h1
  · refine pr_le_of_snd fun y => pr_le_of_snd fun r => pr_le_of_fst fun n =>
      pr_le_of_snd fun g => ?_
    have h := pr_simTail_eq_le (p := pI) (preTail (blk (preLen pI) (preRO Hashes.shake
      (stI (xIOf A r.1)) (encI (xIOf A r.1) ⟨vec r.1.1, vec r.1.2⟩) y.1.1 y.1.2 y.2)))
    rw [tail_pI] at h
    refine le_trans (le_of_eq (pr_congr fun c => ?_)) h
    exact Finset.mem_singleton

/-- An issuance slot's programming, at most one prefix block. -/
lemma progAt_PIR (n : NRR) (c : SimCoins pI) :
    ProgAt (PIR A leanProgIR n c) (fun s => if A.tInit = 0 then ∅ else
      {simBlk Hashes.shake (stI (xIOf A n)) c s}) :=
  ProgAt.ite_else _ (progRO_progAt (R := R) Hashes.shake _ _)

lemma tails_PIR (n : NRR) (c : SimCoins pI) (s : ShR R) :
    ∀ b ∈ (if A.tInit = 0 then ∅ else {simBlk Hashes.shake (stI (xIOf A n)) c s} :
      Finset (ZK.Sim.Bytes (preLen pI))), preTail b = simTail c := by
  intro b hb
  by_cases hT : A.tInit = 0
  · simp only [hT, ↓reduceIte] at hb
    exact absurd hb (Finset.notMem_empty _)
  · simp only [hT, ↓reduceIte, Finset.mem_singleton] at hb
    rw [hb]
    exact preTail_simBlk hashesWF_shake rfl _ _

/-- The issuance simulations' programming in a spend hop. -/
lemma progAt_PI2R {α : Type} (γ : (TIsR (SimCoins pI) × TIsR (SimCoins pI)) × α) :
    ProgAt (PI2R A leanProgIR γ) (fun s =>
      (if A.tInit = 0 then ∅ else {simBlk Hashes.shake (stI (xIOf A γ.1.1.1)) γ.1.1.2.1
          (PIR A leanProgIR γ.1.2.1 γ.1.2.2.1 s)}) ∪
        (if A.tInit = 0 then ∅ else {simBlk Hashes.shake (stI (xIOf A γ.1.2.1)) γ.1.2.2.1 s})) :=
  (progAt_PIR A _ _).comp (progAt_PIR A _ _)

lemma tails_PI2R {α : Type} (γ : (TIsR (SimCoins pI) × TIsR (SimCoins pI)) × α) (s : ShR R) :
    ∀ b ∈ ((if A.tInit = 0 then ∅ else {simBlk Hashes.shake (stI (xIOf A γ.1.1.1)) γ.1.1.2.1
          (PIR A leanProgIR γ.1.2.1 γ.1.2.2.1 s)}) ∪
        (if A.tInit = 0 then ∅ else {simBlk Hashes.shake (stI (xIOf A γ.1.2.1)) γ.1.2.2.1 s}) :
          Finset (ZK.Sim.Bytes (preLen pI))),
      preTail b ∈ ({simTail γ.1.1.2.1, simTail γ.1.2.2.1} : Finset ByteArray) := by
  intro b hb
  rcases Finset.mem_union.1 hb with hb | hb
  · exact Finset.mem_insert.2 (Or.inl (tails_PIR A _ _ _ b hb))
  · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 (tails_PIR A _ _ _ b hb)))

/-- **A real spend changes only through its proof**: either its Client's checks fail (no proof,
the output does not depend on the tables) or the prover's run differs. -/
lemma spRealR_ne {x : TRe} {τ : TokenS} {d : Credits} {u u' : ShR R}
    (h : (spRealR A leanPSR x).out τ d u ≠ (spRealR A leanPSR x).out τ d u') :
    τ.Valid A.pk A.ctx ∧ ∃ t', clientCheck τ.t τ.x d = some t' ∧
      realRO pS Hashes.shake (stS (xSOf A x.1 τ d)) (encS (xSOf A x.1 τ d) (wSOf x.1 τ t')) x.2.1
          x.2.2 u ≠
        realRO pS Hashes.shake (stS (xSOf A x.1 τ d)) (encS (xSOf A x.1 τ d) (wSOf x.1 τ t'))
          x.2.1 x.2.2 u' := by
  rw [spRealR_out, spRealR_out] at h
  by_cases hv : τ.Valid A.pk A.ctx
  · refine ⟨hv, ?_⟩
    simp only [hv, ↓reduceIte] at h
    rcases hc : clientCheck τ.t τ.x d with _ | t'
    · rw [hc] at h; exact absurd rfl h
    · rw [hc] at h
      refine ⟨t', rfl, ?_⟩
      simp only at h
      have h2 : leanPSR ⟨A.pk, τ.nf, d, com (vec x.1.1) A.ctx t' (vec x.1.2), A.ctx⟩
          (wSOf x.1 τ t') (vec x.2.1) x.2.2 u ≠ leanPSR ⟨A.pk, τ.nf, d,
            com (vec x.1.1) A.ctx t' (vec x.1.2), A.ctx⟩ (wSOf x.1 τ t') (vec x.2.1) x.2.2 u' :=
        fun e => h (by rw [e])
      rw [leanPSR_vec, leanPSR_vec] at h2
      have hx : xSOf A x.1 τ d = ⟨A.pk, τ.nf, d, com (vec x.1.1) A.ctx t' (vec x.1.2), A.ctx⟩ := by
        simp only [xSOf, hc, Option.getD_some]
      rw [hx]
      exact vecOf_ne h2
  · simp only [hv, ↓reduceIte] at h
    exact absurd rfl h

/-- **The collision term of hop S1**: `δS₁ ≤ 2⁻¹¹⁰ + εRO(0, 312, 4607) + noHitProb + 2·2⁻¹⁰²⁴`. -/
theorem deltaS1R_le [ZKRow R] (b₁ : Bool) : deltaS1R A leanSimIR leanProgIR leanPSR b₁ ≤
    1 / 2 ^ 110 + ZKRow.εz R pS 0 312 4607 + (noHitProb + 2 / 2 ^ 1024) := by
  unfold deltaS1R
  refine pr_le_of_fst fun γ => ?_
  set τ := τ₁Of A b₁ (i₀R A leanSimIR γ.1) (i₁R A leanSimIR γ.1)
  set d := A.d₁ ((i₀R A leanSimIR γ.1).req, (i₁R A leanSimIR γ.1).req)
  by_cases hv : τ.Valid A.pk A.ctx ∧ ∃ t', clientCheck τ.t τ.x d = some t'
  · obtain ⟨hv, t', hc⟩ := hv
    refine (pr_mono (Q := fun a : (Coins 16 × Tab3) × ShR R =>
        realRO pS Hashes.shake (stS (xSOf A γ.1.2 τ d)) (encS (xSOf A γ.1.2 τ d) (wSOf γ.1.2 τ t'))
            a.1.1 a.1.2 (PI2R A leanProgIR γ.1 a.2) ≠
          realRO pS Hashes.shake (stS (xSOf A γ.1.2 τ d)) (encS (xSOf A γ.1.2 τ d) (wSOf γ.1.2 τ t'))
            a.1.1 a.1.2 a.2) fun a ha => ?_).trans ?_
    · obtain ⟨-, t'', hc', hne⟩ := spRealR_ne A ha
      rw [hc] at hc'
      cases Option.some.inj hc'
      exact hne
    · refine (pr_collide_zk rfl (zkHypS _ _ (spendRel_of A γ.1.2 hv hc)) hashesWF_shake
        smallParams_pS (progAt_PI2R A γ.1) _ (tails_PI2R A γ.1)).trans ?_
      have hcard : (({simTail γ.1.1.1.2.1, simTail γ.1.1.2.2.1} : Finset ByteArray).card : ℝ) ≤ 2 := by
        exact_mod_cast Finset.card_le_two
      rw [show (stS (xSOf A γ.1.2 τ d)).params = pS from rfl, tail_pS]
      gcongr
  · refine le_trans (le_of_eq ?_) (nonneg_bound 2 (by norm_num))
    rw [← pr_false (α := (Coins 16 × Tab3) × ShR R)]
    exact pr_congr fun a => ⟨fun h => hv (by
      obtain ⟨h1, t', h2, -⟩ := spRealR_ne A h
      exact ⟨h1, t', h2⟩), False.elim⟩

/-- **The collision term of hop S2**: `δS₂ ≤ 2⁻¹¹⁰ + εRO(0, 312, 4607) + noHitProb + 3·2⁻¹⁰²⁴`. -/
theorem deltaS2R_le [ZKRow R] (b₁ b₂ : Bool) :
    deltaS2R A leanSimIR leanSimSR leanProgIR leanProgSR leanPSR b₁ b₂ ≤
      1 / 2 ^ 110 + ZKRow.εz R pS 0 312 4607 + (noHitProb + 3 / 2 ^ 1024) := by
  unfold deltaS2R
  refine pr_le_of_fst fun γ => ?_
  set τ := τ₂R A leanSimIR leanSimSR b₁ b₂ γ
  set d := d₂R A leanSimIR leanSimSR b₁ γ
  by_cases hv : τ.Valid A.pk A.ctx ∧ ∃ t', clientCheck τ.t τ.x d = some t'
  · obtain ⟨hv, t', hc⟩ := hv
    set xS := xSOf A γ.1.2.1 (τ₁Of A b₁ (i₀R A leanSimIR γ.1) (i₁R A leanSimIR γ.1))
      (A.d₁ ((i₀R A leanSimIR γ.1).req, (i₁R A leanSimIR γ.1).req))
    set ok := ok1R A leanSimIR γ.1
    have hLi := ProgAt.ite (ok = true) (progRO_progAt (R := R) Hashes.shake (stS xS) γ.1.2.2.1)
    have hL := (progAt_PI2R A γ.1).comp hLi
    have hT : ∀ s : ShR R, ∀ b' ∈ (((if A.tInit = 0 then ∅ else
          {simBlk Hashes.shake (stI (xIOf A γ.1.1.1.1)) γ.1.1.1.2.1
            (PIR A leanProgIR γ.1.1.2.1 γ.1.1.2.2.1
              (if ok = true then progRO pS Hashes.shake (stS xS) γ.1.2.2.1 s else s))}) ∪
          (if A.tInit = 0 then ∅ else {simBlk Hashes.shake (stI (xIOf A γ.1.1.2.1)) γ.1.1.2.2.1
            (if ok = true then progRO pS Hashes.shake (stS xS) γ.1.2.2.1 s else s)})) ∪
        (if ok = true then {simBlk Hashes.shake (stS xS) γ.1.2.2.1 s} else ∅) :
          Finset (ZK.Sim.Bytes (preLen pI))),
        preTail b' ∈ ({simTail γ.1.2.2.1, simTail γ.1.1.1.2.1, simTail γ.1.1.2.2.1} :
          Finset ByteArray) := by
      intro s b' hb
      rcases Finset.mem_union.1 hb with hb | hb
      · exact Finset.mem_insert.2 (Or.inr (tails_PI2R A γ.1 _ b' hb))
      · by_cases hc : ok = true
        · simp only [hc, ↓reduceIte] at hb
          have hb' : b' = simBlk Hashes.shake (stS xS) γ.1.2.2.1 s := Finset.mem_singleton.1 hb
          rw [hb']
          exact Finset.mem_insert.2 (Or.inl (preTail_simBlk hashesWF_shake rfl _ _))
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hb
          exact absurd hb (Finset.notMem_empty _)
    refine (pr_mono (Q := fun a : (Coins 16 × Tab3) × ShR R =>
        realRO pS Hashes.shake (stS (xSOf A γ.2 τ d)) (encS (xSOf A γ.2 τ d) (wSOf γ.2 τ t'))
            a.1.1 a.1.2 (LS2R A leanSimIR leanProgIR leanProgSR b₁ γ a.2) ≠
          realRO pS Hashes.shake (stS (xSOf A γ.2 τ d)) (encS (xSOf A γ.2 τ d) (wSOf γ.2 τ t'))
            a.1.1 a.1.2 a.2) fun a ha => ?_).trans ?_
    · obtain ⟨-, t'', hc', hne⟩ := spRealR_ne A ha
      rw [hc] at hc'
      cases Option.some.inj hc'
      exact hne
    · refine (pr_collide_zk rfl (zkHypS _ _ (spendRel_of A γ.2 hv hc)) hashesWF_shake
        smallParams_pS hL _ hT).trans ?_
      have hcard : (({simTail γ.1.2.2.1, simTail γ.1.1.1.2.1, simTail γ.1.1.2.2.1} :
          Finset ByteArray).card : ℝ) ≤ 3 := by
        exact_mod_cast Finset.card_le_three
      rw [show (stS (xSOf A γ.2 τ d)).params = pS from rfl, tail_pS]
      gcongr
  · refine le_trans (le_of_eq ?_) (nonneg_bound 3 (by norm_num))
    rw [← pr_false (α := (Coins 16 × Tab3) × ShR R)]
    exact pr_congr fun a => ⟨fun h => hv (by
      obtain ⟨h1, t', h2, -⟩ := spRealR_ne A h
      exact ⟨h1, t', h2⟩), False.elim⟩

/-- **Theorem 2 with the Lean prover, every term explicit, for every type of cipher rows**
(`ZKRow R`): as `unlinkabilityRO_leanG` with the collision terms bounded,

    4·εz(pI; q₃, q₅ + 1872, q_E + 13821) + 4·εz(pS; q₃, q₅ + 1872, q_E + 13821)
      + 4·(2⁻¹¹⁰ + εz(pS; 0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide. -/
theorem unlinkabilityRO_lean_numG [ZKRow R] (A : AdversaryRO R Sizes.labelRows) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionR A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameR A leanPIR leanPSR b₁ b₂) - pr _ (realGameR A leanPIR leanPSR b₁' b₂')| ≤
      4 * ZKRow.εz R pI q3 (q5 + 1872) (qE + 13821) +
        4 * ZKRow.εz R pS q3 (q5 + 1872) (qE + 13821) +
        4 * (1 / 2 ^ 110 + ZKRow.εz R pS 0 312 4607) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  refine (unlinkabilityRO_leanG A hA hhide b₁ b₂ b₁' b₂').trans (le_trans (add_le_add (add_le_add
    (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left (deltaI1R_le A) (by norm_num)))
    (add_le_add (deltaS1R_le A b₁) (deltaS1R_le A b₁')))
    (add_le_add (deltaS2R_le A b₁ b₂) (deltaS2R_le A b₁' b₂'))) le_rfl) (le_of_eq ?_))
  generalize (2 : ℝ) ^ 1024 = K
  ring

/-- **Theorem 2 with the Lean prover, in the random-oracle and ideal-cipher model, with every
term explicit.** As `unlinkabilityRO_lean`, with the programming-collision terms bounded: any two
worlds differ by at most

    8·εRO(q₃, q₅ + 1872, q_E + 13821) + 4·(2⁻¹¹⁰ + εRO(0, 312, 4607)) + 6·noHitProb
      + 12·2⁻¹⁰²⁴ + 2·εhide.

(`unlinkabilityRO_lean_numG` at function rows.) -/
theorem unlinkabilityRO_lean_num (A : AdversaryRO (Blk → Blk) Sizes.labelRows) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionR A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameR A leanPIR leanPSR b₁ b₂) - pr _ (realGameR A leanPIR leanPSR b₁' b₂')| ≤
      8 * εRO q3 (q5 + 1872) (qE + 13821) + 4 * (1 / 2 ^ 110 + εRO 0 312 4607) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  (unlinkabilityRO_lean_numG A hA hhide b₁ b₂ b₁' b₂').trans (le_of_eq (by
    rw [ZKRow.εz_fn, ZKRow.εz_fn]
    generalize (2 : ℝ) ^ 1024 = K
    ring))

end VoleMole.Privacy.Ratatouille
