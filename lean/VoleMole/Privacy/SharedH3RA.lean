import VoleMole.Privacy.SharedH3RO
import VoleMole.Privacy.PermRA
import VoleMole.ZK.SharedH3RA

/-!
# Moussaka and Ratatouille privacy with one shared `H₃`, the interaction reading the tables

`Privacy/SharedH3RO.lean` for the games of `Privacy/MoussakaRA.lean` and
`Privacy/RatatouilleRA.lean`, where the adversary's interaction reads the tables before it picks
the redemption and spend statements. With one shared `H₃` the interaction can read `H₃` at the
prefix of a proof that has not run yet (it knows its own future Anchor Sets, digests and amounts,
and an unbounded one may know the Client's `r` from the commitment): the column the proof will use
is fixed before its statement is, and has been read.

* **The adversary of the shared model** reads the tables only: its interaction and its guess read
  no slot slice (`IBudget 0 i₂ i₅ i_E`, `GBudget 0 q₅ q_E`); it reads `H₃` through the rows of the
  shared tables, like the cipher (`i_E`, `q_E` count both).
* **The redemption and spend hops** use `ZK.Sim.ZeroKnowledgeROA.shared`: after the proof's column
  is exchanged with an independent slice off the rows the interaction read (a measure-preserving
  involution that keeps the interaction's view), the real proof reads a fresh slice unless its
  fresh `ρ` is one of those rows: `≤ (i_E + 9214)·2⁻¹²⁸` per hop (Moussaka; Ratatouille: the
  stage budgets). The collision terms move the same way (`ZK.Sim.pr_h3At_sliceA`), at the same
  cost. The issuance hops (statements fixed by the coins) use `ZeroKnowledgeRO.shared`.
* **No prefix-collision term**, as in the slice-free hops of `Privacy/SharedH3RO.lean`.

**`anonymityRASh_numG`** (Moussaka): for every adversary whose interaction and guess read the tables
only,

    4·εz(pI; q_E + i_E + 13824, q₅ + i₅ + 1872, q_E + i_E + 13824)
      + 4·εAdG(pR; 9; q_E + 13822, q₅ + 1248, q_E + 13822; 0, i₂, i₅ + 624, i_E + 9214)
      + 4·(2⁻¹¹⁰ + εP(pR; 0, 312, 4607; i₅ + 624, i_E + 9214)) + 8·(i_E + 9214)·2⁻¹²⁸
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

**`unlinkabilityRASh_numG`** (Ratatouille): see its statement. Function rows (`_num`) and
permutation rows (`_num_perm`) are instances.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy

open VoleMole.ZK.Sim

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Verifier VoleMole.Verifier.Bridge

attribute [local irreducible] com UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [Inhabited R] [CipherRow R]

lemma blk16_ofFn (ρ : Coins 16) : blk 16 (toBA (List.ofFn ρ)) = ρ := by
  rw [toBA_ofFn, blk_ba]

omit [Fintype R] [Nonempty R] [Inhabited R] in
@[simp] lemma leanPR_withH (w : Bytes) (x : RedeemInstance) (rho : Bytes) (G : Tab3)
    (s : ShM (RowH R)) (E : Blk → H3Row) : leanPR w x rho G (withH s E) = leanPR w x rho G s :=
  congrArg (fun o : Except String ByteArray => toL (o.toOption.getD .empty))
    (realROb_withH (p := pR) _ _ _ _ _ s E)

omit [Fintype R] [Nonempty R] [Inhabited R] in
lemma redeemRequestOf_congr {N N' : NIZK RedeemInstance} (tok : Token) (an : AnchorSet) (i : ℕ)
    (ci cr cd rho : Bytes) (h : ∀ w x, N.prove w x rho = N'.prove w x rho) :
    redeemRequestOf N tok an i ci cr cd rho = redeemRequestOf N' tok an i ci cr cd rho := by
  unfold redeemRequestOf
  split
  · rfl
  · split <;> simp only [h]

omit [Fintype R] [Nonempty R] [Inhabited R] in
lemma redRealRO_g3 (A' : AdversaryRO (RowH R)) (ρ : Coins proveSeedBytes) {G G' : Tab3}
    (p : RedeemPt) (s : ShM (RowH R)) (h : G ρ = G' ρ) :
    (redRealRO A' leanPR (ρ, G)).out p s = (redRealRO A' leanPR (ρ, G')).out p s :=
  redeemRequestOf_congr _ _ _ _ _ _ _ fun w x =>
    leanPR_g3 w x (List.ofFn ρ) s (by rw [blk16_ofFn]; exact h)

omit [Fintype R] [Nonempty R] [Inhabited R] in
@[simp] lemma redRealRO_withH (A' : AdversaryRO (RowH R)) (x : TRr) (p : RedeemPt)
    (s : ShM (RowH R)) (E : Blk → H3Row) :
    (redRealRO A' leanPR x).out p (withH s E) = (redRealRO A' leanPR x).out p s := by
  simp only [redRealRO, nizkAt, leanPR_withH]

/-- **Adaptive zero knowledge of the redemption prover with one shared `H₃`**
(`ZeroKnowledgeROA.shared`): readers and distinguishers that do not read the slot slices, error
`εAdG(pR; 9; q_E, q₅, q_E; 0, s₂, s₅, s_E) + s_E·2⁻¹²⁸`. -/
theorem leanPRSh_zkROA [ZKPRow R] (a c s2 s5 sE : ℕ) : ZeroKnowledgeROA RedeemRelW
    (fun x w (ρ : Coins proveSeedBytes) g (s : ShM (RowH R)) => leanPRSh w x (List.ofFn ρ) g s)
    (leanSim pR) leanProgR (fun _ Sx => SReads pR Sx 0 s2 s5 sE) (Budget pR 0 a c)
    (εAdG (RowH R) pR pR.qsDegree c a c 0 s2 s5 sE + sE / 2 ^ 128) :=
  ZeroKnowledgeROA.shared (p := pR)
    (P := fun x w (ρ : Bytes 16) g (s : ShM (RowH R)) => leanPR w x (List.ofFn ρ) g s)
    (fun x w => keyR w x) (fun _ _ _ _ _ _ => leanPR_withH _ _ _ _ _ _)
    (fun x w _ r G G' s h => leanPR_g3 w x (List.ofFn r) s (by rw [blk16_ofFn]; exact h))
    (fun _ _ _ _ => rfl) (leanPR_zkROA (R := RowH R) c a c 0 s2 s5 sE)

variable (A : AdversaryRA (RowH R)) (idx : AnchorSet → UOVKey → ℕ)

/-- **The real game with one shared `H₃` and a table-reading interaction.** -/
def realGameRASh (b : Bool) : ((TIr × TIr) × (TRr × TRr)) × ShM (RowH R) → Prop :=
  realGameRA A idx leanPISh leanPRSh b

/-- The prefix of side `side`'s redemption at the transcript `x`. -/
noncomputable def keyA {α : Type} (b side : Bool) (γ : (TIs (SimCoins pI) × TIs (SimCoins pI)) × α)
    (x : Trans) : Pre :=
  keyR (wROf A.ctxRO (ptA (A := A) (idx := idx) (leanSim pI) b γ x side))
    (xROf A.ctxRO (ptA (A := A) (idx := idx) (leanSim pI) b γ x side))

lemma PA_sh {α : Type} (b side : Bool) (γ : (TIs (SimCoins pI) × TIs (SimCoins pI)) × α) (x : Trans)
    (ρ : Coins proveSeedBytes) (g : Tab3) (s : ShM (RowH R)) :
    PA (A := A) (idx := idx) (leanSim pI) leanPRSh b side γ x ρ g s =
      PA (A := A) (idx := idx) (leanSim pI) leanPR b side γ x ρ (h3At s (keyA A idx b side γ x)) s := by
  unfold PA
  split
  · exact redRealRO_sh A.ctxRO (ρ, g) _ s
  · rfl

lemma PA_g3 {α : Type} (b side : Bool) (γ : (TIs (SimCoins pI) × TIs (SimCoins pI)) × α) (x : Trans)
    (ρ : Coins proveSeedBytes) {G G' : Tab3} (s : ShM (RowH R)) (h : G ρ = G' ρ) :
    PA (A := A) (idx := idx) (leanSim pI) leanPR b side γ x ρ G s =
      PA (A := A) (idx := idx) (leanSim pI) leanPR b side γ x ρ G' s := by
  unfold PA
  split
  · exact redRealRO_g3 A.ctxRO ρ _ s h
  · rfl

lemma PA_withH {α : Type} (b side : Bool) (γ : (TIs (SimCoins pI) × TIs (SimCoins pI)) × α)
    (x : Trans) (ρ : Coins proveSeedBytes) (G : Tab3) (s : ShM (RowH R)) (E : Blk → H3Row) :
    PA (A := A) (idx := idx) (leanSim pI) leanPR b side γ x ρ G (withH s E) =
      PA (A := A) (idx := idx) (leanSim pI) leanPR b side γ x ρ G s := by
  unfold PA
  split
  · exact redRealRO_withH A.ctxRO _ _ s E
  · rfl

omit [Inhabited R] in
@[simp] lemma PIOf_withH {α : Type} (A' : AdversaryRO (RowH R))
    (γ : (TIs (SimCoins pI) × TIs (SimCoins pI)) × α) (s : ShM (RowH R)) (E : Blk → H3Row) :
    PIOf A' leanProgI γ (withH s E) = withH (PIOf A' leanProgI γ s) E := rfl

omit [Inhabited R] in
@[simp] lemma h3At_PIOf {α : Type} (A' : AdversaryRO (RowH R))
    (γ : (TIs (SimCoins pI) × TIs (SimCoins pI)) × α) (s : ShM (RowH R)) (k : Pre) :
    h3At (PIOf A' leanProgI γ s) k = h3At s k := rfl

@[simp] lemma LRA_withH (b : Bool) (γ : ΓR (SimCoins pI) (SimCoins pR)) (x : Trans)
    (s : ShM (RowH R)) (E : Blk → H3Row) :
    LRA (A := A) (idx := idx) (leanSim pI) leanProgI leanProgR b γ x (withH s E) =
      withH (LRA (A := A) (idx := idx) (leanSim pI) leanProgI leanProgR b γ x s) E := by
  unfold LRA progA
  split <;> rfl

@[simp] lemma h3At_LRA (b : Bool) (γ : ΓR (SimCoins pI) (SimCoins pR)) (x : Trans)
    (s : ShM (RowH R)) (k : Pre) :
    h3At (LRA (A := A) (idx := idx) (leanSim pI) leanProgI leanProgR b γ x s) k = h3At s k := by
  unfold LRA progA
  split <;> rfl

theorem deltaLA_sh {i2 i5 iE : ℕ} (hI : A.IBudget 0 i2 i5 iE) (b : Bool) :
    deltaLA (A := A) (idx := idx) (simI := leanSim pI) (progI := leanProgI) (PR := leanPRSh) b ≤
      deltaLA (A := A) (idx := idx) (simI := leanSim pI) (progI := leanProgI) (PR := leanPR) b +
        (iE + 4607 + 4607 : ℕ) / 2 ^ 128 := by
  have h := pr_h3At_sliceA (R := R) (p := pI) (Γ := ΓL (SimCoins pI))
    (fun γ => SxL (A := A) (leanSim pI) leanProgI γ) (sReads_SxL A hI)
    (fun γ x => keyA A idx b false γ x)
    (fun γ x ρ G s => PA (A := A) (idx := idx) (leanSim pI) leanPR b false γ x ρ G
        (PIOf A.ctxRO leanProgI γ s) ≠ PA (A := A) (idx := idx) (leanSim pI) leanPR b false γ x ρ G s)
    (fun γ x ρ G G' s h => by rw [PA_g3 A idx b false γ x ρ _ h, PA_g3 A idx b false γ x ρ s h])
    (fun γ x ρ G s E => by rw [PIOf_withH, PA_withH, PA_withH])
  unfold deltaLA
  simp only [PA_sh, h3At_PIOf]
  exact sub_le_iff_le_add'.1 (abs_le.1 h).2

theorem deltaRA_sh {i2 i5 iE : ℕ} (hI : A.IBudget 0 i2 i5 iE) (b : Bool) :
    deltaRA (A := A) (idx := idx) (simI := leanSim pI) (progI := leanProgI) (progR := leanProgR)
        (PR := leanPRSh) b ≤
      deltaRA (A := A) (idx := idx) (simI := leanSim pI) (progI := leanProgI) (progR := leanProgR)
        (PR := leanPR) b + (iE + 4607 + 4607 : ℕ) / 2 ^ 128 := by
  have h := pr_h3At_sliceA (R := R) (p := pI) (Γ := ΓR (SimCoins pI) (SimCoins pR))
    (fun γ => SxR (A := A) (leanSim pI) leanProgI γ) (sReads_SxR A hI)
    (fun γ x => keyA A idx b true γ x)
    (fun γ x ρ G s => PA (A := A) (idx := idx) (leanSim pI) leanPR b true γ x ρ G
        (LRA (A := A) (idx := idx) (leanSim pI) leanProgI leanProgR b γ x s) ≠
      PA (A := A) (idx := idx) (leanSim pI) leanPR b true γ x ρ G s)
    (fun γ x ρ G G' s h => by rw [PA_g3 A idx b true γ x ρ _ h, PA_g3 A idx b true γ x ρ s h])
    (fun γ x ρ G s E => by rw [LRA_withH, PA_withH, PA_withH])
  unfold deltaRA
  simp only [PA_sh, h3At_LRA]
  exact sub_le_iff_le_add'.1 (abs_le.1 h).2

/-- **Theorem 4(a) with one shared `H₃` and an interaction that reads the tables, every term
explicit, for every type of cipher rows** (`ZKRow R`, `ZKPRow R`). The interaction and the guess
read the tables (rows: the cipher and `H₃`; `H₅`; `H₂³` for the interaction) and no slot slice.
Then the two worlds differ by at most

    4·εz(pI; q_E + i_E + 13824, q₅ + i₅ + 1872, q_E + i_E + 13824)
      + 4·εAdG(pR; 9; q_E + 13822, q₅ + 1248, q_E + 13822; 0, i₂, i₅ + 624, i_E + 9214)
      + 4·(2⁻¹¹⁰ + εP(pR; 0, 312, 4607; i₅ + 624, i_E + 9214)) + 8·(i_E + 9214)·2⁻¹²⁸
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide. -/
theorem anonymityRASh_numG [ZKRow R] [ZKPRow R] {q5 qE i2 i5 iE : ℕ} {εhide : ℝ}
    (hA : A.GBudget 0 q5 qE) (hI : A.IBudget 0 i2 i5 iE)
    (hhide : ∀ b c, hidingAdv A.ctxRO.base.ci A.ctxRO.base.cr
      (reductionRA A idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRASh A idx false) - pr _ (realGameRASh A idx true)| ≤
      4 * ZKRow.εz R pI (qE + iE + 13824) (q5 + i5 + 1872) (qE + iE + 13824) +
        4 * εAdG R pR 9 (qE + 13822) (q5 + 1248) (qE + 13822) 0 i2 (i5 + 624) (iE + 9214) +
        4 * (1 / 2 ^ 110 + ZKPRow.εP R pR 0 312 4607 (i5 + 624) (iE + 9214)) +
        8 * ((iE + 9214 : ℕ) / 2 ^ 128) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  have h := anonymityRA (A := A) (idx := idx) (PI := leanPISh) (PR := leanPRSh) (simI := leanSim pI)
    (simR := leanSim pR) (progI := leanProgI) (progR := leanProgR)
    (εI := fun a c => ZKRow.εz R pI c a c)
    (εR := fun a c => εAdG (RowH R) pR pR.qsDegree c a c 0 i2 (i5 + 312 + 312) (iE + 4607 + 4607) +
      (iE + 4607 + 4607 : ℕ) / 2 ^ 128)
    (AdmS := fun _ Sx => SReads pR Sx 0 i2 (i5 + 312 + 312) (iE + 4607 + 4607))
    hA hI leanPISh_rd5 leanPISh_rdE leanPRSh_rd5 leanPRSh_rdE (fun x c => progRO_isProg c)
    (fun x c => progRO_isProg c) (sReads_SxL A hI) (sReads_SxR A hI)
    (fun a c => leanPISh_zkRO (0 + 0) a c)
    (fun a c => leanPRSh_zkROA a c i2 (i5 + 312 + 312) (iE + 4607 + 4607)) hhide
  beta_reduce at h
  rw [deltaI1_sh] at h
  have d1 := deltaI1_le (R := RowH R) A.ctxRO
  have sL0 := deltaLA_sh A idx hI false
  have sL1 := deltaLA_sh A idx hI true
  have sR0 := deltaRA_sh A idx hI false
  have sR1 := deltaRA_sh A idx hI true
  have dL0 := deltaLA_le A idx hI false
  have dL1 := deltaLA_le A idx hI true
  have dR0 := deltaRA_le A idx hI false
  have dR1 := deltaRA_le A idx hI true
  have mI : ∀ a c, a ≤ q5 + i5 + 1872 → c ≤ qE + iE + 13824 →
      ZKRow.εz R pI c a c ≤ ZKRow.εz R pI (qE + iE + 13824) (q5 + i5 + 1872) (qE + iE + 13824) :=
    fun a c ha hc => ZKRow.εz_mono pI hc ha hc
  have mR : ∀ a c, a ≤ q5 + 1248 → c ≤ qE + 13822 →
      εAdG (RowH R) pR pR.qsDegree c a c 0 i2 (i5 + 312 + 312) (iE + 4607 + 4607) ≤
        εAdG R pR 9 (qE + 13822) (q5 + 1248) (qE + 13822) 0 i2 (i5 + 624) (iE + 9214) :=
    fun a c ha hc => εAdG_mono (R := R) pR hc ha hc le_rfl le_rfl (by omega) (by omega)
  have m1 := mI (624 + (i5 + (624 + 624 + q5))) ((4607 + 1) + (iE + ((4607 + 1) + (4607 + 1) + qE)))
    (by omega) (by omega)
  have m2 := mI (i5 + (624 + 624 + q5) + 312) (iE + ((4607 + 1) + (4607 + 1) + qE) + 4607) (by omega)
    (by omega)
  have m3 := mR (0 + 624 + q5 + (312 + 312)) (0 + (4607 + 1) + qE + (4607 + 4607)) (by omega)
    (by omega)
  have m4 := mR (0 + 0 + q5 + (312 + (312 + 312))) (0 + 0 + qE + (4607 + (4607 + 4607))) (by omega)
    (by omega)
  have e1 : ZKPRow.εP (RowH R) pR 0 312 4607 (i5 + 312 + 312) (iE + 4607 + 4607) =
      ZKPRow.εP R pR 0 312 4607 (i5 + 624) (iE + 9214) := by
    rw [ZKPRow.εP_rowH, show i5 + 312 + 312 = i5 + 624 by omega,
      show iE + 4607 + 4607 = iE + 9214 by omega]
  have e2 : ((iE + 4607 + 4607 : ℕ) : ℝ) / 2 ^ 128 = ((iE + 9214 : ℕ) : ℝ) / 2 ^ 128 := by
    rw [show iE + 4607 + 4607 = iE + 9214 by omega]
  rw [e1] at dL0 dL1 dR0 dR1
  rw [e2] at sL0 sL1 sR0 sR1
  unfold realGameRASh
  refine h.trans ?_
  rw [e2]
  have z : ((0 : ℕ) : ℝ) / 2 ^ 128 = 0 := by simp
  rw [z] at dL0 dL1 dR0 dR1
  rw [div_eq_mul_one_div (2 : ℝ) ((2 : ℝ) ^ 1024)] at dL0 dL1
  rw [div_eq_mul_one_div (3 : ℝ) ((2 : ℝ) ^ 1024)] at dR0 dR1
  rw [div_eq_mul_one_div (12 : ℝ) ((2 : ℝ) ^ 1024)]
  generalize (1 : ℝ) / 2 ^ 1024 = κ at d1 dL0 dL1 dR0 dR1 ⊢
  linarith

/-- **Theorem 4(a) with one shared `H₃` and a table-reading interaction, function rows.** -/
theorem anonymityRASh_num (A : AdversaryRA (RowH (Blk → Blk))) (idx : AnchorSet → UOVKey → ℕ)
    {q5 qE i2 i5 iE : ℕ} {εhide : ℝ} (hA : A.GBudget 0 q5 qE) (hI : A.IBudget 0 i2 i5 iE)
    (hhide : ∀ b c, hidingAdv A.ctxRO.base.ci A.ctxRO.base.cr
      (reductionRA A idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRASh A idx false) - pr _ (realGameRASh A idx true)| ≤
      4 * εRO (qE + iE + 13824) (q5 + i5 + 1872) (qE + iE + 13824) +
        4 * εAd 9 (qE + 13822) (q5 + 1248) (qE + 13822) 0 i2 (i5 + 624) (iE + 9214) +
        4 * (1 / 2 ^ 110 + εROP 0 312 4607 (i5 + 624) (iE + 9214)) +
        8 * ((iE + 9214 : ℕ) / 2 ^ 128) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityRASh_numG A idx hA hI hhide

/-- **Theorem 4(a) with one shared `H₃` and a table-reading interaction, AES as uniformly random
permutations.** -/
theorem anonymityRASh_num_perm (A : AdversaryRA (RowH (Equiv.Perm Blk)))
    (idx : AnchorSet → UOVKey → ℕ) {q5 qE i2 i5 iE : ℕ} {εhide : ℝ} (hA : A.GBudget 0 q5 qE)
    (hI : A.IBudget 0 i2 i5 iE)
    (hhide : ∀ b c, hidingAdv A.ctxRO.base.ci A.ctxRO.base.cr
      (reductionRA A idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRASh A idx false) - pr _ (realGameRASh A idx true)| ≤
      4 * εROPm pI (qE + iE + 13824) (q5 + i5 + 1872) (qE + iE + 13824) +
        4 * εAdPm pR 9 (qE + 13822) (q5 + 1248) (qE + 13822) 0 i2 (i5 + 624) (iE + 9214) +
        4 * (1 / 2 ^ 110 + εROPmP pR 0 312 4607 (i5 + 624) (iE + 9214)) +
        8 * ((iE + 9214 : ℕ) / 2 ^ 128) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityRASh_numG A idx hA hI hhide

end Moussaka

namespace Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.Verifier VoleMole.Verifier.Bridge

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

lemma blk16_vec (ρ : Coins 16) : blk 16 (bOf (vec ρ)) = ρ := by
  rw [bOf_vec, blk_ba]

omit [Fintype R] [Nonempty R] in
@[simp] lemma leanPSR_withH (x : SpendInstance) (w : SpendWitness) (ρ : Rho) (G : Tab3)
    (s : ShR (RowH R)) (E : Blk → H3Row) : leanPSR x w ρ G (withH s E) = leanPSR x w ρ G s :=
  congrArg (vecOf _) (realROb_withH (p := pS) _ _ _ _ _ s E)

omit [Fintype R] [Nonempty R] in
lemma spRealR_g3 (A' : AdversaryRO (RowH R) Sizes.labelRows) (n : NRR) (ρ : Coins 16) {G G' : Tab3}
    (τ : TokenS) (d : Credits) (s : ShR (RowH R)) (h : G ρ = G' ρ) :
    (spRealR A' leanPSR (n, (ρ, G))).out τ d s = (spRealR A' leanPSR (n, (ρ, G'))).out τ d s :=
  congrArg (fun r : Option TokenS × Except Error (PendingSpendS × SpendRequest Sizes.labelRows) =>
    spOutOf A'.base r.2) (spendOf_congr _ _ _ _ _ _ _ _ _ fun t' _ => by
      simp only [primS_proveSpend]
      exact leanPSR_g3 _ _ _ s (by rw [blk16_vec]; exact h))

omit [Fintype R] [Nonempty R] in
@[simp] lemma spRealR_withH (A' : AdversaryRO (RowH R) Sizes.labelRows) (x : TRe) (τ : TokenS)
    (d : Credits) (s : ShR (RowH R)) (E : Blk → H3Row) :
    (spRealR A' leanPSR x).out τ d (withH s E) = (spRealR A' leanPSR x).out τ d s := by
  simp only [spRealR, primS, leanPSR_withH]

/-- A ZK-A statement with error `1` holds for every prover and simulator. -/
lemma ZeroKnowledgeROA.of_one {I W ρT C G S O : Type*} [Fintype ρT] [Fintype C] [Fintype G]
    [Fintype S] (Rl : I → W → Prop) (prove : I → W → ρT → G → S → O) (sim : I → C → O)
    (prog : I → C → S → S) (AdmS : (X : Type) → (G × S → X) → Prop)
    (Adm : (O → G → S → Prop) → Prop) : ZeroKnowledgeROA Rl prove sim prog AdmS Adm 1 := by
  intro X Sx stw _ _ dummy D _
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · linarith [pr_le_one (α := ρT × (G × S)) (fun z => D (Sx z.2)
      (outReal stw prove dummy (Sx z.2) z.1 z.2.1 z.2.2) z.2.1 z.2.2),
      pr_nonneg (α := C × (G × S)) (fun z => D (Sx z.2) (outSim stw sim dummy (Sx z.2) z.1) z.2.1
        (progSim stw prog (Sx z.2) z.1 z.2.2))]
  · linarith [pr_nonneg (α := ρT × (G × S)) (fun z => D (Sx z.2)
      (outReal stw prove dummy (Sx z.2) z.1 z.2.1 z.2.2) z.2.1 z.2.2),
      pr_le_one (α := C × (G × S)) (fun z => D (Sx z.2) (outSim stw sim dummy (Sx z.2) z.1) z.2.1
        (progSim stw prog (Sx z.2) z.1 z.2.2))]

/-- **Adaptive zero knowledge of the spend prover with one shared `H₃`**, against slice-blind
readers and distinguishers. -/
theorem leanPSRSh_zkROA [ZKPRow R] (b c s2 s5 sE : ℕ) : ZeroKnowledgeROA SpendRel
    (fun x w (ρ : Coins 16) g (s : ShR (RowH R)) => leanPSRSh x w (vec ρ) g s) leanSimSR leanProgSR
    (fun _ Sx => SReads pS Sx 0 s2 s5 sE) (Budget pS 0 b c)
    (εAdG (RowH R) pS pS.qsDegree c b c 0 s2 s5 sE + sE / 2 ^ 128) :=
  ZeroKnowledgeROA.shared (p := pS)
    (P := fun x w (ρ : ZK.Sim.Bytes 16) g (s : ShR (RowH R)) => leanPSR x w (vec ρ) g s)
    keySR (fun _ _ _ _ _ _ => leanPSR_withH _ _ _ _ _ _)
    (fun x w _ r G G' s h => leanPSR_g3 x w (vec r) s (by rw [blk16_vec]; exact h))
    (fun _ _ _ _ => rfl) (leanPSR_zkROA (R := RowH R) c b c 0 s2 s5 sE)

/-- `leanPSRSh_zkROA` at every slice budget (error `1` where the slice is read). -/
theorem leanPSRSh_zkROA' [ZKPRow R] (s2 s5 sE : ℕ) (a b c : ℕ) : ZeroKnowledgeROA SpendRel
    (fun x w (ρ : Coins 16) g (s : ShR (RowH R)) => leanPSRSh x w (vec ρ) g s) leanSimSR leanProgSR
    (fun _ Sx => SReads pS Sx 0 s2 s5 sE) (Budget pS a b c)
    (if a = 0 then εAdG (RowH R) pS pS.qsDegree c b c 0 s2 s5 sE + sE / 2 ^ 128 else 1) := by
  split_ifs with ha
  · subst ha
    exact leanPSRSh_zkROA b c s2 s5 sE
  · exact ZeroKnowledgeROA.of_one _ _ _ _ _ _

variable (A : AdversaryRA (RowH R) Sizes.labelRows)

/-- **The real game with one shared `H₃` and a table-reading Issuer.** -/
def realGameRASh (b₁ b₂ : Bool) : ((TRe × TRe) × (TRe × TRe)) × ShR (RowH R) → Prop :=
  realGameRA A leanPIRSh leanPSRSh b₁ b₂

lemma PS1_sh (b₁ : Bool) (γ : ΓS1 (SimCoins pI)) (x : M₁) (ρ : Coins 16) (g : Tab3)
    (s : ShR (RowH R)) :
    PS1 A leanSimIR leanPSRSh b₁ γ x ρ g s =
      PS1 A leanSimIR leanPSR b₁ γ x ρ (h3At s (spKey A.toRO (τ1A A leanSimIR b₁ γ.1 x) x.2 γ.1.2)) s :=
  spRealR_sh A.toRO (γ.1.2, (ρ, g)) _ _ s

lemma PS2_sh (b₁ b₂ : Bool) (γ : ΓS2 (SimCoins pI) (SimCoins pS)) (x : MsgR) (ρ : Coins 16)
    (g : Tab3) (s : ShR (RowH R)) :
    PS2 A leanSimIR leanSimSR leanPSRSh b₁ b₂ γ x ρ g s =
      PS2 A leanSimIR leanSimSR leanPSR b₁ b₂ γ x ρ (h3At s (spKey A.toRO
        (τ₂R (A.fixR x) leanSimIR leanSimSR b₁ b₂ γ) (d₂R (A.fixR x) leanSimIR leanSimSR b₁ γ) γ.2)) s :=
  spRealR_sh A.toRO (γ.2, (ρ, g)) _ _ s

omit [Nonempty R] in
@[simp] lemma PIR_withH {Z : Sizes} (A' : AdversaryRO (RowH R) Z) (n : NRR) (c : SimCoins pI)
    (s : ShR (RowH R)) (E : Blk → H3Row) :
    PIR A' leanProgIR n c (withH s E) = withH (PIR A' leanProgIR n c s) E := by
  unfold PIR
  split <;> rfl

theorem deltaS1A_sh {i2 i5 iE : ℕ} (hI : A.IBudget 0 i2 i5 iE) (b₁ : Bool) :
    deltaS1A A leanSimIR leanProgIR leanPSRSh b₁ ≤
      deltaS1A A leanSimIR leanProgIR leanPSR b₁ + (iE + 4607 + 4607 : ℕ) / 2 ^ 128 := by
  have h := pr_h3At_sliceA (R := R) (p := pI) (Γ := ΓS1 (SimCoins pI))
    (fun γ => Sx1 A leanSimIR leanProgIR γ) (sReads_Sx1 A hI)
    (fun γ x => spKey A.toRO (τ1A A leanSimIR b₁ γ.1 x) x.2 γ.1.2)
    (fun γ x ρ G s => PS1 A leanSimIR leanPSR b₁ γ x ρ G (PI2R A.toRO leanProgIR γ.1 s) ≠
      PS1 A leanSimIR leanPSR b₁ γ x ρ G s)
    (fun γ x ρ G G' s h => by
      simp only [PS1]
      rw [spRealR_g3 A.toRO γ.1.2 ρ _ _ _ h, spRealR_g3 A.toRO γ.1.2 ρ _ _ s h])
    (fun γ x ρ G s E => by
      simp only [PS1, PI2R, PIR_withH, spRealR_withH])
  unfold deltaS1A
  simp only [PS1_sh, PI2R, h3At_PIR]
  exact sub_le_iff_le_add'.1 (abs_le.1 h).2

omit [Nonempty R] in
lemma PI2R_withH {α : Type} (A' : AdversaryRO (RowH R) Sizes.labelRows)
    (γ : (TIsR (SimCoins pI) × TIsR (SimCoins pI)) × α) (s : ShR (RowH R)) (E : Blk → H3Row) :
    PI2R A' leanProgIR γ (withH s E) = withH (PI2R A' leanProgIR γ s) E := by
  simp only [PI2R, PIR_withH]

omit [Fintype R] [Nonempty R] in
lemma ite_progSR_withH (c : Prop) [Decidable c] (x : SpendInstance) (k : SimCoins pS)
    (s : ShR (RowH R)) (E : Blk → H3Row) :
    (if c then leanProgSR x k (withH s E) else withH s E) =
      withH (if c then leanProgSR x k s else s) E := by
  split <;> rfl

omit [Nonempty R] in
lemma LS2R_withH (A' : AdversaryRO (RowH R) Sizes.labelRows) (b₁ : Bool)
    (γ : ((TIsR (SimCoins pI) × TIsR (SimCoins pI)) × TSsR (SimCoins pS)) × NRR)
    (s : ShR (RowH R)) (E : Blk → H3Row) :
    LS2R A' leanSimIR leanProgIR leanProgSR b₁ γ (withH s E) =
      withH (LS2R A' leanSimIR leanProgIR leanProgSR b₁ γ s) E := by
  unfold LS2R
  rw [ite_progSR_withH, PI2R_withH]

omit [Nonempty R] in
@[simp] lemma h3At_LS2R' (A' : AdversaryRO (RowH R) Sizes.labelRows) (b₁ : Bool)
    (γ : ((TIsR (SimCoins pI) × TIsR (SimCoins pI)) × TSsR (SimCoins pS)) × NRR)
    (s : ShR (RowH R)) (k : Pre) :
    h3At (LS2R A' leanSimIR leanProgIR leanProgSR b₁ γ s) k = h3At s k := by
  unfold LS2R
  split <;> simp only [PI2R, h3At_PIR, h3At_leanProgSR]

theorem deltaS2A_sh {i2 i5 iE : ℕ} (hI : A.IBudget 0 i2 i5 iE) (b₁ b₂ : Bool) :
    deltaS2A A leanSimIR leanSimSR leanProgIR leanProgSR leanPSRSh b₁ b₂ ≤
      deltaS2A A leanSimIR leanSimSR leanProgIR leanProgSR leanPSR b₁ b₂ +
        (2 * iE + 23035 : ℕ) / 2 ^ 128 := by
  have hS : ∀ γ, SReads pS (Sx2 A leanSimIR leanSimSR leanProgIR leanProgSR b₁ γ) 0 (2 * i2)
      (2 * i5 + 1560) (2 * iE + 23035) := fun γ =>
    (sReads_Sx2 A hI b₁ γ).mono (by omega) le_rfl le_rfl le_rfl
  have h := pr_h3At_sliceA (R := R) (p := pI) (Γ := ΓS2 (SimCoins pI) (SimCoins pS))
    (fun γ => Sx2 A leanSimIR leanSimSR leanProgIR leanProgSR b₁ γ) hS
    (fun γ x => spKey A.toRO (τ₂R (A.fixR x) leanSimIR leanSimSR b₁ b₂ γ)
      (d₂R (A.fixR x) leanSimIR leanSimSR b₁ γ) γ.2)
    (fun γ x ρ G s => PS2 A leanSimIR leanSimSR leanPSR b₁ b₂ γ x ρ G
        (LS2R (A.fixR x) leanSimIR leanProgIR leanProgSR b₁ γ s) ≠
      PS2 A leanSimIR leanSimSR leanPSR b₁ b₂ γ x ρ G s)
    (fun γ x ρ G G' s h => by
      simp only [PS2]
      rw [spRealR_g3 A.toRO γ.2 ρ _ _ _ h, spRealR_g3 A.toRO γ.2 ρ _ _ s h])
    (fun γ x ρ G s E => by
      simp only [PS2, LS2R_withH, spRealR_withH])
  unfold deltaS2A
  simp only [PS2_sh, h3At_LS2R']
  exact sub_le_iff_le_add'.1 (abs_le.1 h).2

/-- **Theorem 2 with one shared `H₃` and a table-reading Issuer, every term explicit, for every type
of cipher rows** (`ZKRow R`, `ZKPRow R`): each stage of the Issuer's interaction and its guess read
the tables (rows: the cipher and `H₃`) and no slot slice. Any two worlds differ by at most

    4·εz(pI; q_E + 2i_E + 13824, q₅ + 2i₅ + 1872, q_E + 2i_E + 13824)
      + 2·εAdG(pS; 9; q_E + i_E + 13822, q₅ + i₅ + 1248, q_E + i_E + 13822; 0, i₂, i₅ + 624, i_E + 9214)
      + 2·εAdG(pS; 9; q_E + 13821, q₅ + 936, q_E + 13821; 0, 2i₂, 2i₅ + 1560, 2i_E + 23035)
      + 4·(2⁻¹¹⁰ + εP(pS; 0, 312, 4607; 2i₅ + 1560, 2i_E + 23035))
      + 4·(i_E + 9214)·2⁻¹²⁸ + 4·(2i_E + 23035)·2⁻¹²⁸ + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide. -/
theorem unlinkabilityRASh_numG [ZKRow R] [ZKPRow R] {q5 qE i2 i5 iE : ℕ} {εhide : ℝ}
    (hA : A.GBudget 0 q5 qE) (hI : A.IBudget 0 i2 i5 iE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionRA A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRASh A b₁ b₂) - pr _ (realGameRASh A b₁' b₂')| ≤
      4 * ZKRow.εz R pI (qE + 2 * iE + 13824) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13824) +
        2 * εAdG R pS 9 (qE + iE + 13822) (q5 + i5 + 1248) (qE + iE + 13822) 0 i2 (i5 + 624)
          (iE + 9214) +
        2 * εAdG R pS 9 (qE + 13821) (q5 + 936) (qE + 13821) 0 (2 * i2) (2 * i5 + 1560)
          (2 * iE + 23035) +
        4 * (1 / 2 ^ 110 + ZKPRow.εP R pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        4 * ((iE + 9214 : ℕ) / 2 ^ 128) + 4 * ((2 * iE + 23035 : ℕ) / 2 ^ 128) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  have hS2 : ∀ b (γ : ΓS2 (SimCoins pI) (SimCoins pS)),
      SReads pS (Sx2 A leanSimIR leanSimSR leanProgIR leanProgSR b γ) 0 (2 * i2) (2 * i5 + 1560)
        (2 * iE + 23035) := fun b γ => (sReads_Sx2 A hI b γ).mono (by omega) le_rfl le_rfl le_rfl
  have h := unlinkabilityRA (A := A) (PI := leanPIRSh) (PS := leanPSRSh) (simI := leanSimIR)
    (simS := leanSimSR) (progI := leanProgIR) (progS := leanProgSR)
    (εI := fun _ b c => ZKRow.εz R pI c b c)
    (εS₁ := fun a b c => if a = 0 then εAdG (RowH R) pS pS.qsDegree c b c 0 i2 (i5 + 312 + 312)
      (iE + 4607 + 4607) + (iE + 4607 + 4607 : ℕ) / 2 ^ 128 else 1)
    (εS₂ := fun a b c => if a = 0 then εAdG (RowH R) pS pS.qsDegree c b c 0 (2 * i2) (2 * i5 + 1560)
      (2 * iE + 23035) + (2 * iE + 23035 : ℕ) / 2 ^ 128 else 1)
    (AdmS₁ := fun _ Sx => SReads pS Sx 0 i2 (i5 + 312 + 312) (iE + 4607 + 4607))
    (AdmS₂ := fun _ Sx => SReads pS Sx 0 (2 * i2) (2 * i5 + 1560) (2 * iE + 23035))
    hA hI leanPIRSh_rd5 leanPIRSh_rdE leanPSRSh_rd5 leanPSRSh_rdE (fun x c => progRO_isProg c)
    (fun x c => progRO_isProg c) leanProgIR_none leanProgSR_none (sReads_Sx1 A hI) hS2
    (fun a b c => leanPIRSh_zkRO a b c)
    (fun a b c => leanPSRSh_zkROA' _ _ _ a b c) (fun a b c => leanPSRSh_zkROA' _ _ _ a b c)
    (fun a b c => ZKRow.εz_nonneg _ _ _ _) hhide b₁ b₂ b₁' b₂'
  beta_reduce at h
  simp only [show (0 : ℕ) + 0 + 0 = 0 from rfl, ite_true] at h
  rw [deltaI1R_sh] at h
  have d1 := deltaI1R_le (R := RowH R) A.toRO
  have sS1 := deltaS1A_sh A hI b₁
  have sS1' := deltaS1A_sh A hI b₁'
  have sS2 := deltaS2A_sh A hI b₁ b₂
  have sS2' := deltaS2A_sh A hI b₁' b₂'
  have dS1 := deltaS1A_le A hI b₁
  have dS1' := deltaS1A_le A hI b₁'
  have dS2 := deltaS2A_le A hI b₁ b₂
  have dS2' := deltaS2A_le A hI b₁' b₂'
  have mI : ∀ b c, b ≤ q5 + 2 * i5 + 1872 → c ≤ qE + 2 * iE + 13824 →
      ZKRow.εz R pI c b c ≤ ZKRow.εz R pI (qE + 2 * iE + 13824) (q5 + 2 * i5 + 1872)
        (qE + 2 * iE + 13824) := fun b c hb hc => ZKRow.εz_mono pI hc hb hc
  have m1 := mI (0 + (624 + (i5 + (624 + (i5 + (624 + q5))))))
    (0 + ((4607 + 1) + (iE + ((4607 + 1) + (iE + ((4607 + 1) + qE)))))) (by omega) (by omega)
  have m2 := mI (0 + (0 + (i5 + (624 + (i5 + (624 + q5))))) + 312)
    (0 + (0 + (iE + ((4607 + 1) + (iE + ((4607 + 1) + qE))))) + 4607) (by omega) (by omega)
  have m3 : εAdG (RowH R) pS pS.qsDegree (iE + (0 + (0 + (0 + ((4607 + 1) + qE)))) + (4607 + 4607))
      (i5 + (0 + (0 + (0 + (624 + q5)))) + (312 + 312))
      (iE + (0 + (0 + (0 + ((4607 + 1) + qE)))) + (4607 + 4607)) 0 i2 (i5 + 312 + 312)
      (iE + 4607 + 4607) ≤
      εAdG R pS 9 (qE + iE + 13822) (q5 + i5 + 1248) (qE + iE + 13822) 0 i2 (i5 + 624) (iE + 9214) :=
    εAdG_mono (R := R) pS (by omega) (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
  have m4 : εAdG (RowH R) pS pS.qsDegree (0 + (0 + (0 + (0 + qE))) + (4607 + (4607 + 4607)))
      (0 + (0 + (0 + (0 + q5))) + (312 + (312 + 312)))
      (0 + (0 + (0 + (0 + qE))) + (4607 + (4607 + 4607))) 0 (2 * i2) (2 * i5 + 1560)
      (2 * iE + 23035) ≤
      εAdG R pS 9 (qE + 13821) (q5 + 936) (qE + 13821) 0 (2 * i2) (2 * i5 + 1560) (2 * iE + 23035) :=
    εAdG_mono (R := R) pS (by omega) (by omega) (by omega) le_rfl le_rfl le_rfl le_rfl
  have eP : ZKPRow.εP (RowH R) pS 0 312 4607 (i5 + 312 + 312) (iE + 4607 + 4607) ≤
      ZKPRow.εP R pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035) :=
    ZKPRow.εP_mono (R := R) pS le_rfl le_rfl le_rfl (by omega) (by omega)
  have eP' : ZKPRow.εP (RowH R) pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035) =
      ZKPRow.εP R pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035) := rfl
  have e2 : ((iE + 4607 + 4607 : ℕ) : ℝ) / 2 ^ 128 = ((iE + 9214 : ℕ) : ℝ) / 2 ^ 128 := by
    rw [show iE + 4607 + 4607 = iE + 9214 by omega]
  rw [e2] at sS1 sS1'
  rw [eP'] at dS2 dS2'
  have z1 : ((0 : ℕ) : ℝ) / 2 ^ 128 = 0 := by simp
  have z2 : ((2 * 0 : ℕ) : ℝ) / 2 ^ 128 = 0 := by simp
  rw [z1] at dS1 dS1'
  rw [z2] at dS2 dS2'
  unfold realGameRASh
  refine h.trans ?_
  rw [e2]
  rw [div_eq_mul_one_div (2 : ℝ) ((2 : ℝ) ^ 1024)] at dS1 dS1'
  rw [div_eq_mul_one_div (3 : ℝ) ((2 : ℝ) ^ 1024)] at dS2 dS2'
  rw [div_eq_mul_one_div (12 : ℝ) ((2 : ℝ) ^ 1024)]
  generalize (1 : ℝ) / 2 ^ 1024 = κ at d1 dS1 dS1' dS2 dS2' ⊢
  linarith

/-- **Theorem 2 with one shared `H₃` and a table-reading Issuer, function rows.** -/
theorem unlinkabilityRASh_num (A : AdversaryRA (RowH (Blk → Blk)) Sizes.labelRows)
    {q5 qE i2 i5 iE : ℕ} {εhide : ℝ} (hA : A.GBudget 0 q5 qE) (hI : A.IBudget 0 i2 i5 iE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionRA A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRASh A b₁ b₂) - pr _ (realGameRASh A b₁' b₂')| ≤
      4 * εRO (qE + 2 * iE + 13824) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13824) +
        2 * εAd 9 (qE + iE + 13822) (q5 + i5 + 1248) (qE + iE + 13822) 0 i2 (i5 + 624) (iE + 9214) +
        2 * εAd 9 (qE + 13821) (q5 + 936) (qE + 13821) 0 (2 * i2) (2 * i5 + 1560) (2 * iE + 23035) +
        4 * (1 / 2 ^ 110 + εROP 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        4 * ((iE + 9214 : ℕ) / 2 ^ 128) + 4 * ((2 * iE + 23035 : ℕ) / 2 ^ 128) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityRASh_numG A hA hI hhide b₁ b₂ b₁' b₂'

/-- **Theorem 2 with one shared `H₃` and a table-reading Issuer, AES as uniformly random
permutations.** -/
theorem unlinkabilityRASh_num_perm (A : AdversaryRA (RowH (Equiv.Perm Blk)) Sizes.labelRows)
    {q5 qE i2 i5 iE : ℕ} {εhide : ℝ} (hA : A.GBudget 0 q5 qE) (hI : A.IBudget 0 i2 i5 iE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionRA A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRASh A b₁ b₂) - pr _ (realGameRASh A b₁' b₂')| ≤
      4 * εROPm pI (qE + 2 * iE + 13824) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13824) +
        2 * εAdPm pS 9 (qE + iE + 13822) (q5 + i5 + 1248) (qE + iE + 13822) 0 i2 (i5 + 624)
          (iE + 9214) +
        2 * εAdPm pS 9 (qE + 13821) (q5 + 936) (qE + 13821) 0 (2 * i2) (2 * i5 + 1560)
          (2 * iE + 23035) +
        4 * (1 / 2 ^ 110 + εROPmP pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        4 * ((iE + 9214 : ℕ) / 2 ^ 128) + 4 * ((2 * iE + 23035 : ℕ) / 2 ^ 128) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityRASh_numG A hA hI hhide b₁ b₂ b₁' b₂'

end Ratatouille

end VoleMole.Privacy
