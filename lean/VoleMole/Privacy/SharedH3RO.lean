import VoleMole.Privacy.MoussakaDelta
import VoleMole.Privacy.RatatouilleDelta
import VoleMole.ZK.ReadsROPerm
import VoleMole.ZK.SharedH3

/-!
# Moussaka and Ratatouille privacy with one shared `H₃`

The games of `Privacy/MoussakaRO.lean` and `Privacy/RatatouilleRO.lean` give each of their four
proofs its own independent `H₃` slice. In the scheme the four proofs hash with **one** `H₃`, and a
proof's slice is `H₃` at its prefix `wPrefix ‖ μ₁` (`voleith.hpp:168-185`: `H₃(witness_prefix ‖ mu ‖
rho ‖ 3)`). Here the games are stated with one shared `H₃` (`ZK/SharedH3.lean`): the shared tables
carry `H₃`'s columns in their rows (`RowH R`), and each real proof reads its slice at its prefix,
computed from its witness and instance at the time it runs (`keyI`, `keyR`, `keyIR`, `keySR`;
the redemption and spend prefixes depend on the adversary's choices). The slots' own slices are
still drawn by the games but no prover reads them; a shared-`H₃` adversary's guess ignores them
(it may read them: they are independent of everything).

**No prefix-collision term.** The paper justifies the per-proof slices by "the slices are
independent when the four `(μ₁, wPrefix)` differ" (`≤ 2⁻¹⁹²`, an `ε_iv`-type term). This term is not
needed: in each hybrid hop the zero-knowledge theorem is applied to one proof with its column of
`H₃` re-sampled (`ZK.Sim.ZeroKnowledgeRO.shared`); another proof with the same prefix is part of
the distinguisher and reads that column at its own `ρ`, one row read, paid in the zero-knowledge
error's `q₃·2⁻¹²⁸` term (this is where the birthday bound on the `ρ` of proofs with equal prefixes
sits). The collision terms `δ` of the games are unchanged (`ZK.Sim.pr_h3At_slice`).

**The adversary's `H₃` reads.** The adversary reads `H₃` through the rows of the shared tables: a
read of `H₃(x ‖ ρ ‖ 3)` is a read of row `ρ` (with the cipher's row `ρ`), so the guess's budget
`q_E` counts its cipher and `H₃` queries together. In the zero-knowledge error each row read is
also a read of the replaced proof's slice: the error is `εz(q_E', q₅', q_E')` instead of
`εz(q₃, q₅', q_E')`, where `q_E' = q_E + 3·4608` (each later real proof reads `4607` cipher rows
and the row of its `ρ`). An adversary that reads a later proof's prefix before that proof runs
(it knows its own future Anchor Sets and digests, and an unbounded one may know `r` from the
commitment) is covered: the slice it reads is the one the proof uses, as in the slice model.

* **Moussaka** (`anonymitySh_numG`, `anonymitySh_num`, `anonymitySh_num_perm`): for every
  adversary with budget `(q₃, q₅, q_E)` (`q₃`: reads of the unused slot slices, free),

      4·εz(pI; q_E + 13824, q₅ + 1872, q_E + 13824) + 4·εz(pR; q_E + 13824, q₅ + 1872, q_E + 13824)
        + 4·(2⁻¹¹³ + εz(pR; 0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

* **Ratatouille** (`unlinkabilitySh_numG`, `unlinkabilitySh_num`, `unlinkabilitySh_num_perm`): the
  same with `pS` for `pR`.

With function rows `εz = εRO`, so the bound is `anonymityRO_lean_num`'s with `q₃` replaced by
`q_E + 13824` (about `8·(q_E + 13824)·2⁻¹²⁸` more); with permutation rows `εz = εROPm`.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy

open VoleMole.ZK.Sim

namespace Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Verifier VoleMole.Verifier.Bridge

attribute [local irreducible] com UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-- **The prefix of an issuance proof**: `wPrefix ‖ μ₁` (the whole witness is the prefix). -/
noncomputable def keyI (w : Bytes) (x : IssueInstance) : Pre :=
  preKey ((toBA w).extract 0 pI.witnessBytes ++ (stI x).mu1 Hashes.shake)

/-- **The prefix of a redemption proof.** -/
noncomputable def keyR (w : Bytes) (x : RedeemInstance) : Pre :=
  preKey ((toBA w).extract 0 pR.witnessBytes ++ (stR x).mu1 Hashes.shake)

/-- **The Lean issuance prover with one shared `H₃`**: `leanPI` with the slice of the shared
tables at its prefix (the slot's own slice is not read). -/
noncomputable def leanPISh : ProverRO (RowH R) IssueInstance := fun w x rho _ s =>
  leanPI w x rho (h3At s (keyI w x)) s

/-- **The Lean redemption prover with one shared `H₃`.** -/
noncomputable def leanPRSh : ProverRO (RowH R) RedeemInstance := fun w x rho _ s =>
  leanPR w x rho (h3At s (keyR w x)) s

variable (A : AdversaryRO (RowH R)) (idx : AnchorSet → UOVKey → ℕ)

/-- **The real game with one shared `H₃`**: the spec's protocol, every proof computed on the shared
tables, its `H₃` slice the shared `H₃` at its prefix. -/
def realGameSh (b : Bool) : ((TIr × TIr) × (TRr × TRr)) × ShM (RowH R) → Prop :=
  realGameRO A idx leanPISh leanPRSh b

/-! ### What the shared provers read -/

omit [Fintype R] [Nonempty R] in
lemma leanPI_g3 (w : Bytes) (x : IssueInstance) (rho : Bytes) {G G' : Tab3} (s : ShM (RowH R))
    (h : G (blk 16 (toBA rho)) = G' (blk 16 (toBA rho))) : leanPI w x rho G s = leanPI w x rho G' s :=
  congrArg (fun o : Except String ByteArray => toL (o.toOption.getD .empty))
    (realROb_g3_congr' (p := pI) (toBA rho) s h)

omit [Fintype R] [Nonempty R] in
lemma leanPR_g3 (w : Bytes) (x : RedeemInstance) (rho : Bytes) {G G' : Tab3} (s : ShM (RowH R))
    (h : G (blk 16 (toBA rho)) = G' (blk 16 (toBA rho))) : leanPR w x rho G s = leanPR w x rho G' s :=
  congrArg (fun o : Except String ByteArray => toL (o.toOption.getD .empty))
    (realROb_g3_congr' (p := pR) (toBA rho) s h)

omit [Fintype R] [Nonempty R] in
lemma leanPISh_rd5 (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPISh (R := R) w x rho g) 624 :=
  rd5_h3At (fun G => (realROb_rd5 (p := pI) (Hb := Hashes.shake) (st := stI x) (w := toBA w)
    (toBA rho) G).map fun o => toL (o.toOption.getD .empty)) (keyI w x)

omit [Fintype R] [Nonempty R] in
lemma leanPISh_rdE (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) :
    RdE (leanPISh (R := R) w x rho g) (4607 + 1) :=
  rdE_h3At (blk 16 (toBA rho)) (fun _ _ s h => leanPI_g3 w x rho s h)
    (fun G => (realROb_rdE (p := pI) (st := stI x) (w := toBA w) hashesWF_shake (toBA rho) G).map
      fun o => toL (o.toOption.getD .empty)) (keyI w x)

omit [Fintype R] [Nonempty R] in
lemma leanPRSh_rd5 (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPRSh (R := R) w x rho g) 624 :=
  rd5_h3At (fun G => (realROb_rd5 (p := pR) (Hb := Hashes.shake) (st := stR x) (w := toBA w)
    (toBA rho) G).map fun o => toL (o.toOption.getD .empty)) (keyR w x)

omit [Fintype R] [Nonempty R] in
lemma leanPRSh_rdE (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    RdE (leanPRSh (R := R) w x rho g) (4607 + 1) :=
  rdE_h3At (blk 16 (toBA rho)) (fun _ _ s h => leanPR_g3 w x rho s h)
    (fun G => (realROb_rdE (p := pR) (st := stR x) (w := toBA w) hashesWF_shake (toBA rho) G).map
      fun o => toL (o.toOption.getD .empty)) (keyR w x)

omit [Fintype R] [Nonempty R] in
@[simp] lemma leanPI_setK (w : Bytes) (x : IssueInstance) (rho : Bytes) (G : Tab3) (s : ShM (RowH R))
    (k : Pre) (g : Tab3) : leanPI w x rho G (setK s k g) = leanPI w x rho G s := by
  simp only [leanPI, realROb_setK]

omit [Fintype R] [Nonempty R] in
@[simp] lemma leanPR_setK (w : Bytes) (x : RedeemInstance) (rho : Bytes) (G : Tab3)
    (s : ShM (RowH R)) (k : Pre) (g : Tab3) : leanPR w x rho G (setK s k g) = leanPR w x rho G s :=
  congrArg (fun o : Except String ByteArray => toL (o.toOption.getD .empty))
    (realROb_setK (p := pR) _ _ _ _ _ s k g)

omit [Fintype R] [Nonempty R] in
@[simp] lemma leanProgI_setK (x : IssueInstance) (c : SimCoins pI) (s : ShM (RowH R)) (k : Pre)
    (g : Tab3) : leanProgI x c (setK s k g) = setK (leanProgI x c s) k g := rfl

omit [Fintype R] [Nonempty R] in
@[simp] lemma leanProgR_setK (x : RedeemInstance) (c : SimCoins pR) (s : ShM (RowH R)) (k : Pre)
    (g : Tab3) : leanProgR x c (setK s k g) = setK (leanProgR x c s) k g := rfl

omit [Fintype R] [Nonempty R] in
@[simp] lemma h3At_leanProgI (x : IssueInstance) (c : SimCoins pI) (s : ShM (RowH R)) (k : Pre) :
    h3At (leanProgI x c s) k = h3At s k := rfl

omit [Fintype R] [Nonempty R] in
@[simp] lemma h3At_leanProgR (x : RedeemInstance) (c : SimCoins pR) (s : ShM (RowH R)) (k : Pre) :
    h3At (leanProgR x c s) k = h3At s k := rfl

/-! ### Zero knowledge of the shared provers -/

/-- **Zero knowledge of the issuance prover with one shared `H₃`** (`ZeroKnowledgeRO.shared`):
error `εz(pI; q_E, q₅, q_E)`. -/
theorem leanPISh_zkRO [ZKRow R] (q3 q5 qE : ℕ) : ZeroKnowledgeRO IssueRelW
    (fun x w (ρ : Coins proveSeedBytes) g (s : ShM (RowH R)) => leanPISh w x (List.ofFn ρ) g s)
    (leanSim pI) leanProgI (Budget pI q3 q5 qE) (ZKRow.εz R pI qE q5 qE) :=
  ZeroKnowledgeRO.shared (P := fun x w (ρ : Coins proveSeedBytes) g (s : ShM (RowH R)) =>
      leanPI w x (List.ofFn ρ) g s) (ε := ZKRow.εz R pI) (fun x w => keyI w x)
    (fun _ _ _ _ _ _ _ => leanPI_setK _ _ _ _ _ _ _) (fun _ _ _ _ _ => rfl)
    (fun a b c => leanPI_zkRO (R := RowH R) a b c) q3 q5 qE

/-- **Zero knowledge of the redemption prover with one shared `H₃`.** -/
theorem leanPRSh_zkRO [ZKRow R] (q3 q5 qE : ℕ) : ZeroKnowledgeRO RedeemRelW
    (fun x w (ρ : Coins proveSeedBytes) g (s : ShM (RowH R)) => leanPRSh w x (List.ofFn ρ) g s)
    (leanSim pR) leanProgR (Budget pR q3 q5 qE) (ZKRow.εz R pR qE q5 qE) :=
  ZeroKnowledgeRO.shared (p := pR) (P := fun x w (ρ : Coins proveSeedBytes) g (s : ShM (RowH R)) =>
      leanPR w x (List.ofFn ρ) g s) (ε := ZKRow.εz R pR) (fun x w => keyR w x)
    (fun _ _ _ _ _ _ _ => leanPR_setK _ _ _ _ _ _ _) (fun _ _ _ _ _ => rfl)
    (fun a b c => leanPR_zkRO (R := RowH R) a b c) q3 q5 qE

/-! ### The collision terms are the slice model's -/

omit [Nonempty R] in
lemma redRealRO_sh (x : TRr) (p : RedeemPt) (s : ShM (RowH R)) :
    (redRealRO A leanPRSh x).out p s =
      (redRealRO A leanPR (x.1, h3At s (keyR (wROf A p) (xROf A p)))).out p s := by
  simp only [redRealRO, redeemRequestOf, nizkAt, leanPRSh]
  split
  · rfl
  · split <;> rfl

omit [Nonempty R] in
@[simp] lemma redRealRO_setK (x : TRr) (p : RedeemPt) (s : ShM (RowH R)) (k : Pre) (g : Tab3) :
    (redRealRO A leanPR x).out p (setK s k g) = (redRealRO A leanPR x).out p s := by
  simp only [redRealRO, nizkAt, leanPR_setK]

omit [Nonempty R] in
lemma LR_setK {CR : Type} (b : Bool) (γ : (TIs (SimCoins pI) × TIs (SimCoins pI)) × TRs CR)
    (progR : RedeemInstance → CR → ShM (RowH R) → ShM (RowH R))
    (hp : ∀ x c s k g, progR x c (setK s k g) = setK (progR x c s) k g) (s : ShM (RowH R)) (k : Pre)
    (g : Tab3) : LR A idx (leanSim pI) leanProgI progR b γ (setK s k g) =
      setK (LR A idx (leanSim pI) leanProgI progR b γ s) k g := by
  unfold LR
  split <;> simp only [hp, PIOf, leanProgI_setK]

omit [Nonempty R] in
@[simp] lemma h3At_LR (b : Bool) (γ : (TIs (SimCoins pI) × TIs (SimCoins pI)) × TRs (SimCoins pR))
    (s : ShM (RowH R)) (k : Pre) :
    h3At (LR A idx (leanSim pI) leanProgI leanProgR b γ s) k = h3At s k := by
  unfold LR
  split <;> rfl

theorem deltaI1_sh : deltaI1 A leanProgI (leanPISh (R := R)) = deltaI1 A leanProgI leanPI := by
  unfold deltaI1
  simp only [leanPISh, h3At_leanProgI]
  have := pr_h3At_slice (R := R) (Γ := TIs (SimCoins pI) × (NR × (TRr × TRr))) (ρT := Coins proveSeedBytes)
    (p := pI) (fun γ => keyI (wIOf A γ.2.1) (xIOf A γ.2.1))
    (fun γ ρ G s => leanPI (wIOf A γ.2.1) (xIOf A γ.2.1) (List.ofFn ρ) G
      (leanProgI (xIOf A γ.1.1) γ.1.2.1 s) ≠ leanPI (wIOf A γ.2.1) (xIOf A γ.2.1) (List.ofFn ρ) G s)
    fun _ _ _ _ _ _ => by rw [leanProgI_setK, leanPI_setK, leanPI_setK]
  exact this

theorem deltaL_sh (b : Bool) : deltaL A idx (leanSim pI) leanProgI (leanPRSh (R := R)) b =
    deltaL A idx (leanSim pI) leanProgI leanPR b := by
  unfold deltaL
  simp only [redRealRO_sh, PIOf, h3At_leanProgI]
  refine pr_h3At_slice (fun γ => keyR (wROf A (pt A.base idx b (i₀Of A (leanSim pI) γ)
      (i₁Of A (leanSim pI) γ) false)) (xROf A (pt A.base idx b (i₀Of A (leanSim pI) γ)
      (i₁Of A (leanSim pI) γ) false)))
    (fun γ ρ G s => (redRealRO A leanPR (ρ, G)).out (pt A.base idx b (i₀Of A (leanSim pI) γ)
        (i₁Of A (leanSim pI) γ) false) (PIOf A leanProgI γ s) ≠
      (redRealRO A leanPR (ρ, G)).out (pt A.base idx b (i₀Of A (leanSim pI) γ)
        (i₁Of A (leanSim pI) γ) false) s)
    fun _ _ _ _ _ _ => ?_
  simp only [PIOf, leanProgI_setK, redRealRO_setK]

theorem deltaR_sh (b : Bool) :
    deltaR A idx (leanSim pI) leanProgI leanProgR (leanPRSh (R := R)) b =
      deltaR A idx (leanSim pI) leanProgI leanProgR leanPR b := by
  unfold deltaR
  simp only [redRealRO_sh, h3At_LR]
  refine pr_h3At_slice (fun γ => keyR (wROf A (pt A.base idx b (i₀Of A (leanSim pI) γ)
      (i₁Of A (leanSim pI) γ) true)) (xROf A (pt A.base idx b (i₀Of A (leanSim pI) γ)
      (i₁Of A (leanSim pI) γ) true)))
    (fun γ ρ G s => (redRealRO A leanPR (ρ, G)).out (pt A.base idx b (i₀Of A (leanSim pI) γ)
        (i₁Of A (leanSim pI) γ) true) (LR A idx (leanSim pI) leanProgI leanProgR b γ s) ≠
      (redRealRO A leanPR (ρ, G)).out (pt A.base idx b (i₀Of A (leanSim pI) γ)
        (i₁Of A (leanSim pI) γ) true) s)
    fun _ _ _ _ _ _ => ?_
  rw [LR_setK A idx b _ leanProgR (fun _ _ _ _ _ => rfl)]
  simp only [redRealRO_setK]

/-! ### The theorem -/

/-- **Theorem 4(a) (Moussaka issuer hiding and unlinkability) with one shared `H₃`, every term
explicit, for every type of cipher rows** (`ZKRow R`). The real game runs the spec with every proof
on the shared tables, its `H₃` slice the shared `H₃` at its prefix; the adversary's guess reads the
rows (the cipher and `H₃`) at `q_E` keys, `H₅` at `q₅`, `H₂³` freely (and the unused slot slices at
`q₃`). Then the two worlds differ by at most

    4·εz(pI; q_E + 13824, q₅ + 1872, q_E + 13824) + 4·εz(pR; q_E + 13824, q₅ + 1872, q_E + 13824)
      + 4·(2⁻¹¹³ + εz(pR; 0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide,

with no term for proofs whose prefixes coincide. -/
theorem anonymitySh_numG [ZKRow R] {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b c, hidingAdv A.base.ci A.base.cr
      (reductionRO A idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameSh A idx false) - pr _ (realGameSh A idx true)| ≤
      4 * ZKRow.εz R pI (qE + 13824) (q5 + 1872) (qE + 13824) +
        4 * ZKRow.εz R pR (qE + 13824) (q5 + 1872) (qE + 13824) +
        4 * (1 / 2 ^ 113 + ZKRow.εz R pR 0 312 4607) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  have h := anonymityRO (A := A) (idx := idx) (PI := leanPISh) (PR := leanPRSh)
    (simI := leanSim pI) (simR := leanSim pR) (progI := leanProgI) (progR := leanProgR)
    (εI := fun _ a c => ZKRow.εz R pI c a c) (εR := fun _ a c => ZKRow.εz R pR c a c)
    hA leanPISh_rd5 leanPISh_rdE leanPRSh_rd5 leanPRSh_rdE (fun x c => progRO_isProg c)
    (fun x c => progRO_isProg c) (fun a c => leanPISh_zkRO q3 a c) (fun a c => leanPRSh_zkRO q3 a c)
    (fun a c => ZKRow.εz_nonneg _ _ _ _) hhide
  beta_reduce at h
  rw [deltaI1_sh, deltaL_sh, deltaL_sh, deltaR_sh, deltaR_sh] at h
  have d1 := deltaI1_le (R := RowH R) A
  have dL0 := deltaL_le (R := RowH R) A idx false
  have dL1 := deltaL_le (R := RowH R) A idx true
  have dR0 := deltaR_le (R := RowH R) A idx false
  have dR1 := deltaR_le (R := RowH R) A idx true
  simp only [ZKRow.εz_rowH] at dL0 dL1 dR0 dR1
  have m : ∀ (p : Params) a c, a ≤ q5 + 1872 → c ≤ qE + 13824 →
      ZKRow.εz R p c a c ≤ ZKRow.εz R p (qE + 13824) (q5 + 1872) (qE + 13824) :=
    fun p a c ha hc => ZKRow.εz_mono p hc ha hc
  have m1 := m pI (624 + (624 + 624 + q5)) ((4607 + 1) + ((4607 + 1) + (4607 + 1) + qE))
    (by omega) (by omega)
  have m2 := m pI (624 + 624 + q5 + 312) ((4607 + 1) + (4607 + 1) + qE + 4607) (by omega) (by omega)
  have m3 := m pR (0 + 624 + q5 + (312 + 312)) (0 + (4607 + 1) + qE + (4607 + 4607)) (by omega)
    (by omega)
  have m4 := m pR (0 + 0 + q5 + (312 + (312 + 312))) (0 + 0 + qE + (4607 + (4607 + 4607)))
    (by omega) (by omega)
  unfold realGameSh
  refine h.trans (le_trans (add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add m1 m2) m3) m4) (by norm_num))
    (mul_le_mul_of_nonneg_left d1 (by norm_num))) (add_le_add dL0 dL1)) (add_le_add dR0 dR1))
    le_rfl) (le_of_eq ?_))
  generalize (2 : ℝ) ^ 1024 = K
  ring

/-- **Theorem 4(a) with one shared `H₃`, function rows** (`anonymitySh_numG` at `Blk → Blk`):

    8·εRO(q_E + 13824, q₅ + 1872, q_E + 13824) + 4·(2⁻¹¹³ + εRO(0, 312, 4607)) + 6·noHitProb
      + 12·2⁻¹⁰²⁴ + 2·εhide. -/
theorem anonymitySh_num (A : AdversaryRO (RowH (Blk → Blk))) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b c, hidingAdv A.base.ci A.base.cr
      (reductionRO A idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameSh A idx false) - pr _ (realGameSh A idx true)| ≤
      8 * εRO (qE + 13824) (q5 + 1872) (qE + 13824) + 4 * (1 / 2 ^ 113 + εRO 0 312 4607) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  (anonymitySh_numG A idx hA hhide).trans (le_of_eq (by
    rw [ZKRow.εz_fn, ZKRow.εz_fn]
    generalize (2 : ℝ) ^ 1024 = K
    ring))

/-- **Theorem 4(a) with one shared `H₃`, AES as uniformly random permutations**
(`anonymitySh_numG` at `Equiv.Perm Blk`):

    4·εROPm(pI; q_E + 13824, q₅ + 1872, q_E + 13824) + 4·εROPm(pR; q_E + 13824, q₅ + 1872, q_E + 13824)
      + 4·(2⁻¹¹³ + εROPm(pR; 0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide. -/
theorem anonymitySh_num_perm (A : AdversaryRO (RowH (Equiv.Perm Blk)))
    (idx : AnchorSet → UOVKey → ℕ) {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b c, hidingAdv A.base.ci A.base.cr
      (reductionRO A idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameSh A idx false) - pr _ (realGameSh A idx true)| ≤
      4 * εROPm pI (qE + 13824) (q5 + 1872) (qE + 13824) +
        4 * εROPm pR (qE + 13824) (q5 + 1872) (qE + 13824) +
        4 * (1 / 2 ^ 113 + εROPm pR 0 312 4607) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymitySh_numG A idx hA hhide

end Moussaka

namespace Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.Verifier VoleMole.Verifier.Bridge

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-- **The prefix of an issuance proof**: `wPrefix ‖ μ₁`. -/
noncomputable def keyIR (x : IssueInstance) (w : IssueWitness) : Pre :=
  preKey ((encI x w).extract 0 pI.witnessBytes ++ (stI x).mu1 Hashes.shake)

/-- **The prefix of a spend proof.** -/
noncomputable def keySR (x : SpendInstance) (w : SpendWitness) : Pre :=
  preKey ((encS x w).extract 0 pS.witnessBytes ++ (stS x).mu1 Hashes.shake)

/-- **The Lean issuance prover with one shared `H₃`.** -/
noncomputable def leanPIRSh : ProverI (RowH R) Sizes.labelRows := fun x w ρ _ s =>
  leanPIR x w ρ (h3At s (keyIR x w)) s

/-- **The Lean spend prover with one shared `H₃`.** -/
noncomputable def leanPSRSh : ProverS (RowH R) Sizes.labelRows := fun x w ρ _ s =>
  leanPSR x w ρ (h3At s (keySR x w)) s

variable (A : AdversaryRO (RowH R) Sizes.labelRows)

/-- **The real game with one shared `H₃`.** -/
def realGameSh (b₁ b₂ : Bool) : ((TRe × TRe) × (TRe × TRe)) × ShR (RowH R) → Prop :=
  realGameR A leanPIRSh leanPSRSh b₁ b₂

/-! ### What the shared provers read -/

omit [Fintype R] [Nonempty R] in
lemma leanPIR_g3 (x : IssueInstance) (w : IssueWitness) (ρ : Rho) {G G' : Tab3}
    (s : ShR (RowH R)) (h : G (blk 16 (bOf ρ)) = G' (blk 16 (bOf ρ))) :
    leanPIR x w ρ G s = leanPIR x w ρ G' s :=
  congrArg (vecOf _) (realROb_g3_congr' (p := pI) (bOf ρ) s h)

omit [Fintype R] [Nonempty R] in
lemma leanPSR_g3 (x : SpendInstance) (w : SpendWitness) (ρ : Rho) {G G' : Tab3}
    (s : ShR (RowH R)) (h : G (blk 16 (bOf ρ)) = G' (blk 16 (bOf ρ))) :
    leanPSR x w ρ G s = leanPSR x w ρ G' s :=
  congrArg (vecOf _) (realROb_g3_congr' (p := pS) (bOf ρ) s h)

omit [Fintype R] [Nonempty R] in
@[simp] lemma leanPIR_setK (x : IssueInstance) (w : IssueWitness) (ρ : Rho) (G : Tab3)
    (s : ShR (RowH R)) (k : Pre) (g : Tab3) : leanPIR x w ρ G (setK s k g) = leanPIR x w ρ G s :=
  congrArg (vecOf _) (realROb_setK (p := pI) _ _ _ _ _ s k g)

omit [Fintype R] [Nonempty R] in
@[simp] lemma leanPSR_setK (x : SpendInstance) (w : SpendWitness) (ρ : Rho) (G : Tab3)
    (s : ShR (RowH R)) (k : Pre) (g : Tab3) : leanPSR x w ρ G (setK s k g) = leanPSR x w ρ G s :=
  congrArg (vecOf _) (realROb_setK (p := pS) _ _ _ _ _ s k g)

omit [Fintype R] [Nonempty R] in
@[simp] lemma leanProgIR_setK (x : IssueInstance) (c : SimCoins pI) (s : ShR (RowH R)) (k : Pre)
    (g : Tab3) : leanProgIR x c (setK s k g) = setK (leanProgIR x c s) k g := rfl

omit [Fintype R] [Nonempty R] in
@[simp] lemma leanProgSR_setK (x : SpendInstance) (c : SimCoins pS) (s : ShR (RowH R)) (k : Pre)
    (g : Tab3) : leanProgSR x c (setK s k g) = setK (leanProgSR x c s) k g := rfl

omit [Fintype R] [Nonempty R] in
@[simp] lemma h3At_leanProgIR (x : IssueInstance) (c : SimCoins pI) (s : ShR (RowH R)) (k : Pre) :
    h3At (leanProgIR x c s) k = h3At s k := rfl

omit [Fintype R] [Nonempty R] in
@[simp] lemma h3At_leanProgSR (x : SpendInstance) (c : SimCoins pS) (s : ShR (RowH R)) (k : Pre) :
    h3At (leanProgSR x c s) k = h3At s k := rfl

omit [Fintype R] [Nonempty R] in
lemma leanPIRSh_rd5 (x : IssueInstance) (w : IssueWitness) (ρ : Rho) (g : Tab3) :
    Rd5 (leanPIRSh (R := R) x w ρ g) 624 :=
  rd5_h3At (fun G => (realROb_rd5 (p := pI) (Hb := Hashes.shake) (st := stI x) (w := encI x w)
    (bOf ρ) G).map (vecOf Sizes.labelRows.issue)) (keyIR x w)

omit [Fintype R] [Nonempty R] in
lemma leanPIRSh_rdE (x : IssueInstance) (w : IssueWitness) (ρ : Rho) (g : Tab3) :
    RdE (leanPIRSh (R := R) x w ρ g) (4607 + 1) :=
  rdE_h3At (blk 16 (bOf ρ)) (fun _ _ s h => leanPIR_g3 x w ρ s h)
    (fun G => (realROb_rdE (p := pI) (st := stI x) (w := encI x w) hashesWF_shake (bOf ρ) G).map
      (vecOf Sizes.labelRows.issue)) (keyIR x w)

omit [Fintype R] [Nonempty R] in
lemma leanPSRSh_rd5 (x : SpendInstance) (w : SpendWitness) (ρ : Rho) (g : Tab3) :
    Rd5 (leanPSRSh (R := R) x w ρ g) 624 := by
  have h : ∀ G, Rd5 (leanPSR (R := RowH R) x w ρ G) 624 := fun G =>
    (realROb_rd5 (p := pS) (Hb := Hashes.shake) (st := stS x) (w := encS x w) (bOf ρ) G).map
      (vecOf Sizes.labelRows.spend)
  exact rd5_h3At h (keySR x w)

omit [Fintype R] [Nonempty R] in
lemma leanPSRSh_rdE (x : SpendInstance) (w : SpendWitness) (ρ : Rho) (g : Tab3) :
    RdE (leanPSRSh (R := R) x w ρ g) (4607 + 1) := by
  have h : ∀ G, RdE (leanPSR (R := RowH R) x w ρ G) 4607 := fun G =>
    (realROb_rdE (p := pS) (st := stS x) (w := encS x w) hashesWF_shake (bOf ρ) G).map
      (vecOf Sizes.labelRows.spend)
  exact rdE_h3At (blk 16 (bOf ρ)) (fun _ _ s h => leanPSR_g3 x w ρ s h) h (keySR x w)

/-! ### Zero knowledge of the shared provers -/

theorem leanPIRSh_zkRO [ZKRow R] (q3 q5 qE : ℕ) : ZeroKnowledgeRO IssueRel
    (fun x w (ρ : Coins 16) g (s : ShR (RowH R)) => leanPIRSh x w (vec ρ) g s) leanSimIR leanProgIR
    (Budget pI q3 q5 qE) (ZKRow.εz R pI qE q5 qE) :=
  ZeroKnowledgeRO.shared (P := fun x w (ρ : Coins 16) g (s : ShR (RowH R)) => leanPIR x w (vec ρ) g s)
    (ε := ZKRow.εz R pI) keyIR (fun _ _ _ _ _ _ _ => leanPIR_setK _ _ _ _ _ _ _)
    (fun _ _ _ _ _ => rfl) (fun a b c => leanPIR_zkRO (R := RowH R) a b c) q3 q5 qE

theorem leanPSRSh_zkRO [ZKRow R] (q3 q5 qE : ℕ) : ZeroKnowledgeRO SpendRel
    (fun x w (ρ : Coins 16) g (s : ShR (RowH R)) => leanPSRSh x w (vec ρ) g s) leanSimSR leanProgSR
    (Budget pS q3 q5 qE) (ZKRow.εz R pS qE q5 qE) :=
  ZeroKnowledgeRO.shared (p := pS)
    (P := fun x w (ρ : Coins 16) g (s : ShR (RowH R)) => leanPSR x w (vec ρ) g s)
    (ε := ZKRow.εz R pS) keySR (fun _ _ _ _ _ _ _ => leanPSR_setK _ _ _ _ _ _ _)
    (fun _ _ _ _ _ => rfl) (fun a b c => leanPSR_zkRO (R := RowH R) a b c) q3 q5 qE

/-! ### The collision terms are the slice model's -/

/-- The prefix of the issuance at the coins `n`. -/
noncomputable def issKey (n : NRR) : Pre :=
  keyIR ⟨com (vec n.1) A.ctx A.tInit (vec n.2), A.tInit, A.ctx⟩ ⟨vec n.1, vec n.2⟩

/-- The prefix of the spend of the token `τ` and the amount `d` at the coins `n` (when the Client's
check passes). -/
noncomputable def spKey (τ : TokenS) (d : Credits) (n : NRR) : Pre :=
  match clientCheck τ.t τ.x d with
  | none => preKey .empty
  | some t' => keySR ⟨A.pk, τ.nf, d, com (vec n.1) A.ctx t' (vec n.2), A.ctx⟩
      ⟨τ.t, τ.r, τ.x, τ.s, vec n.1, t', vec n.2⟩

omit [Fintype R] [Nonempty R] in
lemma primI_proveIssue {Z : Sizes} (P : ProverI (RowH R) Z) (g : Tab3) (s : ShR (RowH R)) :
    (primI P g s).proveIssue = fun x w ρ => P x w ρ g s := rfl

omit [Fintype R] [Nonempty R] in
lemma primS_proveSpend {Z : Sizes} (P : ProverS (RowH R) Z) (g : Tab3) (s : ShR (RowH R)) :
    (primS P g s).proveSpend = fun x w ρ => P x w ρ g s := rfl

omit [Fintype R] [Nonempty R] in
/-- An issuance depends on its prover only at the call it makes. -/
lemma issueOf_congr {Z : Sizes} {SK : Type} (P P' : Prim Z SK) (tInit : Credits) (ctx : Context)
    (nf : Nullifier) (r : Opening) (ρ : Rho)
    (h : P.proveIssue ⟨com nf ctx tInit r, tInit, ctx⟩ ⟨nf, r⟩ ρ =
      P'.proveIssue ⟨com nf ctx tInit r, tInit, ctx⟩ ⟨nf, r⟩ ρ) :
    issueOf P tInit ctx nf r ρ = issueOf P' tInit ctx nf r ρ := by
  unfold issueOf
  rw [h]

omit [Fintype R] [Nonempty R] in
/-- A spend depends on its prover only at the call it makes. -/
lemma spendOf_congr {Z : Sizes} {SK : Type} (P P' : Prim Z SK) (pk : PublicKey) (τ : TokenS)
    (d : Credits) (ctx : Context) (nf' : Nullifier) (r' : Opening) (ρ : Rho)
    (h : ∀ t', clientCheck τ.t τ.x d = some t' →
      P.proveSpend ⟨pk, τ.nf, d, com nf' ctx t' r', ctx⟩ ⟨τ.t, τ.r, τ.x, τ.s, nf', t', r'⟩ ρ =
        P'.proveSpend ⟨pk, τ.nf, d, com nf' ctx t' r', ctx⟩ ⟨τ.t, τ.r, τ.x, τ.s, nf', t', r'⟩ ρ) :
    spendOf P pk (some τ) d ctx nf' r' ρ = spendOf P' pk (some τ) d ctx nf' r' ρ := by
  unfold spendOf
  dsimp only
  split_ifs
  all_goals first
    | rfl
    | cases hc : clientCheck τ.t τ.x d with
      | none => rfl
      | some t' => dsimp only; rw [h t' hc]

omit [Fintype R] [Nonempty R] in
lemma issRealR_sh (x : TRe) (s : ShR (RowH R)) :
    (issRealR A leanPIRSh x).out s = (issRealR A leanPIR (x.1, x.2.1, h3At s (issKey A x.1))).out s :=
  congrArg (issOutOf A.base) (issueOf_congr _ _ _ _ _ _ _ rfl)

omit [Fintype R] [Nonempty R] in
lemma spRealR_sh (x : TRe) (τ : TokenS) (d : Credits) (s : ShR (RowH R)) :
    (spRealR A leanPSRSh x).out τ d s =
      (spRealR A leanPSR (x.1, x.2.1, h3At s (spKey A τ d x.1))).out τ d s :=
  congrArg (fun r : Option TokenS × Except Error (PendingSpendS × SpendRequest Sizes.labelRows) =>
    spOutOf A.base r.2) (spendOf_congr _ _ _ _ _ _ _ _ _ fun t' ht => by
      simp only [primS_proveSpend, leanPSRSh, spKey, ht])

omit [Nonempty R] in
@[simp] lemma issRealR_setK (x : TRe) (s : ShR (RowH R)) (k : Pre) (g : Tab3) :
    (issRealR A leanPIR x).out (setK s k g) = (issRealR A leanPIR x).out s := by
  simp only [issRealR, primI, leanPIR_setK]

omit [Nonempty R] in
@[simp] lemma spRealR_setK (x : TRe) (τ : TokenS) (d : Credits) (s : ShR (RowH R)) (k : Pre)
    (g : Tab3) : (spRealR A leanPSR x).out τ d (setK s k g) = (spRealR A leanPSR x).out τ d s := by
  simp only [spRealR, primS, leanPSR_setK]

omit [Nonempty R] in
@[simp] lemma PIR_setK (n : NRR) (c : SimCoins pI) (s : ShR (RowH R)) (k : Pre) (g : Tab3) :
    PIR A leanProgIR n c (setK s k g) = setK (PIR A leanProgIR n c s) k g := by
  unfold PIR
  split <;> rfl

omit [Nonempty R] in
@[simp] lemma h3At_PIR (n : NRR) (c : SimCoins pI) (s : ShR (RowH R)) (k : Pre) :
    h3At (PIR A leanProgIR n c s) k = h3At s k := by
  unfold PIR
  split <;> rfl

omit [Nonempty R] in
lemma LS2R_setK (b₁ : Bool) (γ : ((TIsR (SimCoins pI) × TIsR (SimCoins pI)) × TSsR (SimCoins pS)) × NRR)
    (s : ShR (RowH R)) (k : Pre) (g : Tab3) :
    LS2R A leanSimIR leanProgIR leanProgSR b₁ γ (setK s k g) =
      setK (LS2R A leanSimIR leanProgIR leanProgSR b₁ γ s) k g := by
  unfold LS2R
  split <;> simp only [PI2R, PIR_setK, leanProgSR_setK]

omit [Nonempty R] in
@[simp] lemma h3At_LS2R (b₁ : Bool)
    (γ : ((TIsR (SimCoins pI) × TIsR (SimCoins pI)) × TSsR (SimCoins pS)) × NRR)
    (s : ShR (RowH R)) (k : Pre) :
    h3At (LS2R A leanSimIR leanProgIR leanProgSR b₁ γ s) k = h3At s k := by
  unfold LS2R
  split <;> simp only [PI2R, h3At_PIR, h3At_leanProgSR]

theorem deltaI1R_sh : deltaI1R A leanProgIR (leanPIRSh (R := R)) = deltaI1R A leanProgIR leanPIR := by
  unfold deltaI1R
  simp only [issRealR_sh, h3At_PIR]
  have := pr_h3At_slice (R := R) (Γ := TIsR (SimCoins pI) × (NRR × (TRe × TRe))) (ρT := Coins 16)
    (p := pI) (fun γ => issKey A γ.2.1)
    (fun γ ρ G s => (issRealR A leanPIR (γ.2.1, ρ, G)).out (PIR A leanProgIR γ.1.1 γ.1.2.1 s) ≠
      (issRealR A leanPIR (γ.2.1, ρ, G)).out s)
    fun _ _ _ _ _ _ => by rw [PIR_setK, issRealR_setK, issRealR_setK]
  exact this

theorem deltaS1R_sh (b₁ : Bool) : deltaS1R A leanSimIR leanProgIR (leanPSRSh (R := R)) b₁ =
    deltaS1R A leanSimIR leanProgIR leanPSR b₁ := by
  unfold deltaS1R
  simp only [spRealR_sh, PI2R, h3At_PIR]
  have := pr_h3At_slice (R := R) (Γ := ((TIsR (SimCoins pI) × TIsR (SimCoins pI)) × NRR) × TRe)
    (ρT := Coins 16) (p := pI)
    (fun γ => spKey A (τ₁Of A b₁ (i₀R A leanSimIR γ.1) (i₁R A leanSimIR γ.1))
      (A.d₁ ((i₀R A leanSimIR γ.1).req, (i₁R A leanSimIR γ.1).req)) γ.1.2)
    (fun γ ρ G s => (spRealR A leanPSR (γ.1.2, ρ, G)).out
        (τ₁Of A b₁ (i₀R A leanSimIR γ.1) (i₁R A leanSimIR γ.1))
        (A.d₁ ((i₀R A leanSimIR γ.1).req, (i₁R A leanSimIR γ.1).req)) (PI2R A leanProgIR γ.1 s) ≠
      (spRealR A leanPSR (γ.1.2, ρ, G)).out (τ₁Of A b₁ (i₀R A leanSimIR γ.1) (i₁R A leanSimIR γ.1))
        (A.d₁ ((i₀R A leanSimIR γ.1).req, (i₁R A leanSimIR γ.1).req)) s)
    fun _ _ _ _ _ _ => by rw [PI2R, PIR_setK, PIR_setK, spRealR_setK, spRealR_setK]
  exact this

theorem deltaS2R_sh (b₁ b₂ : Bool) :
    deltaS2R A leanSimIR leanSimSR leanProgIR leanProgSR (leanPSRSh (R := R)) b₁ b₂ =
      deltaS2R A leanSimIR leanSimSR leanProgIR leanProgSR leanPSR b₁ b₂ := by
  unfold deltaS2R
  simp only [spRealR_sh, h3At_LS2R]
  have := pr_h3At_slice (R := R)
    (Γ := ((TIsR (SimCoins pI) × TIsR (SimCoins pI)) × TSsR (SimCoins pS)) × NRR) (ρT := Coins 16)
    (p := pI)
    (fun γ => spKey A (τ₂R A leanSimIR leanSimSR b₁ b₂ γ) (d₂R A leanSimIR leanSimSR b₁ γ) γ.2)
    (fun γ ρ G s => (spRealR A leanPSR (γ.2, ρ, G)).out (τ₂R A leanSimIR leanSimSR b₁ b₂ γ)
        (d₂R A leanSimIR leanSimSR b₁ γ) (LS2R A leanSimIR leanProgIR leanProgSR b₁ γ s) ≠
      (spRealR A leanPSR (γ.2, ρ, G)).out (τ₂R A leanSimIR leanSimSR b₁ b₂ γ)
        (d₂R A leanSimIR leanSimSR b₁ γ) s)
    fun _ _ _ _ _ _ => by rw [LS2R_setK, spRealR_setK, spRealR_setK]
  exact this

/-! ### The theorem -/

/-- **Theorem 2 (Ratatouille unlinkability) with one shared `H₃`, every term explicit, for every
type of cipher rows** (`ZKRow R`): any two worlds differ by at most

    4·εz(pI; q_E + 13824, q₅ + 1872, q_E + 13824) + 4·εz(pS; q_E + 13824, q₅ + 1872, q_E + 13824)
      + 4·(2⁻¹¹³ + εz(pS; 0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide,

with no term for proofs whose prefixes coincide. -/
theorem unlinkabilitySh_numG [ZKRow R] {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionR A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameSh A b₁ b₂) - pr _ (realGameSh A b₁' b₂')| ≤
      4 * ZKRow.εz R pI (qE + 13824) (q5 + 1872) (qE + 13824) +
        4 * ZKRow.εz R pS (qE + 13824) (q5 + 1872) (qE + 13824) +
        4 * (1 / 2 ^ 113 + ZKRow.εz R pS 0 312 4607) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  have h := unlinkabilityRO (A := A) (PI := leanPIRSh) (PS := leanPSRSh) (simI := leanSimIR)
    (simS := leanSimSR) (progI := leanProgIR) (progS := leanProgSR)
    (εI := fun _ a c => ZKRow.εz R pI c a c) (εS := fun _ a c => ZKRow.εz R pS c a c)
    hA leanPIRSh_rd5 leanPIRSh_rdE leanPSRSh_rd5 leanPSRSh_rdE (fun x c => progRO_isProg c)
    (fun x c => progRO_isProg c) leanProgIR_none leanProgSR_none
    (fun a c => leanPIRSh_zkRO q3 a c) (fun a c => leanPSRSh_zkRO q3 a c)
    (fun a c => ZKRow.εz_nonneg _ _ _ _) (fun a c => ZKRow.εz_nonneg _ _ _ _) hhide b₁ b₂ b₁' b₂'
  beta_reduce at h
  rw [deltaI1R_sh, deltaS1R_sh, deltaS1R_sh, deltaS2R_sh, deltaS2R_sh] at h
  have d1 := deltaI1R_le (R := RowH R) A
  have dS0 := deltaS1R_le (R := RowH R) A b₁
  have dS1 := deltaS1R_le (R := RowH R) A b₁'
  have dT0 := deltaS2R_le (R := RowH R) A b₁ b₂
  have dT1 := deltaS2R_le (R := RowH R) A b₁' b₂'
  simp only [ZKRow.εz_rowH] at dS0 dS1 dT0 dT1
  have m : ∀ (p : Params) a c, a ≤ q5 + 1872 → c ≤ qE + 13824 →
      ZKRow.εz R p c a c ≤ ZKRow.εz R p (qE + 13824) (q5 + 1872) (qE + 13824) :=
    fun p a c ha hc => ZKRow.εz_mono p hc ha hc
  have m1 := m pI (0 + (624 + (624 + (624 + q5)))) (0 + ((4607 + 1) + ((4607 + 1) + ((4607 + 1) + qE))))
    (by omega) (by omega)
  have m2 := m pI (0 + (0 + (624 + (624 + q5))) + 312) (0 + (0 + ((4607 + 1) + ((4607 + 1) + qE))) + 4607)
    (by omega) (by omega)
  have m3 := m pS (0 + (0 + (0 + (624 + q5))) + (312 + 312))
    (0 + (0 + (0 + ((4607 + 1) + qE))) + (4607 + 4607)) (by omega) (by omega)
  have m4 := m pS (0 + (0 + (0 + (0 + q5))) + (312 + (312 + 312)))
    (0 + (0 + (0 + (0 + qE))) + (4607 + (4607 + 4607))) (by omega) (by omega)
  unfold realGameSh
  refine h.trans (le_trans (add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add m1 m2) m3) m4) (by norm_num))
    (mul_le_mul_of_nonneg_left d1 (by norm_num))) (add_le_add dS0 dS1)) (add_le_add dT0 dT1))
    le_rfl) (le_of_eq ?_))
  generalize (2 : ℝ) ^ 1024 = K
  ring

/-- **Theorem 2 with one shared `H₃`, function rows**:

    8·εRO(q_E + 13824, q₅ + 1872, q_E + 13824) + 4·(2⁻¹¹³ + εRO(0, 312, 4607)) + 6·noHitProb
      + 12·2⁻¹⁰²⁴ + 2·εhide. -/
theorem unlinkabilitySh_num (A : AdversaryRO (RowH (Blk → Blk)) Sizes.labelRows) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionR A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameSh A b₁ b₂) - pr _ (realGameSh A b₁' b₂')| ≤
      8 * εRO (qE + 13824) (q5 + 1872) (qE + 13824) + 4 * (1 / 2 ^ 113 + εRO 0 312 4607) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  (unlinkabilitySh_numG A hA hhide b₁ b₂ b₁' b₂').trans (le_of_eq (by
    rw [ZKRow.εz_fn, ZKRow.εz_fn]
    generalize (2 : ℝ) ^ 1024 = K
    ring))

/-- **Theorem 2 with one shared `H₃`, AES as uniformly random permutations**:

    4·εROPm(pI; q_E + 13824, q₅ + 1872, q_E + 13824) + 4·εROPm(pS; q_E + 13824, q₅ + 1872, q_E + 13824)
      + 4·(2⁻¹¹³ + εROPm(pS; 0, 312, 4607)) + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide. -/
theorem unlinkabilitySh_num_perm (A : AdversaryRO (RowH (Equiv.Perm Blk)) Sizes.labelRows)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionR A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameSh A b₁ b₂) - pr _ (realGameSh A b₁' b₂')| ≤
      4 * εROPm pI (qE + 13824) (q5 + 1872) (qE + 13824) +
        4 * εROPm pS (qE + 13824) (q5 + 1872) (qE + 13824) +
        4 * (1 / 2 ^ 113 + εROPm pS 0 312 4607) + 6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilitySh_numG A hA hhide b₁ b₂ b₁' b₂'

end Ratatouille

end VoleMole.Privacy
