import VoleMole.Theft.MoussakaUnboundManyReads
import VoleMole.Theft.ManyTables

/-!
# Unbound Moussaka for `U` tokens and `M` redemptions with the other hashes read off a random table

`nmUN_lean_plain` (`Theft/MoussakaUnboundManyReads.lean`) has SHAKE for `H₁`, `H₂⁰`, `H₂¹`, `H₂²`,
`H₄` and `H_comb`. Here, as `Theft/LeanHb.lean` and `Theft/Tables.lean` do for the bound
relations:

* `leanPIUH`, `leanPRUH`, `leanProgIUH`, `leanProgRUH`, `verILUH`, `verRLUH`: the Lean unbound
  provers, programmings and verifiers for any base record `Hb`; zero knowledge for every
  well-formed record (`leanPIUH_zkRO`, `leanPRUH_zkRO`, as `Privacy.MoussakaUnbound.leanPI_zkRO`
  with `Hb` for SHAKE), their read budgets, and `accOp_movesUH` (the programming moves the
  verifiers only at their `H₂³` point).
* `leanPIUX`, …, `verRLUX`: the same with the base record read off one more uniform shared table
  `x : X` (`ShX R pI X`), zero knowledge with the extra table (`zkRO_tables`), `accOp_movesUX`.
* `atTN`, `PN_atX`, `pgP_atX`, `badN_atX`: the game at a value of the extra table.
  **`distPN_budgetUXI`**, **`distPN_budgetUXR`**: the hops' read budgets, at every value of the
  extra table (`distN_budgetX`).
* **`nmUN_leanX_plain`**: `nmUN` in this model, with `WeakSEN` replaced by plain extraction and
  the programming term (`ProgMovesN`), both for uniform `X`:

      Pr[BadN] ≤ U·εz(pI; q) + M·εz(pR; q) + Σ_i δ_i + (ε_plain + ε_moves)
                   + Σ_h (ε_prf + (M+1)·2⁻¹⁹² + Adv^bind(B₁ h) + Adv^spr-k(B₂ h)),

  `q = (a₃ + x₃, a₅ + x₅ + 312 + (U + M − 1)·624, a_E + x_E + (U + M)·4607)`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.MoussakaUnbound

open VoleMole.Privacy VoleMole.Privacy.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
  VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Spec.Moussaka (AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes)
open VoleMole.Privacy.Moussaka (ShM leanSim ProverRO)

variable {U M : ℕ}

/-! ## Any base record -/

section H

variable {R : Type} [CipherRow R] (Hb : Hashes)

/-- The Lean unbound issuance prover on the tables, base record `Hb`. -/
noncomputable def leanPIUH : ProverRO R IssueInstance := fun w x rho g s =>
  toL ((realROb pI Hb (Privacy.MoussakaUnbound.stI x) (toBA w) (toBA rho) g s).toOption.getD
    .empty)

/-- The Lean unbound redemption prover on the tables, base record `Hb`. -/
noncomputable def leanPRUH : ProverRO R RedeemInstance := fun w x rho g s =>
  toL ((realROb pR Hb (Privacy.MoussakaUnbound.stR x) (toBA w) (toBA rho) g s).toOption.getD
    .empty)

/-- The simulators' programmings, base record `Hb`. -/
noncomputable def leanProgIUH (x : IssueInstance) (c : SimCoins pI) : ShM R → ShM R :=
  progRO pI Hb (Privacy.MoussakaUnbound.stI x) c
noncomputable def leanProgRUH (x : RedeemInstance) (c : SimCoins pR) : ShM R → ShM R :=
  progRO pR Hb (Privacy.MoussakaUnbound.stR x) c

/-- The Lean unbound verifiers on the shared tables, base record `Hb`. -/
noncomputable def verILUH : IssueInstance → Bytes → ShM R → Bool := fun x pf s =>
  (verRO pI Hb (Privacy.MoussakaUnbound.stI x) (toBA pf) s).accept
noncomputable def verRLUH : RedeemInstance → Bytes → ShM R → Bool := fun x pf s =>
  (verRO pR Hb (Privacy.MoussakaUnbound.stR x) (toBA pf) s).accept

lemma leanPIUH_shake : leanPIUH (R := R) Hashes.shake = leanPI := rfl
lemma leanPRUH_shake : leanPRUH (R := R) Hashes.shake = leanPR := rfl
lemma leanProgIUH_shake : leanProgIUH (R := R) Hashes.shake = leanProgI := rfl
lemma leanProgRUH_shake : leanProgRUH (R := R) Hashes.shake = leanProgR := rfl
lemma verILUH_shake : verILUH (R := R) Hashes.shake = verILU := rfl
lemma verRLUH_shake : verRLUH (R := R) Hashes.shake = verRLU := rfl

variable {Hb}

/-- **Zero knowledge of the Lean unbound issuance prover, for any base record.** -/
theorem leanPIUH_zkRO [Fintype R] [ZKRow R] (hHb : HashesWF Hb) (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPIUH Hb w x (List.ofFn ρ) g s)
      (leanSim pI) (leanProgIUH Hb) (Budget pI q3 q5 qE) (ZKRow.εz R pI q3 q5 qE) := by
  have h := (lean_zeroKnowledgeROG (R := R) Hb pI Privacy.MoussakaUnbound.stI (fun _ => rfl) rfl
    (fun _ w => toBA w) IssueRelW csI zkHypI hHb
    (smallParams_of_le (by decide) (by decide)) q3 q5 qE).transfer
    id (fun _ w => w) (fun _ _ h => h) (fun o => toL (o.toOption.getD .empty))
    (fun D hD => Budget.comp _ hD)
  have e : (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) =>
      leanPIUH Hb w x (List.ofFn ρ) g s) =
      fun x w r g s => toL ((realRO pI Hb (Privacy.MoussakaUnbound.stI (id x)) (toBA w) r g
        s).toOption.getD .empty) := by
    funext x w ρ g s
    simp only [leanPIUH, realRO, toBA_ofFn, id]
  rw [e]
  exact h

/-- **Zero knowledge of the Lean unbound redemption prover, for any base record.** -/
theorem leanPRUH_zkRO [Fintype R] [ZKRow R] (hHb : HashesWF Hb) (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPRUH Hb w x (List.ofFn ρ) g s)
      (leanSim pR) (leanProgRUH Hb) (Budget pR q3 q5 qE) (ZKRow.εz R pR q3 q5 qE) := by
  have h := (lean_zeroKnowledgeROG (R := R) Hb pR Privacy.MoussakaUnbound.stR (fun _ => rfl) rfl
    (fun _ w => toBA w) RedeemRelW csR zkHypR hHb
    (smallParams_of_le (by decide) (by decide)) q3 q5 qE).transfer
    id (fun _ w => w) (fun _ _ h => h) (fun o => toL (o.toOption.getD .empty))
    (fun D hD => Budget.comp _ hD)
  have e : (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) =>
      leanPRUH Hb w x (List.ofFn ρ) g s) =
      fun x w r g s => toL ((realRO pR Hb (Privacy.MoussakaUnbound.stR (id x)) (toBA w) r g
        s).toOption.getD .empty) := by
    funext x w ρ g s
    simp only [leanPRUH, realRO, toBA_ofFn, id]
  rw [e]
  exact h

variable (Hb)

lemma verILUH_rd5 (x : IssueInstance) (pf : Bytes) : Rd5 (verILUH (R := R) Hb x pf) 312 :=
  (verRO_rd5 (p := pI) (Privacy.MoussakaUnbound.stI x) (toBA pf)).map Transcript.accept

lemma verILUH_rdE (x : IssueInstance) (pf : Bytes) : RdE (verILUH (R := R) Hb x pf) 4607 :=
  (verRO_rdE (p := pI) (Privacy.MoussakaUnbound.stI x) (toBA pf)).map Transcript.accept

lemma verRLUH_rd5 (x : RedeemInstance) (pf : Bytes) : Rd5 (verRLUH (R := R) Hb x pf) 312 :=
  (verRO_rd5 (p := pR) (Privacy.MoussakaUnbound.stR x) (toBA pf)).map Transcript.accept

lemma verRLUH_rdE (x : RedeemInstance) (pf : Bytes) : RdE (verRLUH (R := R) Hb x pf) 4607 :=
  (verRO_rdE (p := pR) (Privacy.MoussakaUnbound.stR x) (toBA pf)).map Transcript.accept

lemma leanPIUH_rd5 (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPIUH (R := R) Hb w x rho g) 624 :=
  (realROb_rd5 (p := pI) (Hb := Hb) (st := Privacy.MoussakaUnbound.stI x) (w := toBA w)
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

lemma leanPRUH_rd5 (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPRUH (R := R) Hb w x rho g) 624 :=
  (realROb_rd5 (p := pR) (Hb := Hb) (st := Privacy.MoussakaUnbound.stR x) (w := toBA w)
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

variable {Hb}

lemma leanPIUH_rdE (hHb : HashesWF Hb) (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) :
    RdE (leanPIUH (R := R) Hb w x rho g) 4607 :=
  (realROb_rdE (p := pI) (st := Privacy.MoussakaUnbound.stI x) (w := toBA w) hHb
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

lemma leanPRUH_rdE (hHb : HashesWF Hb) (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    RdE (leanPRUH (R := R) Hb w x rho g) 4607 :=
  (realROb_rdE (p := pR) (st := Privacy.MoussakaUnbound.stR x) (w := toBA w) hHb
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

variable (Hb)

lemma leanProgIUH_isProg (x : IssueInstance) (c : SimCoins pI) :
    IsProg (p := Privacy.Moussaka.pI) (leanProgIUH (R := R) Hb x c) 312 4607 := by
  have h := progRO_isProg (R := R) (p := pI) (Hb := Hb) (st := Privacy.MoussakaUnbound.stI x) c
  exact ⟨h.1, h.2.1, h.2.2⟩

lemma leanProgRUH_isProg (x : RedeemInstance) (c : SimCoins pR) :
    IsProg (p := Privacy.Moussaka.pI) (leanProgRUH (R := R) Hb x c) 312 4607 := by
  have h := progRO_isProg (R := R) (p := pR) (Hb := Hb) (st := Privacy.MoussakaUnbound.stR x) c
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- **The verifier's `H₂³` point of an operation is a programmed point**, base record `Hb`. -/
def HitOpUH (op : UOp) (s' s : ShM R) : Prop :=
  match op with
  | .issue req ci => HitPt (p := pI) Hb (Privacy.MoussakaUnbound.stI (stOfI req ci))
      (toBA (req.drop uovM)) s' s
  | .redeem S' req ci cr cd => HitPt (p := pR) Hb
      (Privacy.MoussakaUnbound.stR (stOfR S' req ci cr cd)) (toBA (req.drop nfBytes)) s' s

/-- **The programming moves the Lean unbound verifiers only at their `H₂³` point**, base record
`Hb`. -/
theorem accOp_movesUH (op : UOp) (s' s : ShM R) (h2 : s'.2 = s.2)
    (h' : AccOp (verILUH Hb) (verRLUH Hb) op s') (h : ¬ AccOp (verILUH Hb) (verRLUH Hb) op s) :
    HitOpUH Hb op s' s := by
  cases op with
  | issue req ci =>
    exact verRO_accept_moved (p := pI) _ _ _ s' s h2 h'.2.2 fun hn => h ⟨h'.1, h'.2.1, hn⟩
  | redeem S' req ci cr cd =>
    exact verRO_accept_moved (p := pR) _ _ _ s' s h2 h'.2.2.2
      fun hn => h ⟨h'.1, h'.2.1, h'.2.2.1, hn⟩

end H

/-! ## The base record read off one more uniform table -/

section X

variable {R : Type} [CipherRow R] {X : Type} (Hb : X → Hashes)

/-- The Lean unbound provers, the base record read off the extra table. -/
noncomputable def leanPIUX : Bytes → IssueInstance → Bytes → Tab3 → ShX R Privacy.Moussaka.pI X →
    Bytes :=
  fun w x rho g t => leanPIUH (Hb t.2.2) w x rho g (shOf t)
noncomputable def leanPRUX : Bytes → RedeemInstance → Bytes → Tab3 →
    ShX R Privacy.Moussaka.pI X → Bytes :=
  fun w x rho g t => leanPRUH (Hb t.2.2) w x rho g (shOf t)

/-- The simulators' programmings. -/
noncomputable def leanProgIUX : IssueInstance → SimCoins pI → ShX R Privacy.Moussaka.pI X →
    ShX R Privacy.Moussaka.pI X :=
  progX fun x => leanProgIUH (Hb x)
noncomputable def leanProgRUX : RedeemInstance → SimCoins pR → ShX R Privacy.Moussaka.pI X →
    ShX R Privacy.Moussaka.pI X :=
  progX fun x => leanProgRUH (Hb x)

/-- The Lean unbound verifiers. -/
noncomputable def verILUX : IssueInstance → Bytes → ShX R Privacy.Moussaka.pI X → Bool :=
  fun x pf t => verILUH (Hb t.2.2) x pf (shOf t)
noncomputable def verRLUX : RedeemInstance → Bytes → ShX R Privacy.Moussaka.pI X → Bool :=
  fun x pf t => verRLUH (Hb t.2.2) x pf (shOf t)

variable {Hb}

/-- **Zero knowledge of the Lean unbound issuance prover with the extra table.** -/
theorem leanPIUX_zkRO [Fintype R] [ZKRow R] [Fintype X] [Nonempty X]
    (hHb : ∀ x, HashesWF (Hb x)) (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g (t : ShX R Privacy.Moussaka.pI X) =>
        leanPIUX Hb w x (List.ofFn ρ) g t)
      (leanSim pI) (leanProgIUX Hb) (BudgetX pI q3 q5 qE) (ZKRow.εz R pI q3 q5 qE) :=
  zkRO_tables eX
    (fun x i w (ρ : Coins proveSeedBytes) g s => leanPIUH (Hb x) w i (List.ofFn ρ) g s)
    (leanSim pI) (fun x => leanProgIUH (Hb x)) (fun _ => Budget pI q3 q5 qE)
    fun x => leanPIUH_zkRO (hHb x) _ _ _

/-- **Zero knowledge of the Lean unbound redemption prover with the extra table.** -/
theorem leanPRUX_zkRO [Fintype R] [ZKRow R] [Fintype X] [Nonempty X]
    (hHb : ∀ x, HashesWF (Hb x)) (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g (t : ShX R Privacy.Moussaka.pI X) =>
        leanPRUX Hb w x (List.ofFn ρ) g t)
      (leanSim pR) (leanProgRUX Hb) (BudgetX pR q3 q5 qE) (ZKRow.εz R pR q3 q5 qE) :=
  zkRO_tables eX
    (fun x i w (ρ : Coins proveSeedBytes) g s => leanPRUH (Hb x) w i (List.ofFn ρ) g s)
    (leanSim pR) (fun x => leanProgRUH (Hb x)) (fun _ => Budget pR q3 q5 qE)
    fun x => leanPRUH_zkRO (hHb x) _ _ _

lemma accOp_atXU (op : UOp) (x : X) (s : ShM R) :
    AccOp (verILUX Hb) (verRLUX Hb) op (atX s x) =
      AccOp (verILUH (Hb x)) (verRLUH (Hb x)) op s := by
  cases op <;> rfl

/-- **The verifier's `H₂³` point of an operation is a programmed point**, the base record read
off the extra table. -/
def HitOpUX (op : UOp) (t' t : ShX R Privacy.Moussaka.pI X) : Prop :=
  HitOpUH (Hb t.2.2) op (shOf t') (shOf t)

variable (Hb) in
/-- **The programming moves the Lean unbound verifiers only at their `H₂³` point.** -/
theorem accOp_movesUX (op : UOp) (t' t : ShX R Privacy.Moussaka.pI X) (h2 : t'.2 = t.2)
    (h' : AccOp (verILUX Hb) (verRLUX Hb) op t') (h : ¬ AccOp (verILUX Hb) (verRLUX Hb) op t) :
    HitOpUX (Hb := Hb) op t' t := by
  obtain ⟨a', b'⟩ := t'
  obtain ⟨a, b⟩ := t
  simp only at h2
  subst h2
  exact accOp_movesUH (Hb b'.2) op (a', b'.1) (a, b'.1) rfl h' h

/-! ### The game at a value of the extra table -/

variable (Hb) (A : ThiefN U M Tab3 (ShX R Privacy.Moussaka.pI X))

/-- **The adversary at a value of the extra table.** -/
def atTN (x : X) : ThiefN U M Tab3 (ShM R) :=
  ⟨A.ctxIss, A.pk, A.respond, A.choose, fun reqs reds g s => A.out reqs reds g (atX s x)⟩

variable (e : Log → UOp → (Fin (U + M) → Tab3) → (Tab5F × (Blk → R)) × X → Bytes)

/-- The extractor at a value of the extra table. -/
def eAt (x : X) : Log → UOp → (Fin (U + M) → Tab3) → Tab5F × (Blk → R) → Bytes :=
  fun l o g b => e l o g (b, x)

omit [CipherRow R] in
lemma xN_atTN (x : X) (p : Pub U) (l : Log) : xN (atTN A x) p l = xN A p l := rfl

lemma PN_atX (x : X) (ω : SecN U) (l : Log) (ρ : Coins proveSeedBytes) (g : Tab3) (s : ShM R) :
    PN A (leanPIUX Hb) (leanPRUX Hb) ω l ρ g (atX s x) =
      PN (atTN A x) (leanPIUH (Hb x)) (leanPRUH (Hb x)) ω l ρ g s := by
  have hw : xwN (atTN A x) ω l = xwN A ω l := rfl
  unfold PN
  rw [xN_atTN, hw]
  rcases xwN A ω l with _ | ⟨xi, w⟩
  · rfl
  · rcases xi with xi | xi <;> rfl

lemma pgP_atX (x : X) (p : Pub U) (l : Log) (c : SimCoins pI × SimCoins pR) (s : ShM R) :
    pgP A (leanProgIUX Hb) (leanProgRUX Hb) p l c (atX s x) =
      atX (pgP (atTN A x) (leanProgIUH (Hb x)) (leanProgRUH (Hb x)) p l c s) x := by
  unfold pgP
  rw [xN_atTN]
  rcases xN A p l with _ | xi
  · rfl
  · rcases xi with xi | xi <;> rfl

lemma badN_atX (x : X) (ω : SecN U) (l : Log) (g : Fin (U + M) → Tab3) (s : ShM R) :
    BadN A (verILUX Hb) (verRLUX Hb) (extOfN e) ω l g (atX s x) =
      BadN (atTN A x) (verILUH (Hb x)) (verRLUH (Hb x)) (extOfN (eAt e x)) ω l g s := by
  simp only [BadN, accN, accOp_atXU]
  rfl

variable {Hb} {a3 a5 aE x3 x5 xE : ℕ}

/-- **The budget of every hop's distinguisher, at every value of the extra table.** -/
theorem distN_budgetUX (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (extOfN e l (opN A l)) x3 x5 xE) (i : Fin (U + M))
    (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    BudgetX Privacy.Moussaka.pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
      (aE + xE + (U + M) * 4607)
      (distN (PN A (leanPIUX Hb) (leanPRUX Hb))
        (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
        (fun ω => pgP A (leanProgIUX Hb) (leanProgRUX Hb) (pubOf A ω))
        (BadN A (verILUX Hb) (verRLUX Hb) (extOfN e)) i ω τ) :=
  (distN_budgetX (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
    (fun x => PN (atTN A x) (leanPIUH (Hb x)) (leanPRUH (Hb x)))
    (fun x ω => pgP (atTN A x) (leanProgIUH (Hb x)) (leanProgRUH (Hb x)) (pubOf A ω))
    (fun x => BadN (atTN A x) (verILUH (Hb x)) (verRLUH (Hb x)) (extOfN (eAt e x)))
    (fun x ω l r g s => PN_atX Hb A x ω l r g s)
    (fun x ω l c s => pgP_atX Hb A x (pubOf A ω) l c s)
    (fun x ω l g s => badN_atX Hb A e x ω l g s)
    (fun x => PN_rd5 (atTN A x) _ _ (leanPIUH_rd5 (Hb x)) (leanPRUH_rd5 (Hb x)))
    (fun x => PN_rdE (atTN A x) _ _ (leanPIUH_rdE (hHb x)) (leanPRUH_rdE (hHb x)))
    (fun x _ _ c => isProg_progO (isProg_sumProg (leanProgIUH_isProg (Hb x))
      (leanProgRUH_isProg (Hb x))) _ c)
    (fun x ω l => bad_budgetN (atTN A x) (verILUH (Hb x)) (verRLUH (Hb x)) (extOfN (eAt e x))
      (fun reqs reds => hA reqs reds x) (fun l => hX l x) (verILUH_rd5 (Hb x))
      (verRLUH_rd5 (Hb x)) (verILUH_rdE (Hb x)) (verRLUH_rdE (Hb x)) ω l) i ω τ).mono le_rfl
    (by have := i.isLt; omega) (by have := i.isLt; omega)

/-- **The budget of an issuance hop**, at every value of the extra table. -/
theorem distPN_budgetUXI (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (extOfN e l (opN A l)) x3 x5 xE) (i : Fin (U + M))
    (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPN A (leanPIUX Hb) (leanPRUX Hb) (leanSim pI) (leanProgIUX Hb) (leanSim pR)
        (leanProgRUX Hb) (verILUX Hb) (verRLUX Hb) (extOfN e) i ω τ) := by
  have h := (distN_budgetUX A e hHb hA hX i ω τ).comp
    (fun o : Bytes => pairO (xN A (pubOf A ω)
      (simPre (fun ω => SmP A (leanSim pI) (leanSim pR) (pubOf A ω))
        (fun ω => pgP A (leanProgIUX Hb) (leanProgRUX Hb) (pubOf A ω)) ω (tapeC τ) i).1)
      (some o))
  -- (the unbound parameters have the `H₂³` table type of the shared tables)
  exact fun x => ⟨(h x).h3, (h x).h5, (h x).hE⟩

/-- **The budget of a redemption hop**, at every value of the extra table. -/
theorem distPN_budgetUXR (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (extOfN e l (opN A l)) x3 x5 xE) (i : Fin (U + M))
    (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    BudgetX pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPN A (leanPIUX Hb) (leanPRUX Hb) (leanSim pI) (leanProgIUX Hb) (leanSim pR)
        (leanProgRUX Hb) (verILUX Hb) (verRLUX Hb) (extOfN e) i ω τ) := by
  have h := distPN_budgetUXI A e hHb hA hX i ω τ
  exact fun x => ⟨(h x).h3, (h x).h5, (h x).hE⟩

lemma progU_sndX (x : UI) (c : SimCoins pI × SimCoins pR) (t : ShX R Privacy.Moussaka.pI X) :
    (progU (leanProgIUX Hb) (leanProgRUX Hb) x c t).2 = t.2 := by
  rcases x with x | x <;> rfl

variable [Fintype R] [Nonempty R] [ZKRow R] [Fintype X] [Nonempty X]

/-- **Unbound non-malleability for `U` tokens and `M` redemptions with the extra table, from a
bound on the simulated game's `Acc ∧ Fresh ∧ ¬ Rel` event**: the zero-knowledge hops and their
budgets (`nmUN_of_se`). -/
theorem nmUN_leanX_of_se (hHb : ∀ x, HashesWF (Hb x)) {εSE εprf : ℝ}
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (extOfN e l (opN A l)) x3 x5 xE)
    (hse' : pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R Privacy.Moussaka.pI X))
      (nmSimN A (leanSim pI) (leanProgIUX Hb) (leanSim pR) (leanProgRUX Hb)
        (seEvN A (verILUX Hb) (verRLUX Hb) (extOfN e))) ≤ εSE)
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX Hb) (leanSim pR)
      (leanProgRUX Hb) (extOfN e) h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R Privacy.Moussaka.pI X))
        (nmRealNE A (leanPIUX Hb) (leanPRUX Hb) (BadN A (verILUX Hb) (verRLUX Hb) (extOfN e))) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R Privacy.Moussaka.pI X))
          (deltaNU A (leanPIUX Hb) (leanPRUX Hb) (leanSim pI) (leanProgIUX Hb) (leanSim pR)
            (leanProgRUX Hb) i) +
        εSE +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX Hb) (leanSim pR) (leanProgRUX Hb)
            (extOfN e) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX Hb) (leanSim pR) (leanProgRUX Hb)
            (extOfN e) h)) :=
  nmUN_of_se (CI := SimCoins pI) (CR := SimCoins pR) A (leanPIUX Hb) (leanPRUX Hb) (leanSim pI)
    (leanProgIUX Hb) (leanSim pR) (leanProgRUX Hb) (verILUX Hb) (verRLUX Hb) (extOfN e)
    (leanPIUX_zkRO hHb _ _ _) (ZKRow.εz_nonneg _ _ _ _) (leanPRUX_zkRO hHb _ _ _)
    (ZKRow.εz_nonneg _ _ _ _) (fun i _ ω τ => distPN_budgetUXI A e hHb hA hX i ω τ)
    (fun i _ ω τ => distPN_budgetUXR A e hHb hA hX i ω τ) hse' pts hpts hprf

/-- **Unbound non-malleability and no squatting for `U` tokens and `M` redemptions with the other
hashes read off a uniform table, with plain extraction**: as `nmUN_lean_plain`, in the model of
`noRedirect_leanX_plain`. The programming term `ε_moves` (`ProgMovesN`) and plain extraction are
for the game's freshness `FreshOpN`, against classes `Adm`, `Adm₀` of the caller's choice
(`hadm`: the last stage composed with `U + M` programmings is in `Adm₀`). -/
theorem nmUN_leanX_plain (hHb : ∀ x, HashesWF (Hb x))
    {Adm Adm₀ : ((Fin (U + M) → Tab3) → ShX R Privacy.Moussaka.pI X → UOp) → Prop}
    {ε₀ εm εprf : ℝ}
    (hA : ∀ reqs reds, StageBudgetNX (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetNX (extOfN e l (opN A l)) x3 x5 xE)
    (hplain : PlainSEN (U + M) (AccOp (verILUX Hb) (verRLUX Hb)) FreshOpN RelOp e Adm₀ ε₀)
    (hmoves : ProgMovesN (U + M) (simU (leanSim pI) (leanSim pR))
      (progU (leanProgIUX Hb) (leanProgRUX Hb)) (AccOp (verILUX Hb) (verRLUX Hb)) FreshOpN Adm
      εm)
    (hAdm : ∀ reqs reds, Adm (A.out reqs reds))
    (hadm : ∀ F L, IsProgs (progU (leanProgIUX Hb) (leanProgRUX Hb)) (U + M) L → Adm F →
      Adm₀ (fun g s => F g (L s)))
    (pts : Fin (M + 1) → Coins ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h) (owkDN (keyBN A (leanSim pI) (leanProgIUX Hb) (leanSim pR)
      (leanProgRUX Hb) (extOfN e) h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R Privacy.Moussaka.pI X))
        (nmRealNE A (leanPIUX Hb) (leanPRUX Hb) (BadN A (verILUX Hb) (verRLUX Hb) (extOfN e))) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShX R Privacy.Moussaka.pI X))
          (deltaNU A (leanPIUX Hb) (leanPRUX Hb) (leanSim pI) (leanProgIUX Hb) (leanSim pR)
            (leanProgRUX Hb) i) +
        (ε₀ + εm) +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) (leanProgIUX Hb) (leanSim pR) (leanProgRUX Hb)
            (extOfN e) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) (leanProgIUX Hb) (leanSim pR) (leanProgRUX Hb)
            (extOfN e) h)) :=
  nmUN_leanX_of_se A e hHb hA hX
    (sim_se_leN A (leanSim pI) (leanProgIUX Hb) (leanSim pR) (leanProgRUX Hb) (verILUX Hb)
      (verRLUX Hb) (extOfN e) (weakSEN_of_plain hplain hmoves progU_sndX hadm)
      fun _ => hAdm _ _) pts hpts hprf

end X

end VoleMole.Theft.MoussakaUnbound
