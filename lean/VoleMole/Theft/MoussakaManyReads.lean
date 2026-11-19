import VoleMole.Theft.MoussakaManyLean
import VoleMole.Theft.ManyReads
import VoleMole.Theft.SimExtractLean

/-!
# Moussaka Theorem 3 for `U` tokens and `M` redemptions: hop budgets and plain extraction

`noRedirectN_lean` (`Theft/MoussakaManyLean.lean`) assumes the read budgets of the `U + M` hops'
distinguishers and `WeakSEN`. Here, as `Theft/Reads.lean` and `Theft/SimExtractLean.lean` do for
one token:

* **`noRedirectN_lean_reads`**: the hops' budgets are proved (`distPN_budgetLI`,
  `distPN_budgetLR`, from `distN_budget`, `Theft/ManyReads.lean`), with the Lean verifiers
  `verIL`, `verRL`. If the adversary's last stage reads `(a₃, a₅, a_E)` (`StageBudgetN`) and the
  extractor `(x₃, x₅, x_E)`, every hop has the budget

      q = (a₃ + x₃,  a₅ + x₅ + 312 + (U + M − 1)·624,  a_E + x_E + (U + M)·4607).

* **`weakSEN_moussaka`**: `WeakSEN` for the Lean simulators and verifiers, extractor `extOfN e`,
  from plain extraction (`PlainSEN`) and one programmed-point term per simulated proof
  (`SlotEvN i … HitKeyM`), by `weakSEN_of_plain` and `progMovesN_of_slots`.
* **`noRedirectN_lean_plain`**:

      Pr[BadN] ≤ U·εz(pI; q) + M·εz(pR; q) + Σ_i δ_i + ε_plain + Σ_i ε_hit,i
                   + Σ_h Adv^ow(inverter h).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim
  VoleMole.Verifier VoleMole.Verifier.Bridge

variable {U M : ℕ}

/-! ## The hops' budgets, for any provers, verifiers and programmings on the tables -/

section Generic

variable {R : Type} {p : Params} (A : ThiefN U M Tab3 (ShG R p))
  (verI : IssueInstance → Bytes → ShG R p → Bool) (verR : RedeemInstance → Bytes → ShG R p → Bool)
  (ext : ExtN U M Tab3 (ShG R p)) {a3 a5 aE x3 x5 xE v5 vE : ℕ}

/-- **The bad event reads what the adversary's last stage, the extractor and the verifiers
read.** -/
theorem bad_budgetN (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (ext l (opN A l)) x3 x5 xE)
    (hI5 : ∀ x π, Rd5 (verI x π) v5) (hR5 : ∀ x π, Rd5 (verR x π) v5)
    (hIE : ∀ x π, RdE (verI x π) vE) (hRE : ∀ x π, RdE (verR x π) vE) (ω : SecN U) (l : Log) :
    StageBudgetN (BadN A verI verR ext ω l) (a3 + x3) (a5 + (x5 + v5)) (aE + (xE + vE)) :=
  (show StageBudgetN (opN A l) a3 a5 aE from hA _ _).event (V := AccOp verI verR)
    (fun op w acc => acc ∧ FreshOpN l op ∧ (¬ RelOp op w ∨ ∃ h, OpensOp (tOfN A ω h) op w))
    (hX l) (accOp_rd5 verI verR hI5 hR5) (accOp_rdE verI verR hIE hRE)

variable (PI : Bytes → IssueInstance → Bytes → Tab3 → ShG R p → Bytes)
  (PR : Bytes → RedeemInstance → Bytes → Tab3 → ShG R p → Bytes) {s5 sE : ℕ}

lemma PN_rd5 (hPI : ∀ w x ρ g, Rd5 (PI w x ρ g) s5) (hPR : ∀ w x ρ g, Rd5 (PR w x ρ g) s5)
    (ω : SecN U) (l : Log) (r : Coins proveSeedBytes) (g : Tab3) : Rd5 (PN A PI PR ω l r g) s5 :=
  (rd5_proveO (prove := PM PI PR) (rd5_sumProve (fun x w r g => hPI w x (List.ofFn r) g)
    (fun x w r g => hPR w x (List.ofFn r) g)) (xwN A ω l) r g).map (pairO (xN A (pubOf A ω) l))

lemma PN_rdE (hPI : ∀ w x ρ g, RdE (PI w x ρ g) sE) (hPR : ∀ w x ρ g, RdE (PR w x ρ g) sE)
    (ω : SecN U) (l : Log) (r : Coins proveSeedBytes) (g : Tab3) : RdE (PN A PI PR ω l r g) sE :=
  (rdE_proveO (prove := PM PI PR) (rdE_sumProve (fun x w r g => hPI w x (List.ofFn r) g)
    (fun x w r g => hPR w x (List.ofFn r) g)) (xwN A ω l) r g).map (pairO (xN A (pubOf A ω) l))

variable {CI CR : Type} [Nonempty CI] [Nonempty CR] (simI : IssueInstance → CI → Bytes)
  (progI : IssueInstance → CI → ShG R p → ShG R p) (simR : RedeemInstance → CR → Bytes)
  (progR : RedeemInstance → CR → ShG R p → ShG R p) {m5 mE : ℕ}

/-- **The budget of every hop's distinguisher.** -/
theorem distPN_budget (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (ext l (opN A l)) x3 x5 xE)
    (hI5 : ∀ x π, Rd5 (verI x π) v5) (hR5 : ∀ x π, Rd5 (verR x π) v5)
    (hIE : ∀ x π, RdE (verI x π) vE) (hRE : ∀ x π, RdE (verR x π) vE)
    (hPI5 : ∀ w x ρ g, Rd5 (PI w x ρ g) s5) (hPR5 : ∀ w x ρ g, Rd5 (PR w x ρ g) s5)
    (hPIE : ∀ w x ρ g, RdE (PI w x ρ g) sE) (hPRE : ∀ w x ρ g, RdE (PR w x ρ g) sE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpR : ∀ x c, IsProg (progR x c) m5 mE)
    (i : Fin (U + M)) (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (CI × CR) Tab3) :
    Budget p (a3 + x3) ((U + M - (i.val + 1)) * s5 + (a5 + (x5 + v5)) + i.val * m5)
      ((U + M - (i.val + 1)) * sE + (aE + (xE + vE)) + i.val * mE)
      (distPN A PI PR simI progI simR progR verI verR ext i ω τ) :=
  (distN_budget (PN A PI PR) (fun ω => SmP A simI simR (pubOf A ω))
    (fun ω => pgP A progI progR (pubOf A ω)) (BadN A verI verR ext)
    (PN_rd5 A PI PR hPI5 hPR5) (PN_rdE A PI PR hPIE hPRE)
    (fun _ _ c => isProg_progO (isProg_sumProg hpI hpR) _ c)
    (fun ω l => bad_budgetN A verI verR ext hA hX hI5 hR5 hIE hRE ω l) i ω τ).comp
    (fun o : Bytes => pairO (xN A (pubOf A ω)
      (simPre (fun ω => SmP A simI simR (pubOf A ω)) (fun ω => pgP A progI progR (pubOf A ω)) ω
        (tapeC τ) i).1) (some o))

end Generic

/-! ## The Lean prover, verifiers and simulators -/

section Lean

variable {R : Type} [CipherRow R]

lemma leanPI_rd5' (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPI (R := R) w x rho g) 624 :=
  (realROb_rd5 (p := pI) (Hb := Hashes.shake) (st := Privacy.Moussaka.stI x) (w := toBA w)
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

lemma leanPI_rdE' (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) :
    RdE (leanPI (R := R) w x rho g) 4607 :=
  (realROb_rdE (p := pI) (st := Privacy.Moussaka.stI x) (w := toBA w) hashesWF_shake
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

variable (A : ThiefN U M Tab3 (ShM R)) (ext : ExtN U M Tab3 (ShM R)) {a3 a5 aE x3 x5 xE : ℕ}

/-- **The budget of an issuance hop with the Lean prover, verifiers and simulators.** -/
theorem distPN_budgetLI (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (ext l (opN A l)) x3 x5 xE) (i : Fin (U + M)) (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    Budget pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPN A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR verIL verRL ext
        i ω τ) :=
  (distPN_budget A verIL verRL ext leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR
    hA hX verIL_rd5 verRL_rd5 verIL_rdE verRL_rdE leanPI_rd5' leanPR_rd5' leanPI_rdE' leanPR_rdE'
    (fun x c => progRO_isProg c) leanProgR_isProg i ω τ).mono le_rfl
    (by have := i.isLt; omega) (by have := i.isLt; omega)

/-- **The budget of a redemption hop with the Lean prover, verifiers and simulators.** -/
theorem distPN_budgetLR (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (ext l (opN A l)) x3 x5 xE) (i : Fin (U + M)) (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    Budget pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPN A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR verIL verRL ext
        i ω τ) := by
  have h := distPN_budgetLI A ext hA hX i ω τ
  -- (`pI` and `pR` have the same `H₂³` table type)
  exact ⟨h.h3, h.h5, h.hE⟩

section Reads

variable [Fintype R] [Nonempty R] [ZKRow R]

/-- **Redemption non-malleability for `U` tokens and `M` redemptions with the Lean prover and
verifiers, the hops' budgets proved.** For an adversary whose last stage reads `(a₃, a₅, a_E)`
and an extractor that reads `(x₃, x₅, x_E)`:

    Pr[BadN] ≤ U·εz(pI; q) + M·εz(pR; q) + Σ_i δ_i + ε_SE + Σ_h Adv^ow(inverter h),

`q = (a₃ + x₃, a₅ + x₅ + 312 + (U + M − 1)·624, a_E + x_E + (U + M)·4607)`. Weak
simulation-extractability (`hse`) is the remaining hypothesis. -/
theorem noRedirectN_lean_reads {AdmE : ((Fin (U + M) → Tab3) → ShM R → MOp) → Prop} {εSE : ℝ}
    (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (ext l (opN A l)) x3 x5 xE)
    (hse : WeakSEN (U + M) (simM (leanSim pI) (leanSim pR)) (progM leanProgI leanProgR)
      (AccOp verIL verRL) FreshOpN RelOp ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
        (nmRealN A leanPI leanPR verIL verRL ext) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
          (deltaNM A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR i) +
        εSE +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) leanProgI (leanSim pR) leanProgR ext h) :=
  noRedirectN_lean A verIL verRL ext (fun i _ ω τ => distPN_budgetLI A ext hA hX i ω τ)
    (fun i _ ω τ => distPN_budgetLR A ext hA hX i ω τ) hse hAE

end Reads

/-! ## Weak simulation-extractability from plain extraction -/

/-- **`k` is the verifier's `H₂³` key of an operation** on the tables `s`. -/
def PtM (op : MOp) (s : ShM R) (k : K2 pI) : Prop :=
  match op with
  | .issue req ci => enc2 pI k = vPoint (p := pI) Hashes.shake
      (Privacy.Moussaka.stI (stOfI req ci)) (toBA (req.drop uovM)) s
  | .redeem S' req ci cr cd => enc2 pR k = vPoint (p := pR) Hashes.shake
      (Privacy.Moussaka.stR (stOfR S' req ci cr cd)) (toBA (req.drop nfBytes)) s

/-- **`k` is a key the simulation of a statement may program**: its prefix is the grinding prefix
recomputed from the simulated proof (coins `c`) on `H₅` and the cipher. -/
noncomputable def MvM (x : MI) (c : SimCoins pI × SimCoins pR) (b : Tab5F × (Blk → R))
    (k : K2 pI) : Prop :=
  match x with
  | .inl x => k.1 = blk (preLen pI) (@outPre (icPrg (rowFn b.2)) Hashes.shake CrtGen.tables
      (Privacy.Moussaka.stI x) b.1 (simulate pI c.1))
  | .inr x => k.1 = blk (preLen pR) (@outPre (icPrg (rowFn b.2)) Hashes.shake CrtGen.tables
      (Privacy.Moussaka.stR x) b.1 (simulate pR c.2))

/-- **The operation's verifier reads `H₂³` at a key the simulation of `x` may program.** -/
noncomputable def HitKeyM (x : MI) (c : SimCoins pI × SimCoins pR) (op : MOp) (s : ShM R) :
    Prop :=
  ∃ k, PtM op s k ∧ MvM x c s.2 k

lemma progM_snd (x : MI) (c : SimCoins pI × SimCoins pR) (s : ShM R) :
    (progM leanProgI leanProgR x c s).2 = s.2 := by
  rcases x with x | x <;> rfl

lemma progM_moved (x : MI) (c : SimCoins pI × SimCoins pR) (s : ShM R) (k : K2 pI)
    (hk : (progM leanProgI leanProgR x c s).1 k ≠ s.1 k) : MvM x c s.2 k := by
  rcases x with x | x
  · exact progRO_moved (p := pI) Hashes.shake (Privacy.Moussaka.stI x) c.1 s k hk
  · exact progRO_moved (p := pR) Hashes.shake (Privacy.Moussaka.stR x) c.2 s k hk

lemma accOp_ptM (op : MOp) (s' s : ShM R) (h2 : s'.2 = s.2)
    (h' : AccOp verIL verRL op s') (h : ¬ AccOp verIL verRL op s) :
    ∃ k, PtM op s k ∧ s'.1 k ≠ s.1 k := by
  have hm := accOp_moves op s' s h2 h' h
  cases op <;> exact hm

variable [Fintype R]

/-- **Weak simulation-extractability of the Lean simulators and verifiers with `U + M` simulated
proofs, from plain extraction** and, for each simulated proof, fresh forgeries whose verifier
reads a key that proof may program. -/
theorem weakSEN_moussaka
    {e : Log → MOp → (Fin (U + M) → Tab3) → Tab5F × (Blk → R) → Bytes} {ε₀ : ℝ}
    {εh : Fin (U + M) → ℝ}
    (hplain : PlainSEN (U + M) (AccOp verIL verRL) FreshOpN RelOp e
      (fun F => StageBudgetN F a3 (a5 + (U + M) * 312) (aE + (U + M) * 4607)) ε₀)
    (hhit : ∀ i, SlotEvN (U + M) i (simM (leanSim pI) (leanSim pR)) (progM leanProgI leanProgR)
      FreshOpN (HitKeyM (R := R)) (fun F => StageBudgetN F a3 a5 aE) (εh i)) :
    WeakSEN (U + M) (simM (leanSim pI) (leanSim pR)) (progM leanProgI leanProgR)
      (AccOp verIL verRL) FreshOpN RelOp (extOfN e) (fun F => StageBudgetN F a3 a5 aE)
      (ε₀ + ∑ i, εh i) :=
  weakSEN_of_plain hplain
    (progMovesN_of_slots progM_snd accOp_ptM progM_moved hhit) progM_snd
    fun _ _ hL hF => hF.comp_prog
      (hL.isProg (isProg_sumProg (fun _ c => progRO_isProg c) leanProgR_isProg))

variable [Nonempty R] [ZKRow R]

/-- **Redemption non-malleability for `U` tokens and `M` redemptions with the Lean prover,
verifiers and simulators, with plain extraction**:

    Pr[BadN] ≤ U·εz(pI; q) + M·εz(pR; q) + Σ_i δ_i + ε_plain + Σ_i ε_hit,i
                 + Σ_h Adv^ow(inverter h),

`q = (a₃ + x₃, a₅ + x₅ + 312 + (U + M − 1)·624, a_E + x_E + (U + M)·4607)`. -/
theorem noRedirectN_lean_plain
    {e : Log → MOp → (Fin (U + M) → Tab3) → Tab5F × (Blk → R) → Bytes} {ε₀ : ℝ}
    {εh : Fin (U + M) → ℝ}
    (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (extOfN e l (opN A l)) x3 x5 xE)
    (hplain : PlainSEN (U + M) (AccOp verIL verRL) FreshOpN RelOp e
      (fun F => StageBudgetN F a3 (a5 + (U + M) * 312) (aE + (U + M) * 4607)) ε₀)
    (hhit : ∀ i, SlotEvN (U + M) i (simM (leanSim pI) (leanSim pR)) (progM leanProgI leanProgR)
      FreshOpN (HitKeyM (R := R)) (fun F => StageBudgetN F a3 a5 aE) (εh i)) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
        (nmRealN A leanPI leanPR verIL verRL (extOfN e)) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
          (deltaNM A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR i) +
        (ε₀ + ∑ i, εh i) +
        ∑ h : Fin U, owAdv (A.ci h) (A.cr h)
          (inverterN A (leanSim pI) leanProgI (leanSim pR) leanProgR (extOfN e) h) :=
  noRedirectN_lean_reads A (extOfN e) hA hX (weakSEN_moussaka hplain hhit)
    fun _ => hA _ _

end Lean

end VoleMole.Theft.Moussaka
