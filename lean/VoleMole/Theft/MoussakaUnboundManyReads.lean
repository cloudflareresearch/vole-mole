import VoleMole.Theft.MoussakaUnboundLean
import VoleMole.Theft.ManyReads
import VoleMole.Theft.SimExtractLean

/-!
# Unbound Moussaka Prop U3 / Thm U4 for `U` tokens and `M` redemptions: hop budgets and plain
extraction

`nmUN_lean`, `noSquatN_lean` and `noRedirectUN_lean` (`Theft/MoussakaUnboundLean.lean`) assume the
read budgets of the `U + M` hops' distinguishers and `WeakSEN`. Here:

* **The Lean verifiers** of the unbound relations on the shared tables (`verILU`, `verRLU`:
  `ZK.Sim.verRO` with SHAKE for the hashes that are not tables).
* **`nmUN_lean_reads`**, **`noSquatN_lean_reads`**, **`noRedirectUN_lean_reads`**: the hops'
  budgets are proved (`distPN_budgetLI`, `distPN_budgetLR`, from `distN_budget`,
  `Theft/ManyReads.lean`). If the adversary's last stage reads `(a₃, a₅, a_E)` (`StageBudgetN`)
  and the extractor `(x₃, x₅, x_E)`, every hop has the budget

      q = (a₃ + x₃,  a₅ + x₅ + 312 + (U + M − 1)·624,  a_E + x_E + (U + M)·4607).

* **`weakSEN_moussakaU`**: `WeakSEN` for the Lean simulators and verifiers, extractor `extOfN e`,
  from plain extraction (`PlainSEN`) and one programmed-point term per simulated proof
  (`SlotEvN i … HitKeyU`), by `weakSEN_of_plain` and `progMovesN_of_slots`.
* **`nmUN_lean_plain`**, **`noSquatN_lean_plain`**, **`noRedirectUN_lean_plain`**: the three
  theorems with `ε_SE` replaced by `ε_plain + Σ_i ε_hit,i`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.MoussakaUnbound

open VoleMole.Privacy VoleMole.Privacy.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
  VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Spec.Moussaka (AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes)
open VoleMole.Privacy.Moussaka (ShM leanSim)

variable {U M : ℕ}

/-! ## The hops' budgets, for any provers, verifiers and programmings on the tables -/

section Generic

variable {R : Type} {p : Params} (A : ThiefN U M Tab3 (ShG R p))
  (verI : IssueInstance → Bytes → ShG R p → Bool) (verR : RedeemInstance → Bytes → ShG R p → Bool)
  (ext : ExtN U M Tab3 (ShG R p)) {a3 a5 aE x3 x5 xE v5 vE : ℕ}

lemma accOp_rd5 (hI : ∀ x π, Rd5 (verI x π) v5) (hR : ∀ x π, Rd5 (verR x π) v5) (op : UOp) :
    Rd5 (AccOp verI verR op) v5 := by
  cases op with
  | issue req ci => exact (hI _ _).map fun b => req.length = uovM + issueProofBytes ∧
      ci.length = ctxBytes ∧ b = true
  | redeem S' req ci cr cd => exact (hR _ _).map fun b =>
      req.length = nfBytes + redeemProofBytes ∧ ci.length = ctxBytes ∧ cr.length = ctxBytes ∧
        b = true

lemma accOp_rdE (hI : ∀ x π, RdE (verI x π) vE) (hR : ∀ x π, RdE (verR x π) vE) (op : UOp) :
    RdE (AccOp verI verR op) vE := by
  cases op with
  | issue req ci => exact (hI _ _).map fun b => req.length = uovM + issueProofBytes ∧
      ci.length = ctxBytes ∧ b = true
  | redeem S' req ci cr cd => exact (hR _ _).map fun b =>
      req.length = nfBytes + redeemProofBytes ∧ ci.length = ctxBytes ∧ cr.length = ctxBytes ∧
        b = true

/-- **The bad event reads what the adversary's last stage, the extractor and the verifiers
read.** -/
theorem bad_budgetN (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (ext l (opN A l)) x3 x5 xE)
    (hI5 : ∀ x π, Rd5 (verI x π) v5) (hR5 : ∀ x π, Rd5 (verR x π) v5)
    (hIE : ∀ x π, RdE (verI x π) vE) (hRE : ∀ x π, RdE (verR x π) vE) (ω : SecN U) (l : Log) :
    StageBudgetN (BadN A verI verR ext ω l) (a3 + x3) (a5 + (x5 + v5)) (aE + (xE + vE)) :=
  (show StageBudgetN (opN A l) a3 a5 aE from hA _ _).event (V := AccOp verI verR)
    (fun op w acc => acc ∧ FreshOpN l op ∧
      (¬ RelOp op w ∨ ∃ h, HitOp (tOfN A ω h) (List.ofFn (ω h).1) op w))
    (hX l) (accOp_rd5 verI verR hI5 hR5) (accOp_rdE verI verR hIE hRE)

variable (PI : Bytes → IssueInstance → Bytes → Tab3 → ShG R p → Bytes)
  (PR : Bytes → RedeemInstance → Bytes → Tab3 → ShG R p → Bytes) {s5 sE : ℕ}

lemma PN_rd5 (hPI : ∀ w x ρ g, Rd5 (PI w x ρ g) s5) (hPR : ∀ w x ρ g, Rd5 (PR w x ρ g) s5)
    (ω : SecN U) (l : Log) (r : Coins proveSeedBytes) (g : Tab3) : Rd5 (PN A PI PR ω l r g) s5 :=
  (rd5_proveO (prove := PU PI PR) (rd5_sumProve (fun x w r g => hPI w x (List.ofFn r) g)
    (fun x w r g => hPR w x (List.ofFn r) g)) (xwN A ω l) r g).map (pairO (xN A (pubOf A ω) l))

lemma PN_rdE (hPI : ∀ w x ρ g, RdE (PI w x ρ g) sE) (hPR : ∀ w x ρ g, RdE (PR w x ρ g) sE)
    (ω : SecN U) (l : Log) (r : Coins proveSeedBytes) (g : Tab3) : RdE (PN A PI PR ω l r g) sE :=
  (rdE_proveO (prove := PU PI PR) (rdE_sumProve (fun x w r g => hPI w x (List.ofFn r) g)
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

/-- **The Lean unbound issuance verifier on the shared tables** (`ZK.Sim.verRO`). -/
noncomputable def verILU : IssueInstance → Bytes → ShM R → Bool := fun x pf s =>
  (verRO pI Hashes.shake (Privacy.MoussakaUnbound.stI x) (toBA pf) s).accept

/-- **The Lean unbound redemption verifier on the shared tables.** -/
noncomputable def verRLU : RedeemInstance → Bytes → ShM R → Bool := fun x pf s =>
  (verRO pR Hashes.shake (Privacy.MoussakaUnbound.stR x) (toBA pf) s).accept

lemma verILU_rd5 (x : IssueInstance) (pf : Bytes) : Rd5 (verILU (R := R) x pf) 312 :=
  (verRO_rd5 (p := pI) (Privacy.MoussakaUnbound.stI x) (toBA pf)).map Transcript.accept

lemma verILU_rdE (x : IssueInstance) (pf : Bytes) : RdE (verILU (R := R) x pf) 4607 :=
  (verRO_rdE (p := pI) (Privacy.MoussakaUnbound.stI x) (toBA pf)).map Transcript.accept

lemma verRLU_rd5 (x : RedeemInstance) (pf : Bytes) : Rd5 (verRLU (R := R) x pf) 312 :=
  (verRO_rd5 (p := pR) (Privacy.MoussakaUnbound.stR x) (toBA pf)).map Transcript.accept

lemma verRLU_rdE (x : RedeemInstance) (pf : Bytes) : RdE (verRLU (R := R) x pf) 4607 :=
  (verRO_rdE (p := pR) (Privacy.MoussakaUnbound.stR x) (toBA pf)).map Transcript.accept

lemma leanPI_rd5' (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPI (R := R) w x rho g) 624 :=
  (realROb_rd5 (p := pI) (Hb := Hashes.shake) (st := Privacy.MoussakaUnbound.stI x) (w := toBA w)
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

lemma leanPI_rdE' (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) :
    RdE (leanPI (R := R) w x rho g) 4607 :=
  (realROb_rdE (p := pI) (st := Privacy.MoussakaUnbound.stI x) (w := toBA w) hashesWF_shake
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

lemma leanPR_rd5' (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    Rd5 (leanPR (R := R) w x rho g) 624 :=
  (realROb_rd5 (p := pR) (Hb := Hashes.shake) (st := Privacy.MoussakaUnbound.stR x) (w := toBA w)
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

lemma leanPR_rdE' (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g : Tab3) :
    RdE (leanPR (R := R) w x rho g) 4607 :=
  (realROb_rdE (p := pR) (st := Privacy.MoussakaUnbound.stR x) (w := toBA w) hashesWF_shake
    (toBA rho) g).map fun o => toL (o.toOption.getD .empty)

lemma leanProgI_isProg (x : IssueInstance) (c : SimCoins pI) :
    IsProg (p := Privacy.Moussaka.pI) (leanProgI (R := R) x c) 312 4607 := by
  have h := progRO_isProg (R := R) (p := pI) (Hb := Hashes.shake)
    (st := Privacy.MoussakaUnbound.stI x) c
  exact ⟨h.1, h.2.1, h.2.2⟩

lemma leanProgR_isProg (x : RedeemInstance) (c : SimCoins pR) :
    IsProg (p := Privacy.Moussaka.pI) (leanProgR (R := R) x c) 312 4607 := by
  have h := progRO_isProg (R := R) (p := pR) (Hb := Hashes.shake)
    (st := Privacy.MoussakaUnbound.stR x) c
  exact ⟨h.1, h.2.1, h.2.2⟩

variable (A : ThiefN U M Tab3 (ShM R)) (ext : ExtN U M Tab3 (ShM R)) {a3 a5 aE x3 x5 xE : ℕ}

/-- **The budget of an issuance hop with the Lean prover, verifiers and simulators.** -/
theorem distPN_budgetLI (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (ext l (opN A l)) x3 x5 xE) (i : Fin (U + M)) (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    Budget pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPN A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR verILU verRLU ext
        i ω τ) := by
  have h := (distPN_budget A verILU verRLU ext leanPI leanPR (leanSim pI) leanProgI (leanSim pR)
    leanProgR hA hX verILU_rd5 verRLU_rd5 verILU_rdE verRLU_rdE leanPI_rd5' leanPR_rd5'
    leanPI_rdE' leanPR_rdE' leanProgI_isProg leanProgR_isProg i ω τ).mono le_rfl
    (q5' := a5 + x5 + 312 + (U + M - 1) * 624) (qE' := aE + xE + (U + M) * 4607)
    (by have := i.isLt; omega) (by have := i.isLt; omega)
  -- (the unbound parameters have the `H₂³` table type of the shared tables)
  exact ⟨h.h3, h.h5, h.hE⟩

/-- **The budget of a redemption hop with the Lean prover, verifiers and simulators.** -/
theorem distPN_budgetLR (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (ext l (opN A l)) x3 x5 xE) (i : Fin (U + M)) (ω : SecN U)
    (τ : Fin (U + M) → Slot (Coins proveSeedBytes) (SimCoins pI × SimCoins pR) Tab3) :
    Budget pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPN A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR verILU verRLU ext
        i ω τ) := by
  have h := distPN_budgetLI A ext hA hX i ω τ
  exact ⟨h.h3, h.h5, h.hE⟩

/-! ## Weak simulation-extractability from plain extraction -/

/-- **`k` is the verifier's `H₂³` key of an operation** on the tables `s`. -/
def PtU (op : UOp) (s : ShM R) (k : K2 Privacy.Moussaka.pI) : Prop :=
  match op with
  | .issue req ci => enc2 pI k = vPoint (p := pI) Hashes.shake
      (Privacy.MoussakaUnbound.stI (stOfI req ci)) (toBA (req.drop uovM)) s
  | .redeem S' req ci cr cd => enc2 pR k = vPoint (p := pR) Hashes.shake
      (Privacy.MoussakaUnbound.stR (stOfR S' req ci cr cd)) (toBA (req.drop nfBytes)) s

/-- **`k` is a key the simulation of a statement may program**: its prefix is the grinding prefix
recomputed from the simulated proof (coins `c`) on `H₅` and the cipher. -/
noncomputable def MvU (x : UI) (c : SimCoins pI × SimCoins pR) (b : Tab5F × (Blk → R))
    (k : K2 Privacy.Moussaka.pI) : Prop :=
  match x with
  | .inl x => k.1 = blk (preLen pI) (@outPre (icPrg (rowFn b.2)) Hashes.shake CrtGen.tables
      (Privacy.MoussakaUnbound.stI x) b.1 (simulate pI c.1))
  | .inr x => k.1 = blk (preLen pR) (@outPre (icPrg (rowFn b.2)) Hashes.shake CrtGen.tables
      (Privacy.MoussakaUnbound.stR x) b.1 (simulate pR c.2))

/-- **The operation's verifier reads `H₂³` at a key the simulation of `x` may program.** -/
noncomputable def HitKeyU (x : UI) (c : SimCoins pI × SimCoins pR) (op : UOp) (s : ShM R) :
    Prop :=
  ∃ k, PtU op s k ∧ MvU x c s.2 k

lemma progU_snd (x : UI) (c : SimCoins pI × SimCoins pR) (s : ShM R) :
    (progU leanProgI leanProgR x c s).2 = s.2 := by
  rcases x with x | x <;> rfl

lemma progU_moved (x : UI) (c : SimCoins pI × SimCoins pR) (s : ShM R)
    (k : K2 Privacy.Moussaka.pI) (hk : (progU leanProgI leanProgR x c s).1 k ≠ s.1 k) :
    MvU x c s.2 k := by
  rcases x with x | x
  · exact progRO_moved (p := pI) Hashes.shake (Privacy.MoussakaUnbound.stI x) c.1 s k hk
  · exact progRO_moved (p := pR) Hashes.shake (Privacy.MoussakaUnbound.stR x) c.2 s k hk

lemma accOp_ptU (op : UOp) (s' s : ShM R) (h2 : s'.2 = s.2)
    (h' : AccOp verILU verRLU op s') (h : ¬ AccOp verILU verRLU op s) :
    ∃ k, PtU op s k ∧ s'.1 k ≠ s.1 k := by
  cases op with
  | issue req ci =>
    exact verRO_accept_moved (p := pI) _ _ _ s' s h2 h'.2.2 fun hn => h ⟨h'.1, h'.2.1, hn⟩
  | redeem S' req ci cr cd =>
    exact verRO_accept_moved (p := pR) _ _ _ s' s h2 h'.2.2.2
      fun hn => h ⟨h'.1, h'.2.1, h'.2.2.1, hn⟩

section Fin

variable [Fintype R]

/-- **Weak simulation-extractability of the Lean simulators and verifiers with `U + M` simulated
proofs, from plain extraction** and, for each simulated proof, fresh forgeries whose verifier
reads a key that proof may program. -/
theorem weakSEN_moussakaU
    {e : Log → UOp → (Fin (U + M) → Tab3) → Tab5F × (Blk → R) → Bytes} {ε₀ : ℝ}
    {εh : Fin (U + M) → ℝ}
    (hplain : PlainSEN (U + M) (AccOp verILU verRLU) FreshOpN RelOp e
      (fun F => StageBudgetN F a3 (a5 + (U + M) * 312) (aE + (U + M) * 4607)) ε₀)
    (hhit : ∀ i, SlotEvN (U + M) i (simU (leanSim pI) (leanSim pR)) (progU leanProgI leanProgR)
      FreshOpN (HitKeyU (R := R)) (fun F => StageBudgetN F a3 a5 aE) (εh i)) :
    WeakSEN (U + M) (simU (leanSim pI) (leanSim pR)) (progU leanProgI leanProgR)
      (AccOp verILU verRLU) FreshOpN RelOp (extOfN e) (fun F => StageBudgetN F a3 a5 aE)
      (ε₀ + ∑ i, εh i) :=
  weakSEN_of_plain hplain
    (progMovesN_of_slots progU_snd accOp_ptU progU_moved hhit) progU_snd
    fun _ _ hL hF => hF.comp_prog (hL.isProg (isProg_sumProg leanProgI_isProg leanProgR_isProg))

end Fin

variable [Fintype R] [Nonempty R] [ZKRow R]

/-- **Unbound non-malleability and no squatting** for `U` tokens and `M` redemptions
with the Lean prover and verifiers, the hops' budgets proved: the bound of `nmUN_lean` at
`q = (a₃ + x₃, a₅ + x₅ + 312 + (U + M − 1)·624, a_E + x_E + (U + M)·4607)`. -/
theorem nmUN_lean_reads {AdmE : ((Fin (U + M) → Tab3) → ShM R → UOp) → Prop} {εSE εprf : ℝ}
    (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (ext l (opN A l)) x3 x5 xE)
    (hse : WeakSEN (U + M) (simU (leanSim pI) (leanSim pR)) (progU leanProgI leanProgR)
      (AccOp verILU verRLU) FreshOpN RelOp ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l))
    (pts : Fin (M + 1) → Coins Spec.Moussaka.ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h)
      (owkDN (keyBN A (leanSim pI) leanProgI (leanSim pR) leanProgR ext h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
        (nmRealNE A leanPI leanPR (BadN A verILU verRLU ext)) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
          (deltaNU A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR i) +
        εSE +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) leanProgI (leanSim pR) leanProgR ext h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) leanProgI (leanSim pR) leanProgR ext h)) :=
  nmUN_lean A verILU verRLU ext (fun i _ ω τ => distPN_budgetLI A ext hA hX i ω τ)
    (fun i _ ω τ => distPN_budgetLR A ext hA hX i ω τ) hse hAE pts hpts hprf

/-- **Proposition U3 (no nullifier squatting)** for `U` tokens and `M` redemptions
with the Lean prover and verifiers, the hops' budgets proved: the bound of `noSquatN_lean` at
`q = (a₃ + x₃, a₅ + x₅ + 312 + (U + M − 1)·624, a_E + x_E + (U + M)·4607)`. -/
theorem noSquatN_lean_reads {AdmE : ((Fin (U + M) → Tab3) → ShM R → UOp) → Prop} {εSE εprf : ℝ}
    (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (ext l (opN A l)) x3 x5 xE)
    (hse : WeakSEN (U + M) (simU (leanSim pI) (leanSim pR)) (progU leanProgI leanProgR)
      (AccOp verILU verRLU) FreshOpN RelOp ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l))
    (pts : Fin (M + 1) → Coins Spec.Moussaka.ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h)
      (owkDN (keyBN A (leanSim pI) leanProgI (leanSim pR) leanProgR ext h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
        (nmRealNE A leanPI leanPR (SquatN A verILU verRLU)) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
          (deltaNU A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR i) +
        εSE +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) leanProgI (leanSim pR) leanProgR ext h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) leanProgI (leanSim pR) leanProgR ext h)) :=
  noSquatN_lean A verILU verRLU ext (fun i _ ω τ => distPN_budgetLI A ext hA hX i ω τ)
    (fun i _ ω τ => distPN_budgetLR A ext hA hX i ω τ) hse hAE pts hpts hprf

/-- **Theorem U4 (no redirect)** for `U` tokens and `M` redemptions
with the Lean prover and verifiers, the hops' budgets proved: the bound of `noRedirectUN_lean` at
`q = (a₃ + x₃, a₅ + x₅ + 312 + (U + M − 1)·624, a_E + x_E + (U + M)·4607)`. -/
theorem noRedirectUN_lean_reads {AdmE : ((Fin (U + M) → Tab3) → ShM R → UOp) → Prop} {εSE εprf : ℝ}
    (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (ext l (opN A l)) x3 x5 xE)
    (hse : WeakSEN (U + M) (simU (leanSim pI) (leanSim pR)) (progU leanProgI leanProgR)
      (AccOp verILU verRLU) FreshOpN RelOp ext AdmE εSE)
    (hAE : ∀ l, AdmE (opN A l))
    (pts : Fin (M + 1) → Coins Spec.Moussaka.ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h)
      (owkDN (keyBN A (leanSim pI) leanProgI (leanSim pR) leanProgR ext h) pts b) ≤ εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
        (nmRealNE A leanPI leanPR (RedirectN A verILU verRLU ext)) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
          (deltaNU A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR i) +
        εSE +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) leanProgI (leanSim pR) leanProgR ext h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) leanProgI (leanSim pR) leanProgR ext h)) :=
  noRedirectUN_lean A verILU verRLU ext (fun i _ ω τ => distPN_budgetLI A ext hA hX i ω τ)
    (fun i _ ω τ => distPN_budgetLR A ext hA hX i ω τ) hse hAE pts hpts hprf

/-- **Unbound non-malleability and no squatting** for `U` tokens and `M` redemptions
with the Lean prover, verifiers and simulators, with plain extraction: the bound of
`nmUN_lean_reads` with `ε_SE = ε_plain + Σ_i ε_hit,i`. -/
theorem nmUN_lean_plain
    {e : Log → UOp → (Fin (U + M) → Tab3) → Tab5F × (Blk → R) → Bytes} {ε₀ εprf : ℝ}
    {εh : Fin (U + M) → ℝ}
    (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (extOfN e l (opN A l)) x3 x5 xE)
    (hplain : PlainSEN (U + M) (AccOp verILU verRLU) FreshOpN RelOp e
      (fun F => StageBudgetN F a3 (a5 + (U + M) * 312) (aE + (U + M) * 4607)) ε₀)
    (hhit : ∀ i, SlotEvN (U + M) i (simU (leanSim pI) (leanSim pR)) (progU leanProgI leanProgR)
      FreshOpN (HitKeyU (R := R)) (fun F => StageBudgetN F a3 a5 aE) (εh i))
    (pts : Fin (M + 1) → Coins Spec.Moussaka.ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h)
      (owkDN (keyBN A (leanSim pI) leanProgI (leanSim pR) leanProgR (extOfN e) h) pts b) ≤
        εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
        (nmRealNE A leanPI leanPR (BadN A verILU verRLU (extOfN e))) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
          (deltaNU A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR i) +
        (ε₀ + ∑ i, εh i) +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) leanProgI (leanSim pR) leanProgR (extOfN e) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) leanProgI (leanSim pR) leanProgR (extOfN e) h)) :=
  nmUN_lean_reads A (extOfN e) hA hX (weakSEN_moussakaU hplain hhit)
    (fun _ => hA _ _) pts hpts hprf

/-- **Proposition U3 (no nullifier squatting)** for `U` tokens and `M` redemptions
with the Lean prover, verifiers and simulators, with plain extraction: the bound of
`noSquatN_lean_reads` with `ε_SE = ε_plain + Σ_i ε_hit,i`. -/
theorem noSquatN_lean_plain
    {e : Log → UOp → (Fin (U + M) → Tab3) → Tab5F × (Blk → R) → Bytes} {ε₀ εprf : ℝ}
    {εh : Fin (U + M) → ℝ}
    (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (extOfN e l (opN A l)) x3 x5 xE)
    (hplain : PlainSEN (U + M) (AccOp verILU verRLU) FreshOpN RelOp e
      (fun F => StageBudgetN F a3 (a5 + (U + M) * 312) (aE + (U + M) * 4607)) ε₀)
    (hhit : ∀ i, SlotEvN (U + M) i (simU (leanSim pI) (leanSim pR)) (progU leanProgI leanProgR)
      FreshOpN (HitKeyU (R := R)) (fun F => StageBudgetN F a3 a5 aE) (εh i))
    (pts : Fin (M + 1) → Coins Spec.Moussaka.ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h)
      (owkDN (keyBN A (leanSim pI) leanProgI (leanSim pR) leanProgR (extOfN e) h) pts b) ≤
        εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
        (nmRealNE A leanPI leanPR (SquatN A verILU verRLU)) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
          (deltaNU A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR i) +
        (ε₀ + ∑ i, εh i) +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) leanProgI (leanSim pR) leanProgR (extOfN e) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) leanProgI (leanSim pR) leanProgR (extOfN e) h)) :=
  noSquatN_lean_reads A (extOfN e) hA hX (weakSEN_moussakaU hplain hhit)
    (fun _ => hA _ _) pts hpts hprf

/-- **Theorem U4 (no redirect)** for `U` tokens and `M` redemptions
with the Lean prover, verifiers and simulators, with plain extraction: the bound of
`noRedirectUN_lean_reads` with `ε_SE = ε_plain + Σ_i ε_hit,i`. -/
theorem noRedirectUN_lean_plain
    {e : Log → UOp → (Fin (U + M) → Tab3) → Tab5F × (Blk → R) → Bytes} {ε₀ εprf : ℝ}
    {εh : Fin (U + M) → ℝ}
    (hA : ∀ reqs reds, StageBudgetN (A.out reqs reds) a3 a5 aE)
    (hX : ∀ l, StageBudgetN (extOfN e l (opN A l)) x3 x5 xE)
    (hplain : PlainSEN (U + M) (AccOp verILU verRLU) FreshOpN RelOp e
      (fun F => StageBudgetN F a3 (a5 + (U + M) * 312) (aE + (U + M) * 4607)) ε₀)
    (hhit : ∀ i, SlotEvN (U + M) i (simU (leanSim pI) (leanSim pR)) (progU leanProgI leanProgR)
      FreshOpN (HitKeyU (R := R)) (fun F => StageBudgetN F a3 a5 aE) (εh i))
    (pts : Fin (M + 1) → Coins Spec.Moussaka.ctxBytes) (hpts : Function.Injective pts)
    (hprf : ∀ h b, prf1Adv (A.ci h)
      (owkDN (keyBN A (leanSim pI) leanProgI (leanSim pR) leanProgR (extOfN e) h) pts b) ≤
        εprf) :
    pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
        (nmRealNE A leanPI leanPR (RedirectN A verILU verRLU (extOfN e))) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pR (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pR) Tab3 (ShM R))
          (deltaNU A leanPI leanPR (leanSim pI) leanProgI (leanSim pR) leanProgR i) +
        (ε₀ + ∑ i, εh i) +
        ∑ h : Fin U, (εprf + (M + 1) / 2 ^ 192 +
          bindAdv (bindBN A (leanSim pI) leanProgI (leanSim pR) leanProgR (extOfN e) h) +
          sprAdvN (A.ci h) (sprBN A (leanSim pI) leanProgI (leanSim pR) leanProgR (extOfN e) h)) :=
  noRedirectUN_lean_reads A (extOfN e) hA hX (weakSEN_moussakaU hplain hhit)
    (fun _ => hA _ _) pts hpts hprf

end Lean

end VoleMole.Theft.MoussakaUnbound
