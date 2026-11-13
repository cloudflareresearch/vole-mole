import VoleMole.Theft.SimExtract

/-!
# The theft theorems with weak simulation-extractability reduced to plain extraction

`weakSE2_of_plain` (`Theft/SimExtract.lean`) at the Lean simulators, verifiers and provers of
Ratatouille and Moussaka, in the random-oracle and ideal-cipher table model of
`Privacy/RatatouilleRO.lean`, `Privacy/MoussakaRO.lean`:

* The Lean simulators program only `H₂³` (`progRO`, so `s.2`, the `H₅` and cipher tables, is
  unchanged), and the adversary's last stage after both programmings reads `H₅` at `624` and the
  cipher at `9214` more keys (`progRO_isProg`, `StageBudget.comp_prog`).
* **`accOp_moves`**: an operation accepted on the programmed tables and rejected on the
  unprogrammed ones has its verifier's `H₂³` point at a programmed key (`HitOp`: `HitPt` for the
  operation's statement and proof). With `progRO_moved`, that key's prefix is a simulated proof's
  recomputed grinding prefix: the forgery's `chal2 ‖ qs_check ‖ ã` equals a simulated proof's.
* **`weakSE2_ratatouille`**, **`weakSE2_moussaka`**: `WeakSE2` for the Lean simulators and
  verifiers, extractor `extOf e`, adversaries with a `StageBudget`, with error
  `ε_plain + ε_hit`, from `PlainSE` (plain extraction) and `ProgEv … HitOp` (fresh forgeries
  that query a programmed point).
* **`noTheft_lean_plain`**, **`noRedirect_lean_plain`**: the theft theorems with no `WeakSE2`
  hypothesis and the hops' budgets proved:

      Pr[Bad] ≤ εz(pI; q) + εz(pS; q) + δ + ε_plain + ε_hit + Adv^ow(inverter),
      q = (a₃ + x₃, a₅ + x₅ + 936, a_E + x_E + 9214).

  The hypotheses left are the budgets of the adversary and of the extractor, `PlainSE` and
  `ProgEv … HitOp` (see `Theft/SimExtract.lean` for why they are not provable in this model).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

/-- **A last stage after a programming** reads what it reads and what the programming reads. -/
lemma StageBudget.comp_prog {R : Type} {p : Params} {X : Type*} {F : Tab3 → Tab3 → ShG R p → X}
    {L : ShG R p → ShG R p} {q3 q5 qE m5 mE : ℕ} (h : StageBudget F q3 q5 qE) (hL : IsProg L m5 mE) :
    StageBudget (fun g₁ g₂ s => F g₁ g₂ (L s)) q3 (q5 + m5) (qE + mE) :=
  ⟨fun g₂ s => h.h3₁ g₂ (L s), fun g₁ s => h.h3₂ g₁ (L s), fun g₁ g₂ => (h.h5 g₁ g₂).comp_prog hL,
    fun g₁ g₂ => (h.hE g₁ g₂).comp_prog hL⟩

/-- The two Lean programmings, composed, are a programming. -/
lemma isProg_progT {R : Type} {p : Params} {I₁ I₂ : Type*} {C₁ C₂ : Type}
    {prog₁ : I₁ → C₁ → ShG R p → ShG R p} {prog₂ : I₂ → C₂ → ShG R p → ShG R p} {a b a' b' : ℕ}
    (h₁ : ∀ x c, IsProg (prog₁ x c) a b) (h₂ : ∀ x c, IsProg (prog₂ x c) a' b')
    (x₁ : Option I₁) (c₁ : C₁) (x₂ : Option I₂) (c₂ : C₂) :
    IsProg (progT prog₁ prog₂ x₁ c₁ x₂ c₂) (a + a') (b + b') :=
  (isProg_progO h₁ x₁ c₁).comp (isProg_progO h₂ x₂ c₂)

/-! ## Ratatouille -/

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

variable {R : Type} [CipherRow R] (A : Thief Sizes.labelRows Tab3 (ShR R))

lemma accOp_issue {Z : Sizes} {G S : Type} (A : Thief Z G S)
    (verI : IssueInstance → IssueProof Z → S → Bool) (verS : SpendInstance → SpendProof Z → S → Bool)
    (q : IssueRequest Z) (t : Credits) (c : Context) (s : S) :
    AccOp A verI verS (.issue q t c) s ↔ verI (opXI q t c) (issueReqProof q) s = true := Iff.rfl

lemma accOp_spend {Z : Sizes} {G S : Type} (A : Thief Z G S)
    (verI : IssueInstance → IssueProof Z → S → Bool) (verS : SpendInstance → SpendProof Z → S → Bool)
    (q : SpendRequest Z) (c : Context) (x : Credits) (s : S) :
    AccOp A verI verS (.spend q c x) s ↔ verS (opXS A q c) (SpendReq.parse q).proof s = true := Iff.rfl

lemma leanVIR_eq (x : IssueInstance) (π : IssueProof Sizes.labelRows) (s : ShR R) :
    leanVIR x π s = (verRO pI Hashes.shake (Privacy.Ratatouille.stI x) (bOf π) s).accept := rfl

lemma leanVSR_eq (x : SpendInstance) (π : SpendProof Sizes.labelRows) (s : ShR R) :
    leanVSR x π s = (verRO pS Hashes.shake (Privacy.Ratatouille.stS x) (bOf π) s).accept := rfl

/-- The spend simulator's programming, on the shared tables (`pI` and `pS` have the same `H₂³`
table type). -/
lemma leanProgSR_isProg (x : SpendInstance) (c : SimCoins pS) :
    IsProg (p := pI) (leanProgSR (R := R) x c) 312 4607 := by
  have h := progRO_isProg (R := R) (p := pS) (Hb := Hashes.shake) (st := Privacy.Ratatouille.stS x) c
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- **The verifier's `H₂³` point of an operation is a programmed point** (tables `s'` against
`s`). -/
def HitOp (op : Op Sizes.labelRows) (s' s : ShR R) : Prop :=
  match op with
  | .issue q t c => HitPt (p := pI) Hashes.shake (Privacy.Ratatouille.stI (opXI q t c))
      (bOf (issueReqProof q)) s' s
  | .spend q c _ => HitPt (p := pS) Hashes.shake (Privacy.Ratatouille.stS (opXS A q c))
      (bOf (SpendReq.parse q).proof) s' s

/-- **The programming moves the Lean verifiers only at their `H₂³` point.** -/
theorem accOp_moves (op : Op Sizes.labelRows) (s' s : ShR R) (h2 : s'.2 = s.2)
    (h' : AccOp A leanVIR leanVSR op s') (h : ¬ AccOp A leanVIR leanVSR op s) : HitOp A op s' s := by
  cases op with
  | issue q t c =>
    rw [accOp_issue, leanVIR_eq] at h' h
    exact verRO_accept_moved (p := pI) _ _ _ s' s h2 h' h
  | spend q c x =>
    rw [accOp_spend, leanVSR_eq] at h' h
    exact verRO_accept_moved (p := pS) _ _ _ s' s h2 h' h

variable [Fintype R] {a3 a5 aE : ℕ}

/-- **Weak simulation-extractability of the Lean simulators and verifiers, from plain
extraction** (`PlainSE`, the adversary's budget after both programmings) and fresh forgeries
that query a programmed `H₂³` point (`ProgEv … HitOp`). -/
theorem weakSE2_ratatouille
    {e : Option (IssueInstance × IssueProof Sizes.labelRows) →
      Option (SpendInstance × SpendProof Sizes.labelRows) → Op Sizes.labelRows → Tab3 → Tab3 →
      Tab5F × (Blk → R) → Wit} {ε₀ εh : ℝ}
    (hplain : PlainSE (AccOp A leanVIR leanVSR) (FreshOp A) (RelOp A) e
      (fun F => StageBudget F a3 (a5 + 624) (aE + 9214)) ε₀)
    (hhit : ProgEv leanSimIR leanProgIR leanSimSR leanProgSR (FreshOp A) (HitOp A)
      (fun F => StageBudget F a3 a5 aE) εh) :
    WeakSE2 leanSimIR leanProgIR leanSimSR leanProgSR (AccOp A leanVIR leanVSR) (FreshOp A)
      (RelOp A) (extOf e) (fun F => StageBudget F a3 a5 aE) (ε₀ + εh) :=
  weakSE2_of_plain hplain
    (progMoves_of_ev (fun _ _ _ => rfl) (fun _ _ _ => rfl) (accOp_moves A) hhit)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    fun _ x₁ c₁ x₂ c₂ hF => hF.comp_prog
      (isProg_progT (fun _ c => progRO_isProg c) leanProgSR_isProg x₁ c₁ x₂ c₂)

variable [Nonempty R] [ZKRow R] {x3 x5 xE : ℕ}

/-- **No theft with the Lean prover, verifiers and simulators, with plain extraction.** For an
adversary whose last stage reads `(a₃, a₅, a_E)` and an extractor `extOf e` (which does not read
`H₂³`) that reads `(x₃, x₅, x_E)`:

    Pr[Bad] ≤ εz(pI; q) + εz(pS; q) + δ_S + ε_plain + ε_hit + Adv^ow(inverter),

`q = (a₃ + x₃, a₅ + x₅ + 936, a_E + x_E + 9214)`. -/
theorem noTheft_lean_plain
    {e : Option (IssueInstance × IssueProof Sizes.labelRows) →
      Option (SpendInstance × SpendProof Sizes.labelRows) → Op Sizes.labelRows → Tab3 → Tab3 →
      Tab5F × (Blk → R) → Wit} {ε₀ εh : ℝ}
    (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (extOf e (stI A o₁) (stS A o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hplain : PlainSE (AccOp A leanVIR leanVSR) (FreshOp A) (RelOp A) e
      (fun F => StageBudget F a3 (a5 + 624) (aE + 9214)) ε₀)
    (hhit : ProgEv leanSimIR leanProgIR leanSimSR leanProgSR (FreshOp A) (HitOp A)
      (fun F => StageBudget F a3 a5 aE) εh) :
    pr _ (theftReal A leanPIR leanPSR leanVIR leanVSR (extOf e)) ≤
      ZKRow.εz R pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ZKRow.εz R pS (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        pr _ (deltaS A leanPIR leanPSR leanSimIR leanProgIR) + (ε₀ + εh) +
        owAdv A.ctx (inverter A (extOf e) leanSimIR leanProgIR leanSimSR leanProgSR) :=
  noTheft_lean_reads A (extOf e) hA hX (weakSE2_ratatouille A hplain hhit) hA

end Ratatouille

/-! ## Moussaka -/

namespace Moussaka

open VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka

variable {R : Type} [CipherRow R]

lemma accOp_issue {S : Type} (verI : IssueInstance → Bytes → S → Bool)
    (verR : RedeemInstance → Bytes → S → Bool) (req ci : Bytes) (s : S) :
    AccOp verI verR (.issue req ci) s ↔ (req.length = issueRequestBytes ∧ ci.length = ctxBytes ∧
      verI (stOfI req ci) (req.drop uovM) s = true) := Iff.rfl

lemma accOp_redeem {S : Type} (verI : IssueInstance → Bytes → S → Bool)
    (verR : RedeemInstance → Bytes → S → Bool) (S' : AnchorSet) (req ci cr cd : Bytes) (s : S) :
    AccOp verI verR (.redeem S' req ci cr cd) s ↔ (req.length = redeemRequestBytes ∧
      verR (stOfR S' req ci cr cd) (req.drop nfBytes) s = true) := Iff.rfl

lemma verIL_eq (x : IssueInstance) (pf : Bytes) (s : ShM R) :
    verIL x pf s = (verRO pI Hashes.shake (Privacy.Moussaka.stI x) (toBA pf) s).accept := rfl

lemma verRL_eq (x : RedeemInstance) (pf : Bytes) (s : ShM R) :
    verRL x pf s = (verRO pR Hashes.shake (Privacy.Moussaka.stR x) (toBA pf) s).accept := rfl

/-- The redemption simulator's programming, on the shared tables. -/
lemma leanProgR_isProg (x : RedeemInstance) (c : SimCoins pR) :
    IsProg (p := pI) (leanProgR (R := R) x c) 312 4607 := by
  have h := progRO_isProg (R := R) (p := pR) (Hb := Hashes.shake) (st := Privacy.Moussaka.stR x) c
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- **The verifier's `H₂³` point of an operation is a programmed point.** -/
def HitOp (op : MOp) (s' s : ShM R) : Prop :=
  match op with
  | .issue req ci => HitPt (p := pI) Hashes.shake (Privacy.Moussaka.stI (stOfI req ci))
      (toBA (req.drop uovM)) s' s
  | .redeem S' req ci cr cd => HitPt (p := pR) Hashes.shake
      (Privacy.Moussaka.stR (stOfR S' req ci cr cd)) (toBA (req.drop nfBytes)) s' s

/-- **The programming moves the Lean verifiers only at their `H₂³` point.** -/
theorem accOp_moves (op : MOp) (s' s : ShM R) (h2 : s'.2 = s.2)
    (h' : AccOp verIL verRL op s') (h : ¬ AccOp verIL verRL op s) : HitOp op s' s := by
  cases op with
  | issue req ci =>
    rw [accOp_issue, verIL_eq] at h' h
    exact verRO_accept_moved (p := pI) _ _ _ s' s h2 h'.2.2 fun hn => h ⟨h'.1, h'.2.1, hn⟩
  | redeem S' req ci cr cd =>
    rw [accOp_redeem, verRL_eq] at h' h
    exact verRO_accept_moved (p := pR) _ _ _ s' s h2 h'.2 fun hn => h ⟨h'.1, hn⟩

variable [Fintype R] (A : Thief Tab3 (ShM R)) {a3 a5 aE : ℕ}

/-- **Weak simulation-extractability of the Lean simulators and verifiers, from plain
extraction.** -/
theorem weakSE2_moussaka
    {e : Option (IssueInstance × Bytes) → Option (RedeemInstance × Bytes) → MOp → Tab3 → Tab3 →
      Tab5F × (Blk → R) → Bytes} {ε₀ εh : ℝ}
    (hplain : PlainSE (AccOp verIL verRL) FreshOp RelOp e
      (fun F => StageBudget F a3 (a5 + 624) (aE + 9214)) ε₀)
    (hhit : ProgEv (simI' (leanSim pI)) leanProgI (simR' (leanSim pR)) leanProgR FreshOp (HitOp (R := R))
      (fun F => StageBudget F a3 a5 aE) εh) :
    WeakSE2 (simI' (leanSim pI)) leanProgI (simR' (leanSim pR)) leanProgR (AccOp verIL verRL)
      FreshOp RelOp (extOf e) (fun F => StageBudget F a3 a5 aE) (ε₀ + εh) :=
  weakSE2_of_plain hplain
    (progMoves_of_ev (fun _ _ _ => rfl) (fun _ _ _ => rfl) (accOp_moves (R := R)) hhit)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    fun _ x₁ c₁ x₂ c₂ hF => hF.comp_prog
      (isProg_progT (fun _ c => progRO_isProg c) leanProgR_isProg x₁ c₁ x₂ c₂)

variable [Nonempty R] [ZKRow R] {x3 x5 xE : ℕ}

/-- **Redemption non-malleability with the Lean prover, verifiers and simulators, with plain
extraction**:

    Pr[Bad] ≤ εz(pI; q) + εz(pR; q) + δ_R + ε_plain + ε_hit + Adv^ow(inverter),

`q = (a₃ + x₃, a₅ + x₅ + 936, a_E + x_E + 9214)`. -/
theorem noRedirect_lean_plain
    {e : Option (IssueInstance × Bytes) → Option (RedeemInstance × Bytes) → MOp → Tab3 → Tab3 →
      Tab5F × (Blk → R) → Bytes} {ε₀ εh : ℝ}
    (hA : ∀ o₁ o₂, StageBudget (A.out o₁ o₂) a3 a5 aE)
    (hX : ∀ o₁ o₂, StageBudget (extOf e (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂)) x3 x5 xE)
    (hplain : PlainSE (AccOp verIL verRL) FreshOp RelOp e
      (fun F => StageBudget F a3 (a5 + 624) (aE + 9214)) ε₀)
    (hhit : ProgEv (simI' (leanSim pI)) leanProgI (simR' (leanSim pR)) leanProgR FreshOp (HitOp (R := R))
      (fun F => StageBudget F a3 a5 aE) εh) :
    pr _ (nmReal A leanPI leanPR verIL verRL (extOf e)) ≤
      ZKRow.εz R pI (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        ZKRow.εz R pR (a3 + x3) (a5 + x5 + 936) (aE + xE + 9214) +
        pr _ (deltaR A leanPR (leanSim pI) leanProgI) + (ε₀ + εh) +
        owAdv A.ci A.cr (inverter A (extOf e) (leanSim pI) leanProgI (leanSim pR) leanProgR) :=
  noRedirect_lean_reads A (extOf e) hA hX (weakSE2_moussaka hplain hhit) hA

end Moussaka

end VoleMole.Theft
