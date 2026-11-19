import VoleMole.Theft.RatatouilleManyLean
import VoleMole.Theft.ManyTables
import VoleMole.Theft.HitMany
import VoleMole.Theft.HitTheft

/-!
# Ratatouille no theft for `U` Clients and `M` spends, the other hashes random tables and
`ε_hit` bounded

`noTheftN_lean_plain` (`Theft/RatatouilleManyLean.lean`) has SHAKE for the chain hashes and the
programmed-point terms `SlotEvN i` as hypotheses. Here the game is in the model of
`noTheft_leanX_plain` (`Theft/Tables.lean`: `H₁`, `H₂⁰`, `H₂¹`, `H₂²`, `H₄`, `H_comb` read off one
more uniform shared table `x : X`), and for the tables `XTab L M` the programmed-point terms are
bounded (`Theft/HitMany.lean`).

* `atTN`: the adversary at a value of the extra table. `PN_atX`, `pgP_atX`, `badN_atX`: the real
  slot, the simulated slot's programming and the bad event on the tables `atX s x` are those of
  the game at `x`, with the base record `Hb x`.
* **`distPI_budgetX`**, **`distPS_budgetX`**: the hops' read budgets at every value of the extra
  table (`distN_budgetX`), with the budget of `noTheftN_lean_reads`.
* **`FreshOkN`**: freshness with the adversary's key, as `Hit.Rata.FreshOk` for one Client (the
  Lean spend statement does not hash the key). In the game every logged spend statement has the
  adversary's key (`xN_pk`), so the game's freshness is `FreshOkN` (`freshOkN_of_log`,
  `sim_se_leN_ok`).
* **`noTheftN_leanX_plain`**: the theorem with the extra table, `WeakSEN` replaced by plain
  extraction and the programming term (`ProgMovesN`), both for uniform `X`.
* **`noTheftN_leanX_hit`**: with `XTab L M` (`L ≥ 14357`) and a last stage that reads the chain
  tables with `q_μ`, `q₂₁`, `q₂₂` queries (`AdmHitN`),

      Pr[BadN] ≤ U·εz(pI; q) + M·εz(pS; q) + Σ_i δ_i + ε_plain
        + N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶) + Σ_j Adv^ow(inverter j),

  `N = U + M`, `q = (a₃ + x₃, a₅ + x₅ + 312 + (N − 1)·624, a_E + x_E + N·4607)`. Plain
  extraction (`PlainSEN`) stays a hypothesis.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Theft.Ratatouille

open VoleMole.Privacy VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille VoleMole.ZK.Sim
  VoleMole.Verifier VoleMole.Verifier.Bridge

variable {U M : ℕ}

/-! ## Freshness with the adversary's key -/

section Fresh

variable {Z : Sizes} {G S : Type} (A : ThiefN Z U M G S)

/-- **Freshness with the adversary's key**: a spend is compared with each logged spend statement
with its key replaced by the adversary's (`Hit.Rata.FreshOk` for one Client). -/
def FreshOkN (l : LogR Z) (op : Op Z) : Prop :=
  match op with
  | .issue q t c => ∀ x π, some (Sum.inl x, π) ∈ l → opXI q t c ≠ x
  | .spend q c _ => ∀ x π, some (Sum.inr x, π) ∈ l → opXS A.base q c ≠ { x with pk := A.pk }

lemma FreshOkN.freshOpN {l : LogR Z} {op : Op Z} (h : FreshOkN A l op) : FreshOpN A l op := by
  cases op with
  | issue q t c => exact h
  | spend q c x =>
    intro y π hy he
    refine h y π hy ?_
    rw [← he]
    rfl

/-- **Every spend statement of the game has the adversary's key.** -/
lemma xN_pk {p : Pub} {l : LogR Z} {x : SpendInstance} (h : xN A p l = some (.inr x)) :
    x.pk = A.pk := by
  unfold xN at h
  cases hx : xtE A p (stOf A p l) with
  | error er => rw [hx] at h; cases h
  | ok xt =>
    rw [hx] at h
    simp only [Option.some.injEq] at h
    unfold xtE at hx
    split_ifs at hx with h1 h2
    · cases hx
      cases h
    · cases hc : (stOf A p l).cur (A.who (stOf A p l)) with
      | none => rw [hc] at hx; cases hx
      | some τ =>
        rw [hc] at hx
        simp only at hx
        split_ifs at hx
        cases hk : clientCheck τ.t τ.x (A.amt (stOf A p l)) with
        | none => rw [hk] at hx; cases hx
        | some t' =>
          rw [hk] at hx
          cases hx
          cases h
          rfl

variable {CI CS : Type} (simI : IssueInstance → CI → Option (IssueProof Z))
  (progI : IssueInstance → CI → S → S) (simS : SpendInstance → CS → Option (SpendProof Z))
  (progS : SpendInstance → CS → S → S)

/-- **On the simulated log, the game's freshness is `FreshOkN`.** -/
lemma freshOkN_of_log (ω : SecN U M) (cs : ℕ → CI × CS) (n : ℕ) (op : Op Z)
    (h : FreshOpN A (simPre (fun ω => SmP A simI simS (pubOf ω))
      (fun ω => pgP A progI progS (pubOf ω)) ω cs n).1 op) :
    FreshOkN A (simPre (fun ω => SmP A simI simS (pubOf ω))
      (fun ω => pgP A progI progS (pubOf ω)) ω cs n).1 op := by
  cases op with
  | issue q t c => exact h
  | spend q c x =>
    intro y π hy
    obtain ⟨j, -, he⟩ := simPre_entry _ _ ω cs n _ hy
    have hk : y.pk = A.pk := by
      simp only [SmP] at he
      rcases hx : xN A (pubOf ω) (simPre (fun ω => SmP A simI simS (pubOf ω))
        (fun ω => pgP A progI progS (pubOf ω)) ω cs j).1 with _ | xi
      · rw [hx] at he
        cases he
      · rw [hx] at he
        rcases hs : simO (simM simI simS) (some xi) (cs j) with _ | π'
        · rw [hs] at he
          cases he
        · rw [hs] at he
          simp only [pairO, Option.some.injEq, Prod.mk.injEq] at he
          rw [← he.1] at hx
          exact xN_pk A hx
    have e : ({ y with pk := A.pk } : SpendInstance) = y := by
      cases y
      simp only at hk
      subst hk
      rfl
    rw [e]
    exact h y π hy

variable (verI : IssueInstance → IssueProof Z → S → Bool)
  (verS : SpendInstance → SpendProof Z → S → Bool) (ext : ExtN Z U M G S)
  [Nonempty CI] [Nonempty CS] [Fintype CI] [Fintype CS] [Fintype G] [Fintype S] [Nonempty G]

/-- **`sim_se_leN` for `FreshOkN`.** -/
theorem sim_se_leN_ok {AdmE : ((Fin (U + M) → G) → S → Op Z) → Prop} {εSE : ℝ}
    (hse : WeakSEN (U + M) (simM simI simS) (progM progI progS) (AccOp A.base verI verS)
      (FreshOkN A) (RelOp A.base) ext AdmE εSE)
    (hAE : ∀ iss sp, AdmE (A.out iss sp)) :
    pr (TapeN U M CI CS G S) (theftSimN A simI progI simS progS (seEvN A verI verS ext)) ≤ εSE := by
  have h := simGN_le_of_weakSEN (Ω := SecN U M) (ρ := Coins 16) hse
    (fun ω l => xN A (pubOf ω) l) (fun ω l => opN A (pubOf ω) l) fun _ _ => hAE _ _
  refine (Privacy.pr_mono fun z hz => ?_).trans h
  exact ⟨hz.1, freshOkN_of_log A simI progI simS progS _ _ _ _ hz.2.1, hz.2.2⟩

end Fresh

/-! ## The game at a value of the extra table -/

section X

variable {R : Type} [CipherRow R] {X : Type} (Hb : X → Hashes)
  (A : ThiefN Sizes.labelRows U M Tab3 (ShX R pI X))

/-- **The adversary at a value of the extra table.** -/
def atTN (x : X) : ThiefN Sizes.labelRows U M Tab3 (ShR R) :=
  ⟨A.pk, A.ctx, A.tInit, A.respond, A.choose, A.respondS,
    fun iss sp g s => A.out iss sp g (atX s x)⟩

variable (e : LogR Sizes.labelRows → Op Sizes.labelRows → (Fin (U + M) → Tab3) →
  (Tab5F × (Blk → R)) × X → Wit)

/-- The extractor at a value of the extra table. -/
def eAt (x : X) : LogR Sizes.labelRows → Op Sizes.labelRows → (Fin (U + M) → Tab3) →
    Tab5F × (Blk → R) → Wit :=
  fun l o g b => e l o g (b, x)

omit [CipherRow R] in
lemma stOf_atTN (x : X) (p : Pub) (l : LogR Sizes.labelRows) : stOf (atTN A x) p l = stOf A p l :=
  rfl

omit [CipherRow R] in
lemma xN_atTN (x : X) (p : Pub) (l : LogR Sizes.labelRows) : xN (atTN A x) p l = xN A p l := rfl

lemma PN_atX (x : X) (ω : SecN U M) (l : LogR Sizes.labelRows) (ρ : Coins 16) (g : Tab3)
    (s : ShR R) :
    PN A (leanPIRX Hb) (leanPSRX Hb) ω l ρ g (atX s x) =
      PN (atTN A x) (leanPIRH (Hb x)) (leanPSRH (Hb x)) ω l ρ g s := by
  have hw : xwN (atTN A x) ω l = xwN A ω l := rfl
  unfold PN
  rw [xN_atTN, hw]
  rcases xwN A ω l with _ | ⟨xi, w⟩
  · rfl
  · rcases xi with xi | xi <;> rfl

lemma pgP_atX (x : X) (p : Pub) (l : LogR Sizes.labelRows) (c : SimCoins pI × SimCoins pS)
    (s : ShR R) :
    pgP A (leanProgIRX Hb) (leanProgSRX Hb) p l c (atX s x) =
      atX (pgP (atTN A x) (leanProgIRH (Hb x)) (leanProgSRH (Hb x)) p l c s) x := by
  unfold pgP
  rw [xN_atTN]
  rcases xN A p l with _ | xi
  · rfl
  · rcases xi with xi | xi <;> rfl

lemma accOp_atXN (op : Op Sizes.labelRows) (x : X) (s : ShR R) :
    AccOp A.base (leanVIRX Hb) (leanVSRX Hb) op (atX s x) =
      AccOp (atTN A x).base (leanVIRH (Hb x)) (leanVSRH (Hb x)) op s := by
  cases op <;> rfl

lemma badN_atX (x : X) (ω : SecN U M) (l : LogR Sizes.labelRows) (g : Fin (U + M) → Tab3)
    (s : ShR R) :
    BadN A (leanVIRX Hb) (leanVSRX Hb) (extOfN e) ω l g (atX s x) =
      BadN (atTN A x) (leanVIRH (Hb x)) (leanVSRH (Hb x)) (extOfN (eAt e x)) ω l g s := by
  simp only [BadN, accN, accOp_atXN]
  rfl

lemma leanPIRH_rd5 (H : Hashes) (x : IssueInstance) (w : IssueWitness) (ρ : Rho) (g : Tab3) :
    Rd5 (leanPIRH (R := R) H x w ρ g) 624 :=
  (realROb_rd5 (p := pI) (Hb := H) (st := Privacy.Ratatouille.stI x) (w := encI x w)
    (bOf ρ) g).map (vecOf Sizes.labelRows.issue)

lemma leanPIRH_rdE {H : Hashes} (hH : HashesWF H) (x : IssueInstance) (w : IssueWitness) (ρ : Rho)
    (g : Tab3) : RdE (leanPIRH (R := R) H x w ρ g) 4607 :=
  (realROb_rdE (p := pI) (st := Privacy.Ratatouille.stI x) (w := encI x w) hH
    (bOf ρ) g).map (vecOf Sizes.labelRows.issue)

variable {Hb} {a3 a5 aE x3 x5 xE : ℕ}

/-- **The budget of every hop's distinguisher, at every value of the extra table.** -/
theorem distN_budgetRX (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ iss sp, StageBudgetNX (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetNX (extOfN e l (opN A pb l)) x3 x5 xE) (i : Fin (U + M))
    (ω : SecN U M) (τ : Fin (U + M) → Slot (Coins 16) (SimCoins pI × SimCoins pS) Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distN (PN A (leanPIRX Hb) (leanPSRX Hb)) (fun ω => SmP A leanSimIR leanSimSR (pubOf ω))
        (fun ω => pgP A (leanProgIRX Hb) (leanProgSRX Hb) (pubOf ω))
        (BadN A (leanVIRX Hb) (leanVSRX Hb) (extOfN e)) i ω τ) :=
  (distN_budgetX (fun ω => SmP A leanSimIR leanSimSR (pubOf ω))
    (fun x => PN (atTN A x) (leanPIRH (Hb x)) (leanPSRH (Hb x)))
    (fun x ω => pgP (atTN A x) (leanProgIRH (Hb x)) (leanProgSRH (Hb x)) (pubOf ω))
    (fun x => BadN (atTN A x) (leanVIRH (Hb x)) (leanVSRH (Hb x)) (extOfN (eAt e x)))
    (fun x ω l r g s => PN_atX Hb A x ω l r g s)
    (fun x ω l c s => pgP_atX Hb A x (pubOf ω) l c s)
    (fun x ω l g s => badN_atX Hb A e x ω l g s)
    (fun x => PN_rd5 (atTN A x) _ _ (leanPIRH_rd5 (Hb x)) (leanPSRH_rd5 (Hb x)))
    (fun x => PN_rdE (atTN A x) _ _ (leanPIRH_rdE (hHb x)) (leanPSRH_rdE (hHb x)))
    (fun x _ _ c => isProg_progO (isProg_sumProg (leanProgIRH_isProg (Hb x))
      (leanProgSRH_isProg (Hb x))) _ c)
    (fun x ω l => bad_budgetN (atTN A x) (leanVIRH (Hb x)) (leanVSRH (Hb x)) (extOfN (eAt e x))
      (fun iss sp => hA iss sp x) (fun pb l => hX pb l x) (leanVIRH_rd5 (Hb x))
      (leanVSRH_rd5 (Hb x)) (leanVIRH_rdE (Hb x)) (leanVSRH_rdE (Hb x)) ω l) i ω τ).mono le_rfl
    (by have := i.isLt; omega) (by have := i.isLt; omega)

/-- **The budget of an issuance hop**, at every value of the extra table. -/
theorem distPI_budgetX (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ iss sp, StageBudgetNX (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetNX (extOfN e l (opN A pb l)) x3 x5 xE) (i : Fin (U + M))
    (ω : SecN U M) (τ : Fin (U + M) → Slot (Coins 16) (SimCoins pI × SimCoins pS) Tab3) :
    BudgetX pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPI A (leanPIRX Hb) (leanPSRX Hb) leanSimIR (leanProgIRX Hb) leanSimSR (leanProgSRX Hb)
        (leanVIRX Hb) (leanVSRX Hb) (extOfN e) i ω τ) :=
  (distN_budgetRX A e hHb hA hX i ω τ).comp
    (fun o : Option (IssueProof Sizes.labelRows) => pairO (xN A (pubOf ω)
      (simPre (fun ω => SmP A leanSimIR leanSimSR (pubOf ω))
        (fun ω => pgP A (leanProgIRX Hb) (leanProgSRX Hb) (pubOf ω)) ω (tapeC τ) i).1)
      (o.map Sum.inl))

/-- **The budget of a spend hop**, at every value of the extra table. -/
theorem distPS_budgetX (hHb : ∀ x, HashesWF (Hb x))
    (hA : ∀ iss sp, StageBudgetNX (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetNX (extOfN e l (opN A pb l)) x3 x5 xE) (i : Fin (U + M))
    (ω : SecN U M) (τ : Fin (U + M) → Slot (Coins 16) (SimCoins pI × SimCoins pS) Tab3) :
    BudgetX pS (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624) (aE + xE + (U + M) * 4607)
      (distPS A (leanPIRX Hb) (leanPSRX Hb) leanSimIR (leanProgIRX Hb) leanSimSR (leanProgSRX Hb)
        (leanVIRX Hb) (leanVSRX Hb) (extOfN e) i ω τ) := by
  have h := (distN_budgetRX A e hHb hA hX i ω τ).comp
    (fun o : Option (SpendProof Sizes.labelRows) => pairO (xN A (pubOf ω)
      (simPre (fun ω => SmP A leanSimIR leanSimSR (pubOf ω))
        (fun ω => pgP A (leanProgIRX Hb) (leanProgSRX Hb) (pubOf ω)) ω (tapeC τ) i).1)
      (o.map Sum.inr))
  -- (`pI` and `pS` have the same `H₂³` table type)
  exact fun x => ⟨(h x).h3, (h x).h5, (h x).hE⟩

lemma progM_sndX (x : RI) (c : SimCoins pI × SimCoins pS) (t : ShX R pI X) :
    (progM (leanProgIRX Hb) (leanProgSRX Hb) x c t).2 = t.2 := by
  rcases x with x | x <;> rfl

variable [Fintype R] [Nonempty R] [ZKRow R] [Fintype X] [Nonempty X]

/-- **No theft for `U` Clients and `M` spends with the other hashes read off a uniform table,
with plain extraction**: as `noTheftN_lean_plain`, in the model of `noTheft_leanX_plain`. The
programming term `ε_moves` (`ProgMovesN`: the fresh output is accepted on the programmed tables
and rejected on the unprogrammed ones) and plain extraction are for the freshness `FreshOkN`
(the adversary's key), against classes `Adm`, `Adm₀` of the caller's choice (`hadm`: the last
stage composed with `U + M` programmings is in `Adm₀`). -/
theorem noTheftN_leanX_plain (hHb : ∀ x, HashesWF (Hb x))
    {Adm Adm₀ : ((Fin (U + M) → Tab3) → ShX R pI X → Op Sizes.labelRows) → Prop} {ε₀ εm : ℝ}
    (hA : ∀ iss sp, StageBudgetNX (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetNX (extOfN e l (opN A pb l)) x3 x5 xE)
    (hplain : PlainSEN (U + M) (AccOp A.base (leanVIRX Hb) (leanVSRX Hb)) (FreshOpN A)
      (RelOp A.base) e Adm₀ ε₀)
    (hmoves : ProgMovesN (U + M) (simM leanSimIR leanSimSR)
      (progM (leanProgIRX Hb) (leanProgSRX Hb)) (AccOp A.base (leanVIRX Hb) (leanVSRX Hb))
      (FreshOkN A) Adm εm)
    (hAdm : ∀ iss sp, Adm (A.out iss sp))
    (hadm : ∀ F L, IsProgs (progM (leanProgIRX Hb) (leanProgSRX Hb)) (U + M) L → Adm F →
      Adm₀ (fun g s => F g (L s))) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (ShX R pI X))
        (theftRealN A (leanPIRX Hb) (leanPSRX Hb) (leanVIRX Hb) (leanVSRX Hb) (extOfN e)) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pS (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (ShX R pI X))
          (deltaNR A (leanPIRX Hb) (leanPSRX Hb) leanSimIR (leanProgIRX Hb) leanSimSR
            (leanProgSRX Hb) i) +
        (ε₀ + εm) +
        ∑ j : Fin (U + M), owAdvK (inverterN A leanSimIR (leanProgIRX Hb) leanSimSR
          (leanProgSRX Hb) (extOfN e) j) :=
  noTheftN_of_se (CI := SimCoins pI) (CS := SimCoins pS) A (leanPIRX Hb) (leanPSRX Hb) leanSimIR
    (leanProgIRX Hb) leanSimSR (leanProgSRX Hb) (leanVIRX Hb) (leanVSRX Hb) (extOfN e)
    (leanPIRX_zkRO hHb _ _ _) (ZKRow.εz_nonneg _ _ _ _) (leanPSRX_zkRO hHb _ _ _)
    (ZKRow.εz_nonneg _ _ _ _) (fun i _ ω τ => distPI_budgetX A e hHb hA hX i ω τ)
    (fun i _ ω τ => distPS_budgetX A e hHb hA hX i ω τ)
    (sim_se_leN_ok A leanSimIR (leanProgIRX Hb) leanSimSR (leanProgSRX Hb) (leanVIRX Hb)
      (leanVSRX Hb) (extOfN e)
      (weakSEN_of_plain (hplain.fresh_mono fun _ _ h => h.freshOpN) hmoves progM_sndX hadm) hAdm)

end X

/-! ## `ε_hit` bounded -/

section Hit

open VoleMole.Theft.Hit

variable {R : Type} [CipherRow R] {L M' : ℕ}
  (A : ThiefN Sizes.labelRows U M Tab3 (ShX R pI (XTab L M')))

/-- The two simulations as one, on the sum of the instance types. -/
noncomputable abbrev DM : RI → SimCoins pI × SimCoins pS → SD :=
  sumD (fun i c => (Privacy.Ratatouille.stI i, simulate pI c))
    (fun i c => (Privacy.Ratatouille.stS i, simulate pS c))

lemma simProgM : SimProg (R := R) (L := L) (M := M') (progM (leanProgIRX hbX) (leanProgSRX hbX))
    DM :=
  Hit.Rata.simProgI.sum Hit.Rata.simProgS

omit [CipherRow R] in
/-- **A fresh forgery's `H₂⁰` input is not a logged simulated statement's.** -/
lemma freshN_ne (l : LogR Sizes.labelRows) (op : Op Sizes.labelRows) (xi : RI)
    (c : SimCoins pI × SimCoins pS) (hfr : FreshOkN A l op)
    (hm : pairO (some xi) (simM leanSimIR leanSimSR xi c) ∈ l)
    (hok : ∃ b, (DM xi c).2 = .ok b) :
    VoleMole.ROM.IC.muIn (Hit.Rata.fd A.base op).1 ≠ VoleMole.ROM.IC.muIn (DM xi c).1 := by
  rcases xi with i | i
  · obtain ⟨b, hb⟩ := hok
    simp only [sumD_inl] at hb ⊢
    refine Hit.Rata.fresh_ne₁ A.base (some i) c.1 none op i ?_ rfl ⟨b, hb⟩
    obtain ⟨π, hπ⟩ := Hit.Rata.simO_some_I (i := i) hb
    have hπ' : leanSimIR i c.1 = some π := by simpa only [simO] using hπ
    have hm' : some (Sum.inl i, Sum.inl π) ∈ l := by
      simpa [simM, sumSimO, hπ', pairO] using hm
    cases op with
    | issue q t cc =>
      intro y hy
      simp only [simO, hπ', pairO, Option.some.injEq] at hy
      subst hy
      exact hfr i _ hm'
    | spend q cc x => exact fun y hy => by cases hy
  · obtain ⟨b, hb⟩ := hok
    simp only [sumD_inr] at hb ⊢
    refine Hit.Rata.fresh_ne₂ A.base none (some i) c.2 op i ?_ rfl ⟨b, hb⟩
    obtain ⟨π, hπ⟩ := Hit.Rata.simO_some_S (i := i) hb
    have hπ' : leanSimSR i c.2 = some π := by simpa only [simO] using hπ
    have hm' : some (Sum.inr i, Sum.inr π) ∈ l := by
      simpa [simM, sumSimO, hπ', pairO] using hm
    cases op with
    | issue q t cc => exact fun y hy => by cases hy
    | spend q cc x =>
      intro y hy
      simp only [simO, hπ', pairO, Option.map_some, Option.some.injEq] at hy
      subst hy
      exact hfr i _ hm'

variable [Fintype R] [Nonempty R]

/-- **The programming term for `U + M` simulated proofs** (`progMovesN_chain`):

    ε_moves ≤ N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶),   N = U + M. -/
theorem progMovesN_hit (hL : Hit.Rata.Lmin ≤ L) (qMu q21 q22 : ℕ) :
    ProgMovesN (U + M) (simM leanSimIR leanSimSR) (progM (leanProgIRX hbX) (leanProgSRX hbX))
      (AccOp A.base (leanVIRX hbX) (leanVSRX hbX)) (FreshOkN A)
      (AdmHitN (R := R) (p := pI) (L := L) (M := M') (N := U + M) (G := Tab3) qMu q21 q22)
      ((U + M : ℕ) * epsHitN (U + M) qMu q21 q22) :=
  progMovesN_chain simProgM (Hit.Rata.fd A.base) (fun _ op _ => Hit.Rata.fd_fOk A.base hL op)
    (fun o t' t h2 ha hn => Hit.Rata.hitG_of_hitOpX A.base o t' t
      (accOp_movesX hbX A.base o t' t h2 ha hn))
    (fun l op xi c hfr hm hok => freshN_ne A l op xi c hfr hm hok) qMu q21 q22

variable [ZKRow R] {a3 a5 aE x3 x5 xE : ℕ}

/-- **No theft for `U` Clients and `M` spends with the other hashes random tables and `ε_hit`
bounded.** As `noTheftN_leanX_plain` with the concrete extra table `XTab L M'` (`hbX`,
`L ≥ 14357`) and the programming term bounded by `progMovesN_hit`: for an adversary whose last
stage reads `(a₃, a₅, a_E)` and the chain tables with `(q_μ, q₂₁, q₂₂)` queries (`AdmHitN`, implied
by its class `Adm`), and an extractor `extOfN e` that reads `(x₃, x₅, x_E)`, with `N = U + M`,

    Pr[BadN] ≤ U·εz(pI; q) + M·εz(pS; q) + Σ_i δ_i + ε_plain
      + N·((q₂₂+N+1)·2⁻⁴⁴⁸ + (q₂₁+N+1)·2⁻¹⁰⁸⁸ + (q_μ+N+1)·2⁻²⁵⁶) + Σ_j Adv^ow(inverter j),

`q = (a₃ + x₃, a₅ + x₅ + 312 + (N − 1)·624, a_E + x_E + N·4607)`. Plain extraction (`hplain`)
stays a hypothesis, against a class `Adm₀` that contains the last stage composed with `N`
programmings (`hadm`). -/
theorem noTheftN_leanX_hit (hL : Hit.Rata.Lmin ≤ L)
    {e : LogR Sizes.labelRows → Op Sizes.labelRows → (Fin (U + M) → Tab3) →
      (Tab5F × (Blk → R)) × XTab L M' → Wit}
    {Adm Adm₀ : ((Fin (U + M) → Tab3) → ShX R pI (XTab L M') → Op Sizes.labelRows) → Prop}
    {ε₀ : ℝ} {qMu q21 q22 : ℕ}
    (hA : ∀ iss sp, StageBudgetNX (A.out iss sp) a3 a5 aE)
    (hX : ∀ pb l, StageBudgetNX (extOfN e l (opN A pb l)) x3 x5 xE)
    (hplain : PlainSEN (U + M) (AccOp A.base (leanVIRX hbX) (leanVSRX hbX)) (FreshOpN A)
      (RelOp A.base) e Adm₀ ε₀)
    (hAdm : ∀ iss sp, Adm (A.out iss sp)) (hAH : ∀ F, Adm F → AdmHitN qMu q21 q22 F)
    (hadm : ∀ F L, IsProgs (progM (leanProgIRX hbX) (leanProgSRX hbX)) (U + M) L → Adm F →
      Adm₀ (fun g s => F g (L s))) :
    pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (ShX R pI (XTab L M')))
        (theftRealN A (leanPIRX hbX) (leanPSRX hbX) (leanVIRX hbX) (leanVSRX hbX) (extOfN e)) ≤
      U * ZKRow.εz R pI (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        M * ZKRow.εz R pS (a3 + x3) (a5 + x5 + 312 + (U + M - 1) * 624)
          (aE + xE + (U + M) * 4607) +
        ∑ i, pr (TapeN U M (SimCoins pI) (SimCoins pS) Tab3 (ShX R pI (XTab L M')))
          (deltaNR A (leanPIRX hbX) (leanPSRX hbX) leanSimIR (leanProgIRX hbX) leanSimSR
            (leanProgSRX hbX) i) +
        (ε₀ + (U + M : ℕ) * epsHitN (U + M) qMu q21 q22) +
        ∑ j : Fin (U + M), owAdvK (inverterN A leanSimIR (leanProgIRX hbX) leanSimSR
          (leanProgSRX hbX) (extOfN e) j) :=
  noTheftN_leanX_plain A e hbX_wf hA hX hplain ((progMovesN_hit A hL qMu q21 q22).mono hAH) hAdm
    hadm

end Hit

end VoleMole.Theft.Ratatouille
