import VoleMole.Privacy.MoussakaNCRO
import VoleMole.Privacy.MoussakaRAK

/-!
# Moussaka against a non-colluding Moderator whose choices read the tables

`Privacy/MoussakaNCRO.lean` proves Theorem 4(b′) in the random-oracle and ideal-cipher model for a
Moderator whose choices (contexts, issuing keys, Anchor Sets, digests) are constants: only its guess
reads the tables. Here the Moderator **chooses after reading the tables**: a setup stage
(`AdversaryNCRA.setup`) reads the four `H₃` slices and the shared tables (`H₂³`, `H₅`, the cipher)
within a budget, consistently (`KBudget`, as `AdversaryRAK.KBudget`), and outputs a state `σ`; the
contexts, keys, Anchor Sets, digests and the guess are those of the adversary `adv σ` of
`MoussakaNCRO`, and the Anchors' signers `sk σ` may depend on `σ` too. A non-colluding Moderator
sees no issuance, so before the redemptions there is nothing else for it to read: the setup is the
most general table-reading choice.

## The game (`realGameNCRA`)

The setup on the slices and the original tables, then `realGameNCRO` of `adv σ` with the signers
`sk σ` (`realGameNCRA`, by definition). Every hybrid is `gameNCROT` of `adv σ`, `σ` read off the
slices and the original tables (`gameNCRA`).

## The hops

1. **The redemption proofs simulated** (`hopL_NCRA`, `hopR_NCRA`): the redemption statements are
   now read off the tables (through the setup), so the hops are `hop_roA` with `ZeroKnowledgeROA`
   for the setup reader (`εAd` at the setup's budget `(k₃, k₂, k₅, k_E)`). The reductions still run
   both issuance proofs and both verifications themselves (reads, no collision term). The right
   hop's collision term `deltaNCA` is still `≤ noHitProb + 2⁻¹⁰²⁴` (`deltaNCA_le`): the right
   real proof's grinding prefix is a function of the tables, the slices and its own randomness,
   none of which the left simulation's coins enter, so its `ã` is the simulation's uniform `ã` with
   that probability (`pr_simTail_eq_le`); no second zero-knowledge application is needed (unlike in
   `MoussakaRA`, where the redemption statements depend on the simulated issuance requests).
2. **The issuance slices the guess sees made independent** (`sim_fresh_NCA`): the setup and the
   guess both read the slice the Moderator sees, so the cost is `2·(k₃ + q₃)·2⁻¹²⁸` per world
   (`Rd3.bind` of the setup and the guess).
3. **The abort hop** (`fresh_hyb_NCA`): the abort event depends on the Clients' coins and on `σ`,
   which is independent of them (a function of the slices the Moderator sees and the tables); it is
   bounded by `φ₀ + φ₁` for any `φ` with `phi (adv σ) (sk σ) c ≤ φ c` at every `σ`.
4. **The swap** (`hybFresh_eqA`): it exchanges the Clients' tapes and keeps the slices the
   Moderator sees and the tables, hence `σ`.

## Results

* **`anonymityNCRA`** (any proof systems; `ZeroKnowledgeROA` of the redemption proofs) and, with
  the Lean prover and verifier, **`anonymityNCRA_leanG`** (every row type),
  **`anonymityNCRA_lean_num`** (function rows), `anonymityNCRA_lean_num_perm`:

      |Pr[W₀] − Pr[W₁]| ≤ 4·εAd(9; q₃, q₅ + 2496, q_E + 23035; k₃, k₂, k₅, k_E)
                          + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁) + 4·(k₃ + q₃)·2⁻¹²⁸.

  With `k = 0` this is `anonymityNCRO_lean_num` up to `4·2⁻¹²⁸` (`εAd` at a zero reader budget is
  `εRO + 2⁻¹²⁸`).
* **`unlinkabilityNCRA`**, `unlinkabilityNCRA_lean_num`, `_perm`: one Anchor at every state, any
  index rule, no abort term.

`ROM/PrivacyReadsNC.lean` gives the setup as a VCVio oracle computation over the tables, with the
syntactic query bound in place of `KBudget`.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim

attribute [local irreducible] com UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R]

/-! ## The model -/

/-- **The non-colluding Moderator whose choices read the tables**: `setup` reads the four `H₃`
slices and the shared tables and outputs a state `σ`; the contexts, the issuing keys, the Anchor
Sets, the digests and the guess are those of `adv σ`. -/
structure AdversaryNCRA (R : Type) (Sg : Type) where
  setup : Slices → ShM R → Sg
  adv : Sg → AdversaryNCRO R

namespace AdversaryNCRA

variable {Sg : Type} (A : AdversaryNCRA R Sg)

/-- **The setup's budget**: as a function of each proof's slice and the shared tables (the other
slices fixed), the setup reads at most `k₃` slice keys, `k₂` `H₂³` keys, `k₅` `H₅` keys and `k_E`
cipher keys, consistently (`SReads`). -/
structure KBudget (k3 k2 k5 kE : ℕ) : Prop where
  s0 : ∀ (g₁ gL gR : Tab3), SReads pI (fun t : Tb R pI => A.setup ((t.1, g₁), (gL, gR)) t.2) k3 k2 k5 kE
  s1 : ∀ (g₀ gL gR : Tab3), SReads pI (fun t : Tb R pI => A.setup ((g₀, t.1), (gL, gR)) t.2) k3 k2 k5 kE
  sL : ∀ (g₀ g₁ gR : Tab3), SReads pR (fun t : Tb R pR => A.setup ((g₀, g₁), (t.1, gR)) t.2) k3 k2 k5 kE
  sR : ∀ (g₀ g₁ gL : Tab3), SReads pR (fun t : Tb R pR => A.setup ((g₀, g₁), (gL, t.1)) t.2) k3 k2 k5 kE

/-- **The guess's budget**, at every state. -/
def Budget (q3 q5 qE : ℕ) : Prop := ∀ σ, (A.adv σ).Budget q3 q5 qE

end AdversaryNCRA

/-! ## The game -/

section Game

variable {Sg : Type} (A : AdversaryNCRA R Sg) (idx : AnchorSet → UOVKey → ℕ)
  (PI : ProverRO R IssueInstance) (V : VerifierRO R) (sk : Sg → Bool → Signer)

/-- The state read off a game tape: the setup on the four slices and the original tables. -/
def σNC {TL TR : Type} (x : ((TIr × TIr) × ((TL × Tab3) × (TR × Tab3))) × ShM R) : Sg :=
  A.setup ((x.1.1.1.2.2, x.1.1.2.2.2), (x.1.2.1.2, x.1.2.2.2)) x.2

/-- **The real game in world `b`**: the setup reads the slices and the tables, then the real game
of `MoussakaNCRO` for `adv σ` with the signers `sk σ`. -/
def realGameNCRA (PR : ProverRO R RedeemInstance) (b : Bool)
    (x : ((TIr × TIr) × (TRr × TRr)) × ShM R) : Prop :=
  realGameNCRO (A.adv (σNC A x)) idx PI V (sk (σNC A x)) PR b x

/-- **The hybrids**: `gameNCROT` of `adv σ` with the redemption slots drawn at `σ`. -/
def gameNCRA {TL TR : Type} (b : Bool) (gL : Sg → TL × Tab3 → RedSlot R)
    (gR : Sg → TR × Tab3 → RedSlot R) (x : ((TIr × TIr) × ((TL × Tab3) × (TR × Tab3))) × ShM R) :
    Prop :=
  gameNCROT (A.adv (σNC A x)) idx PI V (sk (σNC A x)) b (gL (σNC A x)) (gR (σNC A x)) x

theorem realGameNCRA_iff (hsk : ∀ σ c, (sk σ c).Correct ((A.adv σ).pk c))
    (PR : ProverRO R RedeemInstance) (b : Bool) (x : ((TIr × TIr) × (TRr × TRr)) × ShM R) :
    realGameNCRA A idx PI V sk PR b x ↔
      gameNCRA A idx PI V sk b (fun σ => redRealRO (A.adv σ).ro PR)
        (fun σ => redRealRO (A.adv σ).ro PR) x :=
  realGameNCRO_iff _ idx PI V _ (hsk _) PR b x

end Game

/-! ## The statement of a redemption at a fixed state -/

section Stw

variable (B : AdversaryNCRO R) (idx : AnchorSet → UOVKey → ℕ) (sk : Bool → Signer)

/-- The redemption statement and witness of side `side` (none if the redemptions do not happen). -/
def stwNC (b : Bool) (x₀ x₁ : TIr) (side : Bool) : Option (RedeemInstance × Bytes) :=
  if okW B idx sk x₀ x₁ = true then
    some (xROf B.ro (ptW B idx sk b x₀ x₁ side), wROf B.ro (ptW B idx sk b x₀ x₁ side))
  else none

lemma stwNC_rel (hsk : ∀ c, (sk c).Correct (B.pk c)) (b : Bool) (x₀ x₁ : TIr) (side : Bool) :
    ∀ i w, stwNC B idx sk b x₀ x₁ side = some (i, w) → RedeemRelW i w := by
  intro i w h
  unfold stwNC at h
  split_ifs at h with hok
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hwf := tokW_wf B sk hsk (b ^^ side) (bif b ^^ side then x₁ else x₀)
  exact (redeem_facts B.ro (fun _ (_ : Unit) => []) (fun _ _ _ _ _ => []) _ hwf.1 hwf.2.1 hwf.2.2
    (redeemOk_ptW B idx sk x₀ x₁ hok b side)).1

end Stw

/-! ## The two redemption hops -/

section Hops

variable {Sg : Type} (A : AdversaryNCRA R Sg) (idx : AnchorSet → UOVKey → ℕ)
  (PI : ProverRO R IssueInstance) (V : VerifierRO R) (sk : Sg → Bool → Signer)
  (PR : ProverRO R RedeemInstance) {CR : Type} (simR : RedeemInstance → CR → Bytes)
  (progR : RedeemInstance → CR → ShM R → ShM R)

/-- The state in hop L, read off the left redemption's slice and the shared tables. -/
def SxLN (γ : (TIr × TIr) × TRr) (t : Tab3 × ShM R) : Sg :=
  A.setup ((γ.1.1.2.2, γ.1.2.2.2), (t.1, γ.2.2)) t.2

/-- The state in hop R, read off the right redemption's slice and the shared tables. -/
def SxRN (γ : (TIr × TIr) × TRs CR) (t : Tab3 × ShM R) : Sg :=
  A.setup ((γ.1.1.2.2, γ.1.2.2.2), (γ.2.2, t.1)) t.2

/-- **The collision term of the right hop**: the right redemption's real proof (of the statement at
the state read off the tables) on the tables the left simulation programmed differs from the one on
the original tables. -/
noncomputable def deltaNCA [Fintype CR] (b : Bool) : ℝ :=
  pr (((TIr × TIr) × TRs CR) × (Coins proveSeedBytes × (Tab3 × ShM R))) fun z =>
    (redRealRO (A.adv (SxRN A z.1 z.2.2)).ro PR (z.2.1, z.2.2.1)).out
        (ptW (A.adv (SxRN A z.1 z.2.2)) idx (sk (SxRN A z.1 z.2.2)) b z.1.1.1 z.1.1.2 true)
        (LNC (A.adv (SxRN A z.1 z.2.2)) idx (sk (SxRN A z.1 z.2.2)) progR b z.1 z.2.2.2) ≠
      (redRealRO (A.adv (SxRN A z.1 z.2.2)).ro PR (z.2.1, z.2.2.1)).out
        (ptW (A.adv (SxRN A z.1 z.2.2)) idx (sk (SxRN A z.1 z.2.2)) b z.1.1.1 z.1.1.2 true) z.2.2.2

variable {A idx PI V sk PR simR progR} {q3 q5 qE r5 rE v5 vE m5 mE : ℕ}

/-- **The left hop**: the left redemption simulated, its statement read off the tables through the
setup. The reduction runs both issuances, both verifications and the right redemption. -/
theorem hopL_NCRA [Fintype CR] [Nonempty CR] (hsk : ∀ σ c, (sk σ c).Correct ((A.adv σ).pk c))
    (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hV5 : ∀ pf x, Rd5 (V pf x) v5) (hVE : ∀ pf x, RdE (V pf x) vE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    {AdmS : (X : Type) → (Tab3 × ShM R → X) → Prop}
    (hS : ∀ γ : (TIr × TIr) × TRr, AdmS Sg (SxLN A γ))
    {ε : ℝ} (hR : ZeroKnowledgeROA RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmS
      (Budget pR q3 (r5 + v5 + (r5 + v5) + (0 + r5) + q5) (rE + vE + (rE + vE) + (0 + rE) + qE)) ε)
    (b : Bool) :
    |pr _ (gameNCRA A idx PI V sk b (fun σ => redRealRO (A.adv σ).ro PR)
        (fun σ => redRealRO (A.adv σ).ro PR)) -
      pr _ (gameNCRA A idx PI V sk b (fun σ => redSimRO (A.adv σ).ro simR progR)
        (fun σ => redRealRO (A.adv σ).ro PR))| ≤ ε := by
  have h := hop_roA (Γ := (TIr × TIr) × TRr) (ρ := Coins proveSeedBytes) (G := Tab3) (C := CR)
    (S := ShM R) (SxLN A)
    (fun γ σ ρ g s => (redRealRO (A.adv σ).ro PR (ρ, g)).out
      (ptW (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 false) s)
    (fun γ σ c => redSim (A.adv σ).ro.base simR c (ptW (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 false))
    (fun γ σ c s => if okW (A.adv σ) idx (sk σ) γ.1.1 γ.1.2 = true then
      progR (xROf (A.adv σ).ro (ptW (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 false)) c s else s)
    (fun _ _ s => s) (fun γ σ => FLNC (A.adv σ) idx PI V (sk σ) PR b γ) (ε := ε) fun γ => ?_
  · have hδ : pr (((TIr × TIr) × TRr) × (Coins proveSeedBytes × (Tab3 × ShM R))) (fun z =>
        (redRealRO (A.adv (SxLN A z.1 z.2.2)).ro PR (z.2.1, z.2.2.1)).out
            (ptW (A.adv (SxLN A z.1 z.2.2)) idx (sk (SxLN A z.1 z.2.2)) b z.1.1.1 z.1.1.2 false)
            z.2.2.2 ≠
          (redRealRO (A.adv (SxLN A z.1 z.2.2)).ro PR (z.2.1, z.2.2.1)).out
            (ptW (A.adv (SxLN A z.1 z.2.2)) idx (sk (SxLN A z.1 z.2.2)) b z.1.1.1 z.1.1.2 false)
            z.2.2.2) = 0 := by
      rw [pr_congr (Q := fun _ => False) fun z => by simp, pr_const]
      simp
    rw [hδ, add_zero] at h
    let e : ((TIr × TIr) × TRr) × (Coins proveSeedBytes × (Tab3 × ShM R)) ≃
        ((TIr × TIr) × (TRr × TRr)) × ShM R :=
      { toFun := fun z => ((z.1.1, ((z.2.1, z.2.2.1), z.1.2)), z.2.2.2)
        invFun := fun x => ((x.1.1, x.1.2.2), (x.1.2.1.1, (x.1.2.1.2, x.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let e' : ((TIr × TIr) × TRr) × (CR × (Tab3 × ShM R)) ≃
        ((TIr × TIr) × (TRs CR × TRr)) × ShM R :=
      { toFun := fun z => ((z.1.1, ((z.2.1, z.2.2.1), z.1.2)), z.2.2.2)
        invFun := fun x => ((x.1.1, x.1.2.2), (x.1.2.1.1, (x.1.2.1.2, x.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e, ← pr_equiv e']
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · have hz := hR Sg (SxLN A γ) (fun σ => stwNC (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 false) (hS γ)
      (fun σ => stwNC_rel (A.adv σ) idx (sk σ) (hsk σ) b γ.1.1 γ.1.2 false) []
      (fun σ o g s => FLNC (A.adv σ) idx PI V (sk σ) PR b γ
        (.ok ((ptW (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 false).tok.nf ++ o)) g s)
      fun σ => ⟨fun o s => (hA σ).h3L _ _ _ _ _,
        fun o g => rd5_viewNC (hA σ) (rd5_GV hPI5 hV5 _ _) (Rd5.const _) (rd5_redReal hPR5 _ _) _,
        fun o g => rdE_viewNC (hA σ) (rdE_GV hPIE hVE _ _) (RdE.const _) (rdE_redReal hPRE _ _) _⟩
    refine le_of_eq_of_le (congrArg₂ (fun x y => |x - y|) (pr_congr fun a => ?_)
      (pr_congr fun a => ?_)) hz
    · set σ := SxLN A γ a.2 with hσ
      simp only [outReal, stwNC]
      cases hok : okW (A.adv σ) idx (sk σ) γ.1.1 γ.1.2
      · simp only [FLNC, GV_false_of_okW _ idx PI V _ (hsk σ) _ _ _ hok, Bool.cond_false]
      · have hwf := tokW_wf (A.adv σ) (sk σ) (hsk σ) (b ^^ false)
          (bif b ^^ false then γ.1.2 else γ.1.1)
        obtain ⟨-, hreal, -⟩ := redeem_facts (A.adv σ).ro simR PR
          (ptW (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 false) hwf.1 hwf.2.1 hwf.2.2
          (redeemOk_ptW (A.adv σ) idx (sk σ) γ.1.1 γ.1.2 hok b false)
        simp only [↓reduceIte, Option.elim]
        rw [hreal]
    · set σ := SxLN A γ a.2 with hσ
      simp only [outSim, progSim, stwNC]
      cases hok : okW (A.adv σ) idx (sk σ) γ.1.1 γ.1.2
      · simp only [FLNC, GV_false_of_okW _ idx PI V _ (hsk σ) _ _ _ hok, Bool.cond_false,
          Bool.false_eq_true, ↓reduceIte, Option.elim]
      · have hwf := tokW_wf (A.adv σ) (sk σ) (hsk σ) (b ^^ false)
          (bif b ^^ false then γ.1.2 else γ.1.1)
        obtain ⟨-, -, hsim⟩ := redeem_facts (A.adv σ).ro simR PR
          (ptW (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 false) hwf.1 hwf.2.1 hwf.2.2
          (redeemOk_ptW (A.adv σ) idx (sk σ) γ.1.1 γ.1.2 hok b false)
        simp only [↓reduceIte, Option.elim]
        rw [hsim]

/-- **The right hop**: the right redemption simulated, its statement read off the tables through
the setup, the left simulation's programming depending on it; `ε` plus the collision term
`deltaNCA`. -/
theorem hopR_NCRA [Fintype CR] [Nonempty CR] (hsk : ∀ σ c, (sk σ c).Correct ((A.adv σ).pk c))
    (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hV5 : ∀ pf x, Rd5 (V pf x) v5) (hVE : ∀ pf x, RdE (V pf x) vE)
    (hpR : ∀ x c, IsProg (progR x c) m5 mE)
    {AdmS : (X : Type) → (Tab3 × ShM R → X) → Prop}
    (hS : ∀ γ : (TIr × TIr) × TRs CR, AdmS Sg (SxRN A γ))
    {ε : ℝ} (hR : ZeroKnowledgeROA RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmS
      (Budget pR q3 (r5 + v5 + (r5 + v5) + (0 + 0) + q5 + m5) (rE + vE + (rE + vE) + (0 + 0) + qE + mE))
      ε) (b : Bool) :
    |pr _ (gameNCRA A idx PI V sk b (fun σ => redSimRO (A.adv σ).ro simR progR)
        (fun σ => redRealRO (A.adv σ).ro PR)) -
      pr _ (gameNCRA A idx PI V sk b (fun σ => redSimRO (A.adv σ).ro simR progR)
        (fun σ => redSimRO (A.adv σ).ro simR progR))| ≤
      ε + deltaNCA A idx sk PR progR b := by
  have h := hop_roA (Γ := (TIr × TIr) × TRs CR) (ρ := Coins proveSeedBytes) (G := Tab3) (C := CR)
    (S := ShM R) (SxRN A)
    (fun γ σ ρ g s => (redRealRO (A.adv σ).ro PR (ρ, g)).out
      (ptW (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 true) s)
    (fun γ σ c => redSim (A.adv σ).ro.base simR c (ptW (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 true))
    (fun γ σ c s => if okW (A.adv σ) idx (sk σ) γ.1.1 γ.1.2 = true then
      progR (xROf (A.adv σ).ro (ptW (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 true)) c s else s)
    (fun γ σ s => LNC (A.adv σ) idx (sk σ) progR b γ s)
    (fun γ σ => FRNC (A.adv σ) idx PI V (sk σ) simR b γ) (ε := ε) fun γ => ?_
  · let e : ((TIr × TIr) × TRs CR) × (Coins proveSeedBytes × (Tab3 × ShM R)) ≃
        ((TIr × TIr) × (TRs CR × TRr)) × ShM R :=
      { toFun := fun z => ((z.1.1, (z.1.2, (z.2.1, z.2.2.1))), z.2.2.2)
        invFun := fun x => ((x.1.1, x.1.2.1), (x.1.2.2.1, (x.1.2.2.2, x.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let e' : ((TIr × TIr) × TRs CR) × (CR × (Tab3 × ShM R)) ≃
        ((TIr × TIr) × (TRs CR × TRs CR)) × ShM R :=
      { toFun := fun z => ((z.1.1, (z.1.2, (z.2.1, z.2.2.1))), z.2.2.2)
        invFun := fun x => ((x.1.1, x.1.2.1), (x.1.2.2.1, (x.1.2.2.2, x.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e, ← pr_equiv e']
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · have hL : ∀ σ, IsProg (LNC (A.adv σ) idx (sk σ) progR b γ) m5 mE := fun σ =>
      IsProg.ite _ (hpR _ _) (IsProg.id.mono (Nat.zero_le _) (Nat.zero_le _))
    have hz := hR Sg (SxRN A γ) (fun σ => stwNC (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 true) (hS γ)
      (fun σ => stwNC_rel (A.adv σ) idx (sk σ) (hsk σ) b γ.1.1 γ.1.2 true) []
      (fun σ o g s => FRNC (A.adv σ) idx PI V (sk σ) simR b γ
        (.ok ((ptW (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 true).tok.nf ++ o)) g
        (LNC (A.adv σ) idx (sk σ) progR b γ s))
      fun σ => ⟨fun o s => (hA σ).h3R _ _ _ _ _,
        fun o g => (rd5_viewNC (hA σ) (rd5_GV hPI5 hV5 _ _) (Rd5.const _) (Rd5.const _) _).comp_prog
          (hL σ),
        fun o g => (rdE_viewNC (hA σ) (rdE_GV hPIE hVE _ _) (RdE.const _) (RdE.const _) _).comp_prog
          (hL σ)⟩
    refine le_of_eq_of_le (congrArg₂ (fun x y => |x - y|) (pr_congr fun a => ?_)
      (pr_congr fun a => ?_)) hz
    · set σ := SxRN A γ a.2 with hσ
      simp only [outReal, stwNC]
      cases hok : okW (A.adv σ) idx (sk σ) γ.1.1 γ.1.2
      · simp only [FRNC, GV_false_of_okW _ idx PI V _ (hsk σ) _ _ _ hok, Bool.cond_false]
      · have hwf := tokW_wf (A.adv σ) (sk σ) (hsk σ) (b ^^ true)
          (bif b ^^ true then γ.1.2 else γ.1.1)
        obtain ⟨-, hreal, -⟩ := redeem_facts (A.adv σ).ro simR PR
          (ptW (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 true) hwf.1 hwf.2.1 hwf.2.2
          (redeemOk_ptW (A.adv σ) idx (sk σ) γ.1.1 γ.1.2 hok b true)
        simp only [↓reduceIte, Option.elim]
        rw [hreal]
    · set σ := SxRN A γ a.2 with hσ
      simp only [outSim, progSim, stwNC]
      cases hok : okW (A.adv σ) idx (sk σ) γ.1.1 γ.1.2
      · simp only [FRNC, GV_false_of_okW _ idx PI V _ (hsk σ) _ _ _ hok, Bool.cond_false,
          Bool.false_eq_true, ↓reduceIte, Option.elim]
      · have hwf := tokW_wf (A.adv σ) (sk σ) (hsk σ) (b ^^ true)
          (bif b ^^ true then γ.1.2 else γ.1.1)
        obtain ⟨-, -, hsim⟩ := redeem_facts (A.adv σ).ro simR PR
          (ptW (A.adv σ) idx (sk σ) b γ.1.1 γ.1.2 true) hwf.1 hwf.2.1 hwf.2.2
          (redeemOk_ptW (A.adv σ) idx (sk σ) γ.1.1 γ.1.2 hok b true)
        simp only [↓reduceIte, Option.elim]
        rw [hsim]

end Hops

/-! ## Hiding the issuance slices, the abort hop and the swap -/

section Fresh

variable {Sg : Type} (A : AdversaryNCRA R Sg) (idx : AnchorSet → UOVKey → ℕ)
  (PI : ProverRO R IssueInstance) (V : VerifierRO R) (sk : Sg → Bool → Signer) {CR : Type}
  (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → ShM R → ShM R)

/-- The state of the simulated game with independent slices: the setup on the slices the
Moderator sees (`h₀`, `h₁` and the redemption slices) and the tables. The tape is
`((x₁, h₁), (((x₀, h₀), (cL, cR)), t))`, as in `simFreshNC`. -/
def σF (z : (TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)) : Sg :=
  A.setup ((z.2.1.1.2, z.1.2), (z.2.1.2.1.2, z.2.1.2.2.2)) z.2.2

/-- The game with both redemptions simulated, the Moderator seeing independent slices. -/
def simFreshNCA (b : Bool) (z : (TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)) :
    Prop :=
  simFreshNC (A.adv (σF A z)) idx PI V (sk (σF A z)) simR progR b z

/-- The symmetric hybrid at the state of the tape. -/
def hybFreshNCA (b : Bool) (z : (TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)) :
    Prop :=
  hybFreshNC (A.adv (σF A z)) idx PI V simR progR b z

variable {A idx PI V sk simR progR}

/-- **Both slices the Moderator sees made independent**: `2·(k₃ + q₃)·2⁻¹²⁸` (the setup and the
guess both read them). -/
theorem sim_fresh_NCA [Fintype CR] [Nonempty CR] {q3 q5 qE k3 k2 k5 kE : ℕ}
    (hA : A.Budget q3 q5 qE) (hK : A.KBudget k3 k2 k5 kE) (hPI : SliceAt PI) (b : Bool) :
    |pr _ (gameNCRA A idx PI V sk b (fun σ => redSimRO (A.adv σ).ro simR progR)
        (fun σ => redSimRO (A.adv σ).ro simR progR)) -
      pr _ (simFreshNCA A idx PI V sk simR progR b)| ≤ 2 * ((k3 + q3 : ℕ) / 2 ^ 128) := by
  -- Client `0`'s slice.
  have h0 := abs_pr_slice_hop (Rest := (TIr × (TRs CR × TRs CR)) × ShM R) (q := k3 + q3)
    (fun x₀ h r => gameNCROS (A.adv (A.setup ((h, r.1.1.2.2), (r.1.2.1.2, r.1.2.2.2)) r.2)) idx PI V
      (sk (A.setup ((h, r.1.1.2.2), (r.1.2.1.2, r.1.2.2.2)) r.2)) b x₀ r.1.1
      (redSimRO (A.adv (A.setup ((h, r.1.1.2.2), (r.1.2.1.2, r.1.2.2.2)) r.2)).ro simR progR r.1.2.1)
      (redSimRO (A.adv (A.setup ((h, r.1.1.2.2), (r.1.2.1.2, r.1.2.2.2)) r.2)).ro simR progR r.1.2.2)
      h r.1.1.2.2 r.2)
    (fun n ρ ρ' g g' h r hg => gameNCROS_congr₀ (x₀ := (n, (ρ, g))) (x₀' := (n, (ρ', g'))) hPI b
      rfl hg _ _ _ _ _ _)
    (fun x r => ((hK.s0 r.1.1.2.2 r.1.2.1.2 r.1.2.2.2).rd3 r.2).bind
      (f := fun σ h => gameNCROS (A.adv σ) idx PI V (sk σ) b x r.1.1
        (redSimRO (A.adv σ).ro simR progR r.1.2.1) (redSimRO (A.adv σ).ro simR progR r.1.2.2)
        h r.1.1.2.2 r.2) fun σ => (hA σ).h30 _ _ _ _ _)
  -- Client `1`'s slice.
  have h1 := abs_pr_slice_hop (Rest := ((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R) (q := k3 + q3)
    (fun x₁ h r => gameNCROS (A.adv (A.setup ((r.1.1.2, h), (r.1.2.1.2, r.1.2.2.2)) r.2)) idx PI V
      (sk (A.setup ((r.1.1.2, h), (r.1.2.1.2, r.1.2.2.2)) r.2)) b r.1.1.1 x₁
      (redSimRO (A.adv (A.setup ((r.1.1.2, h), (r.1.2.1.2, r.1.2.2.2)) r.2)).ro simR progR r.1.2.1)
      (redSimRO (A.adv (A.setup ((r.1.1.2, h), (r.1.2.1.2, r.1.2.2.2)) r.2)).ro simR progR r.1.2.2)
      r.1.1.2 h r.2)
    (fun n ρ ρ' g g' h r hg => gameNCROS_congr₁ (x₁ := (n, (ρ, g))) (x₁' := (n, (ρ', g'))) hPI b _
      rfl hg _ _ _ _ _)
    (fun x r => ((hK.s1 r.1.1.2 r.1.2.1.2 r.1.2.2.2).rd3 r.2).bind
      (f := fun σ h => gameNCROS (A.adv σ) idx PI V (sk σ) b r.1.1.1 x
        (redSimRO (A.adv σ).ro simR progR r.1.2.1) (redSimRO (A.adv σ).ro simR progR r.1.2.2)
        r.1.1.2 h r.2) fun σ => (hA σ).h31 _ _ _ _ _)
  let e0 : TIr × ((TIr × (TRs CR × TRs CR)) × ShM R) ≃ ((TIr × TIr) × (TRs CR × TRs CR)) × ShM R :=
    { toFun := fun z => (((z.1, z.2.1.1), z.2.1.2), z.2.2)
      invFun := fun x => (x.1.1.1, ((x.1.1.2, x.1.2), x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e1 : TIr × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R) ≃
      (TIr × Tab3) × ((TIr × (TRs CR × TRs CR)) × ShM R) :=
    { toFun := fun z => ((z.2.1.1.1, z.2.1.1.2), ((z.1, z.2.1.2), z.2.2))
      invFun := fun y => (y.2.1.1, (((y.1.1, y.1.2), y.2.1.2), y.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e1] at h0
  rw [← pr_equiv e0]
  calc _ ≤ _ := abs_sub_le _ (pr (TIr × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)) (fun z =>
        gameNCROS (A.adv (A.setup ((z.2.1.1.2, z.1.2.2), (z.2.1.2.1.2, z.2.1.2.2.2)) z.2.2)) idx PI V
          (sk (A.setup ((z.2.1.1.2, z.1.2.2), (z.2.1.2.1.2, z.2.1.2.2.2)) z.2.2)) b z.2.1.1.1 z.1
          (redSimRO (A.adv (A.setup ((z.2.1.1.2, z.1.2.2), (z.2.1.2.1.2, z.2.1.2.2.2)) z.2.2)).ro simR
            progR z.2.1.2.1)
          (redSimRO (A.adv (A.setup ((z.2.1.1.2, z.1.2.2), (z.2.1.2.1.2, z.2.1.2.2.2)) z.2.2)).ro simR
            progR z.2.1.2.2) z.2.1.1.2 z.1.2.2 z.2.2)) _
    _ ≤ (k3 + q3 : ℕ) / 2 ^ 128 + (k3 + q3 : ℕ) / 2 ^ 128 := add_le_add h0 h1
    _ = 2 * ((k3 + q3 : ℕ) / 2 ^ 128) := by ring

/-- **The abort hop**, the state independent of the Clients' coins: `φ false + φ true` for any
uniform bound `φ` of the abort probabilities at every state. -/
theorem fresh_hyb_NCA [Fintype CR] [Nonempty CR] (hsk : ∀ σ c, (sk σ c).Correct ((A.adv σ).pk c))
    (hidx : IdxSound idx) {φ : Bool → ℝ} (hφ : ∀ σ c, phi (A.adv σ).nc (sk σ) c ≤ φ c)
    (b : Bool) :
    |pr _ (simFreshNCA A idx PI V sk simR progR b) - pr _ (hybFreshNCA A idx PI V simR progR b)| ≤
      φ false + φ true := by
  refine (abs_pr_sub_le_of_agree _ _ (fun z :
      (TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R) =>
      (sk (σF A z) false).derivePreimage (com (List.ofFn z.2.1.1.1.1.1)
          (A.adv (σF A z)).nc.base.ci (A.adv (σF A z)).nc.base.cr (List.ofFn z.2.1.1.1.1.2)) = none ∨
        (sk (σF A z) true).derivePreimage (com (List.ofFn z.1.1.1.1)
          (A.adv (σF A z)).nc.base.ci (A.adv (σF A z)).nc.base.cr (List.ofFn z.1.1.1.2)) = none)
      fun z hz => ?_).trans ((pr_or_le _ _).trans (add_le_add ?_ ?_))
  · simp only [not_or] at hz
    exact simFresh_iff_hyb (hsk _) hidx b _ _ _ _ _ _ _ hz.1 hz.2
  · -- Client `0`'s coins are independent of the state.
    let e : NR × ((TIr × Tab3) × ((((Coins proveSeedBytes × Tab3) × Tab3) × (TRs CR × TRs CR)) ×
        ShM R)) ≃ (TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R) :=
      { toFun := fun a => (a.2.1, ((((a.1, a.2.2.1.1.1), a.2.2.1.1.2), a.2.2.1.2), a.2.2.2))
        invFun := fun z => (z.2.1.1.1.1, (z.1, (((z.2.1.1.1.2, z.2.1.1.2), z.2.1.2), z.2.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e]
    refine pr_le_of_snd fun r => le_trans (le_of_eq ?_) (hφ (σF A (e (default, r))) false)
    rfl
  · let e : NR × (((Coins proveSeedBytes × Tab3) × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) ×
        ShM R)) ≃ (TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R) :=
      { toFun := fun a => (((a.1, a.2.1.1), a.2.1.2), a.2.2)
        invFun := fun z => (z.1.1.1, ((z.1.1.2, z.1.2), z.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e]
    refine pr_le_of_snd fun r => le_trans (le_of_eq ?_) (hφ (σF A (e (default, r))) true)
    rfl

/-- **The symmetric hybrid's worlds coincide**: the swap of the Clients' tapes keeps the slices the
Moderator sees and the tables, hence the state. -/
theorem hybFresh_eqA [Fintype CR] :
    pr _ (hybFreshNCA A idx PI V simR progR false) = pr _ (hybFreshNCA A idx PI V simR progR true) := by
  rw [← pr_equiv swapNC]
  exact pr_congr fun z => hybV_swap _ _ _ _ _ _ _

/-- **One Anchor at every state: the simulated game's worlds coincide** (any index rule). -/
theorem simFresh_eq_oneA [Fintype CR] (hpk : ∀ σ, (A.adv σ).pk false = (A.adv σ).pk true)
    (hs : ∀ σ, sk σ false = sk σ true) :
    pr _ (simFreshNCA A idx PI V sk simR progR false) =
      pr _ (simFreshNCA A idx PI V sk simR progR true) := by
  rw [← pr_equiv swapNC]
  refine pr_congr fun z => ?_
  have hsw : σF A (swapNC z) = σF A z := rfl
  show simFreshNCA A idx PI V sk simR progR false (swapNC z) ↔
    simFreshNCA A idx PI V sk simR progR true z
  unfold simFreshNCA
  rw [hsw]
  set σ := σF A z with hσ
  have htok : tokW (A.adv σ) (sk σ) false = tokW (A.adv σ) (sk σ) true := by
    funext x
    simp only [tokW, hs σ]
  have hokC (side : Bool) : okC (A.adv σ) idx (sk σ) false side = okC (A.adv σ) idx (sk σ) true side := by
    funext x
    simp only [okC, htok, hpk σ]
  have hgood : goodV (A.adv σ) idx PI V (sk σ) false = goodV (A.adv σ) idx PI V (sk σ) true := by
    funext x v
    have hpk' : (A.adv σ).nc.pk false = (A.adv σ).nc.pk true := hpk σ
    simp only [goodV, goodNC, okNC, tokDNC, tokNC, respNC, hpk', hs σ]
  have hok (x₀ x₁ : TIr) : okW (A.adv σ) idx (sk σ) x₀ x₁ = okW (A.adv σ) idx (sk σ) x₁ x₀ := by
    unfold okW
    rw [hokC false, hokC true]
    have e : ∀ a b c d : Bool, (a && b && c && d) = (c && d && a && b) := by decide
    exact e _ _ _ _
  have hpt (x₀ x₁ : TIr) (side : Bool) :
      ptW (A.adv σ) idx (sk σ) false x₀ x₁ side = ptW (A.adv σ) idx (sk σ) true x₁ x₀ side := by
    unfold ptW
    cases side
    · simp only [Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.cond_false, Bool.cond_true,
        htok, hpk σ]
    · simp only [Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.cond_false, Bool.cond_true,
        htok, hpk σ]
  have hG (x₀ x₁ : TIr) (v : ShM R) :
      GV (A.adv σ) idx PI V (sk σ) x₀ x₁ v = GV (A.adv σ) idx PI V (sk σ) x₁ x₀ v := by
    unfold GV
    rw [hgood, Bool.and_comm]
  simp only [simFreshNC, swapNC, Equiv.coe_fn_mk]
  unfold gameNCROS
  rw [hok, hpt, hpt, hG]

end Fresh

/-! ## Theorem 4(b′) with the Moderator's choices read off the tables -/

section Main

variable {Sg : Type} {A : AdversaryNCRA R Sg} {idx : AnchorSet → UOVKey → ℕ}
  {PI : ProverRO R IssueInstance} {V : VerifierRO R} {sk : Sg → Bool → Signer}
  {PR : ProverRO R RedeemInstance} {CR : Type} [Fintype CR] [Nonempty CR]
  {simR : RedeemInstance → CR → Bytes} {progR : RedeemInstance → CR → ShM R → ShM R}
  {q3 q5 qE r5 rE v5 vE m5 mE k3 k2 k5 kE : ℕ}

/-- One world: the real game against the simulated game with independent slices. -/
theorem real_simFresh_NCA (hsk : ∀ σ c, (sk σ c).Correct ((A.adv σ).pk c))
    (hA : A.Budget q3 q5 qE) (hK : A.KBudget k3 k2 k5 kE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPI3 : SliceAt PI)
    (hV5 : ∀ pf x, Rd5 (V pf x) v5) (hVE : ∀ pf x, RdE (V pf x) vE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpR : ∀ x c, IsProg (progR x c) m5 mE) {AdmS : (X : Type) → (Tab3 × ShM R → X) → Prop}
    (hSL : ∀ γ : (TIr × TIr) × TRr, AdmS Sg (SxLN A γ))
    (hSR : ∀ γ : (TIr × TIr) × TRs CR, AdmS Sg (SxRN A γ)) {εR : ℕ → ℕ → ℝ}
    (hR : ∀ a c, ZeroKnowledgeROA RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmS
      (Budget pR q3 a c) (εR a c)) (b : Bool) :
    |pr _ (realGameNCRA A idx PI V sk PR b) - pr _ (simFreshNCA A idx PI V sk simR progR b)| ≤
      εR (r5 + v5 + (r5 + v5) + (0 + r5) + q5) (rE + vE + (rE + vE) + (0 + rE) + qE) +
        (εR (r5 + v5 + (r5 + v5) + (0 + 0) + q5 + m5) (rE + vE + (rE + vE) + (0 + 0) + qE + mE) +
          deltaNCA A idx sk PR progR b) + 2 * ((k3 + q3 : ℕ) / 2 ^ 128) := by
  have e0 : pr _ (realGameNCRA A idx PI V sk PR b) =
      pr _ (gameNCRA A idx PI V sk b (fun σ => redRealRO (A.adv σ).ro PR)
        (fun σ => redRealRO (A.adv σ).ro PR)) :=
    pr_congr fun x => realGameNCRA_iff A idx PI V sk hsk PR b x
  have h1 := hopL_NCRA (idx := idx) (simR := simR) hsk hA hPI5 hPIE hV5 hVE hPR5 hPRE hSL (hR _ _) b
  have h2 := hopR_NCRA (idx := idx) (PR := PR) hsk hA hPI5 hPIE hV5 hVE hpR hSR (hR _ _) b
  have h3 := sim_fresh_NCA (idx := idx) (V := V) (sk := sk) (simR := simR) (progR := progR) hA hK
    hPI3 b
  rw [e0]
  have := abs_sub_le (pr _ (gameNCRA A idx PI V sk b (fun σ => redRealRO (A.adv σ).ro PR)
      (fun σ => redRealRO (A.adv σ).ro PR)))
    (pr _ (gameNCRA A idx PI V sk b (fun σ => redSimRO (A.adv σ).ro simR progR)
      (fun σ => redRealRO (A.adv σ).ro PR)))
    (pr _ (simFreshNCA A idx PI V sk simR progR b))
  have := abs_sub_le (pr _ (gameNCRA A idx PI V sk b (fun σ => redSimRO (A.adv σ).ro simR progR)
      (fun σ => redRealRO (A.adv σ).ro PR)))
    (pr _ (gameNCRA A idx PI V sk b (fun σ => redSimRO (A.adv σ).ro simR progR)
      (fun σ => redSimRO (A.adv σ).ro simR progR)))
    (pr _ (simFreshNCA A idx PI V sk simR progR b))
  linarith

/-- **Theorem 4(b′) in the random-oracle and ideal-cipher model with the Moderator's choices read
off the tables, for any proof systems.** The Moderator's setup reads the four slices and the shared
tables within `(k₃, k₂, k₅, k_E)` (`KBudget`), its guess within `(q₃, q₅, q_E)` at every state; the
redemption proofs are `ZeroKnowledgeROA` for readers `AdmS` that contain the setup read off either
redemption slice and the shared tables. Then

    2·(εR(hop L) + εR(hop R)) + Σ_b deltaNCA b + 2·(φ false + φ true) + 4·(k₃ + q₃)·2⁻¹²⁸,

with `φ c` any bound of Anchor `c`'s abort probability at every state. -/
theorem anonymityNCRA (hsk : ∀ σ c, (sk σ c).Correct ((A.adv σ).pk c)) (hidx : IdxSound idx)
    (hA : A.Budget q3 q5 qE) (hK : A.KBudget k3 k2 k5 kE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPI3 : SliceAt PI)
    (hV5 : ∀ pf x, Rd5 (V pf x) v5) (hVE : ∀ pf x, RdE (V pf x) vE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpR : ∀ x c, IsProg (progR x c) m5 mE) {AdmS : (X : Type) → (Tab3 × ShM R → X) → Prop}
    (hSL : ∀ γ : (TIr × TIr) × TRr, AdmS Sg (SxLN A γ))
    (hSR : ∀ γ : (TIr × TIr) × TRs CR, AdmS Sg (SxRN A γ)) {εR : ℕ → ℕ → ℝ}
    (hR : ∀ a c, ZeroKnowledgeROA RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmS
      (Budget pR q3 a c) (εR a c)) {φ : Bool → ℝ} (hφ : ∀ σ c, phi (A.adv σ).nc (sk σ) c ≤ φ c) :
    |pr _ (realGameNCRA A idx PI V sk PR false) - pr _ (realGameNCRA A idx PI V sk PR true)| ≤
      2 * (εR (r5 + v5 + (r5 + v5) + (0 + r5) + q5) (rE + vE + (rE + vE) + (0 + rE) + qE) +
          εR (r5 + v5 + (r5 + v5) + (0 + 0) + q5 + m5) (rE + vE + (rE + vE) + (0 + 0) + qE + mE)) +
        (deltaNCA A idx sk PR progR false + deltaNCA A idx sk PR progR true) +
        2 * (φ false + φ true) + 4 * ((k3 + q3 : ℕ) / 2 ^ 128) := by
  have h0 := real_simFresh_NCA (idx := idx) (simR := simR) hsk hA hK hPI5 hPIE hPI3 hV5 hVE hPR5 hPRE hpR hSL hSR
    hR false
  have h1 := real_simFresh_NCA (idx := idx) (simR := simR) hsk hA hK hPI5 hPIE hPI3 hV5 hVE hPR5 hPRE hpR hSL hSR
    hR true
  have g0 := fresh_hyb_NCA (PI := PI) (V := V) (simR := simR) (progR := progR) hsk hidx hφ false
  have g1 := fresh_hyb_NCA (PI := PI) (V := V) (simR := simR) (progR := progR) hsk hidx hφ true
  have he := hybFresh_eqA (A := A) (idx := idx) (PI := PI) (V := V) (simR := simR) (progR := progR)
  rw [abs_le] at h0 h1 g0 g1 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, g0.1, g0.2, g1.1, g1.2]

/-- **Unlinkability against a non-colluding Moderator whose choices read the tables**: one Anchor
at every state, any index rule, no abort term. -/
theorem unlinkabilityNCRA (hsk : ∀ σ c, (sk σ c).Correct ((A.adv σ).pk c))
    (hpk : ∀ σ, (A.adv σ).pk false = (A.adv σ).pk true) (hs : ∀ σ, sk σ false = sk σ true)
    (hA : A.Budget q3 q5 qE) (hK : A.KBudget k3 k2 k5 kE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPI3 : SliceAt PI)
    (hV5 : ∀ pf x, Rd5 (V pf x) v5) (hVE : ∀ pf x, RdE (V pf x) vE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpR : ∀ x c, IsProg (progR x c) m5 mE) {AdmS : (X : Type) → (Tab3 × ShM R → X) → Prop}
    (hSL : ∀ γ : (TIr × TIr) × TRr, AdmS Sg (SxLN A γ))
    (hSR : ∀ γ : (TIr × TIr) × TRs CR, AdmS Sg (SxRN A γ)) {εR : ℕ → ℕ → ℝ}
    (hR : ∀ a c, ZeroKnowledgeROA RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmS
      (Budget pR q3 a c) (εR a c)) :
    |pr _ (realGameNCRA A idx PI V sk PR false) - pr _ (realGameNCRA A idx PI V sk PR true)| ≤
      2 * (εR (r5 + v5 + (r5 + v5) + (0 + r5) + q5) (rE + vE + (rE + vE) + (0 + rE) + qE) +
          εR (r5 + v5 + (r5 + v5) + (0 + 0) + q5 + m5) (rE + vE + (rE + vE) + (0 + 0) + qE + mE)) +
        (deltaNCA A idx sk PR progR false + deltaNCA A idx sk PR progR true) +
        4 * ((k3 + q3 : ℕ) / 2 ^ 128) := by
  have h0 := real_simFresh_NCA (idx := idx) (simR := simR) hsk hA hK hPI5 hPIE hPI3 hV5 hVE hPR5 hPRE hpR hSL hSR
    hR false
  have h1 := real_simFresh_NCA (idx := idx) (simR := simR) hsk hA hK hPI5 hPIE hPI3 hV5 hVE hPR5 hPRE hpR hSL hSR
    hR true
  have he := simFresh_eq_oneA (idx := idx) (PI := PI) (V := V) (simR := simR) (progR := progR) hpk hs
  rw [abs_le] at h0 h1 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

end Main

end VoleMole.Privacy.Moussaka
