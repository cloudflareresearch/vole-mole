import VoleMole.Privacy.ZeroKnowledgeRO
import VoleMole.Privacy.Hybrid

/-!
# Non-malleability games: two honest proofs, a zero-knowledge hop, weak simulation-extractability

The no-theft theorem of Ratatouille (`security/ratatouille.md` Theorem 3, N2a) and the
redemption non-malleability theorem of Moussaka (`security/moussaka.md` Theorem 3) have one
shape. An honest Client with secret coins `ω` makes two proofs (an issuance and a spend or a
redemption) for statements the adversary helps choose; the adversary sees them and the random
tables, and outputs a request of its own. It wins if the request is accepted, its statement
differs from the honest ones (weak non-malleability: a verbatim copy is allowed, F2), and the
witness the straight-line extractor reads off the run is either not a witness or opens one of the
honest Client's commitments. The proof replaces the honest proofs by simulated ones (zero
knowledge), applies weak simulation-extractability (SE) in the simulated world, and charges the
rest to a one-wayness game for the commitment, which the simulated world reduces to because the
Client's openings enter it only through the commitments.

This file is the protocol-independent part, in the table model of `Privacy/ZeroKnowledgeRO.lean`
(uniform tapes, the random tables part of the tape, simulators that program the shared tables).

* **The games** (`realG`, `simG`): the first proof (`P₁` real, `Sm₁` simulated, programming
  `pg₁`), the second proof, whose statement may depend on the first output (`P₂`, `Sm₂`, `pg₂`),
  and an event `Ev` of the honest secrets, the two outputs, the two proofs' private tables and the
  shared tables. In the simulated game the event reads the tables both simulators programmed.
* **`real_sim_le`**: the two hops of `Privacy.hop_ro`, in order: the first proof, against the
  rest of the game with the second proof real (`ε₁`); then the second proof, run on the tables the
  first simulation programmed (`ε₂`, plus the collision term `δ = deltaG`: the real second proof
  reads the tables differently with and without that programming).
* **`theft_le`**: for an event of the form `Acc ∧ Fresh ∧ (¬ Rel ∨ Opens)`, the real probability
  is at most `ε₁ + ε₂ + δ` plus the simulated probability of `Acc ∧ Fresh ∧ ¬ Rel` (weak SE) plus
  the simulated probability of `Opens` (one-wayness).
* **`WeakSE2`**: weak simulation-extractability against adversaries that see one simulated proof
  of each of two relations, for statements they choose without reading the tables
  (`lean/docs/extraction/L8-simulation-extractability.md`, game `SE_A` with `q_S = 2`, weak form).
  The extractor sees the simulated statements and proofs (L8's log, item 2), the adversary's last
  stage as a function of the tables (its queries, item 1) and the programmed tables. **This is a
  hypothesis** here. `Theft/SimExtract.lean` proves it from plain extraction and a
  programmed-point term (`weakSE2_of_plain`), both still hypotheses; L8 proves it on paper.
* `zk_step`: one zero-knowledge hop for a proof that runs only when its statement exists, the
  form `ZeroKnowledgeRO` gives for the protocols' Clients.
-/

open Finset

namespace VoleMole.Theft

open VoleMole.Privacy

/-! ## Optional statements -/

section Opt

variable {I W P ρ C G S : Type*}

/-- A simulated proof of an optional statement (none when there is no statement). -/
def simO (sim : I → C → Option P) (x : Option I) (c : C) : Option P :=
  match x with
  | some x => sim x c
  | none => none

/-- The programming of an optional statement's simulation (none when there is no statement). -/
def progO (prog : I → C → S → S) (x : Option I) (c : C) (s : S) : S :=
  match x with
  | some x => prog x c s
  | none => s

/-- A real proof of an optional statement and witness. -/
def proveO (prove : I → W → ρ → G → S → Option P) (xw : Option (I × W)) (r : ρ) (g : G) (s : S) :
    Option P :=
  match xw with
  | some xw => prove xw.1 xw.2 r g s
  | none => none

/-- The statement and proof a Client produced, if it produced a proof. -/
def pairO (x : Option I) (π : Option P) : Option (I × P) :=
  match x, π with
  | some x, some p => some (x, p)
  | _, _ => none

end Opt

/-! ## One zero-knowledge hop -/

section Step

variable {I W P O ρ C G S : Type*} [Fintype ρ] [Nonempty ρ] [Fintype C] [Nonempty C] [Fintype G]
  [Fintype S]

/-- **One hop.** A proof that runs only when its statement exists (`xw`), with an output `φ` of
the proof: replacing it by the simulation costs the zero-knowledge error if the statement exists
(and is in the relation, and the distinguisher is admissible), nothing otherwise. -/
theorem zk_step {R : I → W → Prop} {prove : I → W → ρ → G → S → Option P}
    {sim : I → C → Option P} {prog : I → C → S → S} {Adm : (Option P → G → S → Prop) → Prop}
    {ε : ℝ} (hzk : ZeroKnowledgeRO R prove sim prog Adm ε) (hε : 0 ≤ ε) (xw : Option (I × W))
    (hR : ∀ x w, xw = some (x, w) → R x w) (φ : Option P → O) (D : O → G → S → Prop)
    (hD : ∀ x w, xw = some (x, w) → Adm (fun p g u => D (φ p) g u)) :
    |pr ((ρ × G) × S) (fun a => D (φ (proveO prove xw a.1.1 a.1.2 a.2)) a.1.2 a.2) -
      pr ((C × G) × S) (fun a =>
        D (φ (simO sim (xw.map Prod.fst) a.1.1)) a.1.2 (progO prog (xw.map Prod.fst) a.1.1 a.2))| ≤
      ε := by
  rcases xw with _ | ⟨x, w⟩
  · simp only [proveO, simO, progO, Option.map_none]
    have e1 : pr ((ρ × G) × S) (fun a => D (φ none) a.1.2 a.2) = pr (G × S) (fun a => D (φ none) a.1 a.2) := by
      rw [← pr_equiv (Equiv.prodAssoc ρ G S).symm]
      exact pr_prod_snd (α := ρ) (fun a : G × S => D (φ none) a.1 a.2)
    have e2 : pr ((C × G) × S) (fun a => D (φ none) a.1.2 a.2) = pr (G × S) (fun a => D (φ none) a.1 a.2) := by
      rw [← pr_equiv (Equiv.prodAssoc C G S).symm]
      exact pr_prod_snd (α := C) (fun a : G × S => D (φ none) a.1 a.2)
    rw [e1, e2, sub_self, abs_zero]
    exact hε
  · have h := hzk x w (hR x w rfl) _ (hD x w rfl)
    simp only [proveO, simO, progO, Option.map_some]
    exact h

end Step

/-! ## The two games and the two hops -/

section Games

variable {Ω ρ₁ C₁ ρ₂ C₂ G S O₁ O₂ : Type*}
  (P₁ : Ω → ρ₁ → G → S → O₁) (Sm₁ : Ω → C₁ → O₁) (pg₁ : Ω → C₁ → S → S)
  (P₂ : Ω → O₁ → ρ₂ → G → S → O₂) (Sm₂ : Ω → O₁ → C₂ → O₂) (pg₂ : Ω → O₁ → C₂ → S → S)
  (Ev : Ω → O₁ → O₂ → G → G → S → Prop)

/-- **The real game**: both proofs real, on uniform tables. The tape is
`((ω, (ρ₂, g₂)), ((ρ₁, g₁), s))`: the honest secrets, the second proof's randomness and private
table, the first proof's, and the shared tables. -/
def realG (z : (Ω × (ρ₂ × G)) × ((ρ₁ × G) × S)) : Prop :=
  Ev z.1.1 (P₁ z.1.1 z.2.1.1 z.2.1.2 z.2.2)
    (P₂ z.1.1 (P₁ z.1.1 z.2.1.1 z.2.1.2 z.2.2) z.1.2.1 z.1.2.2 z.2.2) z.2.1.2 z.1.2.2 z.2.2

/-- **The simulated game**: both proofs simulated, the event read on the tables both simulations
programmed. The tape is `((ω, (c₁, g₁)), ((c₂, g₂), s))`. -/
def simG (z : (Ω × (C₁ × G)) × ((C₂ × G) × S)) : Prop :=
  Ev z.1.1 (Sm₁ z.1.1 z.1.2.1) (Sm₂ z.1.1 (Sm₁ z.1.1 z.1.2.1) z.2.1.1) z.1.2.2 z.2.1.2
    (pg₁ z.1.1 z.1.2.1 (pg₂ z.1.1 (Sm₁ z.1.1 z.1.2.1) z.2.1.1 z.2.2))

/-- The hybrid: the first proof simulated, the second real on the tables the first programmed. -/
def hybG (z : (Ω × (C₁ × G)) × ((ρ₂ × G) × S)) : Prop :=
  Ev z.1.1 (Sm₁ z.1.1 z.1.2.1)
    (P₂ z.1.1 (Sm₁ z.1.1 z.1.2.1) z.2.1.1 z.2.1.2 (pg₁ z.1.1 z.1.2.1 z.2.2))
    z.1.2.2 z.2.1.2 (pg₁ z.1.1 z.1.2.1 z.2.2)

/-- **The collision term** of the second hop: the real second proof reads the tables differently
with and without the first simulation's programming. -/
def deltaG (z : (Ω × (C₁ × G)) × ((ρ₂ × G) × S)) : Prop :=
  P₂ z.1.1 (Sm₁ z.1.1 z.1.2.1) z.2.1.1 z.2.1.2 (pg₁ z.1.1 z.1.2.1 z.2.2) ≠
    P₂ z.1.1 (Sm₁ z.1.1 z.1.2.1) z.2.1.1 z.2.1.2 z.2.2

/-- The distinguisher of the first hop (fixed `ω`, second proof's randomness and table): the
rest of the game with the second proof real. -/
def D₁ (ω : Ω) (r₂ : ρ₂) (g₂ : G) (o : O₁) (g : G) (u : S) : Prop :=
  Ev ω o (P₂ ω o r₂ g₂ u) g g₂ u

/-- The distinguisher of the second hop (fixed `ω`, first simulation's coins and table): the event,
on the tables the first simulation programs. -/
def D₂ (ω : Ω) (c₁ : C₁) (g₁ : G) (o : O₂) (g : G) (u : S) : Prop :=
  Ev ω (Sm₁ ω c₁) o g₁ g (pg₁ ω c₁ u)

variable [Fintype Ω] [Nonempty Ω] [Fintype ρ₁] [Fintype C₁] [Nonempty C₁]
  [Fintype ρ₂] [Nonempty ρ₂] [Fintype C₂] [Fintype G] [Nonempty G] [Fintype S]

/-- Swap the middle coordinates of the hybrid tape. -/
def swapEq : (Ω × (ρ₂ × G)) × ((C₁ × G) × S) ≃ (Ω × (C₁ × G)) × ((ρ₂ × G) × S) where
  toFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  invFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The two hops.** If the first proof is `ε₁`-zero-knowledge against `D₁` and the second
`ε₂`-zero-knowledge against `D₂` (for every fixed rest of the tape), the real and the simulated
game differ by at most `ε₁ + ε₂ + Pr[deltaG]`. -/
theorem real_sim_le {ε₁ ε₂ : ℝ}
    (h₁ : ∀ ω r₂ g₂, |pr ((ρ₁ × G) × S) (fun a => D₁ P₂ Ev ω r₂ g₂ (P₁ ω a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((C₁ × G) × S) (fun a => D₁ P₂ Ev ω r₂ g₂ (Sm₁ ω a.1.1) a.1.2 (pg₁ ω a.1.1 a.2))| ≤ ε₁)
    (h₂ : ∀ ω c₁ g₁, |pr ((ρ₂ × G) × S) (fun a =>
        D₂ Sm₁ pg₁ Ev ω c₁ g₁ (P₂ ω (Sm₁ ω c₁) a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((C₂ × G) × S) (fun a => D₂ Sm₁ pg₁ Ev ω c₁ g₁ (Sm₂ ω (Sm₁ ω c₁) a.1.1) a.1.2
        (pg₂ ω (Sm₁ ω c₁) a.1.1 a.2))| ≤ ε₂) :
    |pr _ (realG P₁ P₂ Ev) - pr _ (simG Sm₁ pg₁ Sm₂ pg₂ Ev)| ≤
      ε₁ + ε₂ + pr _ (deltaG Sm₁ pg₁ P₂) := by
  -- hop 1: the first proof, on the shared first coordinate `(ω, (ρ₂, g₂))`
  have hop1 := abs_pr_prod_sub_le (realG P₁ P₂ Ev)
    (fun z : (Ω × (ρ₂ × G)) × ((C₁ × G) × S) => hybG Sm₁ pg₁ P₂ Ev (swapEq z))
    fun γ => h₁ γ.1 γ.2.1 γ.2.2
  rw [pr_equiv swapEq (hybG Sm₁ pg₁ P₂ Ev)] at hop1
  -- hop 2: the second proof, on the shared first coordinate `(ω, (c₁, g₁))`
  have hop2 := hop_ro (Γ := Ω × (C₁ × G)) (ρ := ρ₂) (G := G) (C := C₂) (S := S)
    (fun γ => P₂ γ.1 (Sm₁ γ.1 γ.2.1)) (fun γ => Sm₂ γ.1 (Sm₁ γ.1 γ.2.1))
    (fun γ => pg₂ γ.1 (Sm₁ γ.1 γ.2.1)) (fun γ => pg₁ γ.1 γ.2.1)
    (fun γ o g u => Ev γ.1 (Sm₁ γ.1 γ.2.1) o γ.2.2 g u) fun γ => h₂ γ.1 γ.2.1 γ.2.2
  have e1 : pr ((Ω × (C₁ × G)) × ((ρ₂ × G) × S)) (hybG Sm₁ pg₁ P₂ Ev) =
      pr ((Ω × (C₁ × G)) × ((ρ₂ × G) × S)) (fun z =>
        Ev z.1.1 (Sm₁ z.1.1 z.1.2.1)
          (P₂ z.1.1 (Sm₁ z.1.1 z.1.2.1) z.2.1.1 z.2.1.2 (pg₁ z.1.1 z.1.2.1 z.2.2)) z.1.2.2 z.2.1.2
          (pg₁ z.1.1 z.1.2.1 z.2.2)) := rfl
  rw [← e1] at hop2
  have := abs_sub_le (pr _ (realG P₁ P₂ Ev)) (pr _ (hybG Sm₁ pg₁ P₂ Ev))
    (pr _ (simG Sm₁ pg₁ Sm₂ pg₂ Ev))
  have e2 : pr ((Ω × (C₁ × G)) × ((C₂ × G) × S)) (simG Sm₁ pg₁ Sm₂ pg₂ Ev) =
      pr ((Ω × (C₁ × G)) × ((C₂ × G) × S)) (fun z =>
        Ev z.1.1 (Sm₁ z.1.1 z.1.2.1) (Sm₂ z.1.1 (Sm₁ z.1.1 z.1.2.1) z.2.1.1) z.1.2.2 z.2.1.2
          (pg₁ z.1.1 z.1.2.1 (pg₂ z.1.1 (Sm₁ z.1.1 z.1.2.1) z.2.1.1 z.2.2))) := rfl
  have e3 : pr ((Ω × (C₁ × G)) × ((ρ₂ × G) × S)) (deltaG Sm₁ pg₁ P₂) =
      pr ((Ω × (C₁ × G)) × ((ρ₂ × G) × S)) (fun z =>
        P₂ z.1.1 (Sm₁ z.1.1 z.1.2.1) z.2.1.1 z.2.1.2 (pg₁ z.1.1 z.1.2.1 z.2.2) ≠
          P₂ z.1.1 (Sm₁ z.1.1 z.1.2.1) z.2.1.1 z.2.1.2 z.2.2) := rfl
  rw [← e2, ← e3] at hop2
  linarith

/-- **The non-malleability bound, generic.** For the event `Acc ∧ Fresh ∧ (¬ Rel ∨ Opens)` (the
output is accepted, its statement is fresh, and the extracted witness is not a witness or opens an
honest commitment):

    Pr_real[event] ≤ ε₁ + ε₂ + Pr[deltaG] + Pr_sim[Acc ∧ Fresh ∧ ¬ Rel] + Pr_sim[Opens].

The fourth term is weak simulation-extractability, the fifth one-wayness of the commitment in the
simulated world. -/
theorem theft_le (Acc Fr Rl Op : Ω → O₁ → O₂ → G → G → S → Prop) {ε₁ ε₂ : ℝ}
    (h₁ : ∀ ω r₂ g₂, |pr ((ρ₁ × G) × S) (fun a => D₁ P₂ (fun ω o₁ o₂ g₁ g₂ s =>
        Acc ω o₁ o₂ g₁ g₂ s ∧ Fr ω o₁ o₂ g₁ g₂ s ∧ (¬ Rl ω o₁ o₂ g₁ g₂ s ∨ Op ω o₁ o₂ g₁ g₂ s))
        ω r₂ g₂ (P₁ ω a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((C₁ × G) × S) (fun a => D₁ P₂ (fun ω o₁ o₂ g₁ g₂ s =>
        Acc ω o₁ o₂ g₁ g₂ s ∧ Fr ω o₁ o₂ g₁ g₂ s ∧ (¬ Rl ω o₁ o₂ g₁ g₂ s ∨ Op ω o₁ o₂ g₁ g₂ s))
        ω r₂ g₂ (Sm₁ ω a.1.1) a.1.2 (pg₁ ω a.1.1 a.2))| ≤ ε₁)
    (h₂ : ∀ ω c₁ g₁, |pr ((ρ₂ × G) × S) (fun a => D₂ Sm₁ pg₁ (fun ω o₁ o₂ g₁ g₂ s =>
        Acc ω o₁ o₂ g₁ g₂ s ∧ Fr ω o₁ o₂ g₁ g₂ s ∧ (¬ Rl ω o₁ o₂ g₁ g₂ s ∨ Op ω o₁ o₂ g₁ g₂ s))
        ω c₁ g₁ (P₂ ω (Sm₁ ω c₁) a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((C₂ × G) × S) (fun a => D₂ Sm₁ pg₁ (fun ω o₁ o₂ g₁ g₂ s =>
        Acc ω o₁ o₂ g₁ g₂ s ∧ Fr ω o₁ o₂ g₁ g₂ s ∧ (¬ Rl ω o₁ o₂ g₁ g₂ s ∨ Op ω o₁ o₂ g₁ g₂ s))
        ω c₁ g₁ (Sm₂ ω (Sm₁ ω c₁) a.1.1) a.1.2 (pg₂ ω (Sm₁ ω c₁) a.1.1 a.2))| ≤ ε₂) :
    pr _ (realG P₁ P₂ (fun ω o₁ o₂ g₁ g₂ s =>
        Acc ω o₁ o₂ g₁ g₂ s ∧ Fr ω o₁ o₂ g₁ g₂ s ∧ (¬ Rl ω o₁ o₂ g₁ g₂ s ∨ Op ω o₁ o₂ g₁ g₂ s))) ≤
      ε₁ + ε₂ + pr _ (deltaG Sm₁ pg₁ P₂) +
        pr _ (simG Sm₁ pg₁ Sm₂ pg₂ (fun ω o₁ o₂ g₁ g₂ s =>
          Acc ω o₁ o₂ g₁ g₂ s ∧ Fr ω o₁ o₂ g₁ g₂ s ∧ ¬ Rl ω o₁ o₂ g₁ g₂ s)) +
        pr _ (simG Sm₁ pg₁ Sm₂ pg₂ Op) := by
  have h := real_sim_le P₁ Sm₁ pg₁ P₂ Sm₂ pg₂ _ h₁ h₂
  have hs := (pr_mono (α := (Ω × (C₁ × G)) × ((C₂ × G) × S))
    (P := simG Sm₁ pg₁ Sm₂ pg₂ (fun ω o₁ o₂ g₁ g₂ s =>
        Acc ω o₁ o₂ g₁ g₂ s ∧ Fr ω o₁ o₂ g₁ g₂ s ∧ (¬ Rl ω o₁ o₂ g₁ g₂ s ∨ Op ω o₁ o₂ g₁ g₂ s)))
    (Q := fun z => simG Sm₁ pg₁ Sm₂ pg₂ (fun ω o₁ o₂ g₁ g₂ s =>
          Acc ω o₁ o₂ g₁ g₂ s ∧ Fr ω o₁ o₂ g₁ g₂ s ∧ ¬ Rl ω o₁ o₂ g₁ g₂ s) z ∨
        simG Sm₁ pg₁ Sm₂ pg₂ Op z)
    fun z hz => by
      unfold simG at hz ⊢
      rcases hz with ⟨ha, hf, hr | ho⟩
      · exact Or.inl ⟨ha, hf, hr⟩
      · exact Or.inr ho).trans (pr_or_le _ _)
  have := (abs_sub_le_iff.1 h).1
  linarith

end Games

/-! ## Weak simulation-extractability -/

section SE

/-- **Weak simulation-extractability for two simulated proofs** (one of a first relation, one of
a second), with error `ε`, against the adversaries `Adm` admits (for the VOLEitH prover:
bounded reads of the tables).

The adversary has coins `a` (any finite type, uniform). From them it chooses the first statement
`x₁ a` (or none), gets the simulated proof `π₁` (coins `c₁`), chooses the second statement
`x₂ a π₁`, gets `π₂` (coins `c₂`), and then, reading the private tables `g₁`, `g₂` and the shared
tables as both simulations programmed them, outputs `out`. It wins if the output is accepted
(`Acc`), is fresh with respect to the simulated statements it received (`Fresh`, weak: only the
statements count), and the extractor's witness is not one (`¬ Rel`). The extractor `ext` sees
the simulated statements and proofs, the adversary's last stage as a function of the tables (the
queries it makes) and the programmed tables, as in L8's log; it does not see the simulators'
coins. The statements are chosen without reading the tables (as in the zero-knowledge hops of
`Privacy/*RO.lean`); the last stage reads them freely, subject to `Adm`.

The programming order (`prog₁` applied to the tables `prog₂` programmed) is the one the hops of
`real_sim_le` produce. -/
def WeakSE2 {I₁ I₂ P₁ P₂ C₁ C₂ G S Out W : Type*} [Fintype C₁] [Fintype C₂] [Fintype G]
    [Fintype S] (sim₁ : I₁ → C₁ → Option P₁) (prog₁ : I₁ → C₁ → S → S)
    (sim₂ : I₂ → C₂ → Option P₂) (prog₂ : I₂ → C₂ → S → S) (Acc : Out → S → Prop)
    (Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop) (Rel : Out → W → Prop)
    (ext : Option (I₁ × P₁) → Option (I₂ × P₂) → (G → G → S → Out) → G → G → S → W)
    (Adm : (G → G → S → Out) → Prop) (ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [Nonempty α] (x₁ : α → Option I₁) (x₂ : α → Option P₁ → Option I₂)
    (out : α → Option P₁ → Option P₂ → G → G → S → Out),
    (∀ a π₁ π₂, Adm (out a π₁ π₂)) →
    pr ((α × (C₁ × G)) × ((C₂ × G) × S)) (fun z =>
      Acc (out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)
          (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1) z.1.2.2 z.2.1.2
          (progO prog₁ (x₁ z.1.1) z.1.2.1
            (progO prog₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1 z.2.2)))
        (progO prog₁ (x₁ z.1.1) z.1.2.1
          (progO prog₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1 z.2.2)) ∧
      Fresh (pairO (x₁ z.1.1) (simO sim₁ (x₁ z.1.1) z.1.2.1))
        (pairO (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1))
          (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1))
        (out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)
          (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1) z.1.2.2 z.2.1.2
          (progO prog₁ (x₁ z.1.1) z.1.2.1
            (progO prog₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1 z.2.2))) ∧
      ¬ Rel (out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)
          (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1) z.1.2.2 z.2.1.2
          (progO prog₁ (x₁ z.1.1) z.1.2.1
            (progO prog₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1 z.2.2)))
        (ext (pairO (x₁ z.1.1) (simO sim₁ (x₁ z.1.1) z.1.2.1))
          (pairO (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1))
            (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1))
          (out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)
            (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1))
          z.1.2.2 z.2.1.2
          (progO prog₁ (x₁ z.1.1) z.1.2.1
            (progO prog₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1 z.2.2)))) ≤ ε

theorem WeakSE2.mono {I₁ I₂ P₁ P₂ C₁ C₂ G S Out W : Type*} [Fintype C₁] [Fintype C₂] [Fintype G]
    [Fintype S] {sim₁ : I₁ → C₁ → Option P₁} {prog₁ : I₁ → C₁ → S → S}
    {sim₂ : I₂ → C₂ → Option P₂} {prog₂ : I₂ → C₂ → S → S} {Acc : Out → S → Prop}
    {Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop} {Rel : Out → W → Prop}
    {ext : Option (I₁ × P₁) → Option (I₂ × P₂) → (G → G → S → Out) → G → G → S → W}
    {Adm Adm' : (G → G → S → Out) → Prop} {ε ε' : ℝ}
    (h : WeakSE2 sim₁ prog₁ sim₂ prog₂ Acc Fresh Rel ext Adm ε) (hA : ∀ F, Adm' F → Adm F)
    (hε : ε ≤ ε') : WeakSE2 sim₁ prog₁ sim₂ prog₂ Acc Fresh Rel ext Adm' ε' :=
  fun α _ _ x₁ x₂ out hout => (h α x₁ x₂ out fun a π₁ π₂ => hA _ (hout a π₁ π₂)).trans hε

/-- **Non-vacuity**: every pair of simulators is weakly simulation-extractable with error `1`
(a probability), so the hypothesis is satisfiable by the real objects; the content is in `ε`. -/
theorem weakSE2_one {I₁ I₂ P₁ P₂ C₁ C₂ G S Out W : Type*} [Fintype C₁] [Fintype C₂] [Fintype G]
    [Fintype S] (sim₁ : I₁ → C₁ → Option P₁) (prog₁ : I₁ → C₁ → S → S)
    (sim₂ : I₂ → C₂ → Option P₂) (prog₂ : I₂ → C₂ → S → S) (Acc : Out → S → Prop)
    (Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop) (Rel : Out → W → Prop)
    (ext : Option (I₁ × P₁) → Option (I₂ × P₂) → (G → G → S → Out) → G → G → S → W)
    (Adm : (G → G → S → Out) → Prop) :
    WeakSE2 sim₁ prog₁ sim₂ prog₂ Acc Fresh Rel ext Adm 1 :=
  fun _ _ _ _ _ _ _ => pr_le_one _

end SE

end VoleMole.Theft
