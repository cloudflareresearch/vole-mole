import VoleMole.Privacy.ZeroKnowledgeRO

/-!
# Zero knowledge for statements chosen from the tables, and the hybrid hop that uses it

`ZeroKnowledgeRO` (`Privacy/ZeroKnowledgeRO.lean`) is for a statement fixed before the tables are
drawn. In a privacy game the adversary chooses a later proof's statement after reading the tables
(and the earlier simulated proofs). This file is the abstract layer of the adaptive notion.

* **`ZeroKnowledgeROA R prove sim prog AdmS Adm ε`**: for every type `X` of adversary outputs,
  every admissible table reader `Sx : G × S → X` (`AdmS`; for the executable prover, `S` reads the
  tables at bounded numbers of keys, consistently: `ZK/AdaptRO.lean`'s `SReads`), every choice
  `stw : X → Option (I × W)` of a statement and witness in the relation (or none: then no proof is
  produced and nothing is programmed, the output being a fixed `dummy`), and every admissible
  distinguisher of `Sx`'s output, the output and the tables, the real experiment (fresh `ρ`, the
  tables `(g, s)`) and the simulated one (coins `c`, the shared tables programmed) are `ε`-close.
* **`hop_roA`**: `hop_ro` for a proof whose statement is read off the tables: the context `γ`
  fixes the rest of the tape, the statement-determining output `x = Sx γ (g, s)` is computed from
  the uniform tables, and the earlier simulators' programming `L γ x` may depend on it. The real
  proof of this step runs on the programmed tables; replacing it costs the zero-knowledge error plus
  the collision term `Pr[P γ x ρ g (L γ x s) ≠ P γ x ρ g s]`.
-/

open Finset

namespace VoleMole.Privacy

section RO

variable {I W ρ C G S O : Type*} [Fintype ρ] [Fintype C] [Fintype G] [Fintype S]

/-- The real output: the proof of the chosen statement and witness, or `dummy`. -/
def outReal {X : Type*} (stw : X → Option (I × W)) (prove : I → W → ρ → G → S → O) (dummy : O)
    (x : X) (r : ρ) (g : G) (s : S) : O :=
  (stw x).elim dummy fun iw => prove iw.1 iw.2 r g s

/-- The simulated output: the simulation for the chosen statement, or `dummy`. -/
def outSim {X : Type*} (stw : X → Option (I × W)) (sim : I → C → O) (dummy : O) (x : X) (c : C) : O :=
  (stw x).elim dummy fun iw => sim iw.1 c

/-- The simulator's programming for the chosen statement, or none. -/
def progSim {X : Type*} (stw : X → Option (I × W)) (prog : I → C → S → S) (x : X) (c : C) (s : S) :
    S :=
  (stw x).elim s fun iw => prog iw.1 c s

/-- **Zero knowledge with random tables, for a statement chosen by a table reader.** -/
def ZeroKnowledgeROA (R : I → W → Prop) (prove : I → W → ρ → G → S → O) (sim : I → C → O)
    (prog : I → C → S → S) (AdmS : (X : Type) → (G × S → X) → Prop)
    (Adm : (O → G → S → Prop) → Prop) (ε : ℝ) : Prop :=
  ∀ (X : Type) (Sx : G × S → X) (stw : X → Option (I × W)), AdmS X Sx →
    (∀ x i w, stw x = some (i, w) → R i w) → ∀ (dummy : O) (D : X → O → G → S → Prop),
      (∀ x, Adm (D x)) →
      |pr (ρ × (G × S)) (fun z => D (Sx z.2) (outReal stw prove dummy (Sx z.2) z.1 z.2.1 z.2.2)
          z.2.1 z.2.2) -
        pr (C × (G × S)) (fun z => D (Sx z.2) (outSim stw sim dummy (Sx z.2) z.1) z.2.1
          (progSim stw prog (Sx z.2) z.1 z.2.2))| ≤ ε

theorem ZeroKnowledgeROA.mono {R : I → W → Prop} {prove : I → W → ρ → G → S → O}
    {sim : I → C → O} {prog : I → C → S → S} {AdmS AdmS' : (X : Type) → (G × S → X) → Prop}
    {Adm Adm' : (O → G → S → Prop) → Prop} {ε ε' : ℝ}
    (h : ZeroKnowledgeROA R prove sim prog AdmS Adm ε) (hS : ∀ X Sx, AdmS' X Sx → AdmS X Sx)
    (hA : ∀ D, Adm' D → Adm D) (hε : ε ≤ ε') : ZeroKnowledgeROA R prove sim prog AdmS' Adm' ε' :=
  fun X Sx stw hSx hR dummy D hD =>
    (h X Sx stw (hS X Sx hSx) hR dummy D fun x => hA _ (hD x)).trans hε

/-- **The hybrid hop with a statement read off the tables.** For every context `γ`, `Sx γ` reads
the statement-determining output `x` off the uniform tables `(g, s)`; `L γ x` is the earlier
simulators' programming, `F γ x` the rest of the game. If for every `γ` the real proof on the
uniform tables and the simulated one, seen through `(o, g, s) ↦ F γ x o g (L γ x s)`, are
`ε`-close, then the hybrid where this proof is real **on the programmed tables** and the one where
it is simulated are `ε + δ`-close, `δ` the probability that the real proof's output changes with
the earlier programming. -/
theorem hop_roA {Γ X : Type*} [Fintype Γ] [Nonempty Γ] (Sx : Γ → G × S → X)
    (P : Γ → X → ρ → G → S → O) (Sm : Γ → X → C → O) (prog : Γ → X → C → S → S)
    (L : Γ → X → S → S) (F : Γ → X → O → G → S → Prop) {ε : ℝ}
    (h : ∀ γ, |pr (ρ × (G × S)) (fun a => F γ (Sx γ a.2) (P γ (Sx γ a.2) a.1 a.2.1 a.2.2) a.2.1
        (L γ (Sx γ a.2) a.2.2)) -
      pr (C × (G × S)) (fun a => F γ (Sx γ a.2) (Sm γ (Sx γ a.2) a.1) a.2.1
        (L γ (Sx γ a.2) (prog γ (Sx γ a.2) a.1 a.2.2)))| ≤ ε) :
    |pr (Γ × (ρ × (G × S))) (fun z => F z.1 (Sx z.1 z.2.2)
        (P z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.1 (L z.1 (Sx z.1 z.2.2) z.2.2.2)) z.2.2.1
        (L z.1 (Sx z.1 z.2.2) z.2.2.2)) -
      pr (Γ × (C × (G × S))) (fun z => F z.1 (Sx z.1 z.2.2) (Sm z.1 (Sx z.1 z.2.2) z.2.1) z.2.2.1
        (L z.1 (Sx z.1 z.2.2) (prog z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.2)))| ≤
      ε + pr (Γ × (ρ × (G × S))) (fun z =>
        P z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.1 (L z.1 (Sx z.1 z.2.2) z.2.2.2) ≠
          P z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.1 z.2.2.2) := by
  have h1 := abs_pr_sub_le_of_agree
    (fun z : Γ × (ρ × (G × S)) => F z.1 (Sx z.1 z.2.2)
      (P z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.1 (L z.1 (Sx z.1 z.2.2) z.2.2.2)) z.2.2.1
      (L z.1 (Sx z.1 z.2.2) z.2.2.2))
    (fun z => F z.1 (Sx z.1 z.2.2) (P z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.1 z.2.2.2) z.2.2.1
      (L z.1 (Sx z.1 z.2.2) z.2.2.2))
    (fun z => P z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.1 (L z.1 (Sx z.1 z.2.2) z.2.2.2) ≠
      P z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.1 z.2.2.2)
    (fun z hz => by rw [not_not.1 hz])
  have h2 := abs_pr_prod_sub_le
    (fun z : Γ × (ρ × (G × S)) => F z.1 (Sx z.1 z.2.2) (P z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.1 z.2.2.2)
      z.2.2.1 (L z.1 (Sx z.1 z.2.2) z.2.2.2))
    (fun z : Γ × (C × (G × S)) => F z.1 (Sx z.1 z.2.2) (Sm z.1 (Sx z.1 z.2.2) z.2.1) z.2.2.1
      (L z.1 (Sx z.1 z.2.2) (prog z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.2)))
    fun γ => h γ
  have := abs_sub_le
    (pr (Γ × (ρ × (G × S))) fun z => F z.1 (Sx z.1 z.2.2)
      (P z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.1 (L z.1 (Sx z.1 z.2.2) z.2.2.2)) z.2.2.1
      (L z.1 (Sx z.1 z.2.2) z.2.2.2))
    (pr (Γ × (ρ × (G × S))) fun z => F z.1 (Sx z.1 z.2.2)
      (P z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.1 z.2.2.2) z.2.2.1 (L z.1 (Sx z.1 z.2.2) z.2.2.2))
    (pr (Γ × (C × (G × S))) fun z => F z.1 (Sx z.1 z.2.2) (Sm z.1 (Sx z.1 z.2.2) z.2.1) z.2.2.1
      (L z.1 (Sx z.1 z.2.2) (prog z.1 (Sx z.1 z.2.2) z.2.1 z.2.2.2)))
  linarith

end RO

end VoleMole.Privacy
