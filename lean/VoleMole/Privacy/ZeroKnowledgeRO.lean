import VoleMole.Privacy.Hybrid

/-!
# Zero knowledge with random tables the distinguisher sees, and the hybrid hop that uses it

`Privacy.ZeroKnowledge` (`Privacy/Basic.lean`) compares the prover's output with the simulator's
against distinguishers that see the output only. In the random-oracle and ideal-cipher model the
distinguisher also sees the random tables (and reads them at a bounded number of keys), and the
simulator *programs* some of them. This file is the abstract layer of that notion.

* **`ZeroKnowledgeRO R prove sim prog Adm ε`**: for every instance and witness with `R x w` and
  every admissible distinguisher `D` (`Adm D`; for the executable prover, a bound on the keys at
  which it reads each table, `ZK/ReadsRO.lean`), the real experiment (prover's randomness `ρ`, a
  private table `g` of this proof — its slice of `H₃` — and the shared tables `s`, all uniform)
  and the simulated one (coins `c`, the slice `g`, the shared tables programmed by
  `prog x c s`) are `ε`-close:

      |Pr[D(prove x w ρ g s, g, s)] − Pr[D(sim x c, g, prog x c s)]| ≤ ε.

  The simulated proof is a function of the coins only: everything it owes to the tables is in the
  programming.

* **`hop_ro`**: the hybrid step of a game with several proofs that share the tables. The context
  `γ` (every other part of the game's tape) is fixed; the proofs simulated before have already
  programmed the tables (`L γ`), the real proof of this step reads the programmed tables, and the
  rest of the game is `F γ`. Then replacing this proof by its simulation costs the zero-knowledge
  error of the distinguisher `(o, g, s) ↦ F γ o g (L γ s)` (whose reads are the game's plus those
  of `L γ`), **plus** the probability `δ` that the real proof reads the tables differently with and
  without the earlier programming (`prove … (L γ s) ≠ prove … s`): the earlier simulators
  programmed a point this proof reads. With the programming as `L γ` *after* this proof's, the
  hybrid that follows has the tables `L γ (prog s)`, as `hop_ro`'s right side.
-/

open Finset

namespace VoleMole.Privacy

section RO

variable {I W ρ C G S O : Type*} [Fintype ρ] [Fintype C] [Fintype G] [Fintype S]

/-- **Zero knowledge with random tables.** For every instance `x` and witness `w` with `R x w` and
every admissible distinguisher `D`, the prover's output (randomness `ρ`, its private table `g`, the
shared tables `s`) and the simulator's output (coins `c`, the shared tables programmed by
`prog x c`) are `ε`-close, the distinguisher seeing the tables. -/
def ZeroKnowledgeRO (R : I → W → Prop) (prove : I → W → ρ → G → S → O) (sim : I → C → O)
    (prog : I → C → S → S) (Adm : (O → G → S → Prop) → Prop) (ε : ℝ) : Prop :=
  ∀ x w, R x w → ∀ D, Adm D →
    |pr ((ρ × G) × S) (fun a => D (prove x w a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((C × G) × S) (fun a => D (sim x a.1.1) a.1.2 (prog x a.1.1 a.2))| ≤ ε

theorem ZeroKnowledgeRO.mono {R : I → W → Prop} {prove : I → W → ρ → G → S → O}
    {sim : I → C → O} {prog : I → C → S → S} {Adm Adm' : (O → G → S → Prop) → Prop} {ε ε' : ℝ}
    (h : ZeroKnowledgeRO R prove sim prog Adm ε) (hA : ∀ D, Adm' D → Adm D) (hε : ε ≤ ε') :
    ZeroKnowledgeRO R prove sim prog Adm' ε' :=
  fun x w hxw D hD => le_trans (h x w hxw D (hA D hD)) hε

/-- **`ZeroKnowledgeRO` moves along instance, witness and output maps** (for an admissibility
class closed under the output map). -/
theorem ZeroKnowledgeRO.transfer {I' W' O' : Type*} {R : I → W → Prop} {R' : I' → W' → Prop}
    {prove : I → W → ρ → G → S → O} {sim : I → C → O} {prog : I → C → S → S}
    {Adm : (O → G → S → Prop) → Prop} {Adm' : (O' → G → S → Prop) → Prop} {ε : ℝ}
    (h : ZeroKnowledgeRO R prove sim prog Adm ε) (fI : I' → I) (fW : I' → W' → W)
    (hR : ∀ x w, R' x w → R (fI x) (fW x w)) (φ : O → O')
    (hA : ∀ D, Adm' D → Adm (fun o g s => D (φ o) g s)) :
    ZeroKnowledgeRO R' (fun x w r g s => φ (prove (fI x) (fW x w) r g s))
      (fun x c => φ (sim (fI x) c)) (fun x c => prog (fI x) c) Adm' ε :=
  fun x w hxw D hD => h (fI x) (fW x w) (hR x w hxw) (fun o g s => D (φ o) g s) (hA D hD)

/-- **The hybrid hop with shared, programmed tables.** For every context `γ` let `F γ o g u` be
the rest of the game given this proof's output `o`, its private table `g` and the tables `u` the
game runs on, and `L γ` the earlier simulators' programming. If for every `γ` the real proof on
uniform tables and the simulated one, seen through `(o, g, s) ↦ F γ o g (L γ s)`, are `ε`-close,
then the hybrid where this proof is real **on the programmed tables** `L γ s` and the hybrid where
it is simulated (tables `L γ (prog γ c s)`) are `ε + δ`-close, `δ` the probability that the real
proof's output changes with the earlier programming. -/
theorem hop_ro {Γ : Type*} [Fintype Γ] [Nonempty Γ] (P : Γ → ρ → G → S → O) (Sm : Γ → C → O)
    (prog : Γ → C → S → S) (L : Γ → S → S) (F : Γ → O → G → S → Prop) {ε : ℝ}
    (h : ∀ γ, |pr ((ρ × G) × S) (fun a => F γ (P γ a.1.1 a.1.2 a.2) a.1.2 (L γ a.2)) -
      pr ((C × G) × S) (fun a => F γ (Sm γ a.1.1) a.1.2 (L γ (prog γ a.1.1 a.2)))| ≤ ε) :
    |pr (Γ × ((ρ × G) × S)) (fun z =>
        F z.1 (P z.1 z.2.1.1 z.2.1.2 (L z.1 z.2.2)) z.2.1.2 (L z.1 z.2.2)) -
      pr (Γ × ((C × G) × S)) (fun z =>
        F z.1 (Sm z.1 z.2.1.1) z.2.1.2 (L z.1 (prog z.1 z.2.1.1 z.2.2)))| ≤
      ε + pr (Γ × ((ρ × G) × S)) (fun z =>
        P z.1 z.2.1.1 z.2.1.2 (L z.1 z.2.2) ≠ P z.1 z.2.1.1 z.2.1.2 z.2.2) := by
  have h1 := abs_pr_sub_le_of_agree
    (fun z : Γ × ((ρ × G) × S) => F z.1 (P z.1 z.2.1.1 z.2.1.2 (L z.1 z.2.2)) z.2.1.2 (L z.1 z.2.2))
    (fun z => F z.1 (P z.1 z.2.1.1 z.2.1.2 z.2.2) z.2.1.2 (L z.1 z.2.2))
    (fun z => P z.1 z.2.1.1 z.2.1.2 (L z.1 z.2.2) ≠ P z.1 z.2.1.1 z.2.1.2 z.2.2)
    (fun z hz => by rw [not_not.1 hz])
  have h2 := abs_pr_prod_sub_le
    (fun z : Γ × ((ρ × G) × S) => F z.1 (P z.1 z.2.1.1 z.2.1.2 z.2.2) z.2.1.2 (L z.1 z.2.2))
    (fun z : Γ × ((C × G) × S) => F z.1 (Sm z.1 z.2.1.1) z.2.1.2 (L z.1 (prog z.1 z.2.1.1 z.2.2)))
    fun γ => h γ
  have := abs_sub_le
    (pr (Γ × ((ρ × G) × S)) fun z =>
      F z.1 (P z.1 z.2.1.1 z.2.1.2 (L z.1 z.2.2)) z.2.1.2 (L z.1 z.2.2))
    (pr (Γ × ((ρ × G) × S)) fun z => F z.1 (P z.1 z.2.1.1 z.2.1.2 z.2.2) z.2.1.2 (L z.1 z.2.2))
    (pr (Γ × ((C × G) × S)) fun z =>
      F z.1 (Sm z.1 z.2.1.1) z.2.1.2 (L z.1 (prog z.1 z.2.1.1 z.2.2)))
  linarith

/-- A step where this proof does not run (its output is not read): the two sides are equal. -/
theorem hop_ro_unused [Nonempty ρ] [Nonempty C] (F : G → S → Prop) :
    |pr ((ρ × G) × S) (fun a => F a.1.2 a.2) - pr ((C × G) × S) (fun a => F a.1.2 a.2)| ≤ 0 := by
  have e1 : pr ((ρ × G) × S) (fun a => F a.1.2 a.2) = pr (G × S) (fun a => F a.1 a.2) := by
    rw [← pr_equiv (Equiv.prodAssoc ρ G S).symm]
    exact pr_prod_snd (α := ρ) (fun a : G × S => F a.1 a.2)
  have e2 : pr ((C × G) × S) (fun a => F a.1.2 a.2) = pr (G × S) (fun a => F a.1 a.2) := by
    rw [← pr_equiv (Equiv.prodAssoc C G S).symm]
    exact pr_prod_snd (α := C) (fun a : G × S => F a.1 a.2)
  rw [e1, e2, sub_self, abs_zero]

end RO

end VoleMole.Privacy
