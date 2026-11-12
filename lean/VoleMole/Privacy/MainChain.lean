import VoleMole.Privacy.Hybrid

/-!
# The joint hop on `main`: four proofs in sequence, one bad event for all of them

On `main` (no dedicated label rows) one proof is zero-knowledge only up to the probability that the
distinguisher predicts the first 16 witness bytes (`ZK/HopsMain.lean`). In Moussaka and Ratatouille
the token's opening `r` is that prefix for several proofs of the game: a real proof left in the game
helps to predict `r` for the others, so the proofs cannot be replaced one at a time against the
per-proof bound. `security/moussaka.md` §6 replaces them **jointly**: the bad event "some `H₅`
query hits a sibling label of some proof" is evaluated in the hybrid where all proofs are
simulated, where `r` enters only through the commitments. This file is that argument, abstractly,
for a game of four proofs in sequence (each statement may depend on the outputs of the earlier
proofs, as the redemption statements depend on the issuance requests through the adversary's
choices).

## The game (`Game`, `ev`)

A secret `s` (uniform on `S`), and four proof slots. Slot `j` has a statement `σⱼ s o₁ … oⱼ₋₁ :
Option Yⱼ` (`none`: the proof is not run), coins `Aⱼ.K`, an output `Aⱼ.run y k` and an observation
`Aⱼ.obs y k` (what the final event sees of the slot's coins: for the adversary, the random tables).
The event is `Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄`.

* **`hop₁` … `hop₄`**: replacing one slot by another (`Slot.Close`: close on every valid statement
  against every admissible distinguisher of the output and the observation) costs its closeness,
  if the game's event, the other slots fixed, is admissible (`Game.D₁` … `Game.D₄`). These are the
  per-proof hops H1–H4 (to the ideal tape) and the last one (ideal tape to simulator), done one
  proof at a time.

## The joint H6 (`HSlot`, `fill_ideal_le`)

An `HSlot` is a proof on the ideal tape with its sibling answers explicit: tape `c`, sibling answers
`u : ι → R`, its own `H₅` table `g : Kt → R`, other tables `v`; the output `out y c u g v` reads `g`
only at the prover's keys `pk y c` (`out_congr`); the sibling answers sit at the keys `key y c`
(injective). `fillS`: the sibling answers are the table's, `g ∘ key y c` (the prover after H1–H4);
`idealS`: they are the uniform `u` (after H6). Both observe `(y, c, g, v)`.

* `HSlot.stage`: for one slot, `fill` and `ideal` differ by at most the probability that the
  prover's keys or the event's read set `R` contain a sibling key (`abs_pr_hidden_le`: identical
  until a programmed point is read).
* `stage₁` … `stage₄`: the same inside the game, for an event that reads slot `j`'s table only at
  `Rⱼ` (`Congr`).
* **`fill_ideal_le`**: from all slots `fill` to all slots `ideal`, for an event `Φ` whose read sets
  `Rⱼ` are **consistent** (changing table `j` off `Rⱼ` changes neither `Φ` nor any `Rₘ`, `Cons`):

      |Pr[all fill] − Pr[all ideal]| ≤ 15 · Pr_{all ideal}[some slot's sibling key is read]

  (`badAll`). The hops go slot 4, 3, 2, 1; each hop's bad event is measured with the later slots
  ideal and the earlier ones still `fill`, and moved to the all-ideal hybrid through the remaining
  hops, each of which at most doubles it (`pr_badAll_le`): `1 + 2 + 4 + 8 = 15`. The paper's lazy
  sampling would give the factor `1`; the factor is a cost of this proof, which uses only
  `abs_pr_hidden_le`, one table at a time.

Consistency (`Cons`) is what an oracle algorithm's queries satisfy (the set of queries is
determined by the answers to the queries); it is needed because a bad event of one slot is moved
across the hop of another slot. `ZK/HopsMain.lean` instantiates the slots with the executable
prover and turns `badAll` into a prediction of the witness prefixes.
-/

open Finset

namespace VoleMole.Privacy

/-- **Averaging a bound that depends on the shared coordinate**: per-fiber bounds `pr γ (B a ·)`
average to `pr (α × γ) B`. -/
theorem abs_pr_prod_sub_le_pr {α β β' γ : Type*} [Fintype α] [Fintype β] [Fintype β'] [Fintype γ]
    [Nonempty α] (P : α × β → Prop) (Q : α × β' → Prop) (B : α × γ → Prop)
    (h : ∀ a, |pr β (fun b => P (a, b)) - pr β' (fun b => Q (a, b))| ≤ pr γ (fun c => B (a, c))) :
    |pr (α × β) P - pr (α × β') Q| ≤ pr (α × γ) B := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, pr_prod, pr_prod, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hα]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => h a)

/-- The same with the bound on the second coordinate shared. -/
theorem abs_pr_prod_sub_le_pr' {α β β' γ : Type*} [Fintype α] [Fintype β] [Fintype β'] [Fintype γ]
    [Nonempty β] (P : α × β → Prop) (Q : β' × β → Prop) (B : γ × β → Prop)
    (h : ∀ b, |pr α (fun a => P (a, b)) - pr β' (fun a => Q (a, b))| ≤ pr γ (fun c => B (c, b))) :
    |pr (α × β) P - pr (β' × β) Q| ≤ pr (γ × β) B := by
  rw [← pr_equiv (Equiv.prodComm β α), ← pr_equiv (Equiv.prodComm β β'),
    ← pr_equiv (Equiv.prodComm β γ)]
  exact abs_pr_prod_sub_le_pr _ _ _ h

end VoleMole.Privacy

namespace VoleMole.Privacy.MainChain

/-! ## Slots and the game -/

/-- **A proof slot**: coins `K`, the output on a statement, and what the event observes. -/
structure Slot (Y O Ω : Type) where
  K : Type
  [fK : Fintype K]
  [nK : Nonempty K]
  run : Y → K → O
  obs : Option Y → K → Ω

attribute [instance] Slot.fK Slot.nK

/-- The output of a slot on an optional statement. -/
def Slot.out {Y O Ω : Type} (A : Slot Y O Ω) (y : Option Y) (k : A.K) : Option O :=
  y.map (A.run · k)

/-- The slot with its observation mapped. -/
def Slot.mapObs {Y O Ω Ω' : Type} (A : Slot Y O Ω) (f : Ω → Ω') : Slot Y O Ω' where
  K := A.K
  run := A.run
  obs y k := f (A.obs y k)

/-- The slot with another observation of its coins. -/
def Slot.withObs {Y O Ω Ω' : Type} (A : Slot Y O Ω) (f : Option Y → A.K → Ω') : Slot Y O Ω' where
  K := A.K
  run := A.run
  obs := f

/-- **A game of four proofs in sequence**: each statement from the secret and the earlier
outputs. -/
structure Game (S O Y₁ Y₂ Y₃ Y₄ : Type) where
  σ₁ : S → Option Y₁
  σ₂ : S → Option O → Option Y₂
  σ₃ : S → Option O → Option O → Option Y₃
  σ₄ : S → Option O → Option O → Option O → Option Y₄

variable {S O Y₁ Y₂ Y₃ Y₄ Ω₁ Ω₂ Ω₃ Ω₄ : Type}

/-- An event of the game: the secret, the four outputs, the four observations. -/
abbrev Ev (S O Ω₁ Ω₂ Ω₃ Ω₄ : Type) :=
  S → Option O → Option O → Option O → Option O → Ω₁ → Ω₂ → Ω₃ → Ω₄ → Prop

variable (G : Game S O Y₁ Y₂ Y₃ Y₄)

/-- **The game's event** on the tape `(s, k₁, k₂, k₃, k₄)`. -/
def ev (A₁ : Slot Y₁ O Ω₁) (A₂ : Slot Y₂ O Ω₂) (A₃ : Slot Y₃ O Ω₃) (A₄ : Slot Y₄ O Ω₄)
    (Φ : Ev S O Ω₁ Ω₂ Ω₃ Ω₄) (x : S × A₁.K × A₂.K × A₃.K × A₄.K) : Prop :=
  let y₁ := G.σ₁ x.1
  let o₁ := A₁.out y₁ x.2.1
  let y₂ := G.σ₂ x.1 o₁
  let o₂ := A₂.out y₂ x.2.2.1
  let y₃ := G.σ₃ x.1 o₁ o₂
  let o₃ := A₃.out y₃ x.2.2.2.1
  let y₄ := G.σ₄ x.1 o₁ o₂ o₃
  let o₄ := A₄.out y₄ x.2.2.2.2
  Φ x.1 o₁ o₂ o₃ o₄ (A₁.obs y₁ x.2.1) (A₂.obs y₂ x.2.2.1) (A₃.obs y₃ x.2.2.2.1)
    (A₄.obs y₄ x.2.2.2.2)

/-- The event as a function of slot 1's output and observation, the rest fixed. -/
def Game.D₁ (A₂ : Slot Y₂ O Ω₂) (A₃ : Slot Y₃ O Ω₃) (A₄ : Slot Y₄ O Ω₄) (Φ : Ev S O Ω₁ Ω₂ Ω₃ Ω₄)
    (s : S) (k₂ : A₂.K) (k₃ : A₃.K) (k₄ : A₄.K) (o₁ : Option O) (ω₁ : Ω₁) : Prop :=
  let y₂ := G.σ₂ s o₁
  let o₂ := A₂.out y₂ k₂
  let y₃ := G.σ₃ s o₁ o₂
  let o₃ := A₃.out y₃ k₃
  let y₄ := G.σ₄ s o₁ o₂ o₃
  let o₄ := A₄.out y₄ k₄
  Φ s o₁ o₂ o₃ o₄ ω₁ (A₂.obs y₂ k₂) (A₃.obs y₃ k₃) (A₄.obs y₄ k₄)

/-- The event as a function of slot 2's output and observation, the rest fixed. -/
def Game.D₂ (A₁ : Slot Y₁ O Ω₁) (A₃ : Slot Y₃ O Ω₃) (A₄ : Slot Y₄ O Ω₄) (Φ : Ev S O Ω₁ Ω₂ Ω₃ Ω₄)
    (s : S) (k₁ : A₁.K) (k₃ : A₃.K) (k₄ : A₄.K) (o₂ : Option O) (ω₂ : Ω₂) : Prop :=
  let y₁ := G.σ₁ s
  let o₁ := A₁.out y₁ k₁
  let y₃ := G.σ₃ s o₁ o₂
  let o₃ := A₃.out y₃ k₃
  let y₄ := G.σ₄ s o₁ o₂ o₃
  let o₄ := A₄.out y₄ k₄
  Φ s o₁ o₂ o₃ o₄ (A₁.obs y₁ k₁) ω₂ (A₃.obs y₃ k₃) (A₄.obs y₄ k₄)

/-- The event as a function of slot 3's output and observation, the rest fixed. -/
def Game.D₃ (A₁ : Slot Y₁ O Ω₁) (A₂ : Slot Y₂ O Ω₂) (A₄ : Slot Y₄ O Ω₄) (Φ : Ev S O Ω₁ Ω₂ Ω₃ Ω₄)
    (s : S) (k₁ : A₁.K) (k₂ : A₂.K) (k₄ : A₄.K) (o₃ : Option O) (ω₃ : Ω₃) : Prop :=
  let y₁ := G.σ₁ s
  let o₁ := A₁.out y₁ k₁
  let y₂ := G.σ₂ s o₁
  let o₂ := A₂.out y₂ k₂
  let y₄ := G.σ₄ s o₁ o₂ o₃
  let o₄ := A₄.out y₄ k₄
  Φ s o₁ o₂ o₃ o₄ (A₁.obs y₁ k₁) (A₂.obs y₂ k₂) ω₃ (A₄.obs y₄ k₄)

/-- The event as a function of slot 4's output and observation, the rest fixed. -/
def Game.D₄ (A₁ : Slot Y₁ O Ω₁) (A₂ : Slot Y₂ O Ω₂) (A₃ : Slot Y₃ O Ω₃) (Φ : Ev S O Ω₁ Ω₂ Ω₃ Ω₄)
    (s : S) (k₁ : A₁.K) (k₂ : A₂.K) (k₃ : A₃.K) (o₄ : Option O) (ω₄ : Ω₄) : Prop :=
  let y₁ := G.σ₁ s
  let o₁ := A₁.out y₁ k₁
  let y₂ := G.σ₂ s o₁
  let o₂ := A₂.out y₂ k₂
  let y₃ := G.σ₃ s o₁ o₂
  let o₃ := A₃.out y₃ k₃
  Φ s o₁ o₂ o₃ o₄ (A₁.obs y₁ k₁) (A₂.obs y₂ k₂) (A₃.obs y₃ k₃) ω₄

/-- The statement of slot 2, 3, 4 from the earlier coins. -/
def Game.y₂ (A₁ : Slot Y₁ O Ω₁) (s : S) (k₁ : A₁.K) : Option Y₂ := G.σ₂ s (A₁.out (G.σ₁ s) k₁)

def Game.y₃ (A₁ : Slot Y₁ O Ω₁) (A₂ : Slot Y₂ O Ω₂) (s : S) (k₁ : A₁.K) (k₂ : A₂.K) :
    Option Y₃ :=
  G.σ₃ s (A₁.out (G.σ₁ s) k₁) (A₂.out (G.y₂ A₁ s k₁) k₂)

def Game.y₄ (A₁ : Slot Y₁ O Ω₁) (A₂ : Slot Y₂ O Ω₂) (A₃ : Slot Y₃ O Ω₃) (s : S) (k₁ : A₁.K)
    (k₂ : A₂.K) (k₃ : A₃.K) : Option Y₄ :=
  G.σ₄ s (A₁.out (G.σ₁ s) k₁) (A₂.out (G.y₂ A₁ s k₁) k₂) (A₃.out (G.y₃ A₁ A₂ s k₁ k₂) k₃)

/-! ## Replacing one slot -/

/-- **A slot hop**: on every valid statement (or none) and against every admissible distinguisher
of the output and the observation, the slots `A` and `A'` are `ε`-close. -/
def Slot.Close {Y Ω : Type} (Adm : (Option O → Ω → Prop) → Prop) (valid : Y → Prop) (ε : ℝ)
    (A A' : Slot Y O Ω) : Prop :=
  ∀ y : Option Y, (∀ v ∈ y, valid v) → ∀ D, Adm D →
    |pr A.K (fun k => D (A.out y k) (A.obs y k)) - pr A'.K (fun k => D (A'.out y k) (A'.obs y k))| ≤ ε

section Hop

variable [Fintype S] [Nonempty S]

theorem hop₁ {Adm : (Option O → Ω₁ → Prop) → Prop} {valid : Y₁ → Prop} {ε : ℝ}
    {A₁ A₁' : Slot Y₁ O Ω₁} (A₂ : Slot Y₂ O Ω₂) (A₃ : Slot Y₃ O Ω₃) (A₄ : Slot Y₄ O Ω₄)
    (Φ : Ev S O Ω₁ Ω₂ Ω₃ Ω₄) (h : Slot.Close Adm valid ε A₁ A₁')
    (hv : ∀ s, ∀ v ∈ G.σ₁ s, valid v) (hA : ∀ s k₂ k₃ k₄, Adm (G.D₁ A₂ A₃ A₄ Φ s k₂ k₃ k₄)) :
    |pr _ (ev G A₁ A₂ A₃ A₄ Φ) - pr _ (ev G A₁' A₂ A₃ A₄ Φ)| ≤ ε := by
  refine abs_pr_prod_sub_le _ _ fun s => abs_pr_prod_sub_le' _ _ fun r => ?_
  have e : ∀ B : Slot Y₁ O Ω₁, ∀ k : B.K, ev G B A₂ A₃ A₄ Φ (s, k, r) ↔
      G.D₁ A₂ A₃ A₄ Φ s r.1 r.2.1 r.2.2 (B.out (G.σ₁ s) k) (B.obs (G.σ₁ s) k) :=
    fun _ _ => Iff.rfl
  rw [pr_congr (e A₁), pr_congr (e A₁')]
  exact h (G.σ₁ s) (hv s) _ (hA s r.1 r.2.1 r.2.2)

theorem hop₂ {Adm : (Option O → Ω₂ → Prop) → Prop} {valid : Y₂ → Prop} {ε : ℝ}
    (A₁ : Slot Y₁ O Ω₁) {A₂ A₂' : Slot Y₂ O Ω₂} (A₃ : Slot Y₃ O Ω₃) (A₄ : Slot Y₄ O Ω₄)
    (Φ : Ev S O Ω₁ Ω₂ Ω₃ Ω₄) (h : Slot.Close Adm valid ε A₂ A₂')
    (hv : ∀ s o₁, ∀ v ∈ G.σ₂ s o₁, valid v)
    (hA : ∀ s k₁ k₃ k₄, Adm (G.D₂ A₁ A₃ A₄ Φ s k₁ k₃ k₄)) :
    |pr _ (ev G A₁ A₂ A₃ A₄ Φ) - pr _ (ev G A₁ A₂' A₃ A₄ Φ)| ≤ ε := by
  refine abs_pr_prod_sub_le _ _ fun s => abs_pr_prod_sub_le _ _ fun k₁ =>
    abs_pr_prod_sub_le' _ _ fun r => ?_
  have e : ∀ B : Slot Y₂ O Ω₂, ∀ k : B.K, ev G A₁ B A₃ A₄ Φ (s, k₁, k, r) ↔
      G.D₂ A₁ A₃ A₄ Φ s k₁ r.1 r.2 (B.out (G.y₂ A₁ s k₁) k) (B.obs (G.y₂ A₁ s k₁) k) :=
    fun _ _ => Iff.rfl
  rw [pr_congr (e A₂), pr_congr (e A₂')]
  exact h _ (hv s _) _ (hA s k₁ r.1 r.2)

theorem hop₃ {Adm : (Option O → Ω₃ → Prop) → Prop} {valid : Y₃ → Prop} {ε : ℝ}
    (A₁ : Slot Y₁ O Ω₁) (A₂ : Slot Y₂ O Ω₂) {A₃ A₃' : Slot Y₃ O Ω₃} (A₄ : Slot Y₄ O Ω₄)
    (Φ : Ev S O Ω₁ Ω₂ Ω₃ Ω₄) (h : Slot.Close Adm valid ε A₃ A₃')
    (hv : ∀ s o₁ o₂, ∀ v ∈ G.σ₃ s o₁ o₂, valid v)
    (hA : ∀ s k₁ k₂ k₄, Adm (G.D₃ A₁ A₂ A₄ Φ s k₁ k₂ k₄)) :
    |pr _ (ev G A₁ A₂ A₃ A₄ Φ) - pr _ (ev G A₁ A₂ A₃' A₄ Φ)| ≤ ε := by
  refine abs_pr_prod_sub_le _ _ fun s => abs_pr_prod_sub_le _ _ fun k₁ =>
    abs_pr_prod_sub_le _ _ fun k₂ => abs_pr_prod_sub_le' _ _ fun k₄ => ?_
  have e : ∀ B : Slot Y₃ O Ω₃, ∀ k : B.K, ev G A₁ A₂ B A₄ Φ (s, k₁, k₂, k, k₄) ↔
      G.D₃ A₁ A₂ A₄ Φ s k₁ k₂ k₄ (B.out (G.y₃ A₁ A₂ s k₁ k₂) k) (B.obs (G.y₃ A₁ A₂ s k₁ k₂) k) :=
    fun _ _ => Iff.rfl
  rw [pr_congr (e A₃), pr_congr (e A₃')]
  exact h _ (hv s _ _) _ (hA s k₁ k₂ k₄)

theorem hop₄ {Adm : (Option O → Ω₄ → Prop) → Prop} {valid : Y₄ → Prop} {ε : ℝ}
    (A₁ : Slot Y₁ O Ω₁) (A₂ : Slot Y₂ O Ω₂) (A₃ : Slot Y₃ O Ω₃) {A₄ A₄' : Slot Y₄ O Ω₄}
    (Φ : Ev S O Ω₁ Ω₂ Ω₃ Ω₄) (h : Slot.Close Adm valid ε A₄ A₄')
    (hv : ∀ s o₁ o₂ o₃, ∀ v ∈ G.σ₄ s o₁ o₂ o₃, valid v)
    (hA : ∀ s k₁ k₂ k₃, Adm (G.D₄ A₁ A₂ A₃ Φ s k₁ k₂ k₃)) :
    |pr _ (ev G A₁ A₂ A₃ A₄ Φ) - pr _ (ev G A₁ A₂ A₃ A₄' Φ)| ≤ ε := by
  refine abs_pr_prod_sub_le _ _ fun s => abs_pr_prod_sub_le _ _ fun k₁ =>
    abs_pr_prod_sub_le _ _ fun k₂ => abs_pr_prod_sub_le _ _ fun k₃ => ?_
  have e : ∀ B : Slot Y₄ O Ω₄, ∀ k : B.K, ev G A₁ A₂ A₃ B Φ (s, k₁, k₂, k₃, k) ↔
      G.D₄ A₁ A₂ A₃ Φ s k₁ k₂ k₃ (B.out (G.y₄ A₁ A₂ A₃ s k₁ k₂ k₃) k)
        (B.obs (G.y₄ A₁ A₂ A₃ s k₁ k₂ k₃) k) :=
    fun _ _ => Iff.rfl
  rw [pr_congr (e A₄), pr_congr (e A₄')]
  exact h _ (hv s _ _ _) _ (hA s k₁ k₂ k₃)

omit [Nonempty S] in
/-- Events that agree pointwise have the same probability in the game. -/
theorem pr_ev_congr (A₁ : Slot Y₁ O Ω₁) (A₂ : Slot Y₂ O Ω₂) (A₃ : Slot Y₃ O Ω₃)
    (A₄ : Slot Y₄ O Ω₄) {Φ Ψ : Ev S O Ω₁ Ω₂ Ω₃ Ω₄}
    (h : ∀ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄, Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ ↔ Ψ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) :
    pr _ (ev G A₁ A₂ A₃ A₄ Φ) = pr _ (ev G A₁ A₂ A₃ A₄ Ψ) :=
  pr_congr fun _ => h _ _ _ _ _ _ _ _ _

omit [Nonempty S] in
theorem pr_ev_mono (A₁ : Slot Y₁ O Ω₁) (A₂ : Slot Y₂ O Ω₂) (A₃ : Slot Y₃ O Ω₃)
    (A₄ : Slot Y₄ O Ω₄) {Φ Ψ : Ev S O Ω₁ Ω₂ Ω₃ Ω₄}
    (h : ∀ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄, Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ → Ψ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) :
    pr _ (ev G A₁ A₂ A₃ A₄ Φ) ≤ pr _ (ev G A₁ A₂ A₃ A₄ Ψ) :=
  pr_mono fun _ => h _ _ _ _ _ _ _ _ _

omit [Nonempty S] in
/-- **Changing what the event observes**: if the event `Φ` on the slots' observations implies `Ψ`
on other observations of the same coins, the probability can only grow. -/
theorem pr_ev_withObs_mono (A₁ : Slot Y₁ O Ω₁) (A₂ : Slot Y₂ O Ω₂) (A₃ : Slot Y₃ O Ω₃)
    (A₄ : Slot Y₄ O Ω₄) {Ω₁' Ω₂' Ω₃' Ω₄' : Type} (f₁ : Option Y₁ → A₁.K → Ω₁')
    (f₂ : Option Y₂ → A₂.K → Ω₂') (f₃ : Option Y₃ → A₃.K → Ω₃') (f₄ : Option Y₄ → A₄.K → Ω₄')
    (Φ : Ev S O Ω₁ Ω₂ Ω₃ Ω₄) (Ψ : Ev S O Ω₁' Ω₂' Ω₃' Ω₄')
    (h : ∀ s o₁ o₂ o₃ o₄ y₁ k₁ y₂ k₂ y₃ k₃ y₄ k₄,
      Φ s o₁ o₂ o₃ o₄ (A₁.obs y₁ k₁) (A₂.obs y₂ k₂) (A₃.obs y₃ k₃) (A₄.obs y₄ k₄) →
        Ψ s o₁ o₂ o₃ o₄ (f₁ y₁ k₁) (f₂ y₂ k₂) (f₃ y₃ k₃) (f₄ y₄ k₄)) :
    pr _ (ev G A₁ A₂ A₃ A₄ Φ) ≤
      pr _ (ev G (A₁.withObs f₁) (A₂.withObs f₂) (A₃.withObs f₃) (A₄.withObs f₄) Ψ) :=
  pr_mono fun _ hx => h _ _ _ _ _ _ _ _ _ _ _ _ _ hx

end Hop

/-! ## Slots with explicit sibling answers -/

/-- **A proof on the ideal tape with its sibling answers explicit**: tape `C`, sibling answers
`ι → R`, the slot's own `H₅` table `Kt → R` and other tables `V`. The output reads the table only
at the prover's keys `pk` (`out_congr`); the sibling answers are the table's at the injective keys
`key` (in `fillS`). -/
structure HSlot (Y O : Type) where
  C : Type
  ι : Type
  Kt : Type
  V : Type
  R : Type
  [fC : Fintype C]
  [nC : Nonempty C]
  [fι : Fintype ι]
  [nι : Nonempty ι]
  [dι : DecidableEq ι]
  [fKt : Fintype Kt]
  [dKt : DecidableEq Kt]
  [fV : Fintype V]
  [nV : Nonempty V]
  [fR : Fintype R]
  [nR : Nonempty R]
  out : Y → C → (ι → R) → (Kt → R) → V → O
  key : Y → C → ι → Kt
  key_inj : ∀ y c, Function.Injective (key y c)
  pk : Y → C → Finset Kt
  out_congr : ∀ y c u g g' v, (∀ k ∈ pk y c, g k = g' k) → out y c u g v = out y c u g' v

attribute [instance] HSlot.fC HSlot.nC HSlot.fι HSlot.nι HSlot.dι HSlot.fKt HSlot.dKt HSlot.fV
  HSlot.nV HSlot.fR HSlot.nR

namespace HSlot

variable {Y : Type} (H : HSlot Y O)

/-- The coins of an `HSlot`: tape, sibling answers, table, other tables. -/
abbrev Coins := H.C × (H.ι → H.R) × (H.Kt → H.R) × H.V

/-- What the event observes: the statement, the tape, the table, the other tables (not the sibling
answers). -/
abbrev Obs := Option Y × (H.C × (H.Kt → H.R) × H.V)

/-- The observation of the coins. -/
def obsOf (y : Option Y) (k : H.Coins) : H.Obs := (y, (k.1, k.2.2.1, k.2.2.2))

/-- **The prover with the sibling answers from the table** (before H6). -/
def fillS : Slot Y O H.Obs where
  K := H.Coins
  run y k := H.out y k.1 (k.2.2.1 ∘ H.key y k.1) k.2.2.1 k.2.2.2
  obs := H.obsOf

/-- **The prover with uniform sibling answers** (after H6). -/
def idealS : Slot Y O H.Obs where
  K := H.Coins
  run y k := H.out y k.1 k.2.1 k.2.2.1 k.2.2.2
  obs := H.obsOf

lemma fillS_out (y : Y) (k : H.Coins) :
    H.fillS.out (some y) k = some (H.out y k.1 (k.2.2.1 ∘ H.key y k.1) k.2.2.1 k.2.2.2) := rfl

lemma idealS_out (y : Y) (k : H.Coins) :
    H.idealS.out (some y) k = some (H.out y k.1 k.2.1 k.2.2.1 k.2.2.2) := rfl

/-- **The bad event of a slot**: a statement was proved and one of its sibling keys is among the
prover's keys or the read set `Rs`. -/
def bad (Rs : Finset H.Kt) (ω : H.Obs) : Prop :=
  match ω with
  | (some y, (c, _, _)) => ∃ i, H.key y c i ∈ H.pk y c ∨ H.key y c i ∈ Rs
  | (none, _) => False

lemma bad_obsOf_some (Rs : Finset H.Kt) (y : Y) (k : H.Coins) :
    H.bad Rs (H.obsOf (some y) k) ↔ ∃ i, H.key y k.1 i ∈ H.pk y k.1 ∨ H.key y k.1 i ∈ Rs := Iff.rfl

lemma not_bad_obsOf_none (Rs : Finset H.Kt) (k : H.Coins) : ¬ H.bad Rs (H.obsOf none k) := id

/-- The observation with the table replaced. -/
def setTab (ω : H.Obs) (g : H.Kt → H.R) : H.Obs := (ω.1, (ω.2.1, g, ω.2.2.2))

/-- An event of `(o, ω)` reads the table only at `Rs o ω`. -/
def Reads (D : Option O → H.Obs → Prop) (Rs : Option O → H.Obs → Finset H.Kt) : Prop :=
  ∀ o ω g', (∀ k ∈ Rs o ω, ω.2.2.1 k = g' k) → (D o (H.setTab ω g') ↔ D o ω)

lemma abs_pr_hidden_one {K ι R : Type} [Fintype K] [DecidableEq K] [Fintype R] [Nonempty R]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] {x : ι → K} (hx : Function.Injective x)
    (A : (ι → R) → (K → R) → Prop) (Q : (ι → R) → (K → R) → Finset K)
    (hQ : ∀ u g g', (∀ k ∈ Q u g, g k = g' k) → (A u g ↔ A u g')) :
    |pr (K → R) (fun g => A (g ∘ x) g) - pr ((K → R) × (ι → R)) (fun p => A p.2 p.1)| ≤
      pr ((K → R) × (ι → R)) (fun p => ∃ i, x i ∈ Q p.2 p.1) := by
  have h := abs_pr_hidden_le (C := Unit) (x := fun _ => x) (fun _ => hx) (fun _ u g => A u g)
    (fun _ u g => Q u g) (fun _ u g g' h => hQ u g g' h)
  rw [pr_prod_snd (α := Unit) (fun g => A (g ∘ x) g),
    pr_prod_snd (α := Unit) (fun p : (K → R) × (ι → R) => A p.2 p.1),
    pr_prod_snd (α := Unit) (fun p : (K → R) × (ι → R) => ∃ i, x i ∈ Q p.2 p.1)] at h
  exact h

/-- **One slot, fill against ideal.** For an event `D` of the output and the observation that reads
the table only at `Rs` (and the output reads it at `pk`), the two differ by the probability that a
sibling key is among them, in the ideal slot. -/
theorem stage (y : Option Y) (D : Option O → H.Obs → Prop) (Rs : Option O → H.Obs → Finset H.Kt)
    (hD : H.Reads D Rs) :
    |pr H.Coins (fun k => D (H.fillS.out y k) (H.fillS.obs y k)) -
        pr H.Coins (fun k => D (H.idealS.out y k) (H.idealS.obs y k))| ≤
      pr H.Coins (fun k => H.bad (Rs (H.idealS.out y k) (H.idealS.obs y k)) (H.idealS.obs y k)) := by
  rcases y with _ | y
  · exact (abs_nonpos_iff.2 (sub_eq_zero.2 rfl)).trans (pr_nonneg _)
  -- Regroup the coins as (tape, other tables) and (table, sibling answers).
  let e : (H.C × H.V) × ((H.Kt → H.R) × (H.ι → H.R)) ≃ H.Coins :=
    { toFun := fun p => (p.1.1, p.2.2, p.2.1, p.1.2)
      invFun := fun k => ((k.1, k.2.2.2), (k.2.2.1, k.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e, ← pr_equiv e, ← pr_equiv e]
  refine abs_pr_prod_sub_le_pr _ _ _ fun cv => ?_
  obtain ⟨c, v⟩ := cv
  let A : (H.ι → H.R) → (H.Kt → H.R) → Prop := fun u g =>
    D (some (H.out y c u g v)) (some y, (c, g, v))
  let Q : (H.ι → H.R) → (H.Kt → H.R) → Finset H.Kt := fun u g =>
    H.pk y c ∪ Rs (some (H.out y c u g v)) (some y, (c, g, v))
  have hQ : ∀ u g g', (∀ k ∈ Q u g, g k = g' k) → (A u g ↔ A u g') := by
    intro u g g' hg
    have ho : H.out y c u g v = H.out y c u g' v :=
      H.out_congr y c u g g' v fun k hk => hg k (Finset.mem_union_left _ hk)
    show D _ _ ↔ D _ _
    rw [← ho]
    exact (hD (some (H.out y c u g v)) (some y, (c, g, v)) g' fun k hk =>
      hg k (Finset.mem_union_right _ hk)).symm
  have h := abs_pr_hidden_one (H.key_inj y c) A Q hQ
  rw [← pr_prod_fst (β := H.ι → H.R) (fun g => A (g ∘ H.key y c) g)] at h
  refine h.trans (le_of_eq (pr_congr fun x => ?_))
  simp only [Q, Finset.mem_union]
  rfl

end HSlot

/-! ## The H6 hop inside the game, one slot at a time -/

section Stage

variable [Fintype S] [Nonempty S]

/-- The read set of an event on slot `j`'s table, as a function of the whole game's data. -/
abbrev RSet (S O Ω₁ Ω₂ Ω₃ Ω₄ K : Type) :=
  S → Option O → Option O → Option O → Option O → Ω₁ → Ω₂ → Ω₃ → Ω₄ → Finset K

theorem stage₄ (A₁ : Slot Y₁ O Ω₁) (A₂ : Slot Y₂ O Ω₂) (A₃ : Slot Y₃ O Ω₃) (H : HSlot Y₄ O)
    (Φ : Ev S O Ω₁ Ω₂ Ω₃ H.Obs) (R : RSet S O Ω₁ Ω₂ Ω₃ H.Obs H.Kt)
    (hΦ : ∀ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g', (∀ k ∈ R s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄, ω₄.2.2.1 k = g' k) →
      (Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ (H.setTab ω₄ g') ↔ Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄)) :
    |pr _ (ev G A₁ A₂ A₃ H.fillS Φ) - pr _ (ev G A₁ A₂ A₃ H.idealS Φ)| ≤
      pr _ (ev G A₁ A₂ A₃ H.idealS fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ =>
        H.bad (R s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) ω₄) := by
  refine abs_pr_prod_sub_le_pr _ _ _ fun s => abs_pr_prod_sub_le_pr _ _ _ fun k₁ =>
    abs_pr_prod_sub_le_pr _ _ _ fun k₂ => abs_pr_prod_sub_le_pr _ _ _ fun k₃ => ?_
  let y := G.y₄ A₁ A₂ A₃ s k₁ k₂ k₃
  let o₁ := A₁.out (G.σ₁ s) k₁
  let o₂ := A₂.out (G.y₂ A₁ s k₁) k₂
  let o₃ := A₃.out (G.y₃ A₁ A₂ s k₁ k₂) k₃
  let ω₁ := A₁.obs (G.σ₁ s) k₁
  let ω₂ := A₂.obs (G.y₂ A₁ s k₁) k₂
  let ω₃ := A₃.obs (G.y₃ A₁ A₂ s k₁ k₂) k₃
  exact H.stage y (fun o ω => Φ s o₁ o₂ o₃ o ω₁ ω₂ ω₃ ω) (fun o ω => R s o₁ o₂ o₃ o ω₁ ω₂ ω₃ ω)
    fun o ω g' hg => hΦ s o₁ o₂ o₃ o ω₁ ω₂ ω₃ ω g' hg

theorem stage₃ (A₁ : Slot Y₁ O Ω₁) (A₂ : Slot Y₂ O Ω₂) (H : HSlot Y₃ O) (A₄ : Slot Y₄ O Ω₄)
    (Φ : Ev S O Ω₁ Ω₂ H.Obs Ω₄) (R : RSet S O Ω₁ Ω₂ H.Obs Ω₄ H.Kt)
    (hΦ : ∀ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g', (∀ k ∈ R s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄, ω₃.2.2.1 k = g' k) →
      (Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ (H.setTab ω₃ g') ω₄ ↔ Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄)) :
    |pr _ (ev G A₁ A₂ H.fillS A₄ Φ) - pr _ (ev G A₁ A₂ H.idealS A₄ Φ)| ≤
      pr _ (ev G A₁ A₂ H.idealS A₄ fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ =>
        H.bad (R s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) ω₃) := by
  refine abs_pr_prod_sub_le_pr _ _ _ fun s => abs_pr_prod_sub_le_pr _ _ _ fun k₁ =>
    abs_pr_prod_sub_le_pr _ _ _ fun k₂ => abs_pr_prod_sub_le_pr' _ _ _ fun k₄ => ?_
  let y := G.y₃ A₁ A₂ s k₁ k₂
  let o₁ := A₁.out (G.σ₁ s) k₁
  let o₂ := A₂.out (G.y₂ A₁ s k₁) k₂
  let ω₁ := A₁.obs (G.σ₁ s) k₁
  let ω₂ := A₂.obs (G.y₂ A₁ s k₁) k₂
  exact H.stage y (fun o ω => Φ s o₁ o₂ o (A₄.out (G.σ₄ s o₁ o₂ o) k₄) ω₁ ω₂ ω
      (A₄.obs (G.σ₄ s o₁ o₂ o) k₄))
    (fun o ω => R s o₁ o₂ o (A₄.out (G.σ₄ s o₁ o₂ o) k₄) ω₁ ω₂ ω (A₄.obs (G.σ₄ s o₁ o₂ o) k₄))
    fun o ω g' hg => hΦ s o₁ o₂ o _ ω₁ ω₂ ω _ g' hg

theorem stage₂ (A₁ : Slot Y₁ O Ω₁) (H : HSlot Y₂ O) (A₃ : Slot Y₃ O Ω₃) (A₄ : Slot Y₄ O Ω₄)
    (Φ : Ev S O Ω₁ H.Obs Ω₃ Ω₄) (R : RSet S O Ω₁ H.Obs Ω₃ Ω₄ H.Kt)
    (hΦ : ∀ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g', (∀ k ∈ R s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄, ω₂.2.2.1 k = g' k) →
      (Φ s o₁ o₂ o₃ o₄ ω₁ (H.setTab ω₂ g') ω₃ ω₄ ↔ Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄)) :
    |pr _ (ev G A₁ H.fillS A₃ A₄ Φ) - pr _ (ev G A₁ H.idealS A₃ A₄ Φ)| ≤
      pr _ (ev G A₁ H.idealS A₃ A₄ fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ =>
        H.bad (R s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) ω₂) := by
  refine abs_pr_prod_sub_le_pr _ _ _ fun s => abs_pr_prod_sub_le_pr _ _ _ fun k₁ =>
    abs_pr_prod_sub_le_pr' _ _ _ fun r => ?_
  let y := G.y₂ A₁ s k₁
  let o₁ := A₁.out (G.σ₁ s) k₁
  let ω₁ := A₁.obs (G.σ₁ s) k₁
  exact H.stage y (fun o ω => Φ s o₁ o (A₃.out (G.σ₃ s o₁ o) r.1)
      (A₄.out (G.σ₄ s o₁ o (A₃.out (G.σ₃ s o₁ o) r.1)) r.2) ω₁ ω (A₃.obs (G.σ₃ s o₁ o) r.1)
      (A₄.obs (G.σ₄ s o₁ o (A₃.out (G.σ₃ s o₁ o) r.1)) r.2))
    (fun o ω => R s o₁ o (A₃.out (G.σ₃ s o₁ o) r.1)
      (A₄.out (G.σ₄ s o₁ o (A₃.out (G.σ₃ s o₁ o) r.1)) r.2) ω₁ ω (A₃.obs (G.σ₃ s o₁ o) r.1)
      (A₄.obs (G.σ₄ s o₁ o (A₃.out (G.σ₃ s o₁ o) r.1)) r.2))
    fun o ω g' hg => hΦ s o₁ o _ _ ω₁ ω _ _ g' hg

theorem stage₁ (H : HSlot Y₁ O) (A₂ : Slot Y₂ O Ω₂) (A₃ : Slot Y₃ O Ω₃) (A₄ : Slot Y₄ O Ω₄)
    (Φ : Ev S O H.Obs Ω₂ Ω₃ Ω₄) (R : RSet S O H.Obs Ω₂ Ω₃ Ω₄ H.Kt)
    (hΦ : ∀ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g', (∀ k ∈ R s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄, ω₁.2.2.1 k = g' k) →
      (Φ s o₁ o₂ o₃ o₄ (H.setTab ω₁ g') ω₂ ω₃ ω₄ ↔ Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄)) :
    |pr _ (ev G H.fillS A₂ A₃ A₄ Φ) - pr _ (ev G H.idealS A₂ A₃ A₄ Φ)| ≤
      pr _ (ev G H.idealS A₂ A₃ A₄ fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ =>
        H.bad (R s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) ω₁) := by
  refine abs_pr_prod_sub_le_pr _ _ _ fun s => abs_pr_prod_sub_le_pr' _ _ _ fun r => ?_
  let y := G.σ₁ s
  let f₂ : Option O → Option O := fun o => A₂.out (G.σ₂ s o) r.1
  let f₃ : Option O → Option O := fun o => A₃.out (G.σ₃ s o (f₂ o)) r.2.1
  let f₄ : Option O → Option O := fun o => A₄.out (G.σ₄ s o (f₂ o) (f₃ o)) r.2.2
  let w₂ : Option O → Ω₂ := fun o => A₂.obs (G.σ₂ s o) r.1
  let w₃ : Option O → Ω₃ := fun o => A₃.obs (G.σ₃ s o (f₂ o)) r.2.1
  let w₄ : Option O → Ω₄ := fun o => A₄.obs (G.σ₄ s o (f₂ o) (f₃ o)) r.2.2
  exact H.stage y (fun o ω => Φ s o (f₂ o) (f₃ o) (f₄ o) ω (w₂ o) (w₃ o) (w₄ o))
    (fun o ω => R s o (f₂ o) (f₃ o) (f₄ o) ω (w₂ o) (w₃ o) (w₄ o))
    fun o ω g' hg => hΦ s o _ _ _ ω _ _ _ g' hg

end Stage

/-! ## All four slots: one bad event, in the all-ideal hybrid -/

section All

variable [Fintype S] [Nonempty S] (H₁ : HSlot Y₁ O) (H₂ : HSlot Y₂ O) (H₃ : HSlot Y₃ O)
  (H₄ : HSlot Y₄ O)

/-- **The read sets of the event on the four tables.** -/
structure RSets where
  r₁ : RSet S O H₁.Obs H₂.Obs H₃.Obs H₄.Obs H₁.Kt
  r₂ : RSet S O H₁.Obs H₂.Obs H₃.Obs H₄.Obs H₂.Kt
  r₃ : RSet S O H₁.Obs H₂.Obs H₃.Obs H₄.Obs H₃.Kt
  r₄ : RSet S O H₁.Obs H₂.Obs H₃.Obs H₄.Obs H₄.Kt

variable {H₁ H₂ H₃ H₄}

/-- All four read sets at once (for consistency). -/
def RSets.at (R : RSets (S := S) (O := O) H₁ H₂ H₃ H₄) (s : S) (o₁ o₂ o₃ o₄ : Option O)
    (ω₁ : H₁.Obs) (ω₂ : H₂.Obs) (ω₃ : H₃.Obs) (ω₄ : H₄.Obs) :
    Finset H₁.Kt × Finset H₂.Kt × Finset H₃.Kt × Finset H₄.Kt :=
  (R.r₁ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄, R.r₂ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄, R.r₃ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄,
    R.r₄ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄)

/-- **Consistent read sets** for the event `Φ`: changing table `j` off its read set `R.rⱼ`
changes neither `Φ` nor any read set (the queries of an oracle algorithm are determined by the
answers to them). -/
structure Cons (Φ : Ev S O H₁.Obs H₂.Obs H₃.Obs H₄.Obs) (R : RSets (S := S) (O := O) H₁ H₂ H₃ H₄) :
    Prop where
  c₁ : ∀ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g', (∀ k ∈ R.r₁ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄, ω₁.2.2.1 k = g' k) →
    (Φ s o₁ o₂ o₃ o₄ (H₁.setTab ω₁ g') ω₂ ω₃ ω₄ ↔ Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) ∧
      R.at s o₁ o₂ o₃ o₄ (H₁.setTab ω₁ g') ω₂ ω₃ ω₄ = R.at s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄
  c₂ : ∀ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g', (∀ k ∈ R.r₂ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄, ω₂.2.2.1 k = g' k) →
    (Φ s o₁ o₂ o₃ o₄ ω₁ (H₂.setTab ω₂ g') ω₃ ω₄ ↔ Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) ∧
      R.at s o₁ o₂ o₃ o₄ ω₁ (H₂.setTab ω₂ g') ω₃ ω₄ = R.at s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄
  c₃ : ∀ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g', (∀ k ∈ R.r₃ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄, ω₃.2.2.1 k = g' k) →
    (Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ (H₃.setTab ω₃ g') ω₄ ↔ Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) ∧
      R.at s o₁ o₂ o₃ o₄ ω₁ ω₂ (H₃.setTab ω₃ g') ω₄ = R.at s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄
  c₄ : ∀ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g', (∀ k ∈ R.r₄ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄, ω₄.2.2.1 k = g' k) →
    (Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ (H₄.setTab ω₄ g') ↔ Φ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) ∧
      R.at s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ (H₄.setTab ω₄ g') = R.at s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄

/-- **The bad event of the game**: some slot proved a statement and one of its sibling keys is read
(by its prover or by the event). -/
def badAll (R : RSets (S := S) (O := O) H₁ H₂ H₃ H₄) : Ev S O H₁.Obs H₂.Obs H₃.Obs H₄.Obs :=
  fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ =>
    H₁.bad (R.r₁ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) ω₁ ∨ H₂.bad (R.r₂ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) ω₂ ∨
      H₃.bad (R.r₃ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) ω₃ ∨ H₄.bad (R.r₄ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄) ω₄

lemma HSlot.bad_setTab {Y : Type} (H : HSlot Y O) (Rs : Finset H.Kt) (ω : H.Obs) (g' : H.Kt → H.R) :
    H.bad Rs (H.setTab ω g') ↔ H.bad Rs ω := by
  obtain ⟨_ | y, c, g, v⟩ := ω <;> exact Iff.rfl

omit [Fintype S] [Nonempty S] in
/-- The consistency of the read sets makes the bad event consistent too. -/
lemma Cons.bad {Φ : Ev S O H₁.Obs H₂.Obs H₃.Obs H₄.Obs} {R : RSets (S := S) (O := O) H₁ H₂ H₃ H₄}
    (h : Cons Φ R) : Cons (badAll R) R := by
  refine ⟨fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg => ?_, fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg => ?_,
    fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg => ?_, fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg => ?_⟩
  · have e := (h.c₁ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg).2
    simp only [RSets.at, Prod.mk.injEq] at e
    refine ⟨?_, (h.c₁ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg).2⟩
    unfold badAll
    rw [e.1, e.2.1, e.2.2.1, e.2.2.2, HSlot.bad_setTab]
  · have e := (h.c₂ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg).2
    simp only [RSets.at, Prod.mk.injEq] at e
    refine ⟨?_, (h.c₂ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg).2⟩
    unfold badAll
    rw [e.1, e.2.1, e.2.2.1, e.2.2.2, HSlot.bad_setTab]
  · have e := (h.c₃ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg).2
    simp only [RSets.at, Prod.mk.injEq] at e
    refine ⟨?_, (h.c₃ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg).2⟩
    unfold badAll
    rw [e.1, e.2.1, e.2.2.1, e.2.2.2, HSlot.bad_setTab]
  · have e := (h.c₄ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg).2
    simp only [RSets.at, Prod.mk.injEq] at e
    refine ⟨?_, (h.c₄ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg).2⟩
    unfold badAll
    rw [e.1, e.2.1, e.2.2.1, e.2.2.2, HSlot.bad_setTab]

/-- The hybrid with slots `1 … j` filled and the others ideal. -/
noncomputable abbrev W (G : Game S O Y₁ Y₂ Y₃ Y₄) (b₁ b₂ b₃ b₄ : Bool) (Φ : Ev S O H₁.Obs H₂.Obs H₃.Obs H₄.Obs) :
    ℝ :=
  pr _ (ev G (bif b₁ then H₁.fillS else H₁.idealS) (bif b₂ then H₂.fillS else H₂.idealS)
    (bif b₃ then H₃.fillS else H₃.idealS) (bif b₄ then H₄.fillS else H₄.idealS) Φ)

variable {Φ : Ev S O H₁.Obs H₂.Obs H₃.Obs H₄.Obs} {R : RSets (S := S) (O := O) H₁ H₂ H₃ H₄}

/-- **The H6 hop for all four slots at once.** If the event's read sets are consistent, the
all-fill and the all-ideal hybrids differ by at most `15·Pr[badAll]` in the all-ideal hybrid. -/
theorem fill_ideal_le (hc : Cons Φ R) :
    |W G true true true true Φ - W G false false false false Φ| ≤
      15 * W G false false false false (badAll R) := by
  have hb := hc.bad
  -- The four hops, for any consistent event `Ψ`.
  have s4 : ∀ Ψ, Cons Ψ R → |W G true true true true Ψ - W G true true true false Ψ| ≤
      W G true true true false (badAll R) := fun Ψ h =>
    (stage₄ G H₁.fillS H₂.fillS H₃.fillS H₄ Ψ R.r₄ fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg =>
      (h.c₄ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg).1).trans
      (pr_ev_mono G _ _ _ _ fun _ _ _ _ _ _ _ _ _ h => Or.inr (Or.inr (Or.inr h)))
  have s3 : ∀ Ψ, Cons Ψ R → |W G true true true false Ψ - W G true true false false Ψ| ≤
      W G true true false false (badAll R) := fun Ψ h =>
    (stage₃ G H₁.fillS H₂.fillS H₃ H₄.idealS Ψ R.r₃ fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg =>
      (h.c₃ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg).1).trans
      (pr_ev_mono G _ _ _ _ fun _ _ _ _ _ _ _ _ _ h => Or.inr (Or.inr (Or.inl h)))
  have s2 : ∀ Ψ, Cons Ψ R → |W G true true false false Ψ - W G true false false false Ψ| ≤
      W G true false false false (badAll R) := fun Ψ h =>
    (stage₂ G H₁.fillS H₂ H₃.idealS H₄.idealS Ψ R.r₂ fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg =>
      (h.c₂ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg).1).trans
      (pr_ev_mono G _ _ _ _ fun _ _ _ _ _ _ _ _ _ h => Or.inr (Or.inl h))
  have s1 : ∀ Ψ, Cons Ψ R → |W G true false false false Ψ - W G false false false false Ψ| ≤
      W G false false false false (badAll R) := fun Ψ h =>
    (stage₁ G H₁ H₂.idealS H₃.idealS H₄.idealS Ψ R.r₁ fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg =>
      (h.c₁ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g' hg).1).trans
      (pr_ev_mono G _ _ _ _ fun _ _ _ _ _ _ _ _ _ h => Or.inl h)
  -- The bad event, moved to the all-ideal hybrid: each hop at most doubles it.
  set β := W G false false false false (badAll R)
  have b1 : W G true false false false (badAll R) ≤ 2 * β := by
    have := s1 _ hb; have := abs_sub_le_iff.1 this; linarith
  have b2 : W G true true false false (badAll R) ≤ 4 * β := by
    have := s2 _ hb; have := abs_sub_le_iff.1 this; linarith
  have b3 : W G true true true false (badAll R) ≤ 8 * β := by
    have := s3 _ hb; have := abs_sub_le_iff.1 this; linarith
  have h4 := s4 Φ hc
  have h3 := s3 Φ hc
  have h2 := s2 Φ hc
  have h1 := s1 Φ hc
  have := abs_sub_le (W G true true true true Φ) (W G true true true false Φ)
    (W G false false false false Φ)
  have := abs_sub_le (W G true true true false Φ) (W G true true false false Φ)
    (W G false false false false Φ)
  have := abs_sub_le (W G true true false false Φ) (W G true false false false Φ)
    (W G false false false false Φ)
  linarith

end All

end VoleMole.Privacy.MainChain
