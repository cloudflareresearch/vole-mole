import VoleMole.Theft.ManyPlain
import VoleMole.Theft.Reads

/-!
# Read budgets of the hops of a game with many honest proofs

The many-token theft theorems with the Lean prover (`noRedirectN_lean`, `nmUN_lean`,
`noTheftN_lean`) assume that the distinguisher of every zero-knowledge hop has a read budget
(`ZK.Sim.Budget`). Here that is proved, for the generic game of `Theft/Many.lean` on the tables of
the zero-knowledge model (`Tab3` slices, shared tables `ShG R p`), from budgets of its parts, as
`Theft/Reads.lean` does for two proofs.

* **`StageBudgetN F q₃ q₅ q_E`**: a last stage `F g s` (the `N` proofs' `H₃` slices and the shared
  tables) reads each slice at `q₃` keys (the other slices and the tables fixed), `H₅` at `q₅` and
  the cipher at `q_E` keys. `StageBudgetN.event`: an event of a last stage, an extractor and a
  verifier on the stage's output reads the sum. `StageBudgetN.comp_prog`: a last stage after a
  programming.
* **`realFrom_rd5`**, **`realFrom_rdE`**: `m` real proofs in sequence, each reading `a` keys, and
  then a reader of `b` keys, read `m·a + b` keys.
* **`simPre_isProg`**: the composition of `n` programmings, each reading `(a, b)`, is a
  programming that reads `(n·a, n·b)`. `IsProgs.isProg` is the same for `IsProgs`.
* **`distN_budget`**: the distinguisher of hop `i` (`distN`: the `N − i − 1` later proofs real,
  then the event, on the tables the first `i` simulations programmed) has the budget

      (q₃,  (N − i − 1)·s₅ + q₅ + i·m₅,  (N − i − 1)·s_E + q_E + i·m_E)

  if a real slot reads `(s₅, s_E)`, a programming `(m₅, m_E)` and the event `(q₃, q₅, q_E)`.
* Slots of two proof systems (`sumProve`, `sumProveO`, `sumProg`) read what the two systems read.
-/

open Finset

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier

/-! ## Budgets of a last stage with `N` slices -/

section Stage

variable {R : Type} {p : Params} {N : ℕ} {X Y W : Type*}

/-- **The read budget of a last stage** `F g s`: each `H₃` slice at `q3` keys, `H₅` at `q5`, the
cipher at `qE` keys, the other arguments fixed. -/
structure StageBudgetN (F : (Fin N → Tab3) → ShG R p → X) (q3 q5 qE : ℕ) : Prop where
  h3 : ∀ (g : Fin N → Tab3) (j : Fin N) (s : ShG R p),
    Rd3 (fun t => F (Function.update g j t) s) q3
  h5 : ∀ g, Rd5 (F g) q5
  hE : ∀ g, RdE (F g) qE

/-- A constant last stage reads nothing. -/
lemma StageBudgetN.const (x : X) :
    StageBudgetN (R := R) (p := p) (N := N) (fun _ _ => x) 0 0 0 :=
  ⟨fun _ _ _ => Rd3.const x, fun _ => Rd5.const x, fun _ => RdE.const x⟩

lemma StageBudgetN.mono {F : (Fin N → Tab3) → ShG R p → X} {q3 q5 qE q3' q5' qE' : ℕ}
    (h : StageBudgetN F q3 q5 qE) (h3 : q3 ≤ q3') (h5 : q5 ≤ q5') (hE : qE ≤ qE') :
    StageBudgetN F q3' q5' qE' :=
  ⟨fun g j s => (h.h3 g j s).mono h3, fun g => (h.h5 g).mono h5, fun g => (h.hE g).mono hE⟩

/-- **An event of a last stage `F`, an extractor `E` and a verifier `V` on `F`'s output** reads
what the three read. -/
theorem StageBudgetN.event {F : (Fin N → Tab3) → ShG R p → X} {E : (Fin N → Tab3) → ShG R p → W}
    {V : X → ShG R p → Y} {a3 a5 aE x3 x5 xE v5 vE : ℕ} (Φ : X → W → Y → Prop)
    (hF : StageBudgetN F a3 a5 aE) (hE : StageBudgetN E x3 x5 xE)
    (hV5 : ∀ o, Rd5 (V o) v5) (hVE : ∀ o, RdE (V o) vE) :
    StageBudgetN (fun g s => Φ (F g s) (E g s) (V (F g s) s))
      (a3 + x3) (a5 + (x5 + v5)) (aE + (xE + vE)) where
  h3 g j s := (hF.h3 g j s).bind (f := fun o t => Φ o (E (Function.update g j t) s) (V o s))
    fun o => (hE.h3 g j s).map fun w => Φ o w (V o s)
  h5 g := (hF.h5 g).bind (f := fun o s => Φ o (E g s) (V o s))
    fun o => (hE.h5 g).bind (f := fun w s => Φ o w (V o s)) fun w => (hV5 o).map (Φ o w)
  hE g := (hF.hE g).bind (f := fun o s => Φ o (E g s) (V o s))
    fun o => (hE.hE g).bind (f := fun w s => Φ o w (V o s)) fun w => (hVE o).map (Φ o w)

/-- **A last stage after a programming** reads what it reads and what the programming reads. -/
lemma StageBudgetN.comp_prog {F : (Fin N → Tab3) → ShG R p → X} {L : ShG R p → ShG R p}
    {q3 q5 qE m5 mE : ℕ} (h : StageBudgetN F q3 q5 qE) (hL : IsProg L m5 mE) :
    StageBudgetN (fun g s => F g (L s)) q3 (q5 + m5) (qE + mE) :=
  ⟨fun g j s => h.h3 g j (L s), fun g => (h.h5 g).comp_prog hL, fun g => (h.hE g).comp_prog hL⟩

end Stage

/-! ## Slots of two proof systems -/

section Sum

variable {R : Type} {p : Params} {I₁ I₂ W W₁ W₂ ρ Pf P₁ P₂ C₁ C₂ : Type}

lemma rd5_sumProve {p₁ : I₁ → W → ρ → Tab3 → ShG R p → Pf} {p₂ : I₂ → W → ρ → Tab3 → ShG R p → Pf}
    {a : ℕ} (h₁ : ∀ x w r g, Rd5 (p₁ x w r g) a) (h₂ : ∀ x w r g, Rd5 (p₂ x w r g) a)
    (x : I₁ ⊕ I₂) (w : W) (r : ρ) (g : Tab3) : Rd5 (sumProve p₁ p₂ x w r g) a := by
  rcases x with x | x
  · exact (h₁ x w r g).map some
  · exact (h₂ x w r g).map some

lemma rdE_sumProve {p₁ : I₁ → W → ρ → Tab3 → ShG R p → Pf} {p₂ : I₂ → W → ρ → Tab3 → ShG R p → Pf}
    {a : ℕ} (h₁ : ∀ x w r g, RdE (p₁ x w r g) a) (h₂ : ∀ x w r g, RdE (p₂ x w r g) a)
    (x : I₁ ⊕ I₂) (w : W) (r : ρ) (g : Tab3) : RdE (sumProve p₁ p₂ x w r g) a := by
  rcases x with x | x
  · exact (h₁ x w r g).map some
  · exact (h₂ x w r g).map some

lemma rd5_sumProveO {p₁ : I₁ → W₁ → ρ → Tab3 → ShG R p → Option P₁}
    {p₂ : I₂ → W₂ → ρ → Tab3 → ShG R p → Option P₂} {a : ℕ}
    (h₁ : ∀ x w r g, Rd5 (p₁ x w r g) a) (h₂ : ∀ x w r g, Rd5 (p₂ x w r g) a)
    (x : I₁ ⊕ I₂) (w : W₁ × W₂) (r : ρ) (g : Tab3) : Rd5 (sumProveO p₁ p₂ x w r g) a := by
  rcases x with x | x
  · exact (h₁ x w.1 r g).map (Option.map Sum.inl)
  · exact (h₂ x w.2 r g).map (Option.map Sum.inr)

lemma rdE_sumProveO {p₁ : I₁ → W₁ → ρ → Tab3 → ShG R p → Option P₁}
    {p₂ : I₂ → W₂ → ρ → Tab3 → ShG R p → Option P₂} {a : ℕ}
    (h₁ : ∀ x w r g, RdE (p₁ x w r g) a) (h₂ : ∀ x w r g, RdE (p₂ x w r g) a)
    (x : I₁ ⊕ I₂) (w : W₁ × W₂) (r : ρ) (g : Tab3) : RdE (sumProveO p₁ p₂ x w r g) a := by
  rcases x with x | x
  · exact (h₁ x w.1 r g).map (Option.map Sum.inl)
  · exact (h₂ x w.2 r g).map (Option.map Sum.inr)

lemma isProg_sumProg {g₁ : I₁ → C₁ → ShG R p → ShG R p} {g₂ : I₂ → C₂ → ShG R p → ShG R p}
    {a b : ℕ} (h₁ : ∀ x c, IsProg (g₁ x c) a b) (h₂ : ∀ x c, IsProg (g₂ x c) a b)
    (x : I₁ ⊕ I₂) (c : C₁ × C₂) : IsProg (sumProg g₁ g₂ x c) a b := by
  rcases x with x | x
  · exact h₁ x c.1
  · exact h₂ x c.2

/-- A composition of `n` programmings that each read `(a, b)` reads `(n·a, n·b)`. -/
theorem IsProgs.isProg {I C : Type} {prog : I → C → ShG R p → ShG R p} {a b : ℕ}
    (hp : ∀ x c, IsProg (prog x c) a b) {n : ℕ} {L : ShG R p → ShG R p} (h : IsProgs prog n L) :
    IsProg L (n * a) (n * b) := by
  induction h with
  | zero => exact IsProg.id.mono (Nat.zero_le _) (Nat.zero_le _)
  | succ x c _ ih =>
    exact (ih.comp (isProg_progO hp x c)).mono (Nat.succ_mul _ _).ge (Nat.succ_mul _ _).ge

end Sum

/-! ## The hops of the generic game -/

section Dist

variable {Ω O ρ C R : Type} {p : Params} {N : ℕ}
  (P : Ω → List O → ρ → Tab3 → ShG R p → O) (Sm : Ω → List O → C → O)
  (pg : Ω → List O → C → ShG R p → ShG R p)

/-- **`m` real proofs and then a reader**: if a real slot reads `H₅` at `a` keys and `Φ l` at
`b`, the reader on the history after `m` real slots reads `m·a + b`. -/
theorem realFrom_rd5 {X : Type*} (Φ : List O → ShG R p → X) {a b : ℕ}
    (hP : ∀ ω l r g, Rd5 (P ω l r g) a) (hΦ : ∀ l, Rd5 (Φ l) b) (ω : Ω) (rs : ℕ → ρ × Tab3) :
    ∀ (m : ℕ) (h : List O) (j : ℕ), Rd5 (fun s => Φ (realFrom P ω rs s h j m) s) (m * a + b)
  | 0, h, _ => (hΦ h).mono (by omega)
  | m + 1, h, j => by
    have := (hP ω h (rs j).1 (rs j).2).bind
      (f := fun o s => Φ (realFrom P ω rs s (h ++ [o]) (j + 1) m) s)
      fun o => realFrom_rd5 Φ hP hΦ ω rs m (h ++ [o]) (j + 1)
    exact this.mono (by rw [Nat.succ_mul]; omega)

theorem realFrom_rdE {X : Type*} (Φ : List O → ShG R p → X) {a b : ℕ}
    (hP : ∀ ω l r g, RdE (P ω l r g) a) (hΦ : ∀ l, RdE (Φ l) b) (ω : Ω) (rs : ℕ → ρ × Tab3) :
    ∀ (m : ℕ) (h : List O) (j : ℕ), RdE (fun s => Φ (realFrom P ω rs s h j m) s) (m * a + b)
  | 0, h, _ => (hΦ h).mono (by omega)
  | m + 1, h, j => by
    have := (hP ω h (rs j).1 (rs j).2).bind
      (f := fun o s => Φ (realFrom P ω rs s (h ++ [o]) (j + 1) m) s)
      fun o => realFrom_rdE Φ hP hΦ ω rs m (h ++ [o]) (j + 1)
    exact this.mono (by rw [Nat.succ_mul]; omega)

/-- **The programming of the first `n` simulated slots** reads `(n·a, n·b)` if each reads
`(a, b)`. -/
theorem simPre_isProg {a b : ℕ} (hpg : ∀ ω l c, IsProg (pg ω l c) a b) (ω : Ω) (cs : ℕ → C) :
    ∀ n, IsProg (simPre Sm pg ω cs n).2 (n * a) (n * b)
  | 0 => IsProg.id.mono (Nat.zero_le _) (Nat.zero_le _)
  | n + 1 => ((simPre_isProg hpg ω cs n).comp (hpg ω _ _)).mono (Nat.succ_mul _ _).ge
      (Nat.succ_mul _ _).ge

variable [Nonempty ρ] [Nonempty C]

/-- **The budget of the distinguisher of hop `i`**: the later real proofs, the event, and the
programming of the earlier simulations. -/
theorem distN_budget (Ev : Ω → List O → (Fin N → Tab3) → ShG R p → Prop)
    {s5 sE m5 mE q3 q5 qE : ℕ}
    (hP5 : ∀ ω l r g, Rd5 (P ω l r g) s5) (hPE : ∀ ω l r g, RdE (P ω l r g) sE)
    (hpg : ∀ ω l c, IsProg (pg ω l c) m5 mE) (hEv : ∀ ω l, StageBudgetN (Ev ω l) q3 q5 qE)
    (i : Fin N) (ω : Ω) (τ : Fin N → Slot ρ C Tab3) :
    Budget p q3 ((N - (i.val + 1)) * s5 + q5 + i.val * m5)
      ((N - (i.val + 1)) * sE + qE + i.val * mE) (distN P Sm pg Ev i ω τ) := by
  have hL := simPre_isProg Sm pg hpg ω (tapeC τ) i.val
  refine ⟨fun o s => (hEv ω _).h3 (tapeG τ) i _, fun o g => ?_, fun o g => ?_⟩
  · exact (realFrom_rd5 P (fun l s => Ev ω l (Function.update (tapeG τ) i g) s) hP5
      (fun l => (hEv ω l).h5 _) ω (tapeR τ) (N - (i.val + 1))
      ((simPre Sm pg ω (tapeC τ) i).1 ++ [o]) (i.val + 1)).comp_prog hL
  · exact (realFrom_rdE P (fun l s => Ev ω l (Function.update (tapeG τ) i g) s) hPE
      (fun l => (hEv ω l).hE _) ω (tapeR τ) (N - (i.val + 1))
      ((simPre Sm pg ω (tapeC τ) i).1 ++ [o]) (i.val + 1)).comp_prog hL

end Dist

end VoleMole.Theft
