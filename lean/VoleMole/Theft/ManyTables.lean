import VoleMole.Theft.ManyReads
import VoleMole.Theft.ManyPlain
import VoleMole.Theft.Tables

/-!
# The many-token games with the other hashes read off a random table: the generic part

`Theft/Tables.lean` puts one more uniform component `x : X` into the shared tables
(`ShX R p X`) for the one-token theorems. Here are the generic steps for the games with `N` slots
(`Theft/Many.lean`).

* `distN_at`: the distinguisher of hop `i` on tables `φ s`, for a map `φ` of tables that the
  provers, the programmings and the event commute with, is the distinguisher of the game on `s`.
  With `φ = (atX · x)`: the game on `ShX` at a value `x` of the extra table is a game on `ShG`.
* **`distN_budgetX`**: the hops' read budgets, at every value of the extra table (`BudgetX`), from
  the budgets of the game at each value (`distN_budget`).
* `StageBudgetNX`: the read budget of a last stage, at every value of the extra table.
* `simPre_entry`: every entry of the simulated log is a simulated slot.
* `PlainSEN.fresh_mono`, `ProgMovesN.mono`: plain extraction for a stronger freshness, the
  programming term for a smaller class.
-/

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

section At

variable {Ω O ρ C G S S' : Type*} (φ : S' → S)
  {P : Ω → List O → ρ → G → S → O} {P' : Ω → List O → ρ → G → S' → O} (Sm : Ω → List O → C → O)
  {pg : Ω → List O → C → S → S} {pg' : Ω → List O → C → S' → S'}

/-- The simulated log does not depend on the programming. -/
theorem simPre_fst_eq (ω : Ω) (cs : ℕ → C) :
    ∀ j, (simPre Sm pg ω cs j).1 = (simPre Sm pg' ω cs j).1
  | 0 => rfl
  | j + 1 => by simp only [simPre, simPre_fst_eq ω cs j]

/-- The programming of the simulated slots commutes with a map of tables that each programming
commutes with. -/
theorem simPre_at (hpg : ∀ ω l c s, pg ω l c (φ s) = φ (pg' ω l c s)) (ω : Ω) (cs : ℕ → C) :
    ∀ j s, (simPre Sm pg ω cs j).2 (φ s) = φ ((simPre Sm pg' ω cs j).2 s)
  | 0, _ => rfl
  | j + 1, s => by
    simp only [simPre, Function.comp_apply]
    rw [simPre_fst_eq (pg := pg) (pg' := pg') Sm ω cs j, hpg, simPre_at hpg ω cs j]

/-- The real suffix on mapped tables. -/
theorem realFrom_at (hP : ∀ ω l r g s, P ω l r g (φ s) = P' ω l r g s) (ω : Ω) (rs : ℕ → ρ × G)
    (u : S') : ∀ m h j, realFrom P ω rs (φ u) h j m = realFrom P' ω rs u h j m
  | 0, _, _ => rfl
  | m + 1, h, j => by
    simp only [realFrom]
    rw [hP, realFrom_at hP ω rs u m]

variable {N : ℕ} [Nonempty ρ] [Nonempty C] [Nonempty G]

/-- **The distinguisher of hop `i` on mapped tables** is the distinguisher of the game on the
tables before the map. -/
theorem distN_at {Ev : Ω → List O → (Fin N → G) → S → Prop}
    {Ev' : Ω → List O → (Fin N → G) → S' → Prop}
    (hP : ∀ ω l r g s, P ω l r g (φ s) = P' ω l r g s)
    (hpg : ∀ ω l c s, pg ω l c (φ s) = φ (pg' ω l c s))
    (hEv : ∀ ω l g s, Ev ω l g (φ s) = Ev' ω l g s) (i : Fin N) (ω : Ω)
    (τ : Fin N → Slot ρ C G) (o : O) (g : G) (s : S') :
    distN P Sm pg Ev i ω τ o g (φ s) = distN P' Sm pg' Ev' i ω τ o g s := by
  simp only [distN, contN]
  rw [simPre_at φ Sm hpg, realFrom_at φ hP, hEv, simPre_fst_eq (pg := pg) (pg' := pg') Sm]

end At

/-- **Every entry of the simulated log is a simulated slot.** -/
theorem simPre_entry {Ω O C S : Type*} (Sm : Ω → List O → C → O) (pg : Ω → List O → C → S → S)
    (ω : Ω) (cs : ℕ → C) :
    ∀ n, ∀ e ∈ (simPre Sm pg ω cs n).1, ∃ j < n, e = Sm ω (simPre Sm pg ω cs j).1 (cs j)
  | 0, e, h => by simp [simPre] at h
  | n + 1, e, h => by
    simp only [simPre, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · obtain ⟨j, hj, he⟩ := simPre_entry Sm pg ω cs n e h
      exact ⟨j, Nat.lt_succ_of_lt hj, he⟩
    · exact ⟨n, Nat.lt_succ_self n, h⟩

section Budget

variable {R : Type} {p : Params} {X : Type} {N : ℕ} {Y : Type*}

/-- **The read budget of a last stage with `N` slices, at every value of the extra table** (which
it may read freely). -/
def StageBudgetNX (F : (Fin N → Tab3) → ShX R p X → Y) (q3 q5 qE : ℕ) : Prop :=
  ∀ x, StageBudgetN (fun g s => F g (atX s x)) q3 q5 qE

/-- A constant last stage reads nothing. -/
lemma StageBudgetNX.const (y : Y) :
    StageBudgetNX (R := R) (p := p) (X := X) (N := N) (fun _ _ => y) 0 0 0 :=
  fun _ => StageBudgetN.const y

variable {Ω O ρ C : Type} [Nonempty ρ] [Nonempty C]
  {P : Ω → List O → ρ → Tab3 → ShX R p X → O} (Sm : Ω → List O → C → O)
  {pg : Ω → List O → C → ShX R p X → ShX R p X}
  {Ev : Ω → List O → (Fin N → Tab3) → ShX R p X → Prop}

/-- **The budget of the distinguisher of hop `i`, at every value of the extra table.** The game
at the value `x` (`P' x`, `pg' x`, `Ev' x`) is a game on `ShG R p`; its budgets give the budget of
the hop (`distN_budget`). -/
theorem distN_budgetX (P' : X → Ω → List O → ρ → Tab3 → ShG R p → O)
    (pg' : X → Ω → List O → C → ShG R p → ShG R p)
    (Ev' : X → Ω → List O → (Fin N → Tab3) → ShG R p → Prop) {s5 sE m5 mE q3 q5 qE : ℕ}
    (hP : ∀ x ω l r g s, P ω l r g (atX s x) = P' x ω l r g s)
    (hpg : ∀ x ω l c s, pg ω l c (atX s x) = atX (pg' x ω l c s) x)
    (hEv : ∀ x ω l g s, Ev ω l g (atX s x) = Ev' x ω l g s)
    (hP5 : ∀ x ω l r g, Rd5 (P' x ω l r g) s5) (hPE : ∀ x ω l r g, RdE (P' x ω l r g) sE)
    (hpg' : ∀ x ω l c, IsProg (pg' x ω l c) m5 mE)
    (hEv' : ∀ x ω l, StageBudgetN (Ev' x ω l) q3 q5 qE) (i : Fin N) (ω : Ω)
    (τ : Fin N → Slot ρ C Tab3) :
    BudgetX p q3 ((N - (i.val + 1)) * s5 + q5 + i.val * m5)
      ((N - (i.val + 1)) * sE + qE + i.val * mE) (distN P Sm pg Ev i ω τ) := by
  intro x
  have e : (fun o g s => distN P Sm pg Ev i ω τ o g (atX s x)) =
      distN (P' x) Sm (pg' x) (Ev' x) i ω τ := by
    funext o g s
    exact distN_at (fun s => atX s x) Sm (hP x) (hpg x) (hEv x) i ω τ o g s
  rw [e]
  exact distN_budget (P' x) Sm (pg' x) (Ev' x) (hP5 x) (hPE x) (hpg' x) (hEv' x) i ω τ

lemma BudgetX.mono {O' : Type*} {q3 q5 qE q3' q5' qE' : ℕ} {D : O' → Tab3 → ShX R p X → Prop}
    (h : BudgetX p q3 q5 qE D) (h3 : q3 ≤ q3') (h5 : q5 ≤ q5') (hE : qE ≤ qE') :
    BudgetX p q3' q5' qE' D :=
  fun x => (h x).mono h3 h5 hE

lemma BudgetX.comp {O' O'' : Type*} {q3 q5 qE : ℕ} {D : O' → Tab3 → ShX R p X → Prop}
    (h : BudgetX p q3 q5 qE D) (f : O'' → O') :
    BudgetX p q3 q5 qE (fun o g s => D (f o) g s) :=
  fun x => (h x).comp f

end Budget

section Mono

variable {N : ℕ} {I P C G A B Out W : Type} [Fintype G] [Fintype A] [Fintype B]

/-- Plain extraction for a stronger freshness. -/
lemma PlainSEN.fresh_mono {Acc : Out → A × B → Prop}
    {Fresh Fresh' : List (Option (I × P)) → Out → Prop} {Rel : Out → W → Prop}
    {e : List (Option (I × P)) → Out → (Fin N → G) → B → W}
    {Adm : ((Fin N → G) → A × B → Out) → Prop} {ε : ℝ} (h : PlainSEN N Acc Fresh Rel e Adm ε)
    (hF : ∀ l o, Fresh' l o → Fresh l o) : PlainSEN N Acc Fresh' Rel e Adm ε :=
  fun α _ _ lg F hF' => (Privacy.pr_mono fun _ hz => ⟨hz.1, hF _ _ hz.2.1, hz.2.2⟩).trans
    (h α lg F hF')

variable [Fintype C] [Nonempty C]

/-- The programming term for a smaller class of adversaries. -/
lemma ProgMovesN.mono {sim : I → C → Option P} {prog : I → C → A × B → A × B}
    {Acc : Out → A × B → Prop} {Fresh : List (Option (I × P)) → Out → Prop}
    {Adm Adm' : ((Fin N → G) → A × B → Out) → Prop} {ε : ℝ}
    (h : ProgMovesN N sim prog Acc Fresh Adm ε) (hA : ∀ F, Adm' F → Adm F) :
    ProgMovesN N sim prog Acc Fresh Adm' ε :=
  fun α _ _ x out hout => h α x out fun a l => hA _ (hout a l)

end Mono

end VoleMole.Theft
