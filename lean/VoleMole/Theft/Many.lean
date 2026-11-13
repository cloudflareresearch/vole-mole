import VoleMole.Theft.Basic

/-!
# Non-malleability games with many honest proofs

`Theft/Basic.lean` treats one honest Client with two proofs (`real_sim_le`, `theft_le`,
`WeakSE2`). This file is the same argument for `N` honest proofs made in sequence, each for a
statement that may depend on the honest secrets and on everything output before (several honest
tokens, several redemptions per token, in an order the adversary chooses).

* **The game.** Slot `j < N` has a tape `((ρ, c), g)`: the prover's randomness, the simulator's
  coins and the proof's private table (its `H₃` slice). A real slot uses `ρ`, a simulated one `c`,
  so every hybrid lives on one tape `(Ω × (Fin N → Slot)) × S`. `P ω h ρ g s` is the real output
  of the next slot after the history `h` (the list of earlier outputs), `Sm ω h c` the simulated
  one and `pg ω h c` its programming.
* **`hyb N i Ev`**: the first `i` slots simulated (`simPre`: their outputs are functions of the
  coins only, and their programmings compose, the earliest outermost, as in `real_sim_le`), the
  other `N − i` real on the programmed tables (`realFrom`), the event read on the programmed
  tables. `hyb N 0` is the real game (`realGN`), `hyb N N` the simulated one (`simGN`).
* **`hyb_hop`**: slot `i` real or simulated differ by the zero-knowledge error of the hop's
  distinguisher `distN i` (the rest of the game with the later proofs real, on the tables the
  earlier simulations programmed) plus the collision term `deltaN i` (the real proof `i` reads the
  tables differently with and without the earlier programming). It is `Privacy.hop_ro` with every
  other coordinate of the tape fixed.
* **`real_sim_leN`**, **`theftN_le`**: the `N` hops, and the bound for an event
  `Acc ∧ Fresh ∧ (¬ Rel ∨ Hit)`:

      Pr_real ≤ Σ_i (ε_i + Pr[deltaN i]) + Pr_sim[Acc ∧ Fresh ∧ ¬ Rel] + Pr_sim[Hit].

* **`WeakSEN`**: weak simulation-extractability against adversaries that see `N` simulated
  proofs for statements they choose adaptively, from the earlier simulated statements and proofs,
  without reading the tables (`lean/docs/extraction/L8-simulation-extractability.md`, game `SE_A`
  with `q_S = N`, weak form). `WeakSE2` is the case of two proofs, one per relation. **A
  hypothesis**, as `WeakSE2`. `simGN_le_of_weakSEN` applies it to the simulated game.
-/

open Finset

namespace VoleMole.Theft

open VoleMole.Privacy

/-! ## Tapes -/

/-- One slot's tape: the prover's randomness, the simulator's coins, the private table. -/
abbrev Slot (ρ C G : Type*) := (ρ × C) × G

/-- A finite tape as a function on `ℕ` (an arbitrary value beyond its end; never read). -/
noncomputable def extN {N : ℕ} {X : Type*} [Nonempty X] (f : Fin N → X) (j : ℕ) : X :=
  if h : j < N then f ⟨j, h⟩ else Classical.arbitrary X

theorem extN_val {N : ℕ} {X : Type*} [Nonempty X] (f : Fin N → X) (i : Fin N) :
    extN f i.val = f i := by
  simp [extN]

theorem extN_update_ne {N : ℕ} {X : Type*} [Nonempty X] (f : Fin N → X) (i : Fin N) (t : X)
    {j : ℕ} (h : j ≠ i.val) : extN (Function.update f i t) j = extN f j := by
  unfold extN
  split_ifs with hj
  · rw [Function.update_of_ne]
    exact fun e => h (congrArg Fin.val e)
  · rfl

section Many

variable {Ω O ρ C G S : Type*}
  (P : Ω → List O → ρ → G → S → O) (Sm : Ω → List O → C → O) (pg : Ω → List O → C → S → S)

/-- **The simulated prefix**: the outputs of the first `j` slots, simulated, and the programming
they apply (slot `0`'s outermost). -/
def simPre (ω : Ω) (cs : ℕ → C) : ℕ → List O × (S → S)
  | 0 => ([], id)
  | j + 1 =>
    ((simPre ω cs j).1 ++ [Sm ω (simPre ω cs j).1 (cs j)],
      (simPre ω cs j).2 ∘ pg ω (simPre ω cs j).1 (cs j))

theorem simPre_congr {ω : Ω} {cs cs' : ℕ → C} :
    ∀ j, (∀ k < j, cs k = cs' k) → simPre Sm pg ω cs j = simPre Sm pg ω cs' j
  | 0, _ => rfl
  | j + 1, h => by
    simp only [simPre]
    rw [simPre_congr j fun k hk => h k (by omega), h j (by omega)]

theorem simPre_length (ω : Ω) (cs : ℕ → C) : ∀ j, (simPre Sm pg ω cs j).1.length = j
  | 0 => rfl
  | j + 1 => by simp [simPre, simPre_length ω cs j]

/-- The simulated prefix of a game whose simulation depends on `ω` through `f ω` only. -/
theorem simPre_map {Ω' : Type*} (f : Ω → Ω') (Sm' : Ω' → List O → C → O)
    (pg' : Ω' → List O → C → S → S) (ω : Ω) (cs : ℕ → C) :
    ∀ j, simPre (fun ω => Sm' (f ω)) (fun ω => pg' (f ω)) ω cs j = simPre Sm' pg' (f ω) cs j
  | 0 => rfl
  | j + 1 => by simp only [simPre, simPre_map f Sm' pg' ω cs j]

/-- **The real suffix**: `m` real proofs from slot `j` on, after the history `h`, on the tables
`u`. -/
def realFrom (ω : Ω) (rs : ℕ → ρ × G) (u : S) : List O → ℕ → ℕ → List O
  | h, _, 0 => h
  | h, j, m + 1 => realFrom ω rs u (h ++ [P ω h (rs j).1 (rs j).2 u]) (j + 1) m

theorem realFrom_congr {ω : Ω} {u : S} {rs rs' : ℕ → ρ × G} :
    ∀ m h j, (∀ k, j ≤ k → rs k = rs' k) → realFrom P ω rs u h j m = realFrom P ω rs' u h j m
  | 0, _, _, _ => rfl
  | m + 1, h, j, hr => by
    simp only [realFrom]
    rw [hr j le_rfl]
    exact realFrom_congr m _ (j + 1) fun k hk => hr k (by omega)

variable {N : ℕ}

/-- The simulator coins, the provers' inputs and the private tables of a tape. -/
noncomputable def tapeC [Nonempty C] (τ : Fin N → Slot ρ C G) : ℕ → C := extN fun j => (τ j).1.2
noncomputable def tapeR [Nonempty ρ] [Nonempty G] (τ : Fin N → Slot ρ C G) : ℕ → ρ × G :=
  extN fun j => ((τ j).1.1, (τ j).2)
def tapeG (τ : Fin N → Slot ρ C G) : Fin N → G := fun j => (τ j).2

variable [Nonempty ρ] [Nonempty C] [Nonempty G]

omit [Nonempty ρ] [Nonempty G] in
theorem tapeC_update_ne (τ : Fin N → Slot ρ C G) (i : Fin N) (t : Slot ρ C G) {j : ℕ}
    (h : j ≠ i.val) : tapeC (Function.update τ i t) j = tapeC τ j := by
  have e : (fun j => (Function.update τ i t j).1.2) =
      Function.update (fun j => (τ j).1.2) i t.1.2 := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  unfold tapeC
  rw [e, extN_update_ne _ _ _ h]

omit [Nonempty ρ] [Nonempty G] in
theorem tapeC_update_self (τ : Fin N → Slot ρ C G) (i : Fin N) (t : Slot ρ C G) :
    tapeC (Function.update τ i t) i.val = t.1.2 := by
  unfold tapeC
  rw [extN_val]; simp

omit [Nonempty C] in
theorem tapeR_update_ne (τ : Fin N → Slot ρ C G) (i : Fin N) (t : Slot ρ C G) {j : ℕ}
    (h : j ≠ i.val) : tapeR (Function.update τ i t) j = tapeR τ j := by
  have e : (fun j => ((Function.update τ i t j).1.1, (Function.update τ i t j).2)) =
      Function.update (fun j => ((τ j).1.1, (τ j).2)) i (t.1.1, t.2) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  unfold tapeR
  rw [e, extN_update_ne _ _ _ h]

omit [Nonempty C] in
theorem tapeR_update_self (τ : Fin N → Slot ρ C G) (i : Fin N) (t : Slot ρ C G) :
    tapeR (Function.update τ i t) i.val = (t.1.1, t.2) := by
  unfold tapeR
  rw [extN_val]; simp

omit [Nonempty ρ] [Nonempty C] [Nonempty G] in
theorem tapeG_update (τ : Fin N → Slot ρ C G) (i : Fin N) (t : Slot ρ C G) :
    tapeG (Function.update τ i t) = Function.update (tapeG τ) i t.2 := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [tapeG]
  · simp [tapeG, Function.update_of_ne hk]

/-! ## The hybrids -/

variable (Ev : Ω → List O → (Fin N → G) → S → Prop)

/-- **The `i`-th hybrid**: slots `< i` simulated, slots `≥ i` real on the tables the simulations
programmed; the event reads the programmed tables. -/
def hyb (N i : ℕ) (Ev : Ω → List O → (Fin N → G) → S → Prop)
    (z : (Ω × (Fin N → Slot ρ C G)) × S) : Prop :=
  Ev z.1.1
    (realFrom P z.1.1 (tapeR z.1.2) ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2 z.2)
      (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 i (N - i))
    (tapeG z.1.2) ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2 z.2)

/-- **The real game**: every proof real, on uniform tables. -/
def realGN (z : (Ω × (Fin N → Slot ρ C G)) × S) : Prop :=
  Ev z.1.1 (realFrom P z.1.1 (tapeR z.1.2) z.2 [] 0 N) (tapeG z.1.2) z.2

/-- **The simulated game**: every proof simulated, the event read on the programmed tables. -/
def simGN (z : (Ω × (Fin N → Slot ρ C G)) × S) : Prop :=
  Ev z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) N).1 (tapeG z.1.2)
    ((simPre Sm pg z.1.1 (tapeC z.1.2) N).2 z.2)

theorem hyb_zero : hyb P Sm pg N 0 Ev = realGN P Ev := rfl

theorem hyb_last : hyb P Sm pg N N Ev = simGN Sm pg Ev := by
  funext z
  simp only [hyb, simGN, Nat.sub_self, realFrom]

/-- **The rest of the game after slot `i`**, given that slot's output `o`, its private table `g`
and the tables `u` the game runs on: the later proofs real on `u`. Slot `i` of `τ` is not read. -/
def contN (i : Fin N) (ω : Ω) (τ : Fin N → Slot ρ C G) (o : O) (g : G) (u : S) : Prop :=
  Ev ω
    (realFrom P ω (tapeR τ) u ((simPre Sm pg ω (tapeC τ) i).1 ++ [o]) (i.val + 1)
      (N - (i.val + 1)))
    (Function.update (tapeG τ) i g) u

/-- **The distinguisher of hop `i`**: the rest of the game, on the tables the earlier simulations
programmed. -/
def distN (i : Fin N) (ω : Ω) (τ : Fin N → Slot ρ C G) (o : O) (g : G) (u : S) : Prop :=
  contN P Sm pg Ev i ω τ o g ((simPre Sm pg ω (tapeC τ) i).2 u)

/-- **The collision term of hop `i`**: the real proof `i` reads the tables differently with and
without the programming of the simulated slots before it. -/
def deltaN (i : Fin N) (z : (Ω × (Fin N → Slot ρ C G)) × S) : Prop :=
  P z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 (tapeR z.1.2 i).1 (tapeR z.1.2 i).2
      ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2 z.2) ≠
    P z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 (tapeR z.1.2 i).1 (tapeR z.1.2 i).2 z.2

omit [Nonempty ρ] [Nonempty G] in
theorem simPre_update (i : Fin N) (ω : Ω) (τ : Fin N → Slot ρ C G) (t : Slot ρ C G) :
    simPre Sm pg ω (tapeC (Function.update τ i t)) i = simPre Sm pg ω (tapeC τ) i :=
  simPre_congr Sm pg _ fun _ hk => tapeC_update_ne τ i t (Nat.ne_of_lt hk)

/-- Hybrid `i` with slot `i` set to `t`: the real proof of slot `i`, then the rest. -/
theorem hyb_update_real (i : Fin N) (ω : Ω) (τ : Fin N → Slot ρ C G) (t : Slot ρ C G) (s : S) :
    hyb P Sm pg N i Ev ((ω, Function.update τ i t), s) ↔
      contN P Sm pg Ev i ω τ
        (P ω (simPre Sm pg ω (tapeC τ) i).1 t.1.1 t.2 ((simPre Sm pg ω (tapeC τ) i).2 s)) t.2
        ((simPre Sm pg ω (tapeC τ) i).2 s) := by
  have hN : N - i.val = (N - (i.val + 1)) + 1 := by have := i.isLt; omega
  simp only [hyb, contN]
  rw [simPre_update, hN, realFrom, tapeR_update_self, tapeG_update,
    realFrom_congr P _ _ (i.val + 1) fun k hk => tapeR_update_ne τ i t (by omega)]

/-- Hybrid `i + 1` with slot `i` set to `t`: the simulated proof of slot `i`, then the rest. -/
theorem hyb_update_sim (i : Fin N) (ω : Ω) (τ : Fin N → Slot ρ C G) (t : Slot ρ C G) (s : S) :
    hyb P Sm pg N (i.val + 1) Ev ((ω, Function.update τ i t), s) ↔
      contN P Sm pg Ev i ω τ (Sm ω (simPre Sm pg ω (tapeC τ) i).1 t.1.2) t.2
        ((simPre Sm pg ω (tapeC τ) i).2 (pg ω (simPre Sm pg ω (tapeC τ) i).1 t.1.2 s)) := by
  simp only [hyb, contN, simPre, Function.comp]
  rw [simPre_update, tapeC_update_self, tapeG_update,
    realFrom_congr P _ _ (i.val + 1) fun k hk => tapeR_update_ne τ i t (by omega)]

variable [Fintype Ω] [Nonempty Ω] [Fintype ρ] [Fintype C] [Fintype G] [Fintype S]

omit [Nonempty Ω] in
/-- Resampling slot `i` of the tape does not change a probability. -/
theorem pr_slot (i : Fin N) (X : (Ω × (Fin N → Slot ρ C G)) × S → Prop) :
    pr ((Ω × (Fin N → Slot ρ C G)) × (Slot ρ C G × S))
        (fun z => X ((z.1.1, Function.update z.1.2 i z.2.1), z.2.2)) =
      pr ((Ω × (Fin N → Slot ρ C G)) × S) X := by
  let e : (Ω × (Fin N → Slot ρ C G)) × (Slot ρ C G × S) ≃
      Slot ρ C G × ((Ω × (Fin N → Slot ρ C G)) × S) :=
    { toFun := fun z => (z.1.2 i, ((z.1.1, Function.update z.1.2 i z.2.1), z.2.2))
      invFun := fun y => ((y.2.1.1, Function.update y.2.1.2 i y.1), (y.2.1.2 i, y.2.2))
      left_inv := fun z => by simp
      right_inv := fun y => by simp }
  have h := pr_equiv e (fun y : Slot ρ C G × ((Ω × (Fin N → Slot ρ C G)) × S) => X y.2)
  rw [pr_prod_snd] at h
  exact h

omit [Nonempty ρ] [Nonempty G] [Fintype Ω] [Nonempty Ω] in
/-- A slot whose simulator coins are not read. -/
theorem pr_slot_real (X : ρ → G → S → Prop) :
    pr (Slot ρ C G × S) (fun a => X a.1.1.1 a.1.2 a.2) =
      pr ((ρ × G) × S) (fun a => X a.1.1 a.1.2 a.2) := by
  let e : Slot ρ C G × S ≃ C × ((ρ × G) × S) :=
    { toFun := fun a => (a.1.1.2, ((a.1.1.1, a.1.2), a.2))
      invFun := fun y => (((y.2.1.1, y.1), y.2.1.2), y.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := pr_equiv e (fun y : C × ((ρ × G) × S) => X y.2.1.1 y.2.1.2 y.2.2)
  rw [pr_prod_snd (α := C) (fun y : (ρ × G) × S => X y.1.1 y.1.2 y.2)] at h
  exact h

omit [Nonempty C] [Nonempty G] [Fintype Ω] [Nonempty Ω] in
/-- A slot whose prover randomness is not read. -/
theorem pr_slot_sim (X : C → G → S → Prop) :
    pr (Slot ρ C G × S) (fun a => X a.1.1.2 a.1.2 a.2) =
      pr ((C × G) × S) (fun a => X a.1.1 a.1.2 a.2) := by
  let e : Slot ρ C G × S ≃ ρ × ((C × G) × S) :=
    { toFun := fun a => (a.1.1.1, ((a.1.1.2, a.1.2), a.2))
      invFun := fun y => (((y.1, y.2.1.1), y.2.1.2), y.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := pr_equiv e (fun y : ρ × ((C × G) × S) => X y.2.1.1 y.2.1.2 y.2.2)
  rw [pr_prod_snd (α := ρ) (fun y : (C × G) × S => X y.1.1 y.1.2 y.2)] at h
  exact h

/-- **One hop.** If the real proof of slot `i` on uniform tables and its simulation, seen through
the hop's distinguisher `distN i`, are `ε`-close for every rest of the tape, hybrids `i` and
`i + 1` are `ε + Pr[deltaN i]`-close. -/
theorem hyb_hop (i : Fin N) {ε : ℝ}
    (h : ∀ ω τ, |pr ((ρ × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) a.1.2 a.2) -
        pr ((C × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (Sm ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1) a.1.2
          (pg ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.2))| ≤ ε) :
    |pr _ (hyb P Sm pg N i Ev) - pr _ (hyb P Sm pg N (i.val + 1) Ev)| ≤
      ε + pr _ (deltaN P Sm pg i) := by
  -- the three events on the tape with slot `i` resampled
  let A : (Ω × (Fin N → Slot ρ C G)) × (Slot ρ C G × S) → Prop := fun z =>
    contN P Sm pg Ev i z.1.1 z.1.2
      (P z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 z.2.1.1.1 z.2.1.2
        ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2 z.2.2)) z.2.1.2
      ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2 z.2.2)
  let A' : (Ω × (Fin N → Slot ρ C G)) × (Slot ρ C G × S) → Prop := fun z =>
    contN P Sm pg Ev i z.1.1 z.1.2
      (P z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 z.2.1.1.1 z.2.1.2 z.2.2) z.2.1.2
      ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2 z.2.2)
  let B : (Ω × (Fin N → Slot ρ C G)) × (Slot ρ C G × S) → Prop := fun z =>
    contN P Sm pg Ev i z.1.1 z.1.2 (Sm z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 z.2.1.1.2)
      z.2.1.2 ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2
        (pg z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 z.2.1.1.2 z.2.2))
  let bad : (Ω × (Fin N → Slot ρ C G)) × (Slot ρ C G × S) → Prop := fun z =>
    P z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 z.2.1.1.1 z.2.1.2
        ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2 z.2.2) ≠
      P z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 z.2.1.1.1 z.2.1.2 z.2.2
  have eA : pr _ (hyb P Sm pg N i Ev) = pr _ A := by
    rw [← pr_slot i (hyb P Sm pg N i Ev)]
    exact pr_congr fun z => hyb_update_real P Sm pg Ev i z.1.1 z.1.2 z.2.1 z.2.2
  have eB : pr _ (hyb P Sm pg N (i.val + 1) Ev) = pr _ B := by
    rw [← pr_slot i (hyb P Sm pg N (i.val + 1) Ev)]
    exact pr_congr fun z => hyb_update_sim P Sm pg Ev i z.1.1 z.1.2 z.2.1 z.2.2
  have ebad : pr _ (deltaN P Sm pg i) = pr _ bad := by
    rw [← pr_slot i (deltaN P Sm pg i)]
    refine pr_congr fun z => ?_
    simp only [deltaN, bad, simPre_update, tapeR_update_self]
  have h1 : |pr _ A - pr _ A'| ≤ pr _ bad :=
    abs_pr_sub_le_of_agree A A' bad fun z hz => by
      simp only [A, A', bad] at hz ⊢
      rw [not_not.1 hz]
  have h2 : |pr _ A' - pr _ B| ≤ ε := by
    refine abs_pr_prod_sub_le A' B fun γ => ?_
    have e1 := pr_slot_real (C := C) (fun r g s => contN P Sm pg Ev i γ.1 γ.2
      (P γ.1 (simPre Sm pg γ.1 (tapeC γ.2) i).1 r g s) g ((simPre Sm pg γ.1 (tapeC γ.2) i).2 s))
    have e2 := pr_slot_sim (ρ := ρ) (fun c g s => contN P Sm pg Ev i γ.1 γ.2
      (Sm γ.1 (simPre Sm pg γ.1 (tapeC γ.2) i).1 c) g
      ((simPre Sm pg γ.1 (tapeC γ.2) i).2 (pg γ.1 (simPre Sm pg γ.1 (tapeC γ.2) i).1 c s)))
    simp only [A', B]
    rw [e1, e2]
    exact h γ.1 γ.2
  rw [eA, eB, ebad]
  have := abs_sub_le (pr _ A) (pr _ A') (pr _ B)
  linarith

/-- **The `N` hops.** If slot `i`'s real proof and its simulation are `ε i`-close through the
hop's distinguisher, for every `i`, the real and the simulated game differ by at most
`Σ_i (ε i + Pr[deltaN i])`. -/
theorem real_sim_leN (ε : Fin N → ℝ)
    (h : ∀ (i : Fin N) ω τ, |pr ((ρ × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) a.1.2 a.2) -
        pr ((C × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (Sm ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1) a.1.2
          (pg ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.2))| ≤ ε i) :
    |pr _ (realGN (C := C) P Ev) - pr _ (simGN (ρ := ρ) Sm pg Ev)| ≤
      ∑ i, (ε i + pr _ (deltaN P Sm pg i)) := by
  rw [← hyb_zero P Sm pg Ev, ← hyb_last P Sm pg Ev]
  let e : ℕ → ℝ := fun i => if hi : i < N then ε ⟨i, hi⟩ + pr _ (deltaN P Sm pg ⟨i, hi⟩) else 0
  have key : ∀ k, k ≤ N →
      |pr _ (hyb P Sm pg N 0 Ev) - pr _ (hyb P Sm pg N k Ev)| ≤ ∑ i ∈ range k, e i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkN : k < N := by omega
      have hop := hyb_hop P Sm pg Ev ⟨k, hkN⟩ (h ⟨k, hkN⟩)
      have := abs_sub_le (pr _ (hyb P Sm pg N 0 Ev)) (pr _ (hyb P Sm pg N k Ev))
        (pr _ (hyb P Sm pg N (k + 1) Ev))
      rw [Finset.sum_range_succ]
      have ek : e k = ε ⟨k, hkN⟩ + pr _ (deltaN P Sm pg ⟨k, hkN⟩) := by
        simp only [e, hkN, ↓reduceDIte]
      have := ih (by omega)
      linarith
  refine (key N le_rfl).trans (le_of_eq ?_)
  rw [← Fin.sum_univ_eq_sum_range e N]
  exact Finset.sum_congr rfl fun i _ => by simp only [e, i.isLt, ↓reduceDIte]

/-- **The non-malleability bound with `N` honest proofs.** For the event
`Acc ∧ Fresh ∧ (¬ Rel ∨ Hit)`:

    Pr_real[event] ≤ Σ_i (ε i + Pr[deltaN i]) + Pr_sim[Acc ∧ Fresh ∧ ¬ Rel] + Pr_sim[Hit]. -/
theorem theftN_le (Acc Fr Rl Op : Ω → List O → (Fin N → G) → S → Prop) (ε : Fin N → ℝ)
    (h : ∀ (i : Fin N) ω τ, |pr ((ρ × G) × S) (fun a => distN P Sm pg
          (fun ω l g s => Acc ω l g s ∧ Fr ω l g s ∧ (¬ Rl ω l g s ∨ Op ω l g s)) i ω τ
          (P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) a.1.2 a.2) -
        pr ((C × G) × S) (fun a => distN P Sm pg
          (fun ω l g s => Acc ω l g s ∧ Fr ω l g s ∧ (¬ Rl ω l g s ∨ Op ω l g s)) i ω τ
          (Sm ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1) a.1.2
          (pg ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.2))| ≤ ε i) :
    pr _ (realGN (C := C) P
        (fun ω l g s => Acc ω l g s ∧ Fr ω l g s ∧ (¬ Rl ω l g s ∨ Op ω l g s))) ≤
      ∑ i, (ε i + pr _ (deltaN P Sm pg i)) +
        pr _ (simGN (ρ := ρ) Sm pg (fun ω l g s => Acc ω l g s ∧ Fr ω l g s ∧ ¬ Rl ω l g s)) +
        pr _ (simGN (ρ := ρ) Sm pg Op) := by
  have h0 := real_sim_leN P Sm pg _ ε h
  have hs := (pr_mono (α := (Ω × (Fin N → Slot ρ C G)) × S)
    (P := simGN Sm pg (fun ω l g s => Acc ω l g s ∧ Fr ω l g s ∧ (¬ Rl ω l g s ∨ Op ω l g s)))
    (Q := fun z => simGN Sm pg (fun ω l g s => Acc ω l g s ∧ Fr ω l g s ∧ ¬ Rl ω l g s) z ∨
      simGN Sm pg Op z)
    fun z hz => by
      unfold simGN at hz ⊢
      rcases hz with ⟨ha, hf, hr | ho⟩
      · exact Or.inl ⟨ha, hf, hr⟩
      · exact Or.inr ho).trans (pr_or_le _ _)
  have := (abs_sub_le_iff.1 h0).1
  linarith

omit [Nonempty Ω] in
/-- The first hop has no collision term: nothing is programmed before it. -/
theorem deltaN_zero (hN : 0 < N) :
    pr ((Ω × (Fin N → Slot ρ C G)) × S) (deltaN P Sm pg ⟨0, hN⟩) = 0 := by
  have : deltaN P Sm pg (⟨0, hN⟩ : Fin N) = fun _ => False := by
    funext z
    simp [deltaN, simPre]
  rw [this]
  classical
  rw [pr_def]
  simp

end Many

/-! ## Weak simulation-extractability with many simulated proofs -/

section SE

/-- **Weak simulation-extractability for `N` simulated proofs**, with error `ε`, against the
adversaries `Adm` admits.

The adversary has coins `a` (any finite type, uniform). For `j = 0, …, N − 1` it chooses the
`j`-th statement `x a l` (or none) from the log `l` of the earlier simulated statements and
proofs, and gets the simulated proof (coins `c_j`). Then, reading the private tables `g` and the
shared tables as all simulations programmed them (the earliest outermost), it outputs `out`. It
wins if the output is accepted (`Acc`), is fresh with respect to the log (`Fresh`, weak: only the
statements count) and the extractor's witness is not one (`¬ Rel`). The extractor `ext` sees the
log, the adversary's last stage as a function of the tables (its queries) and the programmed
tables; it does not see the simulators' coins. The statements are chosen without reading the
tables; the last stage reads them freely, subject to `Adm`.

This is `WeakSE2` (`Theft/Basic.lean`) with `N` simulated proofs in place of two, for one proof
system (for two relations, the sum of the instance types). -/
def WeakSEN (N : ℕ) {I P C G S Out W : Type*} [Fintype C] [Nonempty C] [Fintype G] [Fintype S]
    (sim : I → C → Option P) (prog : I → C → S → S) (Acc : Out → S → Prop)
    (Fresh : List (Option (I × P)) → Out → Prop) (Rel : Out → W → Prop)
    (ext : List (Option (I × P)) → ((Fin N → G) → S → Out) → (Fin N → G) → S → W)
    (Adm : ((Fin N → G) → S → Out) → Prop) (ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [Nonempty α] (x : α → List (Option (I × P)) → Option I)
    (out : α → List (Option (I × P)) → (Fin N → G) → S → Out),
    (∀ a l, Adm (out a l)) →
    pr ((α × (Fin N → C × G)) × S) (fun z =>
      Acc (out z.1.1
          (simPre (fun a l c => pairO (x a l) (simO sim (x a l) c))
            (fun a l c => progO prog (x a l) c) z.1.1 (extN fun j => (z.1.2 j).1) N).1
          (fun j => (z.1.2 j).2)
          ((simPre (fun a l c => pairO (x a l) (simO sim (x a l) c))
            (fun a l c => progO prog (x a l) c) z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2))
        ((simPre (fun a l c => pairO (x a l) (simO sim (x a l) c))
          (fun a l c => progO prog (x a l) c) z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2) ∧
      Fresh (simPre (fun a l c => pairO (x a l) (simO sim (x a l) c))
          (fun a l c => progO prog (x a l) c) z.1.1 (extN fun j => (z.1.2 j).1) N).1
        (out z.1.1
          (simPre (fun a l c => pairO (x a l) (simO sim (x a l) c))
            (fun a l c => progO prog (x a l) c) z.1.1 (extN fun j => (z.1.2 j).1) N).1
          (fun j => (z.1.2 j).2)
          ((simPre (fun a l c => pairO (x a l) (simO sim (x a l) c))
            (fun a l c => progO prog (x a l) c) z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2)) ∧
      ¬ Rel (out z.1.1
          (simPre (fun a l c => pairO (x a l) (simO sim (x a l) c))
            (fun a l c => progO prog (x a l) c) z.1.1 (extN fun j => (z.1.2 j).1) N).1
          (fun j => (z.1.2 j).2)
          ((simPre (fun a l c => pairO (x a l) (simO sim (x a l) c))
            (fun a l c => progO prog (x a l) c) z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2))
        (ext (simPre (fun a l c => pairO (x a l) (simO sim (x a l) c))
            (fun a l c => progO prog (x a l) c) z.1.1 (extN fun j => (z.1.2 j).1) N).1
          (out z.1.1
            (simPre (fun a l c => pairO (x a l) (simO sim (x a l) c))
              (fun a l c => progO prog (x a l) c) z.1.1 (extN fun j => (z.1.2 j).1) N).1)
          (fun j => (z.1.2 j).2)
          ((simPre (fun a l c => pairO (x a l) (simO sim (x a l) c))
            (fun a l c => progO prog (x a l) c) z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2))) ≤ ε

variable {N : ℕ} {I P C G S Out W : Type} [Fintype C] [Nonempty C] [Fintype G] [Fintype S]
  {sim : I → C → Option P} {prog : I → C → S → S} {Acc : Out → S → Prop}
  {Fresh : List (Option (I × P)) → Out → Prop} {Rel : Out → W → Prop}
  {ext : List (Option (I × P)) → ((Fin N → G) → S → Out) → (Fin N → G) → S → W}

theorem WeakSEN.mono {Adm Adm' : ((Fin N → G) → S → Out) → Prop} {ε ε' : ℝ}
    (h : WeakSEN N sim prog Acc Fresh Rel ext Adm ε) (hA : ∀ F, Adm' F → Adm F) (hε : ε ≤ ε') :
    WeakSEN N sim prog Acc Fresh Rel ext Adm' ε' :=
  fun α _ _ x out hout => (h α x out fun a l => hA _ (hout a l)).trans hε

/-- **Non-vacuity**: every simulator is weakly simulation-extractable with error `1`. -/
theorem weakSEN_one (N : ℕ) (sim : I → C → Option P) (prog : I → C → S → S) (Acc : Out → S → Prop)
    (Fresh : List (Option (I × P)) → Out → Prop) (Rel : Out → W → Prop)
    (ext : List (Option (I × P)) → ((Fin N → G) → S → Out) → (Fin N → G) → S → W)
    (Adm : ((Fin N → G) → S → Out) → Prop) : WeakSEN N sim prog Acc Fresh Rel ext Adm 1 :=
  fun _ _ _ _ _ _ => pr_le_one _

/-- **Weak simulation-extractability bounds the simulated game.** For a game whose simulated
slots are the simulator's proofs of statements `x ω l` chosen from the log, and an event
`Acc ∧ Fresh ∧ ¬ Rel` of the adversary's output `out ω l`. -/
theorem simGN_le_of_weakSEN {Ω ρ : Type} [Fintype Ω] [Nonempty Ω] [Fintype ρ] [Nonempty ρ]
    [Nonempty G] {Adm : ((Fin N → G) → S → Out) → Prop} {ε : ℝ}
    (hse : WeakSEN N sim prog Acc Fresh Rel ext Adm ε)
    (x : Ω → List (Option (I × P)) → Option I)
    (out : Ω → List (Option (I × P)) → (Fin N → G) → S → Out) (hA : ∀ ω l, Adm (out ω l)) :
    pr ((Ω × (Fin N → Slot ρ C G)) × S)
      (simGN (fun ω l c => pairO (x ω l) (simO sim (x ω l) c))
        (fun ω l c => progO prog (x ω l) c)
        (fun ω l g s => Acc (out ω l g s) s ∧ Fresh l (out ω l g s) ∧
          ¬ Rel (out ω l g s) (ext l (out ω l) g s))) ≤ ε := by
  have h := hse (Ω × (Fin N → ρ)) (fun a => x a.1) (fun a => out a.1) fun a l => hA a.1 l
  let e : (Ω × (Fin N → Slot ρ C G)) × S ≃ ((Ω × (Fin N → ρ)) × (Fin N → C × G)) × S :=
    { toFun := fun z => (((z.1.1, fun j => (z.1.2 j).1.1), fun j => ((z.1.2 j).1.2, (z.1.2 j).2)),
        z.2)
      invFun := fun y => ((y.1.1.1, fun j => ((y.1.1.2 j, (y.1.2 j).1), (y.1.2 j).2)), y.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hm : ∀ (a : Ω × (Fin N → ρ)) (cs : ℕ → C),
      simPre (fun (a : Ω × (Fin N → ρ)) l c => pairO (x a.1 l) (simO sim (x a.1 l) c))
        (fun (a : Ω × (Fin N → ρ)) l c => progO prog (x a.1 l) c) a cs N =
      simPre (fun ω l c => pairO (x ω l) (simO sim (x ω l) c))
        (fun ω l c => progO prog (x ω l) c) a.1 cs N :=
    fun a cs => simPre_map (fun a : Ω × (Fin N → ρ) => a.1)
      (fun ω l c => pairO (x ω l) (simO sim (x ω l) c)) (fun ω l c => progO prog (x ω l) c) a cs N
  simp only [hm] at h
  refine le_of_eq_of_le ?_ h
  rw [← pr_equiv e]
  rfl

end SE

end VoleMole.Theft
