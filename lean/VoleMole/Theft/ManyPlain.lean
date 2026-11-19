import VoleMole.Theft.Many

/-!
# `WeakSEN` and simpler hypotheses

`WeakSEN` (`Theft/Many.lean`) is weak simulation-extractability against adversaries that see `N`
simulated proofs. It is the hypothesis of the many-token theft theorems. This file relates it to
simpler statements, in the table model of the zero-knowledge theorems. Nothing here is specific
to a protocol or to the Lean prover.

* **Two proof systems as one, with optional proofs** (`sumProveO`, `sumSimO`, `zk_sumO_inl`,
  `zk_sumO_inr`): as `sumProve`, `sumSim` of `Theft/Many.lean`, for provers and simulators that
  may abort and whose proofs and witnesses have different types.
* **`weakSE2_of_weakSEN`**: `WeakSEN` at `N = 2`, for the sum of two proof systems, implies
  `WeakSE2` (`Theft/Basic.lean`) for the two systems, with the same error. The converse is not
  claimed: a `WeakSEN` adversary may ask for two proofs of the same relation, a `WeakSE2`
  adversary gets one of each.
* **`PlainSEN`**: extraction with **no simulated proofs and no programming**. The adversary has
  advice `a`, a public log `lg a` of "honest" statement–proof pairs (any values independent of the
  tables; they only define freshness) and a last stage `F a g s` on uniform tables. The extractor
  `e` sees the log, the output, the slices and the part `s.2` of the tables that the simulators do
  not program.
* **`ProgMovesN`**: in `WeakSEN`'s game, the adversary's fresh output is accepted on the programmed
  tables and rejected on the unprogrammed ones.
* **`weakSEN_of_plain`**: if the programming leaves `s.2` unchanged, the extractor reads only `s.2`
  (`extOfN e`), and the last stage composed with `N` programmings (`IsProgs`) is admissible for
  plain extraction, then `WeakSEN ≤ ε_plain + ε_moves`. This is `weakSE2_of_plain`
  (`Theft/SimExtract.lean`) for `N` simulated proofs.
* **`progMovesN_of_slots`**: the programming term, one summand per simulated proof. The programmed
  part of the tables is a function `K → V`. If a verifier that the programming moves reads a moved
  key (`hE`, with `Pt o s k`: "`k` is a key the verifier of `o` reads"), and the programming of
  one proof moves only keys in a set fixed by its statement, its coins and `s.2` (`hM`, `Mv`),
  then

      ε_moves ≤ Σ_i ε_i,

  `ε_i` the probability that the fresh output's verifier reads a key that simulated proof `i` may
  program (`SlotEvN i`). `simPre_moved` is the step: a key moved by the composition of the
  programmings is moved by one of them.

`PlainSEN` and `SlotEvN` are hypotheses, as `PlainSE` and `ProgEv` are for two proofs.
-/

open Finset

namespace VoleMole.Theft

open VoleMole.Privacy

/-! ## Two proof systems as one, with optional proofs -/

section SumO

variable {I₁ I₂ W₁ W₂ P₁ P₂ ρ C₁ C₂ G S : Type}

/-- Two provers that may abort as one, on the sum of the instance types; the witness is a pair,
one component per relation. -/
def sumProveO (p₁ : I₁ → W₁ → ρ → G → S → Option P₁) (p₂ : I₂ → W₂ → ρ → G → S → Option P₂)
    (x : I₁ ⊕ I₂) (w : W₁ × W₂) (r : ρ) (g : G) (s : S) : Option (P₁ ⊕ P₂) :=
  match x with
  | .inl x => (p₁ x w.1 r g s).map Sum.inl
  | .inr x => (p₂ x w.2 r g s).map Sum.inr

/-- Two simulators that may abort as one, with coins for both. -/
def sumSimO (s₁ : I₁ → C₁ → Option P₁) (s₂ : I₂ → C₂ → Option P₂) (x : I₁ ⊕ I₂) (c : C₁ × C₂) :
    Option (P₁ ⊕ P₂) :=
  match x with
  | .inl x => (s₁ x c.1).map Sum.inl
  | .inr x => (s₂ x c.2).map Sum.inr

/-- The first relation, on the sum of the instance types and pairs of witnesses. -/
def RelOInl (R₁ : I₁ → W₁ → Prop) (x : I₁ ⊕ I₂) (w : W₁ × W₂) : Prop :=
  match x with
  | .inl x => R₁ x w.1
  | .inr _ => False

/-- The second relation, on the sum of the instance types and pairs of witnesses. -/
def RelOInr (R₂ : I₂ → W₂ → Prop) (x : I₁ ⊕ I₂) (w : W₁ × W₂) : Prop :=
  match x with
  | .inl _ => False
  | .inr x => R₂ x w.2

variable [Fintype ρ] [Fintype C₁] [Fintype C₂] [Fintype G] [Fintype S]
  {p₁ : I₁ → W₁ → ρ → G → S → Option P₁} {p₂ : I₂ → W₂ → ρ → G → S → Option P₂}
  {s₁ : I₁ → C₁ → Option P₁} {s₂ : I₂ → C₂ → Option P₂} {g₁ : I₁ → C₁ → S → S}
  {g₂ : I₂ → C₂ → S → S}

/-- **Zero knowledge of the first proof system, on the sum.** -/
theorem zk_sumO_inl [Nonempty C₂] {R₁ : I₁ → W₁ → Prop}
    {Adm : (Option P₁ → G → S → Prop) → Prop} {ε : ℝ} (hzk : ZeroKnowledgeRO R₁ p₁ s₁ g₁ Adm ε) :
    ZeroKnowledgeRO (RelOInl (I₂ := I₂) (W₂ := W₂) R₁) (sumProveO p₁ p₂) (sumSimO s₁ s₂)
      (sumProg g₁ g₂) (fun D => Adm (fun o g s => D (o.map Sum.inl) g s)) ε := by
  intro x w hxw D hD
  rcases x with x | x
  · have h := hzk x w.1 hxw _ hD
    let e : ((C₁ × C₂) × G) × S ≃ C₂ × ((C₁ × G) × S) :=
      { toFun := fun a => (a.1.1.2, ((a.1.1.1, a.1.2), a.2))
        invFun := fun y => (((y.2.1.1, y.1), y.2.1.2), y.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e1 := pr_equiv e (fun y : C₂ × ((C₁ × G) × S) =>
      D ((s₁ x y.2.1.1).map Sum.inl) y.2.1.2 (g₁ x y.2.1.1 y.2.2))
    rw [pr_prod_snd (α := C₂) (fun y : (C₁ × G) × S =>
      D ((s₁ x y.1.1).map Sum.inl) y.1.2 (g₁ x y.1.1 y.2))] at e1
    simp only [sumProveO, sumSimO, sumProg]
    rw [← e1] at h
    exact h
  · exact hxw.elim

/-- **Zero knowledge of the second proof system, on the sum.** -/
theorem zk_sumO_inr [Nonempty C₁] {R₂ : I₂ → W₂ → Prop}
    {Adm : (Option P₂ → G → S → Prop) → Prop} {ε : ℝ} (hzk : ZeroKnowledgeRO R₂ p₂ s₂ g₂ Adm ε) :
    ZeroKnowledgeRO (RelOInr (I₁ := I₁) (W₁ := W₁) R₂) (sumProveO p₁ p₂) (sumSimO s₁ s₂)
      (sumProg g₁ g₂) (fun D => Adm (fun o g s => D (o.map Sum.inr) g s)) ε := by
  intro x w hxw D hD
  rcases x with x | x
  · exact hxw.elim
  · have h := hzk x w.2 hxw _ hD
    let e : ((C₁ × C₂) × G) × S ≃ C₁ × ((C₂ × G) × S) :=
      { toFun := fun a => (a.1.1.1, ((a.1.1.2, a.1.2), a.2))
        invFun := fun y => (((y.1, y.2.1.1), y.2.1.2), y.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e1 := pr_equiv e (fun y : C₁ × ((C₂ × G) × S) =>
      D ((s₂ x y.2.1.1).map Sum.inr) y.2.1.2 (g₂ x y.2.1.1 y.2.2))
    rw [pr_prod_snd (α := C₁) (fun y : (C₂ × G) × S =>
      D ((s₂ x y.1.1).map Sum.inr) y.1.2 (g₂ x y.1.1 y.2))] at e1
    simp only [sumProveO, sumSimO, sumProg]
    rw [← e1] at h
    exact h

end SumO

/-! ## The game of `WeakSEN` -/

section Game

variable {α I P C S : Type}

/-- **The log and the programming of `WeakSEN`'s game** after `n` simulated proofs: the adversary
with coins `a` chooses statement `x a l` from the log `l`, the simulator has coins `cs`. -/
def seLog (sim : I → C → Option P) (prog : I → C → S → S)
    (x : α → List (Option (I × P)) → Option I) (a : α) (cs : ℕ → C) (n : ℕ) :
    List (Option (I × P)) × (S → S) :=
  simPre (fun a l c => pairO (x a l) (simO sim (x a l) c)) (fun a l c => progO prog (x a l) c) a
    cs n

/-- **A composition of `n` programmings** of optional statements. -/
inductive IsProgs (prog : I → C → S → S) : ℕ → (S → S) → Prop
  | zero : IsProgs prog 0 id
  | succ {n : ℕ} {L : S → S} (x : Option I) (c : C) :
      IsProgs prog n L → IsProgs prog (n + 1) (L ∘ progO prog x c)

theorem seLog_isProgs (sim : I → C → Option P) (prog : I → C → S → S)
    (x : α → List (Option (I × P)) → Option I) (a : α) (cs : ℕ → C) :
    ∀ n, IsProgs prog n (seLog sim prog x a cs n).2
  | 0 => .zero
  | n + 1 => .succ _ _ (seLog_isProgs sim prog x a cs n)

end Game

section Snd

variable {I C A B : Type}

lemma progO_snd' {prog : I → C → A × B → A × B} (hp : ∀ x c s, (prog x c s).2 = s.2)
    (x : Option I) (c : C) (s : A × B) : (progO prog x c s).2 = s.2 := by
  rcases x with _ | x
  · rfl
  · exact hp x c s

/-- A composition of programmings that leave `s.2` unchanged leaves it unchanged. -/
theorem IsProgs.snd {prog : I → C → A × B → A × B} (hp : ∀ x c s, (prog x c s).2 = s.2) {n : ℕ}
    {L : A × B → A × B} (h : IsProgs prog n L) (s : A × B) : (L s).2 = s.2 := by
  induction h generalizing s with
  | zero => rfl
  | succ x c _ ih => rw [Function.comp_apply, ih, progO_snd' hp]

end Snd

/-! ## `WeakSEN` at `N = 2` implies `WeakSE2` -/

section Two

variable {I₁ I₂ P₁ P₂ C₁ C₂ G S Out W : Type}

/-- The first entry of a log, if it is a proof of the first relation. -/
def logFst : List (Option ((I₁ ⊕ I₂) × (P₁ ⊕ P₂))) → Option (I₁ × P₁)
  | some (.inl x, .inl π) :: _ => some (x, π)
  | _ => none

/-- The second entry of a log, if it is a proof of the second relation. -/
def logSnd : List (Option ((I₁ ⊕ I₂) × (P₁ ⊕ P₂))) → Option (I₂ × P₂)
  | _ :: some (.inr x, .inr π) :: _ => some (x, π)
  | _ => none

lemma logFst_pair (sim₁ : I₁ → C₁ → Option P₁) (sim₂ : I₂ → C₂ → Option P₂) (x : Option I₁)
    (c : C₁ × C₂) (t : List (Option ((I₁ ⊕ I₂) × (P₁ ⊕ P₂)))) :
    logFst (pairO (x.map Sum.inl) (simO (sumSimO sim₁ sim₂) (x.map Sum.inl) c) :: t) =
      pairO x (simO sim₁ x c.1) := by
  rcases x with _ | x
  · rfl
  · simp only [Option.map_some, simO, sumSimO]
    cases sim₁ x c.1 <;> rfl

lemma logSnd_pair (sim₁ : I₁ → C₁ → Option P₁) (sim₂ : I₂ → C₂ → Option P₂) (x : Option I₂)
    (c : C₁ × C₂) (e : Option ((I₁ ⊕ I₂) × (P₁ ⊕ P₂))) :
    logSnd [e, pairO (x.map Sum.inr) (simO (sumSimO sim₁ sim₂) (x.map Sum.inr) c)] =
      pairO x (simO sim₂ x c.2) := by
  rcases x with _ | x
  · rfl
  · simp only [Option.map_some, simO, sumSimO]
    cases sim₂ x c.2 <;> rfl

lemma pairO_snd {I P C : Type} (sim : I → C → Option P) (x : Option I) (c : C) :
    (pairO x (simO sim x c)).map Prod.snd = simO sim x c := by
  rcases x with _ | x
  · rfl
  · simp only [simO]
    cases sim x c <;> rfl

lemma progO_sum_inl (prog₁ : I₁ → C₁ → S → S) (prog₂ : I₂ → C₂ → S → S) (x : Option I₁)
    (c : C₁ × C₂) (s : S) :
    progO (sumProg prog₁ prog₂) (x.map Sum.inl) c s = progO prog₁ x c.1 s := by
  rcases x with _ | x <;> rfl

lemma progO_sum_inr (prog₁ : I₁ → C₁ → S → S) (prog₂ : I₂ → C₂ → S → S) (x : Option I₂)
    (c : C₁ × C₂) (s : S) :
    progO (sumProg prog₁ prog₂) (x.map Sum.inr) c s = progO prog₂ x c.2 s := by
  rcases x with _ | x <;> rfl

/-- The statements of the `WeakSEN` adversary built from a `WeakSE2` adversary. -/
def twoX {α : Type} (x₁ : α → Option I₁) (x₂ : α → Option P₁ → Option I₂) (a : α)
    (l : List (Option ((I₁ ⊕ I₂) × (P₁ ⊕ P₂)))) : Option (I₁ ⊕ I₂) :=
  match l with
  | [] => (x₁ a).map Sum.inl
  | [_] => (x₂ a ((logFst l).map Prod.snd)).map Sum.inr
  | _ => none

variable [Fintype C₁] [Nonempty C₁] [Fintype C₂] [Nonempty C₂] [Fintype G] [Fintype S]

/-- The tape of `WeakSEN` at `N = 2` on the sum of two systems is the tape of `WeakSE2` and two
unused coins. -/
def twoEquiv (α : Type) : (α × (Fin 2 → (C₁ × C₂) × G)) × S ≃
    (C₂ × C₁) × ((α × (C₁ × G)) × ((C₂ × G) × S)) where
  toFun z := (((z.1.2 0).1.2, (z.1.2 1).1.1),
    ((z.1.1, ((z.1.2 0).1.1, (z.1.2 0).2)), (((z.1.2 1).1.2, (z.1.2 1).2), z.2)))
  invFun y := ((y.2.1.1, ![((y.2.1.2.1, y.1.1), y.2.1.2.2), ((y.1.2, y.2.2.1.1), y.2.2.1.2)]),
    y.2.2.2)
  left_inv z := by
    refine Prod.ext (Prod.ext rfl (funext fun i => ?_)) rfl
    fin_cases i <;> rfl
  right_inv _ := rfl

/-- **`WeakSEN` with two simulated proofs implies `WeakSE2`.** If the sum of two proof systems is
weakly simulation-extractable against adversaries that see two simulated proofs, the two systems
are weakly simulation-extractable in the sense of `Theft/Basic.lean` (one proof of each), with
the same error. Freshness, the extractor and the admissible class are read off the first two
entries of the log. -/
theorem weakSE2_of_weakSEN {sim₁ : I₁ → C₁ → Option P₁} {prog₁ : I₁ → C₁ → S → S}
    {sim₂ : I₂ → C₂ → Option P₂} {prog₂ : I₂ → C₂ → S → S} {Acc : Out → S → Prop}
    {Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop} {Rel : Out → W → Prop}
    {ext : Option (I₁ × P₁) → Option (I₂ × P₂) → (G → G → S → Out) → G → G → S → W}
    {Adm : (G → G → S → Out) → Prop} {ε : ℝ}
    (h : WeakSEN 2 (sumSimO sim₁ sim₂) (sumProg prog₁ prog₂) Acc
      (fun l o => Fresh (logFst l) (logSnd l) o) Rel
      (fun l F g s => ext (logFst l) (logSnd l) (fun g₁ g₂ => F ![g₁, g₂]) (g 0) (g 1) s)
      (fun F => Adm (fun g₁ g₂ => F ![g₁, g₂])) ε) :
    WeakSE2 sim₁ prog₁ sim₂ prog₂ Acc Fresh Rel ext Adm ε := by
  intro α _ _ x₁ x₂ out hout
  have H := h α (twoX x₁ x₂)
    (fun a l g s => out a ((logFst l).map Prod.snd) ((logSnd l).map Prod.snd) (g 0) (g 1) s)
    (fun a l => hout a _ _)
  rw [← pr_prod_snd (α := C₂ × C₁), ← pr_equiv (twoEquiv α)]
  refine le_of_eq_of_le (pr_congr fun z => ?_) H
  have e0 : extN (fun j => (z.1.2 j).1) 0 = (z.1.2 0).1 := extN_val (fun j => (z.1.2 j).1) 0
  have e1 : extN (fun j => (z.1.2 j).1) 1 = (z.1.2 1).1 := extN_val (fun j => (z.1.2 j).1) 1
  have hg : (![(z.1.2 0).2, (z.1.2 1).2] : Fin 2 → G) = fun j => (z.1.2 j).2 := by
    funext j; fin_cases j <;> rfl
  simp only [simPre, List.nil_append, List.cons_append, twoX, e0, e1, logFst_pair, logSnd_pair,
    pairO_snd, progO_sum_inl, progO_sum_inr, Function.comp_apply, id_eq, twoEquiv]
  rfl

end Two

/-! ## Plain extraction and the programming step, for `N` simulated proofs -/

section Plain

variable {N : ℕ} {I P C G A B Out W : Type}

/-- **An extractor that does not read the programmed part** of the tables: it sees the log, the
adversary's output, the slices and `s.2`. -/
def extOfN (e : List (Option (I × P)) → Out → (Fin N → G) → B → W) :
    List (Option (I × P)) → ((Fin N → G) → A × B → Out) → (Fin N → G) → A × B → W :=
  fun l F g s => e l (F g s) g s.2

variable [Fintype G] [Fintype A] [Fintype B]

/-- **Plain extraction** (no simulated proofs, no programming), with error `ε`, against the
adversaries `Adm` admits. The adversary has advice `a`, a log `lg a` of honest statement–proof
pairs that defines freshness (any values, not read off the tables) and a last stage `F a` on
uniform slices and tables. The extractor `e` sees the log, the output, the slices and `s.2`. -/
def PlainSEN (N : ℕ) (Acc : Out → A × B → Prop) (Fresh : List (Option (I × P)) → Out → Prop)
    (Rel : Out → W → Prop) (e : List (Option (I × P)) → Out → (Fin N → G) → B → W)
    (Adm : ((Fin N → G) → A × B → Out) → Prop) (ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [Nonempty α] (lg : α → List (Option (I × P)))
    (F : α → (Fin N → G) → A × B → Out), (∀ a, Adm (F a)) →
    pr (α × ((Fin N → G) × (A × B))) (fun z =>
      Acc (F z.1 z.2.1 z.2.2) z.2.2 ∧ Fresh (lg z.1) (F z.1 z.2.1 z.2.2) ∧
        ¬ Rel (F z.1 z.2.1 z.2.2) (e (lg z.1) (F z.1 z.2.1 z.2.2) z.2.1 z.2.2.2)) ≤ ε

/-- **Non-vacuity.** -/
theorem plainSEN_one (N : ℕ) (Acc : Out → A × B → Prop)
    (Fresh : List (Option (I × P)) → Out → Prop) (Rel : Out → W → Prop)
    (e : List (Option (I × P)) → Out → (Fin N → G) → B → W)
    (Adm : ((Fin N → G) → A × B → Out) → Prop) : PlainSEN N Acc Fresh Rel e Adm 1 :=
  fun _ _ _ _ _ _ => pr_le_one _

variable [Fintype C] [Nonempty C]

/-- **The programming moves the verifier**, with probability at most `ε`: in `WeakSEN`'s game the
adversary's output is fresh, accepted on the programmed tables and rejected on the unprogrammed
ones. -/
def ProgMovesN (N : ℕ) (sim : I → C → Option P) (prog : I → C → A × B → A × B)
    (Acc : Out → A × B → Prop) (Fresh : List (Option (I × P)) → Out → Prop)
    (Adm : ((Fin N → G) → A × B → Out) → Prop) (ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [Nonempty α] (x : α → List (Option (I × P)) → Option I)
    (out : α → List (Option (I × P)) → (Fin N → G) → A × B → Out), (∀ a l, Adm (out a l)) →
    pr ((α × (Fin N → C × G)) × (A × B)) (fun z =>
      Fresh (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).1
          (out z.1.1 (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).1
            (fun j => (z.1.2 j).2)
            ((seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2)) ∧
        Acc (out z.1.1 (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).1
            (fun j => (z.1.2 j).2)
            ((seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2))
          ((seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2) ∧
        ¬ Acc (out z.1.1 (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).1
            (fun j => (z.1.2 j).2)
            ((seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2)) z.2) ≤ ε

theorem progMovesN_one (N : ℕ) (sim : I → C → Option P) (prog : I → C → A × B → A × B)
    (Acc : Out → A × B → Prop) (Fresh : List (Option (I × P)) → Out → Prop)
    (Adm : ((Fin N → G) → A × B → Out) → Prop) : ProgMovesN N sim prog Acc Fresh Adm 1 :=
  fun _ _ _ _ _ _ => pr_le_one _

/-- The reduction's tape: the advice is the adversary's coins and the simulators' coins. -/
def seEquivN (α : Type) : (α × (Fin N → C × G)) × (A × B) ≃
    (α × (Fin N → C)) × ((Fin N → G) × (A × B)) where
  toFun z := ((z.1.1, fun j => (z.1.2 j).1), (fun j => (z.1.2 j).2, z.2))
  invFun y := ((y.1.1, fun j => (y.1.2 j, y.2.1 j)), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Weak simulation-extractability with `N` simulated proofs, from plain extraction.** If the
simulator's programming leaves `s.2` unchanged and the adversary's last stage composed with `N`
programmings is admissible for plain extraction, the extractor `extOfN e` (which reads only
`s.2`) is weakly simulation-extractable with error `ε_plain + ε_moves`. -/
theorem weakSEN_of_plain {sim : I → C → Option P} {prog : I → C → A × B → A × B}
    {Acc : Out → A × B → Prop} {Fresh : List (Option (I × P)) → Out → Prop} {Rel : Out → W → Prop}
    {e : List (Option (I × P)) → Out → (Fin N → G) → B → W}
    {Adm Adm₀ : ((Fin N → G) → A × B → Out) → Prop} {ε₀ εm : ℝ}
    (hplain : PlainSEN N Acc Fresh Rel e Adm₀ ε₀)
    (hmoves : ProgMovesN N sim prog Acc Fresh Adm εm)
    (hp : ∀ x c s, (prog x c s).2 = s.2)
    (hadm : ∀ F L, IsProgs prog N L → Adm F → Adm₀ (fun g s => F g (L s))) :
    WeakSEN N sim prog Acc Fresh Rel (extOfN e) Adm (ε₀ + εm) := by
  intro α _ _ x out hout
  have hP := hplain (α × (Fin N → C)) (fun b => (seLog sim prog x b.1 (extN b.2) N).1)
    (fun b g s => out b.1 (seLog sim prog x b.1 (extN b.2) N).1 g
      ((seLog sim prog x b.1 (extN b.2) N).2 s))
    fun b => hadm _ _ (seLog_isProgs sim prog x b.1 (extN b.2) N) (hout _ _)
  rw [← pr_equiv (seEquivN α)] at hP
  have hM := hmoves α x out hout
  refine (pr_mono fun z hz => ?_).trans ((pr_or_le _ _).trans (add_le_add hP hM))
  obtain ⟨hacc, hfr, hrel⟩ := hz
  have e2 := (seLog_isProgs sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).snd hp z.2
  by_cases h : Acc (out z.1.1 (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).1
      (fun j => (z.1.2 j).2) ((seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2)) z.2
  · left
    refine ⟨h, hfr, ?_⟩
    simp only [extOfN] at hrel
    simp only [seLog] at e2
    rw [e2] at hrel
    exact hrel
  · right
    exact ⟨hfr, hacc, h⟩

end Plain

/-! ## The programming term, one summand per simulated proof -/

section Moved

variable {Ω O C K V B : Type} (Sm : Ω → List O → C → O)
  (pg : Ω → List O → C → (K → V) × B → (K → V) × B)

/-- **A key moved by the composition of the programmings is moved by one of them**, on tables
with the same unprogrammed part. -/
theorem simPre_moved (hpg : ∀ ω l c s, (pg ω l c s).2 = s.2) (ω : Ω) (cs : ℕ → C) (k : K) :
    ∀ (n : ℕ) (s : (K → V) × B), ((simPre Sm pg ω cs n).2 s).1 k ≠ s.1 k →
      ∃ i < n, ∃ t : (K → V) × B, t.2 = s.2 ∧
        (pg ω (simPre Sm pg ω cs i).1 (cs i) t).1 k ≠ t.1 k
  | 0, _, h => (h rfl).elim
  | n + 1, s, h => by
    by_cases hk : (pg ω (simPre Sm pg ω cs n).1 (cs n) s).1 k = s.1 k
    · have h' : ((simPre Sm pg ω cs n).2 (pg ω (simPre Sm pg ω cs n).1 (cs n) s)).1 k ≠
          (pg ω (simPre Sm pg ω cs n).1 (cs n) s).1 k := by
        rw [hk]; exact h
      obtain ⟨i, hi, t, ht, hm⟩ := simPre_moved hpg ω cs k n _ h'
      exact ⟨i, by omega, t, ht.trans (hpg _ _ _ _), hm⟩
    · exact ⟨n, by omega, s, rfl, hk⟩

end Moved

section Slots

variable {N : ℕ} {I P C G K V B Out : Type} [Fintype C] [Nonempty C] [Fintype G] [Fintype (K → V)]
  [Fintype B]

/-- **An event of simulated proof `i`**, with probability at most `ε`: in `WeakSEN`'s game, the
adversary's output `o` is fresh, the `i`-th statement `x_i` exists, and `E x_i c_i o s` holds for
the simulator's coins `c_i` of that proof and the unprogrammed tables `s`. -/
def SlotEvN (N : ℕ) (i : Fin N) (sim : I → C → Option P)
    (prog : I → C → (K → V) × B → (K → V) × B) (Fresh : List (Option (I × P)) → Out → Prop)
    (E : I → C → Out → (K → V) × B → Prop) (Adm : ((Fin N → G) → (K → V) × B → Out) → Prop)
    (ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [Nonempty α] (x : α → List (Option (I × P)) → Option I)
    (out : α → List (Option (I × P)) → (Fin N → G) → (K → V) × B → Out), (∀ a l, Adm (out a l)) →
    pr ((α × (Fin N → C × G)) × ((K → V) × B)) (fun z =>
      Fresh (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).1
          (out z.1.1 (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).1
            (fun j => (z.1.2 j).2)
            ((seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2)) ∧
        ∃ xi, x z.1.1 (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) i).1 = some xi ∧
          E xi (z.1.2 i).1
            (out z.1.1 (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).1
              (fun j => (z.1.2 j).2)
              ((seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2)) z.2) ≤ ε

theorem slotEvN_one (N : ℕ) (i : Fin N) (sim : I → C → Option P)
    (prog : I → C → (K → V) × B → (K → V) × B) (Fresh : List (Option (I × P)) → Out → Prop)
    (E : I → C → Out → (K → V) × B → Prop) (Adm : ((Fin N → G) → (K → V) × B → Out) → Prop) :
    SlotEvN N i sim prog Fresh E Adm 1 :=
  fun _ _ _ _ _ _ => pr_le_one _

/-- **The programming term is a sum over the simulated proofs.** If a verifier moved by a
programming that leaves `s.2` unchanged reads a moved key (`hE`), and the programming of a
statement moves only keys in `Mv x c s.2` (`hM`), the programming moves the verifier with
probability at most `Σ_i ε_i`, where `ε_i` bounds the event that the fresh output's verifier reads
a key that simulated proof `i` may program. -/
theorem progMovesN_of_slots {sim : I → C → Option P} {prog : I → C → (K → V) × B → (K → V) × B}
    {Acc : Out → (K → V) × B → Prop} {Fresh : List (Option (I × P)) → Out → Prop}
    {Pt : Out → (K → V) × B → K → Prop} {Mv : I → C → B → K → Prop}
    {Adm : ((Fin N → G) → (K → V) × B → Out) → Prop} {εh : Fin N → ℝ}
    (hp : ∀ x c s, (prog x c s).2 = s.2)
    (hE : ∀ o s' s, s'.2 = s.2 → Acc o s' → ¬ Acc o s → ∃ k, Pt o s k ∧ s'.1 k ≠ s.1 k)
    (hM : ∀ x c s k, (prog x c s).1 k ≠ s.1 k → Mv x c s.2 k)
    (hs : ∀ i, SlotEvN N i sim prog Fresh (fun x c o s => ∃ k, Pt o s k ∧ Mv x c s.2 k) Adm
      (εh i)) :
    ProgMovesN N sim prog Acc Fresh Adm (∑ i, εh i) := by
  intro α _ _ x out hout
  let Q : Fin N → (α × (Fin N → C × G)) × ((K → V) × B) → Prop := fun i z =>
    Fresh (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).1
        (out z.1.1 (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).1
          (fun j => (z.1.2 j).2)
          ((seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2)) ∧
      ∃ xi, x z.1.1 (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) i).1 = some xi ∧
        ∃ k, Pt (out z.1.1 (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).1
            (fun j => (z.1.2 j).2)
            ((seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).2 z.2)) z.2 k ∧
          Mv xi (z.1.2 i).1 z.2.2 k
  have h3 : ∀ i, pr _ (Q i) ≤ εh i := fun i => hs i α x out hout
  refine (pr_mono (Q := fun z => ∃ i, Q i z) fun z hz => ?_).trans
    ((pr_exists_le_sum Q).trans (Finset.sum_le_sum fun i _ => h3 i))
  obtain ⟨hfr, hacc, hrej⟩ := hz
  have hsnd := (seLog_isProgs sim prog x z.1.1 (extN fun j => (z.1.2 j).1) N).snd hp z.2
  obtain ⟨k, hk, hne⟩ := hE _ _ _ hsnd hacc hrej
  obtain ⟨i, hi, t, ht, hm⟩ := simPre_moved
    (fun a l c => pairO (x a l) (simO sim (x a l) c)) (fun a l c => progO prog (x a l) c)
    (fun a l c s => progO_snd' hp _ c s) z.1.1 (extN fun j => (z.1.2 j).1) k N z.2 hne
  refine ⟨⟨i, hi⟩, hfr, ?_⟩
  have hc : extN (fun j => (z.1.2 j).1) i = (z.1.2 ⟨i, hi⟩).1 :=
    extN_val (fun j => (z.1.2 j).1) ⟨i, hi⟩
  rw [hc] at hm
  cases hx : x z.1.1 (seLog sim prog x z.1.1 (extN fun j => (z.1.2 j).1) i).1 with
  | none =>
    simp only [seLog] at hx
    rw [hx] at hm
    exact (hm rfl).elim
  | some xi =>
    refine ⟨xi, rfl, k, hk, ?_⟩
    simp only [seLog] at hx
    rw [hx] at hm
    rw [← ht]
    exact hM xi _ t k hm

end Slots

end VoleMole.Theft
