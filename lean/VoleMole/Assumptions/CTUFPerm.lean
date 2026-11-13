import VoleMole.Assumptions.LazyPerm
import VoleMole.Assumptions.CTUFOpenOMPR

/-!
# CT-UF^open with `Com` a random permutation with inverse queries (T4, permutation model)

`lean/docs/security/uov-assumptions.md` §5.4. In the standalone CT-UF^open game, KP800 is a
random permutation `π` of the blocks `T × Z` (`T = F^{45}`, the truncation `Com` reads; `Z` the
rest), lazily sampled (`LazyPerm.rpImpl`), with forward **and inverse** queries. `Com(x)` is the
first component of `π(emb x)`, for an injective encoding `emb : Xc → T × Z` of the openings (the
structured inputs: 576 free bits, 224 fixed).

* **The game** `advCTUFPermAt V σ emb F`: the forger (`specCP`: the world, the `K` signers on
  `(k, t)`, and `π`) returns a forgery `(k, x*, s*)` and openings; the challenger evaluates `π`
  forward at `emb x*` and at every opening (`cpFinal`); the win `CPWin` is `CIWin` with `Com` read
  off the permutation's table (`comP`).
* **The step to the random function** (`advCTUFPermAt_le_rf`): with at most `q_f` forward, `q_i`
  inverse and `q_S` signing queries and `q_S` openings (`CPBudget`), the permutation can be
  replaced by a two-sided random function (`LazyPerm.prEvent_rp_le_rf`, `q = q_f + q_i + q_S + 1`
  queries read it), and the event that an inverse answer is a structured input has probability
  `≤ q_i·|Xc|/|B|` (`LazyPerm.prEvent_invHit_le`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.Assumptions.LazyPerm VoleMole.ROM.OneMore
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.CTUFPerm

section Game

variable {DR : Type} (AR : DR → Type) (K : ℕ) (T Z S : Type)

/-- **The permutation-model forger's oracles**: the world, the `K` signers on `(k, t)`, and the
permutation of `T × Z` (forward and inverse). -/
abbrev specCP := specPm (AnsCO AR K T S) (T × Z)

variable {AR K T Z S} {Xc : Type}

/-- A forward permutation query. -/
def isFwd : (DR ⊕ (Fin K × T)) ⊕ (Bool × (T × Z)) → Bool
  | .inr (true, _) => true
  | _ => false

/-- A signing query. -/
def isSignP : (DR ⊕ (Fin K × T)) ⊕ (Bool × (T × Z)) → Bool
  | .inl (.inr _) => true
  | _ => false

/-- `π(b)`, as a query. -/
def fwdQ (b : T × Z) : OracleComp (specCP AR K T Z S) (T × Z) :=
  liftM ((specCP AR K T Z S).query (.inr (true, b)))

/-- **The challenger's final evaluations**: `π` forward at `emb x*` and at every opening. -/
def cpFinal (emb : Xc → T × Z) (o : CTOut K S Xc) : OracleComp (specCP AR K T Z S) (CTOut K S Xc) := do
  let _ ← ((o.1.map fun f => f.2.1).toList ++ o.2).mapM fun x => fwdQ (emb x)
  pure o

/-- **A permutation-model forger's budget**: at most `q_f` forward, `q_i` inverse and `q_S`
signing queries, at most `q_S` openings. -/
def CPBudget (qf qi qS : ℕ) (f : OracleComp (specCP AR K T Z S) (CTOut K S Xc)) : Prop :=
  IsQueryBoundP f (fun t => isFwd t = true) qf ∧ IsQueryBoundP f (fun t => isInv t = true) qi ∧
    IsQueryBoundP f (fun t => isSignP t = true) qS ∧ ∀ o ∈ support f, o.2.length ≤ qS

variable [DecidableEq T] [DecidableEq Z]

/-- `Com(x)` read off the permutation's table: the first component of `π(emb x)`, if recorded. -/
def comP (emb : Xc → T × Z) (L : PTab (T × Z)) (x : Xc) : Option T :=
  (fwdFind L (emb x)).map Prod.fst

variable (V : Fin K → S → T → Prop)

/-- **The permutation-model CT-UF^open win** (`CIWin` with `Com` read off the permutation). -/
def CPWin (emb : Xc → T × Z) (r : CTOut K S Xc × PTab (T × Z) × CISt AR K T) : Prop :=
  ∃ k x s c, r.1.1 = some (k, x, s) ∧ comP emb r.2.1 x = some c ∧ V k s c ∧
    (∀ q ∈ r.2.2.signed, q.2 ≠ c) ∧ ∀ q ∈ r.2.2.signed, ∃ x' ∈ r.1.2, comP emb r.2.1 x' = some q.2

variable [DecidableEq DR] [∀ d, SampleableType (AR d)] [SampleableType T] [SampleableType Z]
  [Fintype T] [Fintype Z]

/-- **The challenger with `π` a lazy random permutation**: the world and the signers `σ` as in
the function model (`ciOther`), `π` lazily. -/
noncomputable def cpImpl (σ : Fin K × T → S) :
    QueryImpl (specCP AR K T Z S) (StateT (PTab (T × Z) × CISt AR K T) ProbComp) :=
  rpImpl (A := AnsCO AR K T S) (fun _ => none) fun i _ => ciOther σ i

/-- The same challenger with a two-sided random function in place of `π` (the proof's hybrid). -/
def cfImpl (σ : Fin K × T → S) :
    QueryImpl (specCP AR K T Z S) (StateT (PTab (T × Z) × CISt AR K T) ProbComp) :=
  rfImpl (A := AnsCO AR K T S) (fun _ => none) fun i _ => ciOther σ i

/-- **The permutation-model CT-UF^open experiment**: the forger and the final evaluations. -/
noncomputable def cpRun (σ : Fin K × T → S) (emb : Xc → T × Z)
    (f : OracleComp (specCP AR K T Z S) (CTOut K S Xc)) :
    ProbComp (CTOut K S Xc × PTab (T × Z) × CISt AR K T) :=
  (simulateQ (cpImpl σ) (f >>= cpFinal emb)).run ([], ⟨∅, []⟩)

/-- **`Adv^{ct-uf-open}_K` with `Com` the first component of a random permutation with inverse
queries**, at fixed keys (signers `σ`, verification `V`). -/
noncomputable def advCTUFPermAt (σ : Fin K × T → S) (emb : Xc → T × Z)
    (F : ProbComp (OracleComp (specCP AR K T Z S) (CTOut K S Xc))) : ℝ≥0∞ :=
  Pr{let f ← F; let r ← cpRun σ emb f}[CPWin V emb r]

end Game

/-! ## Query bounds -/

section Bounds

variable {DR : Type} {AR : DR → Type} {K : ℕ} {T Z S Xc : Type}

theorem mapM_fwdQ_bound (p : (DR ⊕ (Fin K × T)) ⊕ (Bool × (T × Z)) → Prop) [DecidablePred p]
    (k : ℕ) (hk : ∀ b, p (.inr (true, b)) → 0 < k) (emb : Xc → T × Z) :
    ∀ xs : List Xc, IsQueryBoundP (xs.mapM fun x => fwdQ (AR := AR) (K := K) (S := S) (emb x)) p
      (xs.length * k)
  | [] => by simp
  | x :: xs => by
    rw [List.mapM_cons]
    refine ((isQueryBoundP_bind (n := k) (m := xs.length * k) ?_ fun y _ => ?_).mono
      (by simp [Nat.succ_mul, Nat.add_comm]))
    · exact (isQueryBoundP_query_iff p _ _).2 (hk _)
    · have h := mapM_fwdQ_bound p k hk emb xs
      rw [← Nat.add_zero (xs.length * k)]
      exact isQueryBoundP_bind h fun _ _ => isQueryBoundP_pure _ _ _

theorem cpFinal_bound (p : (DR ⊕ (Fin K × T)) ⊕ (Bool × (T × Z)) → Prop) [DecidablePred p]
    (_hp : ∀ b, p (.inr (true, b))) (emb : Xc → T × Z) (o : CTOut K S Xc) :
    IsQueryBoundP (cpFinal (AR := AR) emb o) p (o.2.length + 1) := by
  unfold cpFinal
  have h := mapM_fwdQ_bound (AR := AR) (K := K) (S := S) p 1 (fun _ _ => Nat.one_pos) emb
    ((o.1.map fun f => f.2.1).toList ++ o.2)
  refine ((isQueryBoundP_bind h fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_)
  cases o.1 <;> simp

theorem cpFinal_bound_zero (p : (DR ⊕ (Fin K × T)) ⊕ (Bool × (T × Z)) → Prop) [DecidablePred p]
    (hp : ∀ b, ¬p (.inr (true, b))) (emb : Xc → T × Z) (o : CTOut K S Xc) :
    IsQueryBoundP (cpFinal (AR := AR) emb o) p 0 := by
  unfold cpFinal
  have h := mapM_fwdQ_bound (AR := AR) (K := K) (S := S) p 0 (fun b h => absurd h (hp b)) emb
    ((o.1.map fun f => f.2.1).toList ++ o.2)
  simpa using isQueryBoundP_bind h fun _ _ => isQueryBoundP_pure _ _ 0

/-- A bound for a disjunction of two kinds is the sum of the bounds. -/
theorem isQueryBoundP_or {ι : Type} {spec : OracleSpec ι} {α : Type} (p q : ι → Prop)
    [DecidablePred p] [DecidablePred q] (oa : OracleComp spec α) :
    ∀ m n, IsQueryBoundP oa p m → IsQueryBoundP oa q n → IsQueryBoundP oa (fun t => p t ∨ q t) (m + n) := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro m n _ _; trivial
  | query_bind t k ih =>
    intro m n hm hn
    rw [isQueryBoundP_query_bind_iff] at hm hn ⊢
    refine ⟨?_, fun u => ?_⟩
    · by_cases h1 : p t
      · exact Or.inr (by have := hm.1.resolve_left (not_not.2 h1); omega)
      · by_cases h2 : q t
        · exact Or.inr (by have := hn.1.resolve_left (not_not.2 h2); omega)
        · exact Or.inl (by tauto)
    · have := ih u _ _ (hm.2 u) (hn.2 u)
      refine this.mono ?_
      have hm0 : p t → 0 < m := fun h => hm.1.resolve_left (not_not.2 h)
      have hn0 : q t → 0 < n := fun h => hn.1.resolve_left (not_not.2 h)
      by_cases h1 : p t <;> by_cases h2 : q t <;> simp only [h1, h2, ite_true, ite_false,
        or_true, or_self, or_false]
      · have := hm0 h1; have := hn0 h2; omega
      · have := hm0 h1; omega
      · have := hn0 h2; omega
      · exact le_rfl

end Bounds

/-! ## From the permutation to the two-sided random function -/

section ToRF

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)] {K : ℕ}
  {T Z S Xc : Type} [DecidableEq T] [DecidableEq Z] [SampleableType T] [SampleableType Z]
  [Fintype T] [Fintype Z] [Fintype Xc] (V : Fin K → S → T → Prop)

/-- **The permutation-model game against the two-sided random function**, up to the switching
term and the inverse hits: with `q = q_f + q_i + q_S + 1` queries reading the permutation,

    Adv^{perm}(F) ≤ Pr_{rf}[CPWin ∧ no inverse answer is a structured input]
                    + q²/|B| + q_i·|Xc|/|B|. -/
theorem advCTUFPermAt_le_rf (σ : Fin K × T → S) (emb : Xc → T × Z)
    (F : ProbComp (OracleComp (specCP AR K T Z S) (CTOut K S Xc))) {qf qi qS : ℕ}
    (hF : ∀ f ∈ support F, CPBudget qf qi qS f) :
    advCTUFPermAt V σ emb F ≤
      Pr{let f ← F; let r ← (simulateQ (cfImpl σ) (f >>= cpFinal emb)).run ([], ⟨∅, []⟩)}[
          CPWin V emb (r.1, r.2.1, r.2.2) ∧ ¬InvHit (Set.range emb) r.2.1] +
        ((qf + qi + qS + 1 : ℕ) : ℝ≥0∞) * ((qf + qi + qS + 1 : ℕ) / Fintype.card (T × Z)) +
        (qi : ℝ≥0∞) * (Fintype.card Xc / Fintype.card (T × Z)) := by
  classical
  unfold advCTUFPermAt cpRun
  rw [add_assoc]
  refine prEvent_bind_le_add_const F _ _ _ fun f hf => ?_
  obtain ⟨hfw, hiv, -, hop⟩ := hF f hf
  have hpm : IsQueryBoundP (f >>= cpFinal emb)
      (fun t => isPm (B := T × Z) (fun _ : DR ⊕ (Fin K × T) => none) t = true) (qf + qi + qS + 1) := by
    rw [show qf + qi + qS + 1 = qf + qi + (qS + 1) by omega]
    refine isQueryBoundP_bind (isQueryBoundP_of_imp _ _ ?_ f _ (isQueryBoundP_or _ _ f qf qi hfw hiv))
      fun o ho => (cpFinal_bound _ (fun _ => rfl) emb o).mono (by have := hop o ho; omega)
    rintro (i | ⟨_ | _, b⟩) <;> simp [isPm, isFwd, isInv]
  have hiv' : IsQueryBoundP (f >>= cpFinal emb) (fun t => isInv t = true) (qi + 0) :=
    isQueryBoundP_bind hiv fun o _ => cpFinal_bound_zero _ (fun _ => by simp [isInv]) emb o
  have h1 := prEvent_rp_le_rf (A := AnsCO AR K T S) (fun _ => none) (fun i _ => ciOther σ i)
    (f >>= cpFinal emb) _ hpm [] ⟨∅, []⟩ fun r => CPWin V emb r
  have h2 := prEvent_invHit_le (A := AnsCO AR K T S) (fun _ => none) (fun i _ => ciOther σ i)
    (f >>= cpFinal emb) qi (by simpa using hiv') (Finset.univ.image emb) [] (by simp [InvHit])
    (⟨∅, []⟩ : CISt AR K T)
  have hS : ((Finset.univ.image emb).card : ℝ≥0∞) ≤ Fintype.card Xc := by
    exact_mod_cast Finset.card_image_le.trans (by simp)
  have hcoe : ((Finset.univ.image emb : Finset (T × Z)) : Set (T × Z)) = Set.range emb := by
    ext; simp
  rw [hcoe] at h2
  simp only [List.length_nil, zero_add] at h1
  have h3 : Pr{let r ← (simulateQ (cfImpl σ) (f >>= cpFinal emb)).run ([], ⟨∅, []⟩)}[
      CPWin V emb r] ≤
      Pr{let r ← (simulateQ (cfImpl σ) (f >>= cpFinal emb)).run ([], ⟨∅, []⟩)}[
        CPWin V emb (r.1, r.2.1, r.2.2) ∧ ¬InvHit (Set.range emb) r.2.1] +
      (qi : ℝ≥0∞) * (Fintype.card Xc / Fintype.card (T × Z)) := by
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _
      (fun r => InvHit (Set.range emb) r.2.1)).trans ?_
    rw [add_comm]
    refine add_le_add le_rfl (h2.trans ?_)
    gcongr
  calc _ ≤ _ := h1
    _ ≤ _ := add_le_add h3 le_rfl
    _ = _ := by rw [add_assoc, add_comm ((qi : ℝ≥0∞) * _)]

end ToRF

/-! ## The reduction to the random-function game

The function-model forger simulates `π` for the permutation-model forger. It keeps the table and
a counter; a fresh forward query at a structured input `emb x` gets `(Com(x), z)` with `z` the
second half of a fresh coin, any other fresh answer is a fresh coin. The coins are values of the
world's random oracle at fresh indices (`ARc`: the world with a coin oracle `ℕ → T × Z`). -/

section Red

variable {DR : Type} (AR : DR → Type) (B : Type)

/-- **The world with coins**: the forger's world `AR`, and a coin oracle `ℕ → B`. -/
abbrev ARc : DR ⊕ ℕ → Type := Sum.elim AR fun _ => B

instance instARc [∀ d, SampleableType (AR d)] [SampleableType B] :
    ∀ d, SampleableType (ARc AR B d)
  | .inl d => inferInstanceAs (SampleableType (AR d))
  | .inr _ => inferInstanceAs (SampleableType B)

variable {AR B} {K : ℕ} {T Z S Xc : Type}

/-- The function-model oracles of the reduction: `specCI` with the world with coins. -/
abbrev specCR (AR : DR → Type) (K : ℕ) (Xc T Z S : Type) := specCI (ARc AR (T × Z)) K Xc T S

/-- A world (or coin) query of the reduction. -/
def wQ (d : DR ⊕ ℕ) : OracleComp (specCR AR K Xc T Z S) (ARc AR (T × Z) d) :=
  liftM ((specCR AR K Xc T Z S).query (.inl (.inl d)))

/-- A signing query of the reduction. -/
def sQ (q : Fin K × T) : OracleComp (specCR AR K Xc T Z S) S :=
  liftM ((specCR AR K Xc T Z S).query (.inl (.inr q)))

/-- A `Com` query of the reduction. -/
def cQ (x : Xc) : OracleComp (specCR AR K Xc T Z S) T :=
  liftM ((specCR AR K Xc T Z S).query (.inr x))

open Classical in
/-- The structured input `b = emb x`, if any. -/
noncomputable def embInv (emb : Xc → T × Z) (b : T × Z) : Option Xc :=
  if h : ∃ x, emb x = b then some h.choose else none

theorem embInv_emb {emb : Xc → T × Z} (hemb : Function.Injective emb) (x : Xc) :
    embInv emb (emb x) = some x := by
  have h : ∃ x', emb x' = emb x := ⟨x, rfl⟩
  simp only [embInv, h, dite_true, Option.some.injEq]
  exact hemb h.choose_spec

theorem embInv_some {emb : Xc → T × Z} {b : T × Z} {x : Xc} (h : embInv emb b = some x) :
    emb x = b := by
  unfold embInv at h
  split_ifs at h with h'
  · cases h; exact h'.choose_spec

variable [DecidableEq T] [DecidableEq Z]

/-- **The reduction's simulation of the permutation-model oracles.** -/
noncomputable def simC (emb : Xc → T × Z) :
    QueryImpl (specCP AR K T Z S) (StateT (PTab (T × Z) × ℕ) (OracleComp (specCR AR K Xc T Z S)))
  | .inl (.inl d) => StateT.mk fun s => (fun a => (a, s)) <$> wQ (.inl d)
  | .inl (.inr q) => StateT.mk fun s => (fun a => (a, s)) <$> sQ q
  | .inr (true, b) => StateT.mk fun s => match fwdFind s.1 b with
    | some y => pure (y, s)
    | none => match embInv emb b with
      | some x => cQ x >>= fun t => (fun c : T × Z => ((t, c.2), (s.1 ++ [(b, (t, c.2), true)],
          s.2 + 1))) <$> wQ (.inr s.2)
      | none => (fun c : T × Z => (c, (s.1 ++ [(b, c, true)], s.2 + 1))) <$> wQ (.inr s.2)
  | .inr (false, c) => StateT.mk fun s => match invFind s.1 c with
    | some x => pure (x, s)
    | none => (fun x : T × Z => (x, (s.1 ++ [(x, c, false)], s.2 + 1))) <$> wQ (.inr s.2)

/-- **The function-model forger**: the permutation-model forger and the final evaluations, under
the simulation. -/
noncomputable def simF (emb : Xc → T × Z) (f : OracleComp (specCP AR K T Z S) (CTOut K S Xc)) :
    OracleComp (specCR AR K Xc T Z S) (CTOut K S Xc) :=
  Prod.fst <$> (simulateQ (simC emb) (f >>= cpFinal emb)).run ([], 0)

/-- **The reduction**, on a distribution of permutation-model forgers. -/
noncomputable def permRed (emb : Xc → T × Z) (F : ProbComp (OracleComp (specCP AR K T Z S) (CTOut K S Xc))) :
    ProbComp (OracleComp (specCR AR K Xc T Z S) (CTOut K S Xc)) :=
  simF emb <$> F

end Red

section RedBudget

variable {DR : Type} {AR : DR → Type} {K : ℕ} {T Z S Xc : Type} [DecidableEq T] [DecidableEq Z]

omit [DecidableEq T] [DecidableEq Z] in
theorem isQueryBoundP_wQ (p : _ → Prop) [DecidablePred p] (d : DR ⊕ ℕ) (n : ℕ) :
    IsQueryBoundP (wQ (AR := AR) (K := K) (Xc := Xc) (T := T) (Z := Z) (S := S) d) p n ↔
      (p (.inl (.inl d)) → 0 < n) := isQueryBoundP_query_iff _ _ _

omit [DecidableEq T] [DecidableEq Z] in
theorem isQueryBoundP_sQ (p : _ → Prop) [DecidablePred p] (q : Fin K × T) (n : ℕ) :
    IsQueryBoundP (sQ (AR := AR) (K := K) (Xc := Xc) (T := T) (Z := Z) (S := S) q) p n ↔
      (p (.inl (.inr q)) → 0 < n) := isQueryBoundP_query_iff _ _ _

omit [DecidableEq T] [DecidableEq Z] in
theorem isQueryBoundP_cQ (p : _ → Prop) [DecidablePred p] (x : Xc) (n : ℕ) :
    IsQueryBoundP (cQ (AR := AR) (K := K) (Xc := Xc) (T := T) (Z := Z) (S := S) x) p n ↔
      (p (.inr x) → 0 < n) := isQueryBoundP_query_iff _ _ _

/-- One step of the simulation makes at most one query of a kind `p₂` that only the queries of
kind `p₁` can make. -/
theorem simC_step_bound (emb : Xc → T × Z) (p₁ : _ → Prop) [DecidablePred p₁] (p₂ : _ → Prop)
    [DecidablePred p₂] (hw : ∀ d, ¬p₂ (.inl (.inl d)))
    (hs : ∀ q, p₂ (.inl (.inr q)) → p₁ (.inl (.inr q)))
    (hc : ∀ x b, p₂ (.inr x) → p₁ (.inr (true, b)))
    (t : (DR ⊕ (Fin K × T)) ⊕ (Bool × (T × Z))) (s : PTab (T × Z) × ℕ) :
    IsQueryBoundP (((simC (AR := AR) (S := S) emb) t).run s) p₂ (if p₁ t then 1 else 0) := by
  rcases t with (d | q) | ⟨_ | _, b⟩
  · simp only [simC, StateT.run_mk]
    exact (isQueryBoundP_map_iff (p := p₂) _ _ _).2 ((isQueryBoundP_wQ _ _ _).2 fun h => absurd h (hw _))
  · simp only [simC, StateT.run_mk]
    exact (isQueryBoundP_map_iff (p := p₂) _ _ _).2 ((isQueryBoundP_sQ _ _ _).2 fun h => by
      simp [hs q h])
  · simp only [simC, StateT.run_mk]
    cases invFind s.1 b with
    | some y => trivial
    | none =>
      exact (isQueryBoundP_map_iff (p := p₂) _ _ _).2 ((isQueryBoundP_wQ _ _ _).2 fun h => absurd h (hw _))
  · simp only [simC, StateT.run_mk]
    cases fwdFind s.1 b with
    | some y => trivial
    | none =>
      cases embInv emb b with
      | none =>
        exact (isQueryBoundP_map_iff (p := p₂) _ _ _).2 ((isQueryBoundP_wQ _ _ _).2 fun h => absurd h (hw _))
      | some x =>
        refine (isQueryBoundP_bind (n := if p₁ (.inr (true, b)) then 1 else 0) (m := 0) ?_
          fun _ _ => ?_)
        · rw [isQueryBoundP_cQ]; exact fun h => by simp [hc x b h]
        · exact (isQueryBoundP_map_iff (p := p₂) _ _ _).2 ((isQueryBoundP_wQ _ _ _).2 fun h => absurd h (hw _))

/-- **The reduction's budget**: `Com` queries at most the forward queries (the forger's and the
final ones), signing queries the forger's, openings the forger's. -/
theorem simF_budget (emb : Xc → T × Z) (f : OracleComp (specCP AR K T Z S) (CTOut K S Xc))
    {qf qi qS : ℕ} (hf : CPBudget qf qi qS f) : CIBudget (qf + qS + 1) qS (simF emb f) := by
  obtain ⟨hfw, -, hsg, hop⟩ := hf
  have hfw' : IsQueryBoundP (f >>= cpFinal emb) (fun t => isFwd t = true) (qf + qS + 1) := by
    rw [add_assoc]
    exact isQueryBoundP_bind hfw fun o ho =>
      (cpFinal_bound _ (fun _ => rfl) emb o).mono (by have := hop o ho; omega)
  have hsg' : IsQueryBoundP (f >>= cpFinal emb) (fun t => isSignP t = true) (qS + 0) :=
    isQueryBoundP_bind hsg fun o _ => cpFinal_bound_zero _ (fun _ => by simp [isSignP]) emb o
  refine ⟨?_, ?_, ?_⟩
  · unfold simF
    rw [isQueryBoundP_map_iff]
    exact isQueryBoundP_run_simulateQ (simC emb) _ _
      (simC_step_bound emb _ _ (fun _ => by simp [LazyIdeal.isRF])
        (fun _ h => by simp [LazyIdeal.isRF] at h) (fun _ _ _ => rfl)) _ _ _ hfw'
  · unfold simF
    rw [isQueryBoundP_map_iff]
    exact isQueryBoundP_run_simulateQ (simC emb) _ _
      (simC_step_bound emb _ _ (fun _ => by simp [isSign]) (fun _ _ => rfl)
        (fun _ _ h => by simp [isSign] at h)) _ _ _ (by simpa using hsg')
  · intro o ho
    unfold simF at ho
    erw [support_map] at ho
    obtain ⟨z, hz, rfl⟩ := ho
    have h1 := mem_support_of_run_simulateQ (simC emb) _ _ z hz
    simp only [mem_support_bind_iff, cpFinal] at h1
    obtain ⟨o', ho', h2⟩ := h1
    simp only [support_pure, Set.mem_singleton_iff] at h2
    obtain ⟨_, _, h3⟩ := h2
    rw [h3]; exact hop o' ho'

end RedBudget

/-! ## The reduction against the function-model challenger -/

section Core

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)] {K : ℕ}
  {T Z S Xc : Type} [DecidableEq T] [DecidableEq Z] [SampleableType T] [SampleableType Z]
  [DecidableEq Xc]

/-- The function-model challenger's state (world with coins). -/
abbrev CRSt (AR : DR → Type) (K : ℕ) (Xc T Z : Type) :=
  CISt (ARc AR (T × Z)) K T × (Xc → Option T)

/-- The function-model challenger for the reduction's oracles. -/
def frImpl (σ : Fin K × T → S) :
    QueryImpl (specCR AR K Xc T Z S) (StateT (CRSt AR K Xc T Z) ProbComp) :=
  LazyIdeal.rfFresh (ciOther σ)

/-- **The reduction run against the function-model challenger, as one handler.** -/
noncomputable def combP (σ : Fin K × T → S) (emb : Xc → T × Z) :
    QueryImpl (specCP AR K T Z S)
      (StateT ((PTab (T × Z) × ℕ) × CRSt AR K Xc T Z) ProbComp) :=
  fun q => StateT.mk fun s => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (frImpl σ) ((simC emb q).run s.1)).run s.2

theorem collapseP (σ : Fin K × T → S) (emb : Xc → T × Z) {α : Type}
    (oa : OracleComp (specCP AR K T Z S) α) (s : PTab (T × Z) × ℕ) (c : CRSt AR K Xc T Z) :
    (simulateQ (frImpl σ) ((simulateQ (simC emb) oa).run s)).run c =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (combP σ emb) oa).run (s, c) := by
  refine simulateQ_StateT_StateT_compose _ _ _ (fun q s c => ?_) oa s c
  show _ = _ <$> ((fun r : (_ × _) × _ => (r.1.1, (r.1.2, r.2))) <$> _)
  rw [Functor.map_map]
  exact (id_map _).symm

/-- The world's cache without the coins. -/
def projRO (c : (specR (ARc AR (T × Z))).QueryCache) : (specR AR).QueryCache :=
  QueryCache.ofFn fun d => c (.inl d)

/-- **The hybrid's state that the reduction's run represents**: the table, and the world's cache
without the coins with the signed targets. -/
def projP (s : (PTab (T × Z) × ℕ) × CRSt AR K Xc T Z) : PTab (T × Z) × CISt AR K T :=
  (s.1.1, ⟨projRO s.2.1.ro, s.2.1.signed⟩)

/-- **The invariant**: the coins from the counter on are unused; `Com` is defined only at
structured inputs with a record; a forward record at a structured input has its `Com` value. -/
def InvP (emb : Xc → T × Z) (s : (PTab (T × Z) × ℕ) × CRSt AR K Xc T Z) : Prop :=
  (∀ m, s.1.2 ≤ m → s.2.1.ro (.inr m) = none) ∧
  (∀ x, fwdFind s.1.1 (emb x) = none → s.2.2 x = none) ∧
  (∀ e ∈ s.1.1, e.2.2 = true → ∀ x, e.1 = emb x → s.2.2 x = some e.2.1.1)

omit [DecidableEq Xc] [∀ d, SampleableType (AR d)] [DecidableEq T] [DecidableEq Z]
  [SampleableType T] [SampleableType Z] in
theorem projRO_inr (c : (specR (ARc AR (T × Z))).QueryCache) (n : ℕ) (u : T × Z) :
    projRO (c.cacheQuery (.inr n) u) = projRO c := by
  refine QueryCache.ext fun d => ?_
  show (c.cacheQuery (.inr n) u) (.inl d) = c (.inl d)
  exact QueryCache.cacheQuery_of_ne _ _ (by simp)

omit [DecidableEq Xc] [∀ d, SampleableType (AR d)] [DecidableEq T] [DecidableEq Z]
  [SampleableType T] [SampleableType Z] in
theorem projRO_inl (c : (specR (ARc AR (T × Z))).QueryCache) (d : DR) (u : AR d) :
    projRO (c.cacheQuery (.inl d) u) = (projRO c).cacheQuery d u := by
  refine QueryCache.ext fun d' => ?_
  show (c.cacheQuery (.inl d) u) (.inl d') = ((projRO c).cacheQuery d u) d'
  by_cases h : d' = d
  · subst h
    rw [show ((projRO c).cacheQuery d' u) d' = some u from QueryCache.cacheQuery_self _ _ _]
    exact QueryCache.cacheQuery_self (spec := specR (ARc AR (T × Z))) c (.inl d') u
  · rw [show ((projRO c).cacheQuery d u) d' = (projRO c) d' from
      QueryCache.cacheQuery_of_ne _ _ h]
    exact QueryCache.cacheQuery_of_ne (spec := specR (ARc AR (T × Z))) c (t := Sum.inl d) u
      (by simpa using h)

omit [DecidableEq Xc] [DecidableEq T] [DecidableEq Z] in
theorem uniform_pair :
    (do let t ← ($ᵗ T : ProbComp T); let c ← ($ᵗ (T × Z) : ProbComp (T × Z)); pure (t, c.2)) =ᵈ
      ($ᵗ (T × Z) : ProbComp (T × Z)) := by
  rw [SampleableType.uniformSample_prod_eq_bind]
  refine EvalDistEq.bind_right _ fun t => ?_
  simp only [bind_assoc, pure_bind]
  exact LazyIdeal.eqd_bind_unused _ _

variable (σ : Fin K × T → S) (emb : Xc → T × Z)

theorem combP_world (d : DR) (L : PTab (T × Z)) (n : ℕ) (ro : (specR (ARc AR (T × Z))).QueryCache)
    (sg : List (Fin K × T)) (tab : Xc → Option T) :
    ((combP σ emb) (.inl (.inl d))).run ((L, n), (⟨ro, sg⟩, tab)) =
      (fun r : AR d × (specR (ARc AR (T × Z))).QueryCache => (r.1, ((L, n), (⟨r.2, sg⟩, tab)))) <$>
        ((specR (ARc AR (T × Z))).randomOracle (Sum.inl d)).run ro := by
  simp only [combP, simC, frImpl, StateT.run_mk, wQ]
  erw [simulateQ_map, simulateQ_spec_query]
  erw [StateT.run_map]
  simp only [LazyIdeal.rfFresh, ciOther]
  repeat (first | erw [StateT.run_mk] | erw [Functor.map_map])
  rfl

theorem combP_sign (q : Fin K × T) (L : PTab (T × Z)) (n : ℕ)
    (ro : (specR (ARc AR (T × Z))).QueryCache) (sg : List (Fin K × T)) (tab : Xc → Option T) :
    ((combP σ emb) (.inl (.inr q))).run ((L, n), (⟨ro, sg⟩, tab)) =
      pure (σ q, ((L, n), (⟨ro, if q ∈ sg then sg else sg ++ [q]⟩, tab))) := by
  simp only [combP, simC, frImpl, StateT.run_mk, sQ]
  erw [simulateQ_map, simulateQ_spec_query]
  erw [StateT.run_map]
  simp only [LazyIdeal.rfFresh, ciOther]
  repeat (first | erw [StateT.run_mk] | erw [Functor.map_map] | erw [map_pure])
  rfl

theorem combP_fwd_found (b y : T × Z) (s : (PTab (T × Z) × ℕ) × CRSt AR K Xc T Z)
    (h : fwdFind s.1.1 b = some y) :
    ((combP σ emb) (.inr (true, b))).run s = pure (y, s) := by
  simp only [combP, simC, StateT.run_mk, h]
  erw [simulateQ_pure]
  rfl

theorem combP_inv_found (c x : T × Z) (s : (PTab (T × Z) × ℕ) × CRSt AR K Xc T Z)
    (h : invFind s.1.1 c = some x) :
    ((combP σ emb) (.inr (false, c))).run s = pure (x, s) := by
  simp only [combP, simC, StateT.run_mk, h]
  erw [simulateQ_pure]
  rfl

theorem combP_inv_fresh (c : T × Z) (L : PTab (T × Z)) (n : ℕ)
    (ro : (specR (ARc AR (T × Z))).QueryCache) (sg : List (Fin K × T)) (tab : Xc → Option T)
    (h : invFind L c = none) (hro : ro (.inr n) = none) :
    ((combP σ emb) (.inr (false, c))).run ((L, n), (⟨ro, sg⟩, tab)) =
      (fun u : T × Z => (u, ((L ++ [(u, c, false)], n + 1), (⟨ro.cacheQuery (.inr n) u, sg⟩, tab)))) <$>
        ($ᵗ (T × Z) : ProbComp (T × Z)) := by
  simp only [combP, simC, StateT.run_mk, h, frImpl, wQ]
  erw [simulateQ_map, simulateQ_spec_query]
  erw [StateT.run_map]
  simp only [LazyIdeal.rfFresh, ciOther]
  erw [StateT.run_mk]
  dsimp only
  erw [StateT.run_mk]
  dsimp only
  erw [randomOracle.run_eq]
  rw [show ro.toFn (Sum.inr n) = none from hro]
  dsimp only
  rw [map_bind]
  simp only [map_pure]
  rw [bind_pure_comp]
  repeat erw [Functor.map_map]
  rfl

theorem combP_fwd_coin (b : T × Z) (L : PTab (T × Z)) (n : ℕ)
    (ro : (specR (ARc AR (T × Z))).QueryCache) (sg : List (Fin K × T)) (tab : Xc → Option T)
    (h : fwdFind L b = none) (he : embInv emb b = none) (hro : ro (.inr n) = none) :
    ((combP σ emb) (.inr (true, b))).run ((L, n), (⟨ro, sg⟩, tab)) =
      (fun u : T × Z => (u, ((L ++ [(b, u, true)], n + 1), (⟨ro.cacheQuery (.inr n) u, sg⟩, tab)))) <$>
        ($ᵗ (T × Z) : ProbComp (T × Z)) := by
  simp only [combP, simC, StateT.run_mk, h, he, frImpl, wQ]
  erw [simulateQ_map, simulateQ_spec_query]
  erw [StateT.run_map]
  simp only [LazyIdeal.rfFresh, ciOther]
  erw [StateT.run_mk]
  dsimp only
  erw [StateT.run_mk]
  dsimp only
  erw [randomOracle.run_eq]
  rw [show ro.toFn (Sum.inr n) = none from hro]
  dsimp only
  rw [map_bind]
  simp only [map_pure]
  rw [bind_pure_comp]
  repeat erw [Functor.map_map]
  rfl

theorem combP_fwd_com (b : T × Z) (x : Xc) (L : PTab (T × Z)) (n : ℕ)
    (ro : (specR (ARc AR (T × Z))).QueryCache) (sg : List (Fin K × T)) (tab : Xc → Option T)
    (h : fwdFind L b = none) (he : embInv emb b = some x) (htab : tab x = none)
    (hro : ro (.inr n) = none) :
    ((combP σ emb) (.inr (true, b))).run ((L, n), (⟨ro, sg⟩, tab)) =
      (do let t ← ($ᵗ T : ProbComp T); let u ← ($ᵗ (T × Z) : ProbComp (T × Z))
          pure ((t, u.2), ((L ++ [(b, (t, u.2), true)], n + 1),
            (⟨ro.cacheQuery (.inr n) u, sg⟩, Function.update tab x (some t))))) := by
  simp only [combP, simC, StateT.run_mk, h, he, frImpl, wQ, cQ]
  erw [simulateQ_bind, simulateQ_spec_query]
  erw [StateT.run_bind]
  simp only [LazyIdeal.rfFresh]
  erw [StateT.run_mk]
  dsimp only
  rw [htab]
  dsimp only
  erw [bind_map_left, map_bind]
  refine bind_congr fun (t : T) => ?_
  erw [simulateQ_map, simulateQ_spec_query, StateT.run_map]
  simp only [LazyIdeal.rfFresh, ciOther]
  erw [StateT.run_mk]
  dsimp only
  erw [StateT.run_mk]
  dsimp only
  erw [randomOracle.run_eq]
  rw [show ro.toFn (Sum.inr n) = none from hro]
  dsimp only
  rw [map_bind]
  simp only [map_pure]
  rw [bind_pure_comp, bind_pure_comp]
  repeat erw [Functor.map_map]
  rfl

end Core

end VoleMole.Assumptions.UOV.CTUFPerm
