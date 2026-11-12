import VoleMole.ROM.Basic
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.EvalDist.EvalDistEq
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore

section Specs

variable {DR : Type} (AR : DR → Type) (X Hn G S : Type)

abbrev specR : OracleSpec DR := OracleSpec.ofFn AR

abbrev AnsA : DR ⊕ ((X × Hn) ⊕ G) → Type := Sum.elim AR (Sum.elim (fun _ => G × Hn) fun _ => S)

abbrev specA : OracleSpec (DR ⊕ ((X × Hn) ⊕ G)) := OracleSpec.ofFn (AnsA AR X Hn G S)

abbrev AnsB : DR ⊕ ((X × Hn) ⊕ G) → Type := Sum.elim AR (Sum.elim (fun _ => Option G) fun _ => S)

abbrev specB : OracleSpec (DR ⊕ ((X × Hn) ⊕ G)) := OracleSpec.ofFn (AnsB AR X Hn G S)

structure Ch where
  ro : (specR AR).QueryCache
  rest : List G
  tg : X → Option (G × Hn)
  iq : ℕ

end Specs

section Impl

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn G S : Type}

/-- The world oracle on the challenger's state. -/
def roStep (d : DR) (c : Ch AR X Hn G) : ProbComp (AR d × Ch AR X Hn G) :=
  (fun r => (r.1, { c with ro := r.2 })) <$> ((specR AR).randomOracle d).run c.ro

def chImpl (pre : G → S) : QueryImpl (specB AR X Hn G S) (StateT (Ch AR X Hn G) ProbComp)
  | .inl d => StateT.mk (roStep d)
  | .inr (.inl (x, h)) => StateT.mk fun c => pure <| match c.rest with
      | u :: r => (some u, { c with rest := r, tg := Function.update c.tg x (some (u, h)) })
      | [] => (none, c)
  | .inr (.inr t) => StateT.mk fun c => pure (pre t, { c with iq := c.iq + 1 })

end Impl

section Real

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn G S : Type} [AddCommGroup G]

/-- The real target oracle and the other oracles, on the state `(H_T table, challenger state)`. -/
def realImpl (φ : Hn → G ≃ G) (pre : G → S) :
    QueryImpl (specA AR X Hn G S) (StateT ((X → Option (G × Hn)) × Ch AR X Hn G) ProbComp)
  | .inl d => StateT.mk fun s => (fun r => (r.1, (s.1, r.2))) <$> roStep d s.2
  | .inr (.inl (x, h)) => StateT.mk fun s => pure <| match s.1 x with
      | some a => (a, s)
      | none => match s.2.rest with
        | u :: r => ((u, h), (Function.update s.1 x (some (u, h)),
            { s.2 with rest := r, tg := Function.update s.2.tg x (some (φ h u, h)) }))
        | [] => (((0 : G), h), (Function.update s.1 x (some (0, h)), s.2))
  | .inr (.inr t) => StateT.mk fun s => pure (pre t, (s.1, { s.2 with iq := s.2.iq + 1 }))

/-- The reduction's handler: world and issuer forwarded, the target oracle programmed. -/
def redImpl (φ : Hn → G ≃ G) :
    QueryImpl (specA AR X Hn G S) (StateT (X → Option (G × Hn)) (OracleComp (specB AR X Hn G S)))
  | .inl d => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specB AR X Hn G S).query (.inl d)) : OracleComp (specB AR X Hn G S) (AR d))
  | .inr (.inl (x, h)) => StateT.mk fun s => match s x with
      | some a => pure (a, s)
      | none => (fun r : Option G => match r with
          | some t => (((φ h).symm t, h), Function.update s x (some ((φ h).symm t, h)))
          | none => (((0 : G), h), Function.update s x (some (0, h)))) <$>
        (liftM ((specB AR X Hn G S).query (.inr (.inl (x, h)))) :
          OracleComp (specB AR X Hn G S) (Option G))
  | .inr (.inr t) => StateT.mk fun s => (fun a => (a, s)) <$>
      (liftM ((specB AR X Hn G S).query (.inr (.inr t))) : OracleComp (specB AR X Hn G S) S)

/-- The reduction run against the challenger, as one handler. -/
def combImpl (φ : Hn → G ≃ G) (pre : G → S) :
    QueryImpl (specA AR X Hn G S) (StateT ((X → Option (G × Hn)) × Ch AR X Hn G) ProbComp) :=
  fun q => StateT.mk fun s => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (chImpl pre) ((redImpl φ q).run s.1)).run s.2

theorem collapse (φ : Hn → G ≃ G) (pre : G → S) {α : Type}
    (oa : OracleComp (specA AR X Hn G S) α) (s : X → Option (G × Hn)) (c : Ch AR X Hn G) :
    (simulateQ (chImpl pre) ((simulateQ (redImpl φ) oa).run s)).run c =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (combImpl φ pre) oa).run (s, c) := by
  refine simulateQ_StateT_StateT_compose _ _ _ (fun q s c => ?_) oa s c
  show _ = _ <$> ((fun r : (_ × _) × _ => (r.1.1, (r.1.2, r.2))) <$> _)
  rw [Functor.map_map]
  exact (id_map _).symm

end Real

section Steps

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn G S : Type} [AddCommGroup G] (φ : Hn → G ≃ G) (pre : G → S)

lemma comb_inl (d : DR) (p : (X → Option (G × Hn)) × Ch AR X Hn G) :
    (combImpl (S := S) φ pre (.inl d)).run p = (realImpl φ pre (.inl d)).run p := by
  simp [combImpl, realImpl, redImpl]
  erw [simulateQ_spec_query]
  rfl

lemma comb_iss (t : G) (p : (X → Option (G × Hn)) × Ch AR X Hn G) :
    (combImpl (S := S) φ pre (.inr (.inr t))).run p = (realImpl φ pre (.inr (.inr t))).run p := by
  simp [combImpl, realImpl, redImpl]
  erw [simulateQ_spec_query]
  simp [chImpl]

lemma comb_cached (x : X) (h : Hn) (s : X → Option (G × Hn)) (a : G × Hn) (hx : s x = some a)
    (c : Ch AR X Hn G) :
    (combImpl (S := S) φ pre (.inr (.inl (x, h)))).run (s, c) = pure (a, (s, c)) := by
  simp [combImpl, redImpl, hx]

lemma real_cached (x : X) (h : Hn) (s : X → Option (G × Hn)) (a : G × Hn) (hx : s x = some a)
    (c : Ch AR X Hn G) :
    (realImpl (S := S) φ pre (.inr (.inl (x, h)))).run (s, c) = pure (a, (s, c)) := by
  simp [realImpl, hx]

lemma comb_fresh_cons (x : X) (h : Hn) (s : X → Option (G × Hn)) (hx : s x = none)
    (u : G) (r : List G) (c : Ch AR X Hn G) :
    (combImpl (S := S) φ pre (.inr (.inl (x, h)))).run (s, { c with rest := u :: r }) =
      pure (((φ h).symm u, h), (Function.update s x (some ((φ h).symm u, h)),
        { c with rest := r, tg := Function.update c.tg x (some (u, h)) })) := by
  simp [combImpl, redImpl, hx]
  erw [simulateQ_spec_query]
  simp [chImpl]

lemma real_fresh_cons (x : X) (h : Hn) (s : X → Option (G × Hn)) (hx : s x = none)
    (u : G) (r : List G) (c : Ch AR X Hn G) :
    (realImpl (S := S) φ pre (.inr (.inl (x, h)))).run (s, { c with rest := u :: r }) =
      pure ((u, h), (Function.update s x (some (u, h)),
        { c with rest := r, tg := Function.update c.tg x (some (φ h u, h)) })) := by
  simp [realImpl, hx]

lemma comb_fresh_nil (x : X) (h : Hn) (s : X → Option (G × Hn)) (hx : s x = none)
    (c : Ch AR X Hn G) :
    (combImpl (S := S) φ pre (.inr (.inl (x, h)))).run (s, { c with rest := [] }) =
      (realImpl (S := S) φ pre (.inr (.inl (x, h)))).run (s, { c with rest := [] }) := by
  simp [combImpl, redImpl, realImpl, hx]
  erw [simulateQ_spec_query]
  simp [chImpl]

end Steps

section Stream

variable (G : Type) [SampleableType G]

/-- `m` independent uniform values. -/
def unifList : ℕ → ProbComp (List G)
  | 0 => pure []
  | m + 1 => do
    let u ← $ᵗ G
    let L ← unifList m
    pure (u :: L)

end Stream

lemma eqd_swap {α β γ : Type} (mx : ProbComp α) (my : ProbComp β) (f : α → β → ProbComp γ) :
    (do let a ← mx; let b ← my; f a b) =ᵈ (do let b ← my; let a ← mx; f a b) := by
  let : MeasurableSpace γ := ⊤
  exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_bind_swap mx my f)

lemma eqd_swap_congr {α β γ : Type} (mx : ProbComp α) (my : ProbComp β)
    (f g : α → β → ProbComp γ)
    (h : ∀ b, (do let a ← mx; f a b) =ᵈ (do let a ← mx; g a b)) :
    (do let a ← mx; let b ← my; f a b) =ᵈ (do let a ← mx; let b ← my; g a b) :=
  (eqd_swap mx my f).trans ((EvalDistEq.bind_right my h).trans (eqd_swap mx my g).symm)

section Programming

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn G S : Type} [AddCommGroup G] [SampleableType G]
  (φ : Hn → G ≃ G) (pre : G → S)

/-- **Programming the target oracle is perfect**: with a uniform stream of targets, the real game
(answer `u`, target `φ h u`) and the reduction against the challenger (target `t`, answer
`(φ h)⁻¹ t`) have the same joint distribution of output and state. -/
theorem real_eqd_comb {α : Type} (oa : OracleComp (specA AR X Hn G S) α) :
    ∀ (s : X → Option (G × Hn)) (c : Ch AR X Hn G) (m : ℕ),
      (do let L ← unifList G m; (simulateQ (realImpl φ pre) oa).run (s, { c with rest := L })) =ᵈ
        (do let L ← unifList G m; (simulateQ (combImpl φ pre) oa).run (s, { c with rest := L })) := by
  induction oa using OracleComp.inductionOn with
  | pure x => intro s c m; exact EvalDistEq.rfl
  | query_bind q k ih =>
    intro s c m
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases q with d | ⟨x, h⟩ | t
    · simp only [comb_inl]
      simp only [realImpl, StateT.run_mk, roStep, Functor.map_map, bind_map_left]
      exact eqd_swap_congr _ _ _ _ fun r => ih r.1 s { c with ro := r.2 } m
    · cases hx : s x with
      | some a =>
        simp only [comb_cached φ pre x h s a hx, real_cached φ pre x h s a hx]
        exact ih a s c m
      | none =>
        cases m with
        | zero =>
          simp only [unifList, pure_bind]
          rw [comb_fresh_nil φ pre x h s hx]
          simp only [realImpl, StateT.run_mk, hx, pure_bind]
          simpa only [unifList, pure_bind] using ih ((0 : G), h) (Function.update s x (some (0, h))) c 0
        | succ m =>
          simp only [unifList, bind_assoc, pure_bind]
          simp only [comb_fresh_cons φ pre x h s hx, real_fresh_cons φ pre x h s hx]
          refine (EvalDistEq.bind_right ($ᵗ G) fun u => ih (u, h) _
            { c with tg := Function.update c.tg x (some (φ h u, h)) } m).trans ?_
          refine EvalDistEq.trans ?_
            ((SampleableType.map_uniformSample_evalDistEq_of_bijective (φ h).bijective).bind_left _)
          simp only [bind_map_left, Equiv.symm_apply_apply]
          exact EvalDistEq.rfl
    · simp only [comb_iss]
      simp only [realImpl, StateT.run_mk, pure_bind]
      exact ih _ s { c with iq := c.iq + 1 } m

end Programming

section Games

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn G S : Type} [AddCommGroup G] [SampleableType G]
  {PK K : Type}

/-- The challenger's initial state: empty random-oracle cache, the target stream `L`, no labelled
targets, no preimage query. -/
def ch0 (L : List G) : Ch AR X Hn G := ⟨∅, L, fun _ => none, 0⟩

variable (KG : ProbComp (PK × K)) (pre : K → G → S) (n : ℕ)

/-- **The one-more forgery game.** -/
def omuf (φ : Hn → G ≃ G)
    (A : PK → ProbComp (OracleComp (specA AR X Hn G S) (List (X × S) × Bool))) :
    ProbComp (PK × (List (X × S) × Bool) × (X → Option (G × Hn)) × Ch AR X Hn G) := do
  let kp ← KG
  let a ← A kp.1
  let L ← unifList G n
  let r ← (simulateQ (realImpl φ (pre kp.2)) a).run (fun _ => none, ch0 L)
  pure (kp.1, r.1, r.2)

/-- **The one-more preimage experiment.** -/
def omExp (B : PK → ProbComp (OracleComp (specB AR X Hn G S) (List (X × S)))) :
    ProbComp (PK × List (X × S) × Ch AR X Hn G) := do
  let kp ← KG
  let b ← B kp.1
  let L ← unifList G n
  let r ← (simulateQ (chImpl (pre kp.2)) b).run (ch0 L)
  pure (kp.1, r.1, r.2)

/-- **The reduction.** -/
def red (φ : Hn → G ≃ G)
    (A : PK → ProbComp (OracleComp (specA AR X Hn G S) (List (X × S) × Bool))) (pk : PK) :
    ProbComp (OracleComp (specB AR X Hn G S) (List (X × S))) := do
  let a ← A pk
  pure ((fun r => r.1.1) <$> (simulateQ (redImpl φ) a).run (fun _ => none))

variable (ℓ : ℕ)

/-- The experiment's win: `ℓ + 1` claims on distinct labels, each good, after at most `ℓ`
preimage queries. -/
def Wins (good : PK → S → Option (G × Hn) → Prop) (pk : PK) (cl : List (X × S))
    (c : Ch AR X Hn G) : Prop :=
  cl.length = ℓ + 1 ∧ (cl.map Prod.fst).Nodup ∧ c.iq ≤ ℓ ∧ ∀ p ∈ cl, good pk p.2 (c.tg p.1)

/-- The forger's win: its own acceptance flag, `ℓ + 1` claims on distinct labels, at most `ℓ`
issuer queries. -/
def Forges (o : List (X × S) × Bool) (c : Ch AR X Hn G) : Prop :=
  o.2 = true ∧ o.1.length = ℓ + 1 ∧ (o.1.map Prod.fst).Nodup ∧ c.iq ≤ ℓ

theorem omuf_good_le (φ : Hn → G ≃ G)
    (A : PK → ProbComp (OracleComp (specA AR X Hn G S) (List (X × S) × Bool)))
    (good : PK → S → Option (G × Hn) → Prop) :
    Pr{let r ← omuf KG pre n φ A}[Forges ℓ r.2.1 r.2.2.2 ∧
        ∀ p ∈ r.2.1.1, good r.1 p.2 (r.2.2.2.tg p.1)] ≤
      Pr{let r ← omExp KG pre n (red φ A)}[Wins ℓ good r.1 r.2.1 r.2.2] := by
  have hR : omExp KG pre n (red φ A) = (do
      let kp ← KG
      let a ← A kp.1
      let L ← unifList G n
      let r ← (simulateQ (combImpl φ (pre kp.2)) a).run (fun _ => none, ch0 L)
      pure (kp.1, r.1.1, r.2.2)) := by
    simp only [omExp, red, bind_assoc, pure_bind, simulateQ_map, StateT.run_map, collapse,
      Functor.map_map, bind_map_left]
  rw [hR]
  have hE : omuf KG pre n φ A =ᵈ (do
      let kp ← KG
      let a ← A kp.1
      let L ← unifList G n
      let r ← (simulateQ (combImpl φ (pre kp.2)) a).run (fun _ => none, ch0 L)
      pure (kp.1, r.1, r.2)) := by
    refine EvalDistEq.bind_right KG fun kp => EvalDistEq.bind_right _ fun a => ?_
    have := (real_eqd_comb φ (pre kp.2) a (fun _ => none) (ch0 []) n).bind_left
      (fun r => pure (kp.1, r.1, r.2))
    simpa only [bind_assoc, pure_bind, ch0] using this
  rw [hE.prEvent_eq]
  have hM : (do
      let kp ← KG
      let a ← A kp.1
      let L ← unifList G n
      let r ← (simulateQ (combImpl φ (pre kp.2)) a).run (fun _ => none, ch0 L)
      pure (kp.1, r.1.1, r.2.2)) = (fun t => (t.1, t.2.1.1, t.2.2.2)) <$> (do
      let kp ← KG
      let a ← A kp.1
      let L ← unifList G n
      let r ← (simulateQ (combImpl φ (pre kp.2)) a).run (fun _ => none, ch0 L)
      pure (kp.1, r.1, r.2)) := by
    simp only [map_bind, map_pure]
  rw [hM, prEvent_map]
  refine prEvent_mono _ _ _ fun r hr => ?_
  obtain ⟨⟨-, hlen, hnd, hiq⟩, hgood⟩ := hr
  exact ⟨hlen, hnd, hiq, hgood⟩

end Games

section Corollaries

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn G S : Type} [AddCommGroup G] [SampleableType G]
  {PK K : Type} (KG : ProbComp (PK × K)) (pre : K → G → S) (n ℓ : ℕ)

/-- The claim at position `i` of the forger's output is accepted but not good. -/
def BadAt (good : PK → S → Option (G × Hn) → Prop) (i : ℕ)
    (r : PK × (List (X × S) × Bool) × (X → Option (G × Hn)) × Ch AR X Hn G) : Prop :=
  r.2.1.2 = true ∧ ∃ p, r.2.1.1[i]? = some p ∧ ¬good r.1 p.2 (r.2.2.2.tg p.1)

/-- **The generic one-more reduction**: a forger's win probability is at most the advantage of
the reduction in the experiment plus, per claim position, the probability that the claim is
accepted but not good. -/
theorem omuf_le (φ : Hn → G ≃ G)
    (A : PK → ProbComp (OracleComp (specA AR X Hn G S) (List (X × S) × Bool)))
    (good : PK → S → Option (G × Hn) → Prop) :
    Pr{let r ← omuf KG pre n φ A}[Forges ℓ r.2.1 r.2.2.2] ≤
      Pr{let r ← omExp KG pre n (red φ A)}[Wins ℓ good r.1 r.2.1 r.2.2] +
        ∑ i : Fin (ℓ + 1), Pr{let r ← omuf KG pre n φ A}[BadAt good i.val r] := by
  refine (prEvent_le_prEvent_add_prEvent_and_not _ _
    (fun r => Forges ℓ r.2.1 r.2.2.2 ∧ ∀ p ∈ r.2.1.1, good r.1 p.2 (r.2.2.2.tg p.1))).trans
    (add_le_add (omuf_good_le KG pre n ℓ φ A good) ?_)
  refine (prEvent_mono _ _ (fun r => ∃ i : Fin (ℓ + 1), BadAt good i.val r)
      fun r hr => ?_).trans (prEvent_exists_le _ _)
  · obtain ⟨hF, hng⟩ := hr
    have hng' : ¬∀ p ∈ r.2.1.1, good r.1 p.2 (r.2.2.2.tg p.1) := fun h => hng ⟨hF, h⟩
    obtain ⟨hacc, hlen, -, -⟩ := hF
    push Not at hng'
    obtain ⟨p, hp, hbad⟩ := hng'
    obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
    exact ⟨⟨i, hlen ▸ hi⟩, hacc, p, List.getElem?_eq_some_iff.2 ⟨hi, hpi⟩, hbad⟩

/-! ### The two assumptions -/

/-- **Def. 3.1's win for a labelled target**: `s` is a preimage of the target. -/
def goodPre (rel : PK → S → G → Prop) (pk : PK) (s : S) (tg : Option (G × Hn)) : Prop :=
  ∃ t h, tg = some (t, h) ∧ rel pk s t

/-- **The τ-shift win**: `s` is a preimage of the target shifted by one of at most `τ` shifts
submitted with the target request. -/
def goodShift (τ : ℕ) (rel : PK → S → G → Prop) (pk : PK) (s : S) (tg : Option (G × List G)) :
    Prop :=
  ∃ t δs, tg = some (t, δs) ∧ δs.length ≤ τ ∧ ∃ δ ∈ δs, rel pk s (t + δ)

/-- U1's programming: answer `u`, target `u + e` for the hint `e`. -/
def addHint : G → G ≃ G := fun e => Equiv.addRight e

/-- U2's: answer = target (the hint is a list of shifts). -/
def noHint : List G → G ≃ G := fun _ => Equiv.refl G

end Corollaries

section Invariant

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn G S : Type} [AddCommGroup G]

/-- In the real game a labelled target is `φ h` of the answer, `h` the hint of the first query. -/
def TgInv (φ : Hn → G ≃ G) (p : (X → Option (G × Hn)) × Ch AR X Hn G) : Prop :=
  ∀ x t h, p.2.tg x = some (t, h) → ∃ a, p.1 x = some (a, h) ∧ t = φ h a

theorem tgInv_preserved (φ : Hn → G ≃ G) (pre : G → S) :
    QueryImpl.PreservesInv (realImpl (AR := AR) (X := X) (S := S) φ pre) (TgInv φ) := by
  intro q p hp z hz
  rcases q with d | ⟨x, h⟩ | t
  · simp only [realImpl, StateT.run_mk, roStep, Functor.map_map, support_map,
      Set.mem_image] at hz
    obtain ⟨r, -, rfl⟩ := hz
    exact hp
  · simp only [realImpl, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    cases hx : p.1 x with
    | some a => simpa [hx] using hp
    | none =>
      cases hr : p.2.rest with
      | nil =>
        intro y t' h' hy
        by_cases hyx : y = x
        · subst hyx
          obtain ⟨a, ha, -⟩ := hp y t' h' hy
          simp [hx] at ha
        · obtain ⟨a, ha, hat⟩ := hp y t' h' hy
          exact ⟨a, by simp [hyx, ha], hat⟩
      | cons u r =>
        intro y t' h' hy
        by_cases hyx : y = x
        · subst hyx
          simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hy ⊢
          exact ⟨u, by simp [hy.2], by rw [← hy.1, ← hy.2]⟩
        · simp only [Function.update_of_ne hyx] at hy ⊢
          exact hp y t' h' hy
  · simp only [realImpl, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hp

end Invariant

section NoFallback

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn G S : Type} [AddCommGroup G]

/-- A target-oracle query. -/
def isTgt : DR ⊕ ((X × Hn) ⊕ G) → Bool
  | .inr (.inl _) => true
  | _ => false

/-- Every recorded answer got a target from the stream. -/
def NoFall (φ : Hn → G ≃ G) (p : (X → Option (G × Hn)) × Ch AR X Hn G) : Prop :=
  ∀ x a h, p.1 x = some (a, h) → p.2.tg x = some (φ h a, h)

/-- **With at most `k ≤ |stream|` target queries, the stream never runs out.** -/
theorem noFall_of_bound (φ : Hn → G ≃ G) (pre : G → S) {α : Type}
    (oa : OracleComp (specA AR X Hn G S) α) :
    ∀ (k : ℕ) (p : (X → Option (G × Hn)) × Ch AR X Hn G),
      IsQueryBoundP oa (fun q => isTgt q = true) k → k ≤ p.2.rest.length → NoFall φ p →
        ∀ z ∈ support ((simulateQ (realImpl φ pre) oa).run p), NoFall φ z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro k p _ _ hp z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hp
  | query_bind q cont ih =>
    intro k p hq hk hp z hz
    rw [isQueryBoundP_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨up, hu, hz⟩ := hz
    rcases q with d | ⟨x, h⟩ | t
    · have hq2 := hq.2 up.1
      change IsQueryBoundP _ _ k at hq2
      simp only [realImpl, StateT.run_mk, roStep, Functor.map_map, support_map,
        Set.mem_image] at hu
      obtain ⟨r, -, rfl⟩ := hu
      exact ih _ k (p.1, { p.2 with ro := r.2 }) hq2 hk hp z hz
    · have hq2 := hq.2 up.1
      change IsQueryBoundP _ _ (k - 1) at hq2
      have hk0 : 0 < k := hq.1.resolve_left (by simp [isTgt])
      simp only [realImpl, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hu
      subst hu
      cases hx : p.1 x with
      | some a =>
        simp only [hx] at hq2 hz
        exact ih _ (k - 1) p hq2 (by omega) hp z hz
      | none =>
        cases hr : p.2.rest with
        | nil => rw [hr] at hk; simp at hk; omega
        | cons v r =>
          simp only [hx, hr] at hq2 hz
          refine ih _ (k - 1) _ hq2 ?_ ?_ z hz
          · rw [hr] at hk
            simp only [List.length_cons] at hk
            simp only
            omega
          · intro y a h' hy
            by_cases hyx : y = x
            · subst hyx
              simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hy ⊢
              obtain ⟨rfl, rfl⟩ := hy
              exact ⟨rfl, rfl⟩
            · simp only [Function.update_of_ne hyx] at hy ⊢
              exact hp y a h' hy
    · have hq2 := hq.2 up.1
      change IsQueryBoundP _ _ k at hq2
      simp only [realImpl, StateT.run_mk, support_pure, Set.mem_singleton_iff] at hu
      subst hu
      exact ih _ k (p.1, { p.2 with iq := p.2.iq + 1 }) hq2 hk hp z hz

end NoFallback

section Bound

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn G S : Type} [AddCommGroup G] [SampleableType G]
  {PK K : Type} (KG : ProbComp (PK × K)) (pre : K → G → S) (n ℓ : ℕ)

omit [AddCommGroup G] in
lemma length_of_mem_unifList : ∀ (m : ℕ) (L : List G), L ∈ support (unifList G m) → L.length = m
  | 0, L, h => by simp only [unifList, support_pure, Set.mem_singleton_iff] at h; subst h; rfl
  | m + 1, L, h => by
    simp only [unifList, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨u, -, L', hL', rfl⟩ := h
    simp [length_of_mem_unifList m L' hL']

/-- The claim at position `i` is accepted but not good for the target the real game programmed
from the answer `a` and the first hint `h` recorded for its label (`φ h a`). -/
def BadS (φ : Hn → G ≃ G) (good : PK → S → Option (G × Hn) → Prop) (i : ℕ)
    (r : PK × (List (X × S) × Bool) × (X → Option (G × Hn)) × Ch AR X Hn G) : Prop :=
  r.2.1.2 = true ∧ ∃ p, r.2.1.1[i]? = some p ∧
    ¬good r.1 p.2 ((r.2.2.1 p.1).map fun ah => (φ ah.2 ah.1, ah.2))

/-- **The generic reduction, with a target-query budget**: if every run of the composed adversary
makes at most `n` target queries (the stream's length), the stream never runs out, and the
per-claim term is about the answer and first hint of the label. -/
theorem omuf_le_of_bound (φ : Hn → G ≃ G)
    (A : PK → ProbComp (OracleComp (specA AR X Hn G S) (List (X × S) × Bool)))
    (hA : ∀ pk, ∀ a ∈ support (A pk), IsQueryBoundP a (fun q => isTgt q = true) n)
    (good : PK → S → Option (G × Hn) → Prop) :
    Pr{let r ← omuf KG pre n φ A}[Forges ℓ r.2.1 r.2.2.2] ≤
      Pr{let r ← omExp KG pre n (red φ A)}[Wins ℓ good r.1 r.2.1 r.2.2] +
        ∑ i : Fin (ℓ + 1), Pr{let r ← omuf KG pre n φ A}[BadS φ good i.val r] := by
  refine (omuf_le KG pre n ℓ φ A good).trans (add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_))
  refine prEvent_mono_of_support _ _ _ fun r hr hbad => ?_
  simp only [omuf, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨kp, -, a, ha, L, hL, r', hr', rfl⟩ := hr
  have hinv := simulateQ_run_preservesInv (realImpl φ (pre kp.2)) (TgInv φ)
    (tgInv_preserved φ (pre kp.2)) a _ (fun x t h hx => by simp [ch0] at hx) r' hr'
  have hnf := noFall_of_bound φ (pre kp.2) a n _ (hA kp.1 a ha)
    (by simp [ch0, length_of_mem_unifList n L hL]) (fun x a h hx => by simp at hx) r' hr'
  obtain ⟨hacc, p, hp, hng⟩ := hbad
  refine ⟨hacc, p, hp, fun hg => hng ?_⟩
  have htg : r'.2.2.tg p.1 = (r'.2.1 p.1).map fun ah => (φ ah.2 ah.1, ah.2) := by
    cases hs : r'.2.1 p.1 with
    | none =>
      cases ht : r'.2.2.tg p.1 with
      | none => rfl
      | some th =>
        obtain ⟨a', ha', -⟩ := hinv p.1 th.1 th.2 ht
        simp [hs] at ha'
    | some ah => simpa using hnf p.1 ah.1 ah.2 hs
  simpa [htg] using hg

end Bound

end VoleMole.ROM.OneMore
