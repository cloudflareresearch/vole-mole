import VoleMole.Assumptions.Shift
import VoleMole.Protocols.UOVAssumptions

/-!
# Theorem R: reductions that are black-box in the adversary only

`lean/docs/security/ompr-shift-algebra.md` §2.
-/

open OracleComp OracleSpec VoleMole.ROM.OneMore
open scoped ENNReal

namespace VoleMole.Assumptions.TheoremR

open VoleMole.Assumptions.UOV

/-! ## OMPR^free -/

section Free

variable {DR : Type} (AR : DR → Type) (X Hn T : Type)

/-- The OMPR^free challenger's state: the world's cache, the labelled targets, the log of the
preimage calls (latest first), the number of targets requested. -/
structure FCh where
  ro : (specR AR).QueryCache
  tg : X → Option (T × Hn)
  calls : List T
  nt : ℕ

end Free

section FreeImpl

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {X : Type} [DecidableEq X] {Hn T S : Type} [SampleableType T]

/-- **The OMPR^free challenger**: the world; a target request `(x, h)` draws a fresh uniform
target and records it under the label `x`; a preimage call is answered and logged. -/
def fImpl (pre : T → S) : QueryImpl (specB AR X Hn T S) (StateT (FCh AR X Hn T) ProbComp)
  | .inl d => StateT.mk fun c =>
      (fun r => (r.1, { c with ro := r.2 })) <$> ((specR AR).randomOracle d).run c.ro
  | .inr (.inl (x, h)) => StateT.mk fun c =>
      (fun t => (some t, { c with tg := Function.update c.tg x (some (t, h)), nt := c.nt + 1 })) <$>
        ($ᵗ T)
  | .inr (.inr t) => StateT.mk fun c => pure (pre t, { c with calls := t :: c.calls })

/-- The initial state. -/
def f0 : FCh AR X Hn T := ⟨∅, fun _ => none, [], 0⟩

variable {PK SK : Type} (tr : Trapdoor PK SK T S)

/-- **The OMPR^free experiment** (`uov-open-reductions.md` §3.1), targets on demand. -/
def freeExp (A : PK → ProbComp (OracleComp (specB AR X Hn T S) (Option (X × S)))) :
    ProbComp (PK × Option (X × S) × FCh AR X Hn T) := do
  let kp ← tr.keyGen
  let a ← A kp.1
  let r ← (simulateQ (fImpl (tr.D kp.2)) a).run f0
  pure (kp.1, r.1, r.2)

variable [Zero T]

/-- **The OMPR^free win**: a preimage of a nonzero target `t_x` such that no call was made on an
element of the class of `t_x`; at most `nT` targets requested and `Q` calls made. -/
def FreeWin (cls : T → T → Prop) (nT Q : ℕ) (r : PK × Option (X × S) × FCh AR X Hn T) : Prop :=
  ∃ x s t h, r.2.1 = some (x, s) ∧ r.2.2.tg x = some (t, h) ∧ tr.IsPre r.1 s t ∧ t ≠ 0 ∧
    (∀ z ∈ r.2.2.calls, ¬ cls z t) ∧ r.2.2.nt ≤ nT ∧ r.2.2.calls.length ≤ Q

/-- **`Adv^{free}(nT, Q)`**: calls outside the classes of the targets are free. -/
noncomputable def advOMPRFree (cls : T → T → Prop) (nT Q : ℕ)
    (A : PK → ProbComp (OracleComp (specB AR X Hn T S) (Option (X × S)))) : ℝ≥0∞ :=
  Pr{let r ← freeExp tr A}[FreeWin tr cls nT Q r]

end FreeImpl

/-! ## The reduction's interface, and the atomic operations of the experiment -/

section Specs

variable {DR : Type} (AR : DR → Type) (τ q : ℕ) (X T S : Type)

/-- The world of the experiment: the reduction's world `AR`, and the private random functions of
`A**_D`: the shift lists `S(h_1..h_{k−1})` and the choices `a(H)`. -/
abbrev WA : DR ⊕ (List T ⊕ List T) → Type :=
  Sum.elim AR (Sum.elim (fun _ => Fin τ → T) fun _ => Fin (q + 1) → Fin τ)

instance instSampWA [∀ d, SampleableType (AR d)] [SampleableType T] [NeZero τ] :
    ∀ d, SampleableType (WA AR τ q T d)
  | .inl d => inferInstanceAs (SampleableType (AR d))
  | .inr (.inl _) => inferInstanceAs (SampleableType (Fin τ → T))
  | .inr (.inr _) => inferInstanceAs (SampleableType (Fin (q + 1) → Fin τ))

/-- The output of a completed run: the choices `a(H)` and the `q + 1` forgeries. -/
abbrev Out := (Fin (q + 1) → Fin τ) × List S

/-- The answers of `A**_D` as a next-message function: the shift list after `h_1..h_{k−1}`; the
junk targets of the run `H`; the output of the run `H` given answers to the junk queries. -/
abbrev AnsAdv : List T ⊕ (List T ⊕ (List T × List S)) → Type :=
  Sum.elim (fun _ => Fin τ → T) (Sum.elim (fun _ => List T) fun _ => Option (Out τ q S))

/-- **The reduction's oracles**: those of the OMPR experiment (`specB`: world, labelled targets,
preimage oracle), and `A**_D` as a next-message function. -/
abbrev specRed : OracleSpec ((DR ⊕ ((X × Unit) ⊕ T)) ⊕ (List T ⊕ (List T ⊕ (List T × List S)))) :=
  OracleSpec.ofFn (Sum.elim (AnsB AR X Unit T S) (AnsAdv τ q T S))

/-- The atomic operations of the experiment. -/
inductive Op (DR X T S : Type) (τ : ℕ) where
  /-- the reduction's world -/
  | w (d : DR)
  /-- the shift list after the prefix `hs` -/
  | lst (hs : List T)
  /-- a challenge target under the label `x` -/
  | tgt (x : X)
  /-- a preimage call of the reduction -/
  | inv (t : T)
  /-- the `j`-th junk target of the run `H` -/
  | junk (H : List T) (j : ℕ)
  /-- the output of the run `H` with shift lists `δs`, given the answers `ans` -/
  | fin (H : List T) (δs : List (Fin τ → T)) (ans : List S)

/-- The answers of the atomic operations. -/
abbrev AnsOp : Op DR X T S τ → Type
  | .w d => AR d
  | .lst _ => Fin τ → T
  | .tgt _ => Option T
  | .inv _ => S
  | .junk _ _ => T
  | .fin _ _ _ => Option (Out τ q S)

abbrev specOp : OracleSpec (Op DR X T S τ) := OracleSpec.ofFn (AnsOp AR τ q X T S)

variable {AR τ q X T S}

/-- One atomic operation. -/
def op (o : Op DR X T S τ) : OracleComp (specOp AR τ q X T S) (AnsOp AR τ q X T S o) :=
  liftM ((specOp AR τ q X T S).query o)

/-- **The reduction's queries as atomic operations.** A junk query for a run `H` of length
`q + 1` forces its `q` junk targets. An output query forces the junk targets and the `q + 1` shift
lists of the run, then asks for the output. -/
def prog : QueryImpl (specRed AR τ q X T S) (OracleComp (specOp AR τ q X T S))
  | .inl (.inl d) => op (.w d)
  | .inl (.inr (.inl (x, _))) => op (.tgt x)
  | .inl (.inr (.inr t)) => op (.inv t)
  | .inr (.inl hs) => op (.lst hs)
  | .inr (.inr (.inl H)) =>
      if H.length = q + 1 then (List.range q).mapM fun j => op (.junk H j) else pure []
  | .inr (.inr (.inr (H, ans))) =>
      if H.length = q + 1 then do
        let _ ← (List.range q).mapM fun j => op (.junk H j)
        let δs ← (List.range (q + 1)).mapM fun k => op (.lst (H.take k))
        op (.fin H δs ans)
      else pure none

/-- An OMPR adversary as a reduction that ignores `A**_D`. -/
def liftB : QueryImpl (specB AR X Unit T S) (OracleComp (specRed AR τ q X T S)) := fun o =>
  liftM ((specRed AR τ q X T S).query (.inl o))

/-- The candidates of the run `H` with shift lists `δs` and choices `a`: `h_k ⊕ δ_{k,a_k}`. -/
def cands [AddCommGroup T] (H : List T) (δs : List (Fin τ → T)) (a : Fin (q + 1) → Fin τ) :
    List T :=
  (List.finRange (q + 1)).map fun k : Fin (q + 1) => H.getD k.val 0 + δs.getD k.val 0 (a k)

/-- `A**_D`'s check of the answers to the junk queries of the run `H`: there are `q`, and the
`j`-th is a preimage of the `j`-th junk target. -/
def valid {PK : Type} (rel : PK → S → T → Prop) [∀ pk s t, Decidable (rel pk s t)] (pk : PK)
    (jt : List T × ℕ → Option T) (H : List T) (ans : List S) : Bool :=
  decide (ans.length = q) && ans.zipIdx.all fun p =>
    match jt (H, p.2) with
    | some t => decide (rel pk p.1 t)
    | none => false

variable (AR τ q X T S) in
/-- The state of the experiment: the world's cache; the reduction's remaining targets, labelled
targets and number of preimage calls; `A**_D`'s junk targets, the number drawn, the outputs of the
completed runs, and their number. -/
structure RSt where
  ro : (specR (WA AR τ q T)).QueryCache
  rem : ℕ
  tg : X → Option (T × Unit)
  iq : ℕ
  jt : List T × ℕ → Option T
  nj : ℕ
  out : List T → Option (Out τ q S)
  nc : ℕ

/-- The reduction's OMPR challenger state inside the experiment's. -/
def RSt.toCh (s : RSt AR τ q X T S) : Ch AR X Unit T :=
  ⟨∅, [], s.tg, s.iq⟩

/-- The initial state, with `n` targets. -/
def r0 (n : ℕ) : RSt AR τ q X T S := ⟨∅, n, fun _ => none, 0, fun _ => none, 0, fun _ => none, 0⟩

end Specs

section Real

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {τ q : ℕ} [NeZero τ] {X : Type} [DecidableEq X] {T S : Type} [AddCommGroup T]
  [SampleableType T] [DecidableEq T]
  {PK SK : Type} (rel : PK → S → T → Prop) [∀ pk s t, Decidable (rel pk s t)]

/-- **The experiment's handler**: the OMPR challenger (targets drawn on demand, at most `rem`)
and `A**_D` (`ompr-shift-algebra.md` §2.1). The output of a completed run is memoized: it is a
function of `H`. -/
def μR (pk : PK) (pre : T → S) :
    QueryImpl (specOp AR τ q X T S) (StateT (RSt AR τ q X T S) ProbComp)
  | .w d => StateT.mk fun s => (fun r => (r.1, { s with ro := r.2 })) <$>
      ((specR (WA AR τ q T)).randomOracle (.inl d)).run s.ro
  | .lst hs => StateT.mk fun s => (fun r => (r.1, { s with ro := r.2 })) <$>
      ((specR (WA AR τ q T)).randomOracle (.inr (.inl hs))).run s.ro
  | .tgt x => StateT.mk fun s =>
      if s.rem = 0 then pure (none, s) else
        (fun t => (some t,
          { s with tg := Function.update s.tg x (some (t, ())), rem := s.rem - 1 })) <$> ($ᵗ T)
  | .inv t => StateT.mk fun s => pure (pre t, { s with iq := s.iq + 1 })
  | .junk H j => StateT.mk fun s =>
      match s.jt (H, j) with
      | some t => pure (t, s)
      | none =>
          (fun t => (t, { s with jt := Function.update s.jt (H, j) (some t), nj := s.nj + 1 })) <$>
            ($ᵗ T)
  | .fin H δs ans => StateT.mk fun s =>
      if valid (q := q) rel pk s.jt H ans then
        match s.out H with
        | some o => pure (some o, s)
        | none =>
            (fun r => (some (r.1, (cands H δs r.1).map pre),
              { s with
                ro := r.2
                out := Function.update s.out H (some (r.1, (cands H δs r.1).map pre))
                nc := s.nc + 1 })) <$>
              ((specR (WA AR τ q T)).randomOracle (.inr (.inr H))).run s.ro
      else pure (none, s)

variable (tr : Trapdoor PK SK T S) [∀ pk s t, Decidable (tr.IsPre pk s t)]

/-- **The experiment of Theorem R**: the reduction `R` in the OMPR game with `n` targets, with
`A**_D` as a next-message function. -/
def redExp (n : ℕ)
    (R : PK → ProbComp (OracleComp (specRed AR τ q X T S) (List (X × S)))) :
    ProbComp (PK × List (X × S) × RSt AR τ q X T S) := do
  let kp ← tr.keyGen
  let r ← R kp.1
  let z ← (simulateQ (μR tr.IsPre kp.1 (tr.D kp.2)) (simulateQ prog r)).run (r0 n)
  pure (kp.1, z.1, z.2)

end Real

/-! ## The OMPR^free adversary `M` -/

section MDefs

variable (τ q : ℕ) (X T S : Type)

/-- `M`'s labels in the OMPR^free game: the reduction's labels, and `(H, j)` for the `j`-th junk
target of the run `H`. -/
abbrev XM := X ⊕ (List T × ℕ)

/-- **`M`'s state.** Its simulation of the experiment: the reduction's remaining targets, the
target of every label, the number of the reduction's calls, the number of junk targets, the
outputs of the completed runs. Its own record: all its calls (latest first), the junk answers of
the completed runs (`jc`). And the bookkeeping of the proof, which its output does not depend on:
all targets drawn (`tl`), the calls that may be charged (`chg`: the reduction's calls and the
counted candidates), the number `W` of counted candidates, the number `K` of completed runs, the
flags `bad` (a bad event on values) and `hit` (the lottery was won: `W > q·K` after some run). -/
structure MSt where
  rem : ℕ
  tg : XM X T → Option T
  iq : ℕ
  nj : ℕ
  out : List T → Option (Out τ q S)
  calls : List T
  jc : List (XM X T × S)
  tl : List T
  chg : List T
  W : ℕ
  K : ℕ
  bad : Bool
  hit : Bool

end MDefs

section MImpl

variable {DR : Type} {AR : DR → Type} {τ q : ℕ} {X : Type} [DecidableEq X] {T S : Type}
  [AddCommGroup T] [DecidableEq T]
  (cls : T → T → Prop) [DecidableRel cls]

/-- `M`'s initial state, with `n` targets for the reduction. -/
def m0 (n : ℕ) : MSt τ q X T S :=
  ⟨n, fun _ => none, 0, 0, fun _ => none, [], [], [], [], 0, 0, false, false⟩

/-- A new target `t` under the label `x`. **Bad events on values** (E1, E2 of the note): `t = 0`;
`t` lies in the class of an earlier target; `t` lies in the class of an earlier call that is not
in `chg`. -/
def MSt.addT (m : MSt τ q X T S) (x : XM X T) (t : T) : MSt τ q X T S :=
  { m with
    tg := Function.update m.tg x (some t)
    tl := t :: m.tl
    bad := m.bad || decide (t = 0) || m.tl.any (fun t' => decide (cls t t')) ||
      m.calls.any fun z => decide (cls z t) && decide (z ∉ m.chg) }

/-- A value is *useful* if it lies in the class of a target drawn so far. -/
def useful (tl : List T) (z : T) : Bool := tl.any fun t => decide (cls z t)

/-- The first useful shift of request `k` of the run `H`, if any. -/
def firstU (tl : List T) (H : List T) (δs : List (Fin τ → T)) (k : Fin (q + 1)) :
    Option (Fin τ) :=
  (List.finRange τ).find? fun a => useful cls tl (H.getD k.val 0 + δs.getD k.val 0 a)

/-- The *counted* requests of a run: those whose choice `a k` is the first useful shift. -/
def counted (tl : List T) (H : List T) (δs : List (Fin τ → T)) (a : Fin (q + 1) → Fin τ) :
    List (Fin (q + 1)) :=
  (List.finRange (q + 1)).filter fun k => decide (firstU cls tl H δs k = some (a k))

/-- The junk claims of a completed run: the label `(H, j)` with the `j`-th answer. -/
def jclaims (H : List T) (ans : List S) : List (XM X T × S) :=
  ans.zipIdx.map fun p => (Sum.inr (H, p.2), p.1)

/-- The run `H` is completed with choices `a` and forgeries `ss`. **Bad event** (E3 of the note):
a candidate is useful but not counted (then two shifts of one request are useful). -/
def MSt.complete (m : MSt τ q X T S) (H : List T) (δs : List (Fin τ → T)) (ans : List S)
    (a : Fin (q + 1) → Fin τ) (ss : List S) : MSt τ q X T S :=
  { m with
    out := Function.update m.out H (some (a, ss))
    calls := (cands H δs a).reverse ++ m.calls
    jc := jclaims H ans ++ m.jc
    chg := (counted cls m.tl H δs a).map (fun k => H.getD k.val 0 + δs.getD k.val 0 (a k)) ++ m.chg
    W := m.W + (counted cls m.tl H δs a).length
    K := m.K + 1
    bad := m.bad || (List.finRange (q + 1)).any fun k =>
      useful cls m.tl (H.getD k.val 0 + δs.getD k.val 0 (a k)) &&
        decide (firstU cls m.tl H δs k ≠ some (a k))
    hit := m.hit || decide (q * (m.K + 1) < m.W + (counted cls m.tl H δs a).length) }

variable {PK : Type} (rel : PK → S → T → Prop) [∀ pk s t, Decidable (rel pk s t)]

/-- `M`'s queries to the world of its OMPR^free game: the reduction's world, a shift list, the
choices of a run. -/
def fqW (d : DR) : OracleComp (specB (WA AR τ q T) (XM X T) Unit T S) (AR d) :=
  liftM ((specB (WA AR τ q T) (XM X T) Unit T S).query (.inl (.inl d)))

@[inherit_doc fqW]
def fqL (hs : List T) : OracleComp (specB (WA AR τ q T) (XM X T) Unit T S) (Fin τ → T) :=
  liftM ((specB (WA AR τ q T) (XM X T) Unit T S).query (.inl (.inr (.inl hs))))

@[inherit_doc fqW]
def fqA (H : List T) :
    OracleComp (specB (WA AR τ q T) (XM X T) Unit T S) (Fin (q + 1) → Fin τ) :=
  liftM ((specB (WA AR τ q T) (XM X T) Unit T S).query (.inl (.inr (.inr H))))

/-- `M`'s request of a target under the label `x`. -/
def fqT (x : XM X T) : OracleComp (specB (WA AR τ q T) (XM X T) Unit T S) (Option T) :=
  liftM ((specB (WA AR τ q T) (XM X T) Unit T S).query (.inr (.inl (x, ()))))

/-- `M`'s preimage call. -/
def fqD (z : T) : OracleComp (specB (WA AR τ q T) (XM X T) Unit T S) S :=
  liftM ((specB (WA AR τ q T) (XM X T) Unit T S).query (.inr (.inr z)))

/-- **`M`'s handler** for the atomic operations (`ompr-shift-algebra.md` §2.2). The world and the
reduction's calls are forwarded. Challenge and junk targets are requested from the game. The shift
lists and the choices `a(H)` are values of the game's world. When a run is completed, `M` stores
the junk answers and calls `D` on the `q + 1` candidates. -/
def μM (pk : PK) :
    QueryImpl (specOp AR τ q X T S)
      (StateT (MSt τ q X T S) (OracleComp (specB (WA AR τ q T) (XM X T) Unit T S)))
  | .w d => StateT.mk fun m => (fun a => (a, m)) <$> fqW d
  | .lst hs => StateT.mk fun m => (fun a => (a, m)) <$> fqL hs
  | .tgt x => StateT.mk fun m =>
      if m.rem = 0 then pure (none, m) else
        (fun o : Option T => match o with
          | some t => (some t, { m.addT cls (.inl x) t with rem := m.rem - 1 })
          | none => (none, m)) <$> fqT (.inl x)
  | .inv t => StateT.mk fun m =>
      (fun s => (s, { m with iq := m.iq + 1, calls := t :: m.calls, chg := t :: m.chg })) <$>
        fqD t
  | .junk H j => StateT.mk fun m =>
      match m.tg (.inr (H, j)) with
      | some t => pure (t, m)
      | none =>
          (fun o : Option T => match o with
            | some t => (t, { m.addT cls (.inr (H, j)) t with nj := m.nj + 1 })
            | none => (0, m)) <$> fqT (.inr (H, j))
  | .fin H δs ans => StateT.mk fun m =>
      if valid (q := q) rel pk (fun k => m.tg (.inr k)) H ans then
        match m.out H with
        | some o => pure (some o, m)
        | none => do
            let a ← fqA H
            let ss ← (cands H δs a).mapM fqD
            pure (some (a, ss), m.complete cls H δs ans a ss)
      else pure (none, m)

/-- `M`'s final step: among the reduction's claims and the stored junk claims, the first whose
target is nonzero and has no call in its class. -/
def pick (cl : List (X × S)) (m : MSt τ q X T S) : Option (XM X T × S) :=
  ((cl.map fun p => ((Sum.inl p.1 : XM X T), p.2)) ++ m.jc).find? fun p =>
    match m.tg p.1 with
    | some t => decide (t ≠ 0) && m.calls.all fun z => !decide (cls z t)
    | none => false

/-- **The OMPR^free adversary `M`** built from the reduction `R`. -/
def redM (n : ℕ) (R : PK → ProbComp (OracleComp (specRed AR τ q X T S) (List (X × S))))
    (pk : PK) :
    ProbComp (OracleComp (specB (WA AR τ q T) (XM X T) Unit T S) (Option (XM X T × S))) :=
  (fun r => (fun z => pick cls z.1 z.2) <$>
    (simulateQ (μM cls rel pk) (simulateQ prog r)).run (m0 n)) <$> R pk

end MImpl

/-! ## The joint experiment: `M` in the OMPR^free game -/

section Joint

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {τ q : ℕ} [NeZero τ] {X : Type} [DecidableEq X] {T S : Type} [AddCommGroup T]
  [SampleableType T] [DecidableEq T]
  (cls : T → T → Prop) [DecidableRel cls]
  {PK SK : Type} (rel : PK → S → T → Prop) [∀ pk s t, Decidable (rel pk s t)]

/-- The joint state: `M`'s and the OMPR^free challenger's. -/
abbrev JSt (AR : DR → Type) (τ q : ℕ) (X T S : Type) :=
  MSt τ q X T S × FCh (WA AR τ q T) (XM X T) Unit T

/-- `M`'s handler run against the OMPR^free challenger, as one handler. -/
def jImpl (pk : PK) (pre : T → S) :
    QueryImpl (specOp AR τ q X T S) (StateT (JSt AR τ q X T S) ProbComp) :=
  fun o => StateT.mk fun s => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (fImpl pre) ((μM cls rel pk o).run s.1)).run s.2

theorem collapseJ (pk : PK) (pre : T → S) {α : Type} (oa : OracleComp (specOp AR τ q X T S) α)
    (m : MSt τ q X T S) (g : FCh (WA AR τ q T) (XM X T) Unit T) :
    (simulateQ (fImpl pre) ((simulateQ (μM cls rel pk) oa).run m)).run g =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (jImpl cls rel pk pre) oa).run (m, g) := by
  refine simulateQ_StateT_StateT_compose _ _ _ (fun o m g => ?_) oa m g
  show _ = _ <$> ((fun r : (_ × _) × _ => (r.1.1, (r.1.2, r.2))) <$> _)
  rw [Functor.map_map]
  exact (id_map _).symm

/-- The experiment's state that a joint state represents. -/
def π (s : JSt AR τ q X T S) : RSt AR τ q X T S :=
  ⟨s.2.ro, s.1.rem, fun x => (s.1.tg (.inl x)).map fun t => (t, ()), s.1.iq,
    fun k => s.1.tg (.inr k), s.1.nj, s.1.out, s.1.K⟩

/-! ### The steps, explicitly -/

variable (pk : PK) (pre : T → S)

omit [AddCommGroup T] in
lemma sim_fqW (d : DR) (g : FCh (WA AR τ q T) (XM X T) Unit T) :
    (simulateQ (fImpl pre) (fqW (τ := τ) (q := q) (X := X) (T := T) (S := S) d)).run g =
      (fun r => (r.1, { g with ro := r.2 })) <$>
        ((specR (WA AR τ q T)).randomOracle (.inl d)).run g.ro := by
  unfold fqW
  erw [simulateQ_spec_query]
  rfl

omit [AddCommGroup T] in
lemma sim_fqL (hs : List T) (g : FCh (WA AR τ q T) (XM X T) Unit T) :
    (simulateQ (fImpl pre) (fqL (AR := AR) (q := q) (X := X) (S := S) hs)).run g =
      (fun r => (r.1, { g with ro := r.2 })) <$>
        ((specR (WA AR τ q T)).randomOracle (.inr (.inl hs))).run g.ro := by
  unfold fqL
  erw [simulateQ_spec_query]
  rfl

omit [AddCommGroup T] in
lemma sim_fqA (H : List T) (g : FCh (WA AR τ q T) (XM X T) Unit T) :
    (simulateQ (fImpl pre) (fqA (AR := AR) (τ := τ) (X := X) (S := S) H)).run g =
      (fun r => (r.1, { g with ro := r.2 })) <$>
        ((specR (WA AR τ q T)).randomOracle (.inr (.inr H))).run g.ro := by
  unfold fqA
  erw [simulateQ_spec_query]
  rfl

omit [AddCommGroup T] in
lemma sim_fqT (x : XM X T) (g : FCh (WA AR τ q T) (XM X T) Unit T) :
    (simulateQ (fImpl pre) (fqT (AR := AR) (τ := τ) (q := q) (S := S) x)).run g =
      (fun t => (some t, { g with tg := Function.update g.tg x (some (t, ())), nt := g.nt + 1 })) <$>
        ($ᵗ T) := by
  unfold fqT
  erw [simulateQ_spec_query]
  rfl

omit [AddCommGroup T] in
lemma sim_fqD (z : T) (g : FCh (WA AR τ q T) (XM X T) Unit T) :
    (simulateQ (fImpl pre) (fqD (AR := AR) (τ := τ) (q := q) (X := X) (S := S) z)).run g =
      pure (pre z, { g with calls := z :: g.calls }) := by
  unfold fqD
  erw [simulateQ_spec_query]
  rfl

omit [AddCommGroup T] in
/-- `M`'s calls on a list of candidates, against the challenger. -/
lemma sim_calls (L : List T) (g : FCh (WA AR τ q T) (XM X T) Unit T) :
    (simulateQ (fImpl pre) (L.mapM (fqD (AR := AR) (τ := τ) (q := q) (X := X) (S := S)))).run g =
      pure (L.map pre, { g with calls := L.reverse ++ g.calls }) := by
  induction L generalizing g with
  | nil => simp
  | cons z L ih =>
    rw [List.mapM_cons]
    simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, sim_fqD, pure_bind, ih,
      StateT.run_pure]
    simp

omit [AddCommGroup T] in
lemma sim_calls' (L : List T) (g : FCh (WA AR τ q T) (XM X T) Unit T) :
    (L.mapM fun z => simulateQ (fImpl pre)
      (fqD (AR := AR) (τ := τ) (q := q) (X := X) (S := S) z)).run g =
      pure (L.map pre, { g with calls := L.reverse ++ g.calls }) := by
  simpa using sim_calls pre L g

lemma j_w (d : DR) (s : JSt AR τ q X T S) :
    (jImpl (S := S) cls rel pk pre (.w d)).run s =
      (fun r => (r.1, (s.1, { s.2 with ro := r.2 }))) <$>
        ((specR (WA AR τ q T)).randomOracle (.inl d)).run s.2.ro := by
  simp [jImpl, μM, sim_fqW]

lemma j_lst (hs : List T) (s : JSt AR τ q X T S) :
    (jImpl (S := S) cls rel pk pre (.lst hs)).run s =
      (fun r => (r.1, (s.1, { s.2 with ro := r.2 }))) <$>
        ((specR (WA AR τ q T)).randomOracle (.inr (.inl hs))).run s.2.ro := by
  simp [jImpl, μM, sim_fqL]

lemma j_tgt_zero (x : X) (s : JSt AR τ q X T S) (h : s.1.rem = 0) :
    (jImpl (S := S) cls rel pk pre (.tgt x)).run s = pure (none, s) := by
  simp [jImpl, μM, h]

lemma j_tgt (x : X) (s : JSt AR τ q X T S) (h : s.1.rem ≠ 0) :
    (jImpl (S := S) cls rel pk pre (.tgt x)).run s =
      (fun t => (some t, ({ s.1.addT cls (.inl x) t with rem := s.1.rem - 1 },
        { s.2 with tg := Function.update s.2.tg (.inl x) (some (t, ())), nt := s.2.nt + 1 }))) <$>
        ($ᵗ T) := by
  simp [jImpl, μM, h, sim_fqT]

lemma j_inv (t : T) (s : JSt AR τ q X T S) :
    (jImpl (S := S) cls rel pk pre (.inv t)).run s =
      pure (pre t, ({ s.1 with iq := s.1.iq + 1, calls := t :: s.1.calls, chg := t :: s.1.chg },
        { s.2 with calls := t :: s.2.calls })) := by
  simp [jImpl, μM, sim_fqD]

lemma j_junk_some (H : List T) (j : ℕ) (s : JSt AR τ q X T S) (t : T)
    (h : s.1.tg (.inr (H, j)) = some t) :
    (jImpl (S := S) cls rel pk pre (.junk H j)).run s = pure (t, s) := by
  simp [jImpl, μM, h]

lemma j_junk (H : List T) (j : ℕ) (s : JSt AR τ q X T S) (h : s.1.tg (.inr (H, j)) = none) :
    (jImpl (S := S) cls rel pk pre (.junk H j)).run s =
      (fun t => (t, ({ s.1.addT cls (.inr (H, j)) t with nj := s.1.nj + 1 },
        { s.2 with tg := Function.update s.2.tg (.inr (H, j)) (some (t, ())),
                   nt := s.2.nt + 1 }))) <$> ($ᵗ T) := by
  simp [jImpl, μM, h, sim_fqT]

lemma j_fin_invalid (H : List T) (δs : List (Fin τ → T)) (ans : List S) (s : JSt AR τ q X T S)
    (h : valid (q := q) rel pk (fun k => s.1.tg (.inr k)) H ans = false) :
    (jImpl (S := S) cls rel pk pre (.fin H δs ans)).run s = pure (none, s) := by
  simp [jImpl, μM, h]

lemma j_fin_some (H : List T) (δs : List (Fin τ → T)) (ans : List S) (s : JSt AR τ q X T S)
    (h : valid (q := q) rel pk (fun k => s.1.tg (.inr k)) H ans = true) (o : Out τ q S)
    (ho : s.1.out H = some o) :
    (jImpl (S := S) cls rel pk pre (.fin H δs ans)).run s = pure (some o, s) := by
  simp [jImpl, μM, h, ho]

lemma j_fin (H : List T) (δs : List (Fin τ → T)) (ans : List S) (s : JSt AR τ q X T S)
    (h : valid (q := q) rel pk (fun k => s.1.tg (.inr k)) H ans = true)
    (ho : s.1.out H = none) :
    (jImpl (S := S) cls rel pk pre (.fin H δs ans)).run s =
      (fun r => (some (r.1, (cands H δs r.1).map pre),
        (s.1.complete cls H δs ans r.1 ((cands H δs r.1).map pre),
          { s.2 with ro := r.2, calls := (cands H δs r.1).reverse ++ s.2.calls }))) <$>
        ((specR (WA AR τ q T)).randomOracle (.inr (.inr H))).run s.2.ro := by
  simp [jImpl, μM, h, ho, sim_fqA, sim_calls']

/-! ### The joint experiment projects to the experiment -/

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [AddCommGroup T] [SampleableType T]
  [DecidableEq T] in
lemma map_upd (g : X → Option T) (x : X) (t : T) :
    (fun y => Option.map (fun t => (t, ())) (Function.update g x (some t) y)) =
      Function.update (fun y => Option.map (fun t => (t, ())) (g y)) x (some (t, ())) := by
  funext y
  by_cases h : y = x
  · subst h; simp
  · simp [h]

/-- Every atomic operation of the joint experiment, projected, is the experiment's. -/
theorem proj_step (o : Op DR X T S τ) (s : JSt AR τ q X T S) :
    (fun z => (z.1, π z.2)) <$> (jImpl cls rel pk pre o).run s = (μR rel pk pre o).run (π s) := by
  cases o with
  | w d => rw [j_w]; simp [μR, π]
  | lst hs => rw [j_lst]; simp [μR, π]
  | tgt x =>
    by_cases h : s.1.rem = 0
    · rw [j_tgt_zero _ _ _ _ _ _ h]; simp [μR, π, h]
    · rw [j_tgt _ _ _ _ _ _ h]
      simp [μR, π, h, MSt.addT, map_upd]
  | inv t => rw [j_inv]; simp [μR, π]
  | junk H j =>
    cases h : s.1.tg (.inr (H, j)) with
    | some t => rw [j_junk_some _ _ _ _ _ _ _ t h]; simp [μR, π, h]
    | none =>
      rw [j_junk _ _ _ _ _ _ _ h]
      simp [μR, π, h, MSt.addT]
      rfl
  | fin H δs ans =>
    cases h : valid (q := q) rel pk (fun k => s.1.tg (.inr k)) H ans with
    | false => rw [j_fin_invalid _ _ _ _ _ _ _ _ h]; simp [μR, π, h]
    | true =>
      cases ho : s.1.out H with
      | some o => rw [j_fin_some _ _ _ _ _ _ _ _ h o ho]; simp [μR, π, h, ho]
      | none =>
        rw [j_fin _ _ _ _ _ _ _ _ h ho]
        simp [μR, π, h, ho, MSt.complete]

/-! ### The invariant of the joint experiment -/

variable (n : ℕ)

/-- **The invariant of the joint experiment.** `M`'s record agrees with the challenger's state
(`tg_eq`, `calls_eq`); the counters (`nt_eq`, `calls_len`, `chg_len`); without a win of the
lottery, `W ≤ q·K` (`lot`); without a bad event, targets are nonzero and lie in distinct classes
(`ne0`, `inj`), and every call in the class of a target is in `chg` (`chgd`); the junk claims are
`q` per completed run, on distinct junk labels, and good (`jc_*`); the choices of a run that is
not completed are not drawn (`fresh`). -/
structure Inv (s : JSt AR τ q X T S) : Prop where
  tg_eq : ∀ x, s.2.tg x = (s.1.tg x).map fun t => (t, ())
  calls_eq : s.2.calls = s.1.calls
  nt_eq : s.2.nt + s.1.rem = n + s.1.nj
  calls_len : s.1.calls.length = s.1.iq + (q + 1) * s.1.K
  chg_len : s.1.chg.length = s.1.iq + s.1.W
  lot : s.1.hit = false → s.1.W ≤ q * s.1.K
  tl_mem : ∀ x t, s.1.tg x = some t → t ∈ s.1.tl
  ne0 : s.1.bad = false → ∀ x t, s.1.tg x = some t → t ≠ 0
  inj : s.1.bad = false → ∀ x₁ x₂ t₁ t₂, s.1.tg x₁ = some t₁ → s.1.tg x₂ = some t₂ →
    cls t₁ t₂ → x₁ = x₂
  chgd : s.1.bad = false → ∀ z ∈ s.1.calls, ∀ x t, s.1.tg x = some t → cls z t → z ∈ s.1.chg
  jc_nd : (s.1.jc.map Prod.fst).Nodup
  jc_len : s.1.jc.length = q * s.1.K
  jc_lab : ∀ p ∈ s.1.jc, ∃ H j, p.1 = .inr (H, j) ∧ (s.1.out H).isSome
  jc_good : ∀ p ∈ s.1.jc, ∃ t, s.1.tg p.1 = some t ∧ rel pk p.2 t
  fresh : ∀ H, s.1.out H = none → s.2.ro (.inr (.inr H)) = none

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [DecidableEq X] [AddCommGroup T]
  [SampleableType T] [DecidableEq T] in
lemma valid_iff (jt : List T × ℕ → Option T) (H : List T) (ans : List S) :
    valid (q := q) rel pk jt H ans = true ↔
      ans.length = q ∧ ∀ p ∈ ans.zipIdx, ∃ t, jt (H, p.2) = some t ∧ rel pk p.1 t := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine and_congr_right fun _ => forall₂_congr fun p _ => ?_
  cases jt (H, p.2) <;> simp

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [SampleableType T] [DecidableEq X]
  [DecidableEq T] [DecidableRel cls] [∀ pk s t, Decidable (rel pk s t)] in
theorem inv_init : Inv (AR := AR) (τ := τ) (q := q) (X := X) cls rel pk n (m0 n, f0) where
  tg_eq _ := rfl
  calls_eq := rfl
  nt_eq := by simp [m0, f0]
  calls_len := by simp [m0]
  chg_len := by simp [m0]
  lot _ := by simp [m0]
  tl_mem x t h := by simp [m0] at h
  ne0 _ x t h := by simp [m0] at h
  inj _ x₁ x₂ t₁ t₂ h := by simp [m0] at h
  chgd _ z hz := by simp [m0] at hz
  jc_nd := by simp [m0]
  jc_len := by simp [m0]
  jc_lab p hp := by simp [m0] at hp
  jc_good p hp := by simp [m0] at hp
  fresh _ _ := rfl

variable {cls rel pk n}

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [SampleableType T] [DecidableEq X]
  [DecidableEq T] [DecidableRel cls] [∀ pk s t, Decidable (rel pk s t)] in
/-- The world's cache changes outside the choices of the runs that are not completed. -/
theorem Inv.ro {s : JSt AR τ q X T S} (hI : Inv cls rel pk n s)
    (c : (specR (WA AR τ q T)).QueryCache)
    (hc : ∀ H, s.1.out H = none → c (.inr (.inr H)) = none) :
    Inv cls rel pk n (s.1, { s.2 with ro := c }) :=
  { hI with fresh := hc }

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [SampleableType T] in
lemma addT_bad {m : MSt τ q X T S} {x : XM X T} {t : T} (hb : (m.addT cls x t).bad = false) :
    m.bad = false ∧ t ≠ 0 ∧ (∀ t' ∈ m.tl, ¬ cls t t') ∧ ∀ z ∈ m.calls, cls z t → z ∈ m.chg := by
  simp only [MSt.addT, Bool.or_eq_false_iff, decide_eq_false_iff_not, List.any_eq_false,
    Bool.and_eq_true, decide_eq_true_eq, not_and, not_not] at hb
  exact ⟨hb.1.1.1, hb.1.1.2, hb.1.2, hb.2⟩

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [SampleableType T]
  [∀ pk s t, Decidable (rel pk s t)] in
/-- A new target keeps the invariant. -/
theorem Inv.addT (hsym : ∀ a b, cls a b → cls b a) {s : JSt AR τ q X T S} (hI : Inv cls rel pk n s)
    (x : XM X T) (t : T) (r' j' : ℕ) (hx : ∀ p ∈ s.1.jc, p.1 ≠ x)
    (hnum : s.2.nt + 1 + r' = n + j') :
    Inv cls rel pk n ({ s.1.addT cls x t with rem := r', nj := j' },
      { s.2 with tg := Function.update s.2.tg x (some (t, ())), nt := s.2.nt + 1 }) where
  tg_eq y := by
    by_cases h : y = x
    · subst h; simp [MSt.addT]
    · simpa [MSt.addT, h] using hI.tg_eq y
  calls_eq := hI.calls_eq
  nt_eq := hnum
  calls_len := hI.calls_len
  chg_len := hI.chg_len
  lot := hI.lot
  tl_mem y t' h := by
    by_cases hy : y = x
    · subst hy
      simp only [MSt.addT, Function.update_self, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · simp only [MSt.addT, Function.update_of_ne hy] at h
      exact List.mem_cons_of_mem _ (hI.tl_mem y t' h)
  ne0 hb y t' h := by
    obtain ⟨hb0, ht0, -, -⟩ := addT_bad (x := x) hb
    by_cases hy : y = x
    · subst hy
      simp only [MSt.addT, Function.update_self, Option.some.injEq] at h
      exact h ▸ ht0
    · simp only [MSt.addT, Function.update_of_ne hy] at h
      exact hI.ne0 hb0 y t' h
  inj hb x₁ x₂ t₁ t₂ h₁ h₂ hc := by
    obtain ⟨hb0, -, htl, -⟩ := addT_bad (x := x) hb
    by_cases h1 : x₁ = x <;> by_cases h2 : x₂ = x
    · rw [h1, h2]
    · subst h1
      simp only [MSt.addT, Function.update_self, Option.some.injEq, Function.update_of_ne h2]
        at h₁ h₂
      subst h₁
      exact absurd hc (htl t₂ (hI.tl_mem x₂ t₂ h₂))
    · subst h2
      simp only [MSt.addT, Function.update_self, Option.some.injEq, Function.update_of_ne h1]
        at h₁ h₂
      subst h₂
      exact absurd (hsym _ _ hc) (htl t₁ (hI.tl_mem x₁ t₁ h₁))
    · simp only [MSt.addT, Function.update_of_ne h1, Function.update_of_ne h2] at h₁ h₂
      exact hI.inj hb0 x₁ x₂ t₁ t₂ h₁ h₂ hc
  chgd hb z hz y t' h hc := by
    obtain ⟨hb0, -, -, hcl⟩ := addT_bad (x := x) hb
    by_cases hy : y = x
    · subst hy
      simp only [MSt.addT, Function.update_self, Option.some.injEq] at h
      subst h
      exact hcl z hz hc
    · simp only [MSt.addT, Function.update_of_ne hy] at h
      exact hI.chgd hb0 z hz y t' h hc
  jc_nd := hI.jc_nd
  jc_len := hI.jc_len
  jc_lab := hI.jc_lab
  jc_good p hp := by
    obtain ⟨t', h, hr⟩ := hI.jc_good p hp
    exact ⟨t', by simpa [MSt.addT, Function.update_of_ne (hx p hp)] using h, hr⟩
  fresh := hI.fresh

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [SampleableType T] [DecidableEq X]
  [DecidableEq T] [DecidableRel cls] [∀ pk s t, Decidable (rel pk s t)] in
/-- A call of the reduction keeps the invariant. -/
theorem Inv.inv {s : JSt AR τ q X T S} (hI : Inv cls rel pk n s) (t : T) :
    Inv cls rel pk n
      ({ s.1 with iq := s.1.iq + 1, calls := t :: s.1.calls, chg := t :: s.1.chg },
        { s.2 with calls := t :: s.2.calls }) where
  tg_eq := hI.tg_eq
  calls_eq := by simp [hI.calls_eq]
  nt_eq := hI.nt_eq
  calls_len := by simp [hI.calls_len]; omega
  chg_len := by simp [hI.chg_len]; omega
  lot := hI.lot
  tl_mem := hI.tl_mem
  ne0 := hI.ne0
  inj := hI.inj
  chgd hb z hz y t' h hc := by
    rcases List.mem_cons.1 hz with rfl | hz
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hI.chgd hb z hz y t' h hc)
  jc_nd := hI.jc_nd
  jc_len := hI.jc_len
  jc_lab := hI.jc_lab
  jc_good := hI.jc_good
  fresh := hI.fresh

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [SampleableType T]
  [DecidableEq X] in
lemma complete_bad {m : MSt τ q X T S} {H : List T} {δs : List (Fin τ → T)} {ans : List S}
    {a : Fin (q + 1) → Fin τ} {ss : List S} (hb : (m.complete cls H δs ans a ss).bad = false) :
    m.bad = false ∧ ∀ k : Fin (q + 1),
      useful cls m.tl (H.getD k.val 0 + δs.getD k.val 0 (a k)) = true →
        firstU cls m.tl H δs k = some (a k) := by
  simp [MSt.complete] at hb
  exact hb

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [SampleableType T]
  [DecidableEq X] in
/-- A completed run keeps the invariant. -/
theorem Inv.complete {s : JSt AR τ q X T S} (hI : Inv cls rel pk n s) (H : List T)
    (δs : List (Fin τ → T)) (ans : List S)
    (hv : valid (q := q) rel pk (fun k => s.1.tg (.inr k)) H ans = true) (ho : s.1.out H = none)
    (a : Fin (q + 1) → Fin τ) (ss : List S) (c : (specR (WA AR τ q T)).QueryCache)
    (hc : ∀ H', H' ≠ H → c (.inr (.inr H')) = s.2.ro (.inr (.inr H'))) :
    Inv cls rel pk n (s.1.complete cls H δs ans a ss,
      { s.2 with ro := c, calls := (cands H δs a).reverse ++ s.2.calls }) := by
  obtain ⟨hlen, hans⟩ := (valid_iff rel pk _ H ans).1 hv
  have hcl : (cands H δs a).length = q + 1 := by simp [cands]
  refine
    { tg_eq := hI.tg_eq
      calls_eq := by simp [MSt.complete, hI.calls_eq]
      nt_eq := hI.nt_eq
      calls_len := by simp [MSt.complete, hcl, hI.calls_len]; ring
      chg_len := by simp [MSt.complete, hI.chg_len]; ring
      lot := fun hh => ?_
      tl_mem := hI.tl_mem
      ne0 := fun hb => hI.ne0 (complete_bad hb).1
      inj := fun hb => hI.inj (complete_bad hb).1
      chgd := fun hb z hz y t' h hcz => ?_
      jc_nd := ?_
      jc_len := by simp [MSt.complete, jclaims, hlen, hI.jc_len]; ring
      jc_lab := fun p hp => ?_
      jc_good := fun p hp => ?_
      fresh := fun H' hH' => ?_ }
  · simp only [MSt.complete, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hh
    exact hh.2
  · obtain ⟨hb0, hfu⟩ := complete_bad hb
    simp only [MSt.complete, List.mem_append, List.mem_reverse] at hz ⊢
    rcases hz with hz | hz
    · left
      simp only [cands, List.mem_map, List.mem_finRange, true_and] at hz
      obtain ⟨k, rfl⟩ := hz
      have hu : useful cls s.1.tl (H.getD k.val 0 + δs.getD k.val 0 (a k)) = true := by
        simp only [useful, List.any_eq_true, decide_eq_true_eq]
        exact ⟨t', hI.tl_mem y t' h, hcz⟩
      simp only [counted, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
        decide_eq_true_eq]
      exact ⟨k, hfu k hu, rfl⟩
    · exact Or.inr (hI.chgd hb0 z hz y t' h hcz)
  · simp only [MSt.complete, List.map_append]
    refine List.Nodup.append ?_ hI.jc_nd fun x hx₁ hx₂ => ?_
    · have : (jclaims (X := X) H ans).map Prod.fst =
          (ans.zipIdx.map Prod.snd).map fun j => Sum.inr (H, j) := by
        simp only [jclaims, List.map_map, Function.comp_def]
      rw [this]
      exact (List.nodup_zipIdx_map_snd ans).map fun j j' hj => by simpa using hj
    · simp only [jclaims, List.map_map, List.mem_map, Function.comp_apply] at hx₁
      obtain ⟨p, -, rfl⟩ := hx₁
      obtain ⟨p', hp', hpe⟩ := List.mem_map.1 hx₂
      obtain ⟨H', j', hl, hs⟩ := hI.jc_lab p' hp'
      rw [hl] at hpe
      simp only [Sum.inr.injEq, Prod.mk.injEq] at hpe
      rw [hpe.1, ho] at hs
      simp at hs
  · simp only [MSt.complete, List.mem_append] at hp
    rcases hp with hp | hp
    · simp only [jclaims, List.mem_map] at hp
      obtain ⟨p', -, rfl⟩ := hp
      exact ⟨H, p'.2, rfl, by simp [MSt.complete]⟩
    · obtain ⟨H', j', hl, hs⟩ := hI.jc_lab p hp
      refine ⟨H', j', hl, ?_⟩
      by_cases hH : H' = H
      · subst hH; simp [MSt.complete]
      · simpa [MSt.complete, Function.update_of_ne hH] using hs
  · simp only [MSt.complete, List.mem_append] at hp
    rcases hp with hp | hp
    · simp only [jclaims, List.mem_map] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      exact hans p' hp'
    · exact hI.jc_good p hp
  · have hne : H' ≠ H := by
      rintro rfl
      simp [MSt.complete] at hH'
    simp only [MSt.complete, Function.update_of_ne hne] at hH'
    show c (.inr (.inr H')) = none
    rw [hc H' hne]
    exact hI.fresh H' hH'

/-- A random-oracle step changes the cache at most at its own point. -/
lemma ro_other {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ t : spec.Domain, SampleableType (spec.Range t)] (t : ι) (c : spec.QueryCache)
    (r : spec.Range t × spec.QueryCache) (hr : r ∈ support ((spec.randomOracle t).run c))
    (t' : ι) (h : t' ≠ t) : r.2 t' = c t' := by
  rw [randomOracle.run_eq] at hr
  cases hc : c t with
  | some u =>
    simp only [hc, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
  | none =>
    simp only [hc, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hr
    obtain ⟨u, -, rfl⟩ := hr
    exact QueryCache.cacheQuery_of_ne c u h

variable (cls rel n) in
/-- **The invariant is preserved** by every atomic operation of the joint experiment. -/
theorem jImpl_inv (hsym : ∀ a b, cls a b → cls b a) :
    QueryImpl.PreservesInv (jImpl (AR := AR) (τ := τ) (q := q) (X := X) cls rel pk pre)
      (Inv cls rel pk n) := by
  intro o s hI z hz
  cases o with
  | w d =>
    rw [j_w] at hz
    erw [support_map] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    exact hI.ro _ fun H hH => by
      rw [ro_other _ _ r hr _ (by simp)]; exact hI.fresh H hH
  | lst hs =>
    rw [j_lst] at hz
    erw [support_map] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    exact hI.ro _ fun H hH => by
      rw [ro_other _ _ r hr _ (by simp)]; exact hI.fresh H hH
  | tgt x =>
    by_cases h : s.1.rem = 0
    · rw [j_tgt_zero _ _ _ _ _ _ h] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hI
    · rw [j_tgt _ _ _ _ _ _ h] at hz
      erw [support_map] at hz
      obtain ⟨t, -, rfl⟩ := hz
      exact hI.addT hsym (.inl x) t (s.1.rem - 1) s.1.nj
        (fun p hp => by obtain ⟨H, j, hl, -⟩ := hI.jc_lab p hp; rw [hl]; simp)
        (by have := hI.nt_eq; omega)
  | inv t =>
    rw [j_inv] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hI.inv t
  | junk H j =>
    cases h : s.1.tg (.inr (H, j)) with
    | some t =>
      rw [j_junk_some _ _ _ _ _ _ _ t h] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hI
    | none =>
      rw [j_junk _ _ _ _ _ _ _ h] at hz
      erw [support_map] at hz
      obtain ⟨t, -, rfl⟩ := hz
      exact hI.addT hsym (.inr (H, j)) t s.1.rem (s.1.nj + 1)
        (fun p hp heq => by
          obtain ⟨t', ht', -⟩ := hI.jc_good p hp
          rw [heq, h] at ht'; cases ht')
        (by have := hI.nt_eq; omega)
  | fin H δs ans =>
    cases h : valid (q := q) rel pk (fun k => s.1.tg (.inr k)) H ans with
    | false =>
      rw [j_fin_invalid _ _ _ _ _ _ _ _ h] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hI
    | true =>
      cases ho : s.1.out H with
      | some o =>
        rw [j_fin_some _ _ _ _ _ _ _ _ h o ho] at hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hI
      | none =>
        rw [j_fin _ _ _ _ _ _ _ _ h ho] at hz
        erw [support_map] at hz
        obtain ⟨r, hr, rfl⟩ := hz
        exact hI.complete H δs ans h ho r.1 _ r.2 fun H' hne =>
          ro_other _ _ r hr _ (by simp [hne])

end Joint

/-! ## The lottery -/

section Lottery

/-- `θ^{#filter}` as a product. -/
lemma pow_filter_length {α : Type} (θ : ℝ) (p : α → Bool) (l : List α) :
    θ ^ (l.filter p).length = (l.map fun k => if p k then θ else 1).prod := by
  induction l with
  | nil => simp
  | cons k l ih =>
    by_cases h : p k
    · simp [h, pow_succ, ih, mul_comm]
    · simp [h, ih]

/-- **The lottery of one run.** Each request `k` has at most one winning shift `b k`; the choices
are uniform. The sum over all choices of `θ^{number of wins}` is at most `(τ − 1 + θ)^m`, i.e.
`E[θ^X] ≤ ((τ − 1 + θ)/τ)^m`. -/
theorem lottery_sum {τ m : ℕ} (θ : ℝ) (hθ : 1 ≤ θ) (b : Fin m → Option (Fin τ)) :
    ∑ a : Fin m → Fin τ,
        θ ^ ((List.finRange m).filter fun k => decide (b k = some (a k))).length ≤
      ((τ : ℝ) - 1 + θ) ^ m := by
  have h1 : ∀ a : Fin m → Fin τ,
      θ ^ ((List.finRange m).filter fun k => decide (b k = some (a k))).length =
        ∏ k, (if b k = some (a k) then θ else 1) := by
    intro a
    rw [pow_filter_length, Fin.prod_univ_def]
    simp
  simp only [h1]
  rw [← Fintype.prod_sum (fun k j => if b k = some j then θ else (1 : ℝ))]
  calc ∏ k, ∑ j, (if b k = some j then θ else (1 : ℝ))
      ≤ ∏ _k : Fin m, ((τ : ℝ) - 1 + θ) := by
        refine Finset.prod_le_prod₀ (fun k _ => Finset.sum_nonneg fun j _ => by
          split_ifs <;> linarith) fun k _ => ?_
        cases hb : b k with
        | none => simp; linarith
        | some j₀ =>
          have : ∀ j : Fin τ, (if some j₀ = some j then θ else (1 : ℝ)) =
              1 + if j = j₀ then θ - 1 else 0 := by
            intro j
            by_cases h : j = j₀
            · subst h; simp
            · have : j₀ ≠ j := fun e => h e.symm
              simp [h, this]
          simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          simp
          linarith
    _ = ((τ : ℝ) - 1 + θ) ^ m := by simp

/-- `θ = τ^{q+1}/2`. -/
noncomputable def θR (τ q : ℕ) : ℝ := (τ : ℝ) ^ (q + 1) / 2

lemma one_le_θR {τ : ℕ} (hτ : 7 ≤ τ) (q : ℕ) : 1 ≤ θR τ q := by
  have h7 : (7 : ℝ) ≤ τ := by exact_mod_cast hτ
  have h1 : (τ : ℝ) ≤ (τ : ℝ) ^ (q + 1) := le_self_pow₀ (by linarith) (Nat.succ_ne_zero q)
  unfold θR
  linarith

variable {τ q : ℕ} {X T S : Type} [DecidableEq X] [AddCommGroup T] [DecidableEq T]
  (cls : T → T → Prop) [DecidableRel cls]

/-- **The potential**: `θ^{Z − 1}` with `Z = W − q·K`, and `1` once the lottery is won. -/
noncomputable def pot (m : MSt τ q X T S) : ℝ :=
  if m.hit then 1 else θR τ q ^ m.W / θR τ q ^ (q * m.K + 1)

omit [DecidableEq X] [AddCommGroup T] [DecidableEq T] in
lemma pot_nonneg (hτ : 7 ≤ τ) (m : MSt τ q X T S) : 0 ≤ pot m := by
  have := one_le_θR hτ q
  unfold pot
  split_ifs
  · norm_num
  · positivity

omit [DecidableEq X] [AddCommGroup T] [DecidableEq T] in
lemma le_pot_of_hit (m : MSt τ q X T S) (h : m.hit = true) : pot m = 1 := by
  simp [pot, h]

omit [DecidableEq X] in
/-- **The supermartingale step** (`uov-open-reductions.md` §4.4, steps 3–4): summed over the
`τ^{q+1}` choices of a completed run, the potential is at most `τ^{q+1}` times the potential
before. -/
theorem pot_complete (hτ : 7 ≤ τ) (hq : 1 ≤ q) (m : MSt τ q X T S) (H : List T)
    (δs : List (Fin τ → T)) (ans : List S) (ss : (Fin (q + 1) → Fin τ) → List S) :
    ∑ a : Fin (q + 1) → Fin τ, pot (m.complete cls H δs ans a (ss a)) ≤
      (τ : ℝ) ^ (q + 1) * pot m := by
  have hθ := one_le_θR hτ q
  have hθ0 : 0 < θR τ q := by linarith
  by_cases hh : m.hit = true
  · have : ∀ a : Fin (q + 1) → Fin τ, pot (m.complete cls H δs ans a (ss a)) = 1 := fun a => by
      simp [pot, MSt.complete, hh]
    simp [this, le_pot_of_hit m hh]
  · simp only [Bool.not_eq_true] at hh
    have key : ∀ a : Fin (q + 1) → Fin τ, pot (m.complete cls H δs ans a (ss a)) ≤
        θR τ q ^ m.W / θR τ q ^ (q * (m.K + 1) + 1) *
          θR τ q ^ ((List.finRange (q + 1)).filter fun k =>
            decide (firstU cls m.tl H δs k = some (a k))).length := by
      intro a
      rw [div_mul_eq_mul_div, ← pow_add]
      by_cases hd : q * (m.K + 1) < m.W + (counted cls m.tl H δs a).length
      · have : pot (m.complete cls H δs ans a (ss a)) = 1 := by
          simp [pot, MSt.complete, hd]
        rw [this, one_le_div (pow_pos hθ0 _)]
        exact pow_le_pow_right₀ hθ (by unfold counted at hd; omega)
      · have : pot (m.complete cls H δs ans a (ss a)) =
            θR τ q ^ (m.W + (counted cls m.tl H δs a).length) /
              θR τ q ^ (q * (m.K + 1) + 1) := by
          simp [pot, MSt.complete, hd, hh]
        rw [this]
        rfl
    have hsm := VoleMole.UOVAssumptions.rewind_supermartingale (τ : ℝ)
      (by exact_mod_cast hτ) q hq
    have hτ0 : (0 : ℝ) < (τ : ℝ) ^ (q + 1) := by
      have : (0 : ℝ) < τ := by exact_mod_cast (by omega : 0 < τ)
      positivity
    rw [div_pow, div_le_iff₀ hτ0] at hsm
    calc ∑ a : Fin (q + 1) → Fin τ, pot (m.complete cls H δs ans a (ss a))
        ≤ ∑ a : Fin (q + 1) → Fin τ, θR τ q ^ m.W / θR τ q ^ (q * (m.K + 1) + 1) *
            θR τ q ^ ((List.finRange (q + 1)).filter fun k =>
              decide (firstU cls m.tl H δs k = some (a k))).length :=
          Finset.sum_le_sum fun a _ => key a
      _ = θR τ q ^ m.W / θR τ q ^ (q * (m.K + 1) + 1) *
            ∑ a : Fin (q + 1) → Fin τ, θR τ q ^ ((List.finRange (q + 1)).filter fun k =>
              decide (firstU cls m.tl H δs k = some (a k))).length := by
          rw [Finset.mul_sum]
      _ ≤ θR τ q ^ m.W / θR τ q ^ (q * (m.K + 1) + 1) * (((τ : ℝ) - 1 + θR τ q) ^ (q + 1)) :=
          mul_le_mul_of_nonneg_left (lottery_sum _ hθ _) (by positivity)
      _ ≤ θR τ q ^ m.W / θR τ q ^ (q * (m.K + 1) + 1) * (θR τ q ^ q * (τ : ℝ) ^ (q + 1)) :=
          mul_le_mul_of_nonneg_left hsm (by positivity)
      _ = (τ : ℝ) ^ (q + 1) * pot m := by
          simp only [pot, hh, Bool.false_eq_true, ite_false]
          have : q * (m.K + 1) + 1 = (q * m.K + 1) + q := by ring
          rw [this, pow_add]
          field_simp

omit [DecidableEq X] [AddCommGroup T] [DecidableEq T] in
lemma pot_eq {m m' : MSt τ q X T S} (h₁ : m'.hit = m.hit) (h₂ : m'.W = m.W) (h₃ : m'.K = m.K) :
    pot m' = pot m := by
  unfold pot
  rw [h₁, h₂, h₃]

end Lottery

/-! ## A potential argument for stateful handlers -/

section Potential

/-- **Ville's inequality for a handler.** If every step of `impl` contracts the potential `Φ`
(`hstep`: any event of a continuation that is bounded by `Φ` of the state after the step is
bounded by `Φ` of the state before it), and the event `E` of a state forces `Φ ≥ 1`, then for
every computation the probability of `E` at the final state is at most `Φ` of the initial state. -/
theorem potential_le {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (Inv : σ → Prop)
    (hinv : QueryImpl.PreservesInv impl Inv) (Φ : σ → ℝ≥0∞) (E : σ → Prop)
    (hE : ∀ s, E s → 1 ≤ Φ s)
    (hstep : ∀ o s, Inv s → ∀ (β : Type) (f : spec.Range o × σ → ProbComp β) (p : β → Prop),
      (∀ z ∈ support ((impl o).run s), Pr{let y ← f z}[p y] ≤ Φ z.2) →
        Pr{let y ← (impl o).run s >>= f}[p y] ≤ Φ s)
    {α : Type} (oa : OracleComp spec α) :
    ∀ s, Inv s → Pr{let z ← (simulateQ impl oa).run s}[E z.2] ≤ Φ s := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro s _
    simp only [simulateQ_pure, StateT.run_pure]
    by_cases h : E s
    · exact (prEvent_le_one _).trans (hE s h)
    · classical
      rw [prEvent_pure]
      simp [h]
  | query_bind o k ih =>
    intro s hs
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact hstep o s hs _ _ _ fun z hz => ih z.1 z.2 (hinv o s hs z hz)

end Potential

section LotteryJoint

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {τ q : ℕ} [NeZero τ] {X : Type} [DecidableEq X] {T S : Type} [AddCommGroup T]
  [SampleableType T] [DecidableEq T]
  (cls : T → T → Prop) [DecidableRel cls]
  {PK : Type} (rel : PK → S → T → Prop) [∀ pk s t, Decidable (rel pk s t)]
  (pk : PK) (pre : T → S) (n : ℕ)

/-- **Every atomic operation contracts the potential.** Only the completion of a run changes it;
there the choices `a(H)` are fresh and uniform (`Inv.fresh`), and `pot_complete` applies. -/
theorem lot_step (hτ : 7 ≤ τ) (hq : 1 ≤ q) (o : Op DR X T S τ) (s : JSt AR τ q X T S)
    (hI : Inv cls rel pk n s) (β : Type)
    (f : AnsOp AR τ q X T S o × JSt AR τ q X T S → ProbComp β) (p : β → Prop)
    (h : ∀ z ∈ support ((jImpl cls rel pk pre o).run s),
      Pr{let y ← f z}[p y] ≤ ENNReal.ofReal (pot z.2.1)) :
    Pr{let y ← (jImpl cls rel pk pre o).run s >>= f}[p y] ≤ ENNReal.ofReal (pot s.1) := by
  have hconst : (∀ z ∈ support ((jImpl cls rel pk pre o).run s), pot z.2.1 = pot s.1) →
      Pr{let y ← (jImpl cls rel pk pre o).run s >>= f}[p y] ≤ ENNReal.ofReal (pot s.1) :=
    fun hc => prEvent_bind_le_of_forall_le_of_support _ _ p fun z hz =>
      (h z hz).trans (le_of_eq (congrArg ENNReal.ofReal (hc z hz)))
  cases o with
  | w d =>
    refine hconst fun z hz => ?_
    rw [j_w] at hz
    erw [support_map] at hz
    obtain ⟨r, -, rfl⟩ := hz
    rfl
  | lst hs =>
    refine hconst fun z hz => ?_
    rw [j_lst] at hz
    erw [support_map] at hz
    obtain ⟨r, -, rfl⟩ := hz
    rfl
  | tgt x =>
    refine hconst fun z hz => ?_
    by_cases h0 : s.1.rem = 0
    · rw [j_tgt_zero _ _ _ _ _ _ h0] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    · rw [j_tgt _ _ _ _ _ _ h0] at hz
      erw [support_map] at hz
      obtain ⟨t, -, rfl⟩ := hz
      exact pot_eq rfl rfl rfl
  | inv t =>
    refine hconst fun z hz => ?_
    rw [j_inv] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact pot_eq rfl rfl rfl
  | junk H j =>
    refine hconst fun z hz => ?_
    cases hj : s.1.tg (.inr (H, j)) with
    | some t =>
      rw [j_junk_some _ _ _ _ _ _ _ t hj] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    | none =>
      rw [j_junk _ _ _ _ _ _ _ hj] at hz
      erw [support_map] at hz
      obtain ⟨t, -, rfl⟩ := hz
      exact pot_eq rfl rfl rfl
  | fin H δs ans =>
    cases hv : valid (q := q) rel pk (fun k => s.1.tg (.inr k)) H ans with
    | false =>
      refine hconst fun z hz => ?_
      rw [j_fin_invalid _ _ _ _ _ _ _ _ hv] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    | true =>
      cases ho : s.1.out H with
      | some o =>
        refine hconst fun z hz => ?_
        rw [j_fin_some _ _ _ _ _ _ _ _ hv o ho] at hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
      | none =>
        have hfr := hI.fresh H ho
        have hrun : (jImpl cls rel pk pre (.fin H δs ans)).run s =
            (fun a : Fin (q + 1) → Fin τ => (some (a, (cands H δs a).map pre),
              (s.1.complete cls H δs ans a ((cands H δs a).map pre),
                { s.2 with ro := s.2.ro.cacheQuery (.inr (.inr H)) a,
                           calls := (cands H δs a).reverse ++ s.2.calls }))) <$>
              ($ᵗ (Fin (q + 1) → Fin τ)) := by
          rw [j_fin _ _ _ _ _ _ _ _ hv ho, randomOracle.run_eq]
          simp only [hfr, map_bind, map_pure]
          exact (map_eq_bind_pure_comp _ _ _).symm
        rw [hrun] at h ⊢
        rw [bind_map_left, prEvent_bind_eq_sum_fintype]
        have hc : (Fintype.card (Fin (q + 1) → Fin τ) : ℝ≥0∞) = (τ : ℝ≥0∞) ^ (q + 1) := by
          simp
        have hτ0 : (τ : ℝ≥0∞) ^ (q + 1) ≠ 0 := by
          have : τ ≠ 0 := by omega
          simp [this]
        have hτt : (τ : ℝ≥0∞) ^ (q + 1) ≠ ⊤ := by simp
        calc ∑ a : Fin (q + 1) → Fin τ, Pr{let x ← $ᵗ (Fin (q + 1) → Fin τ)}[x = a] *
              Pr{let y ← f (some (a, (cands H δs a).map pre),
                (s.1.complete cls H δs ans a ((cands H δs a).map pre),
                  { s.2 with ro := s.2.ro.cacheQuery (.inr (.inr H)) a,
                             calls := (cands H δs a).reverse ++ s.2.calls }))}[p y]
            ≤ ∑ a : Fin (q + 1) → Fin τ, ((τ : ℝ≥0∞) ^ (q + 1))⁻¹ *
                ENNReal.ofReal (pot (s.1.complete cls H δs ans a ((cands H δs a).map pre))) := by
              refine Finset.sum_le_sum fun a _ => ?_
              rw [SampleableType.prEvent_uniformSample_eq_singleton, hc]
              refine mul_le_mul_right (h _ ?_) _
              erw [support_map]
              exact ⟨a, mem_support_uniformSample _, rfl⟩
          _ = ((τ : ℝ≥0∞) ^ (q + 1))⁻¹ * ENNReal.ofReal (∑ a : Fin (q + 1) → Fin τ,
                pot (s.1.complete cls H δs ans a ((cands H δs a).map pre))) := by
              rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun a _ => pot_nonneg hτ _]
          _ ≤ ((τ : ℝ≥0∞) ^ (q + 1))⁻¹ * ENNReal.ofReal ((τ : ℝ) ^ (q + 1) * pot s.1) :=
              mul_le_mul_right (ENNReal.ofReal_le_ofReal (pot_complete cls hτ hq s.1 H δs ans
                fun a => (cands H δs a).map pre)) _
          _ = ENNReal.ofReal (pot s.1) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
                ENNReal.ofReal_natCast, ENNReal.inv_mul_cancel_left hτ0 hτt]

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [NeZero τ] [SampleableType T]
  [∀ pk s t, Decidable (rel pk s t)] in
/-- **Accounting** (`ompr-shift-algebra.md` §2.2, step 3). At a state of the invariant without a
bad event and without a win of the lottery, if the reduction's claims win OMPR with `c` calls,
`M`'s pick wins OMPR^free. -/
theorem free_of_win (hcls : Equivalence cls) {s : JSt AR τ q X T S} (hI : Inv cls rel pk n s)
    (cl : List (X × S)) (c J K₀ : ℕ)
    (hw : Wins c (goodPre rel) pk cl (π s).toCh) (hb : s.1.bad = false) (hh : s.1.hit = false)
    (hj : s.1.nj ≤ J) (hk : s.1.K ≤ K₀) :
    ∃ x sg t, pick cls cl s.1 = some (x, sg) ∧ s.2.tg x = some (t, ()) ∧ rel pk sg t ∧ t ≠ 0 ∧
      (∀ z ∈ s.2.calls, ¬ cls z t) ∧ s.2.nt ≤ n + J ∧ s.2.calls.length ≤ c + (q + 1) * K₀ := by
  obtain ⟨hlen, hnd, hiq, hgood⟩ := hw
  set all : List (XM X T × S) := (cl.map fun p => ((Sum.inl p.1 : XM X T), p.2)) ++ s.1.jc
    with hall
  have hA : (all.map Prod.fst).Nodup := by
    rw [hall, List.map_append, List.map_map]
    refine List.Nodup.append ?_ hI.jc_nd fun x hx₁ hx₂ => ?_
    · have : (Prod.fst ∘ fun p : X × S => ((Sum.inl p.1 : XM X T), p.2)) =
          (Sum.inl : X → XM X T) ∘ Prod.fst := rfl
      rw [this, ← List.map_map]
      exact hnd.map Sum.inl_injective
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx₁
      obtain ⟨p', hp', hpe⟩ := List.mem_map.1 hx₂
      obtain ⟨H, j, hl, -⟩ := hI.jc_lab p' hp'
      rw [hl] at hpe
      simp at hpe
  have hB : ∀ p ∈ all, ∃ t, s.1.tg p.1 = some t ∧ rel pk p.2 t := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
      obtain ⟨t, u, ht, hr⟩ := hgood p' hp'
      have ht' : (s.1.tg (Sum.inl p'.1)).map (fun t => (t, ())) = some (t, u) := ht
      cases htg : s.1.tg (Sum.inl p'.1) with
      | none => simp [htg] at ht'
      | some t₀ =>
        simp only [htg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at ht'
        exact ⟨t₀, rfl, ht'.1 ▸ hr⟩
    · exact hI.jc_good p hp
  have hC : all.length = c + 1 + q * s.1.K := by
    simp [hall, hlen, hI.jc_len]
  have hD : ∃ p ∈ all, ∀ t, s.1.tg p.1 = some t → ∀ z ∈ s.1.calls, ¬ cls z t := by
    by_contra hcon
    push Not at hcon
    have hch : ∀ x ∈ (all.map Prod.fst).toFinset, ∃ z, z ∈ s.1.chg.toFinset ∧
        ∃ t, s.1.tg x = some t ∧ cls z t := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
      obtain ⟨t, ht, z, hz, hc⟩ := hcon p hp
      exact ⟨z, List.mem_toFinset.2 (hI.chgd hb z hz p.1 t ht hc), t, ht, hc⟩
    choose! f hf using hch
    have hcard : (all.map Prod.fst).toFinset.card ≤ s.1.chg.toFinset.card := by
      refine Finset.card_le_card_of_injOn f (fun x hx => (hf x hx).1) fun x₁ hx₁ x₂ hx₂ he => ?_
      obtain ⟨-, t₁, ht₁, hc₁⟩ := hf x₁ hx₁
      obtain ⟨-, t₂, ht₂, hc₂⟩ := hf x₂ hx₂
      rw [he] at hc₁
      exact hI.inj hb x₁ x₂ t₁ t₂ ht₁ ht₂ (hcls.trans (hcls.symm hc₁) hc₂)
    rw [List.toFinset_card_of_nodup hA, List.length_map, hC] at hcard
    have h1 := List.toFinset_card_le s.1.chg
    have h2 := hI.chg_len
    have h3 := hI.lot hh
    have h4 : s.1.iq ≤ c := hiq
    omega
  obtain ⟨p₀, hp₀, hfree⟩ := hD
  obtain ⟨t₀, ht₀, -⟩ := hB p₀ hp₀
  cases hf : pick cls cl s.1 with
  | none =>
    have := List.find?_eq_none.1 hf p₀ hp₀
    simp only [ht₀, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, not_and, not_forall] at this
    obtain ⟨z, hz, hc⟩ := this (hI.ne0 hb p₀.1 t₀ ht₀)
    exact absurd (not_not.1 hc) (hfree t₀ ht₀ z hz)
  | some p₁ =>
    have hmem : p₁ ∈ all := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    obtain ⟨t₁, ht₁, hr₁⟩ := hB p₁ hmem
    simp only [ht₁, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at hpred
    refine ⟨p₁.1, p₁.2, t₁, rfl, ?_, hr₁, hpred.1, ?_, ?_, ?_⟩
    · rw [hI.tg_eq, ht₁]; rfl
    · rw [hI.calls_eq]; exact hpred.2
    · have := hI.nt_eq; omega
    · rw [hI.calls_eq, hI.calls_len]
      have h4 : s.1.iq ≤ c := hiq
      have := Nat.mul_le_mul_left (q + 1) hk
      omega

end LotteryJoint

/-! ## Theorem R -/

section Main

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {τ q : ℕ} [NeZero τ] {X : Type} [DecidableEq X] {T S : Type} [AddCommGroup T]
  [SampleableType T] [DecidableEq T]
  (cls : T → T → Prop) [DecidableRel cls]
  {PK SK : Type} (tr : Trapdoor PK SK T S) [∀ pk s t, Decidable (tr.IsPre pk s t)] (n : ℕ)

/-- **The joint experiment**: `M` in the OMPR^free game, with `M`'s state. -/
def jointExp (R : PK → ProbComp (OracleComp (specRed AR τ q X T S) (List (X × S)))) :
    ProbComp (PK × List (X × S) × JSt AR τ q X T S) := do
  let kp ← tr.keyGen
  let r ← R kp.1
  let z ← (simulateQ (jImpl cls tr.IsPre kp.1 (tr.D kp.2)) (simulateQ prog r)).run (m0 n, f0)
  pure (kp.1, z.1, z.2)

/-- **The probability of a bad event on values** (E1–E3 of `ompr-shift-algebra.md` §2.2, as
flagged by `MSt.addT` and `MSt.complete`) in the joint experiment. -/
noncomputable def badPr (R : PK → ProbComp (OracleComp (specRed AR τ q X T S) (List (X × S)))) :
    ℝ≥0∞ :=
  Pr{let r ← jointExp cls tr n R}[r.2.2.1.bad = true]

/-- **The simulation is exact**: the experiment is the joint experiment, projected. -/
theorem redExp_eqd (R : PK → ProbComp (OracleComp (specRed AR τ q X T S) (List (X × S)))) :
    redExp tr n R =ᵈ (fun r => (r.1, r.2.1, π r.2.2)) <$> jointExp cls tr n R := by
  simp only [redExp, jointExp, map_bind, map_pure]
  refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun r => ?_
  have h := LazyIdeal.simulateQ_proj_eqd_inv (jImpl cls tr.IsPre kp.1 (tr.D kp.2))
    (μR tr.IsPre kp.1 (tr.D kp.2)) π (fun _ => True) (fun _ _ _ _ _ => trivial)
    (fun o s _ => by rw [proj_step]) (simulateQ prog r) (m0 n, f0) trivial
  have h0 : π (m0 n, f0) = (r0 n : RSt AR τ q X T S) := rfl
  rw [h0] at h
  have := h.symm.bind_left (fun z => pure (kp.1, z.1, z.2))
  simpa only [bind_map_left] using this

/-- `M`'s OMPR^free experiment is the joint experiment with `M`'s pick. -/
theorem freeExp_redM (R : PK → ProbComp (OracleComp (specRed AR τ q X T S) (List (X × S)))) :
    freeExp tr (redM cls tr.IsPre n R) =
      (fun r => (r.1, pick cls r.2.1 r.2.2.1, r.2.2.2)) <$> jointExp cls tr n R := by
  simp only [freeExp, redM, jointExp, map_bind, map_pure, bind_map_left, simulateQ_map,
    StateT.run_map, collapseJ, Functor.map_map]

/-- The invariant holds at the end of the joint experiment. -/
theorem jointExp_inv (hsym : ∀ a b, cls a b → cls b a)
    (R : PK → ProbComp (OracleComp (specRed AR τ q X T S) (List (X × S))))
    (r : PK × List (X × S) × JSt AR τ q X T S) (hr : r ∈ support (jointExp cls tr n R)) :
    Inv cls tr.IsPre r.1 n r.2.2 := by
  simp only [jointExp, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨kp, -, b, -, z, hz, rfl⟩ := hr
  exact simulateQ_run_preservesInv _ _ (jImpl_inv cls tr.IsPre (tr.D kp.2) n hsym) _ _
    (inv_init cls tr.IsPre kp.1 n) z hz

/-- **The lottery bound** (`ompr-shift-algebra.md` §2.2, step 2; [OR] A4, steps 3–4): in the
joint experiment the lottery is won, `W > q·K` after some completed run, with probability at
most `2·τ^{−(q+1)}`. -/
theorem lottery_le (hsym : ∀ a b, cls a b → cls b a) (hτ : 7 ≤ τ) (hq : 1 ≤ q)
    (R : PK → ProbComp (OracleComp (specRed AR τ q X T S) (List (X × S)))) :
    Pr{let r ← jointExp cls tr n R}[r.2.2.1.hit = true] ≤ 2 / (τ : ℝ≥0∞) ^ (q + 1) := by
  have h0 : ENNReal.ofReal (pot (m0 n : MSt τ q X T S)) = 2 / (τ : ℝ≥0∞) ^ (q + 1) := by
    have hτ0 : (0 : ℝ) < (τ : ℝ) ^ (q + 1) := by
      have : (0 : ℝ) < τ := by exact_mod_cast (by omega : 0 < τ)
      positivity
    have : pot (m0 n : MSt τ q X T S) = 2 / (τ : ℝ) ^ (q + 1) := by
      simp [pot, m0, θR]
    rw [this, ENNReal.ofReal_div_of_pos hτ0, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  unfold jointExp
  refine prEvent_bind_le_of_forall_le _ _ _ fun kp => prEvent_bind_le_of_forall_le _ _ _ fun r => ?_
  have h := potential_le (jImpl cls tr.IsPre kp.1 (tr.D kp.2)) (Inv cls tr.IsPre kp.1 n)
    (jImpl_inv cls tr.IsPre (tr.D kp.2) n hsym) (fun s => ENNReal.ofReal (pot s.1))
    (fun s => s.1.hit = true) (fun s hs => by simp [le_pot_of_hit s.1 hs])
    (fun o s hI β f p hf => lot_step cls tr.IsPre kp.1 (tr.D kp.2) n hτ hq o s hI β f p hf)
    (simulateQ prog r) (m0 n, f0) (inv_init cls tr.IsPre kp.1 n)
  rw [h0] at h
  have e : (do
      let z ← (simulateQ (jImpl cls tr.IsPre kp.1 (tr.D kp.2)) (simulateQ prog r)).run (m0 n, f0)
      pure (kp.1, z.1, z.2)) = (fun z => (kp.1, z.1, z.2)) <$>
        (simulateQ (jImpl cls tr.IsPre kp.1 (tr.D kp.2)) (simulateQ prog r)).run (m0 n, f0) :=
    (map_eq_bind_pure_comp _ _ _).symm
  rw [e, prEvent_map]
  exact h

/-- **Theorem R** (`ompr-shift-algebra.md` §2). Let `τ ≥ 7`, `q ≥ 1`, and let `cls` be an
equivalence relation on targets (for UOV: equality up to a nonzero scalar). For every reduction
`R` that is black-box in the adversary only, the probability that `R` wins OMPR with `n` targets
and `c` calls when run with `A**_D`, having drawn at most `J` junk targets and completed at most
`K₀` runs, is at most

    2·τ^{−(q+1)} + Adv^{free}(M; n + J, c + (q + 1)·K₀) + Pr[bad event on values],

with `M = redM cls tr.IsPre n R` an explicit OMPR^free adversary. -/
theorem thmR (hcls : Equivalence cls) (hτ : 7 ≤ τ) (hq : 1 ≤ q) (c J K₀ : ℕ)
    (R : PK → ProbComp (OracleComp (specRed AR τ q X T S) (List (X × S)))) :
    Pr{let r ← redExp tr n R}[Wins c (goodPre tr.IsPre) r.1 r.2.1 r.2.2.toCh ∧
        r.2.2.nj ≤ J ∧ r.2.2.nc ≤ K₀] ≤
      2 / (τ : ℝ≥0∞) ^ (q + 1) +
        advOMPRFree tr cls (n + J) (c + (q + 1) * K₀) (redM cls tr.IsPre n R) +
        badPr cls tr n R := by
  have hsym : ∀ a b, cls a b → cls b a := fun _ _ => hcls.symm
  rw [(redExp_eqd cls tr n R).prEvent_eq, prEvent_map]
  unfold advOMPRFree badPr
  rw [freeExp_redM, prEvent_map]
  refine (prEvent_mono_of_support (jointExp cls tr n R) _
    (fun r => r.2.2.1.hit = true ∨
      FreeWin tr cls (n + J) (c + (q + 1) * K₀) (r.1, pick cls r.2.1 r.2.2.1, r.2.2.2) ∨
      r.2.2.1.bad = true) fun r hr hw => ?_).trans ?_
  · by_cases hh : r.2.2.1.hit = true
    · exact Or.inl hh
    by_cases hb : r.2.2.1.bad = true
    · exact Or.inr (Or.inr hb)
    simp only [Bool.not_eq_true] at hh hb
    obtain ⟨x, sg, t, hp, htg, hrel, ht0, hfree, hnt, hcl⟩ :=
      free_of_win cls tr.IsPre r.1 n hcls (jointExp_inv cls tr n hsym R r hr) r.2.1 c J K₀
        hw.1 hb hh hw.2.1 hw.2.2
    exact Or.inr (Or.inl ⟨x, sg, t, (), hp, htg, hrel, ht0, hfree, hnt, hcl⟩)
  · refine (prEvent_or_le _ _ _).trans ?_
    rw [add_assoc]
    exact add_le_add (lottery_le cls tr n hsym hτ hq R) (prEvent_or_le _ _ _)

end Main

/-! ## An OMPR adversary is a reduction, with the same advantage -/

section LiftB

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {τ q : ℕ} [NeZero τ] {X : Type} [DecidableEq X] {T S : Type} [AddCommGroup T]
  [SampleableType T] [DecidableEq T]
  {PK SK : Type} (rel : PK → S → T → Prop) [∀ pk s t, Decidable (rel pk s t)]
  (pk : PK) (pre : T → S)

/-- **An OMPR adversary as a reduction** that never talks to `A**_D`. -/
def liftRed (B : PK → ProbComp (OracleComp (specB AR X Unit T S) (List (X × S)))) (pk : PK) :
    ProbComp (OracleComp (specRed AR τ q X T S) (List (X × S))) :=
  simulateQ liftB <$> B pk

/-- The experiment's handler on the OMPR oracles. -/
def μB (pre : T → S) : QueryImpl (specB AR X Unit T S) (StateT (RSt AR τ q X T S) ProbComp)
  | .inl d => StateT.mk fun s =>
      match s.ro (.inl d) with
      | some u => pure (u, s)
      | none => (fun u => (u, { s with ro := s.ro.cacheQuery (.inl d) u })) <$> ($ᵗ (AR d))
  | .inr (.inl (x, _)) => StateT.mk fun s =>
      if s.rem = 0 then pure (none, s) else
        (fun t => (some t,
          { s with tg := Function.update s.tg x (some (t, ())), rem := s.rem - 1 })) <$> ($ᵗ T)
  | .inr (.inr t) => StateT.mk fun s => pure (pre t, { s with iq := s.iq + 1 })

lemma μR_w_run (d : DR) (s : RSt AR τ q X T S) :
    (μR rel pk pre (.w d)).run s = (μB pre (.inl d)).run s := by
  simp only [μR, μB, StateT.run_mk, randomOracle.run_eq]
  cases h : s.ro (.inl d) with
  | some u => simp
  | none =>
    simp only [map_bind, map_pure]
    exact (map_eq_bind_pure_comp _ _ _).symm

lemma sim_liftB (o : DR ⊕ ((X × Unit) ⊕ T)) :
    simulateQ (μR rel pk pre) (simulateQ prog (liftB (AR := AR) (τ := τ) (q := q) o)) =
      μB pre o := by
  unfold liftB
  erw [simulateQ_spec_query]
  rcases o with d | ⟨x, u⟩ | t
  · show simulateQ _ (op (.w d)) = _
    unfold op
    erw [simulateQ_spec_query]
    exact StateT.ext fun s => μR_w_run rel pk pre d s
  · show simulateQ _ (op (.tgt x)) = _
    unfold op
    erw [simulateQ_spec_query]
    rfl
  · show simulateQ _ (op (.inv t)) = _
    unfold op
    erw [simulateQ_spec_query]
    rfl

/-- An OMPR adversary run as a reduction uses only the OMPR oracles. -/
theorem liftB_sim {α : Type} (b : OracleComp (specB AR X Unit T S) α) :
    simulateQ (μR rel pk pre) (simulateQ prog (simulateQ (liftB (τ := τ) (q := q)) b)) =
      simulateQ (μB pre) b := by
  induction b using OracleComp.inductionOn with
  | pure x => simp
  | query_bind o k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    rw [sim_liftB]

omit [NeZero τ] [AddCommGroup T] in
/-- **The experiment restricted to the OMPR oracles is the OMPR experiment** (`omExp`'s
challenger `chImpl` with a uniform stream of `rem` targets): same joint distribution of the
output, the labelled targets and the number of calls; no junk target is drawn and no run is
completed. -/
theorem liftB_eqd {α : Type} (b : OracleComp (specB AR X Unit T S) α) :
    ∀ (s : RSt AR τ q X T S) (cr : (specR AR).QueryCache), (∀ d, s.ro (.inl d) = cr d) →
      (fun z => (z.1, z.2.tg, z.2.iq, z.2.nj, z.2.nc)) <$> (simulateQ (μB pre) b).run s =ᵈ
        (do let L ← unifList T s.rem
            (fun z : α × Ch AR X Unit T => (z.1, z.2.tg, z.2.iq, s.nj, s.nc)) <$>
              (simulateQ (chImpl pre) b).run ⟨cr, L, s.tg, s.iq⟩) := by
  induction b using OracleComp.inductionOn with
  | pure x =>
    intro s cr _
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact (LazyIdeal.eqd_bind_unused _ _).symm
  | query_bind o k ih =>
    intro s cr hro
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases o with d | ⟨x, u⟩ | t
    · have hch : ∀ c : Ch AR X Unit T, (chImpl (S := S) pre (.inl d)).run c = roStep d c :=
        fun _ => rfl
      simp only [μB, StateT.run_mk, hch, roStep, randomOracle.run_eq]
      have hd := hro d
      cases hc : cr d with
      | some u =>
        rw [hc] at hd
        simp only [hd, pure_bind, map_pure]
        exact ih u s cr hro
      | none =>
        rw [hc] at hd
        simp only [hd]
        have hro' : ∀ (u : AR d) (d' : DR),
            (s.ro.cacheQuery (.inl d) u) (.inl d') = (cr.cacheQuery d u) d' := by
          intro u d'
          by_cases h : d' = d
          · subst h
            exact (QueryCache.cacheQuery_self s.ro (.inl d') u).trans
              (QueryCache.cacheQuery_self cr d' u).symm
          · exact (QueryCache.cacheQuery_of_ne s.ro (t := Sum.inl d) u
              (fun e => h (Sum.inl.inj e))).trans
              ((hro d').trans (QueryCache.cacheQuery_of_ne cr u h).symm)
        have h1 := EvalDistEq.bind_right ($ᵗ (AR d)) fun u =>
          ih u { s with ro := s.ro.cacheQuery (.inl d) u } (cr.cacheQuery d u) (hro' u)
        dsimp only at h1
        refine EvalDistEq.trans ?_ (h1.trans ((eqd_swap _ _ _).trans ?_))
        · erw [bind_map_left]
          exact EvalDistEq.rfl
        · refine EvalDistEq.bind_right _ fun L => ?_
          erw [bind_map_left, bind_assoc]
          simp only [pure_bind]
          exact EvalDistEq.rfl
    · cases u
      simp only [μB, chImpl, StateT.run_mk]
      cases hm : s.rem with
      | zero =>
        simp only [unifList, ite_true, pure_bind]
        have := ih none s cr hro
        rw [hm] at this
        simpa only [unifList, pure_bind] using this
      | succ m =>
        simp only [unifList, Nat.succ_ne_zero, ite_false, bind_map_left, bind_assoc, pure_bind,
          Nat.add_sub_cancel]
        refine EvalDistEq.bind_right _ fun t => ?_
        exact ih (some t) { s with tg := Function.update s.tg x (some (t, ())), rem := m } cr hro
    · simp only [μB, chImpl, StateT.run_mk, pure_bind]
      exact ih _ { s with iq := s.iq + 1 } cr hro

variable (tr : Trapdoor PK SK T S) [∀ pk s t, Decidable (tr.IsPre pk s t)]

/-- **The reduction class contains every OMPR adversary, with its OMPR advantage**: run as a
reduction (`liftRed`), an adversary `B` wins the experiment of Theorem R, with no junk target
drawn and no run completed, with probability `Adv^{ompr}(B; n, c)`. So the experiment's
challenger is the OMPR challenger of `Assumptions/UOV.lean` (`omExp`). -/
theorem redExp_liftRed (n c : ℕ)
    (B : PK → ProbComp (OracleComp (specB AR X Unit T S) (List (X × S)))) :
    Pr{let r ← redExp tr n (liftRed (τ := τ) (q := q) B)}[
        Wins c (goodPre tr.IsPre) r.1 r.2.1 r.2.2.toCh ∧ r.2.2.nj ≤ 0 ∧ r.2.2.nc ≤ 0] =
      advOMPR tr n c B := by
  let W : PK × List (X × S) × (X → Option (T × Unit)) × ℕ × ℕ × ℕ → Prop := fun r =>
    Wins c (goodPre tr.IsPre) r.1 r.2.1 (⟨∅, [], r.2.2.1, r.2.2.2.1⟩ : Ch AR X Unit T) ∧
      r.2.2.2.2.1 ≤ 0 ∧ r.2.2.2.2.2 ≤ 0
  have hE : (fun r => (r.1, r.2.1, r.2.2.tg, r.2.2.iq, r.2.2.nj, r.2.2.nc)) <$>
        redExp tr n (liftRed (τ := τ) (q := q) B) =ᵈ
      (fun r => (r.1, r.2.1, r.2.2.tg, r.2.2.iq, 0, 0)) <$> omExp tr.keyGen tr.D n B := by
    simp only [redExp, liftRed, omExp, map_bind, map_pure, bind_map_left]
    refine EvalDistEq.bind_right _ fun kp => EvalDistEq.bind_right _ fun b => ?_
    rw [liftB_sim]
    have h := liftB_eqd (τ := τ) (q := q) (tr.D kp.2) b (r0 n) ∅ fun _ => rfl
    have := h.bind_left (fun z => pure (kp.1, z.1, z.2))
    simpa only [bind_map_left, bind_assoc, r0, ch0] using this
  have h1 : Pr{let r ← redExp tr n (liftRed (τ := τ) (q := q) B)}[
        Wins c (goodPre tr.IsPre) r.1 r.2.1 r.2.2.toCh ∧ r.2.2.nj ≤ 0 ∧ r.2.2.nc ≤ 0] =
      Pr{let r ← (fun r => (r.1, r.2.1, r.2.2.tg, r.2.2.iq, r.2.2.nj, r.2.2.nc)) <$>
        redExp tr n (liftRed (τ := τ) (q := q) B)}[W r] := by
    rw [prEvent_map]
    rfl
  rw [h1, hE.prEvent_eq, prEvent_map]
  unfold advOMPR
  refine prEvent_congr _ _ _ fun r => ?_
  simp only [W, le_refl, and_true]
  rfl

end LiftB

end VoleMole.Assumptions.TheoremR
