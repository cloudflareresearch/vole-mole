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

end Joint

end VoleMole.Assumptions.TheoremR
