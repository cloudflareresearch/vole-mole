import VoleMole.Assumptions.CTUFPerm
import VoleMole.Assumptions.IdealTag

/-!
# det-FDH (UF-Tag) with `Tag` a random permutation with inverse queries

`lean/docs/security/uov-assumptions.md` §5.1, §5.8 (`ratatouille.md` Lemma 2.1). In the
standalone UF-Tag game, KP800 is a random permutation `π` of the blocks `T × Z`, lazily sampled
(`LazyPerm.rpImpl`), with forward and inverse queries; `Tag(m)` is the first component of
`π(emb m)` for an injective encoding `emb` of the messages `(c, x)`; the signer answers
`D(Tag(m))`, evaluating `π` itself.

* **The game** `advFDHPerm tr emb A` (det-FDH with `H = Tag` read off the permutation): the forger
  (`specFP`: the world, the signer on messages, `π`) returns `(m*, s*)`; the challenger evaluates
  `π(emb m*)` (`fpFinal`); the win `FPWin`: `m*` never signed and `s*` a preimage of `Tag(m*)`.
* **Two hybrids** (`advFDHPerm_le_avoid`): the permutation is replaced by the two-sided random
  function (`LazyPerm.prEvent_rp_le_rf`, `q = q_f + q_i + q_S + 1` queries read it), and fresh
  inverse answers are drawn outside the structured inputs (`LazyPerm.prEvent_rf_le_avoid`,
  `q_i·|M|/|B|`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec VoleMole.Assumptions.LazyPerm VoleMole.ROM.OneMore
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.FDHPerm

open CTUFPerm (comP)

section Game

variable {DR : Type} (AR : DR → Type) (M T Z S : Type)

/-- The other oracles' answers: the world, and the signer on messages. -/
abbrev AnsFP : DR ⊕ M → Type := Sum.elim AR fun _ => S

/-- **The permutation-model det-FDH forger's oracles**: the world, the signer, and `π`. -/
abbrev specFP := specPm (AnsFP AR M S) (T × Z)

/-- The challenger's state besides the permutation: the world's cache, the signed messages. -/
structure FPSt where
  ro : (specR AR).QueryCache
  signed : List M

variable {AR M T Z S}

/-- The signer reads `π` at `emb m`. -/
def ptF (emb : M → T × Z) : DR ⊕ M → Option (T × Z)
  | .inl _ => none
  | .inr m => some (emb m)

/-- A forward permutation query. -/
def isFwdF : (DR ⊕ M) ⊕ (Bool × (T × Z)) → Bool
  | .inr (true, _) => true
  | _ => false

/-- A signing query. -/
def isSignF : (DR ⊕ M) ⊕ (Bool × (T × Z)) → Bool
  | .inl (.inr _) => true
  | _ => false

/-- `π(b)`, as a query. -/
def fwdQF (b : T × Z) : OracleComp (specFP AR M T Z S) (T × Z) :=
  liftM ((specFP AR M T Z S).query (.inr (true, b)))

/-- **The challenger's final evaluation** of `π(emb m*)`. -/
def fpFinal (emb : M → T × Z) (o : M × S) : OracleComp (specFP AR M T Z S) (M × S) := do
  let _ ← fwdQF (emb o.1)
  pure o

/-- **A permutation-model det-FDH forger's budget**: at most `q_f` forward, `q_i` inverse and
`q_S` signing queries. -/
def FPBudget (qf qi qS : ℕ) (a : OracleComp (specFP AR M T Z S) (M × S)) : Prop :=
  IsQueryBoundP a (fun t => isFwdF t = true) qf ∧ IsQueryBoundP a (fun t => isInv t = true) qi ∧
    IsQueryBoundP a (fun t => isSignF t = true) qS

variable [DecidableEq DR] [∀ d, SampleableType (AR d)] [Inhabited T]

/-- The world and the signer `D(Tag(m))` (`Tag(m)` the first component of the value of `π` at
`emb m`), logging the signed messages (newest first). -/
def fpC (D : T → S) : (i : DR ⊕ M) → Option (T × Z) → StateT (FPSt AR M) ProbComp (AnsFP AR M S i)
  | .inl d, _ => StateT.mk fun c =>
      (fun r => (r.1, { c with ro := r.2 })) <$> ((specR AR).randomOracle d).run c.ro
  | .inr m, y => StateT.mk fun c =>
      pure (D ((y.map Prod.fst).getD default), { c with signed := m :: c.signed })

variable [DecidableEq T] [DecidableEq Z] [SampleableType T] [SampleableType Z] [Fintype T]
  [Fintype Z]

/-- **The challenger with `π` a lazy random permutation.** -/
noncomputable def fpImpl (D : T → S) (emb : M → T × Z) :
    QueryImpl (specFP AR M T Z S) (StateT (PTab (T × Z) × FPSt AR M) ProbComp) :=
  rpImpl (ptF emb) (fpC D)

/-- **The permutation-model det-FDH experiment** (one run, the key fixed). -/
noncomputable def fpRun (D : T → S) (emb : M → T × Z) (a : OracleComp (specFP AR M T Z S) (M × S)) :
    ProbComp ((M × S) × PTab (T × Z) × FPSt AR M) :=
  (simulateQ (fpImpl D emb) (a >>= fpFinal emb)).run ([], ⟨∅, []⟩)

variable {PK SK : Type}

/-- **The permutation-model det-FDH win**: `m*` never signed, `s*` a preimage of `Tag(m*)`. -/
def FPWin (IsPre : PK → S → T → Prop) (pk : PK) (emb : M → T × Z)
    (r : (M × S) × PTab (T × Z) × FPSt AR M) : Prop :=
  r.1.1 ∉ r.2.2.signed ∧ ∃ c, comP emb r.2.1 r.1.1 = some c ∧ IsPre pk r.1.2 c

/-- **`Adv^{euf}_{det}` with `H = Tag` the first component of a random permutation with inverse
queries.** -/
noncomputable def advFDHPerm (tr : Trapdoor PK SK T S) (emb : M → T × Z)
    (A : PK → ProbComp (OracleComp (specFP AR M T Z S) (M × S))) : ℝ≥0∞ :=
  Pr{let kp ← tr.keyGen; let a ← A kp.1; let r ← fpRun (tr.D kp.2) emb a}[
    FPWin tr.IsPre kp.1 emb r]

end Game

/-! ## The two hybrids -/

section Hybrids

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {M T Z S : Type} [Inhabited T] [DecidableEq T] [DecidableEq Z] [SampleableType T]
  [SampleableType Z] [Fintype T] [Fintype Z] [Fintype M] {PK SK : Type}

/-- The structured inputs, as a list. -/
noncomputable def sList (emb : M → T × Z) : List (T × Z) := (Finset.univ.image emb).toList

omit [Inhabited T] [SampleableType T] [SampleableType Z] [Fintype T] [Fintype Z] in
theorem sList_length (emb : M → T × Z) : (sList emb).length ≤ Fintype.card M := by
  unfold sList
  rw [Finset.length_toList]
  exact Finset.card_image_le.trans (by simp)

/-- **The hybrid**: `π` replaced by a two-sided random function whose fresh inverse answers avoid
the structured inputs. -/
noncomputable def fhImpl (D : T → S) (emb : M → T × Z) :
    QueryImpl (specFP AR M T Z S) (StateT (PTab (T × Z) × FPSt AR M) ProbComp) :=
  pmImpl2 (ptF emb) (fpC D) (fun _ => $ᵗ (T × Z)) fun _ => unifCompl (sList emb)

omit [DecidableEq DR] [∀ d, SampleableType (AR d)] [Inhabited T] [DecidableEq T] [DecidableEq Z]
  [SampleableType T] [SampleableType Z] [Fintype T] [Fintype Z] [Fintype M] in
theorem fpFinal_bound (p : (DR ⊕ M) ⊕ (Bool × (T × Z)) → Prop) [DecidablePred p]
    (emb : M → T × Z) (o : M × S) (k : ℕ) (hk : ∀ b, p (.inr (true, b)) → 0 < k) :
    IsQueryBoundP (fpFinal (AR := AR) emb o) p k := by
  unfold fpFinal
  rw [← Nat.add_zero k]
  exact isQueryBoundP_bind ((isQueryBoundP_query_iff _ _ _).2 (hk _)) fun _ _ => trivial

/-- **The two hybrids**: with `q = q_f + q_i + q_S + 1` queries reading the permutation,

    Adv^{perm}(A) ≤ Pr_{hybrid}[FPWin] + q²/|B| + q_i·|M|/|B|. -/
theorem advFDHPerm_le_hyb (tr : Trapdoor PK SK T S) (emb : M → T × Z)
    (A : PK → ProbComp (OracleComp (specFP AR M T Z S) (M × S))) {qf qi qS : ℕ}
    (hA : ∀ pk, ∀ a ∈ support (A pk), FPBudget qf qi qS a) :
    advFDHPerm tr emb A ≤
      Pr{let kp ← tr.keyGen; let a ← A kp.1
         let r ← (simulateQ (fhImpl (tr.D kp.2) emb) (a >>= fpFinal emb)).run ([], ⟨∅, []⟩)}[
          FPWin tr.IsPre kp.1 emb r] +
        CTUFPerm.permEps (qf + qi + qS + 1) qi (Fintype.card M) (Fintype.card (T × Z)) := by
  classical
  unfold advFDHPerm fpRun CTUFPerm.permEps
  refine prEvent_bind_le_add_const _ _ _ _ fun kp _ => ?_
  refine prEvent_bind_le_add_const _ _ _ _ fun a ha => ?_
  obtain ⟨hfw, hiv, hsg⟩ := hA kp.1 a ha
  have hpm : IsQueryBoundP (a >>= fpFinal emb)
      (fun t => isPm (ptF (DR := DR) emb) t = true) (qf + qi + qS + 1) := by
    refine isQueryBoundP_bind (isQueryBoundP_of_imp _ _ ?_ a _
      (CTUFPerm.isQueryBoundP_or _ _ a _ _ (CTUFPerm.isQueryBoundP_or _ _ a qf qi hfw hiv) hsg))
      fun o _ => fpFinal_bound _ emb o 1 fun _ _ => Nat.one_pos
    rintro ((d | m) | ⟨_ | _, b⟩) <;> simp [isPm, ptF, isFwdF, isInv, isSignF]
  have hiv' : IsQueryBoundP (a >>= fpFinal emb) (fun t => isInv t = true) (qi + 0) :=
    isQueryBoundP_bind hiv fun o _ => fpFinal_bound _ emb o 0 fun _ h => by simp [isInv] at h
  have h1 := prEvent_rp_le_rf (ptF emb) (fpC (tr.D kp.2)) (a >>= fpFinal emb) _ hpm []
    (⟨∅, []⟩ : FPSt AR M) fun r => FPWin tr.IsPre kp.1 emb r
  have h2 := prEvent_rf_le_avoid (ptF emb) (fpC (tr.D kp.2)) (a >>= fpFinal emb) qi
    (by simpa using hiv') (sList emb) [] (⟨∅, []⟩ : FPSt AR M) fun r => FPWin tr.IsPre kp.1 emb r
  rw [List.length_nil, zero_add] at h1
  have hS : (qi : ℝ≥0∞) * ((sList emb).length / Fintype.card (T × Z)) ≤
      qi * (Fintype.card M / Fintype.card (T × Z)) := by
    gcongr; exact_mod_cast sList_length emb
  calc _ ≤ _ := h1
    _ ≤ _ := add_le_add (h2.trans (add_le_add le_rfl hS)) le_rfl
    _ = _ := by unfold fhImpl; ring

end Hybrids

end VoleMole.Assumptions.UOV.FDHPerm
