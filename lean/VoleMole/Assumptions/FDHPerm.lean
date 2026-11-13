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

set_option linter.unusedSectionVars false

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

theorem sList_length (emb : M → T × Z) : (sList emb).length ≤ Fintype.card M := by
  unfold sList
  rw [Finset.length_toList]
  exact Finset.card_image_le.trans (by simp)

/-- **The hybrid**: `π` replaced by a two-sided random function whose fresh inverse answers avoid
the structured inputs. -/
noncomputable def fhImpl (D : T → S) (emb : M → T × Z) :
    QueryImpl (specFP AR M T Z S) (StateT (PTab (T × Z) × FPSt AR M) ProbComp) :=
  pmImpl2 (ptF emb) (fpC D) (fun _ => $ᵗ (T × Z)) fun _ => unifCompl (sList emb)

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

/-! ## The reduction to the random-function det-FDH game -/

section Red

variable {DR : Type} (AR : DR → Type) {M T Z : Type} [Fintype M] [DecidableEq T] [DecidableEq Z]
  (emb : M → T × Z)

/-- The coins for fresh inverse answers: blocks outside the structured inputs. -/
abbrev Bc := {b : T × Z // b ∉ sList emb}

/-- **The world with coins**: the forger's world, coins `ℕ → T × Z`, coins `ℕ → Bc`. -/
abbrev ARF : DR ⊕ (ℕ ⊕ ℕ) → Type := Sum.elim AR (Sum.elim (fun _ => T × Z) fun _ => Bc emb)

instance instARF [∀ d, SampleableType (AR d)] [SampleableType T] [SampleableType Z]
    [SampleableType (Bc emb)] : ∀ d, SampleableType (ARF AR emb d)
  | .inl d => inferInstanceAs (SampleableType (AR d))
  | .inr (.inl _) => inferInstanceAs (SampleableType (T × Z))
  | .inr (.inr _) => inferInstanceAs (SampleableType (Bc emb))

variable {AR} {S : Type}

/-- The reduction's oracles: det-FDH's, with the world with coins. -/
abbrev specFR := specF (ARF AR emb) M T S

/-- A world (or coin) query. -/
def wQF (d : DR ⊕ (ℕ ⊕ ℕ)) : OracleComp (specFR emb (AR := AR) (S := S)) (ARF AR emb d) :=
  liftM ((specFR emb (AR := AR) (S := S)).query (.inl d))

/-- A hash query. -/
def hQF (m : M) : OracleComp (specFR emb (AR := AR) (S := S)) T :=
  liftM ((specFR emb (AR := AR) (S := S)).query (.inr (.inl m)))

/-- A signing query. -/
def sQF (m : M) : OracleComp (specFR emb (AR := AR) (S := S)) S :=
  liftM ((specFR emb (AR := AR) (S := S)).query (.inr (.inr m)))

/-- **The simulated forward step**: a recorded value, or `(H(m), z)` at a structured input
`emb m` (`z` from a coin), or a coin. -/
noncomputable def simFwd (b : T × Z) (s : PTab (T × Z) × ℕ) :
    OracleComp (specFR emb (AR := AR) (S := S)) ((T × Z) × (PTab (T × Z) × ℕ)) :=
  match fwdFind s.1 b with
  | some y => pure (y, s)
  | none => match CTUFPerm.embInv emb b with
    | some m => hQF emb m >>= fun t => (fun c : T × Z => ((t, c.2), (s.1 ++ [(b, (t, c.2), true)],
        s.2 + 1))) <$> wQF emb (.inr (.inl s.2))
    | none => (fun c : T × Z => (c, (s.1 ++ [(b, c, true)], s.2 + 1))) <$> wQF emb (.inr (.inl s.2))

/-- **The reduction's simulation**: the world forwarded; `Sign(m)` evaluates `π(emb m)` first;
fresh inverse answers are coins outside the structured inputs. -/
noncomputable def simCF :
    QueryImpl (specFP AR M T Z S) (StateT (PTab (T × Z) × ℕ) (OracleComp (specFR emb (AR := AR) (S := S))))
  | .inl (.inl d) => StateT.mk fun s => (fun a => (a, s)) <$> wQF emb (.inl d)
  | .inl (.inr m) => StateT.mk fun s => simFwd emb (emb m) s >>= fun r =>
      (fun a => (a, r.2)) <$> sQF emb m
  | .inr (true, b) => StateT.mk fun s => simFwd emb b s
  | .inr (false, c) => StateT.mk fun s => match invFind s.1 c with
    | some x => pure (x, s)
    | none => (fun x : Bc emb => (x.1, (s.1 ++ [(x.1, c, false)], s.2 + 1))) <$>
        wQF emb (.inr (.inr s.2))

/-- **The function-model forger**: the permutation-model forger and the final evaluation, under
the simulation. -/
noncomputable def simA (a : OracleComp (specFP AR M T Z S) (M × S)) :
    OracleComp (specFR emb (AR := AR) (S := S)) (M × S) :=
  Prod.fst <$> (simulateQ (simCF emb) (a >>= fpFinal emb)).run ([], 0)

/-- **The reduction.** -/
noncomputable def fdhPermRed {PK : Type} (A : PK → ProbComp (OracleComp (specFP AR M T Z S) (M × S)))
    (pk : PK) : ProbComp (OracleComp (specFR emb (AR := AR) (S := S)) (M × S)) :=
  simA emb <$> A pk

end Red

/-! ## The reduction against the det-FDH challenger -/

section Core

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {M T Z S : Type} [Fintype M] [DecidableEq M] [Inhabited T] [DecidableEq T] [DecidableEq Z]
  [SampleableType T] [SampleableType Z] [Fintype T] [Fintype Z] (emb : M → T × Z)
  [SampleableType (Bc emb)] (D : T → S)

/-- **The reduction run against the det-FDH challenger, as one handler.** -/
noncomputable def combF : QueryImpl (specFP AR M T Z S)
    (StateT ((PTab (T × Z) × ℕ) × FDHSt (ARF AR emb) M T) ProbComp) :=
  fun q => StateT.mk fun s => (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (fdhImpl D) ((simCF emb q).run s.1)).run s.2

theorem collapseFP {α : Type} (oa : OracleComp (specFP AR M T Z S) α) (s : PTab (T × Z) × ℕ)
    (c : FDHSt (ARF AR emb) M T) :
    (simulateQ (fdhImpl D) ((simulateQ (simCF emb) oa).run s)).run c =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (combF emb D) oa).run (s, c) := by
  refine simulateQ_StateT_StateT_compose _ _ _ (fun q s c => ?_) oa s c
  show _ = _ <$> ((fun r : (_ × _) × _ => (r.1.1, (r.1.2, r.2))) <$> _)
  rw [Functor.map_map]
  exact (id_map _).symm

/-- The world's cache without the coins. -/
def projROF (c : (specR (ARF AR emb)).QueryCache) : (specR AR).QueryCache :=
  QueryCache.ofFn fun d => c (.inl d)

/-- **The hybrid's state that the reduction's run represents.** -/
def projF (s : (PTab (T × Z) × ℕ) × FDHSt (ARF AR emb) M T) : PTab (T × Z) × FPSt AR M :=
  (s.1.1, ⟨projROF emb s.2.ro, s.2.signed⟩)

/-- **The invariant**: unused coins from the counter on; `H` defined only at messages with a
record; a forward record at a structured input carries `H`; no inverse record at a structured
input. -/
def InvF (s : (PTab (T × Z) × ℕ) × FDHSt (ARF AR emb) M T) : Prop :=
  (∀ k, s.1.2 ≤ k → s.2.ro (.inr (.inl k)) = none ∧ s.2.ro (.inr (.inr k)) = none) ∧
  (∀ m, fwdFind s.1.1 (emb m) = none → s.2.h m = none) ∧
  (∀ e ∈ s.1.1, e.2.2 = true → ∀ m, e.1 = emb m → s.2.h m = some e.2.1.1) ∧
  (∀ e ∈ s.1.1, e.2.2 = false → e.1 ∉ sList emb)

theorem combF_world (d : DR) (L : PTab (T × Z)) (n : ℕ) (c : FDHSt (ARF AR emb) M T) :
    ((combF emb D) (.inl (.inl d))).run ((L, n), c) =
      (fun r : AR d × (specR (ARF AR emb)).QueryCache => (r.1, ((L, n), { c with ro := r.2 }))) <$>
        ((specR (ARF AR emb)).randomOracle (Sum.inl d)).run c.ro := by
  simp only [combF, simCF, StateT.run_mk, wQF]
  erw [simulateQ_map, simulateQ_spec_query]
  erw [StateT.run_map]
  simp only [fdhImpl]
  repeat (first | erw [StateT.run_mk] | erw [Functor.map_map])
  rfl

theorem combF_fwd_found (b y : T × Z) (s : (PTab (T × Z) × ℕ) × FDHSt (ARF AR emb) M T)
    (h : fwdFind s.1.1 b = some y) :
    ((combF emb D) (.inr (true, b))).run s = pure (y, s) := by
  show (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (fdhImpl D) (simFwd emb b s.1)).run s.2 = _
  simp only [simFwd, h]
  erw [simulateQ_pure]
  rfl

theorem combF_inv_found (c x : T × Z) (s : (PTab (T × Z) × ℕ) × FDHSt (ARF AR emb) M T)
    (h : invFind s.1.1 c = some x) :
    ((combF emb D) (.inr (false, c))).run s = pure (x, s) := by
  simp only [combF, simCF, StateT.run_mk, h]
  erw [simulateQ_pure]
  rfl

theorem combF_fwd_coin (b : T × Z) (L : PTab (T × Z)) (n : ℕ) (c : FDHSt (ARF AR emb) M T)
    (h : fwdFind L b = none) (he : CTUFPerm.embInv emb b = none)
    (hro : c.ro (.inr (.inl n)) = none) :
    ((combF emb D) (.inr (true, b))).run ((L, n), c) =
      (fun u : T × Z => (u, ((L ++ [(b, u, true)], n + 1),
        { c with ro := c.ro.cacheQuery (.inr (.inl n)) u }))) <$> ($ᵗ (T × Z) : ProbComp (T × Z)) := by
  show (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (fdhImpl D) (simFwd emb b (L, n))).run c = _
  simp only [simFwd, h, he, wQF]
  erw [simulateQ_map, simulateQ_spec_query]
  erw [StateT.run_map]
  simp only [fdhImpl]
  erw [StateT.run_mk]
  try dsimp only
  erw [randomOracle.run_eq]
  rw [show c.ro.toFn (Sum.inr (Sum.inl n)) = none from hro]
  try dsimp only
  rw [map_bind]
  simp only [map_pure]
  rw [bind_pure_comp]
  repeat erw [Functor.map_map]
  rfl

theorem combF_inv_fresh (c' : T × Z) (L : PTab (T × Z)) (n : ℕ) (c : FDHSt (ARF AR emb) M T)
    (h : invFind L c' = none) (hro : c.ro (.inr (.inr n)) = none) :
    ((combF emb D) (.inr (false, c'))).run ((L, n), c) =
      (fun x : Bc emb => (x.1, ((L ++ [(x.1, c', false)], n + 1),
        { c with ro := c.ro.cacheQuery (.inr (.inr n)) x }))) <$> ($ᵗ (Bc emb) : ProbComp (Bc emb)) := by
  simp only [combF, simCF, StateT.run_mk, h, wQF]
  erw [simulateQ_map, simulateQ_spec_query]
  erw [StateT.run_map]
  simp only [fdhImpl]
  erw [StateT.run_mk]
  try dsimp only
  erw [randomOracle.run_eq]
  rw [show c.ro.toFn (Sum.inr (Sum.inr n)) = none from hro]
  try dsimp only
  rw [map_bind]
  simp only [map_pure]
  rw [bind_pure_comp]
  repeat erw [Functor.map_map]
  rfl

theorem combF_fwd_com (b : T × Z) (m : M) (L : PTab (T × Z)) (n : ℕ) (c : FDHSt (ARF AR emb) M T)
    (h : fwdFind L b = none) (he : CTUFPerm.embInv emb b = some m) (htab : c.h m = none)
    (hro : c.ro (.inr (.inl n)) = none) :
    ((combF emb D) (.inr (true, b))).run ((L, n), c) =
      (do let t ← ($ᵗ T : ProbComp T); let u ← ($ᵗ (T × Z) : ProbComp (T × Z))
          pure ((t, u.2), ((L ++ [(b, (t, u.2), true)], n + 1),
            { c with h := Function.update c.h m (some t), hq := c.hq + 1,
                     ro := c.ro.cacheQuery (.inr (.inl n)) u }))) := by
  show (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (fdhImpl D) (simFwd emb b (L, n))).run c = _
  simp only [simFwd, h, he, wQF, hQF]
  erw [simulateQ_bind, simulateQ_spec_query]
  erw [StateT.run_bind]
  simp only [fdhImpl]
  erw [StateT.run_mk]
  try dsimp only
  simp only [hStep, htab]
  erw [Functor.map_map, bind_map_left, map_bind]
  refine bind_congr fun (t : T) => ?_
  erw [simulateQ_map, simulateQ_spec_query, StateT.run_map]
  simp only [fdhImpl]
  erw [StateT.run_mk]
  try dsimp only
  erw [randomOracle.run_eq]
  rw [show c.ro.toFn (Sum.inr (Sum.inl n)) = none from hro]
  try dsimp only
  rw [map_bind]
  simp only [map_pure]
  rw [bind_pure_comp, bind_pure_comp]
  repeat erw [Functor.map_map]
  rfl

theorem run_sQF (m : M) (c : FDHSt (ARF AR emb) M T) :
    (simulateQ (fdhImpl D) (sQF emb (S := S) m)).run c =
      (fun r => (D r.1, { r.2 with signed := m :: r.2.signed })) <$> hStep m c := by
  unfold sQF
  erw [simulateQ_spec_query]
  rfl

theorem combF_sign (m : M) (s : (PTab (T × Z) × ℕ) × FDHSt (ARF AR emb) M T) :
    ((combF emb D) (.inl (.inr m))).run s =
      ((combF emb D) (.inr (true, emb m))).run s >>= fun r =>
        (fun w => (w.1, (r.2.1, w.2))) <$> (simulateQ (fdhImpl D) (sQF emb (S := S) m)).run r.2.2 := by
  show (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (fdhImpl D) (simFwd emb (emb m) s.1 >>= fun r =>
      (fun a => (a, r.2)) <$> sQF emb m)).run s.2 = (fun r => (r.1.1, (r.1.2, r.2))) <$>
      (simulateQ (fdhImpl D) (simFwd emb (emb m) s.1)).run s.2 >>= _
  rw [simulateQ_bind, StateT.run_bind, map_bind]
  erw [bind_map_left]
  refine bind_congr fun r => ?_
  erw [simulateQ_map, StateT.run_map, Functor.map_map]

theorem projROF_ne (c : (specR (ARF AR emb)).QueryCache) (e : ℕ ⊕ ℕ) (u : ARF AR emb (.inr e)) :
    projROF emb (c.cacheQuery (.inr e) u) = projROF emb c := by
  refine QueryCache.ext fun d => ?_
  show (c.cacheQuery (.inr e) u) (.inl d) = c (.inl d)
  exact QueryCache.cacheQuery_of_ne _ _ (by simp)

theorem roF_proj_inl (d : DR) (ro : (specR (ARF AR emb)).QueryCache) :
    (fun r : (specR (ARF AR emb)).Range (Sum.inl d) × (specR (ARF AR emb)).QueryCache =>
        ((r.1 : AR d), projROF emb r.2)) <$> ((specR (ARF AR emb)).randomOracle (Sum.inl d)).run ro =ᵈ
      ((specR AR).randomOracle d).run (projROF emb ro) := by
  rw [randomOracle.run_eq, randomOracle.run_eq]
  rw [show (projROF emb ro).toFn d = ro.toFn (.inl d) from rfl]
  cases h : ro.toFn (.inl d) with
  | some u => simp only [map_pure]; exact EvalDistEq.rfl
  | none =>
    dsimp only
    rw [map_bind]
    simp only [map_pure]
    have e : ∀ u : AR d, projROF emb (ro.cacheQuery (Sum.inl d) u) = (projROF emb ro).cacheQuery d u := by
      intro u
      refine QueryCache.ext fun d' => ?_
      show (ro.cacheQuery (.inl d) u) (.inl d') = ((projROF emb ro).cacheQuery d u) d'
      by_cases hd : d' = d
      · subst hd
        rw [show ((projROF emb ro).cacheQuery d' u) d' = some u from QueryCache.cacheQuery_self _ _ _]
        exact QueryCache.cacheQuery_self (spec := specR (ARF AR emb)) ro (.inl d') u
      · rw [show ((projROF emb ro).cacheQuery d u) d' = (projROF emb ro) d' from
          QueryCache.cacheQuery_of_ne _ _ hd]
        exact QueryCache.cacheQuery_of_ne (spec := specR (ARF AR emb)) ro (t := Sum.inl d) u
          (by simpa using hd)
    show (($ᵗ (AR d) : ProbComp (AR d)) >>= fun u =>
        (pure (u, projROF emb (ro.cacheQuery (Sum.inl d) u)) : ProbComp (AR d × (specR AR).QueryCache))) =ᵈ
      (($ᵗ (AR d) : ProbComp (AR d)) >>= fun u => pure (u, (projROF emb ro).cacheQuery d u))
    simp only [e]
    exact EvalDistEq.rfl

/-- **The inverse coins are a fresh value outside the structured inputs.** -/
theorem bc_eqd : Subtype.val <$> ($ᵗ (Bc emb) : ProbComp (Bc emb)) =ᵈ unifCompl (sList emb) := by
  have hne : ∃ y, y ∉ sList emb := by
    obtain ⟨⟨y, hy⟩⟩ := SampleableType.nonempty (Bc emb); exact ⟨y, hy⟩
  refine evalDistEq_of_forall_prEvent_eq_output fun a => ?_
  rw [prEvent_unifCompl_eq _ hne, prEvent_map, SampleableType.prEvent_uniformSample]
  have hc : Fintype.card (Bc emb) = (Finset.univ.filter (· ∉ sList emb)).card :=
    Fintype.card_subtype _
  split_ifs with ha
  · have : (Finset.univ.filter fun x : Bc emb => x.val = a) = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro hx; exact x.2 (hx ▸ ha)
    rw [this]; simp
  · have : (Finset.univ.filter fun x : Bc emb => x.val = a) = {⟨a, ha⟩} := by
      ext x; simp [Subtype.ext_iff]
    rw [this, Finset.card_singleton, hc]; simp only [Nat.cast_one, one_div]
    convert rfl

theorem fhImpl_world (d : DR) (L : PTab (T × Z)) (fs : FPSt AR M) :
    ((fhImpl (S := S) D emb) (.inl (.inl d))).run (L, fs) =
      (fun r : AR d × (specR AR).QueryCache => (r.1, (L, (⟨r.2, fs.signed⟩ : FPSt AR M)))) <$>
        ((specR AR).randomOracle d).run fs.ro := by
  simp only [fhImpl, pmImpl2, ptF, StateT.run_mk, fpC]
  repeat (first | erw [StateT.run_mk] | erw [Functor.map_map])
  rfl

theorem fhImpl_sign (m : M) (st : PTab (T × Z) × FPSt AR M) :
    ((fhImpl (S := S) D emb) (.inl (.inr m))).run st =
      ((fhImpl (S := S) D emb) (.inr (true, emb m))).run st >>= fun r =>
        pure (D r.1.1, (r.2.1, (⟨r.2.2.ro, m :: r.2.2.signed⟩ : FPSt AR M))) := by
  simp only [fhImpl, pmImpl2, ptF, StateT.run_mk, fpC, bind_map_left]
  refine bind_congr fun r => ?_
  simp only [map_pure, Option.map_some, Option.getD_some]
  rfl


theorem projROF_coinF (ro : (specR (ARF AR emb)).QueryCache) (n : ℕ) (u : T × Z) :
    projROF emb (ro.cacheQuery (.inr (.inl n)) u) = projROF emb ro := projROF_ne emb ro (.inl n) u

theorem projROF_coinI (ro : (specR (ARF AR emb)).QueryCache) (n : ℕ) (x : Bc emb) :
    projROF emb (ro.cacheQuery (.inr (.inr n)) x) = projROF emb ro := projROF_ne emb ro (.inr n) x

theorem mem_sList (m : M) : emb m ∈ sList emb := by
  unfold sList
  rw [Finset.mem_toList]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- **The forward step.** -/
theorem combF_step_fwd (b : T × Z) (s : (PTab (T × Z) × ℕ) × FDHSt (ARF AR emb) M T)
    (hs : InvF emb s) :
    (fun z => (z.1, projF emb z.2)) <$> ((combF emb D) (.inr (true, b))).run s =ᵈ
      ((fhImpl (S := S) D emb) (.inr (true, b))).run (projF emb s) := by
  obtain ⟨⟨L, n⟩, c⟩ := s
  obtain ⟨h1, h2, -, -⟩ := hs
  have hro : c.ro (.inr (.inl n)) = none := (h1 n le_rfl).1
  show _ =ᵈ (fun r => (r.1, (r.2, (⟨projROF emb c.ro, c.signed⟩ : FPSt AR M)))) <$>
    fwdS (fun _ => ($ᵗ (T × Z) : ProbComp (T × Z))) b L
  simp only [fwdS]
  cases h : fwdFind L b with
  | some y =>
    rw [combF_fwd_found emb D b y _ h]
    simp only [map_pure]; exact EvalDistEq.rfl
  | none =>
    cases he : CTUFPerm.embInv emb b with
    | none =>
      rw [combF_fwd_coin emb D b L n c h he hro]
      exact CTUFPerm.map_map_eqd2 _ _ _ _ _ fun u => by simp [projF, projROF_coinF]
    | some m =>
      have hb := CTUFPerm.embInv_some he
      have htab : c.h m = none := h2 m (by rw [hb]; exact h)
      rw [combF_fwd_com emb D b m L n c h he htab hro]
      have := (CTUFPerm.uniform_pair (T := T) (Z := Z)).map
        (fun y => (y, (L ++ [(b, y, true)], (⟨projROF emb c.ro, c.signed⟩ : FPSt AR M))))
      simp only [map_bind, map_pure, Functor.map_map] at this ⊢
      simp only [projF]
      refine EvalDistEq.trans (EvalDistEq.bind_congr EvalDistEq.rfl fun a =>
        EvalDistEq.bind_congr EvalDistEq.rfl fun u => ?_) this
      rw [projROF_coinF]
      exact EvalDistEq.rfl

/-- **The forward step records its answer.** -/
theorem combF_fwd_rec (b : T × Z) (s : (PTab (T × Z) × ℕ) × FDHSt (ARF AR emb) M T)
    (hs : InvF emb s) :
    ∀ z ∈ support (((combF emb D) (.inr (true, b))).run s), fwdFind z.2.1.1 b = some z.1 := by
  intro z hz
  obtain ⟨⟨L, n⟩, c⟩ := s
  obtain ⟨h1, h2, -, -⟩ := hs
  have hro : c.ro (.inr (.inl n)) = none := (h1 n le_rfl).1
  cases h : fwdFind L b with
  | some y =>
    rw [combF_fwd_found emb D b y _ h] at hz
    erw [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact h
  | none =>
    cases he : CTUFPerm.embInv emb b with
    | none =>
      rw [combF_fwd_coin emb D b L n c h he hro] at hz
      erw [support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      simp [CTUFPerm.fwdFind_append, h]
    | some m =>
      have hb := CTUFPerm.embInv_some he
      have htab : c.h m = none := h2 m (by rw [hb]; exact h)
      rw [combF_fwd_com emb D b m L n c h he htab hro] at hz
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨t, -, u, -, rfl⟩ := hz
      simp [CTUFPerm.fwdFind_append, h]

/-- **Under the invariant, a record at a structured input carries `H`.** -/
theorem h_of_fwdFind {s : (PTab (T × Z) × ℕ) × FDHSt (ARF AR emb) M T} (hs : InvF emb s)
    {m : M} {y : T × Z} (h : fwdFind s.1.1 (emb m) = some y) : s.2.h m = some y.1 := by
  obtain ⟨e, he, he1, he2⟩ := CTUFPerm.fwdFind_some h
  cases hf : e.2.2
  · exact absurd (he1 ▸ mem_sList emb m) (hs.2.2.2 e he hf)
  · rw [hs.2.2.1 e he hf m he1, he2]

/-- **The forward step keeps the invariant.** -/
theorem combF_inv_fwd (hemb : Function.Injective emb) (b : T × Z)
    (s : (PTab (T × Z) × ℕ) × FDHSt (ARF AR emb) M T) (hs : InvF emb s) :
    ∀ z ∈ support (((combF emb D) (.inr (true, b))).run s), InvF emb z.2 := by
  intro z hz
  obtain ⟨⟨L, n⟩, c⟩ := s
  obtain ⟨h1, h2, h3, h4⟩ := hs
  dsimp only at h1 h2 h3 h4
  have hro : c.ro (.inr (.inl n)) = none := (h1 n le_rfl).1
  have hcoin : ∀ (u : T × Z) k, n + 1 ≤ k →
      (c.ro.cacheQuery (.inr (.inl n)) u) (.inr (.inl k)) = none ∧
        (c.ro.cacheQuery (.inr (.inl n)) u) (.inr (.inr k)) = none := fun u k hk =>
    ⟨(QueryCache.cacheQuery_of_ne _ _ (by simp; omega)).trans (h1 k (by omega)).1,
      (QueryCache.cacheQuery_of_ne _ _ (by simp)).trans (h1 k (by omega)).2⟩
  cases h : fwdFind L b with
  | some y =>
    rw [combF_fwd_found emb D b y _ h] at hz
    erw [support_pure, Set.mem_singleton_iff] at hz; subst hz
    exact ⟨h1, h2, h3, h4⟩
  | none =>
    cases he : CTUFPerm.embInv emb b with
    | none =>
      rw [combF_fwd_coin emb D b L n c h he hro] at hz
      erw [support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      refine ⟨hcoin u, fun m hm => h2 m (CTUFPerm.fwdFind_append_none hm).1,
        fun e he' hf m hm => ?_, fun e he' hf => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at he'
        rcases he' with he' | rfl
        · exact h3 e he' hf m hm
        · simp only at hm
          rw [hm, CTUFPerm.embInv_emb hemb] at he; cases he
      · simp only [List.mem_append, List.mem_singleton] at he'
        rcases he' with he' | rfl
        · exact h4 e he' hf
        · simp at hf
    | some m =>
      have hb := CTUFPerm.embInv_some he
      have htab : c.h m = none := h2 m (by rw [hb]; exact h)
      rw [combF_fwd_com emb D b m L n c h he htab hro] at hz
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨t, -, u, -, rfl⟩ := hz
      refine ⟨hcoin u, fun m' hm' => ?_, fun e he' hf m' hm' => ?_, fun e he' hf => ?_⟩
      · obtain ⟨hL, hne⟩ := CTUFPerm.fwdFind_append_none hm'
        have hm'm : m' ≠ m := fun hh => hne (by simp only; rw [hh, hb])
        show Function.update c.h m (some t) m' = none
        rw [Function.update_of_ne hm'm]; exact h2 m' hL
      · show Function.update c.h m (some t) m' = some e.2.1.1
        simp only [List.mem_append, List.mem_singleton] at he'
        rcases he' with he' | rfl
        · by_cases hm'm : m' = m
          · subst hm'm
            exfalso
            have hh := h3 e he' hf m' hm'
            rw [htab] at hh; cases hh
          · rw [Function.update_of_ne hm'm]; exact h3 e he' hf m' hm'
        · simp only at hm'
          have : m' = m := hemb (by rw [← hm', hb])
          subst this; simp
      · simp only [List.mem_append, List.mem_singleton] at he'
        rcases he' with he' | rfl
        · exact h4 e he' hf
        · simp at hf

/-- **A signing query after the forward step**: `D(H(m))` with `H(m)` the recorded value. -/
theorem combF_sign_eqd (hemb : Function.Injective emb) (m : M)
    (s : (PTab (T × Z) × ℕ) × FDHSt (ARF AR emb) M T) (hs : InvF emb s) :
    ((combF emb D) (.inl (.inr m))).run s =ᵈ
      (fun r => (D r.1.1, (r.2.1, { r.2.2 with signed := m :: r.2.2.signed }))) <$>
        ((combF emb D) (.inr (true, emb m))).run s := by
  rw [combF_sign, ← bind_pure_comp]
  refine EvalDistEq.bind_congr_of_support _ fun r hr => ?_
  have hh := h_of_fwdFind emb (combF_inv_fwd emb D hemb _ s hs r hr)
    (combF_fwd_rec emb D _ s hs r hr)
  rw [run_sQF]
  simp only [hStep, hh, map_pure]
  exact EvalDistEq.rfl

/-- **The step**: one query of the reduction against the det-FDH challenger, projected, is the
hybrid's. -/
theorem combF_step (hemb : Function.Injective emb) (q : (DR ⊕ M) ⊕ (Bool × (T × Z)))
    (s : (PTab (T × Z) × ℕ) × FDHSt (ARF AR emb) M T) (hs : InvF emb s) :
    (fun z => (z.1, projF emb z.2)) <$> ((combF emb D) q).run s =ᵈ
      ((fhImpl (S := S) D emb) q).run (projF emb s) := by
  rcases q with (d | m) | ⟨_ | _, b⟩
  · obtain ⟨⟨L, n⟩, c⟩ := s
    rw [combF_world, projF]
    erw [fhImpl_world]
    have := (roF_proj_inl emb d c.ro).map (m := ProbComp)
      (fun p : AR d × (specR AR).QueryCache => (p.1, (L, (⟨p.2, c.signed⟩ : FPSt AR M))))
    erw [Functor.map_map] at this
    erw [Functor.map_map]
    exact this
  · refine ((combF_sign_eqd emb D hemb m s hs).map _).trans ?_
    rw [fhImpl_sign, Functor.map_map]
    have := (combF_step_fwd emb D (emb m) s hs).map (m := ProbComp)
      (fun r : (T × Z) × PTab (T × Z) × FPSt AR M =>
        (D r.1.1, (r.2.1, (⟨r.2.2.ro, m :: r.2.2.signed⟩ : FPSt AR M))))
    erw [Functor.map_map] at this
    rw [bind_pure_comp]
    exact this
  · obtain ⟨⟨L, n⟩, c⟩ := s
    have hro : c.ro (.inr (.inr n)) = none := (hs.1 n le_rfl).2
    show _ =ᵈ (fun r => (r.1, (r.2, (⟨projROF emb c.ro, c.signed⟩ : FPSt AR M)))) <$>
      invS (fun _ => unifCompl (sList emb)) b L
    simp only [invS]
    cases h : invFind L b with
    | some x =>
      rw [combF_inv_found emb D b x _ h]
      simp only [map_pure]; exact EvalDistEq.rfl
    | none =>
      rw [combF_inv_fresh emb D b L n c h hro]
      have e2 := (bc_eqd emb).map (m := ProbComp)
        (fun x : T × Z => (x, (L ++ [(x, b, false)], (⟨projROF emb c.ro, c.signed⟩ : FPSt AR M))))
      refine EvalDistEq.trans ?_ (e2.trans ?_)
      · refine CTUFPerm.map_map_eqd2 _ _ _ _ _ fun x => ?_
        simp [projF, projROF_coinI]
      · rw [Functor.map_map]
  · exact combF_step_fwd emb D b s hs

theorem roF_support (d : DR ⊕ (ℕ ⊕ ℕ)) (ro : (specR (ARF AR emb)).QueryCache) :
    ∀ z ∈ support (((specR (ARF AR emb)).randomOracle d).run ro),
      z.2 = ro ∨ z.2 = ro.cacheQuery d z.1 := by
  intro z hz
  rw [randomOracle.run_eq] at hz
  cases h : ro.toFn d with
  | some u => rw [h] at hz; simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact .inl rfl
  | none =>
    rw [h] at hz
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz; exact .inr rfl

/-- **The invariant is preserved.** -/
theorem combF_inv (hemb : Function.Injective emb) :
    QueryImpl.PreservesInv (combF emb D (S := S)) (InvF (AR := AR) emb) := by
  intro q s hs z hz
  rcases q with (d | m) | ⟨_ | _, b⟩
  · obtain ⟨⟨L, n⟩, c⟩ := s
    obtain ⟨h1, h2, h3, h4⟩ := hs
    erw [combF_world] at hz
    erw [support_map] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    refine ⟨fun k hk => ?_, h2, h3, h4⟩
    have hne : ∀ e : ℕ ⊕ ℕ, (r.2 (.inr e) = c.ro (.inr e)) := by
      intro e
      rcases roF_support emb (.inl d) c.ro r hr with he | he
      · rw [he]
      · rw [he]; exact QueryCache.cacheQuery_of_ne _ _ (by simp)
    exact ⟨(hne _).trans (h1 k hk).1, (hne _).trans (h1 k hk).2⟩
  · rw [combF_sign] at hz
    erw [mem_support_bind_iff] at hz
    obtain ⟨r, hr, hz⟩ := hz
    have hh := h_of_fwdFind emb (combF_inv_fwd emb D hemb _ s hs r hr)
      (combF_fwd_rec emb D _ s hs r hr)
    rw [run_sQF] at hz
    simp only [hStep, hh, map_pure] at hz
    subst hz
    exact combF_inv_fwd emb D hemb _ s hs r hr
  · obtain ⟨⟨L, n⟩, c⟩ := s
    obtain ⟨h1, h2, h3, h4⟩ := hs
    dsimp only at h1 h2 h3 h4
    have hro : c.ro (.inr (.inr n)) = none := (h1 n le_rfl).2
    cases h : invFind L b with
    | some x =>
      rw [combF_inv_found emb D b x _ h] at hz
      erw [support_pure, Set.mem_singleton_iff] at hz; subst hz
      exact ⟨h1, h2, h3, h4⟩
    | none =>
      rw [combF_inv_fresh emb D b L n c h hro] at hz
      erw [support_map] at hz
      obtain ⟨x, -, rfl⟩ := hz
      refine ⟨fun k hk => ⟨?_, ?_⟩, fun m hm => h2 m (CTUFPerm.fwdFind_append_none hm).1,
        fun e he hf m hm => ?_, fun e he hf => ?_⟩
      · exact (QueryCache.cacheQuery_of_ne _ _ (by simp)).trans (h1 k (by simp at hk; omega)).1
      · exact (QueryCache.cacheQuery_of_ne _ _ (by simp at hk ⊢; omega)).trans
          (h1 k (by simp at hk; omega)).2
      · simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact h3 e he hf m hm
        · simp at hf
      · simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact h4 e he hf
        · exact x.2
  · exact combF_inv_fwd emb D hemb b s hs z hz

end Core

end VoleMole.Assumptions.UOV.FDHPerm
