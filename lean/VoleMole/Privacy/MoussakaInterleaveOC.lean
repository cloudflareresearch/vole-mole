import VoleMole.Privacy.MoussakaInterleave
import VoleMole.ZK.ReadsInterleaveOC
import VoleMole.Privacy.RatatouilleAdaptive

/-!
# Moussaka with interleaved sessions, a table-reading scheduler and a free challenge

`Privacy/MoussakaInterleave.lean` with the two generalizations of
`Privacy/PomFRITInterleaveOC.lean`:

* **the scheduler reads the tables**: each step is a VCVio oracle computation over the four
  challenge `H₃` slices and the shared tables (`ROM.Reads.TSpec (Bool × Bool)`), within a per-step
  query bound (`AdversaryILMO.SBudget a₃ a₂ a₅ a_E`); consistency is by construction;
* **the challenge is placed by the scheduler**: it starts at the first step at which `go` holds (at
  most `L₁` steps); the answers (both responses and both Anchor Set choices) are read off the
  transcript at the first step at which `done` holds (at most `L₂` steps later); the outcome
  (§6's rule) is revealed then, and at most `L₃` steps follow.

The two issuance requests are revealed together and the outcome after all answers; as for
PomFRIT, neither restricts the adversary (a request revealed earlier gives more; an answer has no
visible effect before the outcome, which §6's rule computes from all four answers).

## The reduction

For each tape `c` of the further Clients the game is the key-stage game (`realGameRAK`) of
`A.red idx c` (`realGameILMO_iff`, `Iff.rfl`), whose key stage runs the steps before the
challenge, its interaction the steps up to the answers and its guess the rest, each on the slices
and the tables. Budgets (`ZK/ReadsInterleaveOC.lean`, `GoodO.sreads`, per slice position):
key stage `(L₁a₃, 2·2³²n + L₁a₂, 1248n + L₁a₅, 9214n + L₁a_E)` (`red_kBudget`), interaction the
same with `L₂` (`red_iBudget`), guess `((L₂+L₃)a₃ + q₃, 1248n + (L₂+L₃)a₅ + q₅, 9214n + (L₂+L₃)a_E +
q_E)` (`red_gBudget`).

## The bound

`anonymityRAK_lean_numG` for every `c`, averaged: `anonymityILO_lean_numG`, `_num`, `_num_perm`;
in numbers (`anonymityILO_lean_le`)

    ≤ (n + 2)·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 28·L·(a₃ + a₂ + a₅ + 221·a_E)·2⁻¹²⁸ + 2·εhide

with `L = L₁ + L₂ + L₃`: `2⁻⁸¹` (`2⁻⁶⁹`) at `n + 2 ≤ 2²⁰` (`2³²`) plus the budget terms
(`anonymityILO_lean_2pow20`, `_2pow32`). Hiding of `Com` is assumed for the reductions of every
`A.red idx c`.
-/

open Finset OracleComp OracleSpec

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM.Reads (TKey TSpec QBudget sl4 ins4 read_ins4 readAt read_congr)
open VoleMole.Privacy.Ratatouille (εAd9_le grind_le)

attribute [local irreducible] com UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [Inhabited R] [CipherRow R]

/-! ## The game -/

section Game

variable {n : ℕ}

/-- **The colluding adversary of the interleaved game with a table-reading scheduler and a free
challenge**: each step an oracle computation over the four challenge slices and the shared tables;
the challenge starts at the first step at which `go` holds (at most `L₁` steps), the answers are
taken at the first step at which `done` holds (at most `L₂` steps after the issuance requests), and
at most `L₃` steps follow the outcome. -/
structure AdversaryILMO (R : Type) where
  L₁ : ℕ
  L₂ : ℕ
  L₃ : ℕ
  next : List EvM → OracleComp (TSpec (Bool × Bool) R (preLen pI)) ActM
  go : List EvM → Bool
  done : List EvM → Bool
  ctxIss : List EvM → Coins ctxBytes
  ctxRed : List EvM → Coins ctxBytes
  pk : List EvM → Bool → UOVKey
  respond : List EvM → Bool → Coins uovN
  choose : List EvM → Bool → AnchorSet × Bytes
  guess : List EvM → Slices → ShM R → Prop

/-- **The scheduler's budget**: every step queries each slice at most `a₃` times, `H₂³` `a₂`
times, `H₅` `a₅` times and the cipher `a_E` times. -/
def AdversaryILMO.SBudget (A : AdversaryILMO R) (a3 a2 a5 aE : ℕ) : Prop :=
  ∀ tr, QBudget (A.next tr) a3 a2 a5 aE

/-- **The guess's budget**: each challenge slice at `q3` keys, `H₅` at `q5`, the cipher at `qE`;
`H₂³` freely. -/
structure AdversaryILMO.Budget (A : AdversaryILMO R) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ T (g₁ gL gR : Tab3) s, Rd3 (fun g => A.guess T ((g, g₁), (gL, gR)) s) q3
  h31 : ∀ T (g₀ gL gR : Tab3) s, Rd3 (fun g => A.guess T ((g₀, g), (gL, gR)) s) q3
  h3L : ∀ T (g₀ g₁ gR : Tab3) s, Rd3 (fun g => A.guess T ((g₀, g₁), (g, gR)) s) q3
  h3R : ∀ T (g₀ g₁ gL : Tab3) s, Rd3 (fun g => A.guess T ((g₀, g₁), (gL, g)) s) q3
  h5 : ∀ T sl, Rd5 (A.guess T sl) q5
  hE : ∀ T sl, RdE (A.guess T sl) qE

namespace AdversaryILMO

variable (A : AdversaryILMO R) (idx : AnchorSet → UOVKey → ℕ) (c : Fin n → XC)

/-- At most `L` steps of the schedule until `stop`, the scheduler reading the slices `sl` and the
tables `s`. -/
noncomputable def run (stop : List EvM → Bool) (L : ℕ) (tr : List EvM) (sl : Slices) (s : ShM R) :
    List EvM :=
  runO n (outM idx c) A.next stop L tr (TKey.read (m := preLen pI) (sl4 sl) s) ((default : Tab3), s)

/-- The steps before the challenge. -/
noncomputable def tr₁ (sl : Slices) (s : ShM R) : List EvM := A.run idx c A.go A.L₁ [] sl s

/-- The steps between the challenge issuance requests `q₀`, `q₁` and the answers. -/
noncomputable def tr₂ (T₁ : List EvM) (q₀ q₁ : Bytes) (sl : Slices) (s : ShM R) : List EvM :=
  A.run idx c A.done A.L₂ (T₁ ++ [.ext (.inl (q₀, q₁))]) sl s

/-- The steps after the challenge outcome `y`. -/
noncomputable def tr₃ (T₂ : List EvM) (y : Option (Except Error Bytes × Except Error Bytes))
    (sl : Slices) (s : ShM R) : List EvM :=
  A.run idx c (fun _ => false) A.L₃ (T₂ ++ [.ext (.inr y)]) sl s

/-- **The table-reading adversary at the key stage's transcript `T₁`.** -/
noncomputable def atT (T₁ : List EvM) : AdversaryRA R where
  ctxIss := A.ctxIss T₁
  ctxRed := A.ctxRed T₁
  pk := A.pk T₁
  respond q₀ q₁ i sl u := A.respond (A.tr₂ idx c T₁ q₀ q₁ sl u) i
  choose q₀ q₁ side sl u := A.choose (A.tr₂ idx c T₁ q₀ q₁ sl u) side
  guess q₀ q₁ y sl v := A.guess (A.tr₃ idx c (A.tr₂ idx c T₁ q₀ q₁ sl v) y sl v) sl v

/-- **The reduction**: the adversary with a table-reading key stage that runs the schedule. -/
noncomputable def red : AdversaryRAK R (List EvM) :=
  ⟨fun sl s => A.tr₁ idx c sl s, A.atT idx c⟩

/-- The challenge interaction at the transcripts `T₁` (keys) and `T₂` (answers). -/
def chalAdv (T₁ T₂ : List EvM) : Adversary :=
  ⟨A.ctxIss T₁, A.ctxRed T₁, A.pk T₁,
    fun _ _ c => bif c then A.respond T₂ true else A.respond T₂ false,
    fun _ _ side => bif side then A.choose T₂ true else A.choose T₂ false,
    fun _ _ _ => True⟩

end AdversaryILMO

/-- **The interleaved game** in world `b`: the schedule until the challenge, the challenge
contexts and keys from it, the issuance requests, the schedule until the answers, the outcome
(§6's rule), the schedule after it, and the guess; the scheduler reads the challenge slices and
the tables throughout. -/
noncomputable def realGameILMO (A : AdversaryILMO R) (idx : AnchorSet → UOVKey → ℕ) (b : Bool)
    (z : (PT × (Fin n → XC)) × ShM R) : Prop :=
  let T₁ := A.tr₁ idx z.1.2 (slOf z.1.1) z.2
  let q₀ := (issX (List.ofFn (A.ctxIss T₁)) (List.ofFn (A.ctxRed T₁)) z.1.1.1.1 z.2).2
  let q₁ := (issX (List.ofFn (A.ctxIss T₁)) (List.ofFn (A.ctxRed T₁)) z.1.1.1.2 z.2).2
  let T₂ := A.tr₂ idx z.1.2 T₁ q₀ q₁ (slOf z.1.1) z.2
  let y := outAt (A.chalAdv T₁ T₂) idx b z.1.1 z.2
  A.guess (A.tr₃ idx z.1.2 T₂ y (slOf z.1.1) z.2) (slOf z.1.1) z.2

/-- **The interleaved game is the key-stage game of the reduction**, tape by tape. -/
theorem realGameILMO_iff (A : AdversaryILMO R) (idx : AnchorSet → UOVKey → ℕ) (b : Bool) (x : PT)
    (c : Fin n → XC) (s : ShM R) :
    realGameILMO A idx b ((x, c), s) ↔ realGameRAK (A.red idx c) idx leanPI leanPR b (x, s) :=
  Iff.rfl

/-- **The adversary of `realGameILM` is a special case**: a scheduler that reads no table, starts
the challenge after exactly `L₁` steps and takes the answers after exactly `L₂`. -/
def AdversaryILM.toO (A : AdversaryILM R) : AdversaryILMO R where
  L₁ := A.L₁
  L₂ := A.L₂
  L₃ := A.L₃
  next tr := pure (A.next tr)
  go _ := false
  done _ := false
  ctxIss := A.ctxIss
  ctxRed := A.ctxRed
  pk := A.pk
  respond := A.respond
  choose := A.choose
  guess := A.guess

/-- Its scheduler reads nothing. -/
lemma AdversaryILM.toO_sBudget (A : AdversaryILM R) : A.toO.SBudget 0 0 0 0 :=
  fun _ => QBudget.pure _

/-- Its guess's budget is the earlier one. -/
lemma AdversaryILM.Budget.toO {A : AdversaryILM R} {q3 q5 qE : ℕ} (h : A.Budget q3 q5 qE) :
    A.toO.Budget q3 q5 qE := ⟨h.h30, h.h31, h.h3L, h.h3R, h.h5, h.hE⟩

/-- **`realGameILMO` extends `realGameILM`.** -/
theorem realGameILMO_toO (A : AdversaryILM R) (idx : AnchorSet → UOVKey → ℕ) (b : Bool)
    (z : (PT × (Fin n → XC)) × ShM R) : realGameILMO A.toO idx b z ↔ realGameILM A idx b z := by
  simp only [realGameILMO, realGameILM, AdversaryILMO.tr₁, AdversaryILMO.tr₂, AdversaryILMO.tr₃,
    AdversaryILMO.run, AdversaryILM.tr₁, AdversaryILM.tr₂, AdversaryILM.tr₃, AdversaryILM.run,
    AdversaryILMO.chalAdv, AdversaryILM.chalAdv, AdversaryILM.toO, runO_pure]

namespace AdversaryILMO

variable {A : AdversaryILMO R} (idx : AnchorSet → UOVKey → ℕ) (c : Fin n → XC)

/-- **A stretch of the schedule after a constant start is a consistent reader of each slice
position** (the others fixed) and the shared tables: `n` Clients and `L·a` scheduler queries. -/
lemma sreads_run {a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE) (j : Bool × Bool) (sl : Slices)
    (stop : List EvM → Bool) (L : ℕ) (tr : List EvM) :
    SReads pI (fun t : Tb R pI => A.run idx c stop L tr (ins4 j sl t.1) t.2) (L * a3)
      (n * (2 * nGrind) + L * a2) (n * 1248 + L * a5) (n * 9214 + L * aE) := by
  have hg := GoodO.run (fT := fun t : Tb R pI => TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2)
    (π := fun t : Tb R pI => ((default : Tab3), t.2)) (next := A.next) (sessReads_M idx c) stop L
    (GoodO.const (n := n) (Q := QM (R := R) idx c) tr)
  refine GoodO.sreads (j := j) (sessReads_M idx c)
    (fun t t' l hA k hk => by rw [read_ins4, read_ins4]; exact read_congr _ j t t' l hA k hk) hg
    (fun j k h t => ⟨(QM_card idx c j k h t).2.1, (QM_card idx c j k h t).2.2.1,
      (QM_card idx c j k h t).2.2.2⟩) fun t => ?_
  simpa only [List.nil_append] using countP_logO_qb (n := n) (out := outM idx c) hN j stop L tr _ _

/-- **Two stretches**: `L₁ + L₂` steps' scheduler queries. -/
lemma sreads_run₂ {a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE) (j : Bool × Bool) (sl : Slices)
    (stop₁ stop₂ : List EvM → Bool) (L₁ L₂ : ℕ) (tr : List EvM) (e : Option (Except Error Bytes × Except Error Bytes)) :
    SReads pI (fun t : Tb R pI => A.run idx c stop₂ L₂ (A.run idx c stop₁ L₁ tr (ins4 j sl t.1) t.2 ++ [.ext (.inr e)])
        (ins4 j sl t.1) t.2) ((L₁ + L₂) * a3)
      (n * (2 * nGrind) + (L₁ + L₂) * a2) (n * 1248 + (L₁ + L₂) * a5) (n * 9214 + (L₁ + L₂) * aE) := by
  have hg := GoodO.run (fT := fun t : Tb R pI => TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2)
    (π := fun t : Tb R pI => ((default : Tab3), t.2)) (next := A.next) (sessReads_M idx c) stop₂ L₂
    (GoodO.ext (GoodO.run (next := A.next) (sessReads_M idx c) stop₁ L₁
      (GoodO.const (n := n) (Q := QM (R := R) idx c) tr)) (.inr e))
  refine GoodO.sreads (j := j) (sessReads_M idx c)
    (fun t t' l hA k hk => by rw [read_ins4, read_ins4]; exact read_congr _ j t t' l hA k hk) hg
    (fun j k h t => ⟨(QM_card idx c j k h t).2.1, (QM_card idx c j k h t).2.2.1,
      (QM_card idx c j k h t).2.2.2⟩) fun t => ?_
  have h1 := countP_logO_qb (n := n) (out := outM idx c) hN j stop₁ L₁ tr
    (TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2) ((default : Tab3), t.2)
  have h2 := countP_logO_qb (n := n) (out := outM idx c) hN j stop₂ L₂
    (runO n (outM idx c) A.next stop₁ L₁ tr (TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2)
      ((default : Tab3), t.2) ++ [.ext (.inr e)])
    (TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2) ((default : Tab3), t.2)
  simp only [List.nil_append, List.countP_append, Nat.add_mul]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- A reader of slice position `j` with the others of `sl`, at the parameters of that position. -/
lemma sreads_at {X : Type} {f : Slices → ShM R → X} {a3 a2 a5 aE : ℕ}
    (h : ∀ j sl, SReads pI (fun t : Tb R pI => f (ins4 j sl t.1) t.2) a3 a2 a5 aE) :
    (∀ g₁ gL gR : Tab3, SReads pI (fun t : Tb R pI => f ((t.1, g₁), (gL, gR)) t.2) a3 a2 a5 aE) ∧
    (∀ g₀ gL gR : Tab3, SReads pI (fun t : Tb R pI => f ((g₀, t.1), (gL, gR)) t.2) a3 a2 a5 aE) ∧
    (∀ g₀ g₁ gR : Tab3, SReads pR (fun t : Tb R pR => f ((g₀, g₁), (t.1, gR)) t.2) a3 a2 a5 aE) ∧
    (∀ g₀ g₁ gL : Tab3, SReads pR (fun t : Tb R pR => f ((g₀, g₁), (gL, t.1)) t.2) a3 a2 a5 aE) :=
  ⟨fun g₁ gL gR => h (false, false) ((default, g₁), (gL, gR)),
    fun g₀ gL gR => h (false, true) ((g₀, default), (gL, gR)),
    fun g₀ g₁ gR => h (true, false) ((g₀, g₁), (default, gR)),
    fun g₀ g₁ gL => h (true, true) ((g₀, g₁), (gL, default))⟩

/-- **The reduction's key-stage budget**: the steps before the challenge. -/
theorem red_kBudget {a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE) :
    (A.red idx c).KBudget (A.L₁ * a3) (n * (2 * nGrind) + A.L₁ * a2) (n * 1248 + A.L₁ * a5)
      (n * 9214 + A.L₁ * aE) := by
  obtain ⟨h0, h1, hL, hR⟩ := sreads_at (f := fun sl s => A.tr₁ idx c sl s)
    fun j sl => sreads_run idx c hN j sl A.go A.L₁ []
  exact ⟨h0, h1, hL, hR⟩

/-- **The reduction's interaction budget**: at any key-stage transcript, the steps up to the
answers. -/
theorem red_iBudget {a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE) :
    (A.red idx c).IBudget (A.L₂ * a3) (n * (2 * nGrind) + A.L₂ * a2) (n * 1248 + A.L₂ * a5)
      (n * 9214 + A.L₂ * aE) := by
  intro T₁
  have h (q₀ q₁ : Bytes) := sreads_at (f := fun sl s => (A.atT idx c T₁).trans q₀ q₁ sl s)
    (a3 := A.L₂ * a3) (a2 := n * (2 * nGrind) + A.L₂ * a2) (a5 := n * 1248 + A.L₂ * a5)
    (aE := n * 9214 + A.L₂ * aE) fun j sl => by
      have := (sreads_run idx c hN j sl A.done A.L₂ (T₁ ++ [.ext (.inl (q₀, q₁))])).map
        fun T => ((A.respond T false, A.respond T true), (A.choose T false, A.choose T true))
      exact this
  exact ⟨fun q₀ q₁ => (h q₀ q₁).1, fun q₀ q₁ => (h q₀ q₁).2.1, fun q₀ q₁ => (h q₀ q₁).2.2.1,
    fun q₀ q₁ => (h q₀ q₁).2.2.2⟩

/-- **The reduction's guess budget**: the adversary's, plus the `n` Clients' and the scheduler's
reads after the key stage. -/
theorem red_gBudget {q3 q5 qE a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE)
    (hA : A.Budget q3 q5 qE) :
    (A.red idx c).GBudget ((A.L₂ + A.L₃) * a3 + q3) (n * 1248 + (A.L₂ + A.L₃) * a5 + q5)
      (n * 9214 + (A.L₂ + A.L₃) * aE + qE) := by
  intro T₁ tr
  have hG (q₀ q₁ : Bytes) (y : Option (Except Error Bytes × Except Error Bytes)) (j : Bool × Bool)
      (sl : Slices) := sreads_run₂ idx c hN j sl A.done (fun _ => false) A.L₂ A.L₃
    (T₁ ++ [.ext (.inl (q₀, q₁))]) y
  have hs (q₀ q₁ : Bytes) (y : Option (Except Error Bytes × Except Error Bytes)) :=
    sreads_at (f := fun sl s => A.tr₃ idx c (A.tr₂ idx c T₁ q₀ q₁ sl s) y sl s) (hG q₀ q₁ y)
  exact
    { h30 := fun q₀ q₁ y g₁ gL gR s => Rd3.bindEq (fun _ => rfl) (((hs q₀ q₁ y).1 g₁ gL gR).rd3 s)
        fun T => hA.h30 T g₁ gL gR s
      h31 := fun q₀ q₁ y g₀ gL gR s => Rd3.bindEq (fun _ => rfl) (((hs q₀ q₁ y).2.1 g₀ gL gR).rd3 s)
        fun T => hA.h31 T g₀ gL gR s
      h3L := fun q₀ q₁ y g₀ g₁ gR s => Rd3.bindEq (fun _ => rfl)
        (((hs q₀ q₁ y).2.2.1 g₀ g₁ gR).rd3 s) fun T => hA.h3L T g₀ g₁ gR s
      h3R := fun q₀ q₁ y g₀ g₁ gL s => Rd3.bindEq (fun _ => rfl)
        (((hs q₀ q₁ y).2.2.2 g₀ g₁ gL).rd3 s) fun T => hA.h3R T g₀ g₁ gL s
      h5 := fun q₀ q₁ y sl => Rd5.bindEq (m := fun s => A.tr₃ idx c (A.tr₂ idx c T₁ q₀ q₁ sl s) y sl s)
        (f := fun T s => A.guess T sl s) (fun _ => rfl)
        (((hs q₀ q₁ y).1 sl.1.2 sl.2.1 sl.2.2).rd5 sl.1.1) fun T => hA.h5 T sl
      hE := fun q₀ q₁ y sl => RdE.bindEq (m := fun s => A.tr₃ idx c (A.tr₂ idx c T₁ q₀ q₁ sl s) y sl s)
        (f := fun T s => A.guess T sl s) (fun _ => rfl)
        (((hs q₀ q₁ y).1 sl.1.2 sl.2.1 sl.2.2).rdE sl.1.1) fun T => hA.hE T sl }

end AdversaryILMO

end Game

/-! ## The bound -/

section Bound

variable {n : ℕ}

/-- **Theorem 4(a) with interleaved further sessions, a table-reading scheduler and a free
challenge, for every type of cipher rows**: `anonymityRAK_lean_numG` at the key-stage budget
`(L₁a₃, 2·2³²n + L₁a₂, 1248n + L₁a₅, 9214n + L₁a_E)`, the interaction budget (the same with `L₂`)
and the guess budget `((L₂+L₃)a₃ + q₃, 1248n + (L₂+L₃)a₅ + q₅, 9214n + (L₂+L₃)a_E + q_E)`. -/
theorem anonymityILO_lean_numG [ZKRow R] [ZKPRow R] (A : AdversaryILMO R) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE a3 a2 a5 aE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE)
    (hhide : ∀ (c : Fin n → XC) b cc,
      hidingAdv (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)).ctxRO.base.ci
        (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide) :
    |pr ((PT × (Fin n → XC)) × ShM R) (realGameILMO A idx false) -
        pr ((PT × (Fin n → XC)) × ShM R) (realGameILMO A idx true)| ≤
      4 * εAdG R pI 9 (A.L₂ * a3 + ((A.L₂ + A.L₃) * a3 + q3))
          (n * 1248 + (A.L₂ + A.L₃) * a5 + q5 + (n * 1248 + A.L₂ * a5) + 1872)
          (n * 9214 + (A.L₂ + A.L₃) * aE + qE + (n * 9214 + A.L₂ * aE) + 13821)
          (A.L₁ * a3) (n * (2 * nGrind) + A.L₁ * a2) (n * 1248 + A.L₁ * a5) (n * 9214 + A.L₁ * aE) +
        4 * εAdG R pR 9 ((A.L₂ + A.L₃) * a3 + q3) (n * 1248 + (A.L₂ + A.L₃) * a5 + q5 + 1248)
          (n * 9214 + (A.L₂ + A.L₃) * aE + qE + 13821) (A.L₁ * a3 + A.L₂ * a3)
          (n * (2 * nGrind) + A.L₁ * a2 + (n * (2 * nGrind) + A.L₂ * a2))
          (n * 1248 + A.L₁ * a5 + (n * 1248 + A.L₂ * a5) + 624)
          (n * 9214 + A.L₁ * aE + (n * 9214 + A.L₂ * aE) + 9214) +
        4 * (((A.L₁ * a3 + A.L₂ * a3 : ℕ) : ℝ) / 2 ^ 128 + 1 / 2 ^ 113 +
          ZKPRow.εP R pR 0 312 4607 (n * 1248 + A.L₁ * a5 + (n * 1248 + A.L₂ * a5) + 624)
            (n * 9214 + A.L₁ * aE + (n * 9214 + A.L₂ * aE) + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  rw [← pr_equiv tapeILM, ← pr_equiv tapeILM]
  exact abs_pr_prod_sub_le _ _ fun c =>
    anonymityRAK_lean_numG (A.red idx c) idx (AdversaryILMO.red_gBudget idx c hN hA)
      (AdversaryILMO.red_iBudget idx c hN) (AdversaryILMO.red_kBudget idx c hN) (hhide c)

/-- **`anonymityILO_lean_numG` with function rows.** -/
theorem anonymityILO_lean_num (A : AdversaryILMO (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE a3 a2 a5 aE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE)
    (hhide : ∀ (c : Fin n → XC) b cc,
      hidingAdv (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)).ctxRO.base.ci
        (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide) :
    |pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILMO A idx false) -
        pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILMO A idx true)| ≤
      4 * εAd 9 (A.L₂ * a3 + ((A.L₂ + A.L₃) * a3 + q3))
          (n * 1248 + (A.L₂ + A.L₃) * a5 + q5 + (n * 1248 + A.L₂ * a5) + 1872)
          (n * 9214 + (A.L₂ + A.L₃) * aE + qE + (n * 9214 + A.L₂ * aE) + 13821)
          (A.L₁ * a3) (n * (2 * nGrind) + A.L₁ * a2) (n * 1248 + A.L₁ * a5) (n * 9214 + A.L₁ * aE) +
        4 * εAd 9 ((A.L₂ + A.L₃) * a3 + q3) (n * 1248 + (A.L₂ + A.L₃) * a5 + q5 + 1248)
          (n * 9214 + (A.L₂ + A.L₃) * aE + qE + 13821) (A.L₁ * a3 + A.L₂ * a3)
          (n * (2 * nGrind) + A.L₁ * a2 + (n * (2 * nGrind) + A.L₂ * a2))
          (n * 1248 + A.L₁ * a5 + (n * 1248 + A.L₂ * a5) + 624)
          (n * 9214 + A.L₁ * aE + (n * 9214 + A.L₂ * aE) + 9214) +
        4 * (((A.L₁ * a3 + A.L₂ * a3 : ℕ) : ℝ) / 2 ^ 128 + 1 / 2 ^ 113 +
          εROP 0 312 4607 (n * 1248 + A.L₁ * a5 + (n * 1248 + A.L₂ * a5) + 624)
            (n * 9214 + A.L₁ * aE + (n * 9214 + A.L₂ * aE) + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityILO_lean_numG A idx hA hN hhide

/-- **`anonymityILO_lean_numG` with AES as uniformly random permutations.** -/
theorem anonymityILO_lean_num_perm (A : AdversaryILMO (Equiv.Perm Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE a3 a2 a5 aE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE)
    (hhide : ∀ (c : Fin n → XC) b cc,
      hidingAdv (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)).ctxRO.base.ci
        (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide) :
    |pr ((PT × (Fin n → XC)) × ShM (Equiv.Perm Blk)) (realGameILMO A idx false) -
        pr ((PT × (Fin n → XC)) × ShM (Equiv.Perm Blk)) (realGameILMO A idx true)| ≤
      4 * εAdPm pI 9 (A.L₂ * a3 + ((A.L₂ + A.L₃) * a3 + q3))
          (n * 1248 + (A.L₂ + A.L₃) * a5 + q5 + (n * 1248 + A.L₂ * a5) + 1872)
          (n * 9214 + (A.L₂ + A.L₃) * aE + qE + (n * 9214 + A.L₂ * aE) + 13821)
          (A.L₁ * a3) (n * (2 * nGrind) + A.L₁ * a2) (n * 1248 + A.L₁ * a5) (n * 9214 + A.L₁ * aE) +
        4 * εAdPm pR 9 ((A.L₂ + A.L₃) * a3 + q3) (n * 1248 + (A.L₂ + A.L₃) * a5 + q5 + 1248)
          (n * 9214 + (A.L₂ + A.L₃) * aE + qE + 13821) (A.L₁ * a3 + A.L₂ * a3)
          (n * (2 * nGrind) + A.L₁ * a2 + (n * (2 * nGrind) + A.L₂ * a2))
          (n * 1248 + A.L₁ * a5 + (n * 1248 + A.L₂ * a5) + 624)
          (n * 9214 + A.L₁ * aE + (n * 9214 + A.L₂ * aE) + 9214) +
        4 * (((A.L₁ * a3 + A.L₂ * a3 : ℕ) : ℝ) / 2 ^ 128 + 1 / 2 ^ 113 +
          εROPmP pR 0 312 4607 (n * 1248 + A.L₁ * a5 + (n * 1248 + A.L₂ * a5) + 624)
            (n * 9214 + A.L₁ * aE + (n * 9214 + A.L₂ * aE) + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityILO_lean_numG A idx hA hN hhide

/-- A count of `H₂³` keys of at most `M` blocks of `4·2³²` and `s` more costs at most
`(M + s)·2⁻¹²⁸` at the `2⁻¹⁰²⁴` rate. -/
private lemma grind_le_add (x M s : ℕ) (h : x ≤ M * (4 * nGrind) + s) :
    (x : ℝ) / 2 ^ 1024 ≤ M / 2 ^ 128 + s / 2 ^ 128 := by
  have h1 := grind_le (M * (4 * nGrind)) M le_rfl
  have h2 : (s : ℝ) / 2 ^ 1024 ≤ s / 2 ^ 128 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have h3 : (x : ℝ) / 2 ^ 1024 ≤ ((M * (4 * nGrind) : ℕ) : ℝ) / 2 ^ 1024 + s / 2 ^ 1024 := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)
  exact h3.trans (add_le_add h1 h2)

/-- **The bound in numbers**: with `n` further Clients and a scheduler within `(a₃, a₂, a₅, a_E)`
per step for `L = L₁ + L₂ + L₃` steps,

    |Pr[W₀] − Pr[W₁]| ≤ (n + 2)·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸
                         + 28·L·(a₃ + a₂ + a₅ + 221·a_E)·2⁻¹²⁸ + 2·εhide. -/
theorem anonymityILO_lean_le (A : AdversaryILMO (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE a3 a2 a5 aE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE)
    (hhide : ∀ (c : Fin n → XC) b cc,
      hidingAdv (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)).ctxRO.base.ci
        (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide) :
    |pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILMO A idx false) -
        pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILMO A idx true)| ≤
      (n + 2 : ℕ) / 2 ^ 101 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 +
        28 * ((A.L₁ + A.L₂ + A.L₃) * (a3 + a2 + a5 + 221 * aE) : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := anonymityILO_lean_num A idx hA hN hhide
  have u1 := εAd9_le (A.L₂ * a3 + ((A.L₂ + A.L₃) * a3 + q3))
    (n * 1248 + (A.L₂ + A.L₃) * a5 + q5 + (n * 1248 + A.L₂ * a5) + 1872)
    (n * 9214 + (A.L₂ + A.L₃) * aE + qE + (n * 9214 + A.L₂ * aE) + 13821)
    (A.L₁ * a3) (n * (2 * nGrind) + A.L₁ * a2) (n * 1248 + A.L₁ * a5) (n * 9214 + A.L₁ * aE)
  have u2 := εAd9_le ((A.L₂ + A.L₃) * a3 + q3) (n * 1248 + (A.L₂ + A.L₃) * a5 + q5 + 1248)
    (n * 9214 + (A.L₂ + A.L₃) * aE + qE + 13821) (A.L₁ * a3 + A.L₂ * a3)
    (n * (2 * nGrind) + A.L₁ * a2 + (n * (2 * nGrind) + A.L₂ * a2))
    (n * 1248 + A.L₁ * a5 + (n * 1248 + A.L₂ * a5) + 624)
    (n * 9214 + A.L₁ * aE + (n * 9214 + A.L₂ * aE) + 9214)
  have g1 := grind_le_add (n * (2 * nGrind) + A.L₁ * a2) n (A.L₁ * a2)
    (by have : n * (2 * nGrind) ≤ n * (4 * nGrind) := Nat.mul_le_mul_left _ (by omega); omega)
  have g2 := grind_le_add (n * (2 * nGrind) + A.L₁ * a2 + (n * (2 * nGrind) + A.L₂ * a2)) n
    (A.L₁ * a2 + A.L₂ * a2) (by
      have : n * (2 * nGrind) + n * (2 * nGrind) = n * (4 * nGrind) := by ring
      omega)
  have hn := noHitProb_le_128
  have hn0 : 0 ≤ noHitProb := pr_nonneg _
  have h1 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hK : (12 : ℝ) / 2 ^ 1024 ≤ 1 / 2 ^ 128 := by
    have e1024 : (2 : ℝ) ^ 1024 = 2 ^ 128 * 2 ^ 896 := by rw [← pow_add]
    have hb : (2 : ℝ) ^ 32 ≤ 2 ^ 896 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hp : (0 : ℝ) < 2 ^ 128 := by positivity
    rw [e1024, div_le_div_iff₀ (by positivity) (by positivity)]
    have h16 : (12 : ℝ) ≤ 2 ^ 32 := by norm_num
    calc (12 : ℝ) * 2 ^ 128 ≤ 2 ^ 896 * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right (h16.trans hb) hp.le
      _ = 1 * (2 ^ 128 * 2 ^ 896) := by rw [one_mul, mul_comm]
  have eS : (A.L₁ + A.L₂ + A.L₃) * (a3 + a2 + a5 + 221 * aE) = (A.L₁ + A.L₂ + A.L₃) * a3 +
      (A.L₁ + A.L₂ + A.L₃) * a2 + (A.L₁ + A.L₂ + A.L₃) * a5 + 221 * ((A.L₁ + A.L₂ + A.L₃) * aE) := by
    ring
  have f3 : A.L₁ * a3 + A.L₂ * a3 ≤ (A.L₁ + A.L₂ + A.L₃) * a3 := by nlinarith
  have f2 : A.L₁ * a2 + A.L₂ * a2 ≤ (A.L₁ + A.L₂ + A.L₃) * a2 := by nlinarith
  have f5 : A.L₁ * a5 + A.L₂ * a5 ≤ (A.L₁ + A.L₂ + A.L₃) * a5 := by nlinarith
  have fE : A.L₁ * aE + A.L₂ * aE ≤ (A.L₁ + A.L₂ + A.L₃) * aE := by nlinarith
  have f3' : (A.L₂ + A.L₃) * a3 ≤ (A.L₁ + A.L₂ + A.L₃) * a3 := Nat.mul_le_mul_right _ (by omega)
  have f5' : (A.L₂ + A.L₃) * a5 ≤ (A.L₁ + A.L₂ + A.L₃) * a5 := Nat.mul_le_mul_right _ (by omega)
  have fE' : (A.L₂ + A.L₃) * aE ≤ (A.L₁ + A.L₂ + A.L₃) * aE := Nat.mul_le_mul_right _ (by omega)
  rw [eS]
  generalize A.L₁ * a3 = k3 at h u1 u2 f3
  generalize A.L₂ * a3 = i3 at h u1 u2 f3
  generalize (A.L₂ + A.L₃) * a3 = j3 at h u1 u2 f3'
  generalize (A.L₁ + A.L₂ + A.L₃) * a3 = S3 at f3 f3' ⊢
  generalize A.L₁ * a2 = k2 at h u1 u2 f2 g1 g2
  generalize A.L₂ * a2 = i2 at h u1 u2 f2 g1 g2
  generalize (A.L₁ + A.L₂ + A.L₃) * a2 = S2 at f2 ⊢
  generalize A.L₁ * a5 = k5 at h u1 u2 f5
  generalize A.L₂ * a5 = i5 at h u1 u2 f5
  generalize (A.L₂ + A.L₃) * a5 = j5 at h u1 u2 f5'
  generalize (A.L₁ + A.L₂ + A.L₃) * a5 = S5 at f5 f5' ⊢
  generalize A.L₁ * aE = kE at h u1 u2 fE
  generalize A.L₂ * aE = iE at h u1 u2 fE
  generalize (A.L₂ + A.L₃) * aE = jE at h u1 u2 fE'
  generalize (A.L₁ + A.L₂ + A.L₃) * aE = SE at fE fE' ⊢
  have r3 : (k3 : ℝ) + i3 ≤ S3 := by exact_mod_cast f3
  have r2 : (k2 : ℝ) + i2 ≤ S2 := by exact_mod_cast f2
  have r5 : (k5 : ℝ) + i5 ≤ S5 := by exact_mod_cast f5
  have rE : (kE : ℝ) + iE ≤ SE := by exact_mod_cast fE
  have r3' : (j3 : ℝ) ≤ S3 := by exact_mod_cast f3'
  have r5' : (j5 : ℝ) ≤ S5 := by exact_mod_cast f5'
  have rE' : (jE : ℝ) ≤ SE := by exact_mod_cast fE'
  have p3 : (0 : ℝ) ≤ k3 := Nat.cast_nonneg _
  have p3' : (0 : ℝ) ≤ i3 := Nat.cast_nonneg _
  have p2 : (0 : ℝ) ≤ k2 := Nat.cast_nonneg _
  have p2' : (0 : ℝ) ≤ i2 := Nat.cast_nonneg _
  have p5 : (0 : ℝ) ≤ k5 := Nat.cast_nonneg _
  have p5' : (0 : ℝ) ≤ i5 := Nat.cast_nonneg _
  have pE : (0 : ℝ) ≤ kE := Nat.cast_nonneg _
  have pE' : (0 : ℝ) ≤ iE := Nat.cast_nonneg _
  generalize (2 : ℝ) ^ 1024 = κ at hK g1 g2 u1 u2 h
  unfold εROP εRO at h u1 u2
  push_cast at h u1 u2 g1 g2 ⊢
  have e : ∀ x : ℝ, x / 2 ^ 101 = x * 134217728 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  rw [e]
  linarith

/-- **`2²⁰` Clients**: `≤ 2⁻⁸¹ + 2·εhide` plus the guess's and the scheduler's budget terms. -/
theorem anonymityILO_lean_2pow20 (A : AdversaryILMO (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE a3 a2 a5 aE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE)
    (hhide : ∀ (c : Fin n → XC) b cc,
      hidingAdv (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)).ctxRO.base.ci
        (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide)
    (hn : n + 2 ≤ 2 ^ 20) :
    |pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILMO A idx false) -
        pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILMO A idx true)| ≤
      1 / 2 ^ 81 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 +
        28 * ((A.L₁ + A.L₂ + A.L₃) * (a3 + a2 + a5 + 221 * aE) : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := anonymityILO_lean_le A idx hA hN hhide
  have : ((n + 2 : ℕ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hn
  have h2 : ((n + 2 : ℕ) : ℝ) / 2 ^ 101 ≤ 1 / 2 ^ 81 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **`2³²` Clients**: `≤ 2⁻⁶⁹ + 2·εhide` plus the guess's and the scheduler's budget terms. -/
theorem anonymityILO_lean_2pow32 (A : AdversaryILMO (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE a3 a2 a5 aE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE)
    (hhide : ∀ (c : Fin n → XC) b cc,
      hidingAdv (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)).ctxRO.base.ci
        (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atT idx c (A.tr₁ idx c cc.2.1 cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide)
    (hn : n + 2 ≤ 2 ^ 32) :
    |pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILMO A idx false) -
        pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILMO A idx true)| ≤
      1 / 2 ^ 69 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 +
        28 * ((A.L₁ + A.L₂ + A.L₃) * (a3 + a2 + a5 + 221 * aE) : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := anonymityILO_lean_le A idx hA hN hhide
  have : ((n + 2 : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have h2 : ((n + 2 : ℕ) : ℝ) / 2 ^ 101 ≤ 1 / 2 ^ 69 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end Bound

end VoleMole.Privacy.Moussaka
