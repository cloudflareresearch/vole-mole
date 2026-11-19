import VoleMole.Privacy.RatatouilleInterleave
import VoleMole.ZK.ReadsInterleaveOC

/-!
# Ratatouille with interleaved sessions, a table-reading scheduler and a free challenge

`Privacy/RatatouilleInterleave.lean` (further Clients spending up to `K` times along their change
tokens) with the two generalizations of `Privacy/PomFRITInterleaveOC.lean`:

* **the scheduler reads the tables**: each step is a VCVio oracle computation over the four
  challenge `H₃` slices and the shared tables, within a per-step query bound
  (`AdversaryILRO.SBudget a₃ a₂ a₅ a_E`);
* **the challenge is placed by the scheduler**: it starts at the first step at which `go` holds
  (at most `L₁` steps); stage 1 (both issuance responses and `d₁`) is read off the transcript at the
  first step at which `done₁` holds (at most `L₂` steps after the issuance requests); if round 1
  runs, stage 2 (`respond₁`, `d₂`) at the first step at which `done₂` holds (at most `L₃` steps after
  round 1's request); at most `L₄` steps follow the outcome.

The challenge's requests of a stage are revealed together and each stage's answers take effect
together; as for PomFRIT, neither restricts the Issuer (a request revealed earlier gives more, and
an answer has no visible effect before the next challenge event, which needs all of the stage's
answers).

## The reduction

For each tape `c` the game is the key-stage game of `A.red c` (`realGameILRO`, as
`realGameILR`), its key stage the steps before the challenge, stage 1 the steps up to it, stage 2
also round 1's, the guess also those after the outcome, each on the slices and the tables.
Budgets (`GoodO.sreads`, per slice position): key stage `(L₁a₃, (K+1)n·2³² + L₁a₂,
(K+1)n·624 + L₁a₅, (K+1)n·4607 + L₁a_E)` (`red_kBudget`), both stages the same with `L₂ + L₃`
(`red_iBudget`), guess `((L₂+L₃+L₄)a₃ + q₃, (K+1)n·624 + (L₂+L₃+L₄)a₅ + q₅, …)` (`red_gBudget`).

## The bound

`unlinkabilityRAK_lean_numG` for every `c`, averaged: `unlinkabilityILO_lean_numG`, `_num`,
`_num_perm`; in numbers (`unlinkabilityILO_lean_le`)

    ≤ (n(K+1) + 2)·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 46·L·(a₃ + a₂ + a₅ + 221·a_E)·2⁻¹²⁸
      + 2·εhide

with `L = L₁ + L₂ + L₃ + L₄`: `2⁻⁸¹` (`2⁻⁶⁹`) at `n(K+1) + 2 ≤ 2²⁰` (`2³²`) plus the budget terms
(`unlinkabilityILO_lean_2pow20`, `_2pow32`).
-/

open Finset OracleComp OracleSpec

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM.Reads (TKey TSpec QBudget sl4 ins4 read_ins4 readAt read_congr)

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-- The proof sizes of the Lean provers. -/
local notation "ZL" => Sizes.labelRows

/-! ## The game -/

section Game

variable {n K : ℕ}

/-- **The malicious Issuer of the interleaved game with a table-reading scheduler and a free
challenge**: each step an oracle computation over the four challenge slices and the shared tables;
the challenge starts at the first step at which `go` holds (at most `L₁` steps), stage 1 is taken at
the first step at which `done₁` holds (at most `L₂` steps after the issuance requests), stage 2 at the
first at which `done₂` holds (at most `L₃` steps after round 1's request, if round 1 runs), and at
most `L₄` steps follow the outcome. -/
structure AdversaryILRO (R : Type) where
  L₁ : ℕ
  L₂ : ℕ
  L₃ : ℕ
  L₄ : ℕ
  next : List EvR → OracleComp (TSpec (Bool × Bool) R (preLen pI)) ActR
  go : List EvR → Bool
  done₁ : List EvR → Bool
  done₂ : List EvR → Bool
  pk : List EvR → PublicKey
  ctx : List EvR → Context
  tInit : List EvR → Credits
  respondIss : List EvR → Bool → Preimage
  d₁ : List EvR → Credits
  respond₁ : List EvR → SpendResponse
  d₂ : List EvR → Credits
  guess : List EvR → SlicesR → ShR R → Prop

/-- **The scheduler's budget**: every step queries each slice at most `a₃` times, `H₂³` `a₂`
times, `H₅` `a₅` times and the cipher `a_E` times. -/
def AdversaryILRO.SBudget (A : AdversaryILRO R) (a3 a2 a5 aE : ℕ) : Prop :=
  ∀ tr, QBudget (A.next tr) a3 a2 a5 aE

/-- **The guess's budget**: each challenge slice at `q3` keys, `H₅` at `q5`, the cipher at `qE`;
`H₂³` freely. -/
structure AdversaryILRO.Budget (A : AdversaryILRO R) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ T (g₁ g₂ g₃ : Tab3) s, Rd3 (fun g => A.guess T ((g, g₁), (g₂, g₃)) s) q3
  h31 : ∀ T (g₀ g₂ g₃ : Tab3) s, Rd3 (fun g => A.guess T ((g₀, g), (g₂, g₃)) s) q3
  h32 : ∀ T (g₀ g₁ g₃ : Tab3) s, Rd3 (fun g => A.guess T ((g₀, g₁), (g, g₃)) s) q3
  h33 : ∀ T (g₀ g₁ g₂ : Tab3) s, Rd3 (fun g => A.guess T ((g₀, g₁), (g₂, g)) s) q3
  h5 : ∀ T sl, Rd5 (A.guess T sl) q5
  hE : ∀ T sl, RdE (A.guess T sl) qE

namespace AdversaryILRO

variable (A : AdversaryILRO R) (c : Fin n → XK K)

/-- At most `L` steps of the schedule until `stop`, the scheduler reading the slices `sl` and the
tables `s`. -/
noncomputable def run (stop : List EvR → Bool) (L : ℕ) (tr : List EvR) (sl : SlicesR) (s : ShR R) :
    List EvR :=
  runO n (outR c) A.next stop L tr (TKey.read (m := preLen pI) (sl4 sl) s) ((default : Tab3), s)

/-- The steps before the challenge. -/
noncomputable def tr₁ (sl : SlicesR) (s : ShR R) : List EvR := A.run c A.go A.L₁ [] sl s

/-- The steps between the challenge issuance requests `tr` and stage 1. -/
noncomputable def tr₂ (T₁ : List EvR) (tr : IssTr ZL) (sl : SlicesR) (s : ShR R) : List EvR :=
  A.run c A.done₁ A.L₂ (T₁ ++ [.ext (.inl tr)]) sl s

/-- The steps between round 1's request `rq` and stage 2. -/
noncomputable def tr₃ (T₂ : List EvR) (rq : SReq) (sl : SlicesR) (s : ShR R) : List EvR :=
  A.run c A.done₂ A.L₃ (T₂ ++ [.ext (.inr (.inl rq))]) sl s

/-- The transcript before the outcome, as the guess sees it. -/
noncomputable def tr₃G (T₂ : List EvR) (y : Rounds ZL) (sl : SlicesR) (s : ShR R) : List EvR :=
  (y.map Prod.fst).elim T₂ fun rq => A.tr₃ c T₂ rq sl s

/-- The steps after the challenge outcome `y`. -/
noncomputable def tr₄ (T₃ : List EvR) (y : Rounds ZL) (sl : SlicesR) (s : ShR R) : List EvR :=
  A.run c (fun _ => false) A.L₄ (T₃ ++ [.ext (.inr (.inr y))]) sl s

/-- **The table-reading Issuer at the key stage's transcript `T₁`.** -/
noncomputable def atT (T₁ : List EvR) : AdversaryRA R ZL where
  pk := A.pk T₁
  ctx := A.ctx T₁
  tInit := A.tInit T₁
  respondIss tr i sl u := A.respondIss (A.tr₂ c T₁ tr sl u) i
  d₁ tr sl u := A.d₁ (A.tr₂ c T₁ tr sl u)
  respond₁ tr rq sl u := A.respond₁ (A.tr₃ c (A.tr₂ c T₁ tr sl u) rq sl u)
  d₂ tr rq sl u := A.d₂ (A.tr₃ c (A.tr₂ c T₁ tr sl u) rq sl u)
  guess tr y sl v := A.guess (A.tr₄ c (A.tr₃G c (A.tr₂ c T₁ tr sl v) y sl v) y sl v) sl v

/-- **The reduction**: the Issuer with a table-reading key stage that runs the schedule. -/
noncomputable def red : AdversaryRAK R ZL (List EvR) :=
  ⟨fun sl s => A.tr₁ c sl s, A.atT c⟩

end AdversaryILRO

/-- **The interleaved game** in world `(b₁, b₂)`: the key-stage game (`realGameRAK`) of the Issuer
that runs the schedule with the further Clients' tapes `z.1.2`, the scheduler reading the slices
and the tables throughout. -/
noncomputable def realGameILRO (A : AdversaryILRO R) (b₁ b₂ : Bool)
    (z : (((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR R) : Prop :=
  realGameRAK (A.red z.1.2) leanPIR leanPSR b₁ b₂ (z.1.1, z.2)

/-- **The interleaved game at a tape** is `realGameRA` of the Issuer at the key stage's
transcript. -/
theorem realGameILRO_iff (A : AdversaryILRO R) (b₁ b₂ : Bool) (x : (TRe × TRe) × (TRe × TRe))
    (c : Fin n → XK K) (s : ShR R) :
    realGameILRO A b₁ b₂ ((x, c), s) ↔
      realGameRA (A.atT c (A.tr₁ c (slRK x) s)) leanPIR leanPSR b₁ b₂ (x, s) :=
  Iff.rfl

/-- **The Issuer of `realGameILR` is a special case**: a scheduler that reads no table, starts the
challenge after exactly `L₁` steps and takes each stage after exactly `L₂`, `L₃` steps. -/
def AdversaryILR.toO (A : AdversaryILR R) : AdversaryILRO R where
  L₁ := A.L₁
  L₂ := A.L₂
  L₃ := A.L₃
  L₄ := A.L₄
  next tr := pure (A.next tr)
  go _ := false
  done₁ _ := false
  done₂ _ := false
  pk := A.pk
  ctx := A.ctx
  tInit := A.tInit
  respondIss := A.respondIss
  d₁ := A.d₁
  respond₁ := A.respond₁
  d₂ := A.d₂
  guess := A.guess

/-- Its scheduler reads nothing. -/
lemma AdversaryILR.toO_sBudget (A : AdversaryILR R) : A.toO.SBudget 0 0 0 0 :=
  fun _ => QBudget.pure _

/-- Its guess's budget is the earlier one. -/
lemma AdversaryILR.Budget.toO {A : AdversaryILR R} {q3 q5 qE : ℕ} (h : A.Budget q3 q5 qE) :
    A.toO.Budget q3 q5 qE := ⟨h.h30, h.h31, h.h32, h.h33, h.h5, h.hE⟩

lemma AdversaryILR.toO_atT (A : AdversaryILR R) (c : Fin n → XK K) (T₁ : List EvR) :
    A.toO.atT c T₁ = A.atT c T₁ := by
  have r : ∀ L tr (sl : SlicesR) (s : ShR R), A.toO.run c (fun _ => false) L tr sl s = A.run c L tr s :=
    fun L tr sl s => runO_pure _ _ _ _ _ L tr
  unfold AdversaryILRO.atT AdversaryILR.atT
  simp only [AdversaryILRO.tr₂, AdversaryILRO.tr₃, AdversaryILRO.tr₃G, AdversaryILRO.tr₄,
    AdversaryILR.tr₂, AdversaryILR.tr₃, AdversaryILR.tr₃G, AdversaryILR.tr₄]
  have h1 : A.toO.done₁ = fun _ => false := rfl
  have h2 : A.toO.done₂ = fun _ => false := rfl
  have h3 : A.toO.L₂ = A.L₂ := rfl
  have h4 : A.toO.L₃ = A.L₃ := rfl
  have h5 : A.toO.L₄ = A.L₄ := rfl
  simp only [h1, h2, h3, h4, h5, r]
  rfl

/-- **`realGameILRO` extends `realGameILR`.** -/
theorem realGameILRO_toO (A : AdversaryILR R) (b₁ b₂ : Bool)
    (z : (((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR R) :
    realGameILRO A.toO b₁ b₂ z ↔ realGameILR A b₁ b₂ z := by
  have e : (A.toO.red z.1.2 : AdversaryRAK R ZL (List EvR)) = A.red z.1.2 := by
    have r : ∀ (sl : SlicesR) (s : ShR R), A.toO.tr₁ z.1.2 sl s = A.tr₁ z.1.2 s :=
      fun sl s => runO_pure _ _ _ _ _ _ _
    simp only [AdversaryILRO.red, AdversaryILR.red, r, show A.toO.atT z.1.2 = A.atT z.1.2 from
      funext (A.toO_atT z.1.2)]
  simp only [realGameILRO, realGameILR, e]

namespace AdversaryILRO

variable {A : AdversaryILRO R} (c : Fin n → XK K)

lemma sreads_gen {a3 a2 a5 aE : ℕ} (j : Bool × Bool) (sl : SlicesR)
    {F : Tb R pI → List EvR} {G : Tb R pI → List (TKey (Bool × Bool) (preLen pI))}
    (hF : GoodO (spec := TSpec (Bool × Bool) R (preLen pI)) n (QR (R := R) c)
      (fun t : Tb R pI => TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2)
      (fun t : Tb R pI => ((default : Tab3), t.2)) F G) {L : ℕ}
    (hG : ∀ t, (G t).countP (TKey.isH3 j) ≤ L * a3 ∧ (G t).countP TKey.isH2 ≤ L * a2 ∧
      (G t).countP TKey.isH5 ≤ L * a5 ∧ (G t).countP TKey.isIC ≤ L * aE) :
    SReads pI F (L * a3) (n * ((K + 1) * nGrind) + L * a2) (n * ((K + 1) * 624) + L * a5)
      (n * ((K + 1) * 4607) + L * aE) :=
  GoodO.sreads (j := j) (sessReads_R c)
    (fun t t' l hA k hk => by rw [read_ins4, read_ins4]; exact read_congr _ j t t' l hA k hk) hF
    (fun j k h t => ⟨(QR_card c j k h t).2.1, (QR_card c j k h t).2.2.1, (QR_card c j k h t).2.2.2⟩)
    hG

/-- **One stretch** after a constant start, per slice position. -/
lemma sreads_run₁ {a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE) (j : Bool × Bool) (sl : SlicesR)
    (stop : List EvR → Bool) (L : ℕ) (tr : List EvR) :
    SReads pI (fun t : Tb R pI => A.run c stop L tr (ins4 j sl t.1) t.2) (L * a3)
      (n * ((K + 1) * nGrind) + L * a2) (n * ((K + 1) * 624) + L * a5)
      (n * ((K + 1) * 4607) + L * aE) := by
  refine sreads_gen c j sl (GoodO.run (next := A.next) (sessReads_R c) stop L
    (GoodO.const (n := n) (Q := QR (R := R) c) tr)) fun t => ?_
  simpa only [List.nil_append] using countP_logO_qb (n := n) (out := outR c) hN j stop L tr _ _

/-- **Two stretches**. -/
lemma sreads_run₂ {a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE) (j : Bool × Bool) (sl : SlicesR)
    (stop₁ stop₂ : List EvR → Bool) (L₁ L₂ : ℕ) (tr : List EvR) (e : ExtR) :
    SReads pI (fun t : Tb R pI => A.run c stop₂ L₂ (A.run c stop₁ L₁ tr (ins4 j sl t.1) t.2 ++ [.ext e])
        (ins4 j sl t.1) t.2) ((L₁ + L₂) * a3) (n * ((K + 1) * nGrind) + (L₁ + L₂) * a2)
      (n * ((K + 1) * 624) + (L₁ + L₂) * a5) (n * ((K + 1) * 4607) + (L₁ + L₂) * aE) := by
  refine sreads_gen c j sl (GoodO.run (next := A.next) (sessReads_R c) stop₂ L₂
    (GoodO.ext (GoodO.run (next := A.next) (sessReads_R c) stop₁ L₁
      (GoodO.const (n := n) (Q := QR (R := R) c) tr)) e)) fun t => ?_
  have h1 := countP_logO_qb (n := n) (out := outR c) hN j stop₁ L₁ tr
    (TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2) ((default : Tab3), t.2)
  have h2 := countP_logO_qb (n := n) (out := outR c) hN j stop₂ L₂
    (runO n (outR c) A.next stop₁ L₁ tr (TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2)
      ((default : Tab3), t.2) ++ [.ext e])
    (TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2) ((default : Tab3), t.2)
  simp only [List.nil_append, List.countP_append, Nat.add_mul]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- **Three stretches**. -/
lemma sreads_run₃ {a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE) (j : Bool × Bool) (sl : SlicesR)
    (stop₁ stop₂ stop₃ : List EvR → Bool) (L₁ L₂ L₃ : ℕ) (tr : List EvR) (e₁ e₂ : ExtR) :
    SReads pI (fun t : Tb R pI => A.run c stop₃ L₃ (A.run c stop₂ L₂
        (A.run c stop₁ L₁ tr (ins4 j sl t.1) t.2 ++ [.ext e₁]) (ins4 j sl t.1) t.2 ++ [.ext e₂])
        (ins4 j sl t.1) t.2) ((L₁ + L₂ + L₃) * a3) (n * ((K + 1) * nGrind) + (L₁ + L₂ + L₃) * a2)
      (n * ((K + 1) * 624) + (L₁ + L₂ + L₃) * a5) (n * ((K + 1) * 4607) + (L₁ + L₂ + L₃) * aE) := by
  refine sreads_gen c j sl (GoodO.run (next := A.next) (sessReads_R c) stop₃ L₃
    (GoodO.ext (GoodO.run (next := A.next) (sessReads_R c) stop₂ L₂
      (GoodO.ext (GoodO.run (next := A.next) (sessReads_R c) stop₁ L₁
        (GoodO.const (n := n) (Q := QR (R := R) c) tr)) e₁)) e₂)) fun t => ?_
  have h1 := countP_logO_qb (n := n) (out := outR c) hN j stop₁ L₁ tr
    (TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2) ((default : Tab3), t.2)
  have h2 := countP_logO_qb (n := n) (out := outR c) hN j stop₂ L₂
    (runO n (outR c) A.next stop₁ L₁ tr (TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2)
      ((default : Tab3), t.2) ++ [.ext e₁])
    (TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2) ((default : Tab3), t.2)
  have h3 := countP_logO_qb (n := n) (out := outR c) hN j stop₃ L₃
    (runO n (outR c) A.next stop₂ L₂ (runO n (outR c) A.next stop₁ L₁ tr
      (TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2) ((default : Tab3), t.2) ++ [.ext e₁])
      (TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2) ((default : Tab3), t.2) ++ [.ext e₂])
    (TKey.read (m := preLen pI) (sl4 (ins4 j sl t.1)) t.2) ((default : Tab3), t.2)
  simp only [List.nil_append, List.countP_append, Nat.add_mul]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- A reader of slice position `j` with the others of `sl`, at the parameters of that position. -/
lemma sreads_at {X : Type} {f : SlicesR → ShR R → X} {a3 a2 a5 aE : ℕ}
    (h : ∀ j sl, SReads pI (fun t : Tb R pI => f (ins4 j sl t.1) t.2) a3 a2 a5 aE) :
    (∀ g₁ g₂ g₃ : Tab3, SReads pI (fun t : Tb R pI => f ((t.1, g₁), (g₂, g₃)) t.2) a3 a2 a5 aE) ∧
    (∀ g₀ g₂ g₃ : Tab3, SReads pI (fun t : Tb R pI => f ((g₀, t.1), (g₂, g₃)) t.2) a3 a2 a5 aE) ∧
    (∀ g₀ g₁ g₃ : Tab3, SReads pS (fun t : Tb R pS => f ((g₀, g₁), (t.1, g₃)) t.2) a3 a2 a5 aE) ∧
    (∀ g₀ g₁ g₂ : Tab3, SReads pS (fun t : Tb R pS => f ((g₀, g₁), (g₂, t.1)) t.2) a3 a2 a5 aE) :=
  ⟨fun g₁ g₂ g₃ => h (false, false) ((default, g₁), (g₂, g₃)),
    fun g₀ g₂ g₃ => h (false, true) ((g₀, default), (g₂, g₃)),
    fun g₀ g₁ g₃ => h (true, false) ((g₀, g₁), (default, g₃)),
    fun g₀ g₁ g₂ => h (true, true) ((g₀, g₁), (g₂, default))⟩

lemma mono₄ {X : Type} {f : Tb R pI → X} {a3 a2 a5 aE b2 b5 bE : ℕ} {L L' : ℕ}
    (h : SReads pI f (L * a3) (b2 + L * a2) (b5 + L * a5) (bE + L * aE)) (hL : L ≤ L') :
    SReads pI f (L' * a3) (b2 + L' * a2) (b5 + L' * a5) (bE + L' * aE) :=
  h.mono (Nat.mul_le_mul_right _ hL) (by have := Nat.mul_le_mul_right a2 hL; omega)
    (by have := Nat.mul_le_mul_right a5 hL; omega) (by have := Nat.mul_le_mul_right aE hL; omega)

/-- **The reduction's key-stage budget**: the steps before the challenge. -/
theorem red_kBudget {a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE) :
    (A.red c).KBudget (A.L₁ * a3) (n * ((K + 1) * nGrind) + A.L₁ * a2)
      (n * ((K + 1) * 624) + A.L₁ * a5) (n * ((K + 1) * 4607) + A.L₁ * aE) := by
  obtain ⟨h0, h1, h2, h3⟩ := sreads_at (f := fun sl s => A.tr₁ c sl s)
    fun j sl => sreads_run₁ c hN j sl A.go A.L₁ []
  exact ⟨h0, h1, h2, h3⟩

/-- **The reduction's interaction budget**: both stages at every key-stage transcript, `L₂ + L₃`
steps. -/
theorem red_iBudget {a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE) :
    (A.red c).IBudget ((A.L₂ + A.L₃) * a3) (n * ((K + 1) * nGrind) + (A.L₂ + A.L₃) * a2)
      (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) := by
  intro T₁
  have h1 (tr : IssTr ZL) := sreads_at (f := fun sl s => (A.atT c T₁).msg₁ tr sl s)
    (a3 := (A.L₂ + A.L₃) * a3) (a2 := n * ((K + 1) * nGrind) + (A.L₂ + A.L₃) * a2)
    (a5 := n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) (aE := n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE)
    fun j sl => by
      have := mono₄ ((sreads_run₁ c hN j sl A.done₁ A.L₂ (T₁ ++ [.ext (.inl tr)])).map
        fun T => ((A.respondIss T false, A.respondIss T true), A.d₁ T)) (L' := A.L₂ + A.L₃)
        (Nat.le_add_right _ _)
      exact this
  have h2 (tr : IssTr ZL) (rq : SReq) := sreads_at (f := fun sl s => (A.atT c T₁).msg₂ tr rq sl s)
    (a3 := (A.L₂ + A.L₃) * a3) (a2 := n * ((K + 1) * nGrind) + (A.L₂ + A.L₃) * a2)
    (a5 := n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) (aE := n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE)
    fun j sl => by
      have := (sreads_run₂ c hN j sl A.done₁ A.done₂ A.L₂ A.L₃ (T₁ ++ [.ext (.inl tr)])
        (.inr (.inl rq))).map fun T => (A.respond₁ T, A.d₂ T)
      exact this
  exact
    { a0 := fun tr => (h1 tr).1
      a1 := fun tr => (h1 tr).2.1
      a2 := fun tr => (h1 tr).2.2.1
      a3 := fun tr => (h1 tr).2.2.2
      b0 := fun tr rq => (h2 tr rq).1
      b1 := fun tr rq => (h2 tr rq).2.1
      b2 := fun tr rq => (h2 tr rq).2.2.1
      b3 := fun tr rq => (h2 tr rq).2.2.2 }

/-- The guess's transcript, per slice position: `L₂ + L₃ + L₄` steps. -/
lemma sreads_guess {a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE) (T₁ : List EvR) (tr : IssTr ZL)
    (y : Rounds ZL) (j : Bool × Bool) (sl : SlicesR) :
    SReads pI (fun t : Tb R pI => A.tr₄ c (A.tr₃G c (A.tr₂ c T₁ tr (ins4 j sl t.1) t.2) y
        (ins4 j sl t.1) t.2) y (ins4 j sl t.1) t.2) ((A.L₂ + A.L₃ + A.L₄) * a3)
      (n * ((K + 1) * nGrind) + (A.L₂ + A.L₃ + A.L₄) * a2)
      (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5)
      (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE) := by
  unfold tr₄ tr₃G
  rcases y.map Prod.fst with _ | rq
  · simp only [Option.elim]
    refine mono₄ (L := A.L₂ + A.L₄) (L' := A.L₂ + A.L₃ + A.L₄) ?_ (by omega)
    exact sreads_run₂ c hN j sl A.done₁ (fun _ => false) A.L₂ A.L₄ (T₁ ++ [.ext (.inl tr)])
      (.inr (.inr y))
  · simp only [Option.elim]
    exact sreads_run₃ c hN j sl A.done₁ A.done₂ (fun _ => false) A.L₂ A.L₃ A.L₄
      (T₁ ++ [.ext (.inl tr)]) (.inr (.inl rq)) (.inr (.inr y))

/-- **The reduction's guess budget**: the Issuer's, plus the `n` Clients' and the scheduler's reads
after the key stage. -/
theorem red_gBudget {q3 q5 qE a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE)
    (hA : A.Budget q3 q5 qE) :
    (A.red c).GBudget ((A.L₂ + A.L₃ + A.L₄) * a3 + q3)
      (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5 + q5)
      (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE + qE) := by
  intro T₁ m
  have hs (tr : IssTr ZL) (y : Rounds ZL) :=
    sreads_at (f := fun sl s => A.tr₄ c (A.tr₃G c (A.tr₂ c T₁ tr sl s) y sl s) y sl s)
      (sreads_guess c hN T₁ tr y)
  exact
    { h30 := fun tr y g₁ g₂ g₃ s => Rd3.bindEq (fun _ => rfl) (((hs tr y).1 g₁ g₂ g₃).rd3 s)
        fun T => hA.h30 T g₁ g₂ g₃ s
      h31 := fun tr y g₀ g₂ g₃ s => Rd3.bindEq (fun _ => rfl) (((hs tr y).2.1 g₀ g₂ g₃).rd3 s)
        fun T => hA.h31 T g₀ g₂ g₃ s
      h32 := fun tr y g₀ g₁ g₃ s => Rd3.bindEq (fun _ => rfl) (((hs tr y).2.2.1 g₀ g₁ g₃).rd3 s)
        fun T => hA.h32 T g₀ g₁ g₃ s
      h33 := fun tr y g₀ g₁ g₂ s => Rd3.bindEq (fun _ => rfl) (((hs tr y).2.2.2 g₀ g₁ g₂).rd3 s)
        fun T => hA.h33 T g₀ g₁ g₂ s
      h5 := fun tr y sl => Rd5.bindEq (m := fun s => A.tr₄ c (A.tr₃G c (A.tr₂ c T₁ tr sl s) y sl s) y sl s)
        (f := fun T s => A.guess T sl s) (fun _ => rfl)
        (((hs tr y).1 sl.1.2 sl.2.1 sl.2.2).rd5 sl.1.1) fun T => hA.h5 T sl
      hE := fun tr y sl => RdE.bindEq (m := fun s => A.tr₄ c (A.tr₃G c (A.tr₂ c T₁ tr sl s) y sl s) y sl s)
        (f := fun T s => A.guess T sl s) (fun _ => rfl)
        (((hs tr y).1 sl.1.2 sl.2.1 sl.2.2).rdE sl.1.1) fun T => hA.hE T sl }

end AdversaryILRO

end Game

/-! ## The bound -/

section Bound

variable {n K : ℕ}

/-- **Theorem 2 with interleaved further sessions that spend up to `K` times, a table-reading
scheduler and a free challenge, for every type of cipher rows**: `unlinkabilityRAK_lean_numG` at
the key-stage budget `(L₁a₃, (K+1)n·2³² + L₁a₂, (K+1)n·624 + L₁a₅, (K+1)n·4607 + L₁a_E)`, the
interaction budget (the same with `L₂ + L₃`) and the guess budget `((L₂+L₃+L₄)a₃ + q₃,
(K+1)n·624 + (L₂+L₃+L₄)a₅ + q₅, (K+1)n·4607 + (L₂+L₃+L₄)a_E + q_E)`; any two worlds. -/
theorem unlinkabilityILO_lean_numG [ZKRow R] [ZKPRow R] (A : AdversaryILRO R) {q3 q5 qE a3 a2 a5 aE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE)
    (hhide : ∀ (c : Fin n → XK K) b₁ b₂ Y,
      hidingAdv (A.atT c (A.tr₁ c Y.2.1 Y.2.2)).ctx
        (reductionRA (A.atT c (A.tr₁ c Y.2.1 Y.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ Y) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR R) (realGameILRO A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR R) (realGameILRO A b₁' b₂')| ≤
      4 * εAdG R pI 9 (2 * ((A.L₂ + A.L₃) * a3) + ((A.L₂ + A.L₃ + A.L₄) * a3 + q3)) (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5 + q5 + 2 * (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1872)
          (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE + qE + 2 * (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 13821) (A.L₁ * a3) (n * ((K + 1) * nGrind) + A.L₁ * a2) (n * ((K + 1) * 624) + A.L₁ * a5) (n * ((K + 1) * 4607) + A.L₁ * aE) +
        2 * εAdG R pS 9 ((A.L₂ + A.L₃) * a3 + ((A.L₂ + A.L₃ + A.L₄) * a3 + q3)) (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5 + q5 + (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1248) (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE + qE + (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 13821)
          (A.L₁ * a3 + ((A.L₂ + A.L₃) * a3)) (n * ((K + 1) * nGrind) + A.L₁ * a2 + (n * ((K + 1) * nGrind) + (A.L₂ + A.L₃) * a2)) (n * ((K + 1) * 624) + A.L₁ * a5 + (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 624) (n * ((K + 1) * 4607) + A.L₁ * aE + (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 9214) +
        2 * εAdG R pS 9 ((A.L₂ + A.L₃ + A.L₄) * a3 + q3) (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5 + q5 + 936) (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE + qE + 13821) (A.L₁ * a3 + 2 * ((A.L₂ + A.L₃) * a3))
          (n * ((K + 1) * nGrind) + A.L₁ * a2 + 2 * (n * ((K + 1) * nGrind) + (A.L₂ + A.L₃) * a2)) (n * ((K + 1) * 624) + A.L₁ * a5 + 2 * (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1560) (n * ((K + 1) * 4607) + A.L₁ * aE + 2 * (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 23035) +
        2 * (((A.L₁ * a3 + ((A.L₂ + A.L₃) * a3) : ℕ) : ℝ) / 2 ^ 128) + 2 * (((A.L₁ * a3 + 2 * ((A.L₂ + A.L₃) * a3) : ℕ) : ℝ) / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + ZKPRow.εP R pS 0 312 4607 (n * ((K + 1) * 624) + A.L₁ * a5 + 2 * (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1560) (n * ((K + 1) * 4607) + A.L₁ * aE + 2 * (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  rw [← pr_equiv tapeILR, ← pr_equiv tapeILR]
  exact abs_pr_prod_sub_le _ _ fun c =>
    unlinkabilityRAK_lean_numG (A.red c) (AdversaryILRO.red_gBudget c hN hA)
      (AdversaryILRO.red_iBudget c hN) (AdversaryILRO.red_kBudget c hN) (hhide c) b₁ b₂ b₁' b₂'

/-- **`unlinkabilityILO_lean_numG` with function rows.** -/
theorem unlinkabilityILO_lean_num (A : AdversaryILRO (Blk → Blk)) {q3 q5 qE a3 a2 a5 aE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE)
    (hhide : ∀ (c : Fin n → XK K) b₁ b₂ Y,
      hidingAdv (A.atT c (A.tr₁ c Y.2.1 Y.2.2)).ctx
        (reductionRA (A.atT c (A.tr₁ c Y.2.1 Y.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ Y) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILRO A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILRO A b₁' b₂')| ≤
      4 * εAd 9 (2 * ((A.L₂ + A.L₃) * a3) + ((A.L₂ + A.L₃ + A.L₄) * a3 + q3)) (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5 + q5 + 2 * (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1872)
          (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE + qE + 2 * (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 13821) (A.L₁ * a3) (n * ((K + 1) * nGrind) + A.L₁ * a2) (n * ((K + 1) * 624) + A.L₁ * a5) (n * ((K + 1) * 4607) + A.L₁ * aE) +
        2 * εAd 9 ((A.L₂ + A.L₃) * a3 + ((A.L₂ + A.L₃ + A.L₄) * a3 + q3)) (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5 + q5 + (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1248) (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE + qE + (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 13821)
          (A.L₁ * a3 + ((A.L₂ + A.L₃) * a3)) (n * ((K + 1) * nGrind) + A.L₁ * a2 + (n * ((K + 1) * nGrind) + (A.L₂ + A.L₃) * a2)) (n * ((K + 1) * 624) + A.L₁ * a5 + (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 624) (n * ((K + 1) * 4607) + A.L₁ * aE + (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 9214) +
        2 * εAd 9 ((A.L₂ + A.L₃ + A.L₄) * a3 + q3) (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5 + q5 + 936) (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE + qE + 13821) (A.L₁ * a3 + 2 * ((A.L₂ + A.L₃) * a3))
          (n * ((K + 1) * nGrind) + A.L₁ * a2 + 2 * (n * ((K + 1) * nGrind) + (A.L₂ + A.L₃) * a2)) (n * ((K + 1) * 624) + A.L₁ * a5 + 2 * (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1560) (n * ((K + 1) * 4607) + A.L₁ * aE + 2 * (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 23035) +
        2 * (((A.L₁ * a3 + ((A.L₂ + A.L₃) * a3) : ℕ) : ℝ) / 2 ^ 128) + 2 * (((A.L₁ * a3 + 2 * ((A.L₂ + A.L₃) * a3) : ℕ) : ℝ) / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + εROP 0 312 4607 (n * ((K + 1) * 624) + A.L₁ * a5 + 2 * (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1560) (n * ((K + 1) * 4607) + A.L₁ * aE + 2 * (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityILO_lean_numG A hA hN hhide b₁ b₂ b₁' b₂'

/-- **`unlinkabilityILO_lean_numG` with AES as uniformly random permutations.** -/
theorem unlinkabilityILO_lean_num_perm (A : AdversaryILRO (Equiv.Perm Blk)) {q3 q5 qE a3 a2 a5 aE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE)
    (hhide : ∀ (c : Fin n → XK K) b₁ b₂ Y,
      hidingAdv (A.atT c (A.tr₁ c Y.2.1 Y.2.2)).ctx
        (reductionRA (A.atT c (A.tr₁ c Y.2.1 Y.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ Y) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Equiv.Perm Blk)) (realGameILRO A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Equiv.Perm Blk)) (realGameILRO A b₁' b₂')| ≤
      4 * εAdPm pI 9 (2 * ((A.L₂ + A.L₃) * a3) + ((A.L₂ + A.L₃ + A.L₄) * a3 + q3)) (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5 + q5 + 2 * (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1872)
          (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE + qE + 2 * (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 13821) (A.L₁ * a3) (n * ((K + 1) * nGrind) + A.L₁ * a2) (n * ((K + 1) * 624) + A.L₁ * a5) (n * ((K + 1) * 4607) + A.L₁ * aE) +
        2 * εAdPm pS 9 ((A.L₂ + A.L₃) * a3 + ((A.L₂ + A.L₃ + A.L₄) * a3 + q3)) (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5 + q5 + (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1248) (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE + qE + (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 13821)
          (A.L₁ * a3 + ((A.L₂ + A.L₃) * a3)) (n * ((K + 1) * nGrind) + A.L₁ * a2 + (n * ((K + 1) * nGrind) + (A.L₂ + A.L₃) * a2)) (n * ((K + 1) * 624) + A.L₁ * a5 + (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 624) (n * ((K + 1) * 4607) + A.L₁ * aE + (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 9214) +
        2 * εAdPm pS 9 ((A.L₂ + A.L₃ + A.L₄) * a3 + q3) (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5 + q5 + 936) (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE + qE + 13821) (A.L₁ * a3 + 2 * ((A.L₂ + A.L₃) * a3))
          (n * ((K + 1) * nGrind) + A.L₁ * a2 + 2 * (n * ((K + 1) * nGrind) + (A.L₂ + A.L₃) * a2)) (n * ((K + 1) * 624) + A.L₁ * a5 + 2 * (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1560) (n * ((K + 1) * 4607) + A.L₁ * aE + 2 * (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 23035) +
        2 * (((A.L₁ * a3 + ((A.L₂ + A.L₃) * a3) : ℕ) : ℝ) / 2 ^ 128) + 2 * (((A.L₁ * a3 + 2 * ((A.L₂ + A.L₃) * a3) : ℕ) : ℝ) / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + εROPmP pS 0 312 4607 (n * ((K + 1) * 624) + A.L₁ * a5 + 2 * (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1560) (n * ((K + 1) * 4607) + A.L₁ * aE + 2 * (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityILO_lean_numG A hA hN hhide b₁ b₂ b₁' b₂'

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

/-- **The bound in numbers**: with `n` further Clients spending up to `K` times each and a
scheduler within `(a₃, a₂, a₅, a_E)` per step for `L = L₁ + L₂ + L₃ + L₄` steps, any two worlds
differ by at most

    (n(K+1) + 2)·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 46·L·(a₃ + a₂ + a₅ + 221·a_E)·2⁻¹²⁸
      + 2·εhide. -/
theorem unlinkabilityILO_lean_le (A : AdversaryILRO (Blk → Blk)) {q3 q5 qE a3 a2 a5 aE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE)
    (hhide : ∀ (c : Fin n → XK K) b₁ b₂ Y,
      hidingAdv (A.atT c (A.tr₁ c Y.2.1 Y.2.2)).ctx
        (reductionRA (A.atT c (A.tr₁ c Y.2.1 Y.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ Y) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILRO A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILRO A b₁' b₂')| ≤
      (n * (K + 1) + 2 : ℕ) / 2 ^ 101 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 +
        46 * ((A.L₁ + A.L₂ + A.L₃ + A.L₄) * (a3 + a2 + a5 + 221 * aE) : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := unlinkabilityILO_lean_num A hA hN hhide b₁ b₂ b₁' b₂'
  have u1 := εAd9_le (2 * ((A.L₂ + A.L₃) * a3) + ((A.L₂ + A.L₃ + A.L₄) * a3 + q3)) (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5 + q5 + 2 * (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1872)
    (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE + qE + 2 * (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 13821) (A.L₁ * a3) (n * ((K + 1) * nGrind) + A.L₁ * a2) (n * ((K + 1) * 624) + A.L₁ * a5) (n * ((K + 1) * 4607) + A.L₁ * aE)
  have u2 := εAd9_le ((A.L₂ + A.L₃) * a3 + ((A.L₂ + A.L₃ + A.L₄) * a3 + q3)) (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5 + q5 + (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1248) (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE + qE + (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 13821)
    (A.L₁ * a3 + ((A.L₂ + A.L₃) * a3)) (n * ((K + 1) * nGrind) + A.L₁ * a2 + (n * ((K + 1) * nGrind) + (A.L₂ + A.L₃) * a2)) (n * ((K + 1) * 624) + A.L₁ * a5 + (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 624) (n * ((K + 1) * 4607) + A.L₁ * aE + (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 9214)
  have u3 := εAd9_le ((A.L₂ + A.L₃ + A.L₄) * a3 + q3) (n * ((K + 1) * 624) + (A.L₂ + A.L₃ + A.L₄) * a5 + q5 + 936) (n * ((K + 1) * 4607) + (A.L₂ + A.L₃ + A.L₄) * aE + qE + 13821) (A.L₁ * a3 + 2 * ((A.L₂ + A.L₃) * a3))
    (n * ((K + 1) * nGrind) + A.L₁ * a2 + 2 * (n * ((K + 1) * nGrind) + (A.L₂ + A.L₃) * a2)) (n * ((K + 1) * 624) + A.L₁ * a5 + 2 * (n * ((K + 1) * 624) + (A.L₂ + A.L₃) * a5) + 1560) (n * ((K + 1) * 4607) + A.L₁ * aE + 2 * (n * ((K + 1) * 4607) + (A.L₂ + A.L₃) * aE) + 23035)
  have hM : n * ((K + 1) * nGrind) = n * (K + 1) * nGrind := by ring
  have hM4 : n * (K + 1) * (4 * nGrind) = 4 * (n * (K + 1) * nGrind) := by ring
  have g1 := grind_le_add (n * ((K + 1) * nGrind) + A.L₁ * a2) (n * (K + 1)) (A.L₁ * a2) (by rw [hM, hM4]; omega)
  have g2 := grind_le_add (n * ((K + 1) * nGrind) + A.L₁ * a2 + (n * ((K + 1) * nGrind) + (A.L₂ + A.L₃) * a2)) (n * (K + 1)) (A.L₁ * a2 + (A.L₂ + A.L₃) * a2)
    (by rw [hM, hM4]; omega)
  have g3 := grind_le_add (n * ((K + 1) * nGrind) + A.L₁ * a2 + 2 * (n * ((K + 1) * nGrind) + (A.L₂ + A.L₃) * a2)) (n * (K + 1)) (A.L₁ * a2 + 2 * ((A.L₂ + A.L₃) * a2))
    (by rw [hM, hM4]; omega)
  have hn := noHitProb_le_128
  have hn0 : 0 ≤ noHitProb := pr_nonneg _
  have hK : (12 : ℝ) / 2 ^ 1024 ≤ 1 / 2 ^ 128 := by
    have e1024 : (2 : ℝ) ^ 1024 = 2 ^ 128 * 2 ^ 896 := by rw [← pow_add]
    have hb : (2 : ℝ) ^ 32 ≤ 2 ^ 896 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hp : (0 : ℝ) < 2 ^ 128 := by positivity
    rw [e1024, div_le_div_iff₀ (by positivity) (by positivity)]
    have h16 : (12 : ℝ) ≤ 2 ^ 32 := by norm_num
    calc (12 : ℝ) * 2 ^ 128 ≤ 2 ^ 896 * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right (h16.trans hb) hp.le
      _ = 1 * (2 ^ 128 * 2 ^ 896) := by rw [one_mul, mul_comm]
  have eS : (A.L₁ + A.L₂ + A.L₃ + A.L₄) * (a3 + a2 + a5 + 221 * aE) =
      (A.L₁ + A.L₂ + A.L₃ + A.L₄) * a3 + (A.L₁ + A.L₂ + A.L₃ + A.L₄) * a2 +
        (A.L₁ + A.L₂ + A.L₃ + A.L₄) * a5 + 221 * ((A.L₁ + A.L₂ + A.L₃ + A.L₄) * aE) := by ring
  have f3 : A.L₁ * a3 + (A.L₂ + A.L₃) * a3 ≤ (A.L₁ + A.L₂ + A.L₃ + A.L₄) * a3 := by nlinarith
  have f2 : A.L₁ * a2 + (A.L₂ + A.L₃) * a2 ≤ (A.L₁ + A.L₂ + A.L₃ + A.L₄) * a2 := by nlinarith
  have f5 : A.L₁ * a5 + (A.L₂ + A.L₃) * a5 ≤ (A.L₁ + A.L₂ + A.L₃ + A.L₄) * a5 := by nlinarith
  have fE : A.L₁ * aE + (A.L₂ + A.L₃) * aE ≤ (A.L₁ + A.L₂ + A.L₃ + A.L₄) * aE := by nlinarith
  have f3' : (A.L₂ + A.L₃ + A.L₄) * a3 ≤ (A.L₁ + A.L₂ + A.L₃ + A.L₄) * a3 :=
    Nat.mul_le_mul_right _ (by omega)
  have f5' : (A.L₂ + A.L₃ + A.L₄) * a5 ≤ (A.L₁ + A.L₂ + A.L₃ + A.L₄) * a5 :=
    Nat.mul_le_mul_right _ (by omega)
  have fE' : (A.L₂ + A.L₃ + A.L₄) * aE ≤ (A.L₁ + A.L₂ + A.L₃ + A.L₄) * aE :=
    Nat.mul_le_mul_right _ (by omega)
  rw [eS]
  generalize A.L₁ * a3 = k3 at h u1 u2 u3 f3
  generalize (A.L₂ + A.L₃) * a3 = i3 at h u1 u2 u3 f3
  generalize (A.L₂ + A.L₃ + A.L₄) * a3 = j3 at h u1 u2 u3 f3'
  generalize (A.L₁ + A.L₂ + A.L₃ + A.L₄) * a3 = S3 at f3 f3' ⊢
  generalize A.L₁ * a2 = k2 at h u1 u2 u3 f2 g1 g2 g3
  generalize (A.L₂ + A.L₃) * a2 = i2 at h u1 u2 u3 f2 g1 g2 g3
  generalize (A.L₁ + A.L₂ + A.L₃ + A.L₄) * a2 = S2 at f2 ⊢
  generalize A.L₁ * a5 = k5 at h u1 u2 u3 f5
  generalize (A.L₂ + A.L₃) * a5 = i5 at h u1 u2 u3 f5
  generalize (A.L₂ + A.L₃ + A.L₄) * a5 = j5 at h u1 u2 u3 f5'
  generalize (A.L₁ + A.L₂ + A.L₃ + A.L₄) * a5 = S5 at f5 f5' ⊢
  generalize A.L₁ * aE = kE at h u1 u2 u3 fE
  generalize (A.L₂ + A.L₃) * aE = iE at h u1 u2 u3 fE
  generalize (A.L₂ + A.L₃ + A.L₄) * aE = jE at h u1 u2 u3 fE'
  generalize (A.L₁ + A.L₂ + A.L₃ + A.L₄) * aE = SE at fE fE' ⊢
  have r3 : (k3 : ℝ) + i3 ≤ S3 := by exact_mod_cast f3
  have r2 : (k2 : ℝ) + i2 ≤ S2 := by exact_mod_cast f2
  have r5 : (k5 : ℝ) + i5 ≤ S5 := by exact_mod_cast f5
  have rE : (kE : ℝ) + iE ≤ SE := by exact_mod_cast fE
  have r3' : (j3 : ℝ) ≤ S3 := by exact_mod_cast f3'
  have r5' : (j5 : ℝ) ≤ S5 := by exact_mod_cast f5'
  have rE' : (jE : ℝ) ≤ SE := by exact_mod_cast fE'
  have p3 : (0 : ℝ) ≤ k3 := Nat.cast_nonneg _
  have p2 : (0 : ℝ) ≤ k2 := Nat.cast_nonneg _
  have p5 : (0 : ℝ) ≤ k5 := Nat.cast_nonneg _
  have pE : (0 : ℝ) ≤ kE := Nat.cast_nonneg _
  have p3' : (0 : ℝ) ≤ i3 := Nat.cast_nonneg _
  have p2' : (0 : ℝ) ≤ i2 := Nat.cast_nonneg _
  have p5' : (0 : ℝ) ≤ i5 := Nat.cast_nonneg _
  have pE' : (0 : ℝ) ≤ iE := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have h12 : (0 : ℝ) ≤ (n : ℝ) * ((K : ℝ) + 1) := mul_nonneg h1 (by linarith)
  simp only [← Nat.mul_assoc] at h u1 u2 u3 g1 g2 g3
  generalize (2 : ℝ) ^ 1024 = κ at hK g1 g2 g3 u1 u2 u3 h
  unfold εROP εRO at h u1 u2 u3
  push_cast at h u1 u2 u3 g1 g2 g3 ⊢
  generalize (n : ℝ) * ((K : ℝ) + 1) = P at h u1 u2 u3 g1 g2 g3 h12 ⊢
  have e : ∀ x : ℝ, x / 2 ^ 101 = x * 134217728 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  rw [e]
  linarith

/-- **`2²⁰` proofs**: with `n(K+1) + 2 ≤ 2²⁰`, `≤ 2⁻⁸¹ + 2·εhide` plus the guess's and the
scheduler's budget terms. -/
theorem unlinkabilityILO_lean_2pow20 (A : AdversaryILRO (Blk → Blk)) {q3 q5 qE a3 a2 a5 aE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE)
    (hhide : ∀ (c : Fin n → XK K) b₁ b₂ Y,
      hidingAdv (A.atT c (A.tr₁ c Y.2.1 Y.2.2)).ctx
        (reductionRA (A.atT c (A.tr₁ c Y.2.1 Y.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ Y) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) (hn : n * (K + 1) + 2 ≤ 2 ^ 20) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILRO A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILRO A b₁' b₂')| ≤
      1 / 2 ^ 81 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 +
        46 * ((A.L₁ + A.L₂ + A.L₃ + A.L₄) * (a3 + a2 + a5 + 221 * aE) : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := unlinkabilityILO_lean_le A hA hN hhide b₁ b₂ b₁' b₂'
  have : ((n * (K + 1) + 2 : ℕ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hn
  have h2 : ((n * (K + 1) + 2 : ℕ) : ℝ) / 2 ^ 101 ≤ 1 / 2 ^ 81 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **`2³²` proofs**: with `n(K+1) + 2 ≤ 2³²`, `≤ 2⁻⁶⁹ + 2·εhide` plus the guess's and the
scheduler's budget terms. -/
theorem unlinkabilityILO_lean_2pow32 (A : AdversaryILRO (Blk → Blk)) {q3 q5 qE a3 a2 a5 aE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE)
    (hhide : ∀ (c : Fin n → XK K) b₁ b₂ Y,
      hidingAdv (A.atT c (A.tr₁ c Y.2.1 Y.2.2)).ctx
        (reductionRA (A.atT c (A.tr₁ c Y.2.1 Y.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ Y) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) (hn : n * (K + 1) + 2 ≤ 2 ^ 32) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILRO A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILRO A b₁' b₂')| ≤
      1 / 2 ^ 69 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 +
        46 * ((A.L₁ + A.L₂ + A.L₃ + A.L₄) * (a3 + a2 + a5 + 221 * aE) : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := unlinkabilityILO_lean_le A hA hN hhide b₁ b₂ b₁' b₂'
  have : ((n * (K + 1) + 2 : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have h2 : ((n * (K + 1) + 2 : ℕ) : ℝ) / 2 ^ 101 ≤ 1 / 2 ^ 69 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end Bound

end VoleMole.Privacy.Ratatouille
