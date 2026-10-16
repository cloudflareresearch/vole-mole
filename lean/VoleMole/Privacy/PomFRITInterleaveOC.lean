import VoleMole.Privacy.PomFRITInterleave
import VoleMole.ZK.ReadsInterleaveOC
import VoleMole.ROM.PrivacyReads

/-!
# PomFRIT blindness with interleaved sessions, a table-reading scheduler and a free challenge

`Privacy/PomFRITInterleave.lean` proves blindness against an Issuer that schedules further
sessions arbitrarily, but its scheduler is a function of the transcript, and the challenge has a
fixed place in the schedule (`L₁` steps, both requests, `L₂` steps, both answers, `L₃` steps).
Here:

* **the scheduler reads the tables**: each step is a VCVio oracle computation over the two
  challenge `H₃` slices and the shared tables (`ROM.Reads.TSpec Bool`), within a per-step query
  bound (`AdversaryILO.SBudget a₃ a₂ a₅ a_E`, VCVio's `IsQueryBoundP`); consistency is by
  construction (`ZK/ReadsInterleaveOC.lean`);
* **the challenge is placed by the scheduler**: the challenge starts at the first step at which
  `go` holds (at most `L₁` steps), and its answers are taken at the first step at which `done`
  holds (at most `L₂` steps after the requests; the answers, `respond`, are read off the
  transcript then, so each answer may be decided at any step before, e.g. recorded by an action
  to a session that does not exist, which is refused and changes nothing). The outcome is revealed
  at that step, and the scheduler continues for at most `L₃` steps.

What stays fixed is that the two challenge requests are revealed together, and the outcome after
both answers. Neither restricts the Issuer: a request revealed earlier gives the Issuer more, and
an Issuer that wants it later ignores it until then; and the first answer has no visible effect
before the outcome (the outcome is the pair of signatures if both sessions complete, else `none`,
the "both ⊥" rule), so answering one session at an earlier step is answering it at the step of the
second answer with what the Issuer decided earlier (the free placement above).

## The reduction

For each tape `c` of the further sessions, the game is the two-session game with a table-reading
Issuer (`realGameILO_iff`, `Iff.rfl`) for `A.red c`, whose stages run the schedule on the slices
and the shared tables. By the interleaving lemma with a table-reading scheduler (`GoodO.run`), a
stretch of the schedule reads the sessions' read sets (`n` sessions, `H₂³` at one prefix each)
and the scheduler's queries (at most `L·a` for `L` steps): `IBudgetHB ((L₁+L₂)·a₃) (n +
(L₁+L₂)·a₂) (n·624 + (L₁+L₂)·a₅) (n·4607 + (L₁+L₂)·a_E)` (`red_iBudgetHB`, through
`GoodO.sreadsPB_IL`, a joint reader of both slices) and guess `(q₃ + L·a₃, n·624 + L·a₅ + q₅,
n·4607 + L·a_E + q_E)` with `L = L₁ + L₂ + L₃` (`red_gBudget`, through `GoodO.sreads`).

## The bound

`blindnessRAH_lean_numG_pfx` for every `c`, averaged: `blindnessILO_lean_numG`, `_num`,
`_num_perm`; in numbers (`blindnessILO_lean_le`)

    ≤ (n + 2)·2⁻¹⁰² + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 52·L·(a₃ + a₂ + a₅ + 221·a_E)·2⁻¹²⁸,

`2⁻⁸²` (resp. `2⁻⁷⁰`) at `n + 2 ≤ 2²⁰` (`2³²`) plus the budget terms (`blindnessILO_lean_2pow20`,
`_2pow32`): the bound of `blindnessIL_lean_le`, plus the scheduler's reads, each charged as an
interaction read.
-/

open Finset OracleComp OracleSpec

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT
open VoleMole.ROM.Reads (TKey TSpec QBudget sl2 sl2_f sl2_t readAt read_congr
  card_toFinset_filterMap_le)

attribute [local irreducible] commitRefresher UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-! ## Both slices: a joint reader -/

section Joint

variable {Hb : Hashes} {n : ℕ}

lemma SReadsPB.map' {X Y : Type*} {f : TbP R → Y} {a3 b2 a5 aE : ℕ} (hf : SReadsPB f a3 b2 a5 aE)
    (φ : Y → X) : SReadsPB (fun t => φ (f t)) a3 b2 a5 aE := by
  obtain ⟨Q, hQ, hc⟩ := hf
  exact ⟨Q, fun t t' h => ⟨(hQ t t' h).1, by simp only [(hQ t t' h).2]⟩, hc⟩

/-- The scheduler's answers on both slices and the shared tables. -/
def rdP (t : TbP R) : (k : TKey Bool (preLen pP)) → TKey.Ans R k :=
  TKey.read (m := preLen pP) (sl2 t.1) t.2

/-- **A good interleaved transcript is a joint consistent reader of both slices**, `H₂³` at `n`
prefixes for the sessions plus the scheduler's `H₂³` keys. -/
theorem GoodO.sreadsPB_IL (hHb : HashesWF Hb) (c : Fin n → XR) {F : TbP R → List EvP}
    {G : TbP R → List (TKey Bool (preLen pP))}
    (hF : GoodO (spec := TSpec Bool R (preLen pP)) n (QIL Hb c) rdP
      (fun t : TbP R => ((default : Tab3), t.2)) F G) {c3 c2 c5 cE : ℕ}
    (hG : ∀ t, (G t).countP (TKey.isH3 false) ≤ c3 ∧ (G t).countP (TKey.isH3 true) ≤ c3 ∧
      (G t).countP TKey.isH2 ≤ c2 ∧ (G t).countP TKey.isH5 ≤ c5 ∧ (G t).countP TKey.isIC ≤ cE) :
    SReadsPB F c3 (n + c2) (n * 624 + c5) (n * 4607 + cE) := by
  classical
  let S : TbP R → RS pP := fun t => RQl (QIL Hb c) ((default : Tab3), t.2) 0 (sessSt n (F t))
  let K : TbP R → RSP := fun t => AdversaryOC.rsOfP (G t)
  refine ⟨fun t => ((K t).1, (S t).2.1 ∪ (K t).2.1, (S t).2.2.1 ∪ (K t).2.2.1,
    (S t).2.2.2 ∪ (K t).2.2.2), fun t t' h => ?_, fun t => ?_⟩
  · obtain ⟨h0, h1, h2, h5, hE⟩ := h
    have hA : AgT (S t) ((default : Tab3), t.2) ((default : Tab3), t'.2) :=
      ⟨fun _ _ => rfl, fun k hk => h2 k (mem_union_left _ hk),
        fun k hk => h5 k (mem_union_left _ hk), fun k hk => hE k (mem_union_left _ hk)⟩
    have hR : AgP (K t) t t' :=
      ⟨h0, h1, fun k hk => h2 k (mem_union_right _ hk), fun k hk => h5 k (mem_union_right _ hk),
        fun k hk => hE k (mem_union_right _ hk)⟩
    obtain ⟨e1, e2, e3⟩ := hF.cons (sessReads_IL hHb c) t t' hA
      (AdversaryOC.readP_congr t t' (G t) hR)
    refine ⟨?_, e2⟩
    simp only [S, K] at e1 ⊢
    rw [e1, e3]
  · have hl := sessSt_length_le n (F t)
    have s2 := (card_RQl (Q := QIL Hb c) (fun r => r.2.1.image Prod.fst)
      (fun r r' => image_union _ _) (image_empty _) ((default : Tab3), t.2)
      (fun j k h => QIL_pfx c j k h _) (sessSt n (F t)) 0).trans (Nat.mul_le_mul_right 1 hl)
    have s5 := (card_RQl (Q := QIL Hb c) (fun r => r.2.2.1) (fun _ _ => rfl) rfl ((default : Tab3), t.2)
      (fun j k h => (QIL_card c j k h _).2.2.1) (sessSt n (F t)) 0).trans (Nat.mul_le_mul_right 624 hl)
    have sE := (card_RQl (Q := QIL Hb c) (fun r => r.2.2.2) (fun _ _ => rfl) rfl ((default : Tab3), t.2)
      (fun j k h => (QIL_card c j k h _).2.2.2) (sessSt n (F t)) 0).trans (Nat.mul_le_mul_right 4607 hl)
    obtain ⟨g0, g1, g2, g5, gE⟩ := hG t
    have k0 : ((G t).filterMap (TKey.get3 false)).toFinset.card ≤ c3 :=
      (card_toFinset_filterMap_le _ _).trans (by simpa only [TKey.isSome_get3] using g0)
    have k1 : ((G t).filterMap (TKey.get3 true)).toFinset.card ≤ c3 :=
      (card_toFinset_filterMap_le _ _).trans (by simpa only [TKey.isSome_get3] using g1)
    have k2 : ((G t).filterMap TKey.get2).toFinset.card ≤ c2 :=
      (card_toFinset_filterMap_le _ _).trans (by simpa only [TKey.isSome_get2] using g2)
    have k5 : ((G t).filterMap TKey.get5).toFinset.card ≤ c5 :=
      (card_toFinset_filterMap_le _ _).trans (by simpa only [TKey.isSome_get5] using g5)
    have kE : ((G t).filterMap TKey.getE).toFinset.card ≤ cE :=
      (card_toFinset_filterMap_le _ _).trans (by simpa only [TKey.isSome_getE] using gE)
    refine ⟨k0, k1, ?_, (card_union_le _ _).trans (add_le_add s5 k5),
      (card_union_le _ _).trans (add_le_add sE kE)⟩
    rw [image_union]
    refine (card_union_le _ _).trans (add_le_add ?_ (card_image_le.trans k2))
    simp only [S]
    simpa using s2

end Joint

/-! ## The game -/

section Game

variable {n : ℕ}

/-- **The Issuer of the interleaved game with a table-reading scheduler and a free challenge**:
at each step the next action is an oracle computation over both challenge slices and the shared
tables, from the transcript; the challenge starts at the first step at which `go` holds (at most
`L₁` steps), its answers are taken at the first step at which `done` holds (at most `L₂` steps
after the requests), and at most `L₃` steps follow the outcome; the challenge key and messages,
the answers and the guess from the transcript. -/
structure AdversaryILO (R : Type) where
  L₁ : ℕ
  L₂ : ℕ
  L₃ : ℕ
  next : List EvP → OracleComp (TSpec Bool R (preLen pP)) ActP
  go : List EvP → Bool
  done : List EvP → Bool
  pk : List EvP → UOVKey
  msg : List EvP → Bool → Bytes
  respond : List EvP → Bool → Bytes
  guess : List EvP → SlP → ShP R → Prop

/-- **The scheduler's budget**: every step queries each slice at most `a₃` times, `H₂³` `a₂`
times, `H₅` `a₅` times and the cipher `a_E` times (VCVio's `IsQueryBoundP`). -/
def AdversaryILO.SBudget (A : AdversaryILO R) (a3 a2 a5 aE : ℕ) : Prop :=
  ∀ tr, QBudget (A.next tr) a3 a2 a5 aE

/-- **The guess's budget**: each challenge slice at `q3` keys, `H₅` at `q5`, the cipher at `qE`;
`H₂³` freely. -/
structure AdversaryILO.Budget (A : AdversaryILO R) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ T (g₁ : Tab3) s, Rd3 (fun g => A.guess T (g, g₁) s) q3
  h31 : ∀ T (g₀ : Tab3) s, Rd3 (fun g => A.guess T (g₀, g) s) q3
  h5 : ∀ T sl, Rd5 (A.guess T sl) q5
  hE : ∀ T sl, RdE (A.guess T sl) qE

variable (Hb : Hashes)

namespace AdversaryILO

variable (A : AdversaryILO R) (c : Fin n → XR)

/-- At most `L` steps of the schedule until `stop`, the scheduler reading the slices `sl` and the
tables `s`. -/
noncomputable def run (stop : List EvP → Bool) (L : ℕ) (tr : List EvP) (sl : SlP) (s : ShP R) :
    List EvP :=
  runO n (outIL Hb c) A.next stop L tr (rdP (sl, s)) ((default : Tab3), s)

/-- The steps before the challenge. -/
noncomputable def tr₁ (sl : SlP) (s : ShP R) : List EvP := A.run Hb c A.go A.L₁ [] sl s

/-- The steps between the challenge requests `t₀`, `t₁` and the challenge answers. -/
noncomputable def tr₂ (T₁ : List EvP) (t₀ t₁ : Bytes) (sl : SlP) (s : ShP R) : List EvP :=
  A.run Hb c A.done A.L₂ (T₁ ++ [.ext (.inl (t₀, t₁))]) sl s

/-- The steps after the challenge outcome `y`. -/
noncomputable def tr₃ (T₂ : List EvP) (y : Option (Bytes × Bytes)) (sl : SlP) (s : ShP R) :
    List EvP :=
  A.run Hb c (fun _ => false) A.L₃ (T₂ ++ [.ext (.inr y)]) sl s

/-- **The reduction**: the two-session table-reading Issuer whose stages run the schedule on the
slices and the tables, the further sessions' tapes `c` fixed. -/
noncomputable def red : AdversaryRA R where
  pk sl s := A.pk (A.tr₁ Hb c sl s)
  msg b sl s := A.msg (A.tr₁ Hb c sl s) b
  respond t₀ t₁ i sl s := A.respond (A.tr₂ Hb c (A.tr₁ Hb c sl s) t₀ t₁ sl s) i
  guess t₀ t₁ y sl s := A.guess (A.tr₃ Hb c (A.tr₂ Hb c (A.tr₁ Hb c sl s) t₀ t₁ sl s) y sl s) sl s

end AdversaryILO

/-- **The interleaved game** in world `b`: the schedule until the challenge, the challenge
requests (the first session on `µ_b`, the second on `µ_{¬b}`), the schedule until the answers, the
outcome, the schedule after it, and the guess; the scheduler reads the challenge slices and the
tables throughout. -/
noncomputable def realGameILO (A : AdversaryILO R) (b : Bool)
    (z : ((XR × XR) × (Fin n → XR)) × ShP R) : Prop :=
  let sl : SlP := (z.1.1.1.2, z.1.1.2.2)
  let T₁ := A.tr₁ Hb z.1.2 sl z.2
  let S₀ := sessX Hb (A.pk T₁) (A.msg T₁ b) z.1.1.1 z.2
  let S₁ := sessX Hb (A.pk T₁) (A.msg T₁ !b) z.1.1.2 z.2
  let T₂ := A.tr₂ Hb z.1.2 T₁ S₀.1 S₁.1 sl z.2
  let y := outcome b (S₀.2 (A.respond T₂ false)) (S₁.2 (A.respond T₂ true))
  A.guess (A.tr₃ Hb z.1.2 T₂ y sl z.2) sl z.2

/-- **The interleaved game is the two-session game of the reduction**, tape by tape. -/
theorem realGameILO_iff (A : AdversaryILO R) (b : Bool) (x : XR × XR) (c : Fin n → XR)
    (s : ShP R) : realGameILO Hb A b ((x, c), s) ↔ realGameRA Hb (A.red Hb c) b (x, s) :=
  Iff.rfl

/-- **The Issuer of `realGameIL` is a special case**: a scheduler that reads no table, starts the
challenge after exactly `L₁` steps and takes the answers after exactly `L₂`. -/
def AdversaryIL.toO (A : AdversaryIL R) : AdversaryILO R where
  L₁ := A.L₁
  L₂ := A.L₂
  L₃ := A.L₃
  next tr := pure (A.next tr)
  go _ := false
  done _ := false
  pk := A.pk
  msg := A.msg
  respond := A.respond
  guess := A.guess

/-- Its scheduler reads nothing. -/
lemma AdversaryIL.toO_sBudget (A : AdversaryIL R) : A.toO.SBudget 0 0 0 0 := fun _ => QBudget.pure _

/-- Its guess's budget is the earlier one. -/
lemma AdversaryIL.Budget.toO {A : AdversaryIL R} {q3 q5 qE : ℕ} (h : A.Budget q3 q5 qE) :
    A.toO.Budget q3 q5 qE := ⟨h.h30, h.h31, h.h5, h.hE⟩

/-- **`realGameILO` extends `realGameIL`.** -/
theorem realGameILO_toO (A : AdversaryIL R) (b : Bool) (z : ((XR × XR) × (Fin n → XR)) × ShP R) :
    realGameILO Hb A.toO b z ↔ realGameIL Hb A b z := by
  simp only [realGameILO, realGameIL, AdversaryILO.tr₁, AdversaryILO.tr₂, AdversaryILO.tr₃,
    AdversaryILO.run, AdversaryIL.tr₁, AdversaryIL.tr₂, AdversaryIL.tr₃, AdversaryIL.run,
    AdversaryIL.toO, runO_pure]

variable {Hb}

namespace AdversaryILO

variable (A : AdversaryILO R) (c : Fin n → XR) (hHb : HashesWF Hb)

/-- Counting the scheduler's queries over three stretches. -/
lemma count3 {A : AdversaryILO R} (c : Fin n → XR) {a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE) (j : Bool) (stop₁ stop₂ stop₃ : List EvP → Bool)
    (L₁ L₂ L₃ : ℕ) (tr₁ tr₂ tr₃ : List EvP) (f : (k : TKey Bool (preLen pP)) → TKey.Ans R k)
    (tb : Tb R pP) :
    let l := (([] ++ logO n (outIL Hb c) A.next stop₁ L₁ tr₁ f tb) ++
      logO n (outIL Hb c) A.next stop₂ L₂ tr₂ f tb) ++ logO n (outIL Hb c) A.next stop₃ L₃ tr₃ f tb
    l.countP (TKey.isH3 j) ≤ (L₁ + L₂ + L₃) * a3 ∧ l.countP TKey.isH2 ≤ (L₁ + L₂ + L₃) * a2 ∧
      l.countP TKey.isH5 ≤ (L₁ + L₂ + L₃) * a5 ∧ l.countP TKey.isIC ≤ (L₁ + L₂ + L₃) * aE := by
  intro l
  have h1 := countP_logO_qb (n := n) (out := outIL Hb c) hN j stop₁ L₁ tr₁ f tb
  have h2 := countP_logO_qb (n := n) (out := outIL Hb c) hN j stop₂ L₂ tr₂ f tb
  have h3 := countP_logO_qb (n := n) (out := outIL Hb c) hN j stop₃ L₃ tr₃ f tb
  simp only [l, List.nil_append, List.countP_append, Nat.add_mul]
  omega

include hHb

/-- The transcripts are good, on the joint tables, for the joint reader. -/
lemma goodP₁ : GoodO (spec := TSpec Bool R (preLen pP)) n (QIL Hb c) rdP
    (fun t : TbP R => ((default : Tab3), t.2)) (fun t => A.tr₁ Hb c t.1 t.2)
    (fun t => [] ++ logO n (outIL Hb c) A.next A.go A.L₁ [] (rdP t) ((default : Tab3), t.2)) :=
  GoodO.run (next := A.next) (sessReads_IL hHb c) A.go A.L₁ (GoodO.const [])

lemma goodP₂ (t₀ t₁ : Bytes) : GoodO (spec := TSpec Bool R (preLen pP)) n (QIL Hb c) rdP
    (fun t : TbP R => ((default : Tab3), t.2)) (fun t => A.tr₂ Hb c (A.tr₁ Hb c t.1 t.2) t₀ t₁ t.1 t.2)
    (fun t => ([] ++ logO n (outIL Hb c) A.next A.go A.L₁ [] (rdP t) ((default : Tab3), t.2)) ++
      logO n (outIL Hb c) A.next A.done A.L₂ (A.tr₁ Hb c t.1 t.2 ++ [.ext (.inl (t₀, t₁))]) (rdP t)
        ((default : Tab3), t.2)) :=
  GoodO.run (next := A.next) (sessReads_IL hHb c) A.done A.L₂ (GoodO.ext (goodP₁ A c hHb) _)

/-- The guess's transcript, on one slice (the other fixed) and the shared tables. -/
lemma good₃ (fT : Tb R pP → (k : TKey Bool (preLen pP)) → TKey.Ans R k) (σ : Tb R pP → SlP)
    (hσ : ∀ t, fT t = rdP (σ t, t.2)) (t₀ t₁ : Bytes) (y : Option (Bytes × Bytes)) :
    GoodO (spec := TSpec Bool R (preLen pP)) n (QIL Hb c) fT (fun t : Tb R pP => ((default : Tab3), t.2))
      (fun t => A.tr₃ Hb c (A.tr₂ Hb c (A.tr₁ Hb c (σ t) t.2) t₀ t₁ (σ t) t.2) y (σ t) t.2)
      (fun t => (([] ++ logO n (outIL Hb c) A.next A.go A.L₁ [] (fT t) ((default : Tab3), t.2)) ++
        logO n (outIL Hb c) A.next A.done A.L₂ (A.tr₁ Hb c (σ t) t.2 ++ [.ext (.inl (t₀, t₁))]) (fT t)
          ((default : Tab3), t.2)) ++
        logO n (outIL Hb c) A.next (fun _ => false) A.L₃
          (A.tr₂ Hb c (A.tr₁ Hb c (σ t) t.2) t₀ t₁ (σ t) t.2 ++ [.ext (.inr y)]) (fT t)
          ((default : Tab3), t.2)) := by
  have h := GoodO.run (fT := fT) (π := fun t : Tb R pP => ((default : Tab3), t.2)) (next := A.next)
    (sessReads_IL hHb c) (fun _ => false) A.L₃
    (GoodO.ext (GoodO.run (next := A.next) (sessReads_IL hHb c) A.done A.L₂ (GoodO.ext (GoodO.run (next := A.next) (sessReads_IL hHb c)
      A.go A.L₁ (GoodO.const (n := n) (Q := QIL Hb c) (fT := fT) (π := fun t : Tb R pP => ((default : Tab3), t.2))
        [])) (.inl (t₀, t₁)))) (.inr y))
  have e : ∀ t, fT t = rdP (σ t, t.2) := hσ
  simp only [tr₃, tr₂, tr₁, run, ← e]
  exact h

variable {A}

/-- **The reduction's interaction budget**: the sessions' reads (`n` prefixes of `H₂³`) and the
scheduler's queries in the steps up to each stage. -/
theorem red_iBudgetHB {a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE) :
    (A.red Hb c).IBudgetHB ((A.L₁ + A.L₂) * a3) (n + (A.L₁ + A.L₂) * a2)
      (n * 624 + (A.L₁ + A.L₂) * a5) (n * 4607 + (A.L₁ + A.L₂) * aE) where
  k := by
    refine (GoodO.sreadsPB_IL hHb c (goodP₁ A c hHb) fun t => ?_).map' fun T =>
      (A.pk T, A.msg T false, A.msg T true)
    have h := fun j => count3 (Hb := Hb) c hN j A.go A.go A.go A.L₁ 0 0 [] [] [] (rdP t) ((default : Tab3), t.2)
    simp only [logO, List.append_nil, Nat.add_zero] at h
    have m : ∀ x, A.L₁ * x ≤ (A.L₁ + A.L₂) * x := fun x => Nat.mul_le_mul_right _ (by omega)
    exact ⟨(h false).1.trans (m _), (h true).1.trans (m _), (h false).2.1.trans (m _),
      (h false).2.2.1.trans (m _), (h false).2.2.2.trans (m _)⟩
  r t₀ t₁ := by
    refine (GoodO.sreadsPB_IL hHb c (goodP₂ A c hHb t₀ t₁) fun t => ?_).map' fun T =>
      (A.respond T false, A.respond T true)
    have h := fun j => count3 (Hb := Hb) c hN j A.go A.done A.done A.L₁ A.L₂ 0 []
      (A.tr₁ Hb c t.1 t.2 ++ [.ext (.inl (t₀, t₁))]) [] (rdP t) ((default : Tab3), t.2)
    simp only [logO, List.append_nil, Nat.add_zero] at h
    exact ⟨(h false).1, (h true).1, (h false).2.1, (h false).2.2.1, (h false).2.2.2⟩

/-- **The guess's transcript is a consistent reader of each slice** (the other fixed) and the
shared tables. -/
lemma sreads₃ {a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE) (j : Bool) (g : Tab3)
    (t₀ t₁ : Bytes) (y : Option (Bytes × Bytes)) :
    let σ : Tab3 → SlP := fun x => bif j then (g, x) else (x, g)
    SReads pP (fun t : Tb R pP => A.tr₃ Hb c (A.tr₂ Hb c (A.tr₁ Hb c (σ t.1) t.2) t₀ t₁ (σ t.1) t.2) y
        (σ t.1) t.2) ((A.L₁ + A.L₂ + A.L₃) * a3) (n * nGrind + (A.L₁ + A.L₂ + A.L₃) * a2)
      (n * 624 + (A.L₁ + A.L₂ + A.L₃) * a5) (n * 4607 + (A.L₁ + A.L₂ + A.L₃) * aE) := by
  intro σ
  have hf : ∀ t : Tb R pP, rdP (σ t.1, t.2) = readAt (sl2 (σ default)) j t := fun t => by
    cases j
    · simp only [σ, Bool.cond_false, readAt, rdP, sl2_f]
    · simp only [σ, Bool.cond_true, readAt, rdP, sl2_t]
  refine GoodO.sreads (j := j) (sessReads_IL hHb c) (fT := fun t => rdP (σ t.1, t.2))
    (fun t t' l hA k hk => by rw [hf t, hf t']; exact read_congr _ j t t' l hA k hk)
    (good₃ A c hHb _ (fun t => σ t.1) (fun _ => rfl) t₀ t₁ y)
    (fun j k h t => ⟨(QIL_card c j k h t).2.1, (QIL_card c j k h t).2.2.1, (QIL_card c j k h t).2.2.2⟩)
    fun t => count3 (Hb := Hb) c hN j _ _ _ _ _ _ _ _ _ _ _

/-- **The reduction's guess budget**: the Issuer's, plus the `n` sessions' and the scheduler's
reads. -/
theorem red_gBudget {q3 q5 qE a3 a2 a5 aE : ℕ} (hN : A.SBudget a3 a2 a5 aE)
    (hA : A.Budget q3 q5 qE) :
    (A.red Hb c).GBudget ((A.L₁ + A.L₂ + A.L₃) * a3 + q3) (n * 624 + (A.L₁ + A.L₂ + A.L₃) * a5 + q5)
      (n * 4607 + (A.L₁ + A.L₂ + A.L₃) * aE + qE) where
  h30 t₀ t₁ y g₁ s := Rd3.bind' (fun _ => rfl) ((sreads₃ c hHb hN false g₁ t₀ t₁ y).rd3 s)
    fun T => hA.h30 T g₁ s
  h31 t₀ t₁ y g₀ s := Rd3.bind' (fun _ => rfl) ((sreads₃ c hHb hN true g₀ t₀ t₁ y).rd3 s)
    fun T => hA.h31 T g₀ s
  h5 t₀ t₁ y sl := Rd5.bind' (m := fun s => A.tr₃ Hb c (A.tr₂ Hb c (A.tr₁ Hb c sl s) t₀ t₁ sl s) y sl s)
    (f := fun T s => A.guess T sl s) (fun _ => rfl) ((sreads₃ c hHb hN false sl.2 t₀ t₁ y).rd5 sl.1)
    fun T => hA.h5 T sl
  hE t₀ t₁ y sl := RdE.bind' (m := fun s => A.tr₃ Hb c (A.tr₂ Hb c (A.tr₁ Hb c sl s) t₀ t₁ sl s) y sl s)
    (f := fun T s => A.guess T sl s) (fun _ => rfl) ((sreads₃ c hHb hN false sl.2 t₀ t₁ y).rdE sl.1)
    fun T => hA.hE T sl

end AdversaryILO

end Game

/-! ## The bound -/

section Bound

variable {n : ℕ}

/-- **PomFRIT blindness with interleaved further sessions, a table-reading scheduler and a free
challenge, for every type of cipher rows** (`ZKRow R`, `ZK2ARow R`; SHAKE as the base record):
`blindnessRAH_lean_numG_pfx` for the reduction, averaged over the further sessions' tapes, at the
interaction budget `IBudgetHB (L₁₂a₃, n + L₁₂a₂, 624n + L₁₂a₅, 4607n + L₁₂a_E)` (`L₁₂ = L₁ + L₂`)
and the guess budget `(La₃ + q₃, 624n + La₅ + q₅, 4607n + La_E + q_E)` (`L = L₁ + L₂ + L₃`). -/
theorem blindnessILO_lean_numG [ZKRow R] [ZK2ARow R] (A : AdversaryILO R) {q3 q5 qE a3 a2 a5 aE : ℕ}
    (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE) :
    |pr (((XR × XR) × (Fin n → XR)) × ShP R) (realGameILO Hashes.shake A false) -
        pr (((XR × XR) × (Fin n → XR)) × ShP R) (realGameILO Hashes.shake A true)| ≤
      4 * ZKRow.εz R pP ((A.L₁ + A.L₂ + A.L₃) * a3 + q3 + 6 * ((A.L₁ + A.L₂) * a3))
          (n * 624 + (A.L₁ + A.L₂ + A.L₃) * a5 + q5 + 6 * (n * 624 + (A.L₁ + A.L₂) * a5) + 1872)
          (n * 4607 + (A.L₁ + A.L₂ + A.L₃) * aE + qE + 6 * (n * 4607 + (A.L₁ + A.L₂) * aE) + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 +
        h23H R ((A.L₁ + A.L₂) * a3) (n + (A.L₁ + A.L₂) * a2) (n * 624 + (A.L₁ + A.L₂) * a5)
          (n * 4607 + (A.L₁ + A.L₂) * aE) := by
  rw [← pr_equiv tapeIL, ← pr_equiv tapeIL]
  exact abs_pr_prod_sub_le _ _ fun c =>
    blindnessRAH_lean_numG_pfx (A.red Hashes.shake c) (A.red_gBudget c hashesWF_shake hN hA)
      (A.red_iBudgetHB c hashesWF_shake hN)

/-- **`blindnessILO_lean_numG` with function rows.** -/
theorem blindnessILO_lean_num (A : AdversaryILO (Blk → Blk)) {q3 q5 qE a3 a2 a5 aE : ℕ}
    (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE) :
    |pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameILO Hashes.shake A false) -
        pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameILO Hashes.shake A true)| ≤
      4 * εRO ((A.L₁ + A.L₂ + A.L₃) * a3 + q3 + 6 * ((A.L₁ + A.L₂) * a3))
          (n * 624 + (A.L₁ + A.L₂ + A.L₃) * a5 + q5 + 6 * (n * 624 + (A.L₁ + A.L₂) * a5) + 1872)
          (n * 4607 + (A.L₁ + A.L₂ + A.L₃) * aE + qE + 6 * (n * 4607 + (A.L₁ + A.L₂) * aE) + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 +
        (if n + (A.L₁ + A.L₂) * a2 = 0 then 0 else
          4 * (1 / 2 ^ 113 + εRO (6 * ((A.L₁ + A.L₂) * a3)) (6 * (n * 624 + (A.L₁ + A.L₂) * a5) + 2184)
            (6 * (n * 4607 + (A.L₁ + A.L₂) * aE) + 18428) +
            (n + (A.L₁ + A.L₂) * a2 + (n + (A.L₁ + A.L₂) * a2) : ℕ) / 2 ^ 128)) :=
  blindnessILO_lean_numG A hA hN

/-- **`blindnessILO_lean_numG` with AES as uniformly random permutations.** -/
theorem blindnessILO_lean_num_perm (A : AdversaryILO (Equiv.Perm Blk)) {q3 q5 qE a3 a2 a5 aE : ℕ}
    (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE) :
    |pr (((XR × XR) × (Fin n → XR)) × ShP (Equiv.Perm Blk)) (realGameILO Hashes.shake A false) -
        pr (((XR × XR) × (Fin n → XR)) × ShP (Equiv.Perm Blk)) (realGameILO Hashes.shake A true)| ≤
      4 * εROPm pP ((A.L₁ + A.L₂ + A.L₃) * a3 + q3 + 6 * ((A.L₁ + A.L₂) * a3))
          (n * 624 + (A.L₁ + A.L₂ + A.L₃) * a5 + q5 + 6 * (n * 624 + (A.L₁ + A.L₂) * a5) + 1872)
          (n * 4607 + (A.L₁ + A.L₂ + A.L₃) * aE + qE + 6 * (n * 4607 + (A.L₁ + A.L₂) * aE) + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 +
        h23H (Equiv.Perm Blk) ((A.L₁ + A.L₂) * a3) (n + (A.L₁ + A.L₂) * a2)
          (n * 624 + (A.L₁ + A.L₂) * a5) (n * 4607 + (A.L₁ + A.L₂) * aE) :=
  blindnessILO_lean_numG A hA hN

/-- **The bound in numbers**: with `n` further sessions and a scheduler within `(a₃, a₂, a₅, a_E)`
per step for `L = L₁ + L₂ + L₃` steps,

    |Pr[W₀] − Pr[W₁]| ≤ (n + 2)·2⁻¹⁰² + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸
                         + 52·L·(a₃ + a₂ + a₅ + 221·a_E)·2⁻¹²⁸. -/
theorem blindnessILO_lean_le (A : AdversaryILO (Blk → Blk)) {q3 q5 qE a3 a2 a5 aE : ℕ}
    (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE) :
    |pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameILO Hashes.shake A false) -
        pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameILO Hashes.shake A true)| ≤
      (n + 2 : ℕ) / 2 ^ 102 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 +
        52 * ((A.L₁ + A.L₂ + A.L₃) * (a3 + a2 + a5 + 221 * aE) : ℕ) / 2 ^ 128 := by
  have h := blindnessILO_lean_num (n := n) A hA hN
  have u3 : (A.L₁ + A.L₂) * a3 ≤ (A.L₁ + A.L₂ + A.L₃) * a3 := Nat.mul_le_mul_right _ (by omega)
  have u2 : (A.L₁ + A.L₂) * a2 ≤ (A.L₁ + A.L₂ + A.L₃) * a2 := Nat.mul_le_mul_right _ (by omega)
  have u5 : (A.L₁ + A.L₂) * a5 ≤ (A.L₁ + A.L₂ + A.L₃) * a5 := Nat.mul_le_mul_right _ (by omega)
  have uE : (A.L₁ + A.L₂) * aE ≤ (A.L₁ + A.L₂ + A.L₃) * aE := Nat.mul_le_mul_right _ (by omega)
  have eS : (A.L₁ + A.L₂ + A.L₃) * (a3 + a2 + a5 + 221 * aE) = (A.L₁ + A.L₂ + A.L₃) * a3 +
      (A.L₁ + A.L₂ + A.L₃) * a2 + (A.L₁ + A.L₂ + A.L₃) * a5 + 221 * ((A.L₁ + A.L₂ + A.L₃) * aE) := by
    ring
  rw [eS]
  generalize (A.L₁ + A.L₂) * a3 = x3 at h u3
  generalize (A.L₁ + A.L₂) * a2 = x2 at h u2
  generalize (A.L₁ + A.L₂) * a5 = x5 at h u5
  generalize (A.L₁ + A.L₂) * aE = xE at h uE
  generalize (A.L₁ + A.L₂ + A.L₃) * a3 = y3 at h u3 ⊢
  generalize (A.L₁ + A.L₂ + A.L₃) * a2 = y2 at h u2 ⊢
  generalize (A.L₁ + A.L₂ + A.L₃) * a5 = y5 at h u5 ⊢
  generalize (A.L₁ + A.L₂ + A.L₃) * aE = yE at h uE ⊢
  have hn := noHitProb_le_128
  have e : ∀ x : ℝ, x / 2 ^ 102 = x * 67108864 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have e113 : (1 : ℝ) / 2 ^ 113 = 32768 / 2 ^ 128 := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have h1 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have r3 : (x3 : ℝ) ≤ y3 := by exact_mod_cast u3
  have r2 : (x2 : ℝ) ≤ y2 := by exact_mod_cast u2
  have r5 : (x5 : ℝ) ≤ y5 := by exact_mod_cast u5
  have rE : (xE : ℝ) ≤ yE := by exact_mod_cast uE
  have p3 : (0 : ℝ) ≤ x3 := Nat.cast_nonneg _
  have p2 : (0 : ℝ) ≤ x2 := Nat.cast_nonneg _
  have p5 : (0 : ℝ) ≤ x5 := Nat.cast_nonneg _
  have pE : (0 : ℝ) ≤ xE := Nat.cast_nonneg _
  unfold εRO at h
  rw [e113] at h
  split_ifs at h with h0
  · push_cast at h ⊢
    rw [e]
    linarith
  · push_cast at h ⊢
    rw [e]
    linarith

/-- **`2²⁰` sessions**: `≤ 2⁻⁸²` plus the guess's and the scheduler's budget terms. -/
theorem blindnessILO_lean_2pow20 (A : AdversaryILO (Blk → Blk)) {q3 q5 qE a3 a2 a5 aE : ℕ}
    (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE) (hn : n + 2 ≤ 2 ^ 20) :
    |pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameILO Hashes.shake A false) -
        pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameILO Hashes.shake A true)| ≤
      1 / 2 ^ 82 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 +
        52 * ((A.L₁ + A.L₂ + A.L₃) * (a3 + a2 + a5 + 221 * aE) : ℕ) / 2 ^ 128 := by
  have h := blindnessILO_lean_le (n := n) A hA hN
  have : ((n + 2 : ℕ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hn
  have h2 : ((n + 2 : ℕ) : ℝ) / 2 ^ 102 ≤ 1 / 2 ^ 82 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **`2³²` sessions**: `≤ 2⁻⁷⁰` plus the guess's and the scheduler's budget terms. -/
theorem blindnessILO_lean_2pow32 (A : AdversaryILO (Blk → Blk)) {q3 q5 qE a3 a2 a5 aE : ℕ}
    (hA : A.Budget q3 q5 qE) (hN : A.SBudget a3 a2 a5 aE) (hn : n + 2 ≤ 2 ^ 32) :
    |pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameILO Hashes.shake A false) -
        pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameILO Hashes.shake A true)| ≤
      1 / 2 ^ 70 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 +
        52 * ((A.L₁ + A.L₂ + A.L₃) * (a3 + a2 + a5 + 221 * aE) : ℕ) / 2 ^ 128 := by
  have h := blindnessILO_lean_le (n := n) A hA hN
  have : ((n + 2 : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have h2 : ((n + 2 : ℕ) : ℝ) / 2 ^ 102 ≤ 1 / 2 ^ 70 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end Bound

end VoleMole.Privacy.PomFRIT
