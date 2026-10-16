import VoleMole.Privacy.PomFRITAdaptivePfx
import VoleMole.ZK.ReadsInterleave

/-!
# PomFRIT blindness with interleaved further sessions

`Privacy/PomFRITAdaptive.lean` lets the Issuer start further sessions after seeing earlier
outcomes, but each further session runs to the end (request, response, outcome) before the next
starts. Here the Issuer is an **interactive machine that schedules the further sessions
arbitrarily**: at each step it either starts a new honest Client session with a key and message of
its choice (and sees the request) or delivers a response to any pending session (and sees the
outcome), choosing from everything it has seen; it may start many sessions and answer them in any
order, before, during and after the challenge.

## The game

`AdversaryIL`: a step function `next` from the transcript to an action (`ZK.Sim.Act`: start a
session with `(pk, msg)`, or send a response to session `j`), the challenge key and messages
`pk`, `msg`, the challenge responses `respond` and the guess, each a function of the transcript,
and the numbers of steps `L₁`, `L₂`, `L₃` before the challenge requests, between them and the
challenge responses, and after the challenge outcome. (Fixed step counts lose nothing: an action
that is refused, a message to a session that does not exist, is a no-op.) The game
(`realGameIL`) runs the further sessions with tapes `c : Fin n → XR` (the `j`-th session started
uses `c j`; starts beyond `n` are refused), the challenge between the phases as in every PomFRIT
game (the two challenge requests appear in the transcript, then the outcome, the signatures in
message order if both sessions complete), and the guess on the whole transcript, the challenge
slices and the tables. A further session's state is its tape and the messages it has received;
a second response to a finished session is answered with its outcome again.

## The reduction

For each `c` the game is the two-session game with an Issuer that reads the tables, `H₂³`
included (`realGameIL_iff`, `Iff.rfl`), for the Issuer `A.red c` that runs the schedule itself:
its key stage the steps before the challenge, its response stage also those between the challenge
requests and responses, its guess also those after. Its budget comes from the interleaving lemma
(`ZK/ReadsInterleave.lean`, `Good.run`): a session's output after `h` is read off `QIL` (step 1's
keys for the request, `fullKeys` of `Privacy/PomFRITAdaptive.lean` once a response arrived), which
grows with the messages (`sessReads_IL`), so the whole interleaved run is a consistent reader with
`n` times one session's reads: `IBudgetHB 0 n (n·624) (n·4607)` (`red_iBudgetHB`: one `H₂³`
prefix per session, `fullKeys_pfx`) and guess `(q₃, q₅ + n·624, q_E + n·4607)` (`red_gBudget`).

## The bound

`blindnessRAH_lean_numG_pfx` for every `c`, averaged over `c`: `blindnessIL_lean_numG`,
`blindnessIL_lean_num`, `blindnessIL_lean_num_perm`; in numbers (`blindnessIL_lean_le`)
`≤ (n + 2)·2⁻¹⁰² + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸` for `n` further sessions, whatever the schedule
and the number of steps: `2⁻⁸²` at `n + 2 ≤ 2²⁰`, `2⁻⁷⁰` at `n + 2 ≤ 2³²`
(`blindnessIL_lean_2pow20`, `_2pow32`). This is the bound of `blindnessAd_lean_le_pfx` with every
further session counted as one run inside the interaction.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT

attribute [local irreducible] commitRefresher UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-! ## A further session, step by step -/

section Sess

variable {Hb : Hashes}

/-- **A whole further session is read off `fullKeys`** (the read sets of `fullX_sreads`). -/
lemma fullX_cons (hHb : HashesWF Hb) (pk : UOVKey) (msg : Bytes) (ρ : Bytes → Bytes) (x : XR)
    (t t' : Tb R pP) (h : AgT (fullKeys (Hb := Hb) pk msg ρ x t.2) t t') :
    fullKeys (Hb := Hb) pk msg ρ x t'.2 = fullKeys (Hb := Hb) pk msg ρ x t.2 ∧
      fullX Hb pk msg ρ x t'.2 = fullX Hb pk msg ρ x t.2 := by
  classical
  obtain ⟨-, h2, h5, hE⟩ := h
  obtain ⟨g, G2, s₂⟩ := t
  obtain ⟨g', G2', s₂'⟩ := t'
  dsimp only at h2 h5 hE ⊢
  obtain ⟨e5, eE, eS, eT⟩ := full_step1 hHb pk msg ρ x (G2, s₂) (G2', s₂') h5 hE
  have eP := preX_cons hHb pk msg ρ x (G2, s₂) (G2', s₂') h5 hE
  refine ⟨?_, ?_⟩
  · unfold fullKeys
    rw [eT, eP, e5, eE]
  · unfold fullX
    rw [sessX_eq_tR pk msg ρ x (G2', s₂'), sessX_eq_tR pk msg ρ x (G2, s₂)]
    dsimp only
    rw [eT]
    refine Prod.ext rfl ?_
    dsimp only
    cases hv : validB (respAdv (R := R) pk msg ρ) (ρ (tR Hb (respAdv pk msg ρ) msg x (G2, s₂)))
        (tR Hb (respAdv pk msg ρ) msg x (G2, s₂))
    · exact finish_of_not_valid (respAdv pk msg ρ) _ _ _ _ hv
    · rw [sigR_tables hHb _ msg x (G2, s₂) (G2', s₂') eS]
      dsimp only
      rw [sigR_h23 hHb pk msg ρ x G2 G2' s₂ hv fun κ hκ => h2 κ (by
        unfold fullKeys; rw [hv]; exact hκ)]

/-- A session's request is computed from step 1. -/
lemma sessX_fst (pk : UOVKey) (msg : Bytes) (x : XR) (s : ShP R) :
    (sessX Hb pk msg x s).1 = tOf (keyAdv (R := R) pk) msg x.1.2.1 x.1.2.2 (s1R Hb x s) := by
  rw [sessX_eq]
  rfl

/-- A further session's input: the key and the message. -/
abbrev CfgP := UOVKey × Bytes

/-- What a further session outputs: its request (when started), or its outcome (on a response). -/
abbrev OutP := Bytes ⊕ Except Error (Option Bytes)

/-- The challenge's events in the transcript: the two challenge requests, then the outcome. -/
abbrev ExtP := (Bytes × Bytes) ⊕ Option (Bytes × Bytes)

/-- **The Issuer's view of the schedule**: its actions with their results, and the challenge's
events. -/
abbrev EvP := Ev CfgP Bytes OutP ExtP

/-- An action of the Issuer: start a further session, or send a response to one. -/
abbrev ActP := Act CfgP Bytes

variable {n : ℕ}

/-- The tape of the `j`-th session started (sessions beyond `n` are never started). -/
def tapeAt (c : Fin n → XR) (j : ℕ) : XR := if h : j < n then c ⟨j, h⟩ else default

variable (Hb) in
/-- **Further session `j`, configured `k`, after the responses `h`**: its request if it has
received none, else its outcome on the first response (a finished session repeats it). -/
noncomputable def outIL (c : Fin n → XR) (j : ℕ) (k : CfgP) : List Bytes → Tb R pP → OutP
  | [], t => .inl (sessX Hb k.1 k.2 (tapeAt c j) t.2).1
  | r :: _, t => .inr ((sessX Hb k.1 k.2 (tapeAt c j) t.2).2 r)

variable (Hb) in
/-- **What session `j` has read after the responses `h`**: step 1's keys, and once a response
arrived the grinding points of its prefix (`fullKeys`). -/
noncomputable def QIL (c : Fin n → XR) (j : ℕ) (k : CfgP) : List Bytes → Tb R pP → RS pP
  | [], t => s1Keys Hb (tapeAt c j) t.2
  | r :: _, t => fullKeys (Hb := Hb) k.1 k.2 (fun _ => r) (tapeAt c j) t.2

/-- **A further session is a stateful consistent reader**: read off `QIL`, which grows with the
responses. -/
theorem sessReads_IL (hHb : HashesWF Hb) (c : Fin n → XR) :
    SessReads (outIL (R := R) Hb c) (QIL Hb c) where
  cons j k h t t' hA := by
    cases h with
    | nil =>
      obtain ⟨e1, e2⟩ := s1Keys_cons hHb (tapeAt c j) t.2 t'.2 hA.2.2.1 hA.2.2.2
      refine ⟨e1, ?_⟩
      simp only [outIL, sessX_fst, e2]
    | cons r h =>
      obtain ⟨e1, e2⟩ := fullX_cons hHb k.1 k.2 (fun _ => r) (tapeAt c j) t t' hA
      exact ⟨e1, congrArg (fun z : Bytes × Except Error (Option Bytes) => (Sum.inr z.2 : OutP)) e2⟩
  mono j k h m t := by
    cases h with
    | nil => exact ⟨subset_rfl, empty_subset _, subset_rfl, subset_rfl⟩
    | cons r h => exact RS.Le.refl _

lemma QIL_card (c : Fin n → XR) (j : ℕ) (k : CfgP) (h : List Bytes) (t : Tb R pP) :
    (QIL Hb c j k h t).1.card ≤ 0 ∧ (QIL Hb c j k h t).2.1.card ≤ nGrind ∧
      (QIL Hb c j k h t).2.2.1.card ≤ 624 ∧ (QIL Hb c j k h t).2.2.2.card ≤ 4607 := by
  cases h with
  | nil => exact ⟨by simp [QIL, s1Keys], by simp [QIL, s1Keys], (s1Keys_card _ _).1, (s1Keys_card _ _).2⟩
  | cons r h =>
    refine ⟨by simp [QIL, fullKeys], ?_, (s1Keys_card (Hb := Hb) _ t.2).1,
      (s1Keys_card (Hb := Hb) _ t.2).2⟩
    show (fullKeys (Hb := Hb) k.1 k.2 (fun _ => r) (tapeAt c j) t.2).2.1.card ≤ nGrind
    unfold fullKeys
    split_ifs
    · exact card_image_le.trans (by rw [card_univ, Fintype.card_fin])
    · simp

lemma QIL_pfx (c : Fin n → XR) (j : ℕ) (k : CfgP) (h : List Bytes) (t : Tb R pP) :
    ((QIL Hb c j k h t).2.1.image Prod.fst).card ≤ 1 := by
  cases h with
  | nil => simp [QIL, s1Keys]
  | cons r h => exact fullKeys_pfx k.1 k.2 (fun _ => r) (tapeAt c j) t.2

/-- **Interleaved further sessions are a consistent reader**, `n` times a session's keys. -/
theorem Good.sreads_IL (hHb : HashesWF Hb) (c : Fin n → XR) {F : Tb R pP → List EvP}
    (hF : Good n (QIL Hb c) F) : SReads pP F 0 (n * nGrind) (n * 624) (n * 4607) := by
  simpa using hF.sreads (sessReads_IL hHb c) (QIL_card c)

/-- **Interleaved further sessions are a consistent reader, `H₂³` at `n` prefixes.** -/
theorem Good.sreadsB_IL (hHb : HashesWF Hb) (c : Fin n → XR) {F : Tb R pP → List EvP}
    (hF : Good n (QIL Hb c) F) : SReadsB pP F 0 n (n * 624) (n * 4607) := by
  classical
  refine ⟨fun t => RQl (QIL Hb c) t 0 (sessSt n (F t)), fun t t' h => hF.cons (sessReads_IL hHb c) t t' h,
    fun t => ?_⟩
  have hl := sessSt_length_le n (F t)
  have c1 := card_RQl (Q := QIL Hb c) (fun r => r.1) (fun _ _ => rfl) rfl t
    (fun j k h => (QIL_card c j k h t).1) (sessSt n (F t)) 0
  have c2 := card_RQl (Q := QIL Hb c) (fun r => r.2.1.image Prod.fst)
    (fun r r' => image_union _ _) (image_empty _) t (fun j k h => QIL_pfx c j k h t) (sessSt n (F t)) 0
  have c3 := card_RQl (Q := QIL Hb c) (fun r => r.2.2.1) (fun _ _ => rfl) rfl t
    (fun j k h => (QIL_card c j k h t).2.2.1) (sessSt n (F t)) 0
  have c4 := card_RQl (Q := QIL Hb c) (fun r => r.2.2.2) (fun _ _ => rfl) rfl t
    (fun j k h => (QIL_card c j k h t).2.2.2) (sessSt n (F t)) 0
  refine ⟨?_, ?_, c3.trans (Nat.mul_le_mul_right _ hl), c4.trans (Nat.mul_le_mul_right _ hl)⟩
  · simpa using c1
  · simpa using c2.trans (Nat.mul_le_mul_right _ hl)

end Sess

/-! ## The interleaved game -/

section Game

variable {n : ℕ}

/-- **The Issuer of the interleaved game**: `L₁` steps before the challenge, `L₂` between the
challenge requests and the challenge responses, `L₃` after the challenge outcome; at each step
the next action (start a further session with a key and message, or send a response to a pending
one) from the transcript so far; the challenge key and messages, the challenge responses and the
guess from the transcript. The interaction does not read the tables itself (the sessions it runs
do). -/
structure AdversaryIL (R : Type) where
  L₁ : ℕ
  L₂ : ℕ
  L₃ : ℕ
  next : List EvP → ActP
  pk : List EvP → UOVKey
  msg : List EvP → Bool → Bytes
  respond : List EvP → Bool → Bytes
  guess : List EvP → SlP → ShP R → Prop

/-- **The guess's budget**: each challenge slice at `q3` keys, `H₅` at `q5`, the cipher at `qE`;
`H₂³` freely. -/
structure AdversaryIL.Budget (A : AdversaryIL R) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ T (g₁ : Tab3) s, Rd3 (fun g => A.guess T (g, g₁) s) q3
  h31 : ∀ T (g₀ : Tab3) s, Rd3 (fun g => A.guess T (g₀, g) s) q3
  h5 : ∀ T sl, Rd5 (A.guess T sl) q5
  hE : ∀ T sl, RdE (A.guess T sl) qE

variable (Hb : Hashes)

namespace AdversaryIL

variable (A : AdversaryIL R) (c : Fin n → XR)

/-- `L` steps of the schedule from the transcript `tr`, on the tables `s`. -/
noncomputable def run (L : ℕ) (tr : List EvP) (s : ShP R) : List EvP :=
  runT n (outIL Hb c) A.next L tr ((default : Tab3), s)

/-- The steps before the challenge. -/
noncomputable def tr₁ (s : ShP R) : List EvP := A.run Hb c A.L₁ [] s

/-- The steps between the challenge requests `t₀`, `t₁` and the challenge responses. -/
noncomputable def tr₂ (T₁ : List EvP) (t₀ t₁ : Bytes) (s : ShP R) : List EvP :=
  A.run Hb c A.L₂ (T₁ ++ [.ext (.inl (t₀, t₁))]) s

/-- The steps after the challenge outcome `y`. -/
noncomputable def tr₃ (T₂ : List EvP) (y : Option (Bytes × Bytes)) (s : ShP R) : List EvP :=
  A.run Hb c A.L₃ (T₂ ++ [.ext (.inr y)]) s

/-- **The reduction**: the two-session Issuer whose interaction runs the schedule itself, the
further sessions' tapes `c` fixed: its key stage the steps before the challenge, its response stage
also those up to the challenge responses, its guess also those after. -/
noncomputable def red : AdversaryRA R where
  pk _ s := A.pk (A.tr₁ Hb c s)
  msg b _ s := A.msg (A.tr₁ Hb c s) b
  respond t₀ t₁ i _ s := A.respond (A.tr₂ Hb c (A.tr₁ Hb c s) t₀ t₁ s) i
  guess t₀ t₁ y sl s := A.guess (A.tr₃ Hb c (A.tr₂ Hb c (A.tr₁ Hb c s) t₀ t₁ s) y s) sl s

end AdversaryIL

/-- **The interleaved game** in world `b`: the schedule's first `L₁` steps, the challenge requests
(the first session on `µ_b`, the second on `µ_{¬b}`), `L₂` more steps, the challenge responses and
outcome, `L₃` more steps, and the guess. -/
noncomputable def realGameIL (A : AdversaryIL R) (b : Bool) (z : ((XR × XR) × (Fin n → XR)) × ShP R) :
    Prop :=
  let T₁ := A.tr₁ Hb z.1.2 z.2
  let S₀ := sessX Hb (A.pk T₁) (A.msg T₁ b) z.1.1.1 z.2
  let S₁ := sessX Hb (A.pk T₁) (A.msg T₁ !b) z.1.1.2 z.2
  let T₂ := A.tr₂ Hb z.1.2 T₁ S₀.1 S₁.1 z.2
  let y := outcome b (S₀.2 (A.respond T₂ false)) (S₁.2 (A.respond T₂ true))
  A.guess (A.tr₃ Hb z.1.2 T₂ y z.2) (z.1.1.1.2, z.1.1.2.2) z.2

/-- **The interleaved game is the two-session game of the reduction**, tape by tape. -/
theorem realGameIL_iff (A : AdversaryIL R) (b : Bool) (x : XR × XR) (c : Fin n → XR) (s : ShP R) :
    realGameIL Hb A b ((x, c), s) ↔ realGameRA Hb (A.red Hb c) b (x, s) :=
  Iff.rfl

variable {Hb}

namespace AdversaryIL

variable (A : AdversaryIL R) (c : Fin n → XR)

/-- The schedule reads no slice. -/
lemma run_snd (L : ℕ) (tr : List EvP) (t : Tb R pP) :
    A.run Hb c L tr t.2 = runT n (outIL Hb c) A.next L tr t :=
  runT_congr_out (fun j k h => by cases h <;> rfl) L tr

variable (hHb : HashesWF Hb)
include hHb

lemma good₁ : Good n (QIL Hb c) (fun t : Tb R pP => runT n (outIL Hb c) A.next A.L₁ [] t) :=
  Good.run (next := A.next) (sessReads_IL hHb c) A.L₁ (Good.const (n := n) (Q := QIL Hb c) ([] : List EvP))

lemma good₂ (t₀ t₁ : Bytes) : Good n (QIL Hb c) (fun t : Tb R pP =>
    runT n (outIL Hb c) A.next A.L₂ (runT n (outIL Hb c) A.next A.L₁ [] t ++ [.ext (.inl (t₀, t₁))]) t) :=
  Good.run (sessReads_IL hHb c) A.L₂ (Good.ext (good₁ A c hHb) _)

lemma good₃ (t₀ t₁ : Bytes) (y : Option (Bytes × Bytes)) : Good n (QIL Hb c) (fun t : Tb R pP =>
    runT n (outIL Hb c) A.next A.L₃ (runT n (outIL Hb c) A.next A.L₂
      (runT n (outIL Hb c) A.next A.L₁ [] t ++ [.ext (.inl (t₀, t₁))]) t ++ [.ext (.inr y)]) t) :=
  Good.run (sessReads_IL hHb c) A.L₃ (Good.ext (good₂ A c hHb t₀ t₁) _)

/-- **The reduction's interaction budget**: the key stage and the response stage each run the
interleaved schedule up to that point, `n` sessions in all: `H₂³` at `n` prefixes, `n·624` `H₅`
keys and `n·4607` cipher keys, whatever the schedule. -/
theorem red_iBudgetHB : (A.red Hb c).IBudgetHB 0 n (n * 624) (n * 4607) where
  k := by
    have h := (Good.sreadsB_IL hHb c (good₁ A c hHb)).map fun T => (A.pk T, A.msg T false, A.msg T true)
    refine SReadsPB.of_shared (f := fun s => (A.red Hb c).keyOf (default, default) s) ?_ 0
    refine (congrArg (fun F => SReadsB pP F 0 n (n * 624) (n * 4607)) (funext fun t => ?_)).mp h
    simp only [AdversaryRA.keyOf, red, tr₁, run_snd]
  r t₀ t₁ := by
    have h := (Good.sreadsB_IL hHb c (good₂ A c hHb t₀ t₁)).map fun T => (A.respond T false, A.respond T true)
    refine SReadsPB.of_shared (f := fun s => (A.red Hb c).respOf t₀ t₁ (default, default) s) ?_ 0
    refine (congrArg (fun F => SReadsB pP F 0 n (n * 624) (n * 4607)) (funext fun t => ?_)).mp h
    simp only [AdversaryRA.respOf, red, tr₁, tr₂, run_snd]

/-- **The reduction's guess budget**: the Issuer's plus the `n` further sessions' `H₅` and cipher
reads. -/
theorem red_gBudget {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    (A.red Hb c).GBudget q3 (n * 624 + q5) (n * 4607 + qE) where
  h30 _ _ _ g₁ s := hA.h30 _ g₁ s
  h31 _ _ _ g₀ s := hA.h31 _ g₀ s
  h5 t₀ t₁ y sl := Rd5.bindEq (m := fun s => A.tr₃ Hb c (A.tr₂ Hb c (A.tr₁ Hb c s) t₀ t₁ s) y s)
    (f := fun T s => A.guess T sl s) (fun _ => rfl)
    ((Good.sreads_IL hHb c (good₃ A c hHb t₀ t₁ y)).rd5 default) fun T => hA.h5 T sl
  hE t₀ t₁ y sl := RdE.bindEq (m := fun s => A.tr₃ Hb c (A.tr₂ Hb c (A.tr₁ Hb c s) t₀ t₁ s) y s)
    (f := fun T s => A.guess T sl s) (fun _ => rfl)
    ((Good.sreads_IL hHb c (good₃ A c hHb t₀ t₁ y)).rdE default) fun T => hA.hE T sl

end AdversaryIL

/-- The interleaved game's tape, with the further sessions' tapes first. -/
def tapeIL : (Fin n → XR) × ((XR × XR) × ShP R) ≃ ((XR × XR) × (Fin n → XR)) × ShP R where
  toFun z := ((z.2.1, z.1), z.2.2)
  invFun z := (z.1.2, (z.1.1, z.2))
  left_inv _ := rfl
  right_inv _ := rfl

end Game

/-! ## The bound -/

section Bound

variable {n : ℕ}

/-- **PomFRIT blindness with interleaved further sessions, for every type of cipher rows**
(`ZKRow R`, `ZK2ARow R`; SHAKE as the base record): with at most `n` further sessions, scheduled,
started and answered in any order by the Issuer,

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q₃, q₅ + 7n·624 + 1872, q_E + 7n·4607 + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸ + h23H(0, n, n·624, n·4607)

(`blindnessRAH_lean_numG_pfx` for the reduction that runs the schedule, averaged over the
further sessions' tapes). -/
theorem blindnessIL_lean_numG [ZKRow R] [ZK2ARow R] (A : AdversaryIL R) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × (Fin n → XR)) × ShP R) (realGameIL Hashes.shake A false) -
        pr (((XR × XR) × (Fin n → XR)) × ShP R) (realGameIL Hashes.shake A true)| ≤
      4 * ZKRow.εz R pP (q3 + 6 * 0) (n * 624 + q5 + 6 * (n * 624) + 1872)
          (n * 4607 + qE + 6 * (n * 4607) + 23035) + 2 * noHitProb + 2 / 2 ^ 128 +
        h23H R 0 n (n * 624) (n * 4607) := by
  rw [← pr_equiv tapeIL, ← pr_equiv tapeIL]
  exact abs_pr_prod_sub_le _ _ fun c =>
    blindnessRAH_lean_numG_pfx (A.red Hashes.shake c) (A.red_gBudget c hashesWF_shake hA)
      (A.red_iBudgetHB c hashesWF_shake)

/-- **PomFRIT blindness with interleaved further sessions** (function rows). -/
theorem blindnessIL_lean_num (A : AdversaryIL (Blk → Blk)) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameIL Hashes.shake A false) -
        pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameIL Hashes.shake A true)| ≤
      4 * εRO (q3 + 6 * 0) (n * 624 + q5 + 6 * (n * 624) + 1872)
          (n * 4607 + qE + 6 * (n * 4607) + 23035) + 2 * noHitProb + 2 / 2 ^ 128 +
        (if n = 0 then 0 else
          4 * (1 / 2 ^ 113 + εRO (6 * 0) (6 * (n * 624) + 2184) (6 * (n * 4607) + 18428) +
            (n + n : ℕ) / 2 ^ 128)) :=
  blindnessIL_lean_numG A hA

/-- **PomFRIT blindness with interleaved further sessions and AES as uniformly random
permutations.** -/
theorem blindnessIL_lean_num_perm (A : AdversaryIL (Equiv.Perm Blk)) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × (Fin n → XR)) × ShP (Equiv.Perm Blk)) (realGameIL Hashes.shake A false) -
        pr (((XR × XR) × (Fin n → XR)) × ShP (Equiv.Perm Blk)) (realGameIL Hashes.shake A true)| ≤
      4 * εROPm pP (q3 + 6 * 0) (n * 624 + q5 + 6 * (n * 624) + 1872)
          (n * 4607 + qE + 6 * (n * 4607) + 23035) + 2 * noHitProb + 2 / 2 ^ 128 +
        h23H (Equiv.Perm Blk) 0 n (n * 624) (n * 4607) :=
  blindnessIL_lean_numG A hA

/-- **The interleaved bound in numbers**: with `n` further sessions (`n + 2` in all),

    |Pr[W₀] − Pr[W₁]| ≤ (n + 2)·2⁻¹⁰² + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸,

for every schedule and every number of steps. -/
theorem blindnessIL_lean_le (A : AdversaryIL (Blk → Blk)) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameIL Hashes.shake A false) -
        pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameIL Hashes.shake A true)| ≤
      (n + 2 : ℕ) / 2 ^ 102 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessIL_lean_num (n := n) A hA
  have hn := noHitProb_le_128
  have e : ∀ x : ℝ, x / 2 ^ 102 = x * 67108864 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have e113 : (1 : ℝ) / 2 ^ 113 = 32768 / 2 ^ 128 := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have h1 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  unfold εRO at h
  rw [e113] at h
  split_ifs at h with h0
  · push_cast at h ⊢
    rw [e]
    linarith
  · push_cast at h ⊢
    rw [e]
    linarith

/-- **`2²⁰` sessions**: `≤ 2⁻⁸²` plus the guess's budget terms. -/
theorem blindnessIL_lean_2pow20 (A : AdversaryIL (Blk → Blk)) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE)
    (hn : n + 2 ≤ 2 ^ 20) :
    |pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameIL Hashes.shake A false) -
        pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameIL Hashes.shake A true)| ≤
      1 / 2 ^ 82 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessIL_lean_le (n := n) A hA
  have : ((n + 2 : ℕ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hn
  have h2 : ((n + 2 : ℕ) : ℝ) / 2 ^ 102 ≤ 1 / 2 ^ 82 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **`2³²` sessions**: `≤ 2⁻⁷⁰` plus the guess's budget terms. -/
theorem blindnessIL_lean_2pow32 (A : AdversaryIL (Blk → Blk)) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE)
    (hn : n + 2 ≤ 2 ^ 32) :
    |pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameIL Hashes.shake A false) -
        pr (((XR × XR) × (Fin n → XR)) × ShP (Blk → Blk)) (realGameIL Hashes.shake A true)| ≤
      1 / 2 ^ 70 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessIL_lean_le (n := n) A hA
  have : ((n + 2 : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have h2 : ((n + 2 : ℕ) : ℝ) / 2 ^ 102 ≤ 1 / 2 ^ 70 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end Bound

end VoleMole.Privacy.PomFRIT
