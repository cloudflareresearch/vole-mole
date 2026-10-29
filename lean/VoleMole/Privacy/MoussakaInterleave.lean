import VoleMole.Privacy.MoussakaAdaptive
import VoleMole.ZK.ReadsInterleave

/-!
# Moussaka issuer hiding and unlinkability with interleaved further sessions

`Privacy/MoussakaAdaptive.lean` lets the colluding adversary start further sessions after seeing
earlier outcomes, each run to the end before the next starts. Here the adversary is an
**interactive machine that schedules the further Clients arbitrarily**: at each step it either
starts a new honest Client with contexts and an issuing key of its choice (`CfgX`; it sees the
issuance request) or delivers to a pending Client its answer (`AnsX`: the response, and the Anchor
Set and digest to redeem at; it sees the redemption request), choosing from everything it has seen,
before, during and after the challenge.

## The game

`AdversaryILM`: a step function `next` from the transcript to an action (`ZK.Sim.Act`), the
challenge contexts and keys, the challenge responses and Anchor Sets, and the guess, each from the
transcript, and the numbers of steps `L₁`, `L₂`, `L₃` before the challenge issuance requests,
between them and the challenge answers, and after the challenge outcome. `realGameILM`: the
further Clients have tapes `c : Fin n → XC` (the `j`-th started uses `c j`; starts beyond `n` are
refused), the challenge as in `realGameAdM` (§6's rule, `outAt`).

## The reduction

A further Client is a chain (`ZK/ReadsInterleave.lean`, `ChainCons`) of two consistent readers:
its issuance request (`issX_req_sreads`) and, on the first answer, its redemption request
(`redX_sreads`; later answers are ignored). By the interleaving lemma (`Good.run`, `Good.sreads`)
every stretch of the schedule is a consistent reader with `n` times one Client's reads
`(0, 2·2³², 1248, 9214)`. For each `c` the game is the key-stage game (`Privacy/MoussakaRAK.lean`)
of the adversary `A.red idx c` whose key stage runs the steps before the challenge, whose
interaction (at the key stage's transcript) the steps up to the challenge answers and whose guess
the rest (`realGameILM_iff`, `Iff.rfl`). Budgets: key stage and interaction both
`(0, 2·2³²n, 1248n, 9214n)` (`red_kBudget`, `red_iBudget`), guess `(q₃, q₅ + 1248n, q_E + 9214n)`
(`red_gBudget`): a Client started before the challenge and answered after it is read by the key
stage, the interaction and the guess.

## The bound

`anonymityRAK_lean_numG` for every `c`, averaged: `anonymityIL_lean_numG`, `_num`, `_num_perm`; in
numbers (`anonymityIL_lean_le`) `≤ (n + 2)·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide` for `n`
further Clients, whatever the schedule: `2⁻⁸¹` at `n + 2 ≤ 2²⁰`, `2⁻⁶⁹` at `n + 2 ≤ 2³²`
(`anonymityIL_lean_2pow20`, `_2pow32`; exactly, per Client `≈ 2⁻¹⁰¹·¹³`, constant `≈ 2⁻¹⁰¹·⁹⁴`),
twice the sequential schedule's `n·2⁻¹⁰²`: each Client is charged in the key stage and in the
interaction. Hiding of `Com` is assumed for the reductions of every `A.red idx c`.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

attribute [local irreducible] com UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [Inhabited R] [CipherRow R]

/-! ## A further Client, step by step -/

section Sess

/-- What a further Client outputs: its issuance request, or its redemption request. -/
abbrev OutM := Bytes ⊕ Except Error Bytes

/-- The challenge's events in the transcript: the two issuance requests, then the outcome. -/
abbrev ExtM := (Bytes × Bytes) ⊕ Option (Except Error Bytes × Except Error Bytes)

/-- **The adversary's view of the schedule.** -/
abbrev EvM := Ev CfgX AnsX OutM ExtM

/-- An action: start a further Client, or answer one. -/
abbrev ActM := Act CfgX AnsX

variable {n : ℕ}

/-- The tape of the `j`-th Client started. -/
def tapeAtM (c : Fin n → XC) (j : ℕ) : XC := if h : j < n then c ⟨j, h⟩ else default

/-- A further Client's pending token (it does not read the tables, `issX_fst`). -/
def pendX (k : CfgX) (x : XC) : PendingToken :=
  ⟨List.ofFn x.1.1.1, List.ofFn x.1.1.2, List.ofFn k.1, List.ofFn k.2.1,
    com (List.ofFn x.1.1.1) (List.ofFn k.1) (List.ofFn k.2.1) (List.ofFn x.1.1.2)⟩

/-- Client `j`'s first output: its issuance request. -/
noncomputable def initM (c : Fin n → XC) (j : ℕ) (k : CfgX) (t : Tb R pI) : OutM :=
  .inl (issX (List.ofFn k.1) (List.ofFn k.2.1) (tapeAtM c j).1 t.2).2

variable (idx : AnchorSet → UOVKey → ℕ)

/-- Client `j` on an answer: `finalize_issue`, then the redemption request. -/
noncomputable def stepM (c : Fin n → XC) (j : ℕ) (k : CfgX) (_ : ℕ) (a : AnsX) (_ : OutM)
    (t : Tb R pI) : OutM :=
  .inr (redX (List.ofFn k.1) (List.ofFn k.2.1) idx k.2.2 (pendX k (tapeAtM c j)) a.1 a.2
    (tapeAtM c j).2 t.2)

/-- **Further Client `j`, configured `k`, after the answers `h`**: its issuance request if it has
received none, else its redemption on the first answer (later answers are ignored). -/
noncomputable def outM (c : Fin n → XC) (j : ℕ) (k : CfgX) (h : List AnsX) (t : Tb R pI) : OutM :=
  chainGo (stepM idx c j k) t 0 (initM c j k t) (h.take 1)

lemma issX_sreadsM (c : Fin n → XC) (j : ℕ) (k : CfgX) :
    SReads pI (fun t : Tb R pI => (issX (List.ofFn k.1) (List.ofFn k.2.1) (tapeAtM c j).1 t.2).2)
      0 nGrind 624 4607 :=
  issX_req_sreads (R := R) (List.ofFn k.1) (List.ofFn k.2.1) List.length_ofFn List.length_ofFn _

lemma redX_sreadsM (c : Fin n → XC) (j : ℕ) (k : CfgX) (a : AnsX) :
    SReads pI (fun t : Tb R pI => redX (List.ofFn k.1) (List.ofFn k.2.1) idx k.2.2
      (pendX k (tapeAtM c j)) a.1 a.2 (tapeAtM c j).2 t.2) 0 nGrind 624 4607 :=
  SReads.pR_pI (f := fun s => redX (List.ofFn k.1) (List.ofFn k.2.1) idx k.2.2
      (pendX k (tapeAtM c j)) a.1 a.2 (tapeAtM c j).2 s)
    (redX_sreads (R := R) (List.ofFn k.1) (List.ofFn k.2.1) List.length_ofFn List.length_ofFn idx k.2.2
      (pendX k (tapeAtM c j)) List.length_ofFn List.length_ofFn a.1 a.2 (tapeAtM c j).2)

/-- The issuance request's read sets. -/
noncomputable def QiM (c : Fin n → XC) (j : ℕ) (k : CfgX) : Tb R pI → RS pI :=
  Classical.choose (issX_sreadsM (R := R) c j k)

/-- The redemption request's read sets. -/
noncomputable def QsM (c : Fin n → XC) (j : ℕ) (k : CfgX) (_ : ℕ) (a : AnsX) (_ : OutM) :
    Tb R pI → RS pI :=
  Classical.choose (redX_sreadsM (R := R) idx c j k a)

/-- **What Client `j` has read after the answers `h`.** -/
noncomputable def QM (c : Fin n → XC) (j : ℕ) (k : CfgX) (h : List AnsX) (t : Tb R pI) : RS pI :=
  chainGoQ (stepM idx c j k) (QsM idx c j k) t 0 (initM c j k t) (QiM c j k t) (h.take 1)

lemma chainConsM (c : Fin n → XC) (j : ℕ) (k : CfgX) :
    ChainCons (initM (R := R) c j k) (stepM idx c j k) (QiM c j k) (QsM idx c j k) where
  init t t' hA := by
    obtain ⟨e1, e2⟩ := (Classical.choose_spec (issX_sreadsM (R := R) c j k)).1 t t' hA
    exact ⟨e1, congrArg (fun z => (Sum.inl z : OutM)) e2⟩
  step i a σ t t' hA := by
    obtain ⟨e1, e2⟩ := (Classical.choose_spec (redX_sreadsM (R := R) idx c j k a)).1 t t' hA
    exact ⟨e1, congrArg (fun z => (Sum.inr z : OutM)) e2⟩

/-- **A further Client is a stateful consistent reader.** -/
theorem sessReads_M (c : Fin n → XC) : SessReads (outM (R := R) idx c) (QM idx c) :=
  ChainCons.sessReads (fun j k => chainConsM idx c j k) id 1

lemma QM_card (c : Fin n → XC) (j : ℕ) (k : CfgX) (h : List AnsX) (t : Tb R pI) :
    (QM idx c j k h t).1.card ≤ 0 ∧ (QM idx c j k h t).2.1.card ≤ 2 * nGrind ∧
      (QM idx c j k h t).2.2.1.card ≤ 1248 ∧ (QM idx c j k h t).2.2.2.card ≤ 9214 := by
  have h := chain_card (stepM idx c j k) (QsM idx c j k) (QiM c j k) t 1
    ((Classical.choose_spec (issX_sreadsM (R := R) c j k)).2 t)
    (fun i a σ => (Classical.choose_spec (redX_sreadsM (R := R) idx c j k a)).2 t) (initM c j k t) h
  unfold QM
  exact ⟨by simpa using h.1, by have := h.2.1; omega, by have := h.2.2.1; omega,
    by have := h.2.2.2; omega⟩

/-- **Interleaved further Clients are a consistent reader**, `n` times a Client's reads. -/
theorem Good.sreads_M (c : Fin n → XC) {F : Tb R pI → List EvM} (hF : Good n (QM idx c) F) :
    SReads pI F 0 (n * (2 * nGrind)) (n * 1248) (n * 9214) := by
  simpa using hF.sreads (sessReads_M idx c) (QM_card idx c)

end Sess

/-! ## The interleaved game -/

section Game

variable {n : ℕ}

/-- **The colluding adversary of the interleaved game**: `L₁` steps before the challenge, `L₂`
between the challenge issuance requests and the challenge answers, `L₃` after the challenge
outcome; at each step the next action (start a further Client with contexts and a key, or answer
a pending one) from the transcript; the challenge contexts and keys, the challenge responses and
Anchor Sets, and the guess from the transcript. The interaction does not read the tables itself. -/
structure AdversaryILM (R : Type) where
  L₁ : ℕ
  L₂ : ℕ
  L₃ : ℕ
  next : List EvM → ActM
  ctxIss : List EvM → Coins ctxBytes
  ctxRed : List EvM → Coins ctxBytes
  pk : List EvM → Bool → UOVKey
  respond : List EvM → Bool → Coins uovN
  choose : List EvM → Bool → AnchorSet × Bytes
  guess : List EvM → Slices → ShM R → Prop

/-- **The guess's budget**: each challenge slice at `q3` keys, `H₅` at `q5`, the cipher at `qE`;
`H₂³` freely. -/
structure AdversaryILM.Budget (A : AdversaryILM R) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ T (g₁ gL gR : Tab3) s, Rd3 (fun g => A.guess T ((g, g₁), (gL, gR)) s) q3
  h31 : ∀ T (g₀ gL gR : Tab3) s, Rd3 (fun g => A.guess T ((g₀, g), (gL, gR)) s) q3
  h3L : ∀ T (g₀ g₁ gR : Tab3) s, Rd3 (fun g => A.guess T ((g₀, g₁), (g, gR)) s) q3
  h3R : ∀ T (g₀ g₁ gL : Tab3) s, Rd3 (fun g => A.guess T ((g₀, g₁), (gL, g)) s) q3
  h5 : ∀ T sl, Rd5 (A.guess T sl) q5
  hE : ∀ T sl, RdE (A.guess T sl) qE

namespace AdversaryILM

variable (A : AdversaryILM R) (idx : AnchorSet → UOVKey → ℕ) (c : Fin n → XC)

/-- `L` steps of the schedule from the transcript `tr`, on the tables `s`. -/
noncomputable def run (L : ℕ) (tr : List EvM) (s : ShM R) : List EvM :=
  runT n (outM idx c) A.next L tr ((default : Tab3), s)

/-- The steps before the challenge. -/
noncomputable def tr₁ (s : ShM R) : List EvM := A.run idx c A.L₁ [] s

/-- The steps between the challenge issuance requests `q₀`, `q₁` and the challenge answers. -/
noncomputable def tr₂ (T₁ : List EvM) (q₀ q₁ : Bytes) (s : ShM R) : List EvM :=
  A.run idx c A.L₂ (T₁ ++ [.ext (.inl (q₀, q₁))]) s

/-- The steps after the challenge outcome `y`. -/
noncomputable def tr₃ (T₂ : List EvM) (y : Option (Except Error Bytes × Except Error Bytes))
    (s : ShM R) : List EvM :=
  A.run idx c A.L₃ (T₂ ++ [.ext (.inr y)]) s

/-- **The table-reading adversary at the key stage's transcript `T₁`**: its contexts and keys from
`T₁`; its interaction runs the steps up to the challenge answers, its guess also those after. -/
noncomputable def atT (T₁ : List EvM) : AdversaryRA R where
  ctxIss := A.ctxIss T₁
  ctxRed := A.ctxRed T₁
  pk := A.pk T₁
  respond q₀ q₁ i _ u := A.respond (A.tr₂ idx c T₁ q₀ q₁ u) i
  choose q₀ q₁ side _ u := A.choose (A.tr₂ idx c T₁ q₀ q₁ u) side
  guess q₀ q₁ y sl v := A.guess (A.tr₃ idx c (A.tr₂ idx c T₁ q₀ q₁ v) y v) sl v

/-- **The reduction**: the adversary with a table-reading key stage that runs the schedule itself,
the further Clients' tapes `c` fixed. -/
noncomputable def red : AdversaryRAK R (List EvM) :=
  ⟨fun _ s => A.tr₁ idx c s, A.atT idx c⟩

/-- The challenge interaction at the transcripts `T₁` (keys) and `T₂` (answers). -/
def chalAdv (T₁ T₂ : List EvM) : Adversary :=
  ⟨A.ctxIss T₁, A.ctxRed T₁, A.pk T₁,
    fun _ _ c => bif c then A.respond T₂ true else A.respond T₂ false,
    fun _ _ side => bif side then A.choose T₂ true else A.choose T₂ false,
    fun _ _ _ => True⟩

end AdversaryILM

/-- **The interleaved game** in world `b`: the schedule's first `L₁` steps, the challenge contexts
and keys from them, the challenge issuance requests, `L₂` more steps, the challenge answers and
outcome (§6's rule), `L₃` more steps, and the guess. -/
noncomputable def realGameILM (A : AdversaryILM R) (idx : AnchorSet → UOVKey → ℕ) (b : Bool)
    (z : (PT × (Fin n → XC)) × ShM R) : Prop :=
  let T₁ := A.tr₁ idx z.1.2 z.2
  let q₀ := (issX (List.ofFn (A.ctxIss T₁)) (List.ofFn (A.ctxRed T₁)) z.1.1.1.1 z.2).2
  let q₁ := (issX (List.ofFn (A.ctxIss T₁)) (List.ofFn (A.ctxRed T₁)) z.1.1.1.2 z.2).2
  let T₂ := A.tr₂ idx z.1.2 T₁ q₀ q₁ z.2
  let y := outAt (A.chalAdv T₁ T₂) idx b z.1.1 z.2
  A.guess (A.tr₃ idx z.1.2 T₂ y z.2) (slOf z.1.1) z.2

/-- **The interleaved game is the key-stage game of the reduction**, tape by tape. -/
theorem realGameILM_iff (A : AdversaryILM R) (idx : AnchorSet → UOVKey → ℕ) (b : Bool) (x : PT)
    (c : Fin n → XC) (s : ShM R) :
    realGameILM A idx b ((x, c), s) ↔ realGameRAK (A.red idx c) idx leanPI leanPR b (x, s) :=
  Iff.rfl

namespace AdversaryILM

variable (A : AdversaryILM R) (idx : AnchorSet → UOVKey → ℕ) (c : Fin n → XC)

/-- The schedule reads no slice. -/
lemma run_snd (L : ℕ) (tr : List EvM) (t : Tb R pI) :
    A.run idx c L tr t.2 = runT n (outM idx c) A.next L tr t :=
  runT_congr_out (fun j k h => by
    unfold outM; exact chainGo_congr (step := stepM (R := R) idx c j k) (t := t) (t' := (default, t.2))
      (fun _ _ _ => rfl) _ _ (initM c j k t)) L tr

/-- **The reduction's key-stage budget**: the steps before the challenge, at most `n` Clients. -/
theorem red_kBudget : (A.red idx c).KBudget 0 (n * (2 * nGrind)) (n * 1248) (n * 9214) := by
  have h := Good.sreads_M idx c (Good.run (next := A.next) (sessReads_M idx c) A.L₁
    (Good.const (n := n) (Q := QM (R := R) idx c) ([] : List EvM)))
  have h' : SReads pI (fun t : Tb R pI => A.tr₁ idx c t.2) 0 (n * (2 * nGrind)) (n * 1248) (n * 9214) :=
    (congrArg (fun F => SReads pI F 0 (n * (2 * nGrind)) (n * 1248) (n * 9214))
      (funext fun t => (A.run_snd idx c A.L₁ [] t).symm)).mp h
  exact ⟨fun _ _ _ => h', fun _ _ _ => h', fun _ _ _ => h', fun _ _ _ => h'⟩

/-- **The reduction's interaction budget**: at any key-stage transcript, the steps up to the
challenge answers, at most `n` Clients. -/
theorem red_iBudget : (A.red idx c).IBudget 0 (n * (2 * nGrind)) (n * 1248) (n * 9214) := by
  intro T₁
  have h (q₀ q₁ : Bytes) : SReads pI (fun t : Tb R pI => (A.atT idx c T₁).trans q₀ q₁ default t.2) 0
      (n * (2 * nGrind)) (n * 1248) (n * 9214) := by
    have h := (Good.sreads_M idx c (Good.run (next := A.next) (sessReads_M idx c) A.L₂
      (Good.const (n := n) (Q := QM (R := R) idx c) (T₁ ++ [.ext (.inl (q₀, q₁))])))).map
        fun T => ((A.respond T false, A.respond T true), (A.choose T false, A.choose T true))
    refine (congrArg (fun F => SReads pI F 0 (n * (2 * nGrind)) (n * 1248) (n * 9214))
      (funext fun t => ?_)).mp h
    simp only [AdversaryRA.trans, atT, tr₂, run_snd]
  exact ⟨fun q₀ q₁ _ _ _ => h q₀ q₁, fun q₀ q₁ _ _ _ => h q₀ q₁, fun q₀ q₁ _ _ _ => h q₀ q₁,
    fun q₀ q₁ _ _ _ => h q₀ q₁⟩

/-- **The reduction's guess budget**: the adversary's plus the `n` Clients' reads. -/
theorem red_gBudget {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    (A.red idx c).GBudget q3 (n * 1248 + q5) (n * 9214 + qE) := by
  intro T₁ tr
  have hG (q₀ q₁ : Bytes) (y : Option (Except Error Bytes × Except Error Bytes)) :=
    Good.sreads_M idx c (Good.run (next := A.next) (sessReads_M idx c) A.L₃
      (Good.ext (Good.run (next := A.next) (sessReads_M idx c) A.L₂
        (Good.const (n := n) (Q := QM (R := R) idx c) (T₁ ++ [.ext (.inl (q₀, q₁))]))) (.inr y)))
  exact
    { h30 := fun q₀ q₁ y g₁ gL gR s => hA.h30 _ g₁ gL gR s
      h31 := fun q₀ q₁ y g₀ gL gR s => hA.h31 _ g₀ gL gR s
      h3L := fun q₀ q₁ y g₀ g₁ gR s => hA.h3L _ g₀ g₁ gR s
      h3R := fun q₀ q₁ y g₀ g₁ gL s => hA.h3R _ g₀ g₁ gL s
      h5 := fun q₀ q₁ y sl => Rd5.bindEq (m := fun s => A.tr₃ idx c (A.tr₂ idx c T₁ q₀ q₁ s) y s)
        (f := fun T s => A.guess T sl s) (fun _ => rfl) ((hG q₀ q₁ y).rd5 default) fun T => hA.h5 T sl
      hE := fun q₀ q₁ y sl => RdE.bindEq (m := fun s => A.tr₃ idx c (A.tr₂ idx c T₁ q₀ q₁ s) y s)
        (f := fun T s => A.guess T sl s) (fun _ => rfl) ((hG q₀ q₁ y).rdE default) fun T => hA.hE T sl }

end AdversaryILM

/-- The interleaved game's tape, with the further Clients' tapes first. -/
def tapeILM : (Fin n → XC) × (PT × ShM R) ≃ (PT × (Fin n → XC)) × ShM R where
  toFun z := ((z.2.1, z.1), z.2.2)
  invFun z := (z.1.2, (z.1.1, z.2))
  left_inv _ := rfl
  right_inv _ := rfl

end Game

/-! ## The bound -/

section Bound

variable {n : ℕ}

/-- **Theorem 4(a) with interleaved further sessions, for every type of cipher rows** (`ZKRow R`,
`ZKPRow R`; SHAKE as the base record): with at most `n` further Clients, scheduled, started and
answered in any order by the adversary, the bound of `anonymityRAK_lean_numG` at the key-stage and
interaction budgets `(0, 2·2³²n, 1248n, 9214n)` and the guess budget `(q₃, q₅ + 1248n,
q_E + 9214n)` (for the reduction that runs the schedule, averaged over the Clients' tapes). -/
theorem anonymityIL_lean_numG [ZKRow R] [ZKPRow R] (A : AdversaryILM R) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : Fin n → XC) b cc,
      hidingAdv (A.atT idx c (A.tr₁ idx c cc.2.2)).ctxRO.base.ci
        (A.atT idx c (A.tr₁ idx c cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atT idx c (A.tr₁ idx c cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide) :
    |pr ((PT × (Fin n → XC)) × ShM R) (realGameILM A idx false) -
        pr ((PT × (Fin n → XC)) × ShM R) (realGameILM A idx true)| ≤
      4 * εAdG R pI 9 (0 + q3) (n * 1248 + q5 + n * 1248 + 1872)
          (n * 9214 + qE + n * 9214 + 13821) 0 (n * (2 * nGrind)) (n * 1248) (n * 9214) +
        4 * εAdG R pR 9 q3 (n * 1248 + q5 + 1248) (n * 9214 + qE + 13821) (0 + 0)
          (n * (2 * nGrind) + n * (2 * nGrind)) (n * 1248 + n * 1248 + 624) (n * 9214 + n * 9214 + 9214) +
        4 * (((0 + 0 : ℕ) : ℝ) / 2 ^ 128 + 1 / 2 ^ 113 +
          ZKPRow.εP R pR 0 312 4607 (n * 1248 + n * 1248 + 624) (n * 9214 + n * 9214 + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  rw [← pr_equiv tapeILM, ← pr_equiv tapeILM]
  exact abs_pr_prod_sub_le _ _ fun c =>
    anonymityRAK_lean_numG (A.red idx c) idx (A.red_gBudget idx c hA) (A.red_iBudget idx c)
      (A.red_kBudget idx c) (hhide c)

/-- **Theorem 4(a) with interleaved further sessions** (function rows). -/
theorem anonymityIL_lean_num (A : AdversaryILM (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : Fin n → XC) b cc,
      hidingAdv (A.atT idx c (A.tr₁ idx c cc.2.2)).ctxRO.base.ci
        (A.atT idx c (A.tr₁ idx c cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atT idx c (A.tr₁ idx c cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide) :
    |pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILM A idx false) -
        pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILM A idx true)| ≤
      4 * εAd 9 (0 + q3) (n * 1248 + q5 + n * 1248 + 1872)
          (n * 9214 + qE + n * 9214 + 13821) 0 (n * (2 * nGrind)) (n * 1248) (n * 9214) +
        4 * εAd 9 q3 (n * 1248 + q5 + 1248) (n * 9214 + qE + 13821) (0 + 0)
          (n * (2 * nGrind) + n * (2 * nGrind)) (n * 1248 + n * 1248 + 624) (n * 9214 + n * 9214 + 9214) +
        4 * (((0 + 0 : ℕ) : ℝ) / 2 ^ 128 + 1 / 2 ^ 113 +
          εROP 0 312 4607 (n * 1248 + n * 1248 + 624) (n * 9214 + n * 9214 + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityIL_lean_numG A idx hA hhide

/-- **Theorem 4(a) with interleaved further sessions and AES as uniformly random permutations.** -/
theorem anonymityIL_lean_num_perm (A : AdversaryILM (Equiv.Perm Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : Fin n → XC) b cc,
      hidingAdv (A.atT idx c (A.tr₁ idx c cc.2.2)).ctxRO.base.ci
        (A.atT idx c (A.tr₁ idx c cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atT idx c (A.tr₁ idx c cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide) :
    |pr ((PT × (Fin n → XC)) × ShM (Equiv.Perm Blk)) (realGameILM A idx false) -
        pr ((PT × (Fin n → XC)) × ShM (Equiv.Perm Blk)) (realGameILM A idx true)| ≤
      4 * εAdPm pI 9 (0 + q3) (n * 1248 + q5 + n * 1248 + 1872)
          (n * 9214 + qE + n * 9214 + 13821) 0 (n * (2 * nGrind)) (n * 1248) (n * 9214) +
        4 * εAdPm pR 9 q3 (n * 1248 + q5 + 1248) (n * 9214 + qE + 13821) (0 + 0)
          (n * (2 * nGrind) + n * (2 * nGrind)) (n * 1248 + n * 1248 + 624) (n * 9214 + n * 9214 + 9214) +
        4 * (((0 + 0 : ℕ) : ℝ) / 2 ^ 128 + 1 / 2 ^ 113 +
          εROPmP pR 0 312 4607 (n * 1248 + n * 1248 + 624) (n * 9214 + n * 9214 + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityIL_lean_numG A idx hA hhide

/-- **The interleaved bound in numbers**: with `n` further Clients (`n + 2` in all),

    |Pr[W₀] − Pr[W₁]| ≤ (n + 2)·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide,

for every schedule and every number of steps. (Per Client `≈ 2⁻¹⁰¹·¹³`: its reads in the key
stage, the interaction and the guess; the constant is `≈ 2⁻¹⁰¹·⁹⁴`.) -/
theorem anonymityIL_lean_le (A : AdversaryILM (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : Fin n → XC) b cc,
      hidingAdv (A.atT idx c (A.tr₁ idx c cc.2.2)).ctxRO.base.ci
        (A.atT idx c (A.tr₁ idx c cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atT idx c (A.tr₁ idx c cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide) :
    |pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILM A idx false) -
        pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILM A idx true)| ≤
      (n + 2 : ℕ) / 2 ^ 101 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := anonymityIL_lean_num A idx hA hhide
  have hn := noHitProb_le_128
  have hn0 : 0 ≤ noHitProb := pr_nonneg _
  have h1 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have e1024 : (2 : ℝ) ^ 1024 = 2 ^ 128 * 2 ^ 896 := by rw [← pow_add]
  have hb : (2 : ℝ) ^ 32 ≤ 2 ^ 896 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have hG : ∀ m : ℕ, (m : ℝ) * (nGrind : ℝ) / 2 ^ 1024 ≤ m / 2 ^ 128 := fun m => by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    rw [show (nGrind : ℝ) = 2 ^ 32 by simp only [nGrind, Nat.cast_pow, Nat.cast_ofNat], e1024,
      div_le_div_iff₀ (by positivity) (by positivity)]
    calc (m : ℝ) * 2 ^ 32 * 2 ^ 128 = ((m : ℝ) * 2 ^ 128) * 2 ^ 32 := mul_right_comm _ _ _
      _ ≤ ((m : ℝ) * 2 ^ 128) * 2 ^ 896 := mul_le_mul_of_nonneg_left hb (mul_nonneg hm hp.le)
      _ = (m : ℝ) * (2 ^ 128 * 2 ^ 896) := mul_assoc _ _ _
  have hK : (12 : ℝ) / 2 ^ 1024 ≤ 1 / 2 ^ 128 := by
    rw [e1024, div_le_div_iff₀ (by positivity) (by positivity)]
    have h16 : (12 : ℝ) ≤ 2 ^ 32 := by norm_num
    calc (12 : ℝ) * 2 ^ 128 ≤ 2 ^ 896 * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right (h16.trans hb) hp.le
      _ = 1 * (2 ^ 128 * 2 ^ 896) := by rw [one_mul, mul_comm]
  have e : ∀ x : ℝ, x / 2 ^ 101 = x * 134217728 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  unfold εAd h23Term at h
  generalize (2 : ℝ) ^ 1024 = κ at h hK hG
  have hGa : (n : ℝ) * (2 * (nGrind : ℝ)) / κ ≤ 2 * n / 2 ^ 128 := by
    have := hG n
    rw [show (n : ℝ) * (2 * (nGrind : ℝ)) / κ = 2 * ((n : ℝ) * nGrind / κ) by ring,
      show (2 : ℝ) * n / 2 ^ 128 = 2 * (n / 2 ^ 128) by ring]
    linarith
  have hGb : ((n : ℝ) * (2 * (nGrind : ℝ)) + (n : ℝ) * (2 * (nGrind : ℝ))) / κ ≤ 4 * n / 2 ^ 128 := by
    have := hG n
    rw [show ((n : ℝ) * (2 * (nGrind : ℝ)) + (n : ℝ) * (2 * (nGrind : ℝ))) / κ =
        4 * ((n : ℝ) * nGrind / κ) by ring, show (4 : ℝ) * n / 2 ^ 128 = 4 * (n / 2 ^ 128) by ring]
    linarith
  split_ifs at h <;>
  · unfold εROP εRO at h
    push_cast at h ⊢
    rw [e]
    linarith

/-- **`2²⁰` Clients**: `≤ 2⁻⁸¹ + 2·εhide` plus the guess's budget terms. -/
theorem anonymityIL_lean_2pow20 (A : AdversaryILM (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : Fin n → XC) b cc,
      hidingAdv (A.atT idx c (A.tr₁ idx c cc.2.2)).ctxRO.base.ci
        (A.atT idx c (A.tr₁ idx c cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atT idx c (A.tr₁ idx c cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide)
    (hn : n + 2 ≤ 2 ^ 20) :
    |pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILM A idx false) -
        pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILM A idx true)| ≤
      1 / 2 ^ 81 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := anonymityIL_lean_le A idx hA hhide
  have : ((n + 2 : ℕ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hn
  have h2 : ((n + 2 : ℕ) : ℝ) / 2 ^ 101 ≤ 1 / 2 ^ 81 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **`2³²` Clients**: `≤ 2⁻⁶⁹ + 2·εhide` plus the guess's budget terms. -/
theorem anonymityIL_lean_2pow32 (A : AdversaryILM (Blk → Blk)) (idx : AnchorSet → UOVKey → ℕ)
    {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : Fin n → XC) b cc,
      hidingAdv (A.atT idx c (A.tr₁ idx c cc.2.2)).ctxRO.base.ci
        (A.atT idx c (A.tr₁ idx c cc.2.2)).ctxRO.base.cr
        (reductionRA (A.atT idx c (A.tr₁ idx c cc.2.2)) idx (leanSim pI) (leanSim pR) leanProgI
          leanProgR b cc) ≤ εhide)
    (hn : n + 2 ≤ 2 ^ 32) :
    |pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILM A idx false) -
        pr ((PT × (Fin n → XC)) × ShM (Blk → Blk)) (realGameILM A idx true)| ≤
      1 / 2 ^ 69 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := anonymityIL_lean_le A idx hA hhide
  have : ((n + 2 : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have h2 : ((n + 2 : ℕ) : ℝ) / 2 ^ 101 ≤ 1 / 2 ^ 69 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end Bound

end VoleMole.Privacy.Moussaka
