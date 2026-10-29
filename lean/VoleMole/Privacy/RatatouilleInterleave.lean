import VoleMole.Privacy.RatatouilleAdaptive
import VoleMole.ZK.ReadsInterleave

/-!
# Ratatouille unlinkability with interleaved further sessions that spend several times

`Privacy/RatatouilleAdaptive.lean` lets the malicious Issuer start further sessions after seeing
earlier outcomes, each run to the end (issuance and one spend) before the next starts. Here the
Issuer is an **interactive machine that schedules the further Clients arbitrarily**, and each
further Client **spends up to `K` times along its chain of change tokens**: at each step the
Issuer either starts a new honest Client with a key, context and balance of its choice (`CfgR`;
it sees the issuance request) or delivers a message to a pending Client and sees its next spend
request. A Client's first message is the issuance response and the amount of its first spend; its
`i`-th later message is the Issuer's response to its `i`-th spend (which the Client finalizes into
its change token, `finalize_spend`) and the amount of the next spend of that change token.

## The game

`AdversaryILR`: a step function `next` from the transcript to an action (`ZK.Sim.Act`), the
challenge key, context and balance, stage 1 (`respondIss`, `d₁`), stage 2 (`respond₁`, `d₂`) and the
guess, each a function of the transcript, and the numbers of steps `L₁` before the challenge
issuance requests, `L₂` between them and stage 1, `L₃` between round 1's request and stage 2 (they
happen only if round 1 runs), `L₄` after the challenge outcome. `realGameILR` is, as
`realGameAdR`, the key-stage game (`Privacy/RatatouilleRAK.lean`) of the Issuer `A.red c` that runs
the schedule with the further Clients' tapes `c : Fin n → XK K` (an issuance tape and `K` spend
tapes each; starts beyond `n` are refused, messages beyond the `K`-th are ignored).

## The reduction

A further Client is a chain (`ZK/ReadsInterleave.lean`, `ChainCons`) of `1 + K` consistent
readers: its issuance (`issXR_sreads`) and its spends (`spXR_sreads`, at whatever token the
earlier steps left, `tokOf`), so by the interleaving lemma (`Good.run`, `Good.sreads`) every
stretch of the schedule is a consistent reader with `n` times `(0, (K+1)·2³², (K+1)·624,
(K+1)·4607)`. Budgets: key stage and both stages at every state `n·(K+1)·(0, 2³², 624, 4607)`
(`red_kBudget`, `red_iBudget`), guess `(q₃, q₅ + n(K+1)·624, q_E + n(K+1)·4607)` (`red_gBudget`).

## The bound

`unlinkabilityRAK_lean_numG` for every `c`, averaged: `unlinkabilityIL_lean_numG`, `_num`,
`_num_perm`; in numbers (`unlinkabilityIL_lean_le`)
`≤ (n(K+1) + 2)·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide`, linear in the number `n(K+1)` of
the further Clients' proofs, for every schedule: `2⁻⁸¹` for `n(K+1) + 2 ≤ 2²⁰`, `2⁻⁶⁹` for
`n(K+1) + 2 ≤ 2³²` (`unlinkabilityIL_lean_2pow20`, `_2pow32`; exactly, per proof
`≈ 2⁻¹⁰¹·⁷⁷`). Hiding of `Com` is assumed for the reductions of every `A.red c`.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-- The proof sizes of the Lean provers. -/
local notation "ZL" => Sizes.labelRows

/-! ## A further Client with a chain of spends -/

section Sess

/-- **A further Client's message**: the issuance response (first message) or the response to its
last spend (later messages), and the amount of its next spend. -/
abbrev MsgC := (Preimage ⊕ SpendResponse) × Credits

/-- What a further Client outputs: its issuance request, then its spend requests. -/
abbrev OutR := IReq ⊕ SReq

/-- The challenge's events in the transcript: the issuance requests, round 1's request (if round
1 runs), the outcome. -/
abbrev ExtR := IssTr ZL ⊕ SReq ⊕ Rounds ZL

/-- **The Issuer's view of the schedule.** -/
abbrev EvR := Ev CfgR MsgC OutR ExtR

/-- An action: start a further Client, or send one a message. -/
abbrev ActR := Act CfgR MsgC

/-- A further Client's tapes: its issuance tape and `K` spend tapes. -/
abbrev XK (K : ℕ) := TRe × (Fin K → TRe)

/-- **A further Client's state**: its issuance's result, or its last spend's. -/
abbrev StR := Except Error (PendingTokenS × IssueRequest ZL) ⊕
  (Option TokenS × Except Error (PendingSpendS × SpendRequest ZL))

/-- The Client's `finalize_spend` of its last spend on the Issuer's response: its change token. -/
def finSX (pk : PublicKey) (r : Option TokenS × Except Error (PendingSpendS × SpendRequest ZL))
    (resp : SpendResponse) : Option TokenS :=
  match r.2 with
  | .ok q => match (finalizeSpend pk (some q.1) resp).2 with
    | .ok o => o
    | .error _ => none
  | .error _ => none

/-- **The token a Client spends next**: its issued token on the issuance response, its change
token on the response to its last spend. -/
def tokOf (pk : PublicKey) : StR → Preimage ⊕ SpendResponse → Option TokenS
  | .inl r, .inl resp => finI pk r resp
  | .inr r, .inr resp => finSX pk r resp
  | _, _ => none

/-- A Client's output at its state. -/
def outpR : StR → OutR
  | .inl r => .inl (reqIX r)
  | .inr r => .inr (reqSX r)

variable {n K : ℕ}

/-- The tapes of the `j`-th Client started. -/
def tapeAtR (c : Fin n → XK K) (j : ℕ) : XK K := if h : j < n then c ⟨j, h⟩ else default

/-- The tape of a Client's `i`-th spend. -/
def spTape (y : Fin K → TRe) (i : ℕ) : TRe := if h : i < K then y ⟨i, h⟩ else default

/-- Client `j`'s issuance. -/
noncomputable def initR (c : Fin n → XK K) (j : ℕ) (k : CfgR) (t : Tb R pI) : StR :=
  .inl (issXR k.2.1 k.2.2 (tapeAtR c j).1 t.2)

/-- Client `j`'s `i`-th spend, of the token its state and the message give. -/
noncomputable def stepR (c : Fin n → XK K) (j : ℕ) (k : CfgR) (i : ℕ) (a : MsgC) (σ : StR)
    (t : Tb R pI) : StR :=
  .inr (spXR k.1 k.2.1 (tokOf k.1 σ a.1) a.2 (spTape (tapeAtR c j).2 i) t.2)

/-- **Further Client `j`, configured `k`, after the messages `h`**: its issuance request if it has
received none, else the spend request of its last spend (messages beyond the `K`-th are
ignored). -/
noncomputable def outR (c : Fin n → XK K) (j : ℕ) (k : CfgR) (h : List MsgC) (t : Tb R pI) : OutR :=
  outpR (chainGo (stepR c j k) t 0 (initR c j k t) (h.take K))

lemma initR_sreads (c : Fin n → XK K) (j : ℕ) (k : CfgR) :
    SReads pI (initR (R := R) c j k) 0 nGrind 624 4607 :=
  (issXR_sreads (R := R) k.2.1 k.2.2 (tapeAtR c j).1).map fun r => (Sum.inl r : StR)

lemma stepR_sreads (c : Fin n → XK K) (j : ℕ) (k : CfgR) (i : ℕ) (a : MsgC) (σ : StR) :
    SReads pI (stepR (R := R) c j k i a σ) 0 nGrind 624 4607 :=
  (SReads.pS_pI (f := fun s => spXR k.1 k.2.1 (tokOf k.1 σ a.1) a.2 (spTape (tapeAtR c j).2 i) s)
    (spXR_sreads (R := R) k.1 k.2.1 _ _ _)).map fun r => (Sum.inr r : StR)

/-- The issuance's read sets. -/
noncomputable def QiR (c : Fin n → XK K) (j : ℕ) (k : CfgR) : Tb R pI → RS pI :=
  Classical.choose (initR_sreads (R := R) c j k)

/-- A spend's read sets. -/
noncomputable def QsR (c : Fin n → XK K) (j : ℕ) (k : CfgR) (i : ℕ) (a : MsgC) (σ : StR) :
    Tb R pI → RS pI :=
  Classical.choose (stepR_sreads (R := R) c j k i a σ)

/-- **What Client `j` has read after the messages `h`.** -/
noncomputable def QR (c : Fin n → XK K) (j : ℕ) (k : CfgR) (h : List MsgC) (t : Tb R pI) : RS pI :=
  chainGoQ (stepR c j k) (QsR c j k) t 0 (initR c j k t) (QiR c j k t) (h.take K)

lemma chainConsR (c : Fin n → XK K) (j : ℕ) (k : CfgR) :
    ChainCons (initR (R := R) c j k) (stepR c j k) (QiR c j k) (QsR c j k) where
  init t t' hA := (Classical.choose_spec (initR_sreads (R := R) c j k)).1 t t' hA
  step i a σ t t' hA := (Classical.choose_spec (stepR_sreads (R := R) c j k i a σ)).1 t t' hA

/-- **A further Client with a chain of spends is a stateful consistent reader.** -/
theorem sessReads_R (c : Fin n → XK K) : SessReads (outR (R := R) c) (QR c) :=
  ChainCons.sessReads (fun j k => chainConsR c j k) outpR K

lemma QR_card (c : Fin n → XK K) (j : ℕ) (k : CfgR) (h : List MsgC) (t : Tb R pI) :
    (QR c j k h t).1.card ≤ 0 ∧ (QR c j k h t).2.1.card ≤ (K + 1) * nGrind ∧
      (QR c j k h t).2.2.1.card ≤ (K + 1) * 624 ∧ (QR c j k h t).2.2.2.card ≤ (K + 1) * 4607 := by
  have h := chain_card (stepR c j k) (QsR c j k) (QiR c j k) t K
    ((Classical.choose_spec (initR_sreads (R := R) c j k)).2 t)
    (fun i a σ => (Classical.choose_spec (stepR_sreads (R := R) c j k i a σ)).2 t) (initR c j k t) h
  unfold QR
  refine ⟨by simpa using h.1, h.2.1.trans (le_of_eq (by ring)), h.2.2.1.trans (le_of_eq (by ring)),
    h.2.2.2.trans (le_of_eq (by ring))⟩

/-- **Interleaved further Clients are a consistent reader**, `n` times a Client's reads. -/
theorem Good.sreads_R (c : Fin n → XK K) {F : Tb R pI → List EvR} (hF : Good n (QR c) F) :
    SReads pI F 0 (n * (K + 1) * nGrind) (n * (K + 1) * 624) (n * (K + 1) * 4607) := by
  have h := hF.sreads (sessReads_R c) (QR_card c)
  simp only [Nat.mul_zero, Nat.mul_assoc] at h ⊢
  exact h

end Sess

/-! ## The interleaved game -/

section Game

variable {n K : ℕ}

/-- **The malicious Issuer of the interleaved game**: `L₁` steps before the challenge, `L₂`
between the challenge issuance requests and stage 1, `L₃` between round 1's request and stage 2
(only if round 1 runs), `L₄` after the challenge outcome; at each step the next action (start a
further Client with a key, context and balance, or send a pending one its next message) from the
transcript; the challenge key, context and balance, both stages and the guess from the transcript.
The interaction does not read the tables itself. -/
structure AdversaryILR (R : Type) where
  L₁ : ℕ
  L₂ : ℕ
  L₃ : ℕ
  L₄ : ℕ
  next : List EvR → ActR
  pk : List EvR → PublicKey
  ctx : List EvR → Context
  tInit : List EvR → Credits
  respondIss : List EvR → Bool → Preimage
  d₁ : List EvR → Credits
  respond₁ : List EvR → SpendResponse
  d₂ : List EvR → Credits
  guess : List EvR → SlicesR → ShR R → Prop

/-- **The guess's budget**: each challenge slice at `q3` keys, `H₅` at `q5`, the cipher at `qE`;
`H₂³` freely. -/
structure AdversaryILR.Budget (A : AdversaryILR R) (q3 q5 qE : ℕ) : Prop where
  h30 : ∀ T (g₁ g₂ g₃ : Tab3) s, Rd3 (fun g => A.guess T ((g, g₁), (g₂, g₃)) s) q3
  h31 : ∀ T (g₀ g₂ g₃ : Tab3) s, Rd3 (fun g => A.guess T ((g₀, g), (g₂, g₃)) s) q3
  h32 : ∀ T (g₀ g₁ g₃ : Tab3) s, Rd3 (fun g => A.guess T ((g₀, g₁), (g, g₃)) s) q3
  h33 : ∀ T (g₀ g₁ g₂ : Tab3) s, Rd3 (fun g => A.guess T ((g₀, g₁), (g₂, g)) s) q3
  h5 : ∀ T sl, Rd5 (A.guess T sl) q5
  hE : ∀ T sl, RdE (A.guess T sl) qE

namespace AdversaryILR

variable (A : AdversaryILR R) (c : Fin n → XK K)

/-- `L` steps of the schedule from the transcript `tr`, on the tables `s`. -/
noncomputable def run (L : ℕ) (tr : List EvR) (s : ShR R) : List EvR :=
  runT n (outR c) A.next L tr ((default : Tab3), s)

/-- The steps before the challenge. -/
noncomputable def tr₁ (s : ShR R) : List EvR := A.run c A.L₁ [] s

/-- The steps between the challenge issuance requests `tr` and stage 1. -/
noncomputable def tr₂ (T₁ : List EvR) (tr : IssTr ZL) (s : ShR R) : List EvR :=
  A.run c A.L₂ (T₁ ++ [.ext (.inl tr)]) s

/-- The steps between round 1's request `rq` and stage 2. -/
noncomputable def tr₃ (T₂ : List EvR) (rq : SReq) (s : ShR R) : List EvR :=
  A.run c A.L₃ (T₂ ++ [.ext (.inr (.inl rq))]) s

/-- The transcript before the outcome, as the guess sees it: no round-1 steps if round 1 did not
run. -/
noncomputable def tr₃G (T₂ : List EvR) (y : Rounds ZL) (s : ShR R) : List EvR :=
  (y.map Prod.fst).elim T₂ fun rq => A.tr₃ c T₂ rq s

/-- The steps after the challenge outcome `y`. -/
noncomputable def tr₄ (T₃ : List EvR) (y : Rounds ZL) (s : ShR R) : List EvR :=
  A.run c A.L₄ (T₃ ++ [.ext (.inr (.inr y))]) s

/-- **The table-reading Issuer at the key stage's transcript `T₁`**: its key, context and balance
from `T₁`; stage 1 runs the steps up to it, stage 2 also round 1's, the guess also those after the
outcome. -/
noncomputable def atT (T₁ : List EvR) : AdversaryRA R ZL where
  pk := A.pk T₁
  ctx := A.ctx T₁
  tInit := A.tInit T₁
  respondIss tr i _ u := A.respondIss (A.tr₂ c T₁ tr u) i
  d₁ tr _ u := A.d₁ (A.tr₂ c T₁ tr u)
  respond₁ tr rq _ u := A.respond₁ (A.tr₃ c (A.tr₂ c T₁ tr u) rq u)
  d₂ tr rq _ u := A.d₂ (A.tr₃ c (A.tr₂ c T₁ tr u) rq u)
  guess tr y sl v := A.guess (A.tr₄ c (A.tr₃G c (A.tr₂ c T₁ tr v) y v) y v) sl v

/-- **The reduction**: the Issuer with a table-reading key stage that runs the schedule itself,
the further Clients' tapes `c` fixed. -/
noncomputable def red : AdversaryRAK R ZL (List EvR) :=
  ⟨fun _ s => A.tr₁ c s, A.atT c⟩

end AdversaryILR

/-- **The interleaved game** in world `(b₁, b₂)`: the key-stage game (`realGameRAK`, the Lean
provers on the shared tables) of the Issuer that runs the schedule with the further Clients' tapes
`z.1.2`: the steps before the challenge, then the challenge key, context and balance from them
and the challenge protocol of `realGameRA`, the Issuer's stages and guess running the later steps
on the tables. -/
noncomputable def realGameILR (A : AdversaryILR R) (b₁ b₂ : Bool)
    (z : (((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR R) : Prop :=
  realGameRAK (A.red z.1.2) leanPIR leanPSR b₁ b₂ (z.1.1, z.2)

/-- **The interleaved game at a tape** is `realGameRA` of the Issuer at the key stage's
transcript. -/
theorem realGameILR_iff (A : AdversaryILR R) (b₁ b₂ : Bool) (x : (TRe × TRe) × (TRe × TRe))
    (c : Fin n → XK K) (s : ShR R) :
    realGameILR A b₁ b₂ ((x, c), s) ↔ realGameRA (A.atT c (A.tr₁ c s)) leanPIR leanPSR b₁ b₂ (x, s) :=
  Iff.rfl

namespace AdversaryILR

variable (A : AdversaryILR R) (c : Fin n → XK K)

/-- The schedule reads no slice. -/
lemma run_snd (L : ℕ) (tr : List EvR) (t : Tb R pI) :
    A.run c L tr t.2 = runT n (outR c) A.next L tr t :=
  runT_congr_out (fun j k h => by
    unfold outR
    exact congrArg outpR (chainGo_congr (step := stepR (R := R) c j k) (t := t) (t' := (default, t.2))
      (fun _ _ _ => rfl) _ _ (initR c j k t))) L tr

/-- A transcript after any good start and `L` more steps. -/
lemma good_run (L : ℕ) {F : Tb R pI → List EvR} (hF : Good n (QR c) F) :
    Good n (QR c) (fun t => runT n (outR c) A.next L (F t) t) :=
  Good.run (sessReads_R c) L hF

/-- **The reduction's key-stage budget**: the steps before the challenge, at most `n` Clients. -/
theorem red_kBudget :
    (A.red c).KBudget 0 (n * (K + 1) * nGrind) (n * (K + 1) * 624) (n * (K + 1) * 4607) := by
  have h := Good.sreads_R c (A.good_run c A.L₁ (Good.const (n := n) (Q := QR (R := R) c) []))
  have h' : SReads pI (fun t : Tb R pI => A.tr₁ c t.2) 0 (n * (K + 1) * nGrind) (n * (K + 1) * 624)
      (n * (K + 1) * 4607) :=
    (congrArg (fun F => SReads pI F 0 (n * (K + 1) * nGrind) (n * (K + 1) * 624) (n * (K + 1) * 4607))
      (funext fun t => (A.run_snd c A.L₁ [] t).symm)).mp h
  exact ⟨fun _ _ _ => h', fun _ _ _ => h', fun _ _ _ => SReads.pI_pS (f := fun s => A.tr₁ c s) h',
    fun _ _ _ => SReads.pI_pS (f := fun s => A.tr₁ c s) h'⟩

/-- Stage 1 at the key stage's transcript `T₁`. -/
lemma stage1_sreadsIL (T₁ : List EvR) (tr : IssTr ZL) :
    SReads pI (fun t : Tb R pI => (A.atT c T₁).msg₁ tr default t.2) 0 (n * (K + 1) * nGrind)
      (n * (K + 1) * 624) (n * (K + 1) * 4607) := by
  have h := (Good.sreads_R c (A.good_run c A.L₂ (Good.const (n := n) (Q := QR (R := R) c)
    (T₁ ++ [.ext (.inl tr)])))).map
      fun T => ((A.respondIss T false, A.respondIss T true), A.d₁ T)
  refine (congrArg (fun F => SReads pI F 0 (n * (K + 1) * nGrind) (n * (K + 1) * 624)
    (n * (K + 1) * 4607)) (funext fun t => ?_)).mp h
  simp only [AdversaryRA.msg₁, atT, tr₂, run_snd]

/-- Stage 2 at the key stage's transcript `T₁`. -/
lemma stage2_sreadsIL (T₁ : List EvR) (tr : IssTr ZL) (rq : SReq) :
    SReads pI (fun t : Tb R pI => (A.atT c T₁).msg₂ tr rq default t.2) 0 (n * (K + 1) * nGrind)
      (n * (K + 1) * 624) (n * (K + 1) * 4607) := by
  have h := (Good.sreads_R c (A.good_run c A.L₃ (Good.ext (A.good_run c A.L₂
    (Good.const (n := n) (Q := QR (R := R) c) (T₁ ++ [.ext (.inl tr)]))) (.inr (.inl rq))))).map
      fun T => (A.respond₁ T, A.d₂ T)
  refine (congrArg (fun F => SReads pI F 0 (n * (K + 1) * nGrind) (n * (K + 1) * 624)
    (n * (K + 1) * 4607)) (funext fun t => ?_)).mp h
  simp only [AdversaryRA.msg₂, atT, tr₂, tr₃, run_snd]

/-- **The reduction's interaction budget**: each stage at every key-stage transcript, at most `n`
Clients. -/
theorem red_iBudget :
    (A.red c).IBudget 0 (n * (K + 1) * nGrind) (n * (K + 1) * 624) (n * (K + 1) * 4607) := by
  intro T₁
  exact
    { a0 := fun tr _ _ _ => stage1_sreadsIL A c T₁ tr
      a1 := fun tr _ _ _ => stage1_sreadsIL A c T₁ tr
      a2 := fun tr _ _ _ => SReads.pI_pS (f := fun s => (A.atT c T₁).msg₁ tr default s)
        (stage1_sreadsIL A c T₁ tr)
      a3 := fun tr _ _ _ => SReads.pI_pS (f := fun s => (A.atT c T₁).msg₁ tr default s)
        (stage1_sreadsIL A c T₁ tr)
      b0 := fun tr rq _ _ _ => stage2_sreadsIL A c T₁ tr rq
      b1 := fun tr rq _ _ _ => stage2_sreadsIL A c T₁ tr rq
      b2 := fun tr rq _ _ _ => SReads.pI_pS (f := fun s => (A.atT c T₁).msg₂ tr rq default s)
        (stage2_sreadsIL A c T₁ tr rq)
      b3 := fun tr rq _ _ _ => SReads.pI_pS (f := fun s => (A.atT c T₁).msg₂ tr rq default s)
        (stage2_sreadsIL A c T₁ tr rq) }

/-- The guess's transcript is a good one, for every outcome. -/
lemma good_guess (T₁ : List EvR) (tr : IssTr ZL) (y : Rounds ZL) :
    Good n (QR (R := R) c) (fun t : Tb R pI => A.tr₄ c (A.tr₃G c (A.tr₂ c T₁ tr t.2) y t.2) y t.2) := by
  have e : ∀ L tr' (t : Tb R pI), A.run c L tr' t.2 = runT n (outR c) A.next L tr' t :=
    fun L tr' t => A.run_snd c L tr' t
  have h2 := A.good_run c A.L₂ (Good.const (n := n) (Q := QR (R := R) c) (T₁ ++ [.ext (.inl tr)]))
  unfold tr₄ tr₃G
  rcases y.map Prod.fst with _ | rq
  · have h := A.good_run c A.L₄ (Good.ext h2 (.inr (.inr y)))
    intro t t' hA
    simp only [Option.elim, tr₂, e] at hA ⊢
    exact h t t' hA
  · have h := A.good_run c A.L₄ (Good.ext (A.good_run c A.L₃ (Good.ext h2 (.inr (.inl rq))))
      (.inr (.inr y)))
    intro t t' hA
    simp only [Option.elim, tr₂, tr₃, e] at hA ⊢
    exact h t t' hA

/-- **The reduction's guess budget**: the Issuer's plus the `n` Clients' reads. -/
theorem red_gBudget {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    (A.red c).GBudget q3 (n * (K + 1) * 624 + q5) (n * (K + 1) * 4607 + qE) := by
  intro T₁ m
  exact
    { h30 := fun _ _ g₁ g₂ g₃ s => hA.h30 _ g₁ g₂ g₃ s
      h31 := fun _ _ g₀ g₂ g₃ s => hA.h31 _ g₀ g₂ g₃ s
      h32 := fun _ _ g₀ g₁ g₃ s => hA.h32 _ g₀ g₁ g₃ s
      h33 := fun _ _ g₀ g₁ g₂ s => hA.h33 _ g₀ g₁ g₂ s
      h5 := fun tr y sl => Rd5.bindEq (m := fun s => A.tr₄ c (A.tr₃G c (A.tr₂ c T₁ tr s) y s) y s)
        (f := fun T s => A.guess T sl s) (fun _ => rfl)
        ((Good.sreads_R c (A.good_guess c T₁ tr y)).rd5 default) fun T => hA.h5 T sl
      hE := fun tr y sl => RdE.bindEq (m := fun s => A.tr₄ c (A.tr₃G c (A.tr₂ c T₁ tr s) y s) y s)
        (f := fun T s => A.guess T sl s) (fun _ => rfl)
        ((Good.sreads_R c (A.good_guess c T₁ tr y)).rdE default) fun T => hA.hE T sl }

end AdversaryILR

/-- The interleaved game's tape, with the further Clients' tapes first. -/
def tapeILR : (Fin n → XK K) × (((TRe × TRe) × (TRe × TRe)) × ShR R) ≃
    (((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR R where
  toFun z := ((z.2.1, z.1), z.2.2)
  invFun z := (z.1.2, (z.1.1, z.2))
  left_inv _ := rfl
  right_inv _ := rfl

end Game

/-! ## The bound -/

section Bound

variable {n K : ℕ}

/-- **Theorem 2 with interleaved further sessions that spend up to `K` times, for every type of
cipher rows** (`ZKRow R`, `ZKPRow R`; SHAKE as the base record): with at most `n` further Clients,
scheduled, started and answered in any order by the Issuer, the bound of
`unlinkabilityRAK_lean_numG` at the key-stage and interaction budgets
`n(K+1)·(0, 2³², 624, 4607)` and the guess budget `(q₃, q₅ + 624·n(K+1), q_E + 4607·n(K+1))`;
any two worlds. -/
theorem unlinkabilityIL_lean_numG [ZKRow R] [ZKPRow R] (A : AdversaryILR R) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : Fin n → XK K) b₁ b₂ Y,
      hidingAdv (A.atT c (A.tr₁ c Y.2.2)).ctx
        (reductionRA (A.atT c (A.tr₁ c Y.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ Y) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR R) (realGameILR A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR R) (realGameILR A b₁' b₂')| ≤
      4 * εAdG R pI 9 (2 * 0 + q3) (n * (K + 1) * 624 + q5 + 2 * (n * (K + 1) * 624) + 1872)
          (n * (K + 1) * 4607 + qE + 2 * (n * (K + 1) * 4607) + 13821) 0 (n * (K + 1) * nGrind) (n * (K + 1) * 624) (n * (K + 1) * 4607) +
        2 * εAdG R pS 9 (0 + q3) (n * (K + 1) * 624 + q5 + n * (K + 1) * 624 + 1248) (n * (K + 1) * 4607 + qE + n * (K + 1) * 4607 + 13821) (0 + 0)
          (n * (K + 1) * nGrind + n * (K + 1) * nGrind) (n * (K + 1) * 624 + n * (K + 1) * 624 + 624) (n * (K + 1) * 4607 + n * (K + 1) * 4607 + 9214) +
        2 * εAdG R pS 9 q3 (n * (K + 1) * 624 + q5 + 936) (n * (K + 1) * 4607 + qE + 13821) (0 + 2 * 0)
          (n * (K + 1) * nGrind + 2 * (n * (K + 1) * nGrind)) (n * (K + 1) * 624 + 2 * (n * (K + 1) * 624) + 1560) (n * (K + 1) * 4607 + 2 * (n * (K + 1) * 4607) + 23035) +
        2 * (((0 + 0 : ℕ) : ℝ) / 2 ^ 128) + 2 * (((0 + 2 * 0 : ℕ) : ℝ) / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + ZKPRow.εP R pS 0 312 4607 (n * (K + 1) * 624 + 2 * (n * (K + 1) * 624) + 1560)
          (n * (K + 1) * 4607 + 2 * (n * (K + 1) * 4607) + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  rw [← pr_equiv tapeILR, ← pr_equiv tapeILR]
  exact abs_pr_prod_sub_le _ _ fun c =>
    unlinkabilityRAK_lean_numG (A.red c) (A.red_gBudget c hA) (A.red_iBudget c) (A.red_kBudget c)
      (hhide c) b₁ b₂ b₁' b₂'

/-- **Theorem 2 with interleaved further sessions that spend up to `K` times** (function rows). -/
theorem unlinkabilityIL_lean_num (A : AdversaryILR (Blk → Blk)) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : Fin n → XK K) b₁ b₂ Y,
      hidingAdv (A.atT c (A.tr₁ c Y.2.2)).ctx
        (reductionRA (A.atT c (A.tr₁ c Y.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ Y) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILR A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILR A b₁' b₂')| ≤
      4 * εAd 9 (2 * 0 + q3) (n * (K + 1) * 624 + q5 + 2 * (n * (K + 1) * 624) + 1872)
          (n * (K + 1) * 4607 + qE + 2 * (n * (K + 1) * 4607) + 13821) 0 (n * (K + 1) * nGrind) (n * (K + 1) * 624) (n * (K + 1) * 4607) +
        2 * εAd 9 (0 + q3) (n * (K + 1) * 624 + q5 + n * (K + 1) * 624 + 1248) (n * (K + 1) * 4607 + qE + n * (K + 1) * 4607 + 13821) (0 + 0)
          (n * (K + 1) * nGrind + n * (K + 1) * nGrind) (n * (K + 1) * 624 + n * (K + 1) * 624 + 624) (n * (K + 1) * 4607 + n * (K + 1) * 4607 + 9214) +
        2 * εAd 9 q3 (n * (K + 1) * 624 + q5 + 936) (n * (K + 1) * 4607 + qE + 13821) (0 + 2 * 0)
          (n * (K + 1) * nGrind + 2 * (n * (K + 1) * nGrind)) (n * (K + 1) * 624 + 2 * (n * (K + 1) * 624) + 1560) (n * (K + 1) * 4607 + 2 * (n * (K + 1) * 4607) + 23035) +
        2 * (((0 + 0 : ℕ) : ℝ) / 2 ^ 128) + 2 * (((0 + 2 * 0 : ℕ) : ℝ) / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + εROP 0 312 4607 (n * (K + 1) * 624 + 2 * (n * (K + 1) * 624) + 1560)
          (n * (K + 1) * 4607 + 2 * (n * (K + 1) * 4607) + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityIL_lean_numG A hA hhide b₁ b₂ b₁' b₂'

/-- **The same with AES as uniformly random permutations.** -/
theorem unlinkabilityIL_lean_num_perm (A : AdversaryILR (Equiv.Perm Blk)) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : Fin n → XK K) b₁ b₂ Y,
      hidingAdv (A.atT c (A.tr₁ c Y.2.2)).ctx
        (reductionRA (A.atT c (A.tr₁ c Y.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ Y) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Equiv.Perm Blk)) (realGameILR A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Equiv.Perm Blk)) (realGameILR A b₁' b₂')| ≤
      4 * εAdPm pI 9 (2 * 0 + q3) (n * (K + 1) * 624 + q5 + 2 * (n * (K + 1) * 624) + 1872)
          (n * (K + 1) * 4607 + qE + 2 * (n * (K + 1) * 4607) + 13821) 0 (n * (K + 1) * nGrind) (n * (K + 1) * 624) (n * (K + 1) * 4607) +
        2 * εAdPm pS 9 (0 + q3) (n * (K + 1) * 624 + q5 + n * (K + 1) * 624 + 1248) (n * (K + 1) * 4607 + qE + n * (K + 1) * 4607 + 13821) (0 + 0)
          (n * (K + 1) * nGrind + n * (K + 1) * nGrind) (n * (K + 1) * 624 + n * (K + 1) * 624 + 624) (n * (K + 1) * 4607 + n * (K + 1) * 4607 + 9214) +
        2 * εAdPm pS 9 q3 (n * (K + 1) * 624 + q5 + 936) (n * (K + 1) * 4607 + qE + 13821) (0 + 2 * 0)
          (n * (K + 1) * nGrind + 2 * (n * (K + 1) * nGrind)) (n * (K + 1) * 624 + 2 * (n * (K + 1) * 624) + 1560) (n * (K + 1) * 4607 + 2 * (n * (K + 1) * 4607) + 23035) +
        2 * (((0 + 0 : ℕ) : ℝ) / 2 ^ 128) + 2 * (((0 + 2 * 0 : ℕ) : ℝ) / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + εROPmP pS 0 312 4607 (n * (K + 1) * 624 + 2 * (n * (K + 1) * 624) + 1560)
          (n * (K + 1) * 4607 + 2 * (n * (K + 1) * 4607) + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityIL_lean_numG A hA hhide b₁ b₂ b₁' b₂'

/-- **The interleaved bound in numbers**: with `n` further Clients spending up to `K` times each,
any two worlds differ by at most

    (n(K+1) + 2)·2⁻¹⁰¹ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ + 2·εhide,

for every schedule and every number of steps: linear in the further Clients' `n(K+1)` proofs
(per proof `≈ 2⁻¹⁰¹·⁷⁷`, the constant `≈ 2⁻¹⁰¹·⁶¹`). -/
theorem unlinkabilityIL_lean_le (A : AdversaryILR (Blk → Blk)) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : Fin n → XK K) b₁ b₂ Y,
      hidingAdv (A.atT c (A.tr₁ c Y.2.2)).ctx
        (reductionRA (A.atT c (A.tr₁ c Y.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ Y) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILR A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILR A b₁' b₂')| ≤
      (n * (K + 1) + 2 : ℕ) / 2 ^ 101 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := unlinkabilityIL_lean_num A hA hhide b₁ b₂ b₁' b₂'
  have u1 := εAd9_le (2 * 0 + q3) (n * (K + 1) * 624 + q5 + 2 * (n * (K + 1) * 624) + 1872)
    (n * (K + 1) * 4607 + qE + 2 * (n * (K + 1) * 4607) + 13821) 0 (n * (K + 1) * nGrind) (n * (K + 1) * 624) (n * (K + 1) * 4607)
  have u2 := εAd9_le (0 + q3) (n * (K + 1) * 624 + q5 + n * (K + 1) * 624 + 1248) (n * (K + 1) * 4607 + qE + n * (K + 1) * 4607 + 13821) (0 + 0)
    (n * (K + 1) * nGrind + n * (K + 1) * nGrind) (n * (K + 1) * 624 + n * (K + 1) * 624 + 624) (n * (K + 1) * 4607 + n * (K + 1) * 4607 + 9214)
  have u3 := εAd9_le q3 (n * (K + 1) * 624 + q5 + 936) (n * (K + 1) * 4607 + qE + 13821) (0 + 2 * 0)
    (n * (K + 1) * nGrind + 2 * (n * (K + 1) * nGrind)) (n * (K + 1) * 624 + 2 * (n * (K + 1) * 624) + 1560) (n * (K + 1) * 4607 + 2 * (n * (K + 1) * 4607) + 23035)
  have g1 := grind_le (n * (K + 1) * nGrind) (n * (K + 1))
    (Nat.mul_le_mul_left (n * (K + 1)) (show nGrind ≤ 4 * nGrind by omega))
  have g2 := grind_le (n * (K + 1) * nGrind + n * (K + 1) * nGrind) (n * (K + 1)) (by
    calc n * (K + 1) * nGrind + n * (K + 1) * nGrind = n * (K + 1) * (2 * nGrind) := by ring
      _ ≤ n * (K + 1) * (4 * nGrind) := Nat.mul_le_mul_left _ (by omega))
  have g3 := grind_le (n * (K + 1) * nGrind + 2 * (n * (K + 1) * nGrind)) (n * (K + 1)) (by
    calc n * (K + 1) * nGrind + 2 * (n * (K + 1) * nGrind) = n * (K + 1) * (3 * nGrind) := by ring
      _ ≤ n * (K + 1) * (4 * nGrind) := Nat.mul_le_mul_left _ (by omega))
  have hn := noHitProb_le_128
  have hn0 : 0 ≤ noHitProb := pr_nonneg _
  have h1 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have h12 : (0 : ℝ) ≤ (n : ℝ) * ((K : ℝ) + 1) := mul_nonneg h1 (by linarith)
  have hK : (12 : ℝ) / 2 ^ 1024 ≤ 1 / 2 ^ 128 := by
    have e1024 : (2 : ℝ) ^ 1024 = 2 ^ 128 * 2 ^ 896 := by rw [← pow_add]
    have hb : (2 : ℝ) ^ 32 ≤ 2 ^ 896 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hp : (0 : ℝ) < 2 ^ 128 := by positivity
    rw [e1024, div_le_div_iff₀ (by positivity) (by positivity)]
    have h16 : (12 : ℝ) ≤ 2 ^ 32 := by norm_num
    calc (12 : ℝ) * 2 ^ 128 ≤ 2 ^ 896 * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right (h16.trans hb) hp.le
      _ = 1 * (2 ^ 128 * 2 ^ 896) := by rw [one_mul, mul_comm]
  generalize (2 : ℝ) ^ 1024 = κ at hK g1 g2 g3 u1 u2 u3 h
  unfold εROP εRO at h u1 u2 u3
  push_cast at h u1 u2 u3 g1 g2 g3 ⊢
  generalize (n : ℝ) * ((K : ℝ) + 1) = P at h u1 u2 u3 g1 g2 g3 h12 ⊢
  have e : ∀ x : ℝ, x / 2 ^ 101 = x * 134217728 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  rw [e]
  linarith

/-- **`2²⁰` proofs**: with `n(K+1) + 2 ≤ 2²⁰`, `≤ 2⁻⁸¹ + 2·εhide` plus the guess's budget terms. -/
theorem unlinkabilityIL_lean_2pow20 (A : AdversaryILR (Blk → Blk)) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : Fin n → XK K) b₁ b₂ Y,
      hidingAdv (A.atT c (A.tr₁ c Y.2.2)).ctx
        (reductionRA (A.atT c (A.tr₁ c Y.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ Y) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) (hn : n * (K + 1) + 2 ≤ 2 ^ 20) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILR A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILR A b₁' b₂')| ≤
      1 / 2 ^ 81 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := unlinkabilityIL_lean_le A hA hhide b₁ b₂ b₁' b₂'
  have : ((n * (K + 1) + 2 : ℕ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hn
  have h2 : ((n * (K + 1) + 2 : ℕ) : ℝ) / 2 ^ 101 ≤ 1 / 2 ^ 81 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **`2³²` proofs**: with `n(K+1) + 2 ≤ 2³²`, `≤ 2⁻⁶⁹ + 2·εhide` plus the guess's budget terms. -/
theorem unlinkabilityIL_lean_2pow32 (A : AdversaryILR (Blk → Blk)) {q3 q5 qE : ℕ}
    {εhide : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ (c : Fin n → XK K) b₁ b₂ Y,
      hidingAdv (A.atT c (A.tr₁ c Y.2.2)).ctx
        (reductionRA (A.atT c (A.tr₁ c Y.2.2)) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ Y) ≤
        εhide)
    (b₁ b₂ b₁' b₂' : Bool) (hn : n * (K + 1) + 2 ≤ 2 ^ 32) :
    |pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILR A b₁ b₂) -
        pr ((((TRe × TRe) × (TRe × TRe)) × (Fin n → XK K)) × ShR (Blk → Blk)) (realGameILR A b₁' b₂')| ≤
      1 / 2 ^ 69 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have h := unlinkabilityIL_lean_le A hA hhide b₁ b₂ b₁' b₂'
  have : ((n * (K + 1) + 2 : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have h2 : ((n * (K + 1) + 2 : ℕ) : ℝ) / 2 ^ 101 ≤ 1 / 2 ^ 69 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end Bound

end VoleMole.Privacy.Ratatouille
