import VoleMole.Privacy.RatatouilleDelta
import VoleMole.ZK.AdaptRO

/-!
# Ratatouille unlinkability with an Issuer whose interaction reads the tables

`unlinkabilityRO_lean_num` (`Privacy/RatatouilleRO.lean`, `Privacy/RatatouilleDelta.lean`) assumes
that the Issuer's interaction (its issuance responses, the amounts `d₁`, `d₂`, its response to
round 1's spend) does not read the random tables; only its guess does. Here it does
(`AdversaryRA`): every message is a function of what the Issuer has seen, the four `H₃` slices and
the shared tables (`H₂³`, `H₅`, the cipher). This is the construction of `Privacy/MoussakaRA.lean`
on `RatatouilleRO`'s game; the interaction has two stages instead of one.

## The model

* **The interaction** (`AdversaryRA`): stage 1 (`msg₁`: the two issuance responses and `d₁`) from
  the issuance requests, stage 2 (`msg₂`: the response to round 1 and `d₂`) also from round 1's
  request. Its budget (`AdversaryRA.IBudget i₃ i₂ i₅ i_E`): each stage, as a function of each slice
  and the shared tables (the other slices fixed), reads at most `i₃` slice keys, `i₂` `H₂³` keys,
  `i₅` `H₅` keys and `i_E` cipher keys, consistently (`ZK.Sim.SReads`).
* **The game** (`viewRA`): `viewR` for the Issuer with its messages fixed to the transcript
  (`AdversaryRA.fixR`, `transR`), each message read on the tables as the simulations **before it**
  programmed them: stage 1 after the issuances, stage 2 after the issuances and round 1 (round 1's
  programming happens only if round 1 runs, as in `viewR`). Round 1's real proof runs on the tables
  after the issuances, round 2's after round 1. With real slots nothing is programmed and every
  message, proof and the guess read the uniform tables themselves (`realGameRA`): the spec's
  protocol with every hash and the cipher uniform tables and the Issuer querying them. In every
  hybrid a real round 1 runs on the tables after the issuances and a real round 2 on those after
  round 1. The transcript needs no provisional round: it computes round 1's request on the tables
  after the issuances, which do not depend on the spends' programming.

## The hybrids

As in `unlinkabilityRO`: issuance `0`, issuance `1`, round 1, round 2.
* **Issuances** (`hopI0RA`, `hopI1RA`): `hop_ro` with the fixed-statement theorem; both stages of
  the interaction, the two real spends and the guess are the distinguisher, each real proof counted
  once (`rd5_viewRA`: `3·624` `H₅`, `3·4607` cipher keys), each slice read `2i₃ + q₃` times.
* **Round 1** (`hopS1RA`): `hop_roA` with `ZeroKnowledgeROA`. The statement (round 1's token and
  `d₁`) is read off the tables by stage 1 (`Sx1`), through the two issuance simulations'
  programming (`sReads_Sx1`: `(i₃, i₂, i₅ + 624, i_E + 9214)`). Stage 2 reads round 1's proof:
  it is part of the distinguisher (`FS1A`), with round 2's real proof and the guess.
* **Round 2** (`hopS2RA`): `hop_roA`; the statement is read off the tables by the whole transcript
  (`Sx2`), stage 2 also through round 1's programming, which depends on stage 1's messages
  (`sReads_Sx2`: `(2i₃, 2i₂, 2i₅ + 1560, 2i_E + 23035)`).
* The collision terms of the spend hops (`deltaS1A_le`, `deltaS2A_le`) are
  `ZK.Sim.pr_collide_adaptive`; issuance `1`'s is `deltaI1R_le`.
* **The end** (`simGameRA_iff`): the simulated world is `Ratatouille.view` for the Issuer at fixed
  simulator coins, slices and tables (`atRA`), whose messages read the tables programmed by the
  simulations before them as functions of the requests it has seen (`U₁`, `U₂`, from
  `issSim_prog`, `spSim_prog`) and whose guess reads `Vtab`. Two Issuers that agree on what the game
  asks them give the same view (`view_congr`); round 2's messages matter only if round 1 runs.
  Hiding and the exchange of the nullifiers finish as in `unlinkabilityRO`.

**`unlinkabilityRA_lean_num`**: any two worlds differ by at most

    4·εRO(2i₃ + q₃, q₅ + 2i₅ + 1872, q_E + 2i_E + 13821)
      + 2·εAd(9; i₃ + q₃, q₅ + i₅ + 1248, q_E + i_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214)
      + 2·εAd(9; q₃, q₅ + 936, q_E + 13821; 2i₃, 2i₂, 2i₅ + 1560, 2i_E + 23035)
      + 6·i₃·2⁻¹²⁸ + 4·(2⁻¹¹³ + εROP(0, 312, 4607; 2i₅ + 1560, 2i_E + 23035))
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

**Cipher rows.** Everything here is stated for every type of cipher rows `R` (the shared
tables `ZK.Sim.ShG R p`, `ZK/ReadsRO.lean`) with `ZKRow R`, `ZKPRow R`; `unlinkabilityRA_lean_numG` is the generic
Lean-prover bound and `unlinkabilityRA_lean_num` its instance at function rows (`Blk → Blk`, the PRF
view); `Privacy/PermRA.lean` instantiates it at permutation rows (AES as uniformly random
permutations, the adversary reading whole rows: forward and inverse queries).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim

variable {Z : Sizes} {R : Type} [Fintype R] [Nonempty R]

/-! ## The model -/

/-- **The stage-1 messages**: the responses to issuances `0`, `1` and round 1's amount `d₁`. -/
abbrev M₁ := (Preimage × Preimage) × Credits

/-- **The stage-2 messages**: the response to round 1's spend and round 2's amount `d₂`. -/
abbrev M₂ := SpendResponse × Credits

/-- The Issuer's messages in one game. -/
abbrev MsgR := M₁ × M₂

/-- A stage-1 message where none is used (irreducible: the unifier must not compute it). -/
@[irreducible] def m1dflt : M₁ := ((Vector.ofFn fun _ => 0, Vector.ofFn fun _ => 0), 0)

/-- A stage-2 message where none is used. -/
@[irreducible] def m2dflt : M₂ := (Vector.ofFn fun _ => 0, 0)

/-- **The malicious Issuer whose interaction reads the tables**: its key, context and balance, its
messages as functions of what it has seen, the four `H₃` slices and the shared tables, and its
guess. -/
structure AdversaryRA (R : Type) (Z : Sizes) where
  pk : PublicKey
  ctx : Context
  tInit : Credits
  respondIss : IssTr Z → Bool → SlicesR → ShR R → Preimage
  d₁ : IssTr Z → SlicesR → ShR R → Credits
  respond₁ : IssTr Z → Except Error (SpendRequest Z) → SlicesR → ShR R → SpendResponse
  d₂ : IssTr Z → Except Error (SpendRequest Z) → SlicesR → ShR R → Credits
  guess : IssTr Z → Rounds Z → SlicesR → ShR R → Prop

namespace AdversaryRA

variable (A : AdversaryRA R Z)

/-- The stage-1 messages at the issuance transcript `tr`, read on the slices `sl` and tables `u`. -/
def msg₁ (tr : IssTr Z) (sl : SlicesR) (u : ShR R) : M₁ :=
  ((A.respondIss tr false sl u, A.respondIss tr true sl u), A.d₁ tr sl u)

/-- The stage-2 messages at `tr` and round 1's request `rq`. -/
def msg₂ (tr : IssTr Z) (rq : Except Error (SpendRequest Z)) (sl : SlicesR) (u : ShR R) : M₂ :=
  (A.respond₁ tr rq sl u, A.d₂ tr rq sl u)

/-- **The Issuer with its messages fixed**, as an `AdversaryRO`. -/
def fixR (m : MsgR) : AdversaryRO R Z :=
  ⟨A.pk, A.ctx, A.tInit, fun _ c => bif c then m.1.1.2 else m.1.1.1, fun _ => m.1.2,
    fun _ _ => m.2.1, fun _ _ => m.2.2, A.guess⟩

/-- The Issuer's key, context and balance, as an `AdversaryRO` (for the slots). -/
def toRO : AdversaryRO R Z := A.fixR (m1dflt, m2dflt)

/-- **The interaction's budget**: each stage's messages, as a function of each slice and the
shared tables (the other slices fixed), read at most `i₃` slice keys, `i₂` `H₂³` keys, `i₅` `H₅`
keys and `i_E` cipher keys, consistently (`ZK.Sim.SReads`). -/
structure IBudget (i3 i2 i5 iE : ℕ) : Prop where
  a0 : ∀ tr (g₁ g₂ g₃ : Tab3),
    SReads pI (fun t : Tb R pI => A.msg₁ tr ((t.1, g₁), (g₂, g₃)) t.2) i3 i2 i5 iE
  a1 : ∀ tr (g₀ g₂ g₃ : Tab3),
    SReads pI (fun t : Tb R pI => A.msg₁ tr ((g₀, t.1), (g₂, g₃)) t.2) i3 i2 i5 iE
  a2 : ∀ tr (g₀ g₁ g₃ : Tab3),
    SReads pS (fun t : Tb R pS => A.msg₁ tr ((g₀, g₁), (t.1, g₃)) t.2) i3 i2 i5 iE
  a3 : ∀ tr (g₀ g₁ g₂ : Tab3),
    SReads pS (fun t : Tb R pS => A.msg₁ tr ((g₀, g₁), (g₂, t.1)) t.2) i3 i2 i5 iE
  b0 : ∀ tr rq (g₁ g₂ g₃ : Tab3),
    SReads pI (fun t : Tb R pI => A.msg₂ tr rq ((t.1, g₁), (g₂, g₃)) t.2) i3 i2 i5 iE
  b1 : ∀ tr rq (g₀ g₂ g₃ : Tab3),
    SReads pI (fun t : Tb R pI => A.msg₂ tr rq ((g₀, t.1), (g₂, g₃)) t.2) i3 i2 i5 iE
  b2 : ∀ tr rq (g₀ g₁ g₃ : Tab3),
    SReads pS (fun t : Tb R pS => A.msg₂ tr rq ((g₀, g₁), (t.1, g₃)) t.2) i3 i2 i5 iE
  b3 : ∀ tr rq (g₀ g₁ g₂ : Tab3),
    SReads pS (fun t : Tb R pS => A.msg₂ tr rq ((g₀, g₁), (g₂, t.1)) t.2) i3 i2 i5 iE

/-- **The guess's budget** (`AdversaryRO.Budget`). -/
def GBudget (q3 q5 qE : ℕ) : Prop := ∀ m, (A.fixR m).Budget q3 q5 qE

end AdversaryRA

variable (A : AdversaryRA R Z)

/-! ## The game -/

/-- **Stage 2 of the transcript**, given stage 1's messages `m₁`: round 1 on the tables after the
issuances, then the stage-2 messages read on the slices `sl` and the tables after the issuances and
round 1 (programmed by the simulations among them). The slots enter through their outputs and
programmings. -/
def trans₂ (b₁ : Bool) (sl : SlicesR) (m₁ : M₁) (o₀ : ShR R → IssOut Z TokenS) (P₀ : ShR R → ShR R)
    (o₁ : ShR R → IssOut Z TokenS) (P₁ : ShR R → ShR R) (k₁ : TokenS → Credits → ShR R → SpOut Z TokenS)
    (Q₁ : Bool → TokenS → Credits → ShR R → ShR R) (t : ShR R) : M₂ :=
  let u := P₀ (P₁ t)
  let i₀ := o₀ u
  let i₁ := o₁ u
  let B := A.fixR (m₁, m2dflt)
  let τ₁ := τ₁Of B b₁ i₀ i₁
  let ok1 := ok₁ B.base (tokIface B.base) (i₀.req, i₁.req) (i₀.fin m₁.1.1) (i₁.fin m₁.1.2)
  A.msg₂ (i₀.req, i₁.req) (k₁ τ₁ m₁.2 u).req sl (P₀ (P₁ (Q₁ ok1 τ₁ m₁.2 t)))

/-- **The transcript**: the stage-1 messages read on the tables after the issuances, then stage 2. -/
def transS (b₁ : Bool) (sl : SlicesR) (o₀ : ShR R → IssOut Z TokenS) (P₀ : ShR R → ShR R)
    (o₁ : ShR R → IssOut Z TokenS) (P₁ : ShR R → ShR R) (k₁ : TokenS → Credits → ShR R → SpOut Z TokenS)
    (Q₁ : Bool → TokenS → Credits → ShR R → ShR R) (t : ShR R) : MsgR :=
  let m₁ := A.msg₁ ((o₀ (P₀ (P₁ t))).req, (o₁ (P₀ (P₁ t))).req) sl (P₀ (P₁ t))
  (m₁, trans₂ A b₁ sl m₁ o₀ P₀ o₁ P₁ k₁ Q₁ t)

/-- The transcript of four slots. -/
def transR (b₁ : Bool) (s₀ s₁ : IssSlotR R Z) (h₁ h₂ : SpSlotR R Z) (t : ShR R) : MsgR :=
  transS A b₁ ((s₀.slice, s₁.slice), (h₁.slice, h₂.slice)) s₀.out s₀.prog s₁.out s₁.prog h₁.out
    h₁.prog t

/-- **The view in world `(b₁, b₂)`**: `viewR` for the Issuer with its messages fixed to the
transcript, read on the tables as the simulations before each message programmed them. With real
slots (no programming) every message and the guess read the uniform tables `t` themselves. -/
def viewRA (b₁ b₂ : Bool) (s₀ s₁ : IssSlotR R Z) (h₁ h₂ : SpSlotR R Z) (t : ShR R) : Prop :=
  viewR (A.fixR (transR A b₁ s₀ s₁ h₁ h₂ t)) b₁ b₂ s₀ s₁ h₁ h₂ t

/-- The game with the slots drawn from their parts of the tape. -/
def gameRA {T₀ T₁ T₂ T₃ : Type} (b₁ b₂ : Bool) (g₀ : T₀ → IssSlotR R Z) (g₁ : T₁ → IssSlotR R Z)
    (k₁ : T₂ → SpSlotR R Z) (k₂ : T₃ → SpSlotR R Z) (x : ((T₀ × T₁) × (T₂ × T₃)) × ShR R) : Prop :=
  viewRA A b₁ b₂ (g₀ x.1.1.1) (g₁ x.1.1.2) (k₁ x.1.2.1) (k₂ x.1.2.2) x.2

/-- **The real game**: the spec's protocol with every proof computed on the shared uniform tables,
the Issuer's interaction and guess reading them. -/
def realGameRA (PI : ProverI R Z) (PS : ProverS R Z) (b₁ b₂ : Bool) :
    ((TRe × TRe) × (TRe × TRe)) × ShR R → Prop :=
  gameRA A b₁ b₂ (issRealR A.toRO PI) (issRealR A.toRO PI) (spRealR A.toRO PS) (spRealR A.toRO PS)

/-! ## Reads of the game -/

section Reads

variable {A} {q3 q5 qE i3 i2 i5 iE : ℕ}

/-- **Stage 2 as a function of a slice** reads it as the stage-2 messages do. -/
lemma rd3_trans₂ {σ : Tab3 → SlicesR} (h2 : ∀ tr rq u, Rd3 (fun g => A.msg₂ tr rq (σ g) u) i3)
    (b₁ : Bool) (m₁ : M₁) (o₀ : ShR R → IssOut Z TokenS) (P₀ : ShR R → ShR R) (o₁ : ShR R → IssOut Z TokenS)
    (P₁ : ShR R → ShR R) (k₁ : TokenS → Credits → ShR R → SpOut Z TokenS)
    (Q₁ : Bool → TokenS → Credits → ShR R → ShR R) (t : ShR R) :
    Rd3 (fun g => trans₂ A b₁ (σ g) m₁ o₀ P₀ o₁ P₁ k₁ Q₁ t) i3 :=
  h2 _ _ _

/-- **The transcript as a function of a slice** reads it at most `2·i₃` times. -/
lemma rd3_transS {σ : Tab3 → SlicesR} (h1 : ∀ tr u, Rd3 (fun g => A.msg₁ tr (σ g) u) i3)
    (h2 : ∀ tr rq u, Rd3 (fun g => A.msg₂ tr rq (σ g) u) i3)
    (b₁ : Bool) (o₀ : ShR R → IssOut Z TokenS) (P₀ : ShR R → ShR R) (o₁ : ShR R → IssOut Z TokenS)
    (P₁ : ShR R → ShR R) (k₁ : TokenS → Credits → ShR R → SpOut Z TokenS)
    (Q₁ : Bool → TokenS → Credits → ShR R → ShR R) (t : ShR R) :
    Rd3 (fun g => transS A b₁ (σ g) o₀ P₀ o₁ P₁ k₁ Q₁ t) (i3 + i3) :=
  Rd3.bind (m := fun g => A.msg₁ ((o₀ (P₀ (P₁ t))).req, (o₁ (P₀ (P₁ t))).req) (σ g) (P₀ (P₁ t)))
    (f := fun m₁ g => (m₁, trans₂ A b₁ (σ g) m₁ o₀ P₀ o₁ P₁ k₁ Q₁ t)) (h1 _ _)
    fun m₁ => (rd3_trans₂ h2 b₁ m₁ o₀ P₀ o₁ P₁ k₁ Q₁ t).map (Prod.mk m₁)

lemma rd3_viewRA0 (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE) (b₁ b₂ : Bool)
    (o₀ : ShR R → IssOut Z TokenS) (P₀ : ShR R → ShR R) (s₁ : IssSlotR R Z) (h₁ h₂ : SpSlotR R Z)
    (u : ShR R) : Rd3 (fun g => viewRA A b₁ b₂ ⟨o₀, P₀, g⟩ s₁ h₁ h₂ u) (i3 + i3 + q3) :=
  Rd3.bind (m := fun g => transS A b₁ ((g, s₁.slice), (h₁.slice, h₂.slice)) o₀ P₀ s₁.out s₁.prog
      h₁.out h₁.prog u)
    (f := fun m g => viewR (A.fixR m) b₁ b₂ ⟨o₀, P₀, g⟩ s₁ h₁ h₂ u)
    (rd3_transS (σ := fun g => ((g, s₁.slice), (h₁.slice, h₂.slice)))
      (fun _ u => SReads.rd3 (hI.a0 _ _ _ _) u) (fun _ _ u => SReads.rd3 (hI.b0 _ _ _ _ _) u)
      _ _ _ _ _ _ _ _)
    fun m => rd3_viewR0 (hA m) b₁ b₂ o₀ P₀ s₁ h₁ h₂ u

lemma rd3_viewRA1 (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE) (b₁ b₂ : Bool)
    (s₀ : IssSlotR R Z) (o₁ : ShR R → IssOut Z TokenS) (P₁ : ShR R → ShR R) (h₁ h₂ : SpSlotR R Z)
    (u : ShR R) : Rd3 (fun g => viewRA A b₁ b₂ s₀ ⟨o₁, P₁, g⟩ h₁ h₂ u) (i3 + i3 + q3) :=
  Rd3.bind (m := fun g => transS A b₁ ((s₀.slice, g), (h₁.slice, h₂.slice)) s₀.out s₀.prog o₁ P₁
      h₁.out h₁.prog u)
    (f := fun m g => viewR (A.fixR m) b₁ b₂ s₀ ⟨o₁, P₁, g⟩ h₁ h₂ u)
    (rd3_transS (σ := fun g => ((s₀.slice, g), (h₁.slice, h₂.slice)))
      (fun _ u => SReads.rd3 (hI.a1 _ _ _ _) u) (fun _ _ u => SReads.rd3 (hI.b1 _ _ _ _ _) u)
      _ _ _ _ _ _ _ _)
    fun m => rd3_viewR1 (hA m) b₁ b₂ s₀ o₁ P₁ h₁ h₂ u

lemma rd3_viewRA2 (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE) (b₁ b₂ : Bool)
    (s₀ s₁ : IssSlotR R Z) (k₁ : TokenS → Credits → ShR R → SpOut Z TokenS)
    (Q₁ : Bool → TokenS → Credits → ShR R → ShR R) (h₂ : SpSlotR R Z)
    (u : ShR R) : Rd3 (fun g => viewRA A b₁ b₂ s₀ s₁ ⟨k₁, Q₁, g⟩ h₂ u) (i3 + i3 + q3) :=
  Rd3.bind (m := fun g => transS A b₁ ((s₀.slice, s₁.slice), (g, h₂.slice)) s₀.out s₀.prog s₁.out
      s₁.prog k₁ Q₁ u)
    (f := fun m g => viewR (A.fixR m) b₁ b₂ s₀ s₁ ⟨k₁, Q₁, g⟩ h₂ u)
    (rd3_transS (σ := fun g => ((s₀.slice, s₁.slice), (g, h₂.slice)))
      (fun _ u => SReads.rd3 (hI.a2 _ _ _ _) u) (fun _ _ u => SReads.rd3 (hI.b2 _ _ _ _ _) u)
      _ _ _ _ _ _ _ _)
    fun m => rd3_viewR2 (hA m) b₁ b₂ s₀ s₁ k₁ Q₁ h₂ u

lemma rd3_viewRA3 (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE) (b₁ b₂ : Bool)
    (s₀ s₁ : IssSlotR R Z) (h₁ : SpSlotR R Z) (k₂ : TokenS → Credits → ShR R → SpOut Z TokenS)
    (Q₂ : Bool → TokenS → Credits → ShR R → ShR R)
    (u : ShR R) : Rd3 (fun g => viewRA A b₁ b₂ s₀ s₁ h₁ ⟨k₂, Q₂, g⟩ u) (i3 + i3 + q3) :=
  Rd3.bind (m := fun g => transS A b₁ ((s₀.slice, s₁.slice), (h₁.slice, g)) s₀.out s₀.prog s₁.out
      s₁.prog h₁.out h₁.prog u)
    (f := fun m g => viewR (A.fixR m) b₁ b₂ s₀ s₁ h₁ ⟨k₂, Q₂, g⟩ u)
    (rd3_transS (σ := fun g => ((s₀.slice, s₁.slice), (h₁.slice, g)))
      (fun _ u => SReads.rd3 (hI.a3 _ _ _ _) u) (fun _ _ u => SReads.rd3 (hI.b3 _ _ _ _ _) u)
      _ _ _ _ _ _ _ _)
    fun m => rd3_viewR3 (hA m) b₁ b₂ s₀ s₁ h₁ k₂ Q₂ u

/-- **The view, with slots that do not program, reads what its slots, the messages and the guess
read**, each real proof once. -/
lemma rd5_viewRA (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE) (b₁ b₂ : Bool)
    (o₀ o₁ : ShR R → IssOut Z TokenS) (g₀ g₁ g₂ g₃ : Tab3)
    (k₁ k₂ : TokenS → Credits → ShR R → SpOut Z TokenS) {a₀ a₁ c₁ c₂ : ℕ}
    (h₀ : Rd5 o₀ a₀) (h₁ : Rd5 o₁ a₁) (hk₁ : ∀ τ d, Rd5 (k₁ τ d) c₁)
    (hk₂ : ∀ τ d, Rd5 (k₂ τ d) c₂) :
    Rd5 (fun u => viewRA A b₁ b₂ ⟨o₀, fun t => t, g₀⟩ ⟨o₁, fun t => t, g₁⟩
      ⟨k₁, fun _ _ _ t => t, g₂⟩ ⟨k₂, fun _ _ _ t => t, g₃⟩ u)
      (a₀ + (a₁ + (i5 + (c₁ + (i5 + (c₂ + q5)))))) :=
  Rd5.bind4 (m₀ := o₀) (m₁ := o₁) (m₂ := fun i₀ i₁ u => A.msg₁ (i₀.req, i₁.req) ((g₀, g₁), (g₂, g₃)) u)
    (m₃ := fun i₀ i₁ m₁ u => k₁ (τ₁Of (A.fixR (m₁, m2dflt)) b₁ i₀ i₁) m₁.2 u)
    (f := fun i₀ i₁ m₁ O₁ u => A.guess (i₀.req, i₁.req)
      (guessY (A.fixR (m₁, A.msg₂ (i₀.req, i₁.req) O₁.req ((g₀, g₁), (g₂, g₃)) u)) b₁ i₀ i₁ O₁
        (k₂ (τ₂Of (A.fixR (m₁, A.msg₂ (i₀.req, i₁.req) O₁.req ((g₀, g₁), (g₂, g₃)) u)) b₁ b₂ i₀ i₁
          O₁) (A.msg₂ (i₀.req, i₁.req) O₁.req ((g₀, g₁), (g₂, g₃)) u).2 u))
      ((g₀, g₁), (g₂, g₃)) u)
    h₀ h₁ (fun _ _ => SReads.rd5 (hI.a0 _ _ _ _) g₀) (fun _ _ _ => hk₁ _ _)
    fun i₀ i₁ m₁ O₁ =>
      Rd5.bind (m := fun u => A.msg₂ (i₀.req, i₁.req) O₁.req ((g₀, g₁), (g₂, g₃)) u)
        (f := fun m₂ u => A.guess (i₀.req, i₁.req)
          (guessY (A.fixR (m₁, m₂)) b₁ i₀ i₁ O₁ (k₂ (τ₂Of (A.fixR (m₁, m₂)) b₁ b₂ i₀ i₁ O₁) m₂.2 u))
          ((g₀, g₁), (g₂, g₃)) u)
        (SReads.rd5 (hI.b0 _ _ _ _ _) g₀) fun m₂ =>
          Rd5.bind (m := fun u => k₂ (τ₂Of (A.fixR (m₁, m₂)) b₁ b₂ i₀ i₁ O₁) m₂.2 u)
            (f := fun O₂ u => A.guess (i₀.req, i₁.req) (guessY (A.fixR (m₁, m₂)) b₁ i₀ i₁ O₁ O₂)
              ((g₀, g₁), (g₂, g₃)) u)
            (hk₂ _ _) fun _ => (hA (m₁, m₂)).h5 _ _ _

lemma rdE_viewRA (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE) (b₁ b₂ : Bool)
    (o₀ o₁ : ShR R → IssOut Z TokenS) (g₀ g₁ g₂ g₃ : Tab3)
    (k₁ k₂ : TokenS → Credits → ShR R → SpOut Z TokenS) {a₀ a₁ c₁ c₂ : ℕ}
    (h₀ : RdE o₀ a₀) (h₁ : RdE o₁ a₁) (hk₁ : ∀ τ d, RdE (k₁ τ d) c₁)
    (hk₂ : ∀ τ d, RdE (k₂ τ d) c₂) :
    RdE (fun u => viewRA A b₁ b₂ ⟨o₀, fun t => t, g₀⟩ ⟨o₁, fun t => t, g₁⟩
      ⟨k₁, fun _ _ _ t => t, g₂⟩ ⟨k₂, fun _ _ _ t => t, g₃⟩ u)
      (a₀ + (a₁ + (iE + (c₁ + (iE + (c₂ + qE)))))) :=
  RdE.bind4 (m₀ := o₀) (m₁ := o₁) (m₂ := fun i₀ i₁ u => A.msg₁ (i₀.req, i₁.req) ((g₀, g₁), (g₂, g₃)) u)
    (m₃ := fun i₀ i₁ m₁ u => k₁ (τ₁Of (A.fixR (m₁, m2dflt)) b₁ i₀ i₁) m₁.2 u)
    (f := fun i₀ i₁ m₁ O₁ u => A.guess (i₀.req, i₁.req)
      (guessY (A.fixR (m₁, A.msg₂ (i₀.req, i₁.req) O₁.req ((g₀, g₁), (g₂, g₃)) u)) b₁ i₀ i₁ O₁
        (k₂ (τ₂Of (A.fixR (m₁, A.msg₂ (i₀.req, i₁.req) O₁.req ((g₀, g₁), (g₂, g₃)) u)) b₁ b₂ i₀ i₁
          O₁) (A.msg₂ (i₀.req, i₁.req) O₁.req ((g₀, g₁), (g₂, g₃)) u).2 u))
      ((g₀, g₁), (g₂, g₃)) u)
    h₀ h₁ (fun _ _ => SReads.rdE (hI.a0 _ _ _ _) g₀) (fun _ _ _ => hk₁ _ _)
    fun i₀ i₁ m₁ O₁ =>
      RdE.bind (m := fun u => A.msg₂ (i₀.req, i₁.req) O₁.req ((g₀, g₁), (g₂, g₃)) u)
        (f := fun m₂ u => A.guess (i₀.req, i₁.req)
          (guessY (A.fixR (m₁, m₂)) b₁ i₀ i₁ O₁ (k₂ (τ₂Of (A.fixR (m₁, m₂)) b₁ b₂ i₀ i₁ O₁) m₂.2 u))
          ((g₀, g₁), (g₂, g₃)) u)
        (SReads.rdE (hI.b0 _ _ _ _ _) g₀) fun m₂ =>
          RdE.bind (m := fun u => k₂ (τ₂Of (A.fixR (m₁, m₂)) b₁ b₂ i₀ i₁ O₁) m₂.2 u)
            (f := fun O₂ u => A.guess (i₀.req, i₁.req) (guessY (A.fixR (m₁, m₂)) b₁ i₀ i₁ O₁ O₂)
              ((g₀, g₁), (g₂, g₃)) u)
            (hk₂ _ _) fun _ => (hA (m₁, m₂)).hE _ _ _

end Reads

/-! ## The issuance hops -/

section HopsI

variable {A} {CI : Type} {simI : IssueInstance → CI → Option (IssueProof Z)}
  {progI : IssueInstance → CI → ShR R → ShR R} {PI : ProverI R Z} {PS : ProverS R Z}
  {q3 q5 qE i3 i2 i5 iE r5 rE m5 mE : ℕ}

variable (A PI PS) in
/-- The rest of the game around issuance `0`'s output. -/
def F0A (b₁ b₂ : Bool) (γ : NRR × (TRe × (TRe × TRe))) (o : IssOut Z TokenS) (g : Tab3) (u : ShR R) :
    Prop :=
  viewRA A b₁ b₂ (fakeI o g) (issRealR A.toRO PI γ.2.1) (spRealR A.toRO PS γ.2.2.1)
    (spRealR A.toRO PS γ.2.2.2) u

theorem hopI0RA [Fintype CI] [Nonempty CI] (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPI5 : ∀ x w ρ g, Rd5 (PI x w ρ g) r5) (hPIE : ∀ x w ρ g, RdE (PI x w ρ g) rE)
    (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) r5) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) rE)
    {ε : ℝ} (hε : 0 ≤ ε) (hIzk : ZeroKnowledgeRO IssueRel
      (fun x w (ρ : Coins 16) g s => PI x w (vec ρ) g s) simI progI
      (Budget pI (i3 + i3 + q3) (0 + (r5 + (i5 + (r5 + (i5 + (r5 + q5))))))
        (0 + (rE + (iE + (rE + (iE + (rE + qE))))))) ε) (b₁ b₂ : Bool) :
    |pr _ (gameRA A b₁ b₂ (issRealR A.toRO PI) (issRealR A.toRO PI) (spRealR A.toRO PS)
        (spRealR A.toRO PS)) -
      pr _ (gameRA A b₁ b₂ (issSimR A.toRO simI progI) (issRealR A.toRO PI) (spRealR A.toRO PS)
        (spRealR A.toRO PS))| ≤ ε := by
  have h := hop_ro (Γ := NRR × (TRe × (TRe × TRe))) (ρ := Coins 16) (G := Tab3) (C := CI) (S := ShR R)
    (fun γ ρ g s => (issRealR A.toRO PI (γ.1, (ρ, g))).out s)
    (fun γ c => issSim A.toRO.base simI (γ.1.1, γ.1.2, c)) (fun γ c s => PIR A.toRO progI γ.1 c s)
    (fun _ s => s) (F0A A PI PS b₁ b₂) (ε := ε) fun γ => ?_
  · have hδ : pr ((NRR × (TRe × (TRe × TRe))) × ((Coins 16 × Tab3) × ShR R)) (fun z =>
        (issRealR A.toRO PI (z.1.1, (z.2.1.1, z.2.1.2))).out z.2.2 ≠
          (issRealR A.toRO PI (z.1.1, (z.2.1.1, z.2.1.2))).out z.2.2) = 0 := by
      rw [pr_congr (Q := fun _ => False) fun z => by simp, pr_const]
      simp
    rw [hδ, add_zero] at h
    rw [← pr_equiv eqv0R (gameRA A b₁ b₂ (issRealR A.toRO PI) (issRealR A.toRO PI)
        (spRealR A.toRO PS) (spRealR A.toRO PS)), ← pr_equiv eqv0R (gameRA A b₁ b₂
        (issSimR A.toRO simI progI) (issRealR A.toRO PI) (spRealR A.toRO PS) (spRealR A.toRO PS))]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · by_cases hT : A.toRO.tInit = 0
    · simp only [issRealR_out_zero hT, issSim_zero hT, PIR, hT, ↓reduceIte]
      exact (hop_ro_unused (ρ := Coins 16) (C := CI) (fun g u => F0A A PI PS b₁ b₂ γ
        (issOutOf A.toRO.base (.error .invalidArgument)) g u)).trans hε
    · simp only [issRealR_out_ne hT, issSim_ne hT, PIR, hT, ↓reduceIte]
      exact hIzk (xIOf A.toRO γ.1) ⟨vec γ.1.1, vec γ.1.2⟩ rfl
        (fun o g s => F0A A PI PS b₁ b₂ γ (ΦI A.toRO γ.1 o) g s)
        ⟨fun o s => rd3_viewRA0 hA hI b₁ b₂ _ _ _ _ _ _,
          fun o g => rd5_viewRA hA hI b₁ b₂ (fun _ => ΦI A.toRO γ.1 o) (issRealR A.toRO PI γ.2.1).out
            g γ.2.1.2.2 γ.2.2.1.2.2 γ.2.2.2.2.2 (spRealR A.toRO PS γ.2.2.1).out
            (spRealR A.toRO PS γ.2.2.2).out (Rd5.const _) (rd5_issRealR hPI5 _) (rd5_spRealR hPS5 _)
            (rd5_spRealR hPS5 _),
          fun o g => rdE_viewRA hA hI b₁ b₂ (fun _ => ΦI A.toRO γ.1 o) (issRealR A.toRO PI γ.2.1).out
            g γ.2.1.2.2 γ.2.2.1.2.2 γ.2.2.2.2.2 (spRealR A.toRO PS γ.2.2.1).out
            (spRealR A.toRO PS γ.2.2.2).out (RdE.const _) (rdE_issRealR hPIE _) (rdE_spRealR hPSE _)
            (rdE_spRealR hPSE _)⟩

variable (A simI PS) in
/-- The rest of the game around issuance `1`'s output: issuance `0` simulated. -/
def F1A (b₁ b₂ : Bool) (γ : TIsR CI × (NRR × (TRe × TRe))) (o : IssOut Z TokenS) (g : Tab3)
    (u : ShR R) : Prop :=
  viewRA A b₁ b₂ (noProgI A.toRO simI γ.1) (fakeI o g) (spRealR A.toRO PS γ.2.2.1)
    (spRealR A.toRO PS γ.2.2.2) u

theorem hopI1RA [Fintype CI] [Nonempty CI] (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) r5) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE)
    {ε : ℝ} (hε : 0 ≤ ε) (hIzk : ZeroKnowledgeRO IssueRel
      (fun x w (ρ : Coins 16) g s => PI x w (vec ρ) g s) simI progI
      (Budget pI (i3 + i3 + q3) (0 + (0 + (i5 + (r5 + (i5 + (r5 + q5))))) + m5)
        (0 + (0 + (iE + (rE + (iE + (rE + qE))))) + mE)) ε)
    (b₁ b₂ : Bool) :
    |pr _ (gameRA A b₁ b₂ (issSimR A.toRO simI progI) (issRealR A.toRO PI) (spRealR A.toRO PS)
        (spRealR A.toRO PS)) -
      pr _ (gameRA A b₁ b₂ (issSimR A.toRO simI progI) (issSimR A.toRO simI progI)
        (spRealR A.toRO PS) (spRealR A.toRO PS))| ≤ ε + deltaI1R A.toRO progI PI := by
  have h := hop_ro (Γ := TIsR CI × (NRR × (TRe × TRe))) (ρ := Coins 16) (G := Tab3) (C := CI)
    (S := ShR R) (fun γ ρ g s => (issRealR A.toRO PI (γ.2.1, (ρ, g))).out s)
    (fun γ c => issSim A.toRO.base simI (γ.2.1.1, γ.2.1.2, c))
    (fun γ c s => PIR A.toRO progI γ.2.1 c s)
    (fun γ s => PIR A.toRO progI γ.1.1 γ.1.2.1 s) (F1A A simI PS b₁ b₂) (ε := ε) fun γ => ?_
  · rw [← pr_equiv eqv1R (gameRA A b₁ b₂ (issSimR A.toRO simI progI) (issRealR A.toRO PI)
        (spRealR A.toRO PS) (spRealR A.toRO PS)), ← pr_equiv eqv1R (gameRA A b₁ b₂
        (issSimR A.toRO simI progI) (issSimR A.toRO simI progI) (spRealR A.toRO PS)
        (spRealR A.toRO PS))]
    exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
      (pr_congr fun z => Iff.rfl)) h
  · by_cases hT : A.toRO.tInit = 0
    · simp only [issRealR_out_zero hT, issSim_zero hT, PIR, hT, ↓reduceIte]
      exact (hop_ro_unused (ρ := Coins 16) (C := CI) (fun g u => F1A A simI PS b₁ b₂ γ
        (issOutOf A.toRO.base (.error .invalidArgument)) g u)).trans hε
    · have hL : IsProg (progI (xIOf A.toRO γ.1.1) γ.1.2.1) m5 mE := hpI _ _
      simp only [issRealR_out_ne hT, issSim_ne hT, PIR, hT, ↓reduceIte]
      exact hIzk (xIOf A.toRO γ.2.1) ⟨vec γ.2.1.1, vec γ.2.1.2⟩ rfl
        (fun o g s => F1A A simI PS b₁ b₂ γ (ΦI A.toRO γ.2.1 o) g
          (progI (xIOf A.toRO γ.1.1) γ.1.2.1 s))
        ⟨fun o s => rd3_viewRA1 hA hI b₁ b₂ _ _ _ _ _ _,
          fun o g => (rd5_viewRA hA hI b₁ b₂ (noProgI A.toRO simI γ.1).out (fun _ => ΦI A.toRO γ.2.1 o)
            γ.1.2.2 g γ.2.2.1.2.2 γ.2.2.2.2.2 (spRealR A.toRO PS γ.2.2.1).out
            (spRealR A.toRO PS γ.2.2.2).out (Rd5.const _) (Rd5.const _) (rd5_spRealR hPS5 _)
            (rd5_spRealR hPS5 _)).comp_prog hL,
          fun o g => (rdE_viewRA hA hI b₁ b₂ (noProgI A.toRO simI γ.1).out (fun _ => ΦI A.toRO γ.2.1 o)
            γ.1.2.2 g γ.2.2.1.2.2 γ.2.2.2.2.2 (spRealR A.toRO PS γ.2.2.1).out
            (spRealR A.toRO PS γ.2.2.2).out (RdE.const _) (RdE.const _) (rdE_spRealR hPSE _)
            (rdE_spRealR hPSE _)).comp_prog hL⟩

end HopsI

/-! ## Round 1's hop -/

/-- **When round 1 does not run, the guess sees nothing of the spends**, for slots that do not
program then. -/
lemma viewR_not_ok1 (B : AdversaryRO R Z) (b₁ b₂ : Bool) (s₀ s₁ : IssSlotR R Z) (h₁ h₂ : SpSlotR R Z)
    (t : ShR R) (hq₁ : ∀ τ d s, h₁.prog false τ d s = s) (hq₂ : ∀ τ d s, h₂.prog false τ d s = s)
    (h : ok₁ B.base (tokIface B.base) ((s₀.out (s₀.prog (s₁.prog t))).req,
        (s₁.out (s₀.prog (s₁.prog t))).req)
      ((s₀.out (s₀.prog (s₁.prog t))).fin (B.respondIss ((s₀.out (s₀.prog (s₁.prog t))).req,
        (s₁.out (s₀.prog (s₁.prog t))).req) false))
      ((s₁.out (s₀.prog (s₁.prog t))).fin (B.respondIss ((s₀.out (s₀.prog (s₁.prog t))).req,
        (s₁.out (s₀.prog (s₁.prog t))).req) true)) = false) :
    viewR B b₁ b₂ s₀ s₁ h₁ h₂ t ↔
      B.guess ((s₀.out (s₀.prog (s₁.prog t))).req, (s₁.out (s₀.prog (s₁.prog t))).req) none
        ((s₀.slice, s₁.slice), (h₁.slice, h₂.slice)) (s₀.prog (s₁.prog t)) := by
  simp only [viewR, h, Bool.false_and, Bool.cond_false, hq₁, hq₂]

section HopS1

variable {A} {CI CS : Type} {simI : IssueInstance → CI → Option (IssueProof Z)}
  {simS : SpendInstance → CS → Option (SpendProof Z)}
  {progI : IssueInstance → CI → ShR R → ShR R} {progS : SpendInstance → CS → ShR R → ShR R}
  {PS : ProverS R Z} {q3 q5 qE i3 i2 i5 iE r5 rE m5 mE : ℕ}

/-- The context of hop S1: the simulated issuances, round 1's coins `(nf, r)` and round 2's real
tape. -/
abbrev ΓS1 (CI : Type) := ((TIsR CI × TIsR CI) × NRR) × TRe

variable (A simI progI) in
/-- **The stage-1 messages in hop S1**, read off round 1's slice and the shared tables through the
issuance simulations' programming. -/
def Sx1 (γ : ΓS1 CI) (t : Tab3 × ShR R) : M₁ :=
  A.msg₁ ((i₀R A.toRO simI γ.1).req, (i₁R A.toRO simI γ.1).req)
    ((γ.1.1.1.2.2, γ.1.1.2.2.2), (t.1, γ.2.2.2)) (PI2R A.toRO progI γ.1 t.2)

variable (A) in
/-- The Issuer with its stage-1 messages fixed. -/
abbrev B1 (x : M₁) : AdversaryRO R Z := A.fixR (x, m2dflt)

variable (A) in
/-- A spend output where none is read. -/
def dummySp : SpOut Z TokenS := spOutOf A.toRO.base (.error .invalidArgument)

variable (A simI) in
/-- Round 1 runs, at the stage-1 messages `x`. -/
abbrev ok1A {α : Type} (γ : (TIsR CI × TIsR CI) × α) (x : M₁) : Bool := ok1R (B1 A x) simI γ

variable (A simI) in
/-- Round 1's token at the stage-1 messages `x`. -/
abbrev τ1A {α : Type} (b₁ : Bool) (γ : (TIsR CI × TIsR CI) × α) (x : M₁) : TokenS :=
  τ₁Of (B1 A x) b₁ (i₀R A.toRO simI γ) (i₁R A.toRO simI γ)

variable (A simI PS) in
/-- Round 1's real output. -/
def PS1 (b₁ : Bool) (γ : ΓS1 CI) (x : M₁) (ρ : Coins 16) (g : Tab3) (s : ShR R) : SpOut Z TokenS :=
  (spRealR A.toRO PS (γ.1.2, (ρ, g))).out (τ1A A simI b₁ γ.1 x) x.2 s

variable (A simI simS) in
/-- Round 1's simulated output. -/
def SmS1 (b₁ : Bool) (γ : ΓS1 CI) (x : M₁) (c : CS) : SpOut Z TokenS :=
  spSim A.toRO.base simS (γ.1.2.1, γ.1.2.2, c) (τ1A A simI b₁ γ.1 x) x.2

variable (A simI progS) in
/-- Round 1's programming, if it runs. -/
def progS1 (b₁ : Bool) (γ : ΓS1 CI) (x : M₁) (c : CS) (s : ShR R) : ShR R :=
  if ok1A A simI γ.1 x = true then progS (xSOf A.toRO γ.1.2 (τ1A A simI b₁ γ.1 x) x.2) c s else s

variable (A simI PS) in
/-- The rest of the game around round 1's output: the stage-1 messages fixed, the stage-2 messages
read on the tables `u` the game runs on after round 1. -/
def FS1A (b₁ b₂ : Bool) (γ : ΓS1 CI) (x : M₁) (o : SpOut Z TokenS) (g : Tab3) (u : ShR R) : Prop :=
  viewR (A.fixR (x, trans₂ A b₁ ((γ.1.1.1.2.2, γ.1.1.2.2.2), (g, γ.2.2.2)) x
      (noProgI A.toRO simI γ.1.1.1).out (fun t => t) (noProgI A.toRO simI γ.1.1.2).out (fun t => t)
      (fun _ _ _ => o) (fun _ _ _ t => t) u))
    b₁ b₂ (noProgI A.toRO simI γ.1.1.1) (noProgI A.toRO simI γ.1.1.2) (fakeS o g)
    (spRealR A.toRO PS γ.2) u

lemma FS1A_not_ok (b₁ b₂ : Bool) (γ : ΓS1 CI) (x : M₁) (hok : ok1A A simI γ.1 x = false)
    (o o' : SpOut Z TokenS) (g : Tab3) (u : ShR R) :
    FS1A A simI PS b₁ b₂ γ x o g u ↔ FS1A A simI PS b₁ b₂ γ x o' g u := by
  have key : ∀ o : SpOut Z TokenS, FS1A A simI PS b₁ b₂ γ x o g u ↔
      A.guess ((i₀R A.toRO simI γ.1).req, (i₁R A.toRO simI γ.1).req) none
        ((γ.1.1.1.2.2, γ.1.1.2.2.2), (g, γ.2.2.2)) u := by
    intro o
    have h := viewR_not_ok1 (A.fixR (x, trans₂ A b₁ ((γ.1.1.1.2.2, γ.1.1.2.2.2), (g, γ.2.2.2)) x
      (noProgI A.toRO simI γ.1.1.1).out (fun t => t) (noProgI A.toRO simI γ.1.1.2).out (fun t => t)
      (fun _ _ _ => o) (fun _ _ _ t => t) u)) b₁ b₂ (noProgI A.toRO simI γ.1.1.1)
      (noProgI A.toRO simI γ.1.1.2) (fakeS o g) (spRealR A.toRO PS γ.2) u (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) hok
    exact h
  rw [key, key]
variable (A simI progI PS) in
/-- **The collision term of hop S1**: round 1's real proof (of the statement read off the tables)
on the tables programmed by the issuance simulations differs from the one on the original tables. -/
noncomputable def deltaS1A [Fintype CI] (b₁ : Bool) : ℝ :=
  pr (ΓS1 CI × (Coins 16 × (Tab3 × ShR R))) fun z =>
    PS1 A simI PS b₁ z.1 (Sx1 A simI progI z.1 z.2.2) z.2.1 z.2.2.1 (PI2R A.toRO progI z.1.1 z.2.2.2) ≠
      PS1 A simI PS b₁ z.1 (Sx1 A simI progI z.1 z.2.2) z.2.1 z.2.2.1 z.2.2.2

variable (A simI) in
/-- The spend statement and witness of round 1 at the stage-1 messages `x`, if round 1 runs. -/
def stwS1 (b₁ : Bool) (γ : ΓS1 CI) (x : M₁) : Option (SpendInstance × SpendWitness) :=
  if ok1A A simI γ.1 x = true then
    some (xSOf A.toRO γ.1.2 (τ1A A simI b₁ γ.1 x) x.2, wSOf γ.1.2 (τ1A A simI b₁ γ.1 x)
      ((clientCheck (τ1A A simI b₁ γ.1 x).t (τ1A A simI b₁ γ.1 x).x x.2).getD 0))
  else none

/-- Where round 1 runs, its token passes the Client's checks. -/
lemma ok1A_valid {α : Type} (b₁ : Bool) (γ : (TIsR CI × TIsR CI) × α) (x : M₁)
    (hok : ok1A A simI γ x = true) :
    (τ1A A simI b₁ γ x).Valid A.toRO.pk A.toRO.ctx ∧
      ∃ t', clientCheck (τ1A A simI b₁ γ x).t (τ1A A simI b₁ γ x).x x.2 = some t' :=
  valid_of_ok (B := (B1 A x).base) (ok_of_ok₁ (B := (B1 A x).base) b₁ hok)

lemma stwS1_rel (b₁ : Bool) (γ : ΓS1 CI) :
    ∀ x i w, stwS1 A simI b₁ γ x = some (i, w) → SpendRel i w := by
  intro x i w h
  unfold stwS1 at h
  split_ifs at h with hok
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hv, t', hc⟩ := ok1A_valid b₁ γ.1 x hok
    rw [hc, Option.getD_some]
    exact spendRel_of A.toRO γ.1.2 hv hc

set_option maxHeartbeats 600000 in
theorem hopS1RA [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS] (hA : A.GBudget q3 q5 qE)
    (hI : A.IBudget i3 i2 i5 iE)
    (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) r5) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE)
    {AdmS : (X : Type) → (Tab3 × ShR R → X) → Prop}
    (hS : ∀ γ : ΓS1 CI, AdmS M₁ (Sx1 A simI progI γ))
    {ε : ℝ} (hR : ZeroKnowledgeROA SpendRel
      (fun x w (ρ : Coins 16) g s => PS x w (vec ρ) g s) simS progS AdmS
      (Budget pS (i3 + q3) (i5 + (0 + (0 + (0 + (r5 + q5)))) + (m5 + m5))
        (iE + (0 + (0 + (0 + (rE + qE)))) + (mE + mE))) ε)
    (b₁ b₂ : Bool) :
    |pr _ (gameRA A b₁ b₂ (issSimR A.toRO simI progI) (issSimR A.toRO simI progI)
        (spRealR A.toRO PS) (spRealR A.toRO PS)) -
      pr _ (gameRA A b₁ b₂ (issSimR A.toRO simI progI) (issSimR A.toRO simI progI)
        (spSimR A.toRO simS progS) (spRealR A.toRO PS))| ≤
      ε + deltaS1A A simI progI PS b₁ := by
  have h := hop_roA (Γ := ΓS1 CI) (ρ := Coins 16) (G := Tab3) (C := CS) (S := ShR R)
    (Sx1 A simI progI) (PS1 A simI PS b₁) (SmS1 A simI simS b₁) (progS1 A simI progS b₁)
    (fun γ _ s => PI2R A.toRO progI γ.1 s) (FS1A A simI PS b₁ b₂) (ε := ε) fun γ => ?_
  · -- From the hop to the games.
    let e : (((TIsR CI × TIsR CI) × ((NRR × (Coins 16 × Tab3)) × TRe)) × ShR R) ≃
        (ΓS1 CI × (Coins 16 × (Tab3 × ShR R))) :=
      { toFun := fun z => (((z.1.1, z.1.2.1.1), z.1.2.2), (z.1.2.1.2.1, (z.1.2.1.2.2, z.2)))
        invFun := fun z => ((z.1.1.1, ((z.1.1.2, (z.2.1, z.2.2.1)), z.1.2)), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let e' : (((TIsR CI × TIsR CI) × ((NRR × (CS × Tab3)) × TRe)) × ShR R) ≃
        (ΓS1 CI × (CS × (Tab3 × ShR R))) :=
      { toFun := fun z => (((z.1.1, z.1.2.1.1), z.1.2.2), (z.1.2.1.2.1, (z.1.2.1.2.2, z.2)))
        invFun := fun z => ((z.1.1.1, ((z.1.1.2, (z.2.1, z.2.2.1)), z.1.2)), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e1 : pr _ (gameRA A b₁ b₂ (issSimR A.toRO simI progI) (issSimR A.toRO simI progI)
        (spRealR A.toRO PS) (spRealR A.toRO PS)) =
        pr (ΓS1 CI × (Coins 16 × (Tab3 × ShR R))) (fun z =>
          FS1A A simI PS b₁ b₂ z.1 (Sx1 A simI progI z.1 z.2.2)
            (PS1 A simI PS b₁ z.1 (Sx1 A simI progI z.1 z.2.2) z.2.1 z.2.2.1
              (PI2R A.toRO progI z.1.1 z.2.2.2)) z.2.2.1 (PI2R A.toRO progI z.1.1 z.2.2.2)) := by
      rw [← pr_equiv e.symm]
      exact pr_congr fun z => Iff.rfl
    have e2 : pr _ (gameRA A b₁ b₂ (issSimR A.toRO simI progI) (issSimR A.toRO simI progI)
        (spSimR A.toRO simS progS) (spRealR A.toRO PS)) =
        pr (ΓS1 CI × (CS × (Tab3 × ShR R))) (fun z =>
          FS1A A simI PS b₁ b₂ z.1 (Sx1 A simI progI z.1 z.2.2)
            (SmS1 A simI simS b₁ z.1 (Sx1 A simI progI z.1 z.2.2) z.2.1) z.2.2.1
            (PI2R A.toRO progI z.1.1 (progS1 A simI progS b₁ z.1 (Sx1 A simI progI z.1 z.2.2) z.2.1
              z.2.2.2))) := by
      rw [← pr_equiv e'.symm]
      exact pr_congr fun z => Iff.rfl
    rw [e1, e2]
    exact h
  · -- The zero-knowledge step, from `ZeroKnowledgeROA`.
    have hL : IsProg (PI2R A.toRO progI γ.1) (m5 + m5) (mE + mE) :=
      (isProg_PIR hpI _ _).comp (isProg_PIR hpI _ _)
    have hz := hR M₁ (Sx1 A simI progI γ) (stwS1 A simI b₁ γ) (hS γ) (stwS1_rel b₁ γ) none
      (fun x o g s => FS1A A simI PS b₁ b₂ γ x (spOfProof A.toRO γ.1.2 (τ1A A simI b₁ γ.1 x) x.2
        ((clientCheck (τ1A A simI b₁ γ.1 x).t (τ1A A simI b₁ γ.1 x).x x.2).getD 0) o) g
        (PI2R A.toRO progI γ.1 s))
      fun x => ⟨fun o s => Rd3.bind
          (m := fun g => trans₂ A b₁ ((γ.1.1.1.2.2, γ.1.1.2.2.2), (g, γ.2.2.2)) x
            (noProgI A.toRO simI γ.1.1.1).out (fun t => t) (noProgI A.toRO simI γ.1.1.2).out
            (fun t => t) (fun _ _ _ => spOfProof A.toRO γ.1.2 (τ1A A simI b₁ γ.1 x) x.2
              ((clientCheck (τ1A A simI b₁ γ.1 x).t (τ1A A simI b₁ γ.1 x).x x.2).getD 0) o)
            (fun _ _ _ t => t) (PI2R A.toRO progI γ.1 s))
          (f := fun m₂ g => viewR (A.fixR (x, m₂)) b₁ b₂ (noProgI A.toRO simI γ.1.1.1)
            (noProgI A.toRO simI γ.1.1.2) (fakeS (spOfProof A.toRO γ.1.2 (τ1A A simI b₁ γ.1 x) x.2
              ((clientCheck (τ1A A simI b₁ γ.1 x).t (τ1A A simI b₁ γ.1 x).x x.2).getD 0) o) g)
            (spRealR A.toRO PS γ.2) (PI2R A.toRO progI γ.1 s))
          (rd3_trans₂ (σ := fun g => ((γ.1.1.1.2.2, γ.1.1.2.2.2), (g, γ.2.2.2)))
            (fun _ _ u => SReads.rd3 (hI.b2 _ _ _ _ _) u) _ _ _ _ _ _ _ _ _)
          fun m₂ => rd3_viewR2 (hA _) b₁ b₂ _ _ _ _ _ _,
        fun o g => (Rd5.bind
          (m := fun u => trans₂ A b₁ ((γ.1.1.1.2.2, γ.1.1.2.2.2), (g, γ.2.2.2)) x
            (noProgI A.toRO simI γ.1.1.1).out (fun t => t) (noProgI A.toRO simI γ.1.1.2).out
            (fun t => t) (fun _ _ _ => spOfProof A.toRO γ.1.2 (τ1A A simI b₁ γ.1 x) x.2
              ((clientCheck (τ1A A simI b₁ γ.1 x).t (τ1A A simI b₁ γ.1 x).x x.2).getD 0) o)
            (fun _ _ _ t => t) u)
          (f := fun m₂ u => viewR (A.fixR (x, m₂)) b₁ b₂ (noProgI A.toRO simI γ.1.1.1)
            (noProgI A.toRO simI γ.1.1.2) (fakeS (spOfProof A.toRO γ.1.2 (τ1A A simI b₁ γ.1 x) x.2
              ((clientCheck (τ1A A simI b₁ γ.1 x).t (τ1A A simI b₁ γ.1 x).x x.2).getD 0) o) g)
            (spRealR A.toRO PS γ.2) u)
          (SReads.rd5 (hI.b0 ((i₀R A.toRO simI γ.1).req, (i₁R A.toRO simI γ.1).req)
            (spOfProof A.toRO γ.1.2 (τ1A A simI b₁ γ.1 x) x.2
              ((clientCheck (τ1A A simI b₁ γ.1 x).t (τ1A A simI b₁ γ.1 x).x x.2).getD 0) o).req
            γ.1.1.2.2.2 g γ.2.2.2) γ.1.1.1.2.2) fun m₂ =>
            rd5_viewR (hA _) b₁ b₂ _ _ _ _ _ _ _ _ (Rd5.const _) (Rd5.const _)
              (fun _ _ => Rd5.const _) (rd5_spRealR hPS5 _)).comp_prog hL,
        fun o g => (RdE.bind
          (m := fun u => trans₂ A b₁ ((γ.1.1.1.2.2, γ.1.1.2.2.2), (g, γ.2.2.2)) x
            (noProgI A.toRO simI γ.1.1.1).out (fun t => t) (noProgI A.toRO simI γ.1.1.2).out
            (fun t => t) (fun _ _ _ => spOfProof A.toRO γ.1.2 (τ1A A simI b₁ γ.1 x) x.2
              ((clientCheck (τ1A A simI b₁ γ.1 x).t (τ1A A simI b₁ γ.1 x).x x.2).getD 0) o)
            (fun _ _ _ t => t) u)
          (f := fun m₂ u => viewR (A.fixR (x, m₂)) b₁ b₂ (noProgI A.toRO simI γ.1.1.1)
            (noProgI A.toRO simI γ.1.1.2) (fakeS (spOfProof A.toRO γ.1.2 (τ1A A simI b₁ γ.1 x) x.2
              ((clientCheck (τ1A A simI b₁ γ.1 x).t (τ1A A simI b₁ γ.1 x).x x.2).getD 0) o) g)
            (spRealR A.toRO PS γ.2) u)
          (SReads.rdE (hI.b0 ((i₀R A.toRO simI γ.1).req, (i₁R A.toRO simI γ.1).req)
            (spOfProof A.toRO γ.1.2 (τ1A A simI b₁ γ.1 x) x.2
              ((clientCheck (τ1A A simI b₁ γ.1 x).t (τ1A A simI b₁ γ.1 x).x x.2).getD 0) o).req
            γ.1.1.2.2.2 g γ.2.2.2) γ.1.1.1.2.2) fun m₂ =>
            rdE_viewR (hA _) b₁ b₂ _ _ _ _ _ _ _ _ (RdE.const _) (RdE.const _)
              (fun _ _ => RdE.const _) (rdE_spRealR hPSE _)).comp_prog hL⟩
    refine le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun a => ?_)
      (pr_congr fun a => ?_)) hz
    · unfold outReal stwS1
      split_ifs with hok
      · obtain ⟨hv, t', hc⟩ := ok1A_valid b₁ γ.1 (Sx1 A simI progI γ a.2) hok
        simp only [Option.elim, hc, Option.getD_some]
        unfold PS1
        rw [spRealR_out_ok _ hv hc]
      · exact FS1A_not_ok b₁ b₂ _ _ (Bool.of_not_eq_true hok) _ _ _ _
    · unfold outSim progSim stwS1 progS1
      split_ifs with hok
      · obtain ⟨hv, t', hc⟩ := ok1A_valid b₁ γ.1 (Sx1 A simI progI γ a.2) hok
        simp only [Option.elim, hc, Option.getD_some]
        unfold SmS1
        rw [spSim_ok _ _ hv hc]
      · exact FS1A_not_ok b₁ b₂ _ _ (Bool.of_not_eq_true hok) _ _ _ _

end HopS1

/-! ## Round 2's hop -/

section HopS2

variable {A} {CI CS : Type} {simI : IssueInstance → CI → Option (IssueProof Z)}
  {simS : SpendInstance → CS → Option (SpendProof Z)}
  {progI : IssueInstance → CI → ShR R → ShR R} {progS : SpendInstance → CS → ShR R → ShR R}
  {PS : ProverS R Z} {q3 q5 qE i3 i2 i5 iE r5 rE m5 mE : ℕ}

/-- The context of hop S2: the simulated issuances and round 1, round 2's coins `(nf, r)`. -/
abbrev ΓS2 (CI CS : Type) := ((TIsR CI × TIsR CI) × TSsR CS) × NRR

variable (A simI simS progI progS) in
/-- **The transcript in hop S2**, read off round 2's slice and the shared tables: stage 1 through
the issuance simulations' programming, stage 2 through theirs and round 1's. -/
def Sx2 (b₁ : Bool) (γ : ΓS2 CI CS) (t : Tab3 × ShR R) : MsgR :=
  transR A b₁ (issSimR A.toRO simI progI γ.1.1.1) (issSimR A.toRO simI progI γ.1.1.2)
    (spSimR A.toRO simS progS γ.1.2) (fakeS (dummySp A) t.1) t.2

variable (A simI simS PS) in
/-- Round 2's real output at the transcript `x`. -/
def PS2 (b₁ b₂ : Bool) (γ : ΓS2 CI CS) (x : MsgR) (ρ : Coins 16) (g : Tab3) (s : ShR R) :
    SpOut Z TokenS :=
  (spRealR A.toRO PS (γ.2, (ρ, g))).out (τ₂R (A.fixR x) simI simS b₁ b₂ γ)
    (d₂R (A.fixR x) simI simS b₁ γ) s

variable (A simI simS) in
/-- Round 2's simulated output. -/
def SmS2 (b₁ b₂ : Bool) (γ : ΓS2 CI CS) (x : MsgR) (c : CS) : SpOut Z TokenS :=
  spSim A.toRO.base simS (γ.2.1, γ.2.2, c) (τ₂R (A.fixR x) simI simS b₁ b₂ γ)
    (d₂R (A.fixR x) simI simS b₁ γ)

variable (A simI simS progS) in
/-- Round 2's programming, if both rounds run. -/
def progS2 (b₁ b₂ : Bool) (γ : ΓS2 CI CS) (x : MsgR) (c : CS) (s : ShR R) : ShR R :=
  if (ok1R (A.fixR x) simI γ.1 && ok2R (A.fixR x) simI simS b₁ γ) = true then
    progS (xSOf A.toRO γ.2 (τ₂R (A.fixR x) simI simS b₁ b₂ γ) (d₂R (A.fixR x) simI simS b₁ γ)) c s
  else s

lemma FS2R_not_ok (b₁ b₂ : Bool) (γ : ΓS2 CI CS) (x : MsgR)
    (hok : (ok1R (A.fixR x) simI γ.1 && ok2R (A.fixR x) simI simS b₁ γ) = false)
    (o o' : SpOut Z TokenS) (g : Tab3) (u : ShR R) :
    FS2R (A.fixR x) simI simS b₁ b₂ γ o g u ↔ FS2R (A.fixR x) simI simS b₁ b₂ γ o' g u := by
  rcases Bool.and_eq_false_iff.1 hok with h1 | h2
  · simp only [FS2R, viewR, fakeS, noProgI, noProgS, h1, Bool.cond_false]
  · simp only [ok2R, O₁R, τ₁Of] at h2
    simp only [FS2R, viewR, fakeS, noProgI, noProgS, h2, Bool.cond_false]

variable (A simI simS progI progS PS) in
/-- **The collision term of hop S2**: round 2's real proof (of the statement read off the tables)
on the tables programmed by the other three simulations differs from the one on the original
tables. -/
noncomputable def deltaS2A [Fintype CI] [Fintype CS] (b₁ b₂ : Bool) : ℝ :=
  pr (ΓS2 CI CS × (Coins 16 × (Tab3 × ShR R))) fun z =>
    PS2 A simI simS PS b₁ b₂ z.1 (Sx2 A simI simS progI progS b₁ z.1 z.2.2) z.2.1 z.2.2.1
        (LS2R (A.fixR (Sx2 A simI simS progI progS b₁ z.1 z.2.2)) simI progI progS b₁ z.1
          z.2.2.2) ≠
      PS2 A simI simS PS b₁ b₂ z.1 (Sx2 A simI simS progI progS b₁ z.1 z.2.2) z.2.1 z.2.2.1 z.2.2.2

variable (A simI simS) in
/-- The spend statement and witness of round 2 at the transcript `x`, if both rounds run. -/
def stwS2 (b₁ b₂ : Bool) (γ : ΓS2 CI CS) (x : MsgR) : Option (SpendInstance × SpendWitness) :=
  if (ok1R (A.fixR x) simI γ.1 && ok2R (A.fixR x) simI simS b₁ γ) = true then
    some (xSOf A.toRO γ.2 (τ₂R (A.fixR x) simI simS b₁ b₂ γ) (d₂R (A.fixR x) simI simS b₁ γ),
      wSOf γ.2 (τ₂R (A.fixR x) simI simS b₁ b₂ γ)
        ((clientCheck (τ₂R (A.fixR x) simI simS b₁ b₂ γ).t (τ₂R (A.fixR x) simI simS b₁ b₂ γ).x
          (d₂R (A.fixR x) simI simS b₁ γ)).getD 0))
  else none

/-- Where both rounds run, round 2's token passes the Client's checks. -/
lemma ok2A_valid (b₁ b₂ : Bool) (γ : ΓS2 CI CS) (x : MsgR)
    (hok : (ok1R (A.fixR x) simI γ.1 && ok2R (A.fixR x) simI simS b₁ γ) = true) :
    (τ₂R (A.fixR x) simI simS b₁ b₂ γ).Valid A.toRO.pk A.toRO.ctx ∧
      ∃ t', clientCheck (τ₂R (A.fixR x) simI simS b₁ b₂ γ).t (τ₂R (A.fixR x) simI simS b₁ b₂ γ).x
        (d₂R (A.fixR x) simI simS b₁ γ) = some t' :=
  valid_of_ok (B := (A.fixR x).base)
    (ok_of_ok₂ (B := (A.fixR x).base) b₁ b₂ (Bool.and_eq_true_iff.1 hok).2)

lemma stwS2_rel (b₁ b₂ : Bool) (γ : ΓS2 CI CS) :
    ∀ x i w, stwS2 A simI simS b₁ b₂ γ x = some (i, w) → SpendRel i w := by
  intro x i w h
  unfold stwS2 at h
  split_ifs at h with hok
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hv, t', hc⟩ := ok2A_valid b₁ b₂ γ x hok
    rw [hc, Option.getD_some]
    exact spendRel_of A.toRO γ.2 hv hc

set_option maxHeartbeats 600000 in
theorem hopS2RA [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS] (hA : A.GBudget q3 q5 qE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpS : ∀ x c, IsProg (progS x c) m5 mE) (b₁ : Bool)
    {AdmS : (X : Type) → (Tab3 × ShR R → X) → Prop}
    (hS : ∀ γ : ΓS2 CI CS, AdmS MsgR (Sx2 A simI simS progI progS b₁ γ))
    {ε : ℝ} (hR : ZeroKnowledgeROA SpendRel
      (fun x w (ρ : Coins 16) g s => PS x w (vec ρ) g s) simS progS AdmS
      (Budget pS q3 (0 + (0 + (0 + (0 + q5))) + (m5 + (m5 + m5)))
        (0 + (0 + (0 + (0 + qE))) + (mE + (mE + mE)))) ε)
    (b₂ : Bool) :
    |pr _ (gameRA A b₁ b₂ (issSimR A.toRO simI progI) (issSimR A.toRO simI progI)
        (spSimR A.toRO simS progS) (spRealR A.toRO PS)) -
      pr _ (gameRA A b₁ b₂ (issSimR A.toRO simI progI) (issSimR A.toRO simI progI)
        (spSimR A.toRO simS progS) (spSimR A.toRO simS progS))| ≤
      ε + deltaS2A A simI simS progI progS PS b₁ b₂ := by
  have h := hop_roA (Γ := ΓS2 CI CS) (ρ := Coins 16) (G := Tab3) (C := CS) (S := ShR R)
    (Sx2 A simI simS progI progS b₁) (PS2 A simI simS PS b₁ b₂) (SmS2 A simI simS b₁ b₂)
    (progS2 A simI simS progS b₁ b₂) (fun γ x s => LS2R (A.fixR x) simI progI progS b₁ γ s)
    (fun γ x => FS2R (A.fixR x) simI simS b₁ b₂ γ) (ε := ε) fun γ => ?_
  · -- From the hop to the games.
    let e : (((TIsR CI × TIsR CI) × (TSsR CS × (NRR × (Coins 16 × Tab3)))) × ShR R) ≃
        (ΓS2 CI CS × (Coins 16 × (Tab3 × ShR R))) :=
      { toFun := fun z => (((z.1.1, z.1.2.1), z.1.2.2.1), (z.1.2.2.2.1, (z.1.2.2.2.2, z.2)))
        invFun := fun z => ((z.1.1.1, (z.1.1.2, (z.1.2, (z.2.1, z.2.2.1)))), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let e' : (((TIsR CI × TIsR CI) × (TSsR CS × (NRR × (CS × Tab3)))) × ShR R) ≃
        (ΓS2 CI CS × (CS × (Tab3 × ShR R))) :=
      { toFun := fun z => (((z.1.1, z.1.2.1), z.1.2.2.1), (z.1.2.2.2.1, (z.1.2.2.2.2, z.2)))
        invFun := fun z => ((z.1.1.1, (z.1.1.2, (z.1.2, (z.2.1, z.2.2.1)))), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e1 : pr _ (gameRA A b₁ b₂ (issSimR A.toRO simI progI) (issSimR A.toRO simI progI)
        (spSimR A.toRO simS progS) (spRealR A.toRO PS)) =
        pr (ΓS2 CI CS × (Coins 16 × (Tab3 × ShR R))) (fun z =>
          FS2R (A.fixR (Sx2 A simI simS progI progS b₁ z.1 z.2.2)) simI simS b₁ b₂ z.1
            (PS2 A simI simS PS b₁ b₂ z.1 (Sx2 A simI simS progI progS b₁ z.1 z.2.2) z.2.1 z.2.2.1
              (LS2R (A.fixR (Sx2 A simI simS progI progS b₁ z.1 z.2.2)) simI progI progS b₁ z.1
                z.2.2.2)) z.2.2.1
            (LS2R (A.fixR (Sx2 A simI simS progI progS b₁ z.1 z.2.2)) simI progI progS b₁ z.1
              z.2.2.2)) := by
      rw [← pr_equiv e.symm]
      exact pr_congr fun z => Iff.rfl
    have e2 : pr _ (gameRA A b₁ b₂ (issSimR A.toRO simI progI) (issSimR A.toRO simI progI)
        (spSimR A.toRO simS progS) (spSimR A.toRO simS progS)) =
        pr (ΓS2 CI CS × (CS × (Tab3 × ShR R))) (fun z =>
          FS2R (A.fixR (Sx2 A simI simS progI progS b₁ z.1 z.2.2)) simI simS b₁ b₂ z.1
            (SmS2 A simI simS b₁ b₂ z.1 (Sx2 A simI simS progI progS b₁ z.1 z.2.2) z.2.1) z.2.2.1
            (LS2R (A.fixR (Sx2 A simI simS progI progS b₁ z.1 z.2.2)) simI progI progS b₁ z.1
              (progS2 A simI simS progS b₁ b₂ z.1 (Sx2 A simI simS progI progS b₁ z.1 z.2.2) z.2.1
                z.2.2.2))) := by
      rw [← pr_equiv e'.symm]
      exact pr_congr fun z => Iff.rfl
    rw [e1, e2]
    exact h
  · -- The zero-knowledge step, from `ZeroKnowledgeROA`.
    have hz := hR MsgR (Sx2 A simI simS progI progS b₁ γ) (stwS2 A simI simS b₁ b₂ γ) (hS γ)
      (stwS2_rel b₁ b₂ γ) none
      (fun x o g s => FS2R (A.fixR x) simI simS b₁ b₂ γ
        (spOfProof A.toRO γ.2 (τ₂R (A.fixR x) simI simS b₁ b₂ γ) (d₂R (A.fixR x) simI simS b₁ γ)
          ((clientCheck (τ₂R (A.fixR x) simI simS b₁ b₂ γ).t (τ₂R (A.fixR x) simI simS b₁ b₂ γ).x
            (d₂R (A.fixR x) simI simS b₁ γ)).getD 0) o) g
        (LS2R (A.fixR x) simI progI progS b₁ γ s))
      fun x => by
        have hL : IsProg (LS2R (A.fixR x) simI progI progS b₁ γ) (m5 + (m5 + m5))
            (mE + (mE + mE)) :=
          (isProg_PIR hpI _ _).comp ((isProg_PIR hpI _ _).comp (IsProg.ite _ (hpS _ _)
            (IsProg.id.mono (Nat.zero_le _) (Nat.zero_le _))))
        exact ⟨fun o s => rd3_viewR3 (hA x) b₁ b₂ _ _ _ _ _ _,
          fun o g => (rd5_viewR (hA x) b₁ b₂ (noProgI (A.fixR x) simI γ.1.1.1).out
            (noProgI (A.fixR x) simI γ.1.1.2).out γ.1.1.1.2.2 γ.1.1.2.2.2 γ.1.2.2.2 g
            (noProgS (A.fixR x) simS γ.1.2).out _ (Rd5.const _) (Rd5.const _)
            (fun _ _ => Rd5.const _) (fun _ _ => Rd5.const _)).comp_prog hL,
          fun o g => (rdE_viewR (hA x) b₁ b₂ (noProgI (A.fixR x) simI γ.1.1.1).out
            (noProgI (A.fixR x) simI γ.1.1.2).out γ.1.1.1.2.2 γ.1.1.2.2.2 γ.1.2.2.2 g
            (noProgS (A.fixR x) simS γ.1.2).out _ (RdE.const _) (RdE.const _)
            (fun _ _ => RdE.const _) (fun _ _ => RdE.const _)).comp_prog hL⟩
    refine le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun a => ?_)
      (pr_congr fun a => ?_)) hz
    · unfold outReal stwS2
      split_ifs with hok
      · obtain ⟨hv, t', hc⟩ := ok2A_valid b₁ b₂ γ (Sx2 A simI simS progI progS b₁ γ a.2) hok
        simp only [Option.elim, hc, Option.getD_some]
        unfold PS2
        rw [spRealR_out_ok _ hv hc]
      · exact FS2R_not_ok b₁ b₂ _ _ (Bool.of_not_eq_true hok) _ _ _ _
    · unfold outSim progSim stwS2 progS2
      split_ifs with hok
      · obtain ⟨hv, t', hc⟩ := ok2A_valid b₁ b₂ γ (Sx2 A simI simS progI progS b₁ γ a.2) hok
        simp only [Option.elim, hc, Option.getD_some]
        unfold SmS2
        rw [spSim_ok _ _ hv hc]
      · exact FS2R_not_ok b₁ b₂ _ _ (Bool.of_not_eq_true hok) _ _ _ _

end HopS2

/-! ## The simulated world as `Ratatouille.view` for an Issuer at fixed coins and tables -/

/-- **Two Issuers that agree on what the game asks them give the same view**: the same responses
and amount at the issuance transcript, the same stage-2 messages at round 1's request if round 1
runs, and the same guess. -/
theorem view_congr {B B' : Adversary Z} {Tok : Type} (I : Iface Tok) (b₁ b₂ : Bool)
    (i₀ i₁ : IssOut Z Tok) (s₁ s₂ : Tok → Credits → SpOut Z Tok)
    (hr : ∀ c, B.respondIss (i₀.req, i₁.req) c = B'.respondIss (i₀.req, i₁.req) c)
    (hd : B.d₁ (i₀.req, i₁.req) = B'.d₁ (i₀.req, i₁.req))
    (h2 : ok₁ B' I (i₀.req, i₁.req) (i₀.fin (B'.respondIss (i₀.req, i₁.req) false))
        (i₁.fin (B'.respondIss (i₀.req, i₁.req) true)) = true →
      B.respond₁ (i₀.req, i₁.req) (s₁ (tokD I (i₀.fin (B'.respondIss (i₀.req, i₁.req) false))
          (i₁.fin (B'.respondIss (i₀.req, i₁.req) true)) b₁) (B'.d₁ (i₀.req, i₁.req))).req =
        B'.respond₁ (i₀.req, i₁.req) (s₁ (tokD I (i₀.fin (B'.respondIss (i₀.req, i₁.req) false))
          (i₁.fin (B'.respondIss (i₀.req, i₁.req) true)) b₁) (B'.d₁ (i₀.req, i₁.req))).req ∧
      B.d₂ (i₀.req, i₁.req) (s₁ (tokD I (i₀.fin (B'.respondIss (i₀.req, i₁.req) false))
          (i₁.fin (B'.respondIss (i₀.req, i₁.req) true)) b₁) (B'.d₁ (i₀.req, i₁.req))).req =
        B'.d₂ (i₀.req, i₁.req) (s₁ (tokD I (i₀.fin (B'.respondIss (i₀.req, i₁.req) false))
          (i₁.fin (B'.respondIss (i₀.req, i₁.req) true)) b₁) (B'.d₁ (i₀.req, i₁.req))).req)
    (hg : ∀ y, B.guess (i₀.req, i₁.req) y ↔ B'.guess (i₀.req, i₁.req) y) :
    view B I b₁ b₂ i₀ i₁ s₁ s₂ ↔ view B' I b₁ b₂ i₀ i₁ s₁ s₂ := by
  unfold view stage₁ stage₂ stage₃
  rw [hr false, hr true, hd]
  have e1 : ∀ tk₀ tk₁, ok₁ B I (i₀.req, i₁.req) tk₀ tk₁ = ok₁ B' I (i₀.req, i₁.req) tk₀ tk₁ := by
    intro tk₀ tk₁
    unfold ok₁
    rw [hd]
  rw [e1]
  cases h : ok₁ B' I (i₀.req, i₁.req) (i₀.fin (B'.respondIss (i₀.req, i₁.req) false))
      (i₁.fin (B'.respondIss (i₀.req, i₁.req) true))
  · simp only [Bool.cond_false]
    exact hg none
  · obtain ⟨e2, e3⟩ := h2 h
    rw [e2, e3]
    simp only [ok₂, e3]
    exact hg _

section Ideal

variable {CI CS : Type} (simI : IssueInstance → CI → Option (IssueProof Z))
  (simS : SpendInstance → CS → Option (SpendProof Z))
  (progI : IssueInstance → CI → ShR R → ShR R) (progS : SpendInstance → CS → ShR R → ShR R)

/-- **The tables after the issuance simulations**, as a function of the requests the Issuer sees
(`progIm`: a simulation's programming from its request). -/
def U₁ (co : (CI × CI) × (CS × CS)) (t : ShR R) (tr : IssTr Z) : ShR R :=
  progIm A.toRO progI co.1.1 tr.1 (progIm A.toRO progI co.1.2 tr.2 t)

/-- **The tables after the issuance simulations and round 1's**, as a function of the requests. -/
def U₂ (co : (CI × CI) × (CS × CS)) (t : ShR R) (tr : IssTr Z) (rq : Except Error (SpendRequest Z)) :
    ShR R :=
  progIm A.toRO progI co.1.1 tr.1 (progIm A.toRO progI co.1.2 tr.2 (progSm A.toRO progS co.2.1 rq t))

/-- **The Issuer at fixed simulator coins, slices and tables**, as an `Adversary`: its messages
read the tables as the simulations before them programmed them, as functions of the requests it
has seen; its guess reads `Vtab`. -/
def atRA (co : (CI × CI) × (CS × CS)) (t : ShR R) (sl : SlicesR) : Adversary Z :=
  ⟨A.pk, A.ctx, A.tInit, fun tr c => A.respondIss tr c sl (U₁ A progI co t tr),
    fun tr => A.d₁ tr sl (U₁ A progI co t tr),
    fun tr rq => A.respond₁ tr rq sl (U₂ A progI progS co t tr rq),
    fun tr rq => A.d₂ tr rq sl (U₂ A progI progS co t tr rq),
    fun tr y => A.guess tr y sl (Vtab A.toRO progI progS co t tr y)⟩

variable {A simI progI} in
/-- **The issuance simulations' programming is the one of their requests.** -/
lemma issProg_eq (hprogI : ∀ x x' c, simI x c = none → progI x c = progI x' c) (y₀ y₁ : TIsR CI)
    (s : ShR R) :
    (if A.toRO.tInit = 0 then (if A.toRO.tInit = 0 then s else progI (xIOf A.toRO y₁.1) y₁.2.1 s)
      else progI (xIOf A.toRO y₀.1) y₀.2.1
        (if A.toRO.tInit = 0 then s else progI (xIOf A.toRO y₁.1) y₁.2.1 s)) =
      progIm A.toRO progI y₀.2.1 (issSim A.toRO.base simI (y₀.1.1, y₀.1.2, y₀.2.1)).req
        (progIm A.toRO progI y₁.2.1 (issSim A.toRO.base simI (y₁.1.1, y₁.1.2, y₁.2.1)).req s) := by
  rw [issSim_prog hprogI y₁.1 y₁.2.1 s, issSim_prog hprogI y₀.1 y₀.2.1]

/-- The game with all four proofs simulated. -/
def simGameRA (b₁ b₂ : Bool) : ((TIsR CI × TIsR CI) × (TSsR CS × TSsR CS)) × ShR R → Prop :=
  gameRA A b₁ b₂ (issSimR A.toRO simI progI) (issSimR A.toRO simI progI)
    (spSimR A.toRO simS progS) (spSimR A.toRO simS progS)

theorem simGameRA_iff (hprogI : ∀ x x' c, simI x c = none → progI x c = progI x' c)
    (hprogS : ∀ x x' c, simS x c = none → progS x c = progS x' c) (b₁ b₂ : Bool)
    (x : ((TIsR CI × TIsR CI) × (TSsR CS × TSsR CS)) × ShR R) :
    simGameRA A simI simS progI progS b₁ b₂ x ↔
      simGame (atRA A progI progS (coinsOfR x) x.2 (slicesOfR x)) simI simS b₁ b₂ (tapeOfR x) := by
  have h1 := simGameR_iff (A.fixR (transR A b₁ (issSimR A.toRO simI progI x.1.1.1)
    (issSimR A.toRO simI progI x.1.1.2) (spSimR A.toRO simS progS x.1.2.1)
    (spSimR A.toRO simS progS x.1.2.2) x.2)) simI simS progI progS hprogI hprogS b₁ b₂ x
  refine h1.trans ?_
  refine view_congr (tokIface A.toRO.base) b₁ b₂
    (issSim A.toRO.base simI (x.1.1.1.1.1, x.1.1.1.1.2, x.1.1.1.2.1))
    (issSim A.toRO.base simI (x.1.1.2.1.1, x.1.1.2.1.2, x.1.1.2.2.1))
    (spSim A.toRO.base simS (x.1.2.1.1.1, x.1.2.1.1.2, x.1.2.1.2.1))
    (spSim A.toRO.base simS (x.1.2.2.1.1, x.1.2.2.1.2, x.1.2.2.2.1)) ?_ ?_ ?_ fun _ => Iff.rfl
  · intro c
    simp only [AdversaryRO.at, AdversaryRA.fixR, atRA, transR, transS, AdversaryRA.msg₁, issSimR]
    rw [issProg_eq hprogI]
    cases c <;> rfl
  · simp only [AdversaryRO.at, AdversaryRA.fixR, atRA, transR, transS, AdversaryRA.msg₁, issSimR]
    rw [issProg_eq hprogI]
    rfl
  · intro h
    simp only [AdversaryRO.at, AdversaryRA.fixR, atRA, transR, transS, trans₂, AdversaryRA.msg₁,
      AdversaryRA.msg₂, issSimR, spSimR]
    rw [issProg_eq hprogI, issProg_eq hprogI]
    split_ifs with hc
    · rw [spSim_prog (A := A.toRO) hprogS x.1.2.1.1 x.1.2.1.2.1 _ _ ?_]
      · exact ⟨rfl, rfl⟩
      · exact ok_of_ok₁ (B := atRA A progI progS (coinsOfR x) x.2 (slicesOfR x)) b₁ h
    · exact absurd h hc


/-- **The reduction to hiding**: `Ratatouille.reduction` for the Issuer at the simulator coins
`K.1`, the slices `K.2.1` and the tables `K.2.2`. -/
def reductionRA (b₁ b₂ : Bool) (K : KR R CI CS) :
    Quad Nullifier → Quad (Credits → Commitment) → Prop :=
  reduction (atRA A progI progS K.1 K.2.2 K.2.1) simI simS b₁ b₂ K.1

/-- The ideal world: uniform commitments. -/
def idealGameRA (b₁ b₂ : Bool) (y : UTape × KR R CI CS) : Prop :=
  reductionRA A simI simS progI progS b₁ b₂ y.2 (hideIdeal y.1).1 (hideIdeal y.1).2

theorem hiding_hopRA [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS]
    (hprogI : ∀ x x' c, simI x c = none → progI x c = progI x' c)
    (hprogS : ∀ x x' c, simS x c = none → progS x c = progS x' c) (b₁ b₂ : Bool) {εhide : ℝ}
    (hhide : ∀ K, hidingAdv A.ctx (reductionRA A simI simS progI progS b₁ b₂ K) ≤ εhide) :
    |pr _ (simGameRA A simI simS progI progS b₁ b₂) -
      pr _ (idealGameRA A simI simS progI progS b₁ b₂)| ≤ εhide := by
  rw [← pr_equiv regroupR.symm (simGameRA A simI simS progI progS b₁ b₂),
    pr_congr fun y => (simGameRA_iff A simI simS progI progS hprogI hprogS b₁ b₂
      (regroupR.symm y)).trans (simGame_iff _ simI simS b₁ b₂ _)]
  exact abs_pr_prod_sub_le' _ _ fun K => hhide K

/-- **In the ideal world the four worlds coincide**, for every simulator coins, slices and
tables (`Ratatouille.idealGame_eq`, with the coins and the tables fixed). -/
theorem idealGameRA_eq [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS] (b₁ b₂ : Bool) :
    pr _ (idealGameRA A simI simS progI progS b₁ b₂) =
      pr _ (idealGameRA A simI simS progI progS false false) := by
  have key : ∀ K : KR R CI CS, pr UTape (fun u => idealGameRA A simI simS progI progS b₁ b₂ (u, K)) =
      pr UTape (fun u => idealGameRA A simI simS progI progS false false (u, K)) := by
    intro K
    set A' := atRA A progI progS K.1 K.2.2 K.2.1
    have e (c₁ c₂ : Bool) (u : UTape) : idealGameRA A simI simS progI progS c₁ c₂ (u, K) ↔
        idealW A' simI simS (bif c₁ then vec u.1.2.1 else vec u.1.1.1)
          (bif c₂ == c₁ then vec u.2.1.1 else bif c₁ then vec u.1.1.1 else vec u.1.2.1)
          (vec u.1.1.2) (vec u.1.2.2) (vec u.2.1.2) (vec u.2.2.2) K.1 :=
      idealGame_iff A' simI simS c₁ c₂ (u, K.1)
    rw [pr_congr (e b₁ b₂), pr_congr (e false false)]
    cases b₁ <;> cases b₂ <;>
      simp only [Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.not_false, Bool.cond_true,
        Bool.cond_false]
    · rw [← pr_equiv (permU (⟨fun z => (z.1, z.2.2, z.2.1), fun z => (z.1, z.2.2, z.2.1),
        fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
        (fun u => idealW A' simI simS (vec u.1.1.1) (vec u.2.1.1) (vec u.1.1.2) (vec u.1.2.2)
          (vec u.2.1.2) (vec u.2.2.2) K.1)]
      exact pr_congr fun _ => Iff.rfl
    · rw [← pr_equiv (permU (⟨fun z => (z.2.1, z.2.2, z.1), fun z => (z.2.2, z.1, z.2.1),
        fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
        (fun u => idealW A' simI simS (vec u.1.1.1) (vec u.2.1.1) (vec u.1.1.2) (vec u.1.2.2)
          (vec u.2.1.2) (vec u.2.2.2) K.1)]
      exact pr_congr fun _ => Iff.rfl
    · rw [← pr_equiv (permU (⟨fun z => (z.2.1, z.1, z.2.2), fun z => (z.2.1, z.1, z.2.2),
        fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
        (fun u => idealW A' simI simS (vec u.1.1.1) (vec u.2.1.1) (vec u.1.1.2) (vec u.1.2.2)
          (vec u.2.1.2) (vec u.2.2.2) K.1)]
      exact pr_congr fun _ => Iff.rfl
  have h := abs_pr_prod_sub_le' (fun y : UTape × KR R CI CS => idealGameRA A simI simS progI progS b₁ b₂ y)
    (fun y : UTape × KR R CI CS => idealGameRA A simI simS progI progS false false y) (ε := 0)
    fun K => by rw [key K, sub_self, abs_zero]
  rw [abs_nonpos_iff, sub_eq_zero] at h
  exact h

end Ideal

/-! ## Unlinkability with a table-reading interaction -/

variable {A} {CI CS : Type} {simI : IssueInstance → CI → Option (IssueProof Z)}
  {simS : SpendInstance → CS → Option (SpendProof Z)}
  {progI : IssueInstance → CI → ShR R → ShR R} {progS : SpendInstance → CS → ShR R → ShR R}
  {PI : ProverI R Z} {PS : ProverS R Z} in
/-- **Theorem 2 in the random-oracle and ideal-cipher model, the Issuer's interaction reading the
tables, for any proof systems.** The guess has the budget `(q₃, q₅, q_E)` (`GBudget`), each stage of
the interaction `(i₃, i₂, i₅, i_E)` (`IBudget`). If the issuance proofs are `ZeroKnowledgeRO`, the
spend proofs `ZeroKnowledgeROA` for the readers `AdmS₁`, `AdmS₂` (which contain the transcripts of
hops S1 and S2), the provers read `H₅`, the cipher at `r₅`, `r_E` keys and the programmings at
`m₅`, `m_E` keys, a simulation that produces no proof programs independently of its instance, and
the hiding reductions have advantage `≤ εhide`, then any two worlds differ by at most the
zero-knowledge errors at the reductions' budgets, the collision terms of both worlds and
`2εhide`. -/
theorem unlinkabilityRA [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS]
    {q3 q5 qE i3 i2 i5 iE r5 rE m5 mE : ℕ} {εI εS₁ εS₂ : ℕ → ℕ → ℕ → ℝ} {εhide : ℝ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPI5 : ∀ x w ρ g, Rd5 (PI x w ρ g) r5) (hPIE : ∀ x w ρ g, RdE (PI x w ρ g) rE)
    (hPS5 : ∀ x w ρ g, Rd5 (PS x w ρ g) r5) (hPSE : ∀ x w ρ g, RdE (PS x w ρ g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpS : ∀ x c, IsProg (progS x c) m5 mE)
    (hprogI : ∀ x x' c, simI x c = none → progI x c = progI x' c)
    (hprogS : ∀ x x' c, simS x c = none → progS x c = progS x' c)
    {AdmS₁ AdmS₂ : (X : Type) → (Tab3 × ShR R → X) → Prop}
    (hS1 : ∀ γ : ΓS1 CI, AdmS₁ M₁ (Sx1 A simI progI γ))
    (hS2 : ∀ b₁ (γ : ΓS2 CI CS), AdmS₂ MsgR (Sx2 A simI simS progI progS b₁ γ))
    (hIzk : ∀ a b c, ZeroKnowledgeRO IssueRel (fun x w (ρ : Coins 16) g s => PI x w (vec ρ) g s)
      simI progI (Budget pI a b c) (εI a b c))
    (hSzk₁ : ∀ a b c, ZeroKnowledgeROA SpendRel (fun x w (ρ : Coins 16) g s => PS x w (vec ρ) g s)
      simS progS AdmS₁ (Budget pS a b c) (εS₁ a b c))
    (hSzk₂ : ∀ a b c, ZeroKnowledgeROA SpendRel (fun x w (ρ : Coins 16) g s => PS x w (vec ρ) g s)
      simS progS AdmS₂ (Budget pS a b c) (εS₂ a b c))
    (hεI : ∀ a b c, 0 ≤ εI a b c)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx (reductionRA A simI simS progI progS b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRA A PI PS b₁ b₂) - pr _ (realGameRA A PI PS b₁' b₂')| ≤
      2 * (εI (i3 + i3 + q3) (0 + (r5 + (i5 + (r5 + (i5 + (r5 + q5))))))
            (0 + (rE + (iE + (rE + (iE + (rE + qE)))))) +
          εI (i3 + i3 + q3) (0 + (0 + (i5 + (r5 + (i5 + (r5 + q5))))) + m5)
            (0 + (0 + (iE + (rE + (iE + (rE + qE))))) + mE) +
          εS₁ (i3 + q3) (i5 + (0 + (0 + (0 + (r5 + q5)))) + (m5 + m5))
            (iE + (0 + (0 + (0 + (rE + qE)))) + (mE + mE)) +
          εS₂ q3 (0 + (0 + (0 + (0 + q5))) + (m5 + (m5 + m5)))
            (0 + (0 + (0 + (0 + qE))) + (mE + (mE + mE)))) +
        2 * deltaI1R A.toRO progI PI +
        (deltaS1A A simI progI PS b₁ + deltaS1A A simI progI PS b₁') +
        (deltaS2A A simI simS progI progS PS b₁ b₂ + deltaS2A A simI simS progI progS PS b₁' b₂') +
        2 * εhide := by
  have hw (c₁ c₂ : Bool) : |pr _ (realGameRA A PI PS c₁ c₂) -
      pr _ (idealGameRA A simI simS progI progS c₁ c₂)| ≤
      εI (i3 + i3 + q3) (0 + (r5 + (i5 + (r5 + (i5 + (r5 + q5))))))
          (0 + (rE + (iE + (rE + (iE + (rE + qE)))))) +
        (εI (i3 + i3 + q3) (0 + (0 + (i5 + (r5 + (i5 + (r5 + q5))))) + m5)
            (0 + (0 + (iE + (rE + (iE + (rE + qE))))) + mE) + deltaI1R A.toRO progI PI) +
        (εS₁ (i3 + q3) (i5 + (0 + (0 + (0 + (r5 + q5)))) + (m5 + m5))
            (iE + (0 + (0 + (0 + (rE + qE)))) + (mE + mE)) + deltaS1A A simI progI PS c₁) +
        (εS₂ q3 (0 + (0 + (0 + (0 + q5))) + (m5 + (m5 + m5)))
            (0 + (0 + (0 + (0 + qE))) + (mE + (mE + mE))) +
          deltaS2A A simI simS progI progS PS c₁ c₂) + εhide := by
    have h1 := hopI0RA (A := A) (PI := PI) (PS := PS) (simI := simI) (progI := progI) hA hI hPI5
      hPIE hPS5 hPSE (hεI _ _ _) (hIzk _ _ _) c₁ c₂
    have h2 := hopI1RA (A := A) (PI := PI) (PS := PS) (simI := simI) (progI := progI) hA hI hPS5
      hPSE hpI (hεI _ _ _) (hIzk _ _ _) c₁ c₂
    have h3 := hopS1RA (A := A) (PS := PS) (simI := simI) (simS := simS) (progI := progI)
      (progS := progS) hA hI hPS5 hPSE hpI hS1 (hSzk₁ _ _ _) c₁ c₂
    have h4 := hopS2RA (A := A) (PS := PS) (simI := simI) (simS := simS) (progI := progI)
      (progS := progS) hA hpI hpS c₁ (hS2 c₁) (hSzk₂ _ _ _) c₂
    have h5 := hiding_hopRA A simI simS progI progS hprogI hprogS c₁ c₂ (hhide c₁ c₂)
    unfold realGameRA
    unfold simGameRA at h5
    set p0 := pr _ (gameRA A c₁ c₂ (issRealR A.toRO PI) (issRealR A.toRO PI) (spRealR A.toRO PS)
      (spRealR A.toRO PS))
    set p1 := pr _ (gameRA A c₁ c₂ (issSimR A.toRO simI progI) (issRealR A.toRO PI)
      (spRealR A.toRO PS) (spRealR A.toRO PS))
    set p2 := pr _ (gameRA A c₁ c₂ (issSimR A.toRO simI progI) (issSimR A.toRO simI progI)
      (spRealR A.toRO PS) (spRealR A.toRO PS))
    set p3 := pr _ (gameRA A c₁ c₂ (issSimR A.toRO simI progI) (issSimR A.toRO simI progI)
      (spSimR A.toRO simS progS) (spRealR A.toRO PS))
    set p4 := pr _ (gameRA A c₁ c₂ (issSimR A.toRO simI progI) (issSimR A.toRO simI progI)
      (spSimR A.toRO simS progS) (spSimR A.toRO simS progS))
    set p5 := pr _ (idealGameRA A simI simS progI progS c₁ c₂)
    have := abs_sub_le p0 p1 p5
    have := abs_sub_le p1 p2 p5
    have := abs_sub_le p2 p3 p5
    have := abs_sub_le p3 p4 p5
    linarith
  have h := hw b₁ b₂
  have h' := hw b₁' b₂'
  rw [idealGameRA_eq] at h h'
  rw [abs_sub_comm] at h'
  have := abs_sub_le (pr _ (realGameRA A PI PS b₁ b₂))
    (pr _ (idealGameRA A simI simS progI progS false false)) (pr _ (realGameRA A PI PS b₁' b₂'))
  linarith

/-! ## With the Lean prover -/

section Lean

open VoleMole.Verifier VoleMole.Verifier.Bridge

variable [CipherRow R] (A : AdversaryRA R Sizes.labelRows)

/-- **Adaptive zero knowledge of the Lean spend prover** (`ZK.Sim.lean_zeroKnowledgeROA`). -/
theorem leanPSR_zkROA [ZKPRow R] (q3 q5 qE s3 s2 s5 sE : ℕ) : ZeroKnowledgeROA SpendRel
    (fun x w (ρ : Coins 16) g (s : ShR R) => leanPSR x w (vec ρ) g s) leanSimSR leanProgSR
    (fun _ Sx => SReads pS Sx s3 s2 s5 sE) (Budget pS q3 q5 qE)
    (εAdG R pS pS.qsDegree q3 q5 qE s3 s2 s5 sE) := by
  have h := lean_zeroKnowledgeROA (R := R) Hashes.shake pS stS (fun _ => rfl) rfl encS SpendRel csS zkHypS
    hashesWF_shake smallParams_pS q3 q5 qE s3 s2 s5 sE (vecOf Sizes.labelRows.spend)
  have e : (fun x w (ρ : Coins 16) g (s : ShR R) => leanPSR x w (vec ρ) g s) =
      fun x w r g s => vecOf _ (realRO pS Hashes.shake (stS x) (encS x w) r g s) := by
    funext x w ρ g s
    exact leanPSR_vec x w ρ g s
  rw [e]
  exact h

/-- An issuance slot's programming is a consistent programming. -/
lemma cprog_PIR (n : NRR) (c : SimCoins pI) :
    CProg (p := pS) (PIR A.toRO leanProgIR n c) 312 4607 := by
  by_cases hT : A.toRO.tInit = 0
  · have e : PIR A.toRO leanProgIR n c = fun s => if False then leanProgIR (xIOf A.toRO n) c s else s := by
      funext s
      simp [PIR, hT]
    rw [e]
    exact CProg.ite False (progRO_cprog (p := pI) (Hb := Hashes.shake) (st := stI (xIOf A.toRO n)) c)
  · have e : PIR A.toRO leanProgIR n c = fun s => leanProgIR (xIOf A.toRO n) c s := by
      funext s
      simp [PIR, hT]
    rw [e]
    exact progRO_cprog (p := pI) (Hb := Hashes.shake) (st := stI (xIOf A.toRO n)) c

/-- A spend slot's programming, under a condition that does not read the tables, is a consistent
programming. -/
lemma cprog_spSim (y : TSsR (SimCoins pS)) (ok : Bool) (τ : TokenS) (d : Credits) :
    CProg (p := pS) ((spSimR A.toRO leanSimSR leanProgSR y).prog ok τ d) 312 4607 :=
  CProg.ite (ok = true) (progRO_cprog (p := pS) (Hb := Hashes.shake) (st := stS _) _)

/-- **The reader of hop S1** (stage 1 through the issuance programmings) reads
`(i₃, i₂, i₅ + 624, i_E + 9214)`. -/
lemma sReads_Sx1 {i3 i2 i5 iE : ℕ} (hI : A.IBudget i3 i2 i5 iE) (γ : ΓS1 (SimCoins pI)) :
    SReads pS (Sx1 A leanSimIR leanProgIR γ) i3 i2 (i5 + 312 + 312) (iE + 4607 + 4607) := by
  have h1 := hI.a2 ((i₀R A.toRO leanSimIR γ.1).req, (i₁R A.toRO leanSimIR γ.1).req) γ.1.1.1.2.2
      γ.1.1.2.2.2 γ.2.2.2
  have h2 := SReads.comp_prog h1 (cprog_PIR A γ.1.1.1.1 γ.1.1.1.2.1)
  have h3 := SReads.comp_prog h2 (cprog_PIR A γ.1.1.2.1 γ.1.1.2.2.1)
  exact h3

/-- **The reader of hop S2** (stage 1 through the issuance programmings, stage 2 through them and
round 1's) reads `(2i₃, 2i₂, 2i₅ + 1560, 2i_E + 23035)`. -/
lemma sReads_Sx2 {i3 i2 i5 iE : ℕ} (hI : A.IBudget i3 i2 i5 iE) (b₁ : Bool)
    (γ : ΓS2 (SimCoins pI) (SimCoins pS)) :
    SReads pS (Sx2 A leanSimIR leanSimSR leanProgIR leanProgSR b₁ γ) (2 * i3) (2 * i2)
      (2 * i5 + 1560) (2 * iE + 23035) := by
  have hm1 := hI.a3 ((i₀R A.toRO leanSimIR γ.1).req, (i₁R A.toRO leanSimIR γ.1).req) γ.1.1.1.2.2
    γ.1.1.2.2.2 γ.1.2.2.2
  have hm2 := SReads.comp_prog hm1 (cprog_PIR A γ.1.1.1.1 γ.1.1.1.2.1)
  have hm := SReads.comp_prog hm2 (cprog_PIR A γ.1.1.2.1 γ.1.1.2.2.1)
  have hg : ∀ y : M₁, SReads pS (fun t : Tb R pS => (y, trans₂ A b₁
      ((γ.1.1.1.2.2, γ.1.1.2.2.2), (γ.1.2.2.2, t.1)) y
      (issSimR A.toRO leanSimIR leanProgIR γ.1.1.1).out (issSimR A.toRO leanSimIR leanProgIR γ.1.1.1).prog
      (issSimR A.toRO leanSimIR leanProgIR γ.1.1.2).out (issSimR A.toRO leanSimIR leanProgIR γ.1.1.2).prog
      (spSimR A.toRO leanSimSR leanProgSR γ.1.2).out (spSimR A.toRO leanSimSR leanProgSR γ.1.2).prog t.2))
      i3 i2 (i5 + 312 + 312 + 312) (iE + 4607 + 4607 + 4607) := by
    intro y
    have h1 := hI.b3 ((i₀R A.toRO leanSimIR γ.1).req, (i₁R A.toRO leanSimIR γ.1).req)
      (spSim A.toRO.base leanSimSR (γ.1.2.1.1, γ.1.2.1.2, γ.1.2.2.1)
        (τ₁Of (A.fixR (y, m2dflt)) b₁ (i₀R A.toRO leanSimIR γ.1) (i₁R A.toRO leanSimIR γ.1)) y.2).req
      γ.1.1.1.2.2 γ.1.1.2.2.2 γ.1.2.2.2
    have h2 := SReads.comp_prog h1 (cprog_PIR A γ.1.1.1.1 γ.1.1.1.2.1)
    have h3 := SReads.comp_prog h2 (cprog_PIR A γ.1.1.2.1 γ.1.1.2.2.1)
    have h4 := SReads.comp_prog h3 (cprog_spSim A γ.1.2 (ok1R (A.fixR (y, m2dflt)) leanSimIR γ.1)
      (τ₁Of (A.fixR (y, m2dflt)) b₁ (i₀R A.toRO leanSimIR γ.1) (i₁R A.toRO leanSimIR γ.1)) y.2)
    exact h4.map (Prod.mk y)
  have h := SReads.bind hm hg
  exact h.mono (by omega) (by omega) (by omega) (by omega)


/-- The statement and witness of round 1 for the collision bound: whenever its token passes the
Client's checks (a real proof is then computed). -/
def stwC1 (b₁ : Bool) (γ : ΓS1 (SimCoins pI)) (x : M₁) : Option (Statement × ByteArray) :=
  if (tokIface A.toRO.base).ok (τ1A A leanSimIR b₁ γ.1 x) x.2 = true then
    some (stS (xSOf A.toRO γ.1.2 (τ1A A leanSimIR b₁ γ.1 x) x.2),
      encS (xSOf A.toRO γ.1.2 (τ1A A leanSimIR b₁ γ.1 x) x.2) (wSOf γ.1.2 (τ1A A leanSimIR b₁ γ.1 x)
        ((clientCheck (τ1A A leanSimIR b₁ γ.1 x).t (τ1A A leanSimIR b₁ γ.1 x).x x.2).getD 0)))
  else none

lemma stwC1_hyp (b₁ : Bool) (γ : ΓS1 (SimCoins pI)) :
    ∀ x st w, stwC1 A b₁ γ x = some (st, w) → st.params = pS ∧
      ZKHyp CrtGen.tables st w (csS (xSOf A.toRO γ.1.2 (τ1A A leanSimIR b₁ γ.1 x) x.2)) := by
  intro x st w h
  unfold stwC1 at h
  split_ifs at h with hok
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hv, t', hc⟩ := valid_of_ok (B := A.toRO.base) hok
    rw [hc, Option.getD_some]
    exact ⟨rfl, zkHypS _ _ (spendRel_of A.toRO γ.1.2 hv hc)⟩

/-- A real round 1 that changes with the tables changes the Lean prover's run. -/
lemma PS1_ne (b₁ : Bool) (γ : ΓS1 (SimCoins pI)) (x : M₁) (ρ : Coins 16) (g : Tab3) (u u' : ShR R)
    (h : PS1 A leanSimIR leanPSR b₁ γ x ρ g u ≠ PS1 A leanSimIR leanPSR b₁ γ x ρ g u') :
    (stwC1 A b₁ γ x).elim False fun sw =>
      realRO pS Hashes.shake sw.1 sw.2 ρ g u ≠ realRO pS Hashes.shake sw.1 sw.2 ρ g u' := by
  obtain ⟨hv, t', hc, hne⟩ := spRealR_ne A.toRO h
  have hok : (tokIface A.toRO.base).ok (τ1A A leanSimIR b₁ γ.1 x) x.2 = true := by
    simp only [tokIface, Bool.and_eq_true, decide_eq_true_eq, hc, Option.isSome_some, and_true]
    exact hv
  simp only [stwC1, hok, ↓reduceIte, Option.elim, hc, Option.getD_some]
  exact hne

/-- **The collision term of hop S1**, with the statement read off the tables:
`δS₁ ≤ i₃·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607; i₅ + 624, i_E + 9214) + noHitProb + 2·2⁻¹⁰²⁴`. -/
theorem deltaS1A_le [ZKPRow R] {i3 i2 i5 iE : ℕ} (hI : A.IBudget i3 i2 i5 iE) (b₁ : Bool) :
    deltaS1A A leanSimIR leanProgIR leanPSR b₁ ≤
      i3 / 2 ^ 128 + (1 / 2 ^ 113 + ZKPRow.εP R pS 0 312 4607 (i5 + 312 + 312) (iE + 4607 + 4607) +
        (noHitProb + 2 / 2 ^ 1024)) := by
  unfold deltaS1A
  refine pr_le_of_fst fun γ => ?_
  refine (pr_mono fun z hz => PS1_ne A b₁ γ _ z.1 z.2.1 _ _ hz).trans ?_
  refine (pr_collide_adaptive Hashes.shake pS rfl smallParams_pS hashesWF_shake (stwC1 A b₁ γ)
    (fun x => csS (xSOf A.toRO γ.1.2 (τ1A A leanSimIR b₁ γ.1 x) x.2)) (stwC1_hyp A b₁ γ)
    (Sx1 A leanSimIR leanProgIR γ) (sReads_Sx1 A hI γ) (fun _ => PI2R A.toRO leanProgIR γ.1) _
    (fun _ => progAt_PI2R A.toRO γ.1) _ (fun _ => tails_PI2R A.toRO γ.1)).trans ?_
  have hc : (({simTail γ.1.1.1.2.1, simTail γ.1.1.2.2.1} : Finset ByteArray).card : ℝ) ≤ 2 := by
    exact_mod_cast Finset.card_le_two
  rw [show (8 * (16 * (pS.qsDegree - 1)) : ℕ) = 1024 from rfl]
  gcongr


/-- The programming before round 2's (the issuances' and round 1's, if it runs) is at blocks
whose tails are those of the three simulations. -/
lemma progAt_LS2R (B : AdversaryRO R Sizes.labelRows) (b₁ : Bool)
    (γ : ΓS2 (SimCoins pI) (SimCoins pS)) :
    ∃ Bk : ShR R → Finset (ZK.Sim.Bytes (preLen pI)),
      ProgAt (LS2R B leanSimIR leanProgIR leanProgSR b₁ γ) Bk ∧
      ∀ s, ∀ b ∈ Bk s, preTail b ∈
        ({simTail γ.1.2.2.1, simTail γ.1.1.1.2.1, simTail γ.1.1.2.2.1} : Finset ByteArray) := by
  set xS := xSOf B γ.1.2.1 (τ₁Of B b₁ (i₀R B leanSimIR γ.1) (i₁R B leanSimIR γ.1))
    (B.d₁ ((i₀R B leanSimIR γ.1).req, (i₁R B leanSimIR γ.1).req))
  set ok := ok1R B leanSimIR γ.1
  have hLi := ProgAt.ite (ok = true) (progRO_progAt (R := R) Hashes.shake (stS xS) γ.1.2.2.1)
  refine ⟨_, (progAt_PI2R B γ.1).comp hLi, fun s b' hb => ?_⟩
  rcases Finset.mem_union.1 hb with hb | hb
  · exact Finset.mem_insert.2 (Or.inr (tails_PI2R B γ.1 _ b' hb))
  · by_cases hc : ok = true
    · simp only [hc, ↓reduceIte] at hb
      have hb' : b' = simBlk Hashes.shake (stS xS) γ.1.2.2.1 s := Finset.mem_singleton.1 hb
      rw [hb']
      exact Finset.mem_insert.2 (Or.inl (preTail_simBlk hashesWF_shake rfl _ _))
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hb
      exact absurd hb (Finset.notMem_empty _)

/-- The statement and witness of round 2 for the collision bound. -/
def stwC2 (b₁ b₂ : Bool) (γ : ΓS2 (SimCoins pI) (SimCoins pS)) (x : MsgR) :
    Option (Statement × ByteArray) :=
  if (tokIface A.toRO.base).ok (τ₂R (A.fixR x) leanSimIR leanSimSR b₁ b₂ γ)
      (d₂R (A.fixR x) leanSimIR leanSimSR b₁ γ) = true then
    some (stS (xSOf A.toRO γ.2 (τ₂R (A.fixR x) leanSimIR leanSimSR b₁ b₂ γ)
        (d₂R (A.fixR x) leanSimIR leanSimSR b₁ γ)),
      encS (xSOf A.toRO γ.2 (τ₂R (A.fixR x) leanSimIR leanSimSR b₁ b₂ γ)
        (d₂R (A.fixR x) leanSimIR leanSimSR b₁ γ))
        (wSOf γ.2 (τ₂R (A.fixR x) leanSimIR leanSimSR b₁ b₂ γ)
          ((clientCheck (τ₂R (A.fixR x) leanSimIR leanSimSR b₁ b₂ γ).t
            (τ₂R (A.fixR x) leanSimIR leanSimSR b₁ b₂ γ).x
            (d₂R (A.fixR x) leanSimIR leanSimSR b₁ γ)).getD 0)))
  else none

lemma stwC2_hyp (b₁ b₂ : Bool) (γ : ΓS2 (SimCoins pI) (SimCoins pS)) :
    ∀ x st w, stwC2 A b₁ b₂ γ x = some (st, w) → st.params = pS ∧
      ZKHyp CrtGen.tables st w (csS (xSOf A.toRO γ.2 (τ₂R (A.fixR x) leanSimIR leanSimSR b₁ b₂ γ)
        (d₂R (A.fixR x) leanSimIR leanSimSR b₁ γ))) := by
  intro x st w h
  unfold stwC2 at h
  split_ifs at h with hok
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hv, t', hc⟩ := valid_of_ok (B := A.toRO.base) hok
    rw [hc, Option.getD_some]
    exact ⟨rfl, zkHypS _ _ (spendRel_of A.toRO γ.2 hv hc)⟩

lemma PS2_ne (b₁ b₂ : Bool) (γ : ΓS2 (SimCoins pI) (SimCoins pS)) (x : MsgR) (ρ : Coins 16)
    (g : Tab3) (u u' : ShR R)
    (h : PS2 A leanSimIR leanSimSR leanPSR b₁ b₂ γ x ρ g u ≠
      PS2 A leanSimIR leanSimSR leanPSR b₁ b₂ γ x ρ g u') :
    (stwC2 A b₁ b₂ γ x).elim False fun sw =>
      realRO pS Hashes.shake sw.1 sw.2 ρ g u ≠ realRO pS Hashes.shake sw.1 sw.2 ρ g u' := by
  obtain ⟨hv, t', hc, hne⟩ := spRealR_ne A.toRO h
  have hok : (tokIface A.toRO.base).ok (τ₂R (A.fixR x) leanSimIR leanSimSR b₁ b₂ γ)
      (d₂R (A.fixR x) leanSimIR leanSimSR b₁ γ) = true := by
    simp only [tokIface, Bool.and_eq_true, decide_eq_true_eq, hc, Option.isSome_some, and_true]
    exact hv
  simp only [stwC2, hok, ↓reduceIte, Option.elim, hc, Option.getD_some]
  exact hne

/-- **The collision term of hop S2**, with the statement read off the tables:
`δS₂ ≤ 2i₃·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607; 2i₅ + 1560, 2i_E + 23035) + noHitProb + 3·2⁻¹⁰²⁴`. -/
theorem deltaS2A_le [ZKPRow R] {i3 i2 i5 iE : ℕ} (hI : A.IBudget i3 i2 i5 iE) (b₁ b₂ : Bool) :
    deltaS2A A leanSimIR leanSimSR leanProgIR leanProgSR leanPSR b₁ b₂ ≤
      (2 * i3 : ℕ) / 2 ^ 128 + (1 / 2 ^ 113 + ZKPRow.εP R pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035) +
        (noHitProb + 3 / 2 ^ 1024)) := by
  unfold deltaS2A
  refine pr_le_of_fst fun γ => ?_
  refine (pr_mono fun z hz => PS2_ne A b₁ b₂ γ _ z.1 z.2.1 _ _ hz).trans ?_
  choose Bx hBx using fun x : MsgR => progAt_LS2R (A.fixR x) b₁ γ
  refine (pr_collide_adaptive Hashes.shake pS rfl smallParams_pS hashesWF_shake (stwC2 A b₁ b₂ γ)
    (fun x => csS (xSOf A.toRO γ.2 (τ₂R (A.fixR x) leanSimIR leanSimSR b₁ b₂ γ)
      (d₂R (A.fixR x) leanSimIR leanSimSR b₁ γ))) (stwC2_hyp A b₁ b₂ γ)
    (Sx2 A leanSimIR leanSimSR leanProgIR leanProgSR b₁ γ) (sReads_Sx2 A hI b₁ γ)
    (fun x => LS2R (A.fixR x) leanSimIR leanProgIR leanProgSR b₁ γ) Bx (fun x => (hBx x).1) _
    (fun x => (hBx x).2)).trans ?_
  have hc : (({simTail γ.1.2.2.1, simTail γ.1.1.1.2.1, simTail γ.1.1.2.2.1} :
      Finset ByteArray).card : ℝ) ≤ 3 := by
    exact_mod_cast Finset.card_le_three
  rw [show (8 * (16 * (pS.qsDegree - 1)) : ℕ) = 1024 from rfl]
  gcongr


/-- **Theorem 2 with the Lean prover, the Issuer's interaction reading the tables, for every type
of cipher rows** (`ZKPRow R`; `unlinkabilityRA_lean_num` at function rows). -/
theorem unlinkabilityRA_lean_numG [ZKRow R] [ZKPRow R] {q3 q5 qE i3 i2 i5 iE : ℕ} {εhide : ℝ} (hA : A.GBudget q3 q5 qE)
    (hI : A.IBudget i3 i2 i5 iE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionRA A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRA A leanPIR leanPSR b₁ b₂) - pr _ (realGameRA A leanPIR leanPSR b₁' b₂')| ≤
      4 * ZKRow.εz R pI (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) +
        2 * εAdG R pS 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        2 * εAdG R pS 9 q3 (q5 + 936) (qE + 13821) (2 * i3) (2 * i2) (2 * i5 + 1560)
          (2 * iE + 23035) +
        6 * (i3 / 2 ^ 128) +
        4 * (1 / 2 ^ 113 + ZKPRow.εP R pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  have hPI5 : ∀ x w ρ g, Rd5 (leanPIR (R := R) x w ρ g) 624 := fun x w ρ g =>
    (realROb_rd5 (p := pI) (Hb := Hashes.shake) (st := stI x) (w := encI x w) (bOf ρ) g).map
      (vecOf Sizes.labelRows.issue)
  have hPIE : ∀ x w ρ g, RdE (leanPIR (R := R) x w ρ g) 4607 := fun x w ρ g =>
    (realROb_rdE (p := pI) (st := stI x) (w := encI x w) hashesWF_shake (bOf ρ) g).map
      (vecOf Sizes.labelRows.issue)
  have hPS5 : ∀ x w ρ g, Rd5 (leanPSR (R := R) x w ρ g) 624 := fun x w ρ g =>
    (realROb_rd5 (p := pS) (Hb := Hashes.shake) (st := stS x) (w := encS x w) (bOf ρ) g).map
      (vecOf Sizes.labelRows.spend)
  have hPSE : ∀ x w ρ g, RdE (leanPSR (R := R) x w ρ g) 4607 := fun x w ρ g =>
    (realROb_rdE (p := pS) (st := stS x) (w := encS x w) hashesWF_shake (bOf ρ) g).map
      (vecOf Sizes.labelRows.spend)
  have h := unlinkabilityRA (A := A) (PI := leanPIR) (PS := leanPSR) (simI := leanSimIR)
    (simS := leanSimSR) (progI := leanProgIR) (progS := leanProgSR) (εI := ZKRow.εz R pI)
    (εS₁ := fun a b c => εAdG R pS pS.qsDegree a b c i3 i2 (i5 + 312 + 312) (iE + 4607 + 4607))
    (εS₂ := fun a b c => εAdG R pS pS.qsDegree a b c (2 * i3) (2 * i2) (2 * i5 + 1560) (2 * iE + 23035))
    (AdmS₁ := fun _ Sx => SReads pS Sx i3 i2 (i5 + 312 + 312) (iE + 4607 + 4607))
    (AdmS₂ := fun _ Sx => SReads pS Sx (2 * i3) (2 * i2) (2 * i5 + 1560) (2 * iE + 23035))
    hA hI hPI5 hPIE hPS5 hPSE (fun x c => progRO_isProg c) (fun x c => progRO_isProg c)
    leanProgIR_none leanProgSR_none (sReads_Sx1 A hI) (fun b₁ => sReads_Sx2 A hI b₁)
    (fun a b c => leanPIR_zkRO a b c) (fun a b c => leanPSR_zkROA a b c _ _ _ _)
    (fun a b c => leanPSR_zkROA a b c _ _ _ _) (fun a b c => ZKRow.εz_nonneg _ _ _ _) hhide
    b₁ b₂ b₁' b₂'
  have mI : ∀ a b c, a ≤ 2 * i3 + q3 → b ≤ q5 + 2 * i5 + 1872 → c ≤ qE + 2 * iE + 13821 →
      ZKRow.εz R pI a b c ≤ ZKRow.εz R pI (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) :=
    fun a b c ha hb hc => ZKRow.εz_mono pI ha hb hc
  have m1 := mI (i3 + i3 + q3) (0 + (624 + (i5 + (624 + (i5 + (624 + q5))))))
    (0 + (4607 + (iE + (4607 + (iE + (4607 + qE)))))) (by omega) (by omega) (by omega)
  have m2 := mI (i3 + i3 + q3) (0 + (0 + (i5 + (624 + (i5 + (624 + q5))))) + 312)
    (0 + (0 + (iE + (4607 + (iE + (4607 + qE))))) + 4607) (by omega) (by omega) (by omega)
  have m3 : εAdG R pS pS.qsDegree (i3 + q3) (i5 + (0 + (0 + (0 + (624 + q5)))) + (312 + 312))
      (iE + (0 + (0 + (0 + (4607 + qE)))) + (4607 + 4607)) i3 i2 (i5 + 312 + 312)
      (iE + 4607 + 4607) ≤
      εAdG R pS 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) i3 i2 (i5 + 624) (iE + 9214) :=
    εAdG_mono pS le_rfl (by omega) (by omega) le_rfl le_rfl (by omega) (by omega)
  have m4 : εAdG R pS pS.qsDegree q3 (0 + (0 + (0 + (0 + q5))) + (312 + (312 + 312)))
      (0 + (0 + (0 + (0 + qE))) + (4607 + (4607 + 4607))) (2 * i3) (2 * i2) (2 * i5 + 1560)
      (2 * iE + 23035) ≤
      εAdG R pS 9 q3 (q5 + 936) (qE + 13821) (2 * i3) (2 * i2) (2 * i5 + 1560) (2 * iE + 23035) :=
    εAdG_mono pS le_rfl (by omega) (by omega) le_rfl le_rfl le_rfl le_rfl
  have d1 := deltaI1R_le A.toRO
  have dS1 := deltaS1A_le A hI b₁
  have dS1' := deltaS1A_le A hI b₁'
  have dS2 := deltaS2A_le A hI b₁ b₂
  have dS2' := deltaS2A_le A hI b₁' b₂'
  have eP : ZKPRow.εP R pS 0 312 4607 (i5 + 312 + 312) (iE + 4607 + 4607) ≤
      ZKPRow.εP R pS 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035) :=
    ZKPRow.εP_mono pS le_rfl le_rfl le_rfl (by omega) (by omega)
  have ec : ((2 * i3 : ℕ) : ℝ) / 2 ^ 128 = 2 * (i3 / 2 ^ 128) := by push_cast; ring
  rw [ec] at dS2 dS2'
  refine h.trans ?_
  rw [div_eq_mul_one_div (2 : ℝ) ((2 : ℝ) ^ 1024)] at dS1 dS1'
  rw [div_eq_mul_one_div (3 : ℝ) ((2 : ℝ) ^ 1024)] at dS2 dS2'
  rw [div_eq_mul_one_div (12 : ℝ) ((2 : ℝ) ^ 1024)]
  generalize (1 : ℝ) / 2 ^ 1024 = κ at d1 dS1 dS1' dS2 dS2' ⊢
  linarith

/-- **Theorem 2 with the Lean prover, in the random-oracle and ideal-cipher model, the Issuer's
interaction reading the tables, with every term explicit.** The guess reads each `H₃` slice at `q₃`
keys, `H₅` at `q₅`, the cipher at `q_E` and `H₂³` freely; each stage of the interaction (the
issuance responses and `d₁`; round 1's spend response and `d₂`) reads, as a function of each slice
and the shared tables, at most `i₃` slice keys, `i₂` `H₂³` keys, `i₅` `H₅` keys and `i_E` cipher
keys, consistently. Then any two worlds differ by at most

    4·εRO(2i₃ + q₃, q₅ + 2i₅ + 1872, q_E + 2i_E + 13821)
      + 2·εAd(9; i₃ + q₃, q₅ + i₅ + 1248, q_E + i_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214)
      + 2·εAd(9; q₃, q₅ + 936, q_E + 13821; 2i₃, 2i₂, 2i₅ + 1560, 2i_E + 23035)
      + 6·i₃·2⁻¹²⁸ + 4·(2⁻¹¹³ + εROP(0, 312, 4607; 2i₅ + 1560, 2i_E + 23035))
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

The issuance hops pay both stages' reads and the three real proofs (`3·624`, `3·4607`) as the
distinguisher's (`εRO`); round 1's hop is the adaptive theorem with stage 1 as the reader (through
the two issuance programmings) and stage 2, round 2's real proof and the guess as the
distinguisher; round 2's hop has the whole transcript as the reader (stage 2 also through round
1's programming, `5·312`, `5·4607`).

(`unlinkabilityRA_lean_numG` at function rows.) -/
theorem unlinkabilityRA_lean_num (A : AdversaryRA (Blk → Blk) Sizes.labelRows)
    {q3 q5 qE i3 i2 i5 iE : ℕ} {εhide : ℝ} (hA : A.GBudget q3 q5 qE)
    (hI : A.IBudget i3 i2 i5 iE)
    (hhide : ∀ b₁ b₂ K, hidingAdv A.ctx
      (reductionRA A leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGameRA A leanPIR leanPSR b₁ b₂) - pr _ (realGameRA A leanPIR leanPSR b₁' b₂')| ≤
      4 * εRO (2 * i3 + q3) (q5 + 2 * i5 + 1872) (qE + 2 * iE + 13821) +
        2 * εAd 9 (i3 + q3) (q5 + i5 + 1248) (qE + iE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        2 * εAd 9 q3 (q5 + 936) (qE + 13821) (2 * i3) (2 * i2) (2 * i5 + 1560) (2 * iE + 23035) +
        6 * (i3 / 2 ^ 128) + 4 * (1 / 2 ^ 113 + εROP 0 312 4607 (2 * i5 + 1560) (2 * iE + 23035)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  unlinkabilityRA_lean_numG A hA hI hhide b₁ b₂ b₁' b₂'

end Lean

end VoleMole.Privacy.Ratatouille
