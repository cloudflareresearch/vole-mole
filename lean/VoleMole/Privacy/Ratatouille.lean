import VoleMole.Privacy.Basic
import VoleMole.Spec.Ratatouille

/-!
# Ratatouille unlinkability on the executable spec (`security/ratatouille.md` §6, Theorem 2)

A malicious Issuer (any public key, context, initial balance, responses, refunds and amounts)
faces two honest Clients, run on `Spec/Ratatouille.lean`'s `issueRequestWithSeed`,
`finalizeIssue`, `spendRequestWithSeed` and `finalizeSpend`. Both Clients are issued a token
worth `T_init` (the leakage of an issuance; equal for both, as unlinkability requires). Then:

* **round 1**: Client `b₁` spends `d₁` (the Issuer sees the request, answers with a refund and a
  signature, and the Client finalizes its change token);
* **round 2**: Client `b₂` spends `d₂` from its *current* token: the change token from round 1 if
  `b₂ = b₁`, its issued token otherwise.

So `b₁` links a spend to an issuance, and `b₂ = b₁` versus `b₂ ≠ b₁` links two spends through the
change-token mechanics. As in Moussaka's game, a round runs only if it is possible for every
candidate token (each is valid for `pk` and affords the amount); otherwise it is refused for
both, since feasibility is leakage the note allows (`ℒ` is `(pk, ctx, d)` and "whether the client
could afford the spend"). The Issuer's guess sees the two issuance requests and the two spend
requests (or the errors the Clients throw).

## Structure

* `view`: the game for any token type `Tok`, from two issuance slots (`IssOut`: the request and
  the Client's finalization) and two spend slots (`SpOut`, as a function of the token spent and
  the amount). `game` draws each slot from its own part of a uniform tape; `game_hop*` replace
  one slot at a time.
* The spec's world: tokens `TokenS`, slots `issOutOf (issueOf …)`, `spOutOf (spendOf …)`
  (`issueOf`, `spendOf` are the spec functions at the output of `expand_seed`:
  `issueRequestWithSeed_eq`, `spendRequestWithSeed_eq`). **H2** (`issue_close`, `spend_close`):
  real and simulated proofs, slot by slot, from zero knowledge of both proof systems.
* **The public world** (`PubTok`: `nf, t, x, s` and the commitment the Client sent; the opening is
  gone). `view_map`: a token map that commutes with the slots and the refusal test preserves the
  view; so the simulated spec world is the public world with commitment functions
  `t ↦ Com(nf, ctx, t, r)` (`simGame_iff`). This is the note's "the client finalizes against the
  commitment string it sent": after H2 the opening enters nothing but `Com`.
* **H3** (`hiding_hop`): the commitments are replaced by independent uniform strings; hiding of
  `Com` is a computational assumption on Keccak-p[800], stated for the explicit reduction
  `reduction` (the adversary with the simulator coins fixed) in the joint form of `ε_hide^K`
  (§2.2): four commitments, at adaptively chosen credit values, with their nullifiers.
* `idealGame_eq`: in the ideal world the four worlds `(b₁, b₂)` coincide exactly: each spend
  reveals a nullifier that appears nowhere else (`idealGame_iff`, then swaps of the nullifiers).
* **`unlinkability`**: for all `(b₁, b₂)`, `(b₁', b₂')`, the acceptance probabilities differ by at
  most `4εI + 4εS + 2εhide`.

## Assumptions and what is on paper

* Zero knowledge of the issuance and spend proofs (`Privacy.ZeroKnowledge`, including the grinding
  abort `none`), against distinguishers that may know the witness. With the label-row fix this is
  `lean/docs/zk.md`'s theorem. **On `main` no efficient simulator satisfies it**: a distinguisher
  that knows `r = w[0..16)` computes the label offset and runs the test of `lean/docs/zk.md`
  Prop. 4.1. There the note's (PU) argument (`ZK/Relations.lean`, `ratatouille_main_zk`) replaces
  it; that hop is on paper.
* H1 (the seed XOF's output replaced by uniform values, `q_H·Q_P·2⁻²⁵⁶` and Lemma DS) is a
  random-oracle step on paper: the games draw `(nf, r, ρ)` uniformly.
* Hiding (`hidingAdv ≤ εhide` for the reduction).
-/

open Finset

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille

variable {SK : Type}

/-! ## The spec with the seed expansion's output given -/

/-- `issue_request_with_seed` with `(nf, r, ρ) = expand_seed(…)` as arguments. -/
def issueOf (P : Prim SK) (tInit : Credits) (ctx : Context) (nf : Nullifier) (r : Opening)
    (ρ : Rho) : Except Error (PendingTokenS × IssueRequest) :=
  if tInit = 0 then .error .invalidArgument else
  match P.proveIssue ⟨com nf ctx tInit r, tInit, ctx⟩ ⟨nf, r⟩ ρ with
  | none => .error .runtime
  | some pf => .ok (⟨nf, r, tInit, com nf ctx tInit r⟩, issueReqBytes (com nf ctx tInit r) pf)

theorem issueRequestWithSeed_eq (P : Prim SK) (tInit : Credits) (ctx : Context) (seed : Seed) :
    issueRequestWithSeed P tInit ctx seed =
      issueOf P tInit ctx (expandSeed issueSeedDst seed).1 (expandSeed issueSeedDst seed).2.1
        (expandSeed issueSeedDst seed).2.2 := rfl

/-- `spend_request_with_seed` with `(nf', r', ρ) = expand_seed(…)` as arguments. -/
def spendOf (P : Prim SK) (pk : PublicKey) (tok : Option TokenS) (d : Credits) (ctx : Context)
    (nf' : Nullifier) (r' : Opening) (ρ : Rho) :
    Option TokenS × Except Error (PendingSpendS × SpendRequest) :=
  match tok with
  | none => (none, .error .logic)
  | some τ =>
    if ¬ τ.Valid pk ctx then (some τ, .error .invalidArgument) else
    match clientCheck τ.t τ.x d with
    | none => (some τ, .error .invalidArgument)
    | some t' =>
      match P.proveSpend ⟨pk, τ.nf, d, com nf' ctx t' r', ctx⟩ ⟨τ.t, τ.r, τ.x, τ.s, nf', t', r'⟩ ρ with
      | none => (none, .error .runtime)
      | some pf => (none, .ok (⟨nf', t', r', com nf' ctx t' r'⟩,
          SpendReq.toBytes ⟨τ.nf, d, com nf' ctx t' r', pf⟩))

theorem spendRequestWithSeed_eq (P : Prim SK) (pk : PublicKey) (tok : Option TokenS) (d : Credits)
    (ctx : Context) (seed : Seed) :
    spendRequestWithSeed P pk tok d ctx seed =
      spendOf P pk tok d ctx (expandSeed spendSeedDst seed).1 (expandSeed spendSeedDst seed).2.1
        (expandSeed spendSeedDst seed).2.2 := rfl

/-! ## The game, for any token type -/

/-- An issuance as the Issuer meets it: the request (or the Client's error) and the Client's
finalization of a response. -/
structure IssOut (Tok : Type) where
  req : Except Error IssueRequest
  fin : Preimage → Option Tok

/-- A spend: the request (or error) and the Client's finalization of the response. -/
structure SpOut (Tok : Type) where
  req : Except Error SpendRequest
  fin : SpendResponse → Option Tok

/-- The two issuance requests, in Client order. -/
abbrev IssTr := Except Error IssueRequest × Except Error IssueRequest

/-- The malicious Issuer. -/
structure Adversary where
  pk : PublicKey
  ctx : Context
  tInit : Credits
  respondIss : IssTr → Bool → Preimage
  d₁ : IssTr → Credits
  respond₁ : IssTr → Except Error SpendRequest → SpendResponse
  d₂ : IssTr → Except Error SpendRequest → Credits
  guess : IssTr → Option (Except Error SpendRequest × Option (Except Error SpendRequest)) → Prop

/-- What the game needs to know about tokens: the refusal test ("valid and affords `d`") and a
dummy token (used where a token is missing; nothing is revealed then). -/
structure Iface (Tok : Type) where
  ok : Tok → Credits → Bool
  dflt : Tok

variable (A : Adversary) {Tok : Type} (I : Iface Tok)

/-- Client `c`'s token, or the dummy. -/
def tokD (tk₀ tk₁ : Option Tok) (c : Bool) : Tok := (bif c then tk₁ else tk₀).getD I.dflt

/-- Round 1 runs: both tokens exist, and both are valid and afford `d₁`. -/
def ok₁ (tr : IssTr) (tk₀ tk₁ : Option Tok) : Bool :=
  tk₀.isSome && tk₁.isSome && I.ok (tokD I tk₀ tk₁ false) (A.d₁ tr) &&
    I.ok (tokD I tk₀ tk₁ true) (A.d₁ tr)

/-- Round 2 runs: the change token exists, and both current tokens are valid and afford `d₂`. -/
def ok₂ (b₁ : Bool) (tr : IssTr) (tk₀ tk₁ : Option Tok) (rq : Except Error SpendRequest)
    (ch : Option Tok) : Bool :=
  ch.isSome && I.ok (ch.getD I.dflt) (A.d₂ tr rq) && I.ok (tokD I tk₀ tk₁ (!b₁)) (A.d₂ tr rq)

/-- The token Client `b₂` spends in round 2: its change token if it spent in round 1. -/
def cur₂ (b₁ b₂ : Bool) (tk₀ tk₁ : Option Tok) (ch : Option Tok) : Tok :=
  bif b₂ == b₁ then ch.getD I.dflt else tokD I tk₀ tk₁ (!b₁)

/-- The guess, from the issuance transcript, round 1's request and change token, and round 2's
request. -/
def stage₃ (b₁ : Bool) (tr : IssTr) (tk₀ tk₁ : Option Tok) (rq : Except Error SpendRequest)
    (ch : Option Tok) (y : Except Error SpendRequest) : Prop :=
  A.guess tr (bif ok₁ A I tr tk₀ tk₁ then
    some (rq, bif ok₂ A I b₁ tr tk₀ tk₁ rq ch then some y else none) else none)

/-- After round 1. -/
def stage₂ (b₁ b₂ : Bool) (tr : IssTr) (tk₀ tk₁ : Option Tok) (rq : Except Error SpendRequest)
    (ch : Option Tok) (s₂ : Tok → Credits → SpOut Tok) : Prop :=
  stage₃ A I b₁ tr tk₀ tk₁ rq ch (s₂ (cur₂ I b₁ b₂ tk₀ tk₁ ch) (A.d₂ tr rq)).req

/-- After issuance. -/
def stage₁ (b₁ b₂ : Bool) (tr : IssTr) (tk₀ tk₁ : Option Tok) (s₁ s₂ : Tok → Credits → SpOut Tok) :
    Prop :=
  stage₂ A I b₁ b₂ tr tk₀ tk₁ (s₁ (tokD I tk₀ tk₁ b₁) (A.d₁ tr)).req
    ((s₁ (tokD I tk₀ tk₁ b₁) (A.d₁ tr)).fin (A.respond₁ tr (s₁ (tokD I tk₀ tk₁ b₁) (A.d₁ tr)).req))
    s₂

/-- **The view in world `(b₁, b₂)`.** -/
def view (b₁ b₂ : Bool) (i₀ i₁ : IssOut Tok) (s₁ s₂ : Tok → Credits → SpOut Tok) : Prop :=
  stage₁ A I b₁ b₂ (i₀.req, i₁.req) (i₀.fin (A.respondIss (i₀.req, i₁.req) false))
    (i₁.fin (A.respondIss (i₀.req, i₁.req) true)) s₁ s₂

/-- The game with the four slots drawn from their parts of the tape. -/
def game {T₀ T₁ T₂ T₃ : Type} (b₁ b₂ : Bool) (g₀ : T₀ → IssOut Tok) (g₁ : T₁ → IssOut Tok)
    (h₁ : T₂ → Tok → Credits → SpOut Tok) (h₂ : T₃ → Tok → Credits → SpOut Tok)
    (x : (T₀ × T₁) × (T₂ × T₃)) : Prop :=
  view A I b₁ b₂ (g₀ x.1.1) (g₁ x.1.2) (h₁ x.2.1) (h₂ x.2.2)

/-! ## Hops on one slot -/

/-- Two issuance samplers are `ε`-close for every response strategy. -/
def IssClose {T T' : Type} [Fintype T] [Fintype T'] (ε : ℝ) (g : T → IssOut Tok)
    (g' : T' → IssOut Tok) : Prop :=
  ∀ f : Except Error IssueRequest → Preimage, Close ε (fun x => ((g x).req, (g x).fin (f (g x).req)))
    (fun x => ((g' x).req, (g' x).fin (f (g' x).req)))

/-- Two spend samplers are `ε`-close at every token and amount, for every response strategy. -/
def SpClose {T T' : Type} [Fintype T] [Fintype T'] (ε : ℝ) (h : T → Tok → Credits → SpOut Tok)
    (h' : T' → Tok → Credits → SpOut Tok) : Prop :=
  ∀ τ d (f : Except Error SpendRequest → SpendResponse),
    Close ε (fun x => ((h x τ d).req, (h x τ d).fin (f (h x τ d).req)))
      (fun x => ((h' x τ d).req, (h' x τ d).fin (f (h' x τ d).req)))

variable {T₀ T₁ T₂ T₃ T₀' T₁' T₂' T₃' : Type} [Fintype T₀] [Fintype T₁] [Fintype T₂] [Fintype T₃]
  [Fintype T₀'] [Fintype T₁'] [Fintype T₂'] [Fintype T₃']

theorem game_hop₀ [Nonempty T₁] [Nonempty T₂] [Nonempty T₃] (b₁ b₂ : Bool) {ε : ℝ}
    {g₀ : T₀ → IssOut Tok} {g₀' : T₀' → IssOut Tok} (g₁ : T₁ → IssOut Tok)
    (h₁ : T₂ → Tok → Credits → SpOut Tok) (h₂ : T₃ → Tok → Credits → SpOut Tok)
    (h : IssClose ε g₀ g₀') :
    |pr _ (game A I b₁ b₂ g₀ g₁ h₁ h₂) - pr _ (game A I b₁ b₂ g₀' g₁ h₁ h₂)| ≤ ε :=
  abs_pr_prod_sub_le' _ _ fun y => abs_pr_prod_sub_le' _ _ fun x₁ =>
    h (fun rq => A.respondIss (rq, (g₁ x₁).req) false) (fun p =>
      stage₁ A I b₁ b₂ (p.1, (g₁ x₁).req) p.2 ((g₁ x₁).fin (A.respondIss (p.1, (g₁ x₁).req) true))
        (h₁ y.1) (h₂ y.2))

theorem game_hop₁ [Nonempty T₀] [Nonempty T₂] [Nonempty T₃] (b₁ b₂ : Bool) {ε : ℝ}
    (g₀ : T₀ → IssOut Tok) {g₁ : T₁ → IssOut Tok} {g₁' : T₁' → IssOut Tok}
    (h₁ : T₂ → Tok → Credits → SpOut Tok) (h₂ : T₃ → Tok → Credits → SpOut Tok)
    (h : IssClose ε g₁ g₁') :
    |pr _ (game A I b₁ b₂ g₀ g₁ h₁ h₂) - pr _ (game A I b₁ b₂ g₀ g₁' h₁ h₂)| ≤ ε :=
  abs_pr_prod_sub_le' _ _ fun y => abs_pr_prod_sub_le _ _ fun x₀ =>
    h (fun rq => A.respondIss ((g₀ x₀).req, rq) true) (fun p =>
      stage₁ A I b₁ b₂ ((g₀ x₀).req, p.1) ((g₀ x₀).fin (A.respondIss ((g₀ x₀).req, p.1) false)) p.2
        (h₁ y.1) (h₂ y.2))

theorem game_hop₂ [Nonempty T₀] [Nonempty T₁] [Nonempty T₃] (b₁ b₂ : Bool) {ε : ℝ}
    (g₀ : T₀ → IssOut Tok) (g₁ : T₁ → IssOut Tok) {h₁ : T₂ → Tok → Credits → SpOut Tok}
    {h₁' : T₂' → Tok → Credits → SpOut Tok} (h₂ : T₃ → Tok → Credits → SpOut Tok)
    (h : SpClose ε h₁ h₁') :
    |pr _ (game A I b₁ b₂ g₀ g₁ h₁ h₂) - pr _ (game A I b₁ b₂ g₀ g₁ h₁' h₂)| ≤ ε :=
  abs_pr_prod_sub_le _ _ fun x => abs_pr_prod_sub_le' _ _ fun y₂ =>
    let tr : IssTr := ((g₀ x.1).req, (g₁ x.2).req)
    let tk₀ := (g₀ x.1).fin (A.respondIss tr false)
    let tk₁ := (g₁ x.2).fin (A.respondIss tr true)
    h (tokD I tk₀ tk₁ b₁) (A.d₁ tr) (A.respond₁ tr)
      (fun p => stage₂ A I b₁ b₂ tr tk₀ tk₁ p.1 p.2 (h₂ y₂))

theorem game_hop₃ [Nonempty T₀] [Nonempty T₁] [Nonempty T₂] (b₁ b₂ : Bool) {ε : ℝ}
    (g₀ : T₀ → IssOut Tok) (g₁ : T₁ → IssOut Tok) (h₁ : T₂ → Tok → Credits → SpOut Tok)
    {h₂ : T₃ → Tok → Credits → SpOut Tok} {h₂' : T₃' → Tok → Credits → SpOut Tok}
    (h : SpClose ε h₂ h₂') :
    |pr _ (game A I b₁ b₂ g₀ g₁ h₁ h₂) - pr _ (game A I b₁ b₂ g₀ g₁ h₁ h₂')| ≤ ε :=
  abs_pr_prod_sub_le _ _ fun x => abs_pr_prod_sub_le _ _ fun y₁ =>
    let tr : IssTr := ((g₀ x.1).req, (g₁ x.2).req)
    let tk₀ := (g₀ x.1).fin (A.respondIss tr false)
    let tk₁ := (g₁ x.2).fin (A.respondIss tr true)
    let o := h₁ y₁ (tokD I tk₀ tk₁ b₁) (A.d₁ tr)
    let ch := o.fin (A.respond₁ tr o.req)
    h (cur₂ I b₁ b₂ tk₀ tk₁ ch) (A.d₂ tr o.req) (fun _ => default)
      (fun p => stage₃ A I b₁ tr tk₀ tk₁ o.req ch p.1)

/-! ## The spec's world -/

/-- A well-formed dummy token. -/
def dfltTok : TokenS := ⟨Vector.ofFn fun _ => 0, 0, Vector.ofFn fun _ => 0, 0, Vector.ofFn fun _ => 0⟩

/-- The spec's refusal test: `TokenS.Valid` (`ratatouille.cpp:221`, recomputing `Com` from the
opening) and the Client's 64-bit check. -/
def tokIface : Iface TokenS :=
  ⟨fun τ d => decide (τ.Valid A.pk A.ctx) && (clientCheck τ.t τ.x d).isSome, dfltTok⟩

/-- An issuance slot from the spec's `issue_request_with_seed` output and `finalize_issue`. -/
def issOutOf (r : Except Error (PendingTokenS × IssueRequest)) : IssOut TokenS where
  req := match r with
    | .ok q => .ok q.2
    | .error e => .error e
  fin s := match r with
    | .ok q => match (finalizeIssue A.pk (some q.1) s).2 with
      | .ok o => o
      | .error _ => none
    | .error _ => none

/-- A spend slot from the spec's `spend_request_with_seed` output and `finalize_spend`. -/
def spOutOf (r : Except Error (PendingSpendS × SpendRequest)) : SpOut TokenS where
  req := match r with
    | .ok q => .ok q.2
    | .error e => .error e
  fin resp := match r with
    | .ok q => match (finalizeSpend A.pk (some q.1) resp).2 with
      | .ok o => o
      | .error _ => none
    | .error _ => none

/-- Bytes from uniform coins. -/
abbrev vec {n : ℕ} (c : Coins n) : Bytes n := Vector.ofFn c

/-- A real issuance from `(nf, r, ρ)`. -/
def issReal (P : Prim SK) (x : Coins 24 × Coins 16 × Coins 16) : IssOut TokenS :=
  issOutOf A (issueOf P A.tInit A.ctx (vec x.1) (vec x.2.1) (vec x.2.2))

/-- A real spend from `(nf', r', ρ)`. -/
def spReal (P : Prim SK) (x : Coins 24 × Coins 16 × Coins 16) (τ : TokenS) (d : Credits) :
    SpOut TokenS :=
  spOutOf A (spendOf P A.pk (some τ) d A.ctx (vec x.1) (vec x.2.1) (vec x.2.2)).2

/-- **The real game** in world `(b₁, b₂)`. -/
def realGame (P : Prim SK) (b₁ b₂ : Bool) :=
  game A (tokIface A) b₁ b₂ (issReal A P) (issReal A P) (spReal A P) (spReal A P)

variable {CI CS : Type} (simI : IssueInstance → CI → Option IssueProof)
  (simS : SpendInstance → CS → Option SpendProof)

/-- `issueOf` with a simulated proof. -/
def issueSim (tInit : Credits) (ctx : Context) (nf : Nullifier) (r : Opening) (c : CI) :
    Except Error (PendingTokenS × IssueRequest) :=
  if tInit = 0 then .error .invalidArgument else
  match simI ⟨com nf ctx tInit r, tInit, ctx⟩ c with
  | none => .error .runtime
  | some pf => .ok (⟨nf, r, tInit, com nf ctx tInit r⟩, issueReqBytes (com nf ctx tInit r) pf)

/-- `spendOf` with a simulated proof (the Client's checks unchanged). -/
def spendSim (pk : PublicKey) (τ : TokenS) (d : Credits) (ctx : Context) (nf' : Nullifier)
    (r' : Opening) (c : CS) : Except Error (PendingSpendS × SpendRequest) :=
  if ¬ τ.Valid pk ctx then .error .invalidArgument else
  match clientCheck τ.t τ.x d with
  | none => .error .invalidArgument
  | some t' =>
    match simS ⟨pk, τ.nf, d, com nf' ctx t' r', ctx⟩ c with
    | none => .error .runtime
    | some pf => .ok (⟨nf', t', r', com nf' ctx t' r'⟩, SpendReq.toBytes ⟨τ.nf, d, com nf' ctx t' r', pf⟩)

def issSim (x : Coins 24 × Coins 16 × CI) : IssOut TokenS :=
  issOutOf A (issueSim simI A.tInit A.ctx (vec x.1) (vec x.2.1) x.2.2)

def spSim (x : Coins 24 × Coins 16 × CS) (τ : TokenS) (d : Credits) : SpOut TokenS :=
  spOutOf A (spendSim simS A.pk τ d A.ctx (vec x.1) (vec x.2.1) x.2.2)

/-- The issuance prover with uniform `ρ`. -/
def proveI (P : Prim SK) (x : IssueInstance) (w : IssueWitness) (ρ : Coins 16) : Option IssueProof :=
  P.proveIssue x w (vec ρ)

/-- The spend prover with uniform `ρ`. -/
def proveS (P : Prim SK) (x : SpendInstance) (w : SpendWitness) (ρ : Coins 16) : Option SpendProof :=
  P.proveSpend x w (vec ρ)

/-- **One issuance proof (H2).** -/
theorem issue_close [Fintype CI] [Nonempty CI] (P : Prim SK) {εI : ℝ} (hε : 0 ≤ εI)
    (hI : ZeroKnowledge IssueRel (proveI P) simI εI) : IssClose εI (issReal A P) (issSim A simI) := by
  intro f
  refine Close.congr (Close.prod_right (X := fun nf y => let o := issReal A P (nf, y); (o.req, o.fin (f o.req)))
    (Y := fun nf y => let o := issSim A simI (nf, y); (o.req, o.fin (f o.req))) fun nf => Close.congr
      (Close.prod_right (X := fun r ρ => let o := issReal A P (nf, r, ρ); (o.req, o.fin (f o.req)))
        (Y := fun r c => let o := issSim A simI (nf, r, c); (o.req, o.fin (f o.req))) fun r => ?_)
      (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl) (fun _ => rfl)
  by_cases hT : A.tInit = 0
  · simp only [issReal, issSim, issueOf, issueSim, hT, ↓reduceIte]
    exact close_const hε _
  · simp only [issReal, issSim, issueOf, issueSim, hT, ↓reduceIte]
    exact (hI ⟨com (vec nf) A.ctx A.tInit (vec r), A.tInit, A.ctx⟩ ⟨vec nf, vec r⟩ rfl).map
      fun (o : Option IssueProof) =>
        let q := issOutOf A (match o with
          | none => .error .runtime
          | some pf => .ok (⟨vec nf, vec r, A.tInit, com (vec nf) A.ctx A.tInit (vec r)⟩,
              issueReqBytes (com (vec nf) A.ctx A.tInit (vec r)) pf))
        (q.req, q.fin (f q.req))

/-- **One spend proof (H2).** At every token and amount: if the Client's checks fail both sides
throw alike; otherwise the witness satisfies `SpendRel` (V1 is the validity check, V2 holds by
construction, V3 is `clientCheck_eq`). -/
theorem spend_close [Fintype CS] [Nonempty CS] (P : Prim SK) {εS : ℝ} (hε : 0 ≤ εS)
    (hS : ZeroKnowledge SpendRel (proveS P) simS εS) : SpClose εS (spReal A P) (spSim A simS) := by
  intro τ d f
  refine Close.congr (Close.prod_right
    (X := fun nf y => let o := spReal A P (nf, y) τ d; (o.req, o.fin (f o.req)))
    (Y := fun nf y => let o := spSim A simS (nf, y) τ d; (o.req, o.fin (f o.req))) fun nf => Close.congr
      (Close.prod_right (X := fun r ρ => let o := spReal A P (nf, r, ρ) τ d; (o.req, o.fin (f o.req)))
        (Y := fun r c => let o := spSim A simS (nf, r, c) τ d; (o.req, o.fin (f o.req))) fun r => ?_)
      (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl) (fun _ => rfl)
  by_cases hv : τ.Valid A.pk A.ctx
  · cases hc : clientCheck τ.t τ.x d with
    | none =>
      simp only [spReal, spSim, spendOf, spendSim, hv, hc, not_true_eq_false, ↓reduceIte]
      exact close_const hε _
    | some t' =>
      simp only [spReal, spSim, spendOf, spendSim, hv, hc, not_true_eq_false, ↓reduceIte]
      have hrel : SpendRel ⟨A.pk, τ.nf, d, com (vec nf) A.ctx t' (vec r), A.ctx⟩
          ⟨τ.t, τ.r, τ.x, τ.s, vec nf, t', vec r⟩ :=
        ⟨hv, rfl, by have := clientCheck_eq hc; simp only at this ⊢; omega⟩
      let Φr : Option SpendProof → Except Error SpendRequest × Option TokenS := fun o =>
        let q := spOutOf A (match o with
          | none => ((none : Option TokenS),
              (Except.error .runtime : Except Error (PendingSpendS × SpendRequest)))
          | some pf => (none, Except.ok (⟨vec nf, t', vec r, com (vec nf) A.ctx t' (vec r)⟩,
              SpendReq.toBytes ⟨τ.nf, d, com (vec nf) A.ctx t' (vec r), pf⟩))).2
        (q.req, q.fin (f q.req))
      let Φs : Option SpendProof → Except Error SpendRequest × Option TokenS := fun o =>
        let q := spOutOf A (match o with
          | none => .error .runtime
          | some pf => .ok (⟨vec nf, t', vec r, com (vec nf) A.ctx t' (vec r)⟩,
              SpendReq.toBytes ⟨τ.nf, d, com (vec nf) A.ctx t' (vec r), pf⟩))
        (q.req, q.fin (f q.req))
      have hΦ : ∀ o, Φr o = Φs o := by intro o; cases o <;> rfl
      exact Close.congr ((hS _ _ hrel).map Φs) (fun ρ => hΦ (proveS P _ _ ρ)) (fun _ => rfl)
  · simp only [spReal, spSim, spendOf, spendSim, hv, not_false_eq_true, ↓reduceIte]
    exact close_const hε _

/-! ## The public world: tokens without openings -/

section Map

variable {Tok' : Type} (I' : Iface Tok') (π : Tok → Tok')

theorem tokD_map (hd : π I.dflt = I'.dflt) (tk₀ tk₁ : Option Tok) (c : Bool) :
    tokD I' (tk₀.map π) (tk₁.map π) c = π (tokD I tk₀ tk₁ c) := by
  cases c <;> simp [tokD, ← hd, Option.getD_map]

theorem ok₁_map (hd : π I.dflt = I'.dflt) (hok : ∀ τ d, I'.ok (π τ) d = I.ok τ d) (tr : IssTr)
    (tk₀ tk₁ : Option Tok) : ok₁ A I' tr (tk₀.map π) (tk₁.map π) = ok₁ A I tr tk₀ tk₁ := by
  simp [ok₁, tokD_map I I' π hd, hok]

theorem ok₂_map (hd : π I.dflt = I'.dflt) (hok : ∀ τ d, I'.ok (π τ) d = I.ok τ d) (b₁ : Bool)
    (tr : IssTr) (tk₀ tk₁ : Option Tok) (rq : Except Error SpendRequest) (ch : Option Tok) :
    ok₂ A I' b₁ tr (tk₀.map π) (tk₁.map π) rq (ch.map π) = ok₂ A I b₁ tr tk₀ tk₁ rq ch := by
  simp [ok₂, tokD_map I I' π hd, hok, ← hd, Option.getD_map]

theorem cur₂_map (hd : π I.dflt = I'.dflt) (b₁ b₂ : Bool) (tk₀ tk₁ ch : Option Tok) :
    cur₂ I' b₁ b₂ (tk₀.map π) (tk₁.map π) (ch.map π) = π (cur₂ I b₁ b₂ tk₀ tk₁ ch) := by
  unfold cur₂
  cases b₂ == b₁ <;> simp [tokD_map I I' π hd, ← hd, Option.getD_map]

/-- **A token map that commutes with the slots and the refusal test preserves the view.** -/
theorem view_map (hd : π I.dflt = I'.dflt) (hok : ∀ τ d, I'.ok (π τ) d = I.ok τ d)
    (b₁ b₂ : Bool) {i₀ i₁ : IssOut Tok} {i₀' i₁' : IssOut Tok'}
    (hr₀ : i₀'.req = i₀.req) (hf₀ : ∀ s, i₀'.fin s = (i₀.fin s).map π)
    (hr₁ : i₁'.req = i₁.req) (hf₁ : ∀ s, i₁'.fin s = (i₁.fin s).map π)
    {s₁ s₂ : Tok → Credits → SpOut Tok} {s₁' s₂' : Tok' → Credits → SpOut Tok'}
    (hs₁r : ∀ τ d, (s₁' (π τ) d).req = (s₁ τ d).req)
    (hs₁f : ∀ τ d r, (s₁' (π τ) d).fin r = ((s₁ τ d).fin r).map π)
    (hs₂r : ∀ τ d, (s₂' (π τ) d).req = (s₂ τ d).req) :
    view A I' b₁ b₂ i₀' i₁' s₁' s₂' ↔ view A I b₁ b₂ i₀ i₁ s₁ s₂ := by
  unfold view stage₁ stage₂ stage₃
  rw [hr₀, hr₁, hf₀, hf₁, tokD_map I I' π hd, hs₁r, hs₁f, ok₁_map A I I' π hd hok,
    ok₂_map A I I' π hd hok, cur₂_map I I' π hd, hs₂r]

end Map

/-- A token as the Issuer could know it: no opening, and the commitment the Client sent. -/
structure PubTok where
  nf : Nullifier
  t : Credits
  x : Credits
  s : Preimage
  c : Commitment

/-- The public part of a spec token, with its commitment recomputed from the opening. -/
def pubOf (τ : TokenS) : PubTok := ⟨τ.nf, τ.t, τ.x, τ.s, com τ.nf A.ctx τ.t τ.r⟩

/-- The refusal test on public tokens: validity against the commitment sent. -/
def pubIface : Iface PubTok :=
  ⟨fun τ d => decide (uovEval A.pk τ.s = tag τ.c τ.x) && (clientCheck τ.t τ.x d).isSome,
    pubOf A dfltTok⟩

/-- A simulated issuance in the public world, with commitment `cf T_init`. -/
def pubIss (cf : Credits → Commitment) (nf : Nullifier) (c : CI) : IssOut PubTok :=
  if A.tInit = 0 then ⟨.error .invalidArgument, fun _ => none⟩ else
  match simI ⟨cf A.tInit, A.tInit, A.ctx⟩ c with
  | none => ⟨.error .runtime, fun _ => none⟩
  | some pf => ⟨.ok (issueReqBytes (cf A.tInit) pf), fun s =>
      if uovEval A.pk s = tag (cf A.tInit) 0 then some ⟨nf, A.tInit, 0, s, cf A.tInit⟩ else none⟩

/-- A simulated spend in the public world, with new commitment `cf t'`. -/
def pubSp (cf : Credits → Commitment) (nf' : Nullifier) (c : CS) (τ : PubTok) (d : Credits) :
    SpOut PubTok :=
  if ¬ uovEval A.pk τ.s = tag τ.c τ.x then ⟨.error .invalidArgument, fun _ => none⟩ else
  match clientCheck τ.t τ.x d with
  | none => ⟨.error .invalidArgument, fun _ => none⟩
  | some t' =>
    match simS ⟨A.pk, τ.nf, d, cf t', A.ctx⟩ c with
    | none => ⟨.error .runtime, fun _ => none⟩
    | some pf => ⟨.ok (SpendReq.toBytes ⟨τ.nf, d, cf t', pf⟩), fun resp =>
        if uovEval A.pk (respSig resp) = tag (cf t') (respRefund resp) then
          some ⟨nf', t', respRefund resp, respSig resp, cf t'⟩ else none⟩

/-- The commitment function of an honest Client: `t ↦ Com(nf, ctx, t, r)`. -/
def comFn (nf : Nullifier) (r : Opening) (t : Credits) : Commitment := com nf A.ctx t r

theorem tokIface_ok (τ : TokenS) (d : Credits) :
    (pubIface A).ok (pubOf A τ) d = (tokIface A).ok τ d := rfl

theorem issSim_pub (x : Coins 24 × Coins 16 × CI) :
    (pubIss A simI (comFn A (vec x.1) (vec x.2.1)) (vec x.1) x.2.2).req = (issSim A simI x).req ∧
      ∀ s, (pubIss A simI (comFn A (vec x.1) (vec x.2.1)) (vec x.1) x.2.2).fin s =
        ((issSim A simI x).fin s).map (pubOf A) := by
  unfold pubIss issSim issueSim issOutOf comFn
  by_cases hT : A.tInit = 0
  · simp [hT]
  · simp only [hT, ↓reduceIte]
    cases simI ⟨com (vec x.1) A.ctx A.tInit (vec x.2.1), A.tInit, A.ctx⟩ x.2.2 with
    | none => simp
    | some pf =>
      refine ⟨rfl, fun s => ?_⟩
      simp only [finalizeIssue]
      split_ifs <;> rfl

theorem spSim_pub (x : Coins 24 × Coins 16 × CS) (τ : TokenS) (d : Credits) :
    (pubSp A simS (comFn A (vec x.1) (vec x.2.1)) (vec x.1) x.2.2 (pubOf A τ) d).req =
        (spSim A simS x τ d).req ∧
      ∀ r, (pubSp A simS (comFn A (vec x.1) (vec x.2.1)) (vec x.1) x.2.2 (pubOf A τ) d).fin r =
        ((spSim A simS x τ d).fin r).map (pubOf A) := by
  unfold pubSp spSim spendSim spOutOf comFn
  by_cases hv : τ.Valid A.pk A.ctx
  · have hv' : uovEval A.pk (pubOf A τ).s = tag (pubOf A τ).c (pubOf A τ).x := hv
    simp only [hv, hv', not_true_eq_false, ↓reduceIte]
    cases hc : clientCheck τ.t τ.x d with
    | none => simp [pubOf, hc]
    | some t' =>
      simp only [pubOf, hc]
      cases simS ⟨A.pk, τ.nf, d, com (vec x.1) A.ctx t' (vec x.2.1), A.ctx⟩ x.2.2 with
      | none => simp
      | some pf =>
        refine ⟨rfl, fun r => ?_⟩
        simp only [finalizeSpend]
        split_ifs <;> rfl
  · have hv' : ¬ uovEval A.pk (pubOf A τ).s = tag (pubOf A τ).c (pubOf A τ).x := hv
    simp [hv, hv']

/-! ## From the simulated spec world to the public world -/

/-- The game with all four proofs simulated. -/
def simGame (b₁ b₂ : Bool) :=
  game A (tokIface A) b₁ b₂ (issSim A simI) (issSim A simI) (spSim A simS) (spSim A simS)

/-- Four of a kind: the two issuance slots and the two spend slots. -/
abbrev Quad (α : Type) := (α × α) × (α × α)

/-- **The public world**, from the nullifiers `n`, the commitment functions `cf` and the simulator
coins `co` of the four slots. This is what the hiding reduction runs. -/
def pubView (b₁ b₂ : Bool) (n : Quad Nullifier) (cf : Quad (Credits → Commitment))
    (co : (CI × CI) × (CS × CS)) : Prop :=
  view A (pubIface A) b₁ b₂ (pubIss A simI cf.1.1 n.1.1 co.1.1) (pubIss A simI cf.1.2 n.1.2 co.1.2)
    (pubSp A simS cf.2.1 n.2.1 co.2.1) (pubSp A simS cf.2.2 n.2.2 co.2.2)

/-- The simulated spec world's tape. -/
abbrev SimTape (CI CS : Type) :=
  ((Coins 24 × Coins 16 × CI) × (Coins 24 × Coins 16 × CI)) ×
    ((Coins 24 × Coins 16 × CS) × (Coins 24 × Coins 16 × CS))

/-- **After H2 the openings enter nothing but `Com`**: the simulated spec world is the public world
with the honest commitment functions. -/
theorem simGame_iff (b₁ b₂ : Bool) (x : SimTape CI CS) :
    simGame A simI simS b₁ b₂ x ↔
      pubView A simI simS b₁ b₂ ((vec x.1.1.1, vec x.1.2.1), (vec x.2.1.1, vec x.2.2.1))
        ((comFn A (vec x.1.1.1) (vec x.1.1.2.1), comFn A (vec x.1.2.1) (vec x.1.2.2.1)),
          (comFn A (vec x.2.1.1) (vec x.2.1.2.1), comFn A (vec x.2.2.1) (vec x.2.2.2.1)))
        ((x.1.1.2.2, x.1.2.2.2), (x.2.1.2.2, x.2.2.2.2)) :=
  (view_map A (tokIface A) (pubIface A) (pubOf A) rfl (tokIface_ok A) b₁ b₂
    (issSim_pub A simI x.1.1).1 (issSim_pub A simI x.1.1).2
    (issSim_pub A simI x.1.2).1 (issSim_pub A simI x.1.2).2
    (fun τ d => (spSim_pub A simS x.2.1 τ d).1) (fun τ d => (spSim_pub A simS x.2.1 τ d).2)
    (fun τ d => (spSim_pub A simS x.2.2 τ d).1)).symm

/-! ## H3: the hiding hop -/

/-- The hiding experiment's tape: `(nf, r)` for each of the four honest commitments. -/
abbrev HTape := Quad (Coins 24 × Coins 16)

/-- The ideal tape: `(nf, u)`, `u` a uniform commitment. -/
abbrev UTape := Quad (Coins 24 × Coins 32)

/-- Real: the nullifiers and the honest commitment functions `t ↦ Com(nf, ctx, t, r)`. -/
def hideReal (ctx : Context) (x : HTape) : Quad Nullifier × Quad (Credits → Commitment) :=
  (((vec x.1.1.1, vec x.1.2.1), (vec x.2.1.1, vec x.2.2.1)),
    ((fun t => com (vec x.1.1.1) ctx t (vec x.1.1.2), fun t => com (vec x.1.2.1) ctx t (vec x.1.2.2)),
      (fun t => com (vec x.2.1.1) ctx t (vec x.2.1.2), fun t => com (vec x.2.2.1) ctx t (vec x.2.2.2))))

/-- Ideal: the nullifiers and constant uniform commitments. -/
def hideIdeal (x : UTape) : Quad Nullifier × Quad (Credits → Commitment) :=
  (((vec x.1.1.1, vec x.1.2.1), (vec x.2.1.1, vec x.2.2.1)),
    ((fun _ => vec x.1.1.2, fun _ => vec x.1.2.2), (fun _ => vec x.2.1.2, fun _ => vec x.2.2.2)))

/-- **The hiding advantage** of `D` (`security/ratatouille.md` §2.2, `ε_hide^K`): four commitments
with uniform openings, each evaluated at a credit value of the distinguisher's choice, and their
nullifiers, against independent uniform strings. -/
noncomputable def hidingAdv (ctx : Context) (D : Quad Nullifier → Quad (Credits → Commitment) → Prop) :
    ℝ :=
  |pr HTape (fun x => D (hideReal ctx x).1 (hideReal ctx x).2) -
    pr UTape (fun x => D (hideIdeal x).1 (hideIdeal x).2)|

/-- **The reduction to hiding**: the Issuer with the simulator coins `co` fixed, in the public
world. It evaluates each commitment function once, at the credit value of that commitment. -/
def reduction (b₁ b₂ : Bool) (co : (CI × CI) × (CS × CS)) (n : Quad Nullifier)
    (cf : Quad (Credits → Commitment)) : Prop :=
  pubView A simI simS b₁ b₂ n cf co

/-- The ideal world: uniform commitments. -/
def idealGame (b₁ b₂ : Bool) (y : UTape × ((CI × CI) × (CS × CS))) : Prop :=
  reduction A simI simS b₁ b₂ y.2 (hideIdeal y.1).1 (hideIdeal y.1).2

/-- Regroup the simulated tape as the hiding tape and the simulator coins. -/
def regroup : SimTape CI CS ≃ HTape × ((CI × CI) × (CS × CS)) where
  toFun x := ((((x.1.1.1, x.1.1.2.1), (x.1.2.1, x.1.2.2.1)), ((x.2.1.1, x.2.1.2.1), (x.2.2.1, x.2.2.2.1))),
    ((x.1.1.2.2, x.1.2.2.2), (x.2.1.2.2, x.2.2.2.2)))
  invFun y := (((y.1.1.1.1, y.1.1.1.2, y.2.1.1), (y.1.1.2.1, y.1.1.2.2, y.2.1.2)),
    ((y.1.2.1.1, y.1.2.1.2, y.2.2.1), (y.1.2.2.1, y.1.2.2.2, y.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

theorem hiding_hop [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS] (b₁ b₂ : Bool)
    {εhide : ℝ} (hhide : ∀ co, hidingAdv A.ctx (reduction A simI simS b₁ b₂ co) ≤ εhide) :
    |pr _ (simGame A simI simS b₁ b₂) - pr _ (idealGame A simI simS b₁ b₂)| ≤ εhide := by
  rw [← pr_equiv regroup.symm (simGame A simI simS b₁ b₂),
    pr_congr fun y => simGame_iff A simI simS b₁ b₂ (regroup.symm y)]
  exact abs_pr_prod_sub_le' _ _ fun co => hhide co

/-! ## The ideal world: the four worlds coincide -/

/-- A simulated spend request revealing `n`, with new commitment `u`. -/
def reqS (n : Nullifier) (d : Credits) (u : Commitment) (c : CS) : Except Error SpendRequest :=
  match simS ⟨A.pk, n, d, u, A.ctx⟩ c with
  | none => .error .runtime
  | some pf => .ok (SpendReq.toBytes ⟨n, d, u, pf⟩)

/-- The all-zero nullifier, where the ideal view needs none. -/
def nf0 : Nullifier := Vector.ofFn fun _ => 0

/-- **The ideal view**, as a function of the nullifier `X` revealed in round 1 and `Y` revealed in
round 2: no other nullifier, and neither `b₁` nor `b₂`, appears. -/
def idealW (X Y : Nullifier) (u₀ u₁ u₂ u₃ : Commitment) (co : (CI × CI) × (CS × CS)) : Prop :=
  let i₀ := pubIss A simI (fun _ => u₀) nf0 co.1.1
  let i₁ := pubIss A simI (fun _ => u₁) nf0 co.1.2
  let tr : IssTr := (i₀.req, i₁.req)
  let d₁ := A.d₁ tr
  let ok₁ := (i₀.fin (A.respondIss tr false)).isSome && (i₁.fin (A.respondIss tr true)).isSome &&
    (clientCheck A.tInit 0 d₁).isSome
  let rq := reqS A simS X d₁ u₂ co.2.1
  let resp := A.respond₁ tr rq
  let d₂ := A.d₂ tr rq
  let ok₂ := (simS ⟨A.pk, X, d₁, u₂, A.ctx⟩ co.2.1).isSome &&
    decide (uovEval A.pk (respSig resp) = tag u₂ (respRefund resp)) &&
    (clientCheck ((clientCheck A.tInit 0 d₁).getD 0) (respRefund resp) d₂).isSome &&
    (clientCheck A.tInit 0 d₂).isSome
  A.guess tr (bif ok₁ then some (rq, bif ok₂ then some (reqS A simS Y d₂ u₃ co.2.2) else none)
    else none)

theorem pubIss_req (cf : Credits → Commitment) (n n' : Nullifier) (c : CI) :
    (pubIss A simI cf n c).req = (pubIss A simI cf n' c).req := by
  unfold pubIss
  split_ifs
  · rfl
  · split <;> rfl

theorem pubIss_fin (cf : Credits → Commitment) (n n' : Nullifier) (c : CI) (s : Preimage) :
    (pubIss A simI cf n c).fin s = if ((pubIss A simI cf n' c).fin s).isSome then
      some ⟨n, A.tInit, 0, s, cf A.tInit⟩ else none := by
  unfold pubIss
  by_cases hT : A.tInit = 0
  · simp [hT]
  · simp only [hT, ↓reduceIte]
    cases simI ⟨cf A.tInit, A.tInit, A.ctx⟩ c with
    | none => simp
    | some pf => by_cases hv : uovEval A.pk s = tag (cf A.tInit) 0 <;> simp [hv]

/-- An issued token's signature is valid for the commitment sent. -/
theorem valid_issued (cf : Credits → Commitment) (n : Nullifier) (c : CI) (s : Preimage)
    (h : ((pubIss A simI cf n c).fin s).isSome = true) : uovEval A.pk s = tag (cf A.tInit) 0 := by
  unfold pubIss at h
  by_cases hT : A.tInit = 0
  · simp [hT] at h
  · simp only [hT, ↓reduceIte] at h
    cases hs : simI ⟨cf A.tInit, A.tInit, A.ctx⟩ c with
    | none => simp [hs] at h
    | some pf =>
      simp only [hs] at h
      by_cases hv : uovEval A.pk s = tag (cf A.tInit) 0
      · exact hv
      · simp [hv] at h

/-- At a token that passes the refusal test, a public spend with a constant commitment `u` reveals
only the token's nullifier; its change token holds the Client's new balance. -/
theorem pubSp_ok (u : Commitment) (n : Nullifier) (c : CS) (τ : PubTok) (d : Credits)
    (h : (pubIface A).ok τ d = true) :
    (pubSp A simS (fun _ => u) n c τ d).req = reqS A simS τ.nf d u c ∧
      ∀ r, (pubSp A simS (fun _ => u) n c τ d).fin r =
        if (simS ⟨A.pk, τ.nf, d, u, A.ctx⟩ c).isSome &&
            decide (uovEval A.pk (respSig r) = tag u (respRefund r)) then
          some ⟨n, (clientCheck τ.t τ.x d).getD 0, respRefund r, respSig r, u⟩ else none := by
  simp only [pubIface, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hv, hc⟩ := h
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.1 hc
  unfold pubSp reqS
  simp only [hv, not_true_eq_false, ↓reduceIte, ht', Option.getD_some]
  cases simS ⟨A.pk, τ.nf, d, u, A.ctx⟩ c with
  | none => simp
  | some pf =>
    refine ⟨rfl, fun r => ?_⟩
    by_cases hr : uovEval A.pk (respSig r) = tag u (respRefund r) <;> simp [hr]

/-- The issued tokens as the ideal world builds them. -/
def issTok (e : Bool) (N : Nullifier) (S : Preimage) (U : Commitment) : Option PubTok :=
  if e then some ⟨N, A.tInit, 0, S, U⟩ else none

theorem tokD_issTok (N₀ N₁ : Nullifier) (S₀ S₁ : Preimage) (U₀ U₁ : Commitment) (c : Bool) :
    tokD (pubIface A) (issTok A true N₀ S₀ U₀) (issTok A true N₁ S₁ U₁) c =
      ⟨bif c then N₁ else N₀, A.tInit, 0, bif c then S₁ else S₀, bif c then U₁ else U₀⟩ := by
  cases c <;> rfl

/-- **The stages of the ideal world**: with valid issued tokens and constant commitments, the view
reveals the spent tokens' nullifiers and nothing else about the tokens. -/
theorem stage_ideal (b₁ b₂ : Bool) (tr : IssTr) (e₀ e₁ : Bool) (N₀ N₁ : Nullifier) (S₀ S₁ : Preimage)
    (U₀ U₁ : Commitment) (hv₀ : e₀ = true → uovEval A.pk S₀ = tag U₀ 0)
    (hv₁ : e₁ = true → uovEval A.pk S₁ = tag U₁ 0) (m₁ m₂ : Nullifier) (v₁ v₂ : Commitment)
    (c₁ c₂ : CS) :
    stage₁ A (pubIface A) b₁ b₂ tr (issTok A e₀ N₀ S₀ U₀) (issTok A e₁ N₁ S₁ U₁)
        (pubSp A simS (fun _ => v₁) m₁ c₁) (pubSp A simS (fun _ => v₂) m₂ c₂) ↔
      let X := bif b₁ then N₁ else N₀
      let Y := bif b₂ == b₁ then m₁ else bif b₁ then N₀ else N₁
      let d₁ := A.d₁ tr
      let rq := reqS A simS X d₁ v₁ c₁
      let resp := A.respond₁ tr rq
      let d₂ := A.d₂ tr rq
      let ok₂ := (simS ⟨A.pk, X, d₁, v₁, A.ctx⟩ c₁).isSome &&
        decide (uovEval A.pk (respSig resp) = tag v₁ (respRefund resp)) &&
        (clientCheck ((clientCheck A.tInit 0 d₁).getD 0) (respRefund resp) d₂).isSome &&
        (clientCheck A.tInit 0 d₂).isSome
      A.guess tr (bif e₀ && e₁ && (clientCheck A.tInit 0 d₁).isSome then
        some (rq, bif ok₂ then some (reqS A simS Y d₂ v₂ c₂) else none) else none) := by
  unfold stage₁ stage₂ stage₃
  cases e₀
  · simp [ok₁, issTok]
  cases e₁
  · simp [ok₁, issTok]
  have hv₀ := hv₀ rfl
  have hv₁ := hv₁ rfl
  have hok (c : Bool) (d : Credits) :
      (pubIface A).ok (tokD (pubIface A) (issTok A true N₀ S₀ U₀) (issTok A true N₁ S₁ U₁) c) d =
        (clientCheck A.tInit 0 d).isSome := by
    rw [tokD_issTok]
    cases c <;> simp [pubIface, hv₀, hv₁]
  have hok₁ : ok₁ A (pubIface A) tr (issTok A true N₀ S₀ U₀) (issTok A true N₁ S₁ U₁) =
      (clientCheck A.tInit 0 (A.d₁ tr)).isSome := by
    unfold ok₁
    rw [hok, hok]
    simp [issTok]
  simp only [hok₁, Bool.true_and]
  cases hc₁ : (clientCheck A.tInit 0 (A.d₁ tr)).isSome
  · rfl
  obtain ⟨hreq, hfin⟩ := pubSp_ok A simS v₁ m₁ c₁ _ (A.d₁ tr) ((hok b₁ _).trans hc₁)
  rw [hreq, hfin]
  simp only [tokD_issTok]
  generalize reqS A simS (bif b₁ then N₁ else N₀) (A.d₁ tr) v₁ c₁ = rq
  cases hC : ((simS ⟨A.pk, bif b₁ then N₁ else N₀, A.d₁ tr, v₁, A.ctx⟩ c₁).isSome &&
      decide (uovEval A.pk (respSig (A.respond₁ tr rq)) = tag v₁ (respRefund (A.respond₁ tr rq))))
  · simp [ok₂]
  have hsig : uovEval A.pk (respSig (A.respond₁ tr rq)) = tag v₁ (respRefund (A.respond₁ tr rq)) := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hC
    exact hC.2
  simp only [↓reduceIte]
  have hok₂ : ok₂ A (pubIface A) b₁ tr (issTok A true N₀ S₀ U₀) (issTok A true N₁ S₁ U₁) rq
      (some ⟨m₁, (clientCheck A.tInit 0 (A.d₁ tr)).getD 0, respRefund (A.respond₁ tr rq),
        respSig (A.respond₁ tr rq), v₁⟩) =
      ((clientCheck ((clientCheck A.tInit 0 (A.d₁ tr)).getD 0) (respRefund (A.respond₁ tr rq))
        (A.d₂ tr rq)).isSome && (clientCheck A.tInit 0 (A.d₂ tr rq)).isSome) := by
    unfold ok₂
    rw [hok]
    simp [pubIface, hsig]
  rw [hok₂]
  simp only [Bool.true_and]
  cases hO : ((clientCheck ((clientCheck A.tInit 0 (A.d₁ tr)).getD 0) (respRefund (A.respond₁ tr rq))
      (A.d₂ tr rq)).isSome && (clientCheck A.tInit 0 (A.d₂ tr rq)).isSome)
  · rfl
  simp only [Bool.and_eq_true] at hO
  obtain ⟨hO₁, hO₂⟩ := hO
  have hcur : (pubIface A).ok (cur₂ (pubIface A) b₁ b₂ (issTok A true N₀ S₀ U₀) (issTok A true N₁ S₁ U₁)
      (some ⟨m₁, (clientCheck A.tInit 0 (A.d₁ tr)).getD 0, respRefund (A.respond₁ tr rq),
        respSig (A.respond₁ tr rq), v₁⟩)) (A.d₂ tr rq) = true := by
    unfold cur₂
    cases b₂ == b₁
    · rw [Bool.cond_false, hok]; exact hO₂
    · simp [pubIface, hsig, hO₁]
  rw [(pubSp_ok A simS v₂ m₂ c₂ _ _ hcur).1]
  unfold cur₂
  cases b₂ == b₁
  · simp only [Bool.cond_false, tokD_issTok]
    cases b₁ <;> rfl
  · rfl

theorem idealGame_iff (b₁ b₂ : Bool) (y : UTape × ((CI × CI) × (CS × CS))) :
    idealGame A simI simS b₁ b₂ y ↔
      idealW A simI simS (bif b₁ then vec y.1.1.2.1 else vec y.1.1.1.1)
        (bif b₂ == b₁ then vec y.1.2.1.1 else bif b₁ then vec y.1.1.1.1 else vec y.1.1.2.1)
        (vec y.1.1.1.2) (vec y.1.1.2.2) (vec y.1.2.1.2) (vec y.1.2.2.2) y.2 := by
  obtain ⟨⟨⟨⟨n₀, u₀⟩, ⟨n₁, u₁⟩⟩, ⟨⟨m₁, v₁⟩, ⟨m₂, v₂⟩⟩⟩, co⟩ := y
  simp only [idealGame, reduction, pubView, hideIdeal, view]
  rw [pubIss_req A simI _ (vec n₀) nf0, pubIss_req A simI _ (vec n₁) nf0,
    pubIss_fin A simI _ (vec n₀) nf0, pubIss_fin A simI _ (vec n₁) nf0]
  exact stage_ideal A simS b₁ b₂ _ _ _ _ _ _ _ _ _ (valid_issued A simI _ _ _ _)
    (valid_issued A simI _ _ _ _) _ _ _ _ _ _

/-- Permute the nullifiers of the first three slots (`nf₀`, `nf₁`, `nf'₁`) by `e`. -/
def permN (e : (Coins 24 × Coins 24 × Coins 24) ≃ (Coins 24 × Coins 24 × Coins 24)) :
    UTape × ((CI × CI) × (CS × CS)) ≃ UTape × ((CI × CI) × (CS × CS)) where
  toFun y :=
    let z := e (y.1.1.1.1, y.1.1.2.1, y.1.2.1.1)
    ((((z.1, y.1.1.1.2), (z.2.1, y.1.1.2.2)), ((z.2.2, y.1.2.1.2), y.1.2.2)), y.2)
  invFun y :=
    let z := e.symm (y.1.1.1.1, y.1.1.2.1, y.1.2.1.1)
    ((((z.1, y.1.1.1.2), (z.2.1, y.1.1.2.2)), ((z.2.2, y.1.2.1.2), y.1.2.2)), y.2)
  left_inv y := by simp
  right_inv y := by simp

/-- **In the ideal world the four worlds coincide**: each world reveals two of the three
nullifiers `nf₀`, `nf₁`, `nf'₁`, none of which appears anywhere else, and a permutation of them
maps one world to another. -/
theorem idealGame_eq [Fintype CI] [Fintype CS] (b₁ b₂ : Bool) :
    pr _ (idealGame A simI simS b₁ b₂) = pr _ (idealGame A simI simS false false) := by
  rw [pr_congr (idealGame_iff A simI simS b₁ b₂), pr_congr (idealGame_iff A simI simS false false)]
  cases b₁ <;> cases b₂ <;>
    simp only [Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.not_false, Bool.cond_true,
      Bool.cond_false]
  · -- `(false, true)` reveals `(nf₀, nf₁)`: exchange `nf₁` and `nf'₁`.
    rw [← pr_equiv (permN (⟨fun z => (z.1, z.2.2, z.2.1), fun z => (z.1, z.2.2, z.2.1),
      fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
      (fun y => idealW A simI simS (vec y.1.1.1.1) (vec y.1.2.1.1) (vec y.1.1.1.2) (vec y.1.1.2.2)
        (vec y.1.2.1.2) (vec y.1.2.2.2) y.2)]
    exact pr_congr fun _ => Iff.rfl
  · -- `(true, false)` reveals `(nf₁, nf₀)`: the three-cycle.
    rw [← pr_equiv (permN (⟨fun z => (z.2.1, z.2.2, z.1), fun z => (z.2.2, z.1, z.2.1),
      fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
      (fun y => idealW A simI simS (vec y.1.1.1.1) (vec y.1.2.1.1) (vec y.1.1.1.2) (vec y.1.1.2.2)
        (vec y.1.2.1.2) (vec y.1.2.2.2) y.2)]
    exact pr_congr fun _ => Iff.rfl
  · -- `(true, true)` reveals `(nf₁, nf'₁)`: exchange `nf₀` and `nf₁`.
    rw [← pr_equiv (permN (⟨fun z => (z.2.1, z.1, z.2.2), fun z => (z.2.1, z.1, z.2.2),
      fun _ => rfl, fun _ => rfl⟩ : (Coins 24 × Coins 24 × Coins 24) ≃ _))
      (fun y => idealW A simI simS (vec y.1.1.1.1) (vec y.1.2.1.1) (vec y.1.1.1.2) (vec y.1.1.2.2)
        (vec y.1.2.1.2) (vec y.1.2.2.2) y.2)]
    exact pr_congr fun _ => Iff.rfl

/-! ## Unlinkability -/

/-- **Theorem 2 (unlinkability), from uniform seed expansions.** If the issuance and spend proofs are
`εI`- and `εS`-zero-knowledge (the label-row fix; not on `main`, see above) and the reduction to
hiding has advantage at most `εhide`, then for every malicious Issuer the acceptance
probabilities of any two worlds `(b₁, b₂)`, `(b₁', b₂')` differ by at most
`4εI + 4εS + 2εhide`: neither which Client spends in round 1 (spend–issuance linking) nor whether
round 2's spender is round 1's (spend–spend linking, through the change token) is
distinguishable. -/
theorem unlinkability [Fintype CI] [Nonempty CI] [Fintype CS] [Nonempty CS] (P : Prim SK)
    {εI εS εhide : ℝ} (hεI : 0 ≤ εI) (hεS : 0 ≤ εS)
    (hI : ZeroKnowledge IssueRel (proveI P) simI εI)
    (hS : ZeroKnowledge SpendRel (proveS P) simS εS)
    (hhide : ∀ b₁ b₂ co, hidingAdv A.ctx (reduction A simI simS b₁ b₂ co) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGame A P b₁ b₂) - pr _ (realGame A P b₁' b₂')| ≤ 4 * εI + 4 * εS + 2 * εhide := by
  have hiss := issue_close A simI P hεI hI
  have hsp := spend_close A simS P hεS hS
  have hw (b₁ b₂ : Bool) :
      |pr _ (realGame A P b₁ b₂) - pr _ (idealGame A simI simS b₁ b₂)| ≤ 2 * εI + 2 * εS + εhide := by
    set p0 := pr _ (realGame A P b₁ b₂)
    set p1 := pr _ (game A (tokIface A) b₁ b₂ (issSim A simI) (issReal A P) (spReal A P) (spReal A P))
    set p2 := pr _ (game A (tokIface A) b₁ b₂ (issSim A simI) (issSim A simI) (spReal A P) (spReal A P))
    set p3 := pr _ (game A (tokIface A) b₁ b₂ (issSim A simI) (issSim A simI) (spSim A simS)
      (spReal A P))
    set p4 := pr _ (simGame A simI simS b₁ b₂)
    set p5 := pr _ (idealGame A simI simS b₁ b₂)
    have h1 : |p0 - p1| ≤ εI :=
      game_hop₀ A (tokIface A) b₁ b₂ (issReal A P) (spReal A P) (spReal A P) hiss
    have h2 : |p1 - p2| ≤ εI :=
      game_hop₁ A (tokIface A) b₁ b₂ (issSim A simI) (spReal A P) (spReal A P) hiss
    have h3 : |p2 - p3| ≤ εS :=
      game_hop₂ A (tokIface A) b₁ b₂ (issSim A simI) (issSim A simI) (spReal A P) hsp
    have h4 : |p3 - p4| ≤ εS :=
      game_hop₃ A (tokIface A) b₁ b₂ (issSim A simI) (issSim A simI) (spSim A simS) hsp
    have h5 : |p4 - p5| ≤ εhide := hiding_hop A simI simS b₁ b₂ (hhide b₁ b₂)
    have := abs_sub_le p0 p1 p5
    have := abs_sub_le p1 p2 p5
    have := abs_sub_le p2 p3 p5
    have := abs_sub_le p3 p4 p5
    linarith
  have h := hw b₁ b₂
  have h' := hw b₁' b₂'
  rw [idealGame_eq] at h h'
  have := abs_sub_le (pr _ (realGame A P b₁ b₂)) (pr _ (idealGame A simI simS false false))
    (pr _ (realGame A P b₁' b₂'))
  rw [abs_sub_comm (pr _ (idealGame A simI simS false false))] at this
  linarith

end VoleMole.Privacy.Ratatouille
