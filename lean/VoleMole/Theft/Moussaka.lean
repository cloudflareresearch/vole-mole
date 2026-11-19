import VoleMole.Theft.Basic
import VoleMole.Privacy.Moussaka

/-!
# Moussaka: redemption non-malleability (`security/moussaka.md` §5.3, Theorem 3)

**The game NM** (one honest token). An honest Client with secret coins `ω = (nf, r)` runs the
executable spec (`Spec/Moussaka.lean`): it requests a token for the contexts `ctx_iss`, `ctx_red`
(`issueRequest`, with the seed expansion's output given), finalizes the response against the
Anchor key `pk` (`finalizeIssue`), and redeems it under the Anchor Set `S` and challenge digest
`cd` the adversary chooses (`main`'s `redeem_request`: the Client finds its issuer's index in `S`
itself, `findIssuer`). The adversary (`Thief`) is the Moderator and every Anchor: it chooses the
contexts, `pk`, the response, `S` and `cd`, from the messages it sees (not from the tables). It then
reads the tables and outputs an operation (`MOp`): a redemption request with its own Anchor Set,
contexts and digest (`finalize_redeem`'s arguments), or an issuance request with its own `ctx_iss`.

**The event** (`Bad`): the operation is accepted (`AccOp`: the request has the length the API
checks and the verifier accepts), its statement differs from the honest statement of the same
relation (`FreshOp`; a verbatim replay is left to the nullifier store), and the extracted witness
is not a witness or **opens the honest commitment** `t = Com(nf, ctx_iss, ctx_red, r)`
(`OpensOp`: the redemption's `Com(nf*, ctx_iss*, ctx_red*, r*)`, the issuance's opening). Off this
event no honest token is redirected (`not_redirect`): an accepted redemption whose statement
differs from the honest one (another digest, Anchor Set or context), even with the honest `nf`, has
an extracted commitment `≠ t` that some Anchor of its set signed, a different token (F2's
squatting at most).

**`noRedirect`**:

    Pr[Bad] ≤ ε_I + ε_R + δ_R + ε_SE + Adv^ow(inverter),

with `ε_I`, `ε_R` zero knowledge of the two proof systems (`ZeroKnowledgeRO` for `IssueRelW`,
`RedeemRelW`, at the hops' distinguishers), `δ_R` the real redemption proof reading the tables
differently after the simulated issuance's programming, `ε_SE` weak simulation-extractability
(`WeakSE2`, **a hypothesis**, L8 on paper), and `Adv^ow` the explicit inverter's chance of finding
an opening of `t` from `nf` and `t` alone (`owAdv`). The note's
`ε_dig + Adv^bind + K·Adv^ct-uf-open + U·Adv^ow-r` is not needed for this event: an opening of
`t`, equal to the Client's or not, is what the inverter outputs (`docs/security/moussaka.md` §5.3).
-/

open Finset

namespace VoleMole.Theft.Moussaka

open VoleMole.Privacy VoleMole.Privacy.Moussaka VoleMole.Spec VoleMole.Spec.Moussaka

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

variable {G S : Type}

/-- The honest Client's coins `(nf, r)`. -/
abbrev Sec := Coins nfBytes × Coins rBytes

/-- An operation the adversary submits: an issuance request under its `ctx_iss`, or a
redemption request with its Anchor Set, contexts and challenge digest. -/
inductive MOp
  | issue (req ctxIss : Bytes)
  | redeem (anchors : AnchorSet) (req ctxIss ctxRed cd : Bytes)

/-- **The adversary**: the Moderator and every Anchor. -/
structure Thief (G S : Type) where
  ctxIss : Coins ctxBytes
  ctxRed : Coins ctxBytes
  pk : UOVKey
  respond : Bytes → Coins uovN
  choose : Bytes → AnchorSet × Bytes
  out : Bytes → Except Error Bytes → G → G → S → MOp

variable (A : Thief G S)

def Thief.ci : Bytes := List.ofFn A.ctxIss
def Thief.cr : Bytes := List.ofFn A.ctxRed

/-! ## The Client, in public form (the nullifier `nf` and the commitment `t`) -/

/-- The issuance request from the proof. -/
def reqI (t : Bytes) (π : Option Bytes) : Bytes := t ++ π.getD []

/-- The Client's signature on its token, from the issuance request. -/
def sig (req : Bytes) : Bytes := List.ofFn (A.respond req)

/-- **The redemption statement**, if the Client redeems: its token finalized (`P(s) = t`) and some
key of `S` verifies it (`find_issuer`). -/
def xR (nf t req : Bytes) : Option RedeemInstance :=
  if A.pk.eval (sig A req) = t then
    match findIssuer (A.choose req).1 t (sig A req) with
    | none => none
    | some _ => some ⟨(A.choose req).1.keys, nf, A.ci, A.cr, (A.choose req).2⟩
  else none

/-- **The redemption request** from the proof (an error if the Client does not redeem). -/
def reqR (nf t req : Bytes) (π : Option Bytes) : Except Error Bytes :=
  if A.pk.eval (sig A req) = t then
    match findIssuer (A.choose req).1 t (sig A req) with
    | none => .error .invalidToken
    | some _ => .ok (nf ++ π.getD [])
  else .error .invalidToken

/-! ## The Client, from the spec -/

/-- The commitment of the coins. -/
def tOf (ω : Sec) : Bytes := com (List.ofFn ω.1) A.ci A.cr (List.ofFn ω.2)

/-- A prover with the tables fixed, as the spec's `NIZK`. -/
def nizkG {I : Type} (P : Bytes → I → Bytes → G → S → Bytes) (g : G) (s : S) : NIZK I :=
  ⟨fun w x rho => P w x rho g s, fun _ _ => true⟩

/-- `redeem_request_with_seed` of `main` (`redeemRequest`) with `ρ_red` given. -/
def redeemOf (PR : NIZK RedeemInstance) (tok : Token) (S' : AnchorSet) (ci cr cd rho : Bytes) :
    Except Error Bytes :=
  match findIssuer S' (com tok.nf ci cr tok.r) tok.s with
  | none => .error .invalidToken
  | some i =>
    .ok (tok.nf ++ PR.prove (encodeRedeemWitness tok.nf ci cr tok.r tok.s i)
      ⟨S'.keys, tok.nf, ci, cr, cd⟩ rho)

theorem redeemRequest_eq (PR : NIZK RedeemInstance) (tok : Token) (S' : AnchorSet)
    (ci cr cd seed : Bytes) :
    redeemRequest PR tok S' ci cr cd seed = redeemOf PR tok S' ci cr cd (expandRedeemSeed seed) :=
  rfl

variable (PI : Bytes → IssueInstance → Bytes → G → S → Bytes)
  (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)

/-- **The real issuance request**: `issue_request` at `(nf, r, ρ)`, the prover on the tables. -/
def specI (ω : Sec) (ρ : Coins proveSeedBytes) (g : G) (s : S) : Bytes :=
  (issueRequestOf (nizkG PI g s) A.ci A.cr (List.ofFn ω.1) (List.ofFn ω.2) (List.ofFn ρ)).2

/-- The Client's token after `finalize_issue`. -/
def tokS (ω : Sec) (req : Bytes) : Option Token :=
  finalizeIssue A.pk ⟨List.ofFn ω.1, List.ofFn ω.2, A.ci, A.cr, tOf A ω⟩ (sig A req)

/-- **The real redemption request**: `redeem_request` at `ρ`, from the token, under the adversary's
Anchor Set and digest. -/
def specR (ω : Sec) (req : Bytes) (ρ : Coins proveSeedBytes) (g : G) (s : S) : Except Error Bytes :=
  match tokS A ω req with
  | none => .error .invalidToken
  | some tok => redeemOf (nizkG PR g s) tok (A.choose req).1 A.ci A.cr (A.choose req).2 (List.ofFn ρ)

/-- The provers with uniform randomness and an optional output (they never abort). -/
abbrev PI' (x : IssueInstance) (w : Bytes) (ρ : Coins proveSeedBytes) (g : G) (s : S) :
    Option Bytes := some (PI w x (List.ofFn ρ) g s)
abbrev PR' (x : RedeemInstance) (w : Bytes) (ρ : Coins proveSeedBytes) (g : G) (s : S) :
    Option Bytes := some (PR w x (List.ofFn ρ) g s)

/-- The issuance statement and witness. -/
def xwI (ω : Sec) : Option (IssueInstance × Bytes) :=
  some (⟨tOf A ω, A.ci⟩, encodeIssueWitness (List.ofFn ω.1) A.ci A.cr (List.ofFn ω.2))

/-- The redemption statement and witness. -/
def xwR (ω : Sec) (req : Bytes) : Option (RedeemInstance × Bytes) :=
  if A.pk.eval (sig A req) = tOf A ω then
    match findIssuer (A.choose req).1 (tOf A ω) (sig A req) with
    | none => none
    | some i => some (⟨(A.choose req).1.keys, List.ofFn ω.1, A.ci, A.cr, (A.choose req).2⟩,
        encodeRedeemWitness (List.ofFn ω.1) A.ci A.cr (List.ofFn ω.2) (sig A req) i)
  else none

theorem xwI_fst (ω : Sec) : (xwI A ω).map Prod.fst = some ⟨tOf A ω, A.ci⟩ := rfl

theorem xwR_fst (ω : Sec) (req : Bytes) :
    (xwR A ω req).map Prod.fst = xR A (List.ofFn ω.1) (tOf A ω) req := by
  unfold xwR xR
  split_ifs
  · cases findIssuer (A.choose req).1 (tOf A ω) (sig A req) <;> rfl
  · rfl

theorem xwI_rel (ω : Sec) : ∀ x w, xwI A ω = some (x, w) → IssueRelW x w := by
  intro x w h
  cases h
  exact ⟨⟨List.ofFn ω.1, List.ofFn ω.2, A.cr, List.length_ofFn, List.length_ofFn, List.length_ofFn,
    rfl, rfl⟩, List.length_ofFn⟩

theorem xwR_rel (ω : Sec) (req : Bytes) : ∀ x w, xwR A ω req = some (x, w) → RedeemRelW x w := by
  intro x w h
  unfold xwR at h
  split_ifs at h with hv
  cases hf : findIssuer (A.choose req).1 (tOf A ω) (sig A req) with
  | none => rw [hf] at h; cases h
  | some i =>
    rw [hf] at h
    cases h
    obtain ⟨pk, hk, he⟩ := findIssuer_some hf
    exact ⟨⟨List.ofFn ω.2, sig A req, i, pk, List.length_ofFn, List.length_ofFn, hk, rfl, he⟩,
      (A.choose req).1.valid.2.1, List.length_ofFn, List.length_ofFn, List.length_ofFn⟩

/-- **The spec's issuance request is `reqI` of the proof.** -/
theorem specI_eq (ω : Sec) (ρ : Coins proveSeedBytes) (g : G) (s : S) :
    specI A PI ω ρ g s = reqI (tOf A ω) (proveO (PI' PI) (xwI A ω) ρ g s) := rfl

/-- **The spec's redemption request is `reqR` of the proof.** -/
theorem specR_eq (ω : Sec) (req : Bytes) (ρ : Coins proveSeedBytes) (g : G) (s : S) :
    specR A PR ω req ρ g s =
      reqR A (List.ofFn ω.1) (tOf A ω) req (proveO (PR' PR) (xwR A ω req) ρ g s) := by
  unfold specR reqR xwR tokS finalizeIssue
  by_cases hv : A.pk.eval (sig A req) = tOf A ω
  · simp only [hv, ite_true]
    unfold redeemOf
    have ht : com (List.ofFn ω.1) A.ci A.cr (List.ofFn ω.2) = tOf A ω := rfl
    simp only [ht]
    cases findIssuer (A.choose req).1 (tOf A ω) (sig A req) <;> rfl
  · simp only [hv, ite_false]

/-! ## The event -/

/-- The statement of an issuance request under `ctx_iss` (`issue_response`'s parse). -/
def stOfI (req ci : Bytes) : IssueInstance := ⟨req.take uovM, ci⟩

/-- The statement of a redemption request (`finalize_redeem`'s parse). -/
def stOfR (S' : AnchorSet) (req ci cr cd : Bytes) : RedeemInstance :=
  ⟨S'.keys, req.take nfBytes, ci, cr, cd⟩

/-- Statement and proof of the Client's issuance request. -/
def stI (req : Bytes) : Option (IssueInstance × Bytes) := some (stOfI req A.ci, req.drop uovM)

/-- Statement and proof of the Client's redemption request (under the adversary's set and digest). -/
def stR (req₁ : Bytes) (req : Except Error Bytes) : Option (RedeemInstance × Bytes) :=
  match req with
  | .ok b => some (stOfR (A.choose req₁).1 b A.ci A.cr (A.choose req₁).2, b.drop nfBytes)
  | .error _ => none

/-- **The operation is accepted**: the lengths the API checks, and the verifier. -/
def AccOp (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)
    (op : MOp) (s : S) : Prop :=
  match op with
  | .issue req ci => req.length = issueRequestBytes ∧ ci.length = ctxBytes ∧
      verI (stOfI req ci) (req.drop uovM) s = true
  | .redeem S' req ci cr cd => req.length = redeemRequestBytes ∧
      verR (stOfR S' req ci cr cd) (req.drop nfBytes) s = true

/-- **Its statement is fresh** (weak non-malleability). -/
def FreshOp (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes)) (op : MOp) :
    Prop :=
  match op with
  | .issue req ci => ∀ y, p₁ = some y → stOfI req ci ≠ y.1
  | .redeem S' req ci cr cd => ∀ y, p₂ = some y → stOfR S' req ci cr cd ≠ y.1

/-- **The extracted witness is a witness** (the spec relations). -/
def RelOp (op : MOp) (w : Bytes) : Prop :=
  match op with
  | .issue req ci => IssueRel (stOfI req ci) w
  | .redeem S' req ci cr cd => RedeemRel (stOfR S' req ci cr cd) w

/-- An opening `(nf, ctx_iss, ctx_red, r)`. -/
abbrev Open4 := Bytes × Bytes × Bytes × Bytes

def comOf (o : Open4) : Bytes := com o.1 o.2.1 o.2.2.1 o.2.2.2

/-- **The opening a witness carries**: an issuance witness `r ‖ ctx_red ‖ nf ‖ …`; a redemption
witness `r ‖ …` with `nf` and the contexts from the statement. -/
def opensOf : MOp → Bytes → List Open4
  | .issue _ ci, w => [((w.drop 32).take nfBytes, ci, (w.drop 16).take ctxBytes, w.take rBytes)]
  | .redeem _ req ci cr _, w => [(req.take nfBytes, ci, cr, w.take rBytes)]

/-- **The witness opens `t`.** -/
def OpensOp (t : Bytes) (op : MOp) (w : Bytes) : Prop := ∃ o ∈ opensOf op w, comOf o = t

/-- **The extractor**: the Client's statements and proofs, the adversary's last stage, the
tables. -/
abbrev Ext (G S : Type) :=
  Option (IssueInstance × Bytes) → Option (RedeemInstance × Bytes) → (G → G → S → MOp) → G → G →
    S → Bytes

variable (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)
  (ext : Ext G S)

def accE (_ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  AccOp verI verR (A.out o₁ o₂ g₁ g₂ s) s

def freshE (_ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  FreshOp (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂ g₁ g₂ s)

def relE (_ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  RelOp (A.out o₁ o₂ g₁ g₂ s) (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) g₁ g₂ s)

def opensE (ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  OpensOp (tOf A ω) (A.out o₁ o₂ g₁ g₂ s) (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) g₁ g₂ s)

/-- **The bad event.** -/
def Bad (ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  accE A verI verR ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧
    (¬ relE A ext ω o₁ o₂ g₁ g₂ s ∨ opensE A ext ω o₁ o₂ g₁ g₂ s)

/-- **The real game NM**: the Client's coins, the redemption's randomness and `H₃` slice, the
issuance's, the shared tables. -/
def nmReal (z : (Sec × (Coins proveSeedBytes × G)) × ((Coins proveSeedBytes × G) × S)) : Prop :=
  Bad A verI verR ext z.1.1 (specI A PI z.1.1 z.2.1.1 z.2.1.2 z.2.2)
    (specR A PR z.1.1 (specI A PI z.1.1 z.2.1.1 z.2.1.2 z.2.2) z.1.2.1 z.1.2.2 z.2.2)
    z.2.1.2 z.1.2.2 z.2.2

/-- **No redirect off the bad event.** An accepted redemption whose statement differs from the
honest one has a witness: some key of its Anchor Set signs `Com(nf*, ctx_iss*, ctx_red*, r)`, and
that commitment is not the honest `t`. So the honest token is not redeemed under another digest,
Anchor Set or context; a redemption with the honest `nf` spends another token. -/
theorem not_redirect (ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S)
    (S' : AnchorSet) (req ci cr cd : Bytes) (hq : A.out o₁ o₂ g₁ g₂ s = .redeem S' req ci cr cd)
    (hA : accE A verI verR ω o₁ o₂ g₁ g₂ s) (hF : freshE A ω o₁ o₂ g₁ g₂ s)
    (hB : ¬ Bad A verI verR ext ω o₁ o₂ g₁ g₂ s) :
    let w := ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) g₁ g₂ s
    RedeemRel (stOfR S' req ci cr cd) w ∧ com (req.take nfBytes) ci cr (w.take rBytes) ≠ tOf A ω := by
  have h : relE A ext ω o₁ o₂ g₁ g₂ s ∧ ¬ opensE A ext ω o₁ o₂ g₁ g₂ s := by
    unfold Bad at hB; tauto
  obtain ⟨hR, hO⟩ := h
  simp only [relE, opensE, hq, RelOp, OpensOp, opensOf, List.mem_cons, List.not_mem_nil, or_false,
    comOf, exists_eq_left] at hR hO
  exact ⟨hR, hO⟩

/-! ## The simulated world and the reductions -/

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → S → S)
  (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → S → S)

/-- The simulators with an optional output. -/
abbrev simI' (x : IssueInstance) (c : CI) : Option Bytes := some (simI x c)
abbrev simR' (x : RedeemInstance) (c : CR) : Option Bytes := some (simR x c)

/-- The simulated issuance request, from the commitment. -/
def simIssP (t : Bytes) (c : CI) : Bytes := reqI t (simO (simI' simI) (some ⟨t, A.ci⟩) c)
def pgIP (t : Bytes) (c : CI) (s : S) : S := progO progI (some ⟨t, A.ci⟩) c s

/-- The simulated redemption request, from `nf` and the commitment. -/
def simRedP (nf t req : Bytes) (c : CR) : Except Error Bytes :=
  reqR A nf t req (simO (simR' simR) (xR A nf t req) c)
def pgRP (nf t req : Bytes) (c : CR) (s : S) : S := progO progR (xR A nf t req) c s

/-- **The simulated game.** -/
def nmSim (z : (Sec × (CI × G)) × ((CR × G) × S)) : Prop :=
  simG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω))
    (fun ω => simRedP A simR (List.ofFn ω.1) (tOf A ω)) (fun ω => pgRP A progR (List.ofFn ω.1) (tOf A ω))
    (Bad A verI verR ext) z


/-- **The collision term** `δ_R`: the real redemption proof, after the simulated issuance, reads the
tables differently with and without the issuance's programming. -/
def deltaR (z : (Sec × (CI × G)) × ((Coins proveSeedBytes × G) × S)) : Prop :=
  deltaG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω)) (specR A PR) z

/-- **The first hop's distinguisher**, as a function of the issuance proof. -/
def distI (ω : Sec) (r₂ : Coins proveSeedBytes) (g₂ : G) (p : Bytes) (g : G) (u : S) : Prop :=
  D₁ (specR A PR) (Bad A verI verR ext) ω r₂ g₂ (reqI (tOf A ω) (some p)) g u

/-- **The second hop's distinguisher**, as a function of the redemption proof. -/
def distR (ω : Sec) (c₁ : CI) (g₁ : G) (p : Bytes) (g : G) (u : S) : Prop :=
  D₂ (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω)) (Bad A verI verR ext)
    ω c₁ g₁ (reqR A (List.ofFn ω.1) (tOf A ω) (simIssP A simI (tOf A ω) c₁) (some p)) g u

section OW

/-- **One-wayness of `Com`**: from the nullifier `nf` and the commitment
`t = Com(nf, ctx_iss, ctx_red, r)` (and auxiliary coins `β`), find an opening of `t` (any: one
other than the Client's is a binding break). -/
noncomputable def owAdv {β : Type} [Fintype β] (ci cr : Bytes) (B : Bytes → Bytes → β → Open4) : ℝ :=
  pr (Sec × β) fun z =>
    comOf (B (List.ofFn z.1.1) (com (List.ofFn z.1.1) ci cr (List.ofFn z.1.2)) z.2) =
      com (List.ofFn z.1.1) ci cr (List.ofFn z.1.2)

/-- The first opening of `t` in a list. -/
def pick (t : Bytes) : List Open4 → Open4
  | [] => ([], [], [], [])
  | o :: os => if comOf o = t then o else pick t os

theorem pick_win (t : Bytes) (l : List Open4) (h : ∃ o ∈ l, comOf o = t) : comOf (pick t l) = t := by
  induction l with
  | nil => obtain ⟨o, ho, _⟩ := h; cases ho
  | cons a l ih =>
    simp only [pick]
    split_ifs with ha
    · exact ha
    · obtain ⟨o, ho, ho'⟩ := h
      rcases List.mem_cons.1 ho with rfl | ho
      · exact absurd ho' ha
      · exact ih ⟨o, ho, ho'⟩

/-- **The inverter**: the simulated world from `nf` and `t` alone, the adversary, the extractor;
it outputs the first extracted opening of `t`. -/
def inverter (nf t : Bytes) (b : (CI × G) × ((CR × G) × S)) : Open4 :=
  let o₁ := simIssP A simI t b.1.1
  let x₂ := xR A nf t o₁
  let o₂ := reqR A nf t o₁ (simO (simR' simR) x₂ b.2.1.1)
  let s := progO progI (some ⟨t, A.ci⟩) b.1.1 (progO progR x₂ b.2.1.1 b.2.2)
  pick t (opensOf (A.out o₁ o₂ b.1.2 b.2.1.2 s) (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) b.1.2 b.2.1.2 s))

variable [Fintype CI] [Fintype CR] [Fintype G] [Fintype S]

/-- **One-wayness step.** -/
theorem sim_opens_le :
    pr ((Sec × (CI × G)) × ((CR × G) × S))
        (simG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω))
          (fun ω => simRedP A simR (List.ofFn ω.1) (tOf A ω))
          (fun ω => pgRP A progR (List.ofFn ω.1) (tOf A ω)) (opensE A ext)) ≤
      owAdv A.ci A.cr (inverter A ext simI progI simR progR) := by
  unfold owAdv
  rw [← pr_equiv (Equiv.prodAssoc Sec (CI × G) ((CR × G) × S)).symm]
  refine pr_mono fun z hz => ?_
  exact pick_win _ _ hz

end OW

theorem stI_simIss (t : Bytes) (ht : t.length = uovM) (c : CI) :
    stI A (simIssP A simI t c) = pairO (some ⟨t, A.ci⟩) (simO (simI' simI) (some ⟨t, A.ci⟩) c) := by
  simp only [stI, simIssP, reqI, simO, simI', pairO, Option.getD_some, stOfI, List.take_left' ht,
    List.drop_left' ht]

theorem stR_simRed (nf t req : Bytes) (hn : nf.length = nfBytes) (c : CR) :
    stR A req (simRedP A simR nf t req c) = pairO (xR A nf t req) (simO (simR' simR) (xR A nf t req) c) := by
  unfold simRedP reqR xR
  split_ifs
  · cases findIssuer (A.choose req).1 t (sig A req) with
    | none => rfl
    | some i =>
      simp only [stR, simO, simR', pairO, Option.getD_some, stOfR, List.take_left' hn,
        List.drop_left' hn]
  · rfl

/-- The simulated game's `Acc ∧ Fresh ∧ ¬ Rel` part. -/
def seEv (ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  accE A verI verR ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧ ¬ relE A ext ω o₁ o₂ g₁ g₂ s

variable [Fintype CI] [Fintype CR] [Fintype G] [Fintype S]

/-- **Weak simulation-extractability step.** -/
theorem sim_se_le {AdmE : (G → G → S → MOp) → Prop} {εSE : ℝ}
    (hse : WeakSE2 (simI' simI) progI (simR' simR) progR (AccOp verI verR) FreshOp RelOp ext AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr ((Sec × (CI × G)) × ((CR × G) × S))
        (simG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω))
          (fun ω => simRedP A simR (List.ofFn ω.1) (tOf A ω))
          (fun ω => pgRP A progR (List.ofFn ω.1) (tOf A ω)) (seEv A verI verR ext)) ≤ εSE := by
  have h := hse Sec (fun ω => some ⟨tOf A ω, A.ci⟩)
    (fun ω π₁ => xR A (List.ofFn ω.1) (tOf A ω) (reqI (tOf A ω) π₁))
    (fun ω π₁ π₂ => A.out (reqI (tOf A ω) π₁)
      (reqR A (List.ofFn ω.1) (tOf A ω) (reqI (tOf A ω) π₁) π₂))
    fun _ _ _ => hAE _ _
  refine le_of_eq_of_le (pr_congr fun z => ?_) h
  have h1 := stI_simIss A simI (tOf A z.1.1) (length_com _ _ _ _) z.1.2.1
  have h2 := stR_simRed A simR (List.ofFn z.1.1.1) (tOf A z.1.1) (simIssP A simI (tOf A z.1.1) z.1.2.1)
    List.length_ofFn z.2.1.1
  simp only [simG, seEv, accE, freshE, relE, h1, h2]
  rfl

/-- **Redemption non-malleability, from a bound on the simulated game's `Acc ∧ Fresh ∧ ¬ Rel`
event** (`hse`; `noRedirect` gets it from `WeakSE2`). -/
theorem noRedirect_of_se [Nonempty CI] [Nonempty CR] [Nonempty G] [Nonempty S]
    {AdmI : (Bytes → G → S → Prop) → Prop} {AdmR : (Bytes → G → S → Prop) → Prop}
    {εI εR εSE : ℝ}
    (hzkI : ZeroKnowledgeRO IssueRelW (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s)
      simI progI AdmI εI) (hεI : 0 ≤ εI)
    (hzkR : ZeroKnowledgeRO RedeemRelW (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s)
      simR progR AdmR εR) (hεR : 0 ≤ εR)
    (hAI : ∀ ω r₂ g₂, AdmI (distI A PR verI verR ext ω r₂ g₂))
    (hAR : ∀ ω c₁ g₁, AdmR (distR A verI verR ext simI progI ω c₁ g₁))
    (hse : pr ((Sec × (CI × G)) × ((CR × G) × S))
      (simG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω))
        (fun ω => simRedP A simR (List.ofFn ω.1) (tOf A ω))
        (fun ω => pgRP A progR (List.ofFn ω.1) (tOf A ω)) (seEv A verI verR ext)) ≤ εSE) :
    pr _ (nmReal A PI PR verI verR ext) ≤
      εI + εR + pr _ (deltaR A PR simI progI) + εSE +
        owAdv A.ci A.cr (inverter A ext simI progI simR progR) := by
  have hzkI' : ZeroKnowledgeRO IssueRelW (PI' PI) (simI' simI) progI
      (fun D => AdmI (fun o g s => D (some o) g s)) εI :=
    hzkI.transfer id (fun _ w => w) (fun _ _ h => h) some (fun _ hD => hD)
  have hzkR' : ZeroKnowledgeRO RedeemRelW (PR' PR) (simR' simR) progR
      (fun D => AdmR (fun o g s => D (some o) g s)) εR :=
    hzkR.transfer id (fun _ w => w) (fun _ _ h => h) some (fun _ hD => hD)
  have h := theft_le (Ω := Sec) (ρ₁ := Coins proveSeedBytes) (ρ₂ := Coins proveSeedBytes) (C₁ := CI)
    (C₂ := CR) (G := G) (S := S) (specI A PI) (fun ω => simIssP A simI (tOf A ω))
    (fun ω => pgIP A progI (tOf A ω)) (specR A PR)
    (fun ω => simRedP A simR (List.ofFn ω.1) (tOf A ω))
    (fun ω => pgRP A progR (List.ofFn ω.1) (tOf A ω)) (accE A verI verR) (freshE A) (relE A ext)
    (opensE A ext) (ε₁ := εI) (ε₂ := εR)
    (fun ω r₂ g₂ => by
      have := zk_step hzkI' hεI (xwI A ω) (xwI_rel A ω) (reqI (tOf A ω))
        (D₁ (specR A PR) (Bad A verI verR ext) ω r₂ g₂) (fun _ _ _ => hAI ω r₂ g₂)
      rw [xwI_fst] at this
      simp only [specI_eq]
      exact this)
    (fun ω c₁ g₁ => by
      have := zk_step hzkR' hεR (xwR A ω (simIssP A simI (tOf A ω) c₁)) (xwR_rel A ω _)
        (reqR A (List.ofFn ω.1) (tOf A ω) (simIssP A simI (tOf A ω) c₁))
        (D₂ (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω))
          (Bad A verI verR ext) ω c₁ g₁) (fun _ _ _ => hAR ω c₁ g₁)
      rw [xwR_fst] at this
      simp only [specR_eq]
      exact this)
  have hse' : pr ((Sec × (CI × G)) × ((CR × G) × S))
      (simG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω))
        (fun ω => simRedP A simR (List.ofFn ω.1) (tOf A ω))
        (fun ω => pgRP A progR (List.ofFn ω.1) (tOf A ω))
        (fun ω o₁ o₂ g₁ g₂ s => accE A verI verR ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧
          ¬ relE A ext ω o₁ o₂ g₁ g₂ s)) ≤ εSE := hse
  have hop := sim_opens_le A ext simI progI simR progR
  have hd : pr ((Sec × (CI × G)) × ((Coins proveSeedBytes × G) × S)) (deltaR A PR simI progI) =
      pr ((Sec × (CI × G)) × ((Coins proveSeedBytes × G) × S))
        (deltaG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω)) (specR A PR)) :=
    rfl
  have hr : pr ((Sec × (Coins proveSeedBytes × G)) × ((Coins proveSeedBytes × G) × S))
      (nmReal A PI PR verI verR ext) =
      pr ((Sec × (Coins proveSeedBytes × G)) × ((Coins proveSeedBytes × G) × S))
        (realG (specI A PI) (specR A PR)
        (fun ω o₁ o₂ g₁ g₂ s => accE A verI verR ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧
          (¬ relE A ext ω o₁ o₂ g₁ g₂ s ∨ opensE A ext ω o₁ o₂ g₁ g₂ s))) :=
    rfl
  rw [hr, hd]
  linarith

/-- **Redemption non-malleability (Theorem 3).** For every adversary, with zero knowledge of both
proof systems at the hops' distinguishers and weak simulation-extractability:

    Pr[Bad] ≤ ε_I + ε_R + δ_R + ε_SE + Adv^ow(inverter). -/
theorem noRedirect [Nonempty CI] [Nonempty CR] [Nonempty G] [Nonempty S]
    {AdmI : (Bytes → G → S → Prop) → Prop} {AdmR : (Bytes → G → S → Prop) → Prop}
    {AdmE : (G → G → S → MOp) → Prop} {εI εR εSE : ℝ}
    (hzkI : ZeroKnowledgeRO IssueRelW (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s)
      simI progI AdmI εI) (hεI : 0 ≤ εI)
    (hzkR : ZeroKnowledgeRO RedeemRelW (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s)
      simR progR AdmR εR) (hεR : 0 ≤ εR)
    (hAI : ∀ ω r₂ g₂, AdmI (distI A PR verI verR ext ω r₂ g₂))
    (hAR : ∀ ω c₁ g₁, AdmR (distR A verI verR ext simI progI ω c₁ g₁))
    (hse : WeakSE2 (simI' simI) progI (simR' simR) progR (AccOp verI verR) FreshOp RelOp ext AdmE εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr _ (nmReal A PI PR verI verR ext) ≤
      εI + εR + pr _ (deltaR A PR simI progI) + εSE +
        owAdv A.ci A.cr (inverter A ext simI progI simR progR) :=
  noRedirect_of_se A PI PR verI verR ext simI progI simR progR hzkI hεI hzkR hεR hAI hAR
    (sim_se_le A verI verR ext simI progI simR progR hse hAE)

end VoleMole.Theft.Moussaka
