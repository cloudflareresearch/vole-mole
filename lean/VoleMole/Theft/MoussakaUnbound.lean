import VoleMole.Theft.Basic
import VoleMole.Privacy.MoussakaUnbound
import VoleMole.Prob.Bytes

/-!
# Unbound Moussaka: no nullifier squatting and redemption non-malleability
(`security/moussaka-unbound.md` §5.2 Proposition U3, §5.3 Theorem U4)

The two theorems as one game on the executable spec (`Spec/MoussakaUnbound.lean`), in the table
model of `Theft/Basic.lean`, built as `Theft/Moussaka.lean` (the bound Theorem 3).

**The game NM-U** (one honest token). An honest Client with secret coins `ω = (nf_key, r)`
requests an unbound token for the adversary's `ctx_iss` (`issueRequestOf`, the seed expansion's
output given), finalizes the response against the Anchor key `pk` (`finalizeIssue`), and redeems
it once under the Anchor Set, **redemption context** `ctx_red` and digest `cd` that the adversary
chooses after seeing the issuance request (`redeemRequestOf`, with the C++ `find_issuer`). The
adversary (`Thief`) is the Moderator and every Anchor. It then reads the tables and outputs an
operation (`UOp`): an unbound issuance request with its own `ctx_iss`, or an unbound redemption
request with its own Anchor Set, contexts and digest (`unbound_finalize_redeem`'s arguments).

**The event** (`Bad`): the operation is accepted (`AccOp`: the lengths the API's types fix and the
verifier), its statement differs from the honest statement of the same relation (`FreshOp`), and
the extracted witness is not a witness, or it is and it **hits** the honest token (`HitOp`):
* it opens the honest commitment `t = UCom(nf_key, ctx_iss, r)` (Theorem U4: redirecting the honest
  redemption to another digest, Anchor Set or **redemption context**, or re-signing `t`), or
* it is a redemption carrying the honest token's nullifier for **its own** context,
  `nf* = Derive(nf_key, ctx_red*)`, whether the Client revealed it or not (Proposition U3, no
  squatting; also the redirect of U4 with the honest nullifier).

**`nmU`**:

    Pr[Bad] ≤ ε_I + ε_R + δ_R + ε_SE + (2⁻¹⁹² + ε_prf) + Adv^bind(B₁) + Adv^spr-k(B₂),

with `ε_I`, `ε_R` zero knowledge of the two unbound proof systems (`ZeroKnowledgeRO` for
`IssueRelW`, `RedeemRelW`), `δ_R` the collision term of the second hop, `ε_SE` weak
simulation-extractability (`WeakSE2`, **a hypothesis**, L8 on paper), `ε_prf` the PRF advantage of
`Derive` with the commitment leaked (`prf1Adv`, `Adv^prf-t_1`, **a hypothesis** on Keccak-p[800]) of
the explicit distinguisher `owkD`, `Adv^bind` the binding advantage of `UCom` of an explicit
collision finder `B₁` (`bindAdv`) and `Adv^spr-k` the key second-preimage advantage of `Derive` of
an explicit `B₂` (`sprAdv`). The corollaries `noSquat` (U3) and `noRedirectU` (U4) restrict the
event.

**Key recovery is not an assumption** (`owkAdv_le`): an adversary that outputs the honest key
from `t` and one nullifier is turned into a PRF distinguisher, which checks the key at a second,
fresh context (`other`): `Adv^ow-k ≤ Adv^prf-t_1 + 2⁻¹⁹²`. So `Adv^ow-kr` (U4) and the key-recovery
case of U3 cost `ε_prf + 2⁻¹⁹²`, not an extra one-wayness assumption on `UCom`.

**Scope.** One honest token, one issuance and one redemption (the two hops of `Theft/Basic.lean`).
The note's `U` tokens (the guessing factor `U`) and several honest redemptions per token are not
modelled; they would need `WeakSE2` with more than two simulated proofs.
-/

open Finset

namespace VoleMole.Theft.MoussakaUnbound

open VoleMole.Privacy VoleMole.Privacy.MoussakaUnbound VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

variable {G S : Type}

/-- The honest Client's coins `(nf_key, r)`. -/
abbrev Sec := Coins nfKeyBytes × Coins rBytes

/-- An operation the adversary submits: an unbound issuance request under its `ctx_iss`, or an
unbound redemption request with its Anchor Set, contexts and challenge digest. -/
inductive UOp
  | issue (req ctxIss : Bytes)
  | redeem (anchors : AnchorSet) (req ctxIss ctxRed cd : Bytes)

/-- **The adversary**: the Moderator and every Anchor. From the Client's issuance request it
chooses the response and the Anchor Set, redemption context and digest of the honest redemption. -/
structure Thief (G S : Type) where
  ctxIss : Coins ctxBytes
  pk : UOVKey
  respond : Bytes → Coins uovN
  choose : Bytes → AnchorSet × Coins ctxBytes × Bytes
  out : Bytes → Except Error Bytes → G → G → S → UOp

variable (A : Thief G S)

def Thief.ci : Bytes := List.ofFn A.ctxIss

/-- The honest redemption's Anchor Set, context and digest, from the issuance request. -/
def Thief.set (req : Bytes) : AnchorSet := (A.choose req).1
def Thief.cr (req : Bytes) : Bytes := List.ofFn (A.choose req).2.1
def Thief.cd (req : Bytes) : Bytes := (A.choose req).2.2

/-! ## The Client, in public form (the nullifier `nf` and the commitment `t`) -/

/-- The issuance request from the proof. -/
def reqI (t : Bytes) (π : Option Bytes) : Bytes := t ++ π.getD []

/-- The Client's signature on its token, from the issuance request. -/
def sig (req : Bytes) : Bytes := List.ofFn (A.respond req)

/-- **The redemption statement**, if the Client redeems: its token finalized (`P(s) = t`) and some
key of the set verifies it (`find_issuer`). -/
def xR (nf t req : Bytes) : Option RedeemInstance :=
  if A.pk.eval (sig A req) = t then
    match findIssuer (A.set req) t (sig A req) with
    | none => none
    | some _ => some ⟨(A.set req).keys, nf, A.ci, A.cr req, A.cd req⟩
  else none

/-- **The redemption request** from the proof (an error if the Client does not redeem). -/
def reqR (nf t req : Bytes) (π : Option Bytes) : Except Error Bytes :=
  if A.pk.eval (sig A req) = t then
    match findIssuer (A.set req) t (sig A req) with
    | none => .error .invalidToken
    | some _ => .ok (nf ++ π.getD [])
  else .error .invalidToken

/-! ## The Client, from the spec -/

/-- The commitment of the coins, `UCom(nf_key, ctx_iss, r)`. -/
def tOf (ω : Sec) : Bytes := ucom (List.ofFn ω.1) A.ci (List.ofFn ω.2)

/-- The honest nullifier in the redemption context chosen from `req`, `Derive(nf_key, ctx_red)`. -/
def nfOf (ω : Sec) (req : Bytes) : Bytes := derive (List.ofFn ω.1) (A.cr req)

/-- A prover with the tables fixed, as the spec's `NIZK`. -/
def nizkG {I : Type} (P : Bytes → I → Bytes → G → S → Bytes) (g : G) (s : S) : NIZK I :=
  ⟨fun w x rho => P w x rho g s, fun _ _ => true⟩

variable (PI : Bytes → IssueInstance → Bytes → G → S → Bytes)
  (PR : Bytes → RedeemInstance → Bytes → G → S → Bytes)

/-- **The real issuance request**: `unbound_issue_request` at `(nf_key, r, ρ)`. -/
def specI (ω : Sec) (ρ : Coins proveSeedBytes) (g : G) (s : S) : Bytes :=
  (issueRequestOf (nizkG PI g s) A.ci (List.ofFn ω.1) (List.ofFn ω.2) (List.ofFn ρ)).2

/-- The Client's token after `finalize_issue`. -/
def tokS (ω : Sec) (req : Bytes) : Option Token :=
  finalizeIssue A.pk ⟨List.ofFn ω.1, List.ofFn ω.2, A.ci, tOf A ω⟩ (sig A req)

/-- **The real redemption request**: `UnboundToken::redeem_request` at `ρ`, under the adversary's
Anchor Set, redemption context and digest. -/
def specR (ω : Sec) (req : Bytes) (ρ : Coins proveSeedBytes) (g : G) (s : S) : Except Error Bytes :=
  match tokS A ω req with
  | none => .error .invalidToken
  | some tok => redeemRequestOf (nizkG PR g s) tok (A.set req) A.ci (A.cr req) (A.cd req)
      (List.ofFn ρ)

/-- The provers with uniform randomness and an optional output (they never abort). -/
abbrev PI' (x : IssueInstance) (w : Bytes) (ρ : Coins proveSeedBytes) (g : G) (s : S) :
    Option Bytes := some (PI w x (List.ofFn ρ) g s)
abbrev PR' (x : RedeemInstance) (w : Bytes) (ρ : Coins proveSeedBytes) (g : G) (s : S) :
    Option Bytes := some (PR w x (List.ofFn ρ) g s)

/-- The issuance statement and witness. -/
def xwI (ω : Sec) : Option (IssueInstance × Bytes) :=
  some (⟨tOf A ω, A.ci⟩, encodeIssueWitness (List.ofFn ω.1) A.ci (List.ofFn ω.2))

/-- The redemption statement and witness. -/
def xwR (ω : Sec) (req : Bytes) : Option (RedeemInstance × Bytes) :=
  if A.pk.eval (sig A req) = tOf A ω then
    match findIssuer (A.set req) (tOf A ω) (sig A req) with
    | none => none
    | some i => some (⟨(A.set req).keys, nfOf A ω req, A.ci, A.cr req, A.cd req⟩,
        encodeRedeemWitness (List.ofFn ω.1) A.ci (A.cr req) (List.ofFn ω.2) (sig A req) i)
  else none

theorem xwI_fst (ω : Sec) : (xwI A ω).map Prod.fst = some ⟨tOf A ω, A.ci⟩ := rfl

theorem xwR_fst (ω : Sec) (req : Bytes) :
    (xwR A ω req).map Prod.fst = xR A (nfOf A ω req) (tOf A ω) req := by
  unfold xwR xR
  split_ifs
  · cases findIssuer (A.set req) (tOf A ω) (sig A req) <;> rfl
  · rfl

theorem xwI_rel (ω : Sec) : ∀ x w, xwI A ω = some (x, w) → IssueRelW x w := by
  intro x w h
  cases h
  exact ⟨⟨List.ofFn ω.1, List.ofFn ω.2, List.length_ofFn, List.length_ofFn, rfl, rfl⟩,
    List.length_ofFn⟩

theorem xwR_rel (ω : Sec) (req : Bytes) : ∀ x w, xwR A ω req = some (x, w) → RedeemRelW x w := by
  intro x w h
  unfold xwR at h
  split_ifs at h with hv
  cases hf : findIssuer (A.set req) (tOf A ω) (sig A req) with
  | none => rw [hf] at h; cases h
  | some i =>
    rw [hf] at h
    cases h
    obtain ⟨pk, hk, he⟩ := findIssuer_some hf
    exact ⟨⟨List.ofFn ω.1, List.ofFn ω.2, sig A req, i, pk, List.length_ofFn, List.length_ofFn,
      List.length_ofFn, hk, rfl, he, rfl⟩,
      (A.set req).valid.2.1, length_derive _ _, List.length_ofFn, List.length_ofFn⟩

/-- **The spec's issuance request is `reqI` of the proof.** -/
theorem specI_eq (ω : Sec) (ρ : Coins proveSeedBytes) (g : G) (s : S) :
    specI A PI ω ρ g s = reqI (tOf A ω) (proveO (PI' PI) (xwI A ω) ρ g s) := rfl

/-- **The spec's redemption request is `reqR` of the proof.** -/
theorem specR_eq (ω : Sec) (req : Bytes) (ρ : Coins proveSeedBytes) (g : G) (s : S) :
    specR A PR ω req ρ g s =
      reqR A (nfOf A ω req) (tOf A ω) req (proveO (PR' PR) (xwR A ω req) ρ g s) := by
  unfold specR reqR xwR tokS finalizeIssue
  by_cases hv : A.pk.eval (sig A req) = tOf A ω
  · simp only [hv, ite_true]
    unfold redeemRequestOf
    have ht : ucom (List.ofFn ω.1) A.ci (List.ofFn ω.2) = tOf A ω := rfl
    simp only [ht]
    cases findIssuer (A.set req) (tOf A ω) (sig A req) <;> rfl
  · simp only [hv, ite_false]

/-! ## The event -/

/-- The statement of an unbound issuance request under `ctx_iss` (`unbound_issue_response`'s
parse). -/
def stOfI (req ci : Bytes) : IssueInstance := ⟨req.take uovM, ci⟩

/-- The statement of an unbound redemption request (`unbound_finalize_redeem`'s parse). -/
def stOfR (S' : AnchorSet) (req ci cr cd : Bytes) : RedeemInstance :=
  ⟨S'.keys, req.take nfBytes, ci, cr, cd⟩

/-- Statement and proof of the Client's issuance request. -/
def stI (req : Bytes) : Option (IssueInstance × Bytes) := some (stOfI req A.ci, req.drop uovM)

/-- Statement and proof of the Client's redemption request. -/
def stR (req₁ : Bytes) (req : Except Error Bytes) : Option (RedeemInstance × Bytes) :=
  match req with
  | .ok b => some (stOfR (A.set req₁) b A.ci (A.cr req₁) (A.cd req₁), b.drop nfBytes)
  | .error _ => none

/-- **The operation is accepted**: the lengths the C++ types fix (`UnboundIssueRequest`,
`UnboundRedeemRequest`, `Context = std::array<uint8_t, 16>`, `include/vole_mole/ihat.hpp`) and
the verifier. -/
def AccOp (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)
    (op : UOp) (s : S) : Prop :=
  match op with
  | .issue req ci => req.length = uovM + issueProofBytes ∧ ci.length = ctxBytes ∧
      verI (stOfI req ci) (req.drop uovM) s = true
  | .redeem S' req ci cr cd => req.length = nfBytes + redeemProofBytes ∧ ci.length = ctxBytes ∧
      cr.length = ctxBytes ∧ verR (stOfR S' req ci cr cd) (req.drop nfBytes) s = true

/-- **Its statement is fresh** (weak non-malleability). -/
def FreshOp (p₁ : Option (IssueInstance × Bytes)) (p₂ : Option (RedeemInstance × Bytes)) (op : UOp) :
    Prop :=
  match op with
  | .issue req ci => ∀ y, p₁ = some y → stOfI req ci ≠ y.1
  | .redeem S' req ci cr cd => ∀ y, p₂ = some y → stOfR S' req ci cr cd ≠ y.1

/-- **The extracted witness is a witness** (the spec relations). -/
def RelOp (op : UOp) (w : Bytes) : Prop :=
  match op with
  | .issue req ci => IssueRel (stOfI req ci) w
  | .redeem S' req ci cr cd => RedeemRel (stOfR S' req ci cr cd) w

/-- The issuance context of an operation. -/
def ciOf : UOp → Bytes
  | .issue _ ci => ci
  | .redeem _ _ ci _ _ => ci

/-- The `r` and `nf_key` of a witness (both encodings start `r ‖ nf_key`). -/
def rOf (w : Bytes) : Bytes := w.take rBytes
def keyOf (w : Bytes) : Bytes := (w.drop rBytes).take nfKeyBytes

/-- **The witness opens `t`**: it is a witness, and its `UCom` input, with the operation's
`ctx_iss` (16 bytes), commits to `t`. -/
def OpensOp (t : Bytes) (op : UOp) (w : Bytes) : Prop :=
  RelOp op w ∧ (ciOf op).length = ctxBytes ∧ ucom (keyOf w) (ciOf op) (rOf w) = t

/-- **The operation carries the nullifier of the key `k` in its own context**: a redemption with
`nf* = Derive(k, ctx_red*)` and a witness. -/
def NfOp (k : Bytes) (op : UOp) (w : Bytes) : Prop :=
  RelOp op w ∧
    match op with
    | .issue _ _ => False
    | .redeem _ req _ cr _ => req.take nfBytes = derive k cr

/-- **The witness hits the honest token** (`t`, `nf_key`). -/
def HitOp (t k : Bytes) (op : UOp) (w : Bytes) : Prop := OpensOp t op w ∨ NfOp k op w

/-- **The extractor**: the Client's statements and proofs, the adversary's last stage, the
tables. -/
abbrev Ext (G S : Type) :=
  Option (IssueInstance × Bytes) → Option (RedeemInstance × Bytes) → (G → G → S → UOp) → G → G →
    S → Bytes

variable (verI : IssueInstance → Bytes → S → Bool) (verR : RedeemInstance → Bytes → S → Bool)
  (ext : Ext G S)

def accE (_ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  AccOp verI verR (A.out o₁ o₂ g₁ g₂ s) s

def freshE (_ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  FreshOp (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂ g₁ g₂ s)

def relE (_ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  RelOp (A.out o₁ o₂ g₁ g₂ s) (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) g₁ g₂ s)

def hitE (ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  HitOp (tOf A ω) (List.ofFn ω.1) (A.out o₁ o₂ g₁ g₂ s)
    (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) g₁ g₂ s)

/-- **The bad event.** -/
def Bad (ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  accE A verI verR ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧
    (¬ relE A ext ω o₁ o₂ g₁ g₂ s ∨ hitE A ext ω o₁ o₂ g₁ g₂ s)

/-- **The real game NM-U** for an event: the Client's coins, the redemption's randomness and `H₃`
slice, the issuance's, the shared tables. -/
def nmRealE (Ev : Sec → Bytes → Except Error Bytes → G → G → S → Prop)
    (z : (Sec × (Coins proveSeedBytes × G)) × ((Coins proveSeedBytes × G) × S)) : Prop :=
  Ev z.1.1 (specI A PI z.1.1 z.2.1.1 z.2.1.2 z.2.2)
    (specR A PR z.1.1 (specI A PI z.1.1 z.2.1.1 z.2.1.2 z.2.2) z.1.2.1 z.1.2.2 z.2.2)
    z.2.1.2 z.1.2.2 z.2.2

/-- **The real game NM-U** with the bad event. -/
def nmReal (z : (Sec × (Coins proveSeedBytes × G)) × ((Coins proveSeedBytes × G) × S)) : Prop :=
  nmRealE A PI PR (Bad A verI verR ext) z

/-- **The squatting event (Proposition U3)**: an accepted redemption with a fresh statement that
carries the honest token's nullifier for its own context, `nf* = Derive(nf_key, ctx_red*)`. It
does not mention extraction. -/
def Squat (ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  accE A verI verR ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧
    match A.out o₁ o₂ g₁ g₂ s with
    | .issue _ _ => False
    | .redeem _ req _ cr _ => req.take nfBytes = derive (List.ofFn ω.1) cr

/-- **The redirect event (Theorem U4)**: an accepted operation with a fresh statement whose
extracted witness is not a witness or opens the honest commitment `t` (another digest, Anchor
Set or redemption context for the honest token, or `t` signed again). -/
def Redirect (ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  accE A verI verR ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧
    (¬ relE A ext ω o₁ o₂ g₁ g₂ s ∨
      ucom (keyOf (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) g₁ g₂ s))
        (ciOf (A.out o₁ o₂ g₁ g₂ s)) (rOf (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) g₁ g₂ s)) =
        tOf A ω)

/-! ## The event in plain terms -/

theorem keyOf_issue {k ci r : Bytes} (hk : k.length = nfKeyBytes) (hr : r.length = rBytes) :
    keyOf (encodeIssueWitness k ci r) = k ∧ rOf (encodeIssueWitness k ci r) = r := by
  unfold keyOf rOf encodeIssueWitness
  simp only [List.append_assoc]
  exact ⟨by rw [List.drop_left' hr, List.take_left' hk], List.take_left' hr⟩

theorem keyOf_redeem {k ci cr r s : Bytes} {u : ℕ} (hk : k.length = nfKeyBytes)
    (hr : r.length = rBytes) :
    keyOf (encodeRedeemWitness k ci cr r s u) = k ∧ rOf (encodeRedeemWitness k ci cr r s u) = r := by
  unfold keyOf rOf encodeRedeemWitness
  simp only [List.append_assoc]
  exact ⟨by rw [List.drop_left' hr, List.take_left' hk], List.take_left' hr⟩

/-- **What a witness gives**: its key and `r` have 16 bytes. -/
theorem relOp_len {op : UOp} {w : Bytes} (h : RelOp op w) :
    (keyOf w).length = nfKeyBytes ∧ (rOf w).length = rBytes := by
  rcases op with ⟨req, ci⟩ | ⟨S', req, ci, cr, cd⟩
  · obtain ⟨k, r, hk, hr, rfl, -⟩ := h
    obtain ⟨e1, e2⟩ := keyOf_issue (ci := ci) hk hr
    simp only [stOfI]; rw [e1, e2]; exact ⟨hk, hr⟩
  · obtain ⟨k, r, s, u, pk, hk, hr, -, -, rfl, -, -⟩ := h
    obtain ⟨e1, e2⟩ := keyOf_redeem (ci := ci) (cr := cr) (s := s) (u := u) hk hr
    simp only [stOfR]; rw [e1, e2]; exact ⟨hk, hr⟩

/-- **A redemption witness's key gives the statement's nullifier.** -/
theorem relOp_nf {S' : AnchorSet} {req ci cr cd w : Bytes} (h : RelOp (.redeem S' req ci cr cd) w) :
    req.take nfBytes = derive (keyOf w) cr := by
  obtain ⟨k, r, s, u, pk, hk, hr, -, -, rfl, -, hn⟩ := h
  obtain ⟨e1, -⟩ := keyOf_redeem (ci := ci) (cr := cr) (s := s) (u := u) hk hr
  simp only [stOfR] at hn ⊢; rw [e1]
  exact hn

/-- **The bad event, read plainly**: an accepted operation with a fresh statement whose extracted
witness is not a witness, or opens `t` (with its `ctx_iss`), or is a redemption carrying the
nullifier `Derive(nf_key, ctx_red*)` of the honest key in its own context. The 16-byte
`ctx_iss` of `OpensOp` is implied by acceptance. -/
theorem bad_iff (ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) :
    Bad A verI verR ext ω o₁ o₂ g₁ g₂ s ↔
      accE A verI verR ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧
        (¬ relE A ext ω o₁ o₂ g₁ g₂ s ∨
          (let op := A.out o₁ o₂ g₁ g₂ s
           let w := ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) g₁ g₂ s
           ucom (keyOf w) (ciOf op) (rOf w) = tOf A ω ∨
             (match op with
              | .issue _ _ => False
              | .redeem _ req _ cr _ => req.take nfBytes = derive (List.ofFn ω.1) cr))) := by
  unfold Bad hitE HitOp OpensOp NfOp
  simp only [relE]
  constructor
  · rintro ⟨ha, hf, hr | ⟨_, -, ho⟩ | ⟨_, hn⟩⟩
    · exact ⟨ha, hf, Or.inl hr⟩
    · exact ⟨ha, hf, Or.inr (Or.inl ho)⟩
    · exact ⟨ha, hf, Or.inr (Or.inr hn)⟩
  · rintro ⟨ha, hf, hr | ho | hn⟩
    · exact ⟨ha, hf, Or.inl hr⟩
    · by_cases hr : RelOp (A.out o₁ o₂ g₁ g₂ s) (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) g₁ g₂ s)
      · refine ⟨ha, hf, Or.inr (Or.inl ⟨hr, ?_, ho⟩)⟩
        unfold accE AccOp at ha
        revert ha
        cases A.out o₁ o₂ g₁ g₂ s <;> simp only [ciOf] <;> tauto
      · exact ⟨ha, hf, Or.inl hr⟩
    · by_cases hr : RelOp (A.out o₁ o₂ g₁ g₂ s) (ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) g₁ g₂ s)
      · exact ⟨ha, hf, Or.inr (Or.inr ⟨hr, hn⟩)⟩
      · exact ⟨ha, hf, Or.inl hr⟩

/-! ## The assumptions on `UCom` and `Derive`, as games -/

/-- A nullifier table: one uniform 24-byte value per redemption context. -/
abbrev Tab1 := Coins ctxBytes → Coins nfBytes

/-- **The real PRF experiment with the commitment leaked** (one key): `t = UCom(k, ctx_iss, r)` and
the table `ctx ↦ Derive(k, ctx)`. -/
def prf1Real (ci : Bytes) (x : Sec) : Bytes × (Coins ctxBytes → Bytes) :=
  (ucom (List.ofFn x.1) ci (List.ofFn x.2), fun c => derive (List.ofFn x.1) (List.ofFn c))

/-- **The ideal PRF experiment**: the same `t`, a uniform table. -/
def prf1Ideal (ci : Bytes) (x : Sec × Tab1) : Bytes × (Coins ctxBytes → Bytes) :=
  (ucom (List.ofFn x.1.1) ci (List.ofFn x.1.2), fun c => List.ofFn (x.2 c))

/-- **The PRF advantage** of `D` (`security/moussaka-unbound.md` §3.2, `Adv^prf-t_1`). -/
noncomputable def prf1Adv (ci : Bytes) (D : Bytes × (Coins ctxBytes → Bytes) → Prop) : ℝ :=
  |pr Sec (fun x => D (prf1Real ci x)) - pr (Sec × Tab1) (fun x => D (prf1Ideal ci x))|

/-- **An adversary with one nullifier**: from the commitment `t` (and its coins) it chooses one
context, gets `Derive(k, ·)` there, and outputs a result. -/
structure OAdv (β X : Type) where
  qry : Bytes → β → Coins ctxBytes
  fin : Bytes → Bytes → β → X

/-- The adversary's output on the key and opening `x.1` and its coins `x.2`. -/
def OAdv.run {β X : Type} (B : OAdv β X) (ci : Bytes) (x : Sec × β) : X :=
  B.fin (ucom (List.ofFn x.1.1) ci (List.ofFn x.1.2))
    (derive (List.ofFn x.1.1) (List.ofFn (B.qry (ucom (List.ofFn x.1.1) ci (List.ofFn x.1.2)) x.2)))
    x.2

/-- **Key recovery** (`Adv^ow-k`): the adversary outputs the key `nf_key`. -/
noncomputable def owkAdv {β : Type} [Fintype β] (ci : Bytes) (B : OAdv β Bytes) : ℝ :=
  pr (Sec × β) fun x => B.run ci x = List.ofFn x.1.1

/-- A key second preimage for the key `k`: a 16-byte key `k' ≠ k` and a context `c'` with
`Derive(k', c') = Derive(k, c')`. -/
def SprWin (k : Bytes) (o : Bytes × Bytes) : Prop :=
  o.1.length = nfKeyBytes ∧ o.1 ≠ k ∧ derive o.1 o.2 = derive k o.2

/-- **Second preimages of `Derive` in the key** (`Adv^spr-k`). -/
noncomputable def sprAdv {β : Type} [Fintype β] (ci : Bytes) (B : OAdv β (Bytes × Bytes)) : ℝ :=
  pr (Sec × β) fun x => SprWin (List.ofFn x.1.1) (B.run ci x)

/-- A `UCom` input `(nf_key, ctx_iss, r)`. -/
abbrev UOpening := Bytes × Bytes × Bytes

/-- Two distinct `UCom` inputs of 16-byte fields with one commitment. -/
def BindWin (p : UOpening × UOpening) : Prop :=
  p.1 ≠ p.2 ∧ p.1.1.length = 16 ∧ p.1.2.1.length = 16 ∧ p.1.2.2.length = 16 ∧
    p.2.1.length = 16 ∧ p.2.2.1.length = 16 ∧ p.2.2.2.length = 16 ∧
    ucom p.1.1 p.1.2.1 p.1.2.2 = ucom p.2.1 p.2.2.1 p.2.2.2

/-- **Binding of `UCom`** (`Adv^bind`): the probability that `B` outputs a collision, from coins
`γ`. -/
noncomputable def bindAdv {γ : Type} [Fintype γ] (B : γ → UOpening × UOpening) : ℝ :=
  pr γ fun z => BindWin (B z)

/-! ## Key recovery reduces to the PRF -/

/-- Two fixed distinct contexts. -/
def c₀ : Coins ctxBytes := fun _ => 0
def c₁ : Coins ctxBytes := fun _ => 1

/-- A context other than `c`. -/
def other (c : Coins ctxBytes) : Coins ctxBytes := if c = c₀ then c₁ else c₀

theorem other_ne (c : Coins ctxBytes) : other c ≠ c := by
  unfold other
  split_ifs with h
  · rw [h]; intro e; have := congrFun e 0; simp [c₀, c₁] at this
  · exact fun e => h e.symm

/-- **The PRF distinguisher of a key-recovery adversary** (coins `b` fixed): it runs the adversary
on `t` and the table at its context, and checks the output key at the other context. -/
def owkD {β : Type} (B : OAdv β Bytes) (b : β) (z : Bytes × (Coins ctxBytes → Bytes)) : Prop :=
  derive (B.fin z.1 (z.2 (B.qry z.1 b)) b) (List.ofFn (other (B.qry z.1 b))) =
    z.2 (other (B.qry z.1 b))

theorem card_coins24 : Fintype.card (Coins nfBytes) = 2 ^ 192 := by
  rw [Fintype.card_fun, Fintype.card_fin, Prob.card_uint8]; norm_num

/-- **The ideal experiment**: the table at the other context is independent of everything the
adversary saw, so the check passes with probability `2⁻¹⁹²`. -/
theorem owkD_ideal {β : Type} (ci : Bytes) (B : OAdv β Bytes) (b : β) :
    pr (Sec × Tab1) (fun x => owkD B b (prf1Ideal ci x)) ≤ 1 / 2 ^ 192 := by
  rw [pr_prod]
  rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos)]
  have hx : ∀ x : Sec, pr Tab1 (fun F => owkD B b (prf1Ideal ci (x, F))) ≤ 1 / 2 ^ 192 := by
    intro x
    set t := ucom (List.ofFn x.1) ci (List.ofFn x.2)
    set c := B.qry t b
    let pts : Bool → Coins ctxBytes := fun i => cond i (other c) c
    have hinj : Function.Injective pts := by
      intro i j h
      cases i <;> cases j <;> simp only [pts, Bool.cond_true, Bool.cond_false] at h <;>
        first | rfl | exact absurd h (other_ne c) | exact absurd h.symm (other_ne c)
    have h1 := close_restrict (R := Coins nfBytes) hinj
      (fun u => derive (B.fin t (List.ofFn (u false)) b) (List.ofFn (other c)) = List.ofFn (u true))
    have e : pr Tab1 (fun F => owkD B b (prf1Ideal ci (x, F))) =
        pr (Bool → Coins nfBytes) (fun u =>
          derive (B.fin t (List.ofFn (u false)) b) (List.ofFn (other c)) = List.ofFn (u true)) :=
      sub_eq_zero.1 (abs_nonpos_iff.1 h1)
    rw [e, ← pr_equiv ((Equiv.boolArrowEquivProd (Coins nfBytes)).trans (Equiv.prodComm _ _)).symm]
    have h2 := pr_mem_indep_le (α := Coins nfBytes) (β := Coins nfBytes) List.ofFn
      List.ofFn_injective (fun v => {derive (B.fin t (List.ofFn v) b) (List.ofFn (other c))})
      (q := 1) (fun _ => by simp)
    rw [card_coins24] at h2
    refine le_of_eq_of_le (pr_congr fun p => ?_) (h2.trans (by norm_num))
    simp [Equiv.boolArrowEquivProd, eq_comm]
  calc ∑ x : Sec, pr Tab1 (fun F => owkD B b (prf1Ideal ci (x, F)))
      ≤ ∑ _x : Sec, (1 : ℝ) / 2 ^ 192 := Finset.sum_le_sum fun x _ => hx x
    _ = 1 / 2 ^ 192 * Fintype.card Sec := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- An event on `α × β` bounded for every fixed second coordinate is bounded. -/
theorem pr_le_of_snd {α β : Type*} [Fintype α] [Fintype β] [Nonempty β] {P : α × β → Prop} {c : ℝ}
    (h : ∀ b, pr α (fun a => P (a, b)) ≤ c) : pr (α × β) P ≤ c := by
  rw [← pr_equiv (Equiv.prodComm β α), pr_prod]
  rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos)]
  calc ∑ b, pr α (fun a => P ((Equiv.prodComm β α) (b, a)))
      ≤ ∑ _b : β, c := Finset.sum_le_sum fun b _ => h b
    _ = c * Fintype.card β := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **Key recovery is bounded by the PRF assumption**: `Adv^ow-k(B) ≤ ε_prf + 2⁻¹⁹²` if every
`owkD B b` has PRF advantage at most `ε_prf`. -/
theorem owkAdv_le {β : Type} [Fintype β] [Nonempty β] (ci : Bytes) (B : OAdv β Bytes) {εprf : ℝ}
    (hprf : ∀ b, prf1Adv ci (owkD B b) ≤ εprf) : owkAdv ci B ≤ εprf + 1 / 2 ^ 192 := by
  unfold owkAdv
  refine pr_le_of_snd fun b => ?_
  have hreal : pr Sec (fun a => B.run ci (a, b) = List.ofFn a.1) ≤
      pr Sec (fun x => owkD B b (prf1Real ci x)) := pr_mono fun a ha => by
    simp only [OAdv.run] at ha
    simp only [owkD, prf1Real, ha]
  have h := hprf b
  unfold prf1Adv at h
  have := (abs_le.1 h).2
  linarith [owkD_ideal ci B b]

/-! ## The simulated world and the reductions -/

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (progI : IssueInstance → CI → S → S)
  (simR : RedeemInstance → CR → Bytes) (progR : RedeemInstance → CR → S → S)

/-- The simulators with an optional output. -/
abbrev simI' (x : IssueInstance) (c : CI) : Option Bytes := some (simI x c)
abbrev simR' (x : RedeemInstance) (c : CR) : Option Bytes := some (simR x c)

/-- The simulated issuance request, from the commitment. -/
def simIssP (t : Bytes) (c : CI) : Bytes := reqI t (simO (simI' simI) (some ⟨t, A.ci⟩) c)
def pgIP (t : Bytes) (c : CI) (s : S) : S := progO progI (some ⟨t, A.ci⟩) c s

/-- The simulated redemption request, from the nullifier and the commitment. -/
def simRedP (nf t req : Bytes) (c : CR) : Except Error Bytes :=
  reqR A nf t req (simO (simR' simR) (xR A nf t req) c)
def pgRP (nf t req : Bytes) (c : CR) (s : S) : S := progO progR (xR A nf t req) c s

/-- The simulated world's coins. -/
abbrev SimC (CI CR G S : Type) := (CI × G) × ((CR × G) × S)

/-- **The simulated world as a function of `t` and the one nullifier**: the context the honest
redemption uses (`qry`) and the operation with its extracted witness (`view`). -/
def qry (t : Bytes) (b : SimC CI CR G S) : Coins ctxBytes := (A.choose (simIssP A simI t b.1.1)).2.1

def view (t nf : Bytes) (b : SimC CI CR G S) : UOp × Bytes :=
  let o₁ := simIssP A simI t b.1.1
  let x₂ := xR A nf t o₁
  let o₂ := reqR A nf t o₁ (simO (simR' simR) x₂ b.2.1.1)
  let s := progO progI (some ⟨t, A.ci⟩) b.1.1 (progO progR x₂ b.2.1.1 b.2.2)
  (A.out o₁ o₂ b.1.2 b.2.1.2 s, ext (stI A o₁) (stR A o₁ o₂) (A.out o₁ o₂) b.1.2 b.2.1.2 s)

/-- The redemption context of an operation (unused for issuance). -/
def crOf : UOp → Bytes
  | .issue _ _ => []
  | .redeem _ _ _ cr _ => cr

/-- **`B_k`, key recovery**: the simulated world's extracted key. -/
def keyB : OAdv (SimC CI CR G S) Bytes :=
  ⟨qry A simI, fun t nf b => keyOf (view A ext simI progI simR progR t nf b).2⟩

/-- **`B₁`, binding**: the honest opening and the extracted one. -/
def bindB (z : Sec × SimC CI CR G S) : UOpening × UOpening :=
  let v := (⟨qry A simI, fun t nf b => view A ext simI progI simR progR t nf b⟩ :
    OAdv (SimC CI CR G S) (UOp × Bytes)).run A.ci z
  ((List.ofFn z.1.1, A.ci, List.ofFn z.1.2), (keyOf v.2, ciOf v.1, rOf v.2))

/-- **`B₂`, key second preimage**: the extracted key and the operation's redemption context. -/
def sprB : OAdv (SimC CI CR G S) (Bytes × Bytes) :=
  ⟨qry A simI, fun t nf b =>
    let v := view A ext simI progI simR progR t nf b
    (keyOf v.2, crOf v.1)⟩

/-- **The collision term** `δ_R`: the real redemption proof, after the simulated issuance, reads
the tables differently with and without the issuance's programming. -/
def deltaR (z : (Sec × (CI × G)) × ((Coins proveSeedBytes × G) × S)) : Prop :=
  deltaG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω)) (specR A PR) z

/-- **The first hop's distinguisher**, as a function of the issuance proof. -/
def distI (ω : Sec) (r₂ : Coins proveSeedBytes) (g₂ : G) (p : Bytes) (g : G) (u : S) : Prop :=
  D₁ (specR A PR) (Bad A verI verR ext) ω r₂ g₂ (reqI (tOf A ω) (some p)) g u

/-- **The second hop's distinguisher**, as a function of the redemption proof. -/
def distR (ω : Sec) (c₁ : CI) (g₁ : G) (p : Bytes) (g : G) (u : S) : Prop :=
  D₂ (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω)) (Bad A verI verR ext)
    ω c₁ g₁ (reqR A (nfOf A ω (simIssP A simI (tOf A ω) c₁)) (tOf A ω)
      (simIssP A simI (tOf A ω) c₁) (some p)) g u

/-- The simulated game's components. -/
def smR (ω : Sec) (o₁ : Bytes) (c : CR) : Except Error Bytes :=
  simRedP A simR (nfOf A ω o₁) (tOf A ω) o₁ c
def pgR (ω : Sec) (o₁ : Bytes) (c : CR) (s : S) : S := pgRP A progR (nfOf A ω o₁) (tOf A ω) o₁ c s

/-- **The simulated game.** -/
def nmSim (Ev : Sec → Bytes → Except Error Bytes → G → G → S → Prop)
    (z : (Sec × (CI × G)) × ((CR × G) × S)) : Prop :=
  simG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω)) (smR A simR)
    (pgR A progR) Ev z

section Red

variable [Fintype CI] [Fintype CR] [Fintype G] [Fintype S]

/-- **The hit cases, per run**: a witness that hits the honest token (`t = UCom(k, ctx_iss, r)`)
carries the honest key, or breaks binding against the honest opening, or is a key second
preimage. -/
theorem hit_cases {k ci r : Bytes} (hk : k.length = nfKeyBytes) (hci : ci.length = ctxBytes)
    (hr : r.length = rBytes) {op : UOp} {w : Bytes} (h : HitOp (ucom k ci r) k op w) :
    keyOf w = k ∨ BindWin ((k, ci, r), (keyOf w, ciOf op, rOf w)) ∨ SprWin k (keyOf w, crOf op) := by
  by_cases hkw : keyOf w = k
  · exact Or.inl hkw
  rcases h with ⟨hR, hc, ho⟩ | ⟨hR, hn⟩
  · obtain ⟨h1, h2⟩ := relOp_len hR
    refine Or.inr (Or.inl ⟨fun e => hkw (congrArg Prod.fst e).symm, hk, hci, hr, h1, hc, h2, ho.symm⟩)
  · obtain ⟨h1, -⟩ := relOp_len hR
    rcases op with ⟨req, ci'⟩ | ⟨S', req, ci', cr, cd⟩
    · exact hn.elim
    · exact Or.inr (Or.inr ⟨h1, hkw, (relOp_nf hR).symm.trans hn⟩)

/-- **The hit step.** In the simulated world, a hit is a key recovery (`B_k`), a binding break
(`B₁`) or a key second preimage (`B₂`). -/
theorem sim_hit_le :
    pr ((Sec × (CI × G)) × ((CR × G) × S)) (nmSim A simI progI simR progR (hitE A ext)) ≤
      owkAdv A.ci (keyB A ext simI progI simR progR) +
        bindAdv (bindB A ext simI progI simR progR) +
        sprAdv A.ci (sprB A ext simI progI simR progR) := by
  rw [← pr_equiv (Equiv.prodAssoc Sec (CI × G) ((CR × G) × S)).symm]
  unfold owkAdv sprAdv bindAdv
  refine (pr_mono fun z hz => hit_cases (ci := A.ci) List.length_ofFn List.length_ofFn
    List.length_ofFn hz).trans ?_
  refine (pr_or_le _ _).trans ?_
  rw [add_assoc]
  exact add_le_add le_rfl (pr_or_le _ _)

omit [Fintype CI] [Fintype G] [Fintype S] in
theorem stI_simIss (t : Bytes) (ht : t.length = uovM) (c : CI) :
    stI A (simIssP A simI t c) = pairO (some ⟨t, A.ci⟩) (simO (simI' simI) (some ⟨t, A.ci⟩) c) := by
  simp only [stI, simIssP, reqI, simO, simI', pairO, Option.getD_some, stOfI, List.take_left' ht,
    List.drop_left' ht]

omit [Fintype CR] [Fintype G] [Fintype S] in
theorem stR_simRed (nf t req : Bytes) (hn : nf.length = nfBytes) (c : CR) :
    stR A req (simRedP A simR nf t req c) =
      pairO (xR A nf t req) (simO (simR' simR) (xR A nf t req) c) := by
  unfold simRedP reqR xR
  split_ifs
  · cases findIssuer (A.set req) t (sig A req) with
    | none => rfl
    | some i =>
      simp only [stR, simO, simR', pairO, Option.getD_some, stOfR, List.take_left' hn,
        List.drop_left' hn]
  · rfl

/-- The simulated game's `Acc ∧ Fresh ∧ ¬ Rel` part. -/
def seEv (ω : Sec) (o₁ : Bytes) (o₂ : Except Error Bytes) (g₁ g₂ : G) (s : S) : Prop :=
  accE A verI verR ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧ ¬ relE A ext ω o₁ o₂ g₁ g₂ s

/-- **Weak simulation-extractability step.** -/
theorem sim_se_le {AdmE : (G → G → S → UOp) → Prop} {εSE : ℝ}
    (hse : WeakSE2 (simI' simI) progI (simR' simR) progR (AccOp verI verR) FreshOp RelOp ext AdmE
      εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂)) :
    pr ((Sec × (CI × G)) × ((CR × G) × S)) (nmSim A simI progI simR progR (seEv A verI verR ext)) ≤
      εSE := by
  have h := hse Sec (fun ω => some ⟨tOf A ω, A.ci⟩)
    (fun ω π₁ => xR A (nfOf A ω (reqI (tOf A ω) π₁)) (tOf A ω) (reqI (tOf A ω) π₁))
    (fun ω π₁ π₂ => A.out (reqI (tOf A ω) π₁)
      (reqR A (nfOf A ω (reqI (tOf A ω) π₁)) (tOf A ω) (reqI (tOf A ω) π₁) π₂))
    fun _ _ _ => hAE _ _
  refine le_of_eq_of_le (pr_congr fun z => ?_) h
  have h1 := stI_simIss A simI (tOf A z.1.1) (length_ucom _ _ _) z.1.2.1
  have h2 := stR_simRed A simR (nfOf A z.1.1 (simIssP A simI (tOf A z.1.1) z.1.2.1)) (tOf A z.1.1)
    (simIssP A simI (tOf A z.1.1) z.1.2.1) (length_derive _ _) z.2.1.1
  simp only [nmSim, simG, seEv, accE, freshE, relE, smR, pgR, h1, h2]
  rfl

/-- **Unbound redemption non-malleability and no squatting (Theorems U4 and U3 together).** For
every adversary, with zero knowledge of both unbound proof systems at the hops' distinguishers,
weak simulation-extractability, and the PRF assumption for the key-recovery distinguishers:

    Pr[Bad] ≤ ε_I + ε_R + δ_R + ε_SE + (ε_prf + 2⁻¹⁹²) + Adv^bind(B₁) + Adv^spr-k(B₂). -/
theorem nmU [Nonempty CI] [Nonempty CR] [Nonempty G] [Nonempty S]
    {AdmI : (Bytes → G → S → Prop) → Prop} {AdmR : (Bytes → G → S → Prop) → Prop}
    {AdmE : (G → G → S → UOp) → Prop} {εI εR εSE εprf : ℝ}
    (hzkI : ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI AdmI εI)
    (hεI : 0 ≤ εI)
    (hzkR : ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmR εR)
    (hεR : 0 ≤ εR)
    (hAI : ∀ ω r₂ g₂, AdmI (distI A PR verI verR ext ω r₂ g₂))
    (hAR : ∀ ω c₁ g₁, AdmR (distR A verI verR ext simI progI ω c₁ g₁))
    (hse : WeakSE2 (simI' simI) progI (simR' simR) progR (AccOp verI verR) FreshOp RelOp ext AdmE
      εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂))
    (hprf : ∀ b, prf1Adv A.ci (owkD (keyB A ext simI progI simR progR) b) ≤ εprf) :
    pr _ (nmReal A PI PR verI verR ext) ≤
      εI + εR + pr _ (deltaR A PR simI progI) + εSE + (εprf + 1 / 2 ^ 192) +
        bindAdv (bindB A ext simI progI simR progR) +
        sprAdv A.ci (sprB A ext simI progI simR progR) := by
  have hzkI' : ZeroKnowledgeRO IssueRelW (PI' PI) (simI' simI) progI
      (fun D => AdmI (fun o g s => D (some o) g s)) εI :=
    hzkI.transfer id (fun _ w => w) (fun _ _ h => h) some (fun _ hD => hD)
  have hzkR' : ZeroKnowledgeRO RedeemRelW (PR' PR) (simR' simR) progR
      (fun D => AdmR (fun o g s => D (some o) g s)) εR :=
    hzkR.transfer id (fun _ w => w) (fun _ _ h => h) some (fun _ hD => hD)
  have h := theft_le (Ω := Sec) (ρ₁ := Coins proveSeedBytes) (ρ₂ := Coins proveSeedBytes)
    (C₁ := CI) (C₂ := CR) (G := G) (S := S) (specI A PI) (fun ω => simIssP A simI (tOf A ω))
    (fun ω => pgIP A progI (tOf A ω)) (specR A PR) (smR A simR) (pgR A progR)
    (accE A verI verR) (freshE A) (relE A ext) (hitE A ext) (ε₁ := εI) (ε₂ := εR)
    (fun ω r₂ g₂ => by
      have := zk_step hzkI' hεI (xwI A ω) (xwI_rel A ω) (reqI (tOf A ω))
        (D₁ (specR A PR) (Bad A verI verR ext) ω r₂ g₂) (fun _ _ _ => hAI ω r₂ g₂)
      rw [xwI_fst] at this
      simp only [specI_eq]
      exact this)
    (fun ω c₁ g₁ => by
      have := zk_step hzkR' hεR (xwR A ω (simIssP A simI (tOf A ω) c₁)) (xwR_rel A ω _)
        (reqR A (nfOf A ω (simIssP A simI (tOf A ω) c₁)) (tOf A ω) (simIssP A simI (tOf A ω) c₁))
        (D₂ (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω))
          (Bad A verI verR ext) ω c₁ g₁) (fun _ _ _ => hAR ω c₁ g₁)
      rw [xwR_fst] at this
      simp only [specR_eq]
      exact this)
  have hse' := sim_se_le A verI verR ext simI progI simR progR hse hAE
  have hhit := sim_hit_le A ext simI progI simR progR
  have hkey := owkAdv_le A.ci (keyB A ext simI progI simR progR) hprf
  have hd : pr ((Sec × (CI × G)) × ((Coins proveSeedBytes × G) × S)) (deltaR A PR simI progI) =
      pr ((Sec × (CI × G)) × ((Coins proveSeedBytes × G) × S))
        (deltaG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω))
          (specR A PR)) := rfl
  have hr : pr ((Sec × (Coins proveSeedBytes × G)) × ((Coins proveSeedBytes × G) × S))
      (nmReal A PI PR verI verR ext) =
      pr ((Sec × (Coins proveSeedBytes × G)) × ((Coins proveSeedBytes × G) × S))
        (realG (specI A PI) (specR A PR)
        (fun ω o₁ o₂ g₁ g₂ s => accE A verI verR ω o₁ o₂ g₁ g₂ s ∧ freshE A ω o₁ o₂ g₁ g₂ s ∧
          (¬ relE A ext ω o₁ o₂ g₁ g₂ s ∨ hitE A ext ω o₁ o₂ g₁ g₂ s))) :=
    rfl
  have e1 : pr ((Sec × (CI × G)) × ((CR × G) × S)) (nmSim A simI progI simR progR (seEv A verI verR ext)) =
      pr ((Sec × (CI × G)) × ((CR × G) × S))
        (simG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω)) (smR A simR)
          (pgR A progR) (fun ω o₁ o₂ g₁ g₂ s => accE A verI verR ω o₁ o₂ g₁ g₂ s ∧
            freshE A ω o₁ o₂ g₁ g₂ s ∧ ¬ relE A ext ω o₁ o₂ g₁ g₂ s)) := rfl
  have e2 : pr ((Sec × (CI × G)) × ((CR × G) × S)) (nmSim A simI progI simR progR (hitE A ext)) =
      pr ((Sec × (CI × G)) × ((CR × G) × S))
        (simG (fun ω => simIssP A simI (tOf A ω)) (fun ω => pgIP A progI (tOf A ω)) (smR A simR)
          (pgR A progR) (hitE A ext)) := rfl
  rw [hr, hd]
  rw [e1] at hse'
  rw [e2] at hhit
  linarith

/-- **Proposition U3 (no nullifier squatting)**: the probability that an accepted redemption with
a fresh statement carries the honest token's nullifier for its context is at most the bound of
`nmU`. -/
theorem noSquat [Nonempty CI] [Nonempty CR] [Nonempty G] [Nonempty S]
    {AdmI : (Bytes → G → S → Prop) → Prop} {AdmR : (Bytes → G → S → Prop) → Prop}
    {AdmE : (G → G → S → UOp) → Prop} {εI εR εSE εprf : ℝ}
    (hzkI : ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI AdmI εI)
    (hεI : 0 ≤ εI)
    (hzkR : ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmR εR)
    (hεR : 0 ≤ εR)
    (hAI : ∀ ω r₂ g₂, AdmI (distI A PR verI verR ext ω r₂ g₂))
    (hAR : ∀ ω c₁ g₁, AdmR (distR A verI verR ext simI progI ω c₁ g₁))
    (hse : WeakSE2 (simI' simI) progI (simR' simR) progR (AccOp verI verR) FreshOp RelOp ext AdmE
      εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂))
    (hprf : ∀ b, prf1Adv A.ci (owkD (keyB A ext simI progI simR progR) b) ≤ εprf) :
    pr _ (nmRealE A PI PR (Squat A verI verR)) ≤
      εI + εR + pr _ (deltaR A PR simI progI) + εSE + (εprf + 1 / 2 ^ 192) +
        bindAdv (bindB A ext simI progI simR progR) +
        sprAdv A.ci (sprB A ext simI progI simR progR) := by
  refine (pr_mono fun z hz => ?_).trans
    (nmU A PI PR verI verR ext simI progI simR progR hzkI hεI hzkR hεR hAI hAR hse hAE hprf)
  obtain ⟨ha, hf, hn⟩ := hz
  exact ⟨ha, hf, or_iff_not_imp_left.2 fun hr => Or.inr ⟨not_not.1 hr, hn⟩⟩

/-- **Theorem U4 (redemption non-malleability, no redirect to another digest, Anchor Set or
redemption context)**: the probability of `Redirect` is at most the bound of `nmU`. -/
theorem noRedirectU [Nonempty CI] [Nonempty CR] [Nonempty G] [Nonempty S]
    {AdmI : (Bytes → G → S → Prop) → Prop} {AdmR : (Bytes → G → S → Prop) → Prop}
    {AdmE : (G → G → S → UOp) → Prop} {εI εR εSE εprf : ℝ}
    (hzkI : ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI AdmI εI)
    (hεI : 0 ≤ εI)
    (hzkR : ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmR εR)
    (hεR : 0 ≤ εR)
    (hAI : ∀ ω r₂ g₂, AdmI (distI A PR verI verR ext ω r₂ g₂))
    (hAR : ∀ ω c₁ g₁, AdmR (distR A verI verR ext simI progI ω c₁ g₁))
    (hse : WeakSE2 (simI' simI) progI (simR' simR) progR (AccOp verI verR) FreshOp RelOp ext AdmE
      εSE)
    (hAE : ∀ o₁ o₂, AdmE (A.out o₁ o₂))
    (hprf : ∀ b, prf1Adv A.ci (owkD (keyB A ext simI progI simR progR) b) ≤ εprf) :
    pr _ (nmRealE A PI PR (Redirect A verI verR ext)) ≤
      εI + εR + pr _ (deltaR A PR simI progI) + εSE + (εprf + 1 / 2 ^ 192) +
        bindAdv (bindB A ext simI progI simR progR) +
        sprAdv A.ci (sprB A ext simI progI simR progR) := by
  refine (pr_mono fun z hz => ?_).trans
    (nmU A PI PR verI verR ext simI progI simR progR hzkI hεI hzkR hεR hAI hAR hse hAE hprf)
  exact (bad_iff A verI verR ext _ _ _ _ _ _).2 (by
    obtain ⟨ha, hf, ho⟩ := hz
    exact ⟨ha, hf, ho.imp id Or.inl⟩)

end Red

end VoleMole.Theft.MoussakaUnbound
