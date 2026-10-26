import VoleMole.Spec.Moussaka
import VoleMole.Arith.MoussakaUnbound

/-!
# Executable spec of unbound Moussaka tokens (PR #63)

The byte-level pieces of `src/moussaka/moussaka.cpp`, `unbound_issue.hpp` and `unbound_redeem.hpp`
that do not depend on the VOLEitH internals: the issue seed expansion, `UCom`, `Derive`, and the two
witness encodings. The Keccak inputs are `Arith.MoussakaUnbound.encodeUnboundComState` and
`encodeDeriveState` themselves, so `lake exe spec_kats` (which checks these functions against
`tests/moussaka/unbound_moussaka_kat.txt`) tests the encodings that the soundness and completeness
theorems of `Arith/MoussakaUnbound.lean` are stated over.
-/

namespace VoleMole.Spec.MoussakaUnbound

open VoleMole.Arith VoleMole.Spec

/-- A byte list as a function, zero beyond its end. -/
def fn (b : Bytes) : ℕ → UInt8 := fun i => b.getD i 0

/-- `NF_KEY_BYTES`. -/
def nfKeyBytes : ℕ := 16

/-- `UNBOUND_MOUSSAKA_ISSUE_SEED_DST`, `UNBOUND_MOUSSAKA_REDEEM_SEED_DST`. -/
def issueSeedDst : Bytes := makeDst "mous" 1 's' '0'
def redeemSeedDst : Bytes := makeDst "mous" 1 's' '1'

/-- `expand_unbound_issue_seed`: `nf_key ‖ r ‖ ρ_iss`. -/
def expandIssueSeed (seed : Bytes) : Bytes × Bytes × Bytes :=
  let o := shake128B (issueSeedDst ++ seed) (nfKeyBytes + Moussaka.rBytes + Moussaka.proveSeedBytes)
  (o.take nfKeyBytes, slice o nfKeyBytes Moussaka.rBytes,
    slice o (nfKeyBytes + Moussaka.rBytes) Moussaka.proveSeedBytes)

/-- `encode_unbound_com_state(nf_key, ctx_iss, r)`. -/
def ucomState (k ctxIss r : Bytes) : Keccak.State :=
  MoussakaUnbound.encodeUnboundComState (fn k) (fn ctxIss) (fn r)

/-- `encode_derive_state(nf_key, ctx_red)`. -/
def deriveState (k ctxRed : Bytes) : Keccak.State :=
  MoussakaUnbound.encodeDeriveState (fn k) (fn ctxRed)

/-- `UCom(nf_key, ctx_iss, r)`. -/
def ucom (k ctxIss r : Bytes) : Bytes := (Keccak.keccakP800 (ucomState k ctxIss r)).toList.take uovM

/-- `Derive(nf_key, ctx_red)`. -/
def derive (k ctxRed : Bytes) : Bytes :=
  (Keccak.keccakP800 (deriveState k ctxRed)).toList.take Moussaka.nfBytes

theorem length_ucom (k ctxIss r : Bytes) : (ucom k ctxIss r).length = uovM := by
  simp [ucom, uovM]

theorem length_derive (k ctxRed : Bytes) : (derive k ctxRed).length = Moussaka.nfBytes := by
  simp [derive, Moussaka.nfBytes]

/-- `encode_unbound_issue_witness`: `r ‖ nf_key ‖ s5 ‖ s9` (232 bytes). -/
def encodeIssueWitness (k ctxIss r : Bytes) : Bytes :=
  r ++ k ++ Moussaka.committedStates (ucomState k ctxIss r)

/-- `encode_unbound_redeem_witness`: `r ‖ nf_key ‖ s ‖ (s5 ‖ s9 of UCom) ‖ (s5 ‖ s9 of Derive) ‖ b`
(559 bytes). -/
def encodeRedeemWitness (k ctxIss ctxRed r s : Bytes) (i : ℕ) : Bytes :=
  r ++ k ++ s ++ Moussaka.committedStates (ucomState k ctxIss r) ++
    Moussaka.committedStates (deriveState k ctxRed) ++ Moussaka.selector i

/-- The byte spec's `UCom` is the Arith model's, component by component. -/
theorem ucom_getD (k ctxIss r : Bytes) (j : Fin uovM) :
    (ucom k ctxIss r).getD j.val 0 = VoleMole.Arith.MoussakaUnbound.ucom (fn k) (fn ctxIss) (fn r) j := by
  have hj := j.isLt
  simp [ucom, VoleMole.Arith.MoussakaUnbound.ucom, ucomState, uovM] at *

/-- The byte spec's `Derive` is the Arith model's, component by component. -/
theorem derive_getD (k ctxRed : Bytes) (j : Fin MoussakaUnbound.NF) :
    (derive k ctxRed).getD j.val 0 = VoleMole.Arith.MoussakaUnbound.derive (fn k) (fn ctxRed) j := by
  have hj := j.isLt
  simp [derive, VoleMole.Arith.MoussakaUnbound.derive, deriveState, Moussaka.nfBytes] at *

/-! ## The protocol -/

open VoleMole.Spec.Moussaka (NIZK AnchorSet Error)

/-- `UNBOUND_ISSUE_PROOF_BYTES`, `UNBOUND_REDEEM_PROOF_BYTES`. -/
abbrev issueProofBytes : ℕ := 6864
abbrev redeemProofBytes : ℕ := 12423

/-- `expand_redeem_seed<UnboundRedeemRelation>(seed, UNBOUND_MOUSSAKA_REDEEM_SEED_DST)`. -/
def expandRedeemSeed (seed : Bytes) : Bytes := shake128B (redeemSeedDst ++ seed) Moussaka.proveSeedBytes

structure IssueInstance where
  t : Bytes
  ctxIss : Bytes

/-- `UnboundIssueRelation::hash_instance`: `t ‖ ctx_iss`. -/
def IssueInstance.encode (x : IssueInstance) : Bytes := x.t ++ x.ctxIss

structure RedeemInstance where
  anchors : List UOVKey
  nf : Bytes
  ctxIss : Bytes
  ctxRed : Bytes
  challengeDigest : Bytes

/-- The unbound issuance relation: the witness encodes some `(nf_key, r)` with
`t = UCom(nf_key, ctx_iss, r)` (soundness of the constraints: `Arith.MoussakaUnbound.uIssue_sound`). -/
def IssueRel (x : IssueInstance) (w : Bytes) : Prop :=
  ∃ k r, k.length = nfKeyBytes ∧ r.length = Moussaka.rBytes ∧
    w = encodeIssueWitness k x.ctxIss r ∧ x.t = ucom k x.ctxIss r

/-- The unbound redemption relation: for some Anchor `u` of the set, `P_u(s) = UCom(nf_key, ctx_iss,
r)`, and `nf = Derive(nf_key, ctx_red)` (`Arith.MoussakaUnbound.uRedeem_sound_card`). -/
def RedeemRel (x : RedeemInstance) (w : Bytes) : Prop :=
  ∃ k r s u pk, k.length = nfKeyBytes ∧ r.length = Moussaka.rBytes ∧ s.length = uovN ∧
    x.anchors[u]? = some pk ∧ w = encodeRedeemWitness k x.ctxIss x.ctxRed r s u ∧
    pk.eval s = ucom k x.ctxIss r ∧ x.nf = derive k x.ctxRed

/-- `PendingUnboundToken`. -/
structure PendingToken where
  k : Bytes
  r : Bytes
  ctxIss : Bytes
  t : Bytes

/-- `UnboundToken`: `(nf_key, r, s)`; not bound to a redemption context. -/
structure Token where
  k : Bytes
  r : Bytes
  s : Bytes

/-- `detail::unbound_issue_request_with_seed(ctx_iss, seed)`. -/
def issueRequest (PI : NIZK IssueInstance) (ctxIss seed : Bytes) : PendingToken × Bytes :=
  let (k, r, rho) := expandIssueSeed seed
  let t := ucom k ctxIss r
  (⟨k, r, ctxIss, t⟩, t ++ PI.prove (encodeIssueWitness k ctxIss r) ⟨t, ctxIss⟩ rho)

/-- `PendingUnboundToken::finalize_issue(pk, s)`. -/
def finalizeIssue (pk : UOVKey) (p : PendingToken) (s : Bytes) : Option Token :=
  if pk.eval s = p.t then some ⟨p.k, p.r, s⟩ else none

/-- `find_issuer(anchors, t, s)` (`moussaka.cpp:120-139`): the bound Client's search
(`Spec.Moussaka.findIssuer`), the last index `u` with `P_u(s) = t`, or `none`. -/
abbrev findIssuer : AnchorSet → Bytes → Bytes → Option ℕ := Moussaka.findIssuer

theorem findIssuer_some {A : AnchorSet} {t s : Bytes} {i : ℕ} (h : findIssuer A t s = some i) :
    ∃ pk : UOVKey, A.keys[i]? = some pk ∧ pk.eval s = t := Moussaka.findIssuer_some h

theorem findIssuer_isSome {A : AnchorSet} {t s : Bytes} :
    (findIssuer A t s).isSome ↔ ∃ i : ℕ, ∃ pk : UOVKey, A.keys[i]? = some pk ∧ pk.eval s = t :=
  Moussaka.findIssuer_isSome

/-- `detail::unbound_redeem_request_with_seed(token, anchors, ctx_iss, ctx_red, challenge_digest,
seed)`: the Client finds its Anchor itself; `nf = Derive(nf_key, ctx_red)`. -/
def redeemRequest (PR : NIZK RedeemInstance) (tok : Token) (A : AnchorSet)
    (ctxIss ctxRed cd seed : Bytes) : Except Error Bytes :=
  match findIssuer A (ucom tok.k ctxIss tok.r) tok.s with
  | none => .error .invalidToken
  | some i =>
    .ok (derive tok.k ctxRed ++ PR.prove (encodeRedeemWitness tok.k ctxIss ctxRed tok.r tok.s i)
      ⟨A.keys, derive tok.k ctxRed, ctxIss, ctxRed, cd⟩ (expandRedeemSeed seed))

/-- `unbound_finalize_redeem(anchors, request, ctx_iss, ctx_red, challenge_digest)`. -/
def finalizeRedeem (VR : NIZK RedeemInstance) (A : AnchorSet) (req ctxIss ctxRed cd : Bytes) :
    Option Bytes :=
  if req.length ≠ Moussaka.nfBytes + redeemProofBytes then none else
  let nf := req.take Moussaka.nfBytes
  if VR.verify (req.drop Moussaka.nfBytes) ⟨A.keys, nf, ctxIss, ctxRed, cd⟩ then some nf else none

end VoleMole.Spec.MoussakaUnbound
