import VoleMole.Spec.Common

/-!
# Executable protocol spec of Moussaka (`src/moussaka/*`, `include/vole_mole/moussaka.hpp`)

## What is modelled

* Message formats: `IssueRequest = t ‖ π_iss` (`45 + 7272` bytes), `IssueResponse = s` (119),
  `RedeemRequest = nf ‖ π_red` (`24 + 8751`), and the field sizes of `moussaka.hpp:24-36`.
* Client randomness: `nf ‖ r ‖ ρ_iss = SHAKE128(ISSUE_SEED_DST ‖ seed)` and
  `ρ_red = SHAKE128(REDEEM_SEED_DST ‖ seed')` (`moussaka.cpp:58-85`).
* The commitment `Com(nf, ctx_iss, ctx_red, r) = KP800(state)[0..45)` with the 100-byte state of
  `commit.hpp:33-48` (`comState`), using `Arith.Keccak.keccakP800`.
* The witness layouts (`encode_issue_witness`, `issue.hpp:90-103`; `encode_redeem_witness`,
  `redeem.hpp:110-124`), including the committed Keccak states `s5`, `s9`
  (`keccak/segmented.hpp:113-119`) and the 64-bit one-hot selector.
* The proof instances as hashed by `hash_instance` (`issue.hpp:164-167`, `redeem.hpp:182-200`),
  and the relations the constraint systems are proved (in `Arith/Moussaka.lean`) to enforce.
* Every step: `issueRequest`, `issueResponse` (Anchor), `finalizeIssue`, `redeemRequest` (the
  Client finds its issuer itself, `findIssuer`, `moussaka.cpp:184-219`; the index-taking step of
  the API before `21be618` is `redeemRequestAt`, `redeemRequest_eq_at`), `finalizeRedeem` (Moderator,
  `:276-287`), the `AnchorSet` constructor's validation (`:138-152`), and a Moderator that keeps
  one nullifier record per `(ctx_iss, ctx_red)` across all Anchor Sets, as `moussaka.hpp:136-146`
  requires of the caller.
* UOV verification `P(s) = t` concretely (`UOVKey.eval`).

## What is abstract

* VOLEitH prove/verify (`NIZK`), with completeness for the relation (`NIZK.Correct`).
* UOV preimage derivation (`Signer`). Constant-time behaviour, moved-from objects, and lengths
  that C++ `std::array` types enforce (reported here as `malformed`, or as a rejection).

## Results

* `honest_run_redeems`: correctness (issue, finalize, redeem under any Anchor Set containing the
  issuer, Moderator acceptance).
* `run_accepted_nodup`, `run_accepted_ctx_nodup`: the Moderator accepts each nullifier at most once
  per `(ctx_iss, ctx_red)`, over any sequence of requests and Anchor Sets.
* `redeemEncode_inj`, `redeemEncode_ne_of_challengeDigest`, `issueEncode_inj`, `comState_inj`:
  instance and commitment encodings parse uniquely (redemption is bound to `challenge_digest`,
  the Anchor Set, `nf` and both contexts; the commitment input determines all of its fields).
* Input validation: `redeemRequest_invalidToken`, `redeemRequestAt_index`, `finalizeIssue_none_iff`,
  `issueResponse_none_iff`, `finalizeRedeem_some`, `AnchorSet.mk?_valid`.
-/

namespace VoleMole.Spec.Moussaka

open VoleMole.Arith

/-! ## Constants -/

def comDst : Bytes := makeDst "mous" 0 'c' '0'
def issueSeedDst : Bytes := makeDst "mous" 0 's' '0'
def redeemSeedDst : Bytes := makeDst "mous" 0 's' '1'

#guard comDst = [0x6d, 0x6f, 0x75, 0x73, 0x00, 0x63, 0x30]

abbrev nfBytes : ℕ := 24
abbrev ctxBytes : ℕ := 16
abbrev rBytes : ℕ := 16
abbrev cdBytes : ℕ := 32
abbrev proveSeedBytes : ℕ := 16
abbrev maxAnchors : ℕ := 64
abbrev issueProofBytes : ℕ := 7272
abbrev redeemProofBytes : ℕ := 8751
abbrev issueRequestBytes : ℕ := uovM + issueProofBytes
abbrev redeemRequestBytes : ℕ := nfBytes + redeemProofBytes

/-! ## Randomness, commitment, witnesses -/

/-- `expand_issue_seed`: `nf ‖ r ‖ ρ_iss`. -/
def expandIssueSeed (seed : Bytes) : Bytes × Bytes × Bytes :=
  let o := shake128B (issueSeedDst ++ seed) (nfBytes + rBytes + proveSeedBytes)
  (o.take nfBytes, slice o nfBytes rBytes, slice o (nfBytes + rBytes) proveSeedBytes)

/-- `expand_redeem_seed`: `ρ_red`. -/
def expandRedeemSeed (seed : Bytes) : Bytes := shake128B (redeemSeedDst ++ seed) proveSeedBytes

/-- `encode_com_state(nf, ctx_iss, ctx_red, r)`:
`DST ‖ r ‖ 0⁹ ‖ ctx_iss ‖ ctx_red ‖ nf ‖ 0¹²`. -/
def comState (nf ctxIss ctxRed r : Bytes) : Bytes :=
  comDst ++ r ++ List.replicate 9 0 ++ ctxIss ++ ctxRed ++ nf ++ List.replicate 12 0

/-- `Com(nf, ctx_iss, ctx_red, r)`. -/
def com (nf ctxIss ctxRed r : Bytes) : Bytes :=
  (Keccak.keccakP800 (stateOfBytes (comState nf ctxIss ctxRed r))).toList.take uovM

/-- `encode_committed_states`: the states after rounds 5 and 9. -/
def committedStates (x : Keccak.State) : Bytes :=
  let s5 := Keccak.keccakP800Rounds 0 5 x
  let s9 := Keccak.keccakP800Rounds 5 4 s5
  s5.toList ++ s9.toList

/-- `encode_issue_witness`: `r ‖ ctx_red ‖ nf ‖ s5 ‖ s9` (256 bytes). -/
def encodeIssueWitness (nf ctxIss ctxRed r : Bytes) : Bytes :=
  r ++ ctxRed ++ nf ++ committedStates (stateOfBytes (comState nf ctxIss ctxRed r))

/-- The selector `b`: bit `i` of the 8 bytes set (`selector_bit`). -/
def selector (i : ℕ) : Bytes :=
  (List.range (maxAnchors / 8)).map fun j => if i / 8 = j then ((1 : UInt8) <<< (i % 8).toUInt8) else 0

/-- `encode_redeem_witness`: `r ‖ s ‖ s5 ‖ s9 ‖ b` (343 bytes). -/
def encodeRedeemWitness (nf ctxIss ctxRed r s : Bytes) (i : ℕ) : Bytes :=
  r ++ s ++ committedStates (stateOfBytes (comState nf ctxIss ctxRed r)) ++ selector i

theorem length_com (nf ctxIss ctxRed r : Bytes) : (com nf ctxIss ctxRed r).length = uovM := by
  simp [com, uovM]

/-! ## Instances, relations, the abstract proof system -/

structure IssueInstance where
  t : Bytes
  ctxIss : Bytes

/-- `IssueRelation::hash_instance`: `t ‖ ctx_iss`. -/
def IssueInstance.encode (x : IssueInstance) : Bytes := x.t ++ x.ctxIss

structure RedeemInstance where
  anchors : List UOVKey
  nf : Bytes
  ctxIss : Bytes
  ctxRed : Bytes
  challengeDigest : Bytes

/-- `RedeemRelation::hash_instance`:
`⟨64⟩₄ ‖ ⟨n⟩₄ ‖ dig(P₀) ‖ … ‖ dig(P_{n-1}) ‖ nf ‖ ctx_iss ‖ ctx_red ‖ challenge_digest`. -/
def RedeemInstance.encode (x : RedeemInstance) : Bytes :=
  u32le maxAnchors ++ u32le x.anchors.length ++ (x.anchors.map (·.digest)).flatten ++ x.nf ++
    x.ctxIss ++ x.ctxRed ++ x.challengeDigest

/-- The issuance relation: the witness is the encoding of some `(nf, r, ctx_red)` whose commitment
is `t` (`issue.hpp:1-21`; soundness of the constraints in `Arith/Moussaka.lean`). -/
def IssueRel (x : IssueInstance) (w : Bytes) : Prop :=
  ∃ nf r ctxRed, nf.length = nfBytes ∧ r.length = rBytes ∧ ctxRed.length = ctxBytes ∧
    w = encodeIssueWitness nf x.ctxIss ctxRed r ∧ x.t = com nf x.ctxIss ctxRed r

/-- The redemption relation: for some Anchor `u` of the set, `P_u(s) = Com(nf, ctx_iss, ctx_red, r)`
(`redeem.hpp:1-36`). -/
def RedeemRel (x : RedeemInstance) (w : Bytes) : Prop :=
  ∃ r s u pk, r.length = rBytes ∧ s.length = uovN ∧ x.anchors[u]? = some pk ∧
    w = encodeRedeemWitness x.nf x.ctxIss x.ctxRed r s u ∧ pk.eval s = com x.nf x.ctxIss x.ctxRed r

/-- An abstract NIZK for instances `I`: `voleith_prove(proof, witness, instance, rho)` and
`voleith_verify(proof, instance)`. -/
structure NIZK (I : Type) where
  prove : Bytes → I → Bytes → Bytes
  verify : Bytes → I → Bool

/-- Completeness and proof length. -/
def NIZK.Correct {I : Type} (R : I → Bytes → Prop) (pfBytes : ℕ) (Z : NIZK I) : Prop :=
  ∀ x w rho, R x w → rho.length = proveSeedBytes →
    (Z.prove w x rho).length = pfBytes ∧ Z.verify (Z.prove w x rho) x = true

/-! ## The Anchor Set -/

def AnchorSet.Valid (keys : List UOVKey) : Prop :=
  keys ≠ [] ∧ keys.length ≤ maxAnchors ∧ (keys.map (·.digest)).Nodup

/-- `AnchorSet`: a validated list of Anchor keys. -/
structure AnchorSet where
  keys : List UOVKey
  valid : AnchorSet.Valid keys

inductive Error where
  | malformed
  | deriveFailed
  | anchorSetSize
  | duplicateAnchor
  | indexOutOfRange
  | invalidToken
  deriving DecidableEq, Repr

/-- The `AnchorSet` constructor (`std::invalid_argument` on a bad size or a repeated key). -/
def AnchorSet.mk? (keys : List UOVKey) : Except Error AnchorSet :=
  if h1 : keys ≠ [] ∧ keys.length ≤ maxAnchors then
    if h2 : (keys.map (·.digest)).Nodup then .ok ⟨keys, h1.1, h1.2, h2⟩
    else .error .duplicateAnchor
  else .error .anchorSetSize

theorem AnchorSet.mk?_valid {keys : List UOVKey} {A : AnchorSet} (h : AnchorSet.mk? keys = .ok A) :
    A.keys = keys := by
  unfold AnchorSet.mk? at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

theorem AnchorSet.mk?_ok_iff (keys : List UOVKey) :
    (∃ A, AnchorSet.mk? keys = .ok A) ↔ AnchorSet.Valid keys := by
  unfold AnchorSet.mk? AnchorSet.Valid
  constructor
  · rintro ⟨A, h⟩
    split at h
    · split at h
      · rename_i h1 h2; exact ⟨h1.1, h1.2, h2⟩
      · cases h
    · cases h
  · rintro ⟨h1, h2, h3⟩
    simp [h1, h2, h3]

/-! ## The protocol -/

structure PendingToken where
  nf : Bytes
  r : Bytes
  ctxIss : Bytes
  ctxRed : Bytes
  t : Bytes

structure Token where
  nf : Bytes
  r : Bytes
  s : Bytes

/-- `detail::issue_request_with_seed(ctx_iss, ctx_red, seed)`. -/
def issueRequest (PI : NIZK IssueInstance) (ctxIss ctxRed seed : Bytes) : PendingToken × Bytes :=
  let (nf, r, rho) := expandIssueSeed seed
  let t := com nf ctxIss ctxRed r
  let pf := PI.prove (encodeIssueWitness nf ctxIss ctxRed r) ⟨t, ctxIss⟩ rho
  (⟨nf, r, ctxIss, ctxRed, t⟩, t ++ pf)

/-- `issue_response(sk, request, ctx_iss)`; `.ok none` is `std::nullopt` (invalid proof). -/
def issueResponse (PI : NIZK IssueInstance) (sk : Signer) (req ctxIss : Bytes) :
    Except Error (Option Bytes) :=
  if req.length ≠ issueRequestBytes ∨ ctxIss.length ≠ ctxBytes then .error .malformed else
  let t := req.take uovM
  if PI.verify (req.drop uovM) ⟨t, ctxIss⟩ then
    match sk.derivePreimage t with
    | some s => .ok (some s)
    | none => .error .deriveFailed
  else .ok none

/-- `PendingToken::finalize_issue(pk, s)`. -/
def finalizeIssue (pk : UOVKey) (p : PendingToken) (s : Bytes) : Option Token :=
  if pk.eval s = p.t then some ⟨p.nf, p.r, s⟩ else none

/-- The redemption step of the API before `21be618`, where the caller passes the issuer's index `i`
(`redeem_request_with_seed(token, anchors, i, …)`): out of range is `indexOutOfRange`, a key that
does not verify the token `invalidToken`. `redeemRequest` is this step at the index `findIssuer`
returns (`redeemRequest_eq_at`); the privacy games parametrized by an index rule
(`Privacy/Moussaka*.lean`) are stated for it. -/
def redeemRequestAt (PR : NIZK RedeemInstance) (tok : Token) (A : AnchorSet) (i : ℕ)
    (ctxIss ctxRed cd seed : Bytes) : Except Error Bytes :=
  match A.keys[i]? with
  | none => .error .indexOutOfRange
  | some pk =>
    if pk.eval tok.s = com tok.nf ctxIss ctxRed tok.r then
      .ok (tok.nf ++ PR.prove (encodeRedeemWitness tok.nf ctxIss ctxRed tok.r tok.s i)
        ⟨A.keys, tok.nf, ctxIss, ctxRed, cd⟩ (expandRedeemSeed seed))
    else .error .invalidToken

/-- `find_issuer` (`moussaka.cpp:192-209`, the loop of `redeem_request_with_seed`): the last
index `u` with `P_u(s) = t`, or `none` (`std::invalid_argument("Moussaka: invalid token")`). -/
def findIssuer (A : AnchorSet) (t s : Bytes) : Option ℕ :=
  ((List.range A.keys.length).filter fun u => decide (A.keys[u]?.map (·.eval s) = some t)).getLast?

theorem findIssuer_some {A : AnchorSet} {t s : Bytes} {i : ℕ} (h : findIssuer A t s = some i) :
    ∃ pk : UOVKey, A.keys[i]? = some pk ∧ pk.eval s = t := by
  have hm := List.mem_of_getLast? h
  simp only [List.mem_filter, decide_eq_true_eq] at hm
  obtain ⟨-, he⟩ := hm
  cases hk : A.keys[i]? with
  | none => simp [hk] at he
  | some pk => simp only [hk, Option.map_some, Option.some.injEq] at he; exact ⟨pk, rfl, he⟩

theorem findIssuer_isSome {A : AnchorSet} {t s : Bytes} :
    (findIssuer A t s).isSome ↔ ∃ i : ℕ, ∃ pk : UOVKey, A.keys[i]? = some pk ∧ pk.eval s = t := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 h
    exact ⟨i, findIssuer_some hi⟩
  · rintro ⟨i, pk, hk, he⟩
    have hi : i < A.keys.length := (List.getElem?_eq_some_iff.1 hk).1
    unfold findIssuer
    rw [Option.isSome_iff_ne_none, Ne, List.getLast?_eq_none_iff, ← Ne, ← List.length_pos_iff]
    refine List.length_pos_of_mem (a := i) ?_
    have : A.keys[i] = pk := (List.getElem?_eq_some_iff.1 hk).2
    simp [hi, this, he]

/-- `detail::redeem_request_with_seed(token, anchors, ctx_iss, ctx_red, challenge_digest, seed)`
(`moussaka.cpp:184-219`): the Client finds its issuer's index itself (`findIssuer`, the last key
that verifies the token) and rejects the token if no key does. -/
def redeemRequest (PR : NIZK RedeemInstance) (tok : Token) (A : AnchorSet)
    (ctxIss ctxRed cd seed : Bytes) : Except Error Bytes :=
  match findIssuer A (com tok.nf ctxIss ctxRed tok.r) tok.s with
  | none => .error .invalidToken
  | some i =>
    .ok (tok.nf ++ PR.prove (encodeRedeemWitness tok.nf ctxIss ctxRed tok.r tok.s i)
      ⟨A.keys, tok.nf, ctxIss, ctxRed, cd⟩ (expandRedeemSeed seed))

/-- **The bridge to the index-taking step**: where `findIssuer` succeeds, `redeemRequest` is
`redeemRequestAt` at the index it returns. -/
theorem redeemRequest_eq_at (PR : NIZK RedeemInstance) (tok : Token) (A : AnchorSet) (i : ℕ)
    (ctxIss ctxRed cd seed : Bytes) (h : findIssuer A (com tok.nf ctxIss ctxRed tok.r) tok.s = some i) :
    redeemRequest PR tok A ctxIss ctxRed cd seed = redeemRequestAt PR tok A i ctxIss ctxRed cd seed := by
  obtain ⟨pk, hk, he⟩ := findIssuer_some h
  simp [redeemRequest, redeemRequestAt, h, hk, he]

/-- No key of the set verifies the token: rejected (`std::invalid_argument`), before any proving. -/
theorem redeemRequest_invalidToken (PR : NIZK RedeemInstance) (tok : Token) (A : AnchorSet)
    (ctxIss ctxRed cd seed : Bytes)
    (h : ∀ pk ∈ A.keys, pk.eval tok.s ≠ com tok.nf ctxIss ctxRed tok.r) :
    redeemRequest PR tok A ctxIss ctxRed cd seed = .error .invalidToken := by
  cases hf : findIssuer A (com tok.nf ctxIss ctxRed tok.r) tok.s with
  | none => simp [redeemRequest, hf]
  | some i =>
    obtain ⟨pk, hk, he⟩ := findIssuer_some hf
    exact absurd he (h pk (List.mem_of_getElem? hk))

/-- `finalize_redeem(anchors, request, ctx_iss, ctx_red, challenge_digest)`. -/
def finalizeRedeem (VR : NIZK RedeemInstance) (A : AnchorSet) (req ctxIss ctxRed cd : Bytes) :
    Option Bytes :=
  if req.length ≠ redeemRequestBytes then none else
  let nf := req.take nfBytes
  if VR.verify (req.drop nfBytes) ⟨A.keys, nf, ctxIss, ctxRed, cd⟩ then some nf else none

/-! ## The Moderator's double-spend bookkeeping -/

/-- The Moderator: one record `(ctx_iss, ctx_red, nf)` per accepted redemption, shared by all
Anchor Sets. -/
structure Moderator where
  spent : List (Bytes × Bytes × Bytes)

/-- A redemption query. -/
structure Query where
  anchors : AnchorSet
  req : Bytes
  ctxIss : Bytes
  ctxRed : Bytes
  challengeDigest : Bytes

/-- Verify, then reject a recorded nullifier, else record it. -/
def Moderator.step (VR : NIZK RedeemInstance) (m : Moderator) (q : Query) :
    Option Bytes × Moderator :=
  match finalizeRedeem VR q.anchors q.req q.ctxIss q.ctxRed q.challengeDigest with
  | none => (none, m)
  | some nf =>
    if (q.ctxIss, q.ctxRed, nf) ∈ m.spent then (none, m)
    else (some nf, ⟨(q.ctxIss, q.ctxRed, nf) :: m.spent⟩)

/-- Run a sequence of queries; returns the accepted records in order, and the final state. -/
def run (VR : NIZK RedeemInstance) : Moderator → List Query → List (Bytes × Bytes × Bytes) × Moderator
  | m, [] => ([], m)
  | m, q :: qs =>
    let (o, m') := m.step VR q
    let (acc, mf) := run VR m' qs
    (match o with
      | some nf => (q.ctxIss, q.ctxRed, nf) :: acc
      | none => acc, mf)

theorem run_spent (VR : NIZK RedeemInstance) :
    ∀ (m : Moderator) (qs : List Query), m.spent.Nodup →
      (run VR m qs).2.spent = (run VR m qs).1.reverse ++ m.spent ∧ (run VR m qs).2.spent.Nodup
  | m, [], h => by simp [run, h]
  | m, q :: qs, h => by
    simp only [run]
    unfold Moderator.step
    split
    · exact run_spent VR m qs h
    · rename_i nf _
      split
      · exact run_spent VR m qs h
      · rename_i hmem
        obtain ⟨h1, h2⟩ := run_spent VR ⟨(q.ctxIss, q.ctxRed, nf) :: m.spent⟩ qs
          (List.nodup_cons.2 ⟨hmem, h⟩)
        refine ⟨?_, h2⟩
        rw [h1]; simp

/-- **Double-spend detection.** Starting from no records, the accepted records are pairwise
distinct (and distinct from any initial records). -/
theorem run_accepted_nodup (VR : NIZK RedeemInstance) (m : Moderator) (qs : List Query)
    (h : m.spent.Nodup) : (run VR m qs).1.Nodup := by
  obtain ⟨h1, h2⟩ := run_spent VR m qs h
  rw [h1] at h2
  exact List.nodup_reverse.1 (List.Nodup.of_append_left h2)

/-- Per context: the nullifiers accepted for `(ctx_iss, ctx_red)` are distinct, whatever Anchor
Sets the queries use. -/
theorem run_accepted_ctx_nodup (VR : NIZK RedeemInstance) (qs : List Query) (ci cr : Bytes) :
    (((run VR ⟨[]⟩ qs).1.filter (fun t => t.1 = ci ∧ t.2.1 = cr)).map (·.2.2)).Nodup := by
  have h := (run_accepted_nodup VR ⟨[]⟩ qs List.nodup_nil).filter (fun t => t.1 = ci ∧ t.2.1 = cr)
  refine h.map_on ?_
  intro a ha b hb hab
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp only at ha hb hab
  rw [ha.2.1, ha.2.2, hb.2.1, hb.2.2, hab]

/-! ## Lengths -/

theorem length_expandIssueSeed (seed : Bytes) :
    (expandIssueSeed seed).1.length = nfBytes ∧ (expandIssueSeed seed).2.1.length = rBytes ∧
    (expandIssueSeed seed).2.2.length = proveSeedBytes := by
  simp [expandIssueSeed, slice, length_shake128B, nfBytes, rBytes, proveSeedBytes]

theorem length_expandRedeemSeed (seed : Bytes) :
    (expandRedeemSeed seed).length = proveSeedBytes := length_shake128B _ _

/-! ## Correctness -/

/-- **Correctness.** With complete proof systems and a correct signer that answers, an honest
issuance yields a token, and redeeming it under any Anchor Set whose `i`-th key is the issuer's
produces a request that the Moderator accepts (from no records), returning the token's
nullifier. -/
theorem honest_run_redeems (PI : NIZK IssueInstance) (PR : NIZK RedeemInstance)
    (hPI : PI.Correct IssueRel issueProofBytes) (hPR : PR.Correct RedeemRel redeemProofBytes)
    (pk : UOVKey) (sk : Signer) (hsk : sk.Correct pk) (ctxIss ctxRed seed seed' cd : Bytes)
    (hci : ctxIss.length = ctxBytes) (hcr : ctxRed.length = ctxBytes)
    (s : Bytes) (hs : sk.derivePreimage (issueRequest PI ctxIss ctxRed seed).1.t = some s)
    (A : AnchorSet) (i : ℕ) (hA : A.keys[i]? = some pk) :
    issueResponse PI sk (issueRequest PI ctxIss ctxRed seed).2 ctxIss = .ok (some s) ∧
    ∃ tok, finalizeIssue pk (issueRequest PI ctxIss ctxRed seed).1 s = some tok ∧
      tok.nf = (expandIssueSeed seed).1 ∧
      ∃ req, redeemRequest PR tok A ctxIss ctxRed cd seed' = .ok req ∧
        finalizeRedeem PR A req ctxIss ctxRed cd = some tok.nf ∧
        (Moderator.step PR ⟨[]⟩ ⟨A, req, ctxIss, ctxRed, cd⟩).1 = some tok.nf := by
  obtain ⟨hl1, hl2, hl3⟩ := length_expandIssueSeed seed
  set e := expandIssueSeed seed with he
  obtain ⟨nf, r, rho⟩ := e
  simp only at hl1 hl2 hl3
  generalize ht : com nf ctxIss ctxRed r = t
  have htl : t.length = uovM := ht ▸ length_com _ _ _ _
  have hrel : IssueRel ⟨t, ctxIss⟩ (encodeIssueWitness nf ctxIss ctxRed r) :=
    ⟨nf, r, ctxRed, hl1, hl2, hcr, rfl, ht.symm⟩
  obtain ⟨hpl, hpv⟩ := hPI _ _ rho hrel hl3
  have hreq : issueRequest PI ctxIss ctxRed seed =
      (⟨nf, r, ctxIss, ctxRed, t⟩, t ++ PI.prove (encodeIssueWitness nf ctxIss ctxRed r) ⟨t, ctxIss⟩ rho) := by
    simp only [issueRequest, ← he, ht]
  rw [hreq] at hs ⊢
  simp only at hs
  obtain ⟨hsl, hev⟩ := hsk _ _ htl hs
  have hev' : pk.eval s = com nf ctxIss ctxRed r := hev.trans ht.symm
  refine ⟨?_, ⟨nf, r, s⟩, ?_, rfl, ?_⟩
  · simp [issueResponse, hci, htl, hpl, take_append_eq htl, drop_append_eq htl, hpv, hs]
  · simp [finalizeIssue, hev]
  · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1
      (findIssuer_isSome.2 ⟨i, pk, hA, hev'⟩ : (findIssuer A (com nf ctxIss ctxRed r) s).isSome)
    obtain ⟨pk', hA', hev''⟩ := findIssuer_some hj
    have hrel2 : RedeemRel ⟨A.keys, nf, ctxIss, ctxRed, cd⟩
        (encodeRedeemWitness nf ctxIss ctxRed r s j) := ⟨r, s, j, pk', hl2, hsl, hA', rfl, hev''⟩
    obtain ⟨hpl2, hpv2⟩ := hPR _ _ _ hrel2 (length_expandRedeemSeed seed')
    refine ⟨nf ++ PR.prove (encodeRedeemWitness nf ctxIss ctxRed r s j)
      ⟨A.keys, nf, ctxIss, ctxRed, cd⟩ (expandRedeemSeed seed'), ?_, ?_, ?_⟩
    · simp only [redeemRequest, hj]
    · simp [finalizeRedeem, hl1, hpl2, take_append_eq hl1, drop_append_eq hl1, hpv2]
    · simp [Moderator.step, finalizeRedeem, hl1, hpl2, take_append_eq hl1, drop_append_eq hl1, hpv2]

/-! ## Input validation -/

theorem redeemRequestAt_index (PR : NIZK RedeemInstance) (tok : Token) (A : AnchorSet) (i : ℕ)
    (ctxIss ctxRed cd seed : Bytes) (hi : A.keys.length ≤ i) :
    redeemRequestAt PR tok A i ctxIss ctxRed cd seed = .error .indexOutOfRange := by
  simp [redeemRequestAt, List.getElem?_eq_none hi]

theorem redeemRequestAt_invalidToken (PR : NIZK RedeemInstance) (tok : Token) (A : AnchorSet)
    (i : ℕ) (ctxIss ctxRed cd seed : Bytes) (pk : UOVKey) (hA : A.keys[i]? = some pk)
    (h : pk.eval tok.s ≠ com tok.nf ctxIss ctxRed tok.r) :
    redeemRequestAt PR tok A i ctxIss ctxRed cd seed = .error .invalidToken := by
  simp [redeemRequestAt, hA, h]

theorem finalizeIssue_none_iff (pk : UOVKey) (p : PendingToken) (s : Bytes) :
    finalizeIssue pk p s = none ↔ pk.eval s ≠ p.t := by
  by_cases h : pk.eval s = p.t <;> simp [finalizeIssue, h]

/-- The Anchor answers `std::nullopt` exactly when the issuance proof fails for `(t, ctx_iss)`. -/
theorem issueResponse_none_iff (PI : NIZK IssueInstance) (sk : Signer) (req ctxIss : Bytes)
    (hr : req.length = issueRequestBytes) (hc : ctxIss.length = ctxBytes) :
    issueResponse PI sk req ctxIss = .ok none ↔ PI.verify (req.drop uovM) ⟨req.take uovM, ctxIss⟩ = false := by
  unfold issueResponse
  simp only [hr, hc, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
  cases hv : PI.verify (req.drop uovM) ⟨req.take uovM, ctxIss⟩
  · simp
  · simp only [↓reduceIte, Bool.true_eq_false, iff_false]
    split <;> simp

/-- The Moderator's output is the request's nullifier prefix, and only after the proof verified for
exactly the queried Anchor Set, contexts and challenge digest. -/
theorem finalizeRedeem_some (VR : NIZK RedeemInstance) (A : AnchorSet) (req ctxIss ctxRed cd nf : Bytes)
    (h : finalizeRedeem VR A req ctxIss ctxRed cd = some nf) :
    req.length = redeemRequestBytes ∧ nf = req.take nfBytes ∧
      VR.verify (req.drop nfBytes) ⟨A.keys, nf, ctxIss, ctxRed, cd⟩ = true := by
  unfold finalizeRedeem at h
  split at h
  · cases h
  · rename_i hl
    simp only at h
    split at h
    · rename_i hv; cases h; exact ⟨by simpa using hl, rfl, hv⟩
    · cases h

/-! ## Binding: the encodings parse uniquely -/

theorem issueEncode_inj {x y : IssueInstance} (ht : x.t.length = y.t.length)
    (h : x.encode = y.encode) : x.t = y.t ∧ x.ctxIss = y.ctxIss :=
  concat_inj h ht

theorem u32le_inj {a b : ℕ} (ha : a < 256) (hb : b < 256) (h : u32le a = u32le b) : a = b := by
  have h0 := congrArg (fun l => (l.headD 0).toNat) h
  simp only [u32le, List.headD_cons, Nat.toUInt8] at h0
  rwa [UInt8.toNat_ofNat_of_lt' ha, UInt8.toNat_ofNat_of_lt' hb] at h0

/-- The redemption instance encoding determines the Anchor Set's digests, `nf`, both contexts and
the challenge digest (fixed-length fields, at most 255 Anchors). -/
theorem redeemEncode_inj {x y : RedeemInstance}
    (hx : ∀ pk ∈ x.anchors, pk.digest.length = digestBytes)
    (hy : ∀ pk ∈ y.anchors, pk.digest.length = digestBytes)
    (hnx : x.anchors.length < 256) (hny : y.anchors.length < 256)
    (hnf : x.nf.length = y.nf.length) (hci : x.ctxIss.length = y.ctxIss.length)
    (hcr : x.ctxRed.length = y.ctxRed.length) (h : x.encode = y.encode) :
    x.anchors.map (·.digest) = y.anchors.map (·.digest) ∧ x.nf = y.nf ∧ x.ctxIss = y.ctxIss ∧
      x.ctxRed = y.ctxRed ∧ x.challengeDigest = y.challengeDigest := by
  unfold RedeemInstance.encode at h
  simp only [List.append_assoc] at h
  obtain ⟨-, h⟩ := concat_inj h rfl
  have hu : (u32le x.anchors.length).length = (u32le y.anchors.length).length := by simp [u32le]
  obtain ⟨hn, h⟩ := concat_inj h hu
  have hn := u32le_inj hnx hny hn
  have hdx : ∀ d ∈ x.anchors.map (·.digest), d.length = digestBytes := by
    simp only [List.mem_map]; rintro d ⟨pk, hpk, rfl⟩; exact hx pk hpk
  have hdy : ∀ d ∈ y.anchors.map (·.digest), d.length = digestBytes := by
    simp only [List.mem_map]; rintro d ⟨pk, hpk, rfl⟩; exact hy pk hpk
  obtain ⟨hd, h⟩ := concat_inj h (by
    rw [length_flatten_of_forall hdx, length_flatten_of_forall hdy]; simp [hn])
  have hd := flatten_inj (by simp [hn]) hdx hdy hd
  obtain ⟨h1, h⟩ := concat_inj h hnf
  obtain ⟨h2, h⟩ := concat_inj h hci
  obtain ⟨h3, h4⟩ := concat_inj h hcr
  exact ⟨hd, h1, h2, h3, h4⟩

/-- A redemption proof's instance hash input differs for different challenge digests (with
everything else equal): redemption is bound to the challenge. -/
theorem redeemEncode_ne_of_challengeDigest (anchors : List UOVKey) (nf ctxIss ctxRed cd cd' : Bytes)
    (h : cd ≠ cd') :
    RedeemInstance.encode ⟨anchors, nf, ctxIss, ctxRed, cd⟩ ≠
      RedeemInstance.encode ⟨anchors, nf, ctxIss, ctxRed, cd'⟩ := by
  intro he
  simp only [RedeemInstance.encode] at he
  exact h (List.append_cancel_left he)

/-- The commitment input determines `(nf, ctx_iss, ctx_red, r)` (fixed-length fields); since
Keccak-p[800] is a permutation, so does the full output state. -/
theorem comState_inj {nf ci cr r nf' ci' cr' r' : Bytes} (hr : r.length = r'.length)
    (hci : ci.length = ci'.length) (hcr : cr.length = cr'.length) (hnf : nf.length = nf'.length)
    (h : comState nf ci cr r = comState nf' ci' cr' r') :
    nf = nf' ∧ ci = ci' ∧ cr = cr' ∧ r = r' := by
  unfold comState at h
  obtain ⟨h, -⟩ := concat_inj h (by simp [hr, hci, hcr, hnf])
  obtain ⟨h, h4⟩ := concat_inj h (by simp [hr, hci, hcr])
  obtain ⟨h, h3⟩ := concat_inj h (by simp [hr, hci])
  obtain ⟨h, h2⟩ := concat_inj h (by simp [hr])
  obtain ⟨h, -⟩ := concat_inj h (by simp [hr])
  obtain ⟨-, h1⟩ := concat_inj h rfl
  exact ⟨h4, h2, h3, h1⟩

end VoleMole.Spec.Moussaka
