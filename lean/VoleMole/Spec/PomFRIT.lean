import VoleMole.Spec.Common

/-!
# Executable protocol spec of PomFRIT (`src/pomfrit/pomfrit.cpp`, `include/vole_mole/pomfrit.hpp`)

## What is modelled

* Message formats: the request `t` (`M` bytes), the response `s` (`N` bytes), and the blind
  signature `σ = proof ‖ refresher_com ‖ refresher` (`SIGNATURE_BYTES = 5387`,
  `pomfrit.cpp:44-50`), with the two proof fields PomFRIT reads directly: the VOLE check proof `ũ`
  (`OFFSET_VOLE_CHECK_PROOF = 2819`, 64 bytes) and the prefix correction `d[0..M)` (start of the
  witness correction, `OFFSET_CORRECTION = 2883`; `faest_sig.hpp:52-66`).
* Hashing: `XOF_seed` (`pomfrit.cpp:150-161`), `H_ref = commit_to_refresher` (`:76-84`) and
  `H_T = hash_to_target` (`:96-111`), all SHAKE128 (`hash_state::init(s128)`).
* Every step: `issueRequest` (Sig1, `detail::issue_request_with_seed`, `:140-180`),
  `issueResponse` (Sig2, `:188-190`), `finalizeIssue` (Sig3, `:193-217`, including the wrong-key
  exception and the `P(s) = t` check) and `verify` (`:220-237`).
* UOV verification `P(s) = t` concretely (`UOVKey.eval`).

## What is abstract

* The two-phase VOLEitH prover/verifier (`voleith_vole_gen` / `voleith_prove_commit`,
  `voleith_vole_reconstruct` / `voleith_verify_commit`): the structures `Prover` and `Verifier`,
  with the properties used for correctness collected in `ProofSystem.Correct`.
* UOV preimage derivation (`Signer`). Moved-from objects: Lean values are immutable; the C++
  `std::logic_error` on reuse is not modelled.
* Lengths that the C++ enforces by `std::array` types are checked explicitly here and reported as
  `Error.malformed` (unrepresentable in C++).

## Results

* `honest_run_verifies`: correctness of an honest run.
* `finalizeIssue_none_iff`, `finalizeIssue_wrongKey`: the Client's checks.
* `verify_false_of_refresher`, `verify_false_of_length`: verifier input validation.
* `targetInput_inj`: the input of `H_T` parses uniquely, so `h` binds `pk`'s digest, `chal1`,
  `ũ`, the prefix correction `d[0..M)` (finding F4 of `security/pomfrit.md`) and `msg`.
* `request_xor`: the Client recovers `h = t ⊕ r`.
-/

namespace VoleMole.Spec.PomFRIT

open VoleMole.Arith

/-! ## Constants and layout -/

/-- `POMFRIT_*_DST` (`src/dst.hpp:41-45`), version 0. -/
def seedDst : Bytes := makeDst "pomf" 0 's' '0'
def refresherDst : Bytes := makeDst "pomf" 0 'r' '0'
def targetDst : Bytes := makeDst "pomf" 0 'h' '0'

#guard seedDst = [0x70, 0x6f, 0x6d, 0x66, 0x00, 0x73, 0x30]

/-- `detail::SEED_BYTES`, `PROVE_SEED_BYTES` (λ/8), `REFRESHER_BYTES` (2λ/8). -/
abbrev seedBytes : ℕ := 32
abbrev proveSeedBytes : ℕ := 16
abbrev refresherBytes : ℕ := 32

/-- `PROOF_BYTES<RedeemRelation>` and the proof fields read by PomFRIT. -/
abbrev proofBytes : ℕ := 5323
abbrev offVoleCheck : ℕ := 2819
abbrev voleCheckBytes : ℕ := 64
abbrev offCorrection : ℕ := 2883
abbrev correctionBytes : ℕ := uovM + uovN

/-- `SIGNATURE_BYTES` (`pomfrit.hpp:27`). -/
abbrev sigBytes : ℕ := proofBytes + 2 * refresherBytes

#guard sigBytes = 5387

def sigProof (sig : Bytes) : Bytes := sig.take proofBytes
def sigRefresherCom (sig : Bytes) : Bytes := slice sig proofBytes refresherBytes
def sigRefresher (sig : Bytes) : Bytes := slice sig (proofBytes + refresherBytes) refresherBytes
/-- `proof.vole_check_proof()` (`ũ`). -/
def sigUTilde (sig : Bytes) : Bytes := slice sig offVoleCheck voleCheckBytes
/-- `sig_witness_prefix_correction(sig)`: `d[0..M)`. -/
def sigPrefixCorrection (sig : Bytes) : Bytes := slice sig offCorrection uovM

/-! ## Hashes -/

/-- `XOF_seed`: `SHAKE128(DST ‖ seed ‖ dig(pk) ‖ msg)` squeezed into `rho ‖ refresher ‖ r`. -/
def expandSeed (dig msg seed : Bytes) : Bytes × Bytes × Bytes :=
  let out := shake128B (seedDst ++ seed ++ dig ++ msg) (proveSeedBytes + refresherBytes + uovM)
  (out.take proveSeedBytes, slice out proveSeedBytes refresherBytes,
    slice out (proveSeedBytes + refresherBytes) uovM)

/-- `commit_to_refresher`: `SHAKE128(DST ‖ refresher)`, 32 bytes. -/
def commitRefresher (refresher : Bytes) : Bytes := shake128B (refresherDst ++ refresher) refresherBytes

/-- The input of `hash_to_target`. -/
def targetInput (dig chal1 uTilde d msg : Bytes) : Bytes :=
  targetDst ++ dig ++ chal1 ++ uTilde ++ d ++ msg

/-- `hash_to_target(pk, sig, chal1, msg)`. -/
def hashToTarget (dig chal1 sig msg : Bytes) : Bytes :=
  shake128B (targetInput dig chal1 (sigUTilde sig) (sigPrefixCorrection sig) msg) uovM

/-! ## The abstract proof system -/

/-- The prover, with pending state `St`. `voleGen r rho binder` is `voleith_vole_gen(proof,
nullptr, r, rho, binder)`: the proof buffer after step 1, `chal1`, and the pending state.
`proveCommit proof pk h s binder₂ st` is `voleith_prove_commit(proof, {&pk, h}, s, st, binder₂)`:
the completed proof. -/
structure Prover (St : Type) where
  voleGen : Bytes → Bytes → Bytes → Bytes × Bytes × St
  proveCommit : Bytes → UOVKey → Bytes → Bytes → Bytes → St → Bytes

/-- The verifier. `reconstruct proof binder` is `voleith_vole_reconstruct` (its `chal1`, or `none`
if rejected); `verifyCommit proof binder pk h binder₂` is `voleith_verify_commit` after it. -/
structure Verifier where
  reconstruct : Bytes → Bytes → Option Bytes
  verifyCommit : Bytes → Bytes → UOVKey → Bytes → Bytes → Bool

/-- The properties of an honest proof system used for correctness. -/
structure Correct {St : Type} (P : Prover St) (V : Verifier) : Prop where
  voleGen_length : ∀ r rho b, (P.voleGen r rho b).1.length = proofBytes
  proveCommit_length : ∀ pf pk h s b st, (P.proveCommit pf pk h s b st).length = proofBytes
  /-- Step 2 leaves `ũ` and `d[0..M)`, written by step 1, unchanged. -/
  keeps_uTilde : ∀ pf pk h s b st,
    slice (P.proveCommit pf pk h s b st) offVoleCheck voleCheckBytes = slice pf offVoleCheck voleCheckBytes
  keeps_prefix : ∀ pf pk h s b st,
    slice (P.proveCommit pf pk h s b st) offCorrection uovM = slice pf offCorrection uovM
  /-- The verifier recomputes the prover's `chal1`. -/
  reconstruct_eq : ∀ r rho b pk h s b₂,
    V.reconstruct (P.proveCommit (P.voleGen r rho b).1 pk h s b₂ (P.voleGen r rho b).2.2) b =
      some (P.voleGen r rho b).2.1
  /-- Completeness for `R((pk, h), (r, s)) ⇔ P(s) = h ⊕ r`. -/
  complete : ∀ r rho b pk h s b₂, r.length = uovM → h.length = uovM → s.length = uovN →
    pk.eval s = xorBytes h r →
    V.verifyCommit (P.proveCommit (P.voleGen r rho b).1 pk h s b₂ (P.voleGen r rho b).2.2) b pk h b₂
      = true

/-! ## The protocol -/

inductive Error where
  | malformed
  | wrongKey
  | deriveFailed
  deriving DecidableEq, Repr

/-- The Client's state (`PendingBlindSignature::Impl`). -/
structure Pending (St : Type) where
  pkDigest : Bytes
  t : Bytes
  h : Bytes
  sig : Bytes
  st : St

/-- Sig1: `detail::issue_request_with_seed(pk, msg, seed)`; returns the pending state and `t`. -/
def issueRequest {St : Type} (P : Prover St) (pk : UOVKey) (msg seed : Bytes) : Pending St × Bytes :=
  let (rho, refresher, r) := expandSeed pk.digest msg seed
  let refresherCom := commitRefresher refresher
  let (proof, chal1, st) := P.voleGen r rho refresherCom
  let sig := proof ++ refresherCom ++ refresher
  let h := hashToTarget pk.digest chal1 sig msg
  let t := xorBytes h r
  (⟨pk.digest, t, h, sig, st⟩, t)

/-- Sig2: `issue_response(sk, t) = sk.derive_preimage(t)`. -/
def issueResponse (sk : Signer) (t : Bytes) : Except Error Bytes :=
  if t.length ≠ uovM then .error .malformed else
  match sk.derivePreimage t with
  | some s => .ok s
  | none => .error .deriveFailed

/-- Sig3: `PendingBlindSignature::finalize_issue(pk, s)`. `.ok none` is `std::nullopt`. -/
def finalizeIssue {St : Type} (P : Prover St) (pk : UOVKey) (p : Pending St) (s : Bytes) :
    Except Error (Option Bytes) :=
  if s.length ≠ uovN then .error .malformed
  else if pk.digest ≠ p.pkDigest then .error .wrongKey
  else if pk.eval s ≠ p.t then .ok none
  else
    let proof := P.proveCommit (sigProof p.sig) pk p.h s (sigRefresher p.sig) p.st
    .ok (some (proof ++ sigRefresherCom p.sig ++ sigRefresher p.sig))

/-- `verify(pk, msg, sig)`. -/
def verify (V : Verifier) (pk : UOVKey) (msg sig : Bytes) : Bool :=
  if sig.length ≠ sigBytes then false
  else if commitRefresher (sigRefresher sig) ≠ sigRefresherCom sig then false
  else match V.reconstruct (sigProof sig) (sigRefresherCom sig) with
    | none => false
    | some chal1 =>
      V.verifyCommit (sigProof sig) (sigRefresherCom sig) pk (hashToTarget pk.digest chal1 sig msg)
        (sigRefresher sig)

/-! ## Lemmas on the layout -/

/-- Arithmetic on the layout constants. -/
macro "layout_omega" : tactic => `(tactic| (simp only [proofBytes, offVoleCheck, voleCheckBytes,
  offCorrection, uovM, uovN, sigBytes, refresherBytes, proveSeedBytes] at *; omega))

theorem length_expandSeed (dig msg seed : Bytes) :
    (expandSeed dig msg seed).1.length = proveSeedBytes ∧
    (expandSeed dig msg seed).2.1.length = refresherBytes ∧
    (expandSeed dig msg seed).2.2.length = uovM := by
  simp [expandSeed, slice, length_shake128B]; layout_omega

theorem length_commitRefresher (b : Bytes) : (commitRefresher b).length = refresherBytes :=
  length_shake128B _ _

theorem length_hashToTarget (dig chal1 sig msg : Bytes) :
    (hashToTarget dig chal1 sig msg).length = uovM := length_shake128B _ _

/-- The fields of a signature assembled as `proof ‖ refresher_com ‖ refresher`. -/
theorem sig_fields {proof rc ref : Bytes} (hp : proof.length = proofBytes)
    (hrc : rc.length = refresherBytes) (href : ref.length = refresherBytes) :
    sigProof (proof ++ rc ++ ref) = proof ∧ sigRefresherCom (proof ++ rc ++ ref) = rc ∧
    sigRefresher (proof ++ rc ++ ref) = ref ∧
    sigUTilde (proof ++ rc ++ ref) = slice proof offVoleCheck voleCheckBytes ∧
    sigPrefixCorrection (proof ++ rc ++ ref) = slice proof offCorrection uovM ∧
    (proof ++ rc ++ ref).length = sigBytes := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sigProof, List.append_assoc, take_append_eq hp]
  · rw [sigRefresherCom, List.append_assoc, slice_append_right (by layout_omega), hp, Nat.sub_self,
      slice_append_left (by layout_omega), slice_eq_self hrc]
  · rw [sigRefresher, List.append_assoc, slice_append_right (by layout_omega), hp,
      slice_append_right (by layout_omega), hrc, Nat.add_sub_cancel_left, Nat.sub_self, slice_eq_self href]
  · rw [sigUTilde, List.append_assoc, slice_append_left (by layout_omega)]
  · rw [sigPrefixCorrection, List.append_assoc, slice_append_left (by layout_omega)]
  · simp [hp, hrc, href]; omega

/-! ## Correctness -/

/-- **Correctness.** With a correct proof system and a correct signer that answers, the honest run
`issueRequest → issueResponse → finalizeIssue` yields a signature that `verify` accepts. -/
theorem honest_run_verifies {St : Type} (P : Prover St) (V : Verifier) (hPV : Correct P V)
    (pk : UOVKey) (sk : Signer) (hsk : sk.Correct pk) (msg seed : Bytes) (s : Bytes)
    (hs : issueResponse sk (issueRequest P pk msg seed).2 = .ok s) :
    ∃ sig, finalizeIssue P pk (issueRequest P pk msg seed).1 s = .ok (some sig) ∧
      verify V pk msg sig = true := by
  obtain ⟨hl1, hl2, hl3⟩ := length_expandSeed pk.digest msg seed
  set e := expandSeed pk.digest msg seed with he
  obtain ⟨rho, refresher, r⟩ := e
  simp only at hl1 hl2 hl3
  set g := P.voleGen r rho (commitRefresher refresher) with hg
  obtain ⟨proof, chal1, st⟩ := g
  have hpl : proof.length = proofBytes := by
    have := hPV.voleGen_length r rho (commitRefresher refresher); rw [← hg] at this; exact this
  have hrc := length_commitRefresher refresher
  obtain ⟨f1, f2, f3, f4, f5, -⟩ := sig_fields hpl hrc hl2
  set h := hashToTarget pk.digest chal1 (proof ++ commitRefresher refresher ++ refresher) msg with hh
  have hhl : h.length = uovM := length_hashToTarget _ _ _ _
  have hreq : issueRequest P pk msg seed =
      (⟨pk.digest, xorBytes h r, h, proof ++ commitRefresher refresher ++ refresher, st⟩,
        xorBytes h r) := by
    simp only [issueRequest, ← he, ← hg, hh]
  rw [hreq] at hs ⊢
  have htl : (xorBytes h r).length = uovM := by simp [length_xorBytes, hhl, hl3]
  simp only [issueResponse, htl, ne_eq, not_true_eq_false, ↓reduceIte] at hs
  split at hs
  case h_2 => cases hs
  rename_i s' hd
  cases hs
  obtain ⟨hsl, hev⟩ := hsk _ _ htl hd
  simp only [finalizeIssue, hsl, ne_eq, not_true_eq_false, ↓reduceIte, hev, Except.ok.injEq,
    Option.some.injEq, exists_eq_left', f1, f2, f3]
  set proof2 := P.proveCommit proof pk h s (refresher) st with hp2
  have hp2l : proof2.length = proofBytes := hPV.proveCommit_length _ _ _ _ _ _
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := sig_fields hp2l hrc hl2
  have hrec : V.reconstruct proof2 (commitRefresher refresher) = some chal1 := by
    have := hPV.reconstruct_eq r rho (commitRefresher refresher) pk h s refresher
    rw [← hg] at this; exact this
  have hH : hashToTarget pk.digest chal1 (proof2 ++ commitRefresher refresher ++ refresher) msg = h := by
    rw [hh, hashToTarget, hashToTarget, g4, g5, f4, f5, hp2, hPV.keeps_uTilde, hPV.keeps_prefix]
  have hcomp := hPV.complete r rho (commitRefresher refresher) pk h s refresher hl3 hhl hsl
  rw [← hg] at hcomp
  simp only at hcomp
  have hx : pk.eval s = xorBytes h r := hev
  simp only [verify, g6, ne_eq, not_true_eq_false, ↓reduceIte, g2, g3, g1, hrec, hH]
  exact hcomp hx

/-! ## The Client's checks -/

/-- `finalize_issue` returns `std::nullopt` exactly when `P(s) ≠ t` (well-formed `s`, same key). -/
theorem finalizeIssue_none_iff {St : Type} (P : Prover St) (pk : UOVKey) (p : Pending St) (s : Bytes)
    (hs : s.length = uovN) (hk : pk.digest = p.pkDigest) :
    finalizeIssue P pk p s = .ok none ↔ pk.eval s ≠ p.t := by
  by_cases he : pk.eval s = p.t <;> simp [finalizeIssue, hs, hk, he]

/-- A different key throws (`std::invalid_argument`), before the response is looked at. -/
theorem finalizeIssue_wrongKey {St : Type} (P : Prover St) (pk : UOVKey) (p : Pending St) (s : Bytes)
    (hs : s.length = uovN) (hk : pk.digest ≠ p.pkDigest) :
    finalizeIssue P pk p s = .error .wrongKey := by
  simp [finalizeIssue, hs, hk]

/-- The masked target is `t = h ⊕ r`, so `h = t ⊕ r`. -/
theorem request_xor {St : Type} (P : Prover St) (pk : UOVKey) (msg seed : Bytes) :
    xorBytes (issueRequest P pk msg seed).2 (expandSeed pk.digest msg seed).2.2 =
      (issueRequest P pk msg seed).1.h := by
  simp only [issueRequest]
  exact xorBytes_xorBytes_right (by
    rw [length_hashToTarget, (length_expandSeed _ _ _).2.2])

/-! ## Verifier input validation -/

theorem verify_false_of_length (V : Verifier) (pk : UOVKey) (msg sig : Bytes)
    (h : sig.length ≠ sigBytes) : verify V pk msg sig = false := by
  simp [verify, h]

/-- A refresher that does not open `refresher_com` is rejected before any proof work. -/
theorem verify_false_of_refresher (V : Verifier) (pk : UOVKey) (msg sig : Bytes)
    (h : commitRefresher (sigRefresher sig) ≠ sigRefresherCom sig) :
    verify V pk msg sig = false := by
  simp [verify, h]

/-! ## Binding: the input of `H_T` parses uniquely -/

/-- `chal1` length (`VOLE_CHECK::CHALLENGE_BYTES`); any fixed length works below. -/
theorem targetInput_inj {dig chal1 u d msg dig' chal1' u' d' msg' : Bytes}
    (hdig : dig.length = dig'.length) (hc : chal1.length = chal1'.length)
    (hu : u.length = u'.length) (hd : d.length = d'.length)
    (h : targetInput dig chal1 u d msg = targetInput dig' chal1' u' d' msg') :
    dig = dig' ∧ chal1 = chal1' ∧ u = u' ∧ d = d' ∧ msg = msg' := by
  unfold targetInput at h
  obtain ⟨h1, h5⟩ := concat_inj h (by simp [hdig, hc, hu, hd])
  obtain ⟨h2, h4⟩ := concat_inj h1 (by simp [hdig, hc, hu])
  obtain ⟨h3, h3'⟩ := concat_inj h2 (by simp [hdig, hc])
  obtain ⟨h6, h6'⟩ := concat_inj h3 (by simp [hdig])
  obtain ⟨-, h7⟩ := concat_inj h6 rfl
  exact ⟨h7, h6', h3', h4, h5⟩

/-- In particular two signatures with the same `pk`, `chal1`, `ũ` and `msg` but different prefix
corrections hash different inputs to `H_T` (F4: without `d[0..M)` in the hash, a Client could
re-target a signature). -/
theorem targetInput_ne_of_prefix {dig chal1 sig sig' msg : Bytes}
    (hd : sigPrefixCorrection sig ≠ sigPrefixCorrection sig')
    (hl : sig.length = sigBytes) (hl' : sig'.length = sigBytes) :
    targetInput dig chal1 (sigUTilde sig) (sigPrefixCorrection sig) msg ≠
      targetInput dig chal1 (sigUTilde sig') (sigPrefixCorrection sig') msg := by
  intro h
  have hu : (sigUTilde sig).length = (sigUTilde sig').length := by
    rw [sigUTilde, sigUTilde, length_slice_of_le (by layout_omega), length_slice_of_le (by layout_omega)]
  have hp : (sigPrefixCorrection sig).length = (sigPrefixCorrection sig').length := by
    rw [sigPrefixCorrection, sigPrefixCorrection, length_slice_of_le (by layout_omega),
      length_slice_of_le (by layout_omega)]
  exact hd (targetInput_inj rfl rfl hu hp h).2.2.2.1

end VoleMole.Spec.PomFRIT
