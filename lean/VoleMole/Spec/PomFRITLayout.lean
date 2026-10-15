import VoleMole.Spec.PomFRIT

/-!
# PomFRIT on either proof layout

`Spec/PomFRIT.lean` hard-codes the proof layout of `main` (`PROOF_BYTES = 5323`, `ũ` at 2819,
`d` at 2883). With dedicated label rows (branch `voleith-label-rows`) the proof is 256 bytes
longer and both fields move (the corrections grow by 16 bytes each): `5579`, `3075`, `3139`. The
protocol is otherwise the same. Here the layout-dependent part of the spec is a function of a
`Layout`: the signature's fields (`sigProof`, …), `hash_to_target` (which reads `ũ` and
`d[0..M)` from the signature), `issueRequest`, `finalizeIssue` and `verify`. At `Layout.main` every
one is the spec's (`main_hashToTarget`, `main_issueRequest`, `main_finalizeIssue`, `main_verify`:
`rfl`).

* `Layout.main`, `Layout.labelRows`; `Layout.sig_fields`, `Layout.length_hashToTarget`.
* `Layout.Correct`: `Spec.PomFRIT.Correct` with the layout's proof length and fields;
  `Layout.honest_run_verifies`: correctness of an honest run, for any layout.
-/

namespace VoleMole.Spec.PomFRIT

open VoleMole.Arith

/-- The proof layout PomFRIT reads: the proof length, and the offsets of the VOLE check proof `ũ`
(64 bytes) and of the witness correction `d` (whose first `M` bytes it reads). -/
structure Layout where
  proofBytes : ℕ
  offVoleCheck : ℕ
  offCorrection : ℕ
  vole_le : offVoleCheck + voleCheckBytes ≤ proofBytes
  corr_le : offCorrection + uovM ≤ proofBytes

namespace Layout

/-- `main`'s layout (`Spec/PomFRIT.lean`'s constants). -/
def main : Layout :=
  ⟨PomFRIT.proofBytes, PomFRIT.offVoleCheck, PomFRIT.offCorrection, by decide, by decide⟩

/-- The layout with dedicated label rows: corrections `16 · 180` bytes, `c_mult` 195, then `ũ`
and `d`; 5579 bytes in all (`Verifier.Params.proofBytes`, `labelRows := true`). -/
def labelRows : Layout := ⟨5579, 3075, 3139, by decide, by decide⟩

variable (L : Layout)

/-- `SIGNATURE_BYTES`. -/
def sigBytes : ℕ := L.proofBytes + 2 * refresherBytes

def sigProof (sig : Bytes) : Bytes := sig.take L.proofBytes
def sigRefresherCom (sig : Bytes) : Bytes := slice sig L.proofBytes refresherBytes
def sigRefresher (sig : Bytes) : Bytes := slice sig (L.proofBytes + refresherBytes) refresherBytes
/-- `proof.vole_check_proof()` (`ũ`). -/
def sigUTilde (sig : Bytes) : Bytes := slice sig L.offVoleCheck voleCheckBytes
/-- `sig_witness_prefix_correction(sig)`: `d[0..M)`. -/
def sigPrefixCorrection (sig : Bytes) : Bytes := slice sig L.offCorrection uovM

/-- `hash_to_target(pk, sig, chal1, msg)`. -/
def hashToTarget (dig chal1 sig msg : Bytes) : Bytes :=
  shake128B (targetInput dig chal1 (L.sigUTilde sig) (L.sigPrefixCorrection sig) msg) uovM

/-- Sig1 (`issueRequest`). -/
def issueRequest {St : Type} (P : Prover St) (pk : UOVKey) (msg seed : Bytes) :
    Pending St × Bytes :=
  let (rho, refresher, r) := expandSeed pk.digest msg seed
  let refresherCom := commitRefresher refresher
  let (proof, chal1, st) := P.voleGen r rho refresherCom
  let sig := proof ++ refresherCom ++ refresher
  let h := L.hashToTarget pk.digest chal1 sig msg
  let t := xorBytes h r
  (⟨pk.digest, t, h, sig, st⟩, t)

/-- Sig3 (`finalizeIssue`). -/
def finalizeIssue {St : Type} (P : Prover St) (pk : UOVKey) (p : Pending St) (s : Bytes) :
    Except Error (Option Bytes) :=
  if s.length ≠ uovN then .error .malformed
  else if pk.digest ≠ p.pkDigest then .error .wrongKey
  else if pk.eval s ≠ p.t then .ok none
  else
    let proof := P.proveCommit (L.sigProof p.sig) pk p.h s (L.sigRefresher p.sig) p.st
    .ok (some (proof ++ L.sigRefresherCom p.sig ++ L.sigRefresher p.sig))

/-- `verify(pk, msg, sig)`. -/
def verify (V : Verifier) (pk : UOVKey) (msg sig : Bytes) : Bool :=
  if sig.length ≠ L.sigBytes then false
  else if commitRefresher (L.sigRefresher sig) ≠ L.sigRefresherCom sig then false
  else match V.reconstruct (L.sigProof sig) (L.sigRefresherCom sig) with
    | none => false
    | some chal1 =>
      V.verifyCommit (L.sigProof sig) (L.sigRefresherCom sig) pk
        (L.hashToTarget pk.digest chal1 sig msg) (L.sigRefresher sig)

/-! ## `main` is the spec -/

theorem main_hashToTarget : main.hashToTarget = PomFRIT.hashToTarget := rfl

theorem main_issueRequest {St : Type} (P : Prover St) :
    main.issueRequest P = PomFRIT.issueRequest P := rfl

theorem main_finalizeIssue {St : Type} (P : Prover St) :
    main.finalizeIssue P = PomFRIT.finalizeIssue P := rfl

theorem main_verify (V : Verifier) : main.verify V = PomFRIT.verify V := rfl

/-! ## Lemmas -/

theorem length_hashToTarget (dig chal1 sig msg : Bytes) :
    (L.hashToTarget dig chal1 sig msg).length = uovM := length_shake128B _ _

/-- The fields of a signature assembled as `proof ‖ refresher_com ‖ refresher`. -/
theorem sig_fields {proof rc ref : Bytes} (hp : proof.length = L.proofBytes)
    (hrc : rc.length = refresherBytes) (href : ref.length = refresherBytes) :
    L.sigProof (proof ++ rc ++ ref) = proof ∧ L.sigRefresherCom (proof ++ rc ++ ref) = rc ∧
    L.sigRefresher (proof ++ rc ++ ref) = ref ∧
    L.sigUTilde (proof ++ rc ++ ref) = slice proof L.offVoleCheck voleCheckBytes ∧
    L.sigPrefixCorrection (proof ++ rc ++ ref) = slice proof L.offCorrection uovM ∧
    (proof ++ rc ++ ref).length = L.sigBytes := by
  have h1 := L.vole_le
  have h2 := L.corr_le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [sigProof, List.append_assoc, take_append_eq hp]
  · rw [sigRefresherCom, List.append_assoc, slice_append_right (by omega), hp, Nat.sub_self,
      slice_append_left (by omega), slice_eq_self hrc]
  · rw [sigRefresher, List.append_assoc, slice_append_right (by omega), hp,
      slice_append_right (by omega), hrc, Nat.add_sub_cancel_left, Nat.sub_self,
      slice_eq_self href]
  · rw [sigUTilde, List.append_assoc, slice_append_left (by omega)]
  · rw [sigPrefixCorrection, List.append_assoc, slice_append_left (by omega)]
  · simp [sigBytes, hp, hrc, href]; omega

/-! ## Correctness -/

/-- `Spec.PomFRIT.Correct` for the layout `L`. -/
structure Correct {St : Type} (P : Prover St) (V : Verifier) : Prop where
  voleGen_length : ∀ r rho b, (P.voleGen r rho b).1.length = L.proofBytes
  proveCommit_length : ∀ pf pk h s b st, (P.proveCommit pf pk h s b st).length = L.proofBytes
  keeps_uTilde : ∀ pf pk h s b st,
    slice (P.proveCommit pf pk h s b st) L.offVoleCheck voleCheckBytes =
      slice pf L.offVoleCheck voleCheckBytes
  keeps_prefix : ∀ pf pk h s b st,
    slice (P.proveCommit pf pk h s b st) L.offCorrection uovM = slice pf L.offCorrection uovM
  reconstruct_eq : ∀ r rho b pk h s b₂,
    V.reconstruct (P.proveCommit (P.voleGen r rho b).1 pk h s b₂ (P.voleGen r rho b).2.2) b =
      some (P.voleGen r rho b).2.1
  complete : ∀ r rho b pk h s b₂, r.length = uovM → h.length = uovM → s.length = uovN →
    pk.eval s = xorBytes h r →
    V.verifyCommit (P.proveCommit (P.voleGen r rho b).1 pk h s b₂ (P.voleGen r rho b).2.2) b pk h b₂
      = true

theorem correct_main_iff {St : Type} (P : Prover St) (V : Verifier) :
    main.Correct P V ↔ PomFRIT.Correct P V :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩, fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩⟩

/-- **Correctness on the layout `L`** (`Spec.PomFRIT.honest_run_verifies`). -/
theorem honest_run_verifies {St : Type} (P : Prover St) (V : Verifier) (hPV : L.Correct P V)
    (pk : UOVKey) (sk : Signer) (hsk : sk.Correct pk) (msg seed : Bytes) (s : Bytes)
    (hs : issueResponse sk (L.issueRequest P pk msg seed).2 = .ok s) :
    ∃ sig, L.finalizeIssue P pk (L.issueRequest P pk msg seed).1 s = .ok (some sig) ∧
      L.verify V pk msg sig = true := by
  obtain ⟨hl1, hl2, hl3⟩ := length_expandSeed pk.digest msg seed
  set e := expandSeed pk.digest msg seed with he
  obtain ⟨rho, refresher, r⟩ := e
  simp only at hl1 hl2 hl3
  set g := P.voleGen r rho (commitRefresher refresher) with hg
  obtain ⟨proof, chal1, st⟩ := g
  have hpl : proof.length = L.proofBytes := by
    have := hPV.voleGen_length r rho (commitRefresher refresher); rw [← hg] at this; exact this
  have hrc := length_commitRefresher refresher
  obtain ⟨f1, f2, f3, f4, f5, -⟩ := L.sig_fields hpl hrc hl2
  set h := L.hashToTarget pk.digest chal1 (proof ++ commitRefresher refresher ++ refresher) msg
    with hh
  have hhl : h.length = uovM := L.length_hashToTarget _ _ _ _
  have hreq : L.issueRequest P pk msg seed =
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
  set proof2 := P.proveCommit proof pk h s refresher st with hp2
  have hp2l : proof2.length = L.proofBytes := hPV.proveCommit_length _ _ _ _ _ _
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := L.sig_fields hp2l hrc hl2
  have hrec : V.reconstruct proof2 (commitRefresher refresher) = some chal1 := by
    have := hPV.reconstruct_eq r rho (commitRefresher refresher) pk h s refresher
    rw [← hg] at this; exact this
  have hH : L.hashToTarget pk.digest chal1 (proof2 ++ commitRefresher refresher ++ refresher) msg =
      h := by
    rw [hh, hashToTarget, hashToTarget, g4, g5, f4, f5, hp2, hPV.keeps_uTilde, hPV.keeps_prefix]
  have hcomp := hPV.complete r rho (commitRefresher refresher) pk h s refresher hl3 hhl hsl
  rw [← hg] at hcomp
  simp only at hcomp
  have hx : pk.eval s = xorBytes h r := hev
  simp only [verify, g6, ne_eq, not_true_eq_false, ↓reduceIte, g2, g3, g1, hrec, hH]
  exact hcomp hx

end Layout

end VoleMole.Spec.PomFRIT
