import VoleMole.Spec.Moussaka

/-!
# Moussaka's issuance message length with dedicated label rows

`Spec/Moussaka.lean` models `main`: an issuance request is `t ‖ π_iss` with a `7272`-byte proof
(`issueRequestBytes = 45 + 7272`), and `issueResponse` (the Anchor) rejects every other length as
malformed. With dedicated label rows (branch `voleith-label-rows`, the layout the privacy games'
Lean prover uses: `Verifier.Proof`, `{ witnessBytes := 256, qsDegree := 9, labelRows := true }`)
the issuance proof has `7528` bytes, so a `main`-length check rejects every label-row request.

* `issueResponseN n`: `issue_response` with the request length `n`; `issueResponse` is
  `issueResponseN issueRequestBytes` (`issueResponseN_main`, by definition).
* `issueResponseLR`: the label-row Anchor (`n = issueRequestBytesLR = 45 + 7528`), which the
  non-colluding privacy games (`Privacy/MoussakaNC.lean`) use.
* `finalizeRedeemN n`, `finalizeRedeemLR`: the Moderator's `finalize_redeem` for redemption
  requests of `n` bytes; `main`'s is `finalizeRedeemN redeemRequestBytes` (`24 + 8751`), the
  label-row one `24 + 9007` (`Audit/Liveness.lean`: the Lean redemption proofs have `9007` bytes,
  so `main`'s Moderator would reject every one; no game runs an honest Moderator, so nothing was
  vacuous, but a game that adds one must use `finalizeRedeemLR`).
-/

namespace VoleMole.Spec.Moussaka

/-- The issuance proof's size with dedicated label rows. -/
abbrev issueProofBytesLR : ℕ := 7528
/-- The issuance request's size with dedicated label rows. -/
abbrev issueRequestBytesLR : ℕ := uovM + issueProofBytesLR

/-- `issue_response(sk, request, ctx_iss)` for requests of `n` bytes. -/
def issueResponseN (n : ℕ) (PI : NIZK IssueInstance) (sk : Signer) (req ctxIss : Bytes) :
    Except Error (Option Bytes) :=
  if req.length ≠ n ∨ ctxIss.length ≠ ctxBytes then .error .malformed else
  let t := req.take uovM
  if PI.verify (req.drop uovM) ⟨t, ctxIss⟩ then
    match sk.derivePreimage t with
    | some s => .ok (some s)
    | none => .error .deriveFailed
  else .ok none

/-- `main`'s Anchor. -/
theorem issueResponseN_main : issueResponseN issueRequestBytes = issueResponse := rfl

/-- **The Anchor with dedicated label rows** (`45 + 7528`-byte requests). -/
abbrev issueResponseLR :
    NIZK IssueInstance → Signer → Bytes → Bytes → Except Error (Option Bytes) :=
  issueResponseN issueRequestBytesLR

/-- The redemption proof's size with dedicated label rows. -/
abbrev redeemProofBytesLR : ℕ := 9007
/-- The redemption request's size with dedicated label rows. -/
abbrev redeemRequestBytesLR : ℕ := nfBytes + redeemProofBytesLR

/-- `finalize_redeem(anchors, request, ctx_iss, ctx_red, challenge_digest)` for requests of `n`
bytes. -/
def finalizeRedeemN (n : ℕ) (VR : NIZK RedeemInstance) (A : AnchorSet) (req ctxIss ctxRed cd : Bytes) :
    Option Bytes :=
  if req.length ≠ n then none else
  let nf := req.take nfBytes
  if VR.verify (req.drop nfBytes) ⟨A.keys, nf, ctxIss, ctxRed, cd⟩ then some nf else none

/-- `main`'s Moderator. -/
theorem finalizeRedeemN_main : finalizeRedeemN redeemRequestBytes = finalizeRedeem := rfl

/-- **The Moderator with dedicated label rows** (`24 + 9007`-byte requests). -/
abbrev finalizeRedeemLR :
    NIZK RedeemInstance → AnchorSet → Bytes → Bytes → Bytes → Bytes → Option Bytes :=
  finalizeRedeemN redeemRequestBytesLR

end VoleMole.Spec.Moussaka
