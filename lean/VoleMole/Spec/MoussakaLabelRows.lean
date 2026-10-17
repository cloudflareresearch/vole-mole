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

end VoleMole.Spec.Moussaka
