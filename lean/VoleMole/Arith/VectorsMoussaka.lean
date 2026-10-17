import VoleMole.Arith.Vectors
import VoleMole.Arith.Moussaka

/-!
# Differential tests of Moussaka issue and redeem (`moussaka_issue.txt`, `moussaka_redeem.txt`)

Both relations contain a Keccak-p[800] gadget, whose `Expr` trees are exponential to evaluate, so
these are values generators: `Moussaka.issueValues` and `Moussaka.redeemValues` compute the
constraint values with sharing and are proved equal to `System.values` of `issueSystem` and
`redeemSystem` (`issueValues_eq`, `redeemValues_eq`).

The Keccak input's public part is computed in Lean (`issuePub`, `redeemPub`, i.e.
`encode_com_state` with the secret fields zeroed) and compared with the C++ `keccak_in_0`.
-/

namespace VoleMole.Arith.Vectors

open VoleMole.Arith.Keccak

/-- Check that a Lean-computed public Keccak state equals the record's `keccak_in_0`. -/
def checkKeccakIn (r : Record) (pub : State) : Except String Unit := do
  let b ← r.bytes "keccak_in_0"
  if b.size ≠ 100 then throw s!"keccak_in_0: expected 100 bytes, got {b.size}"
  for i in List.finRange 100 do
    if pub[i] ≠ b.get! i.val then
      throw s!"keccak_in_0 differs from the Lean encode_com_state at byte {i.val}"

/-- Check the length of a byte field. -/
def checkLen (r : Record) (k : String) (n : ℕ) : Except String Unit := do
  let b ← r.bytes k
  if b.size ≠ n then throw s!"{k}: expected {n} bytes, got {b.size}"

/-- Moussaka issuance (`moussaka_issue.txt`): instance `t`, `ctx_iss`. -/
def moussakaIssueGenerator : ValuesGenerator := fun _ r => do
  checkLen r "t" 45
  checkLen r "ctx_iss" 16
  let t ← r.byte "t"
  let ctxIss ← r.byte "ctx_iss"
  checkKeccakIn r (Moussaka.issuePub ctxIss)
  pure (Moussaka.issueValues (F := GF128) (fun k => t k.val) ctxIss)

/-- Moussaka redemption (`moussaka_redeem.txt`): instance `anchors`, `nf`, `ctx_iss`, `ctx_red`
(`challenge_digest` enters only the transcript hash), and the combination coefficients `l`. -/
def moussakaRedeemGenerator : ValuesGenerator := fun env r => do
  let anchors ← env.pks (← r.get "anchors")
  if anchors.length > 64 then throw s!"{anchors.length} anchors > MAX_ANCHORS"
  checkLen r "nf" 24
  checkLen r "ctx_iss" 16
  checkLen r "ctx_red" 16
  let nf ← r.byte "nf"
  let ctxIss ← r.byte "ctx_iss"
  let ctxRed ← r.byte "ctx_red"
  let l ← r.coeffs "l" Moussaka.M
  checkKeccakIn r (Moussaka.redeemPub nf ctxIss ctxRed)
  pure (Moussaka.redeemValues beta GF256.toBits anchors nf ctxIss ctxRed l)

end VoleMole.Arith.Vectors
