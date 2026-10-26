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

end VoleMole.Spec.MoussakaUnbound
