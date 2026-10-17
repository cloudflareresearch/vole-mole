import VoleMole.Arith.Vectors
import VoleMole.Arith.Ratatouille

/-!
# Differential tests of the Ratatouille relations (`ratatouille_issue.txt`, `ratatouille_spend.txt`)

Values generators for `Ratatouille.issueSystem` and `Ratatouille.spendSystem`: they return
`issueValues` / `spendValues`, which `Ratatouille.issueSystem_values` / `spendSystem_values` prove
equal to `System.values` of the generators (the Keccak trees are evaluated with sharing). The
public Keccak inputs that the generators build from the instance (`comState`, `tagState`) are also
compared with the dumped `keccak_in_K`.
-/

namespace VoleMole.Arith.Vectors

open VoleMole.Arith.Ratatouille VoleMole.Arith.Keccak

/-- A byte string of exactly `n` bytes, as a function (zero beyond the end). -/
def Record.ratatouilleBytesN (r : Record) (k : String) (n : ℕ) : Except String (ℕ → UInt8) := do
  let b ← r.bytes k
  if b.size ≠ n then throw s!"key `{k}`: expected {n} bytes, got {b.size}"
  r.byte k

/-- Check that the public Keccak input `keccak_in_K` equals the state the generator builds. -/
def ratatouilleCheckKeccakIn (r : Record) (k : String) (s : State) : Except String Unit := do
  let b ← r.bytes k
  if b.toList ≠ s.toList then throw s!"`{k}` differs from the Lean public Keccak input"

/-- Ratatouille issuance (`ratatouille_issue.txt`). -/
def ratatouilleIssueGenerator : ValuesGenerator := fun _ r => do
  let c ← r.ratatouilleBytesN "c" 32
  let tInit ← r.nat "t_init"
  let ctx ← r.ratatouilleBytesN "ctx_iss" 16
  ratatouilleCheckKeccakIn r "keccak_in_0" (comState zeros ctx tInit zeros)
  pure (issueValues c tInit ctx)

/-- Ratatouille spend (`ratatouille_spend.txt`). -/
def ratatouilleSpendGenerator : ValuesGenerator := fun env r => do
  let pk ← env.pk (← r.get "pk")
  let nf ← r.ratatouilleBytesN "nf" 24
  let d ← r.nat "d"
  let cNext ← r.ratatouilleBytesN "c_next" 32
  let ctx ← r.ratatouilleBytesN "ctx_iss" 16
  let l ← r.coeffs "l" Ratatouille.uovM
  ratatouilleCheckKeccakIn r "keccak_in_0" (comState nf ctx 0 zeros)
  ratatouilleCheckKeccakIn r "keccak_in_1" (tagState zeros 0)
  ratatouilleCheckKeccakIn r "keccak_in_2" (comState zeros ctx 0 zeros)
  pure (spendValues beta GF256.toBits pk nf d cNext ctx l)

end VoleMole.Arith.Vectors
