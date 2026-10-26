import VoleMole.Verifier.ProverKats

/-!
# `lake exe prover_vectors`

Runs `ProverKats.main`: the Lean prover (`Verifier/Prover.lean`) on every KAT proof, byte for byte
against the C++, plus the completeness smoke tests. Usage:
`lake exe prover_vectors [TESTS_DIR [main|labelrows|none [FILTER]]]` (default `../tests`, `main`).
Exits with status 1 on any failure.
-/

def main (args : List String) : IO UInt32 := VoleMole.Verifier.ProverKats.main args
