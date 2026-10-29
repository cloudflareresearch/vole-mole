import VoleMole.ZK.SimKats

/-!
# `lake exe zk_sim`

Runs `SimKats.main`: on every KAT run, the ideal-tape prover at the run's own tape reproduces the
proof, and the verifier accepts the simulator's and the ideal-tape prover's proofs under the
programmed oracle. Usage: `lake exe zk_sim [TESTS_DIR [main|labelrows|none [FILTER]]]`. Exits with
status 1 on any failure.
-/

def main (args : List String) : IO UInt32 := VoleMole.ZK.SimKats.main args
