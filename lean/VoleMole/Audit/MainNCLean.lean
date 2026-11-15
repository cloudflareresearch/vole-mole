import VoleMole.Audit.MainSharedAll
import VoleMole.Privacy.MoussakaNCMainLean

/-!
# Audit of Moussaka 4(b') on `main` with the Lean issuance prover (`Privacy/MoussakaNCMainLean.lean`)

* **`anonymityNC_main_lean` applies with a non-trivial signer and no abort term**: the Moderator
  `ncm d` of `Audit/MainSharedAll.lean` (the key `keyI d` for both Anchors, trapdoor signers that
  never fail, `φ = 0`), the index rule `Rule.ofIdx idxEval`. Every hypothesis holds; the bound is
  that of `anonymityNC_main` plus `4·2⁻¹¹³`, every term a number.
* **The verdict hop's failure event is a number for every Moderator**: each Client's issuance
  fails (`issFail`, the event of `complete_rom_ic`) with probability `≤ 2⁻¹¹³`
  (`pr_issFail_le`), and an honest request has `main`'s request length (`issueReq_length`).

No `sorry`, no `axiom`.
-/

namespace VoleMole.Audit.MainNCLean

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka VoleMole.Audit.Live
open VoleMole.Audit.MainSharedAll

/-- `anonymityNC_main_lean` for `ncm d` with the trapdoor signers: every hypothesis holds, and the
abort term vanishes. -/
example [HasPrg] (d : Spec.Bytes) :
    |realNCML (ncm d) (Rule.ofIdx Audit.idxEval) (fun _ => skI d) false -
        realNCML (ncm d) (Rule.ofIdx Audit.idxEval) (fun _ => skI d) true| ≤
      30 * (εS 0 (0 + 8 * 4607) + Δ23 9) +
        15 * (8 * noHitProb + (4 * ((0 : ℕ) + 625) + 626) / 2 ^ 128) + 2 / 2 ^ 128 +
        4 / 2 ^ 113 := by
  have h := anonymityNC_main_lean (ncm d) (Rule.ofIdx Audit.idxEval) (fun _ => skI d)
    (fun _ => skI_correct d) (ruleNC_ofIdx _ _ Audit.idxEval_sound) (ncm_cons d) (q5 := 0)
    (fun _ _ _ => le_rfl)
  rw [MainSharedAll.phi_skI, MainSharedAll.phi_skI] at h
  simpa using h

/-- Each Client's issuance on the shared tables fails with probability at most `2⁻¹¹³`. -/
example [HasPrg] (A : AdversaryNCM) (c : Bool) := pr_issFail_le A c

end VoleMole.Audit.MainNCLean
