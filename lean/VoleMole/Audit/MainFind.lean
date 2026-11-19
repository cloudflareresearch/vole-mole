import VoleMole.Audit.MainSharedAll
import VoleMole.Privacy.MoussakaMainFind

/-!
# Audit of Moussaka 4(a) and 4(b') on `main` for `main`'s Client (`find_issuer`)

* **`anonymity_main_sharedAll_find` applies**: for the adversary `mH` of `Audit/MainSharedAll.lean`
  (constant guess, no table reads) every hypothesis holds with `εhide = 0`, and for the
  `H₃`-reading `mH3 k ρ` with `εhide = 1`.
* **`anonymityNC_main_find` applies with a non-trivial signer, sets that contain both issuers and
  no abort term**: the Moderator `ncmF` has the two keys `pkL c` of `Audit/Liveness.lean`
  (trapdoor signers `skI (digL c)` that never fail, so `φ = 0`) and chooses the set `SL` of both
  keys on each side, so `MoussakaFind.Contains` holds (`ncmF_contains`); the rule `findIdx` is
  then sound with outcome `true` (`ruleNC_findIdx`). Every hypothesis holds and every term of the
  bound is a number.
* **`unlinkabilityNC_main_find` applies**: one key `keyI d`, any sets (`ncm d`).

No `sorry`, no `axiom`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.MainFind

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Privacy.PU VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka VoleMole.Audit.Live
open VoleMole.Audit.MainSharedAll

/-- `anonymity_main_sharedAll_find` for `mH`. -/
example :=
  anonymity_main_sharedAll_find mH mH_cons (εhide := 0)
    (fun _ _ _ => (Audit.hidingAdv_true _ _).le)

/-- `anonymity_main_sharedAll_find` for the `H₃`-reading `mH3 k ρ`. -/
example (k : Pre) (ρ : ZK.Sim.Bytes 16) :=
  anonymity_main_sharedAll_find (mH3 k ρ) (mH3_cons k ρ) (εhide := 1)
    (fun _ _ _ => Audit.hidingAdv_le_one _ _ _)

/-- A non-colluding Moderator on `main` with the two keys `pkL`, the set `SL` of both on each
side, a constant guess and no table reads. -/
noncomputable def ncmF : AdversaryNCM :=
  ⟨fun _ => 0, fun _ => 0, pkL, fun _ => (SL, []), fun _ _ _ => True, fun _ _ _ => ∅⟩

theorem ncmF_cons : ncmF.ConsH 0 0 := ⟨fun _ => rdTH_const True, fun _ => rdTH_const ∅⟩

/-- **Both sets contain both issuers.** -/
theorem ncmF_contains : MoussakaFind.Contains ncmF.nc := fun c _ =>
  ⟨pkL c, by cases c <;> simp [AdversaryNCM.nc, ncmF, SL], rfl⟩

/-- The abort term of the trapdoor signers is `0`. -/
theorem phi_skL (A : AdversaryNC) (c : Bool) : phi A (fun c => skI (digL c)) c = 0 := by
  unfold phi
  rw [pr_congr (Q := fun _ => False) fun y => by simp [skI_some]]
  exact pr_false

/-- `anonymityNC_main_find` for `ncmF`: every hypothesis holds, and the abort term vanishes. -/
example (PI : NIZK IssueInstance) :
    |realNCM ncmF findIdx PI (fun c => skI (digL c)) false -
        realNCM ncmF findIdx PI (fun c => skI (digL c)) true| ≤
      30 * (εS 0 (0 + 8 * 4607) + Δ23 9) +
        15 * (8 * noHitProb + (4 * ((0 : ℕ) + 625) + 626) / 2 ^ 128) + 2 / 2 ^ 128 := by
  have h := anonymityNC_main_find ncmF PI (fun c => skI (digL c)) (fun c => skI_correct _)
    ncmF_contains ncmF_cons (q5 := 0) (fun _ _ _ => le_rfl)
  rw [phi_skL, phi_skL] at h
  simpa using h

/-- `unlinkabilityNC_main_find` for `ncm d` (one key, any sets). -/
example (d : Spec.Bytes) (PI : NIZK IssueInstance) :=
  unlinkabilityNC_main_find (ncm d) PI (fun _ => skI d) (fun _ => skI_correct d) rfl rfl
    (ncm_cons d) (q5 := 0) (fun _ _ _ => le_rfl)

end VoleMole.Audit.MainFind
