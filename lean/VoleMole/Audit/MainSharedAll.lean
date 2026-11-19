import VoleMole.Audit.MainShared23
import VoleMole.Privacy.MoussakaMainSharedAll
import VoleMole.Privacy.RatatouilleMainSharedAll
import VoleMole.Privacy.MoussakaNCMain
import VoleMole.Audit.Liveness

/-!
# Audit of the results on `main` with one shared `H₃` (`lean/docs/zk.md` §4.2)

* **`anonymity_main_sharedAll` and `unlinkability_main_sharedAll` apply**: for the adversaries
  `mH`, `rH` (constant guess, no table reads) every hypothesis holds, with `εhide = 0`.
* **The guess may read the one `H₃`**: `mH3 k ρ` and `rH3 k ρ` read it at one point
  `(prefix k, ρ)` (any prefix, e.g. a Client's), and `ConsH 1 0` holds; the theorems apply with
  the trivial hiding bound `εhide = 1` (Moussaka) or any bound on the hiding reductions
  (Ratatouille). So the consistency condition does not force a guess that
  ignores `H₃`.
* **`anonymityNC_main` (Moussaka 4(b') on `main`) applies with a non-trivial signer and no abort
  term**: the Moderator `ncm d` uses the key `keyI d` of `Audit/Liveness.lean` for both Anchors,
  whose trapdoor signer `skI d` never fails (`skI_some`), so `φ = 0` (`phi_skI`); the index rule
  is `Rule.ofIdx idxEval` (`IdxSound`, `ruleNC_ofIdx`). Every hypothesis holds and every term of the bound is a number.
* **The prefix-collision term is a number**: `pr_coll_le`, `pr_collR_le` bound it by `2⁻¹²⁸`
  (Moussaka) and `2·2⁻¹²⁸` (Ratatouille) per world, for every adversary.

No `sorry`, no `axiom`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.MainSharedAll

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Privacy.PU VoleMole.Verifier VoleMole.Verifier.Bridge

section Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka

/-- The colluding adversary with one `H₃`, a constant guess and no table reads. -/
def mH : AdversaryH :=
  ⟨fun _ => 0, fun _ => 0, fun _ => Audit.k0, fun _ _ _ _ => 0, fun _ _ _ => (Audit.S0, []),
    fun _ _ _ _ _ => True, fun _ _ _ _ _ => ∅⟩

lemma rdTH_const {X : Sort*} (x : X) : RdTH (fun _ _ => x) (fun _ _ => ∅) 0 0 :=
  ⟨fun _ _ _ _ => rfl, ⟨fun _ _ => ∅, fun _ _ => le_rfl, fun _ _ _ _ => rfl⟩,
    ⟨fun _ _ => ∅, fun _ _ => le_rfl, fun _ _ _ _ => rfl⟩⟩

theorem mH_cons : mH.ConsH 0 0 := ⟨fun _ _ _ => rdTH_const True, fun _ _ _ => rdTH_const ∅⟩

/-- `anonymity_main_sharedAll` for `mH`. -/
example (idx : Rule) :=
  anonymity_main_sharedAll mH idx mH_cons (εhide := 0)
    (fun _ _ _ => (Audit.hidingAdv_true _ _).le)

/-- An adversary whose guess reads the one `H₃` at the point `(k, ρ)`. -/
def mH3 (k : Pre) (ρ : ZK.Sim.Bytes 16) : AdversaryH :=
  ⟨fun _ => 0, fun _ => 0, fun _ => Audit.k0, fun _ _ _ _ => 0, fun _ _ _ => (Audit.S0, []),
    fun _ _ _ _ T => T k ρ = fun _ => 0, fun _ _ _ _ _ => ∅⟩

/-- **`ConsH` holds for a guess that reads `H₃`**: one point, no cipher or `H₅` reads. -/
theorem mH3_cons (k : Pre) (ρ : ZK.Sim.Bytes 16) : (mH3 k ρ).ConsH 1 0 :=
  ⟨fun _ _ _ => ⟨fun _ _ _ _ => rfl, ⟨fun _ _ => ∅, fun _ _ => Nat.zero_le _, fun _ _ _ _ => rfl⟩,
      ⟨fun _ _ => {(k, ρ)}, fun _ _ => le_rfl, fun _ T T' h => by
        show (T' k ρ = fun _ => 0) = (T k ρ = fun _ => 0)
        rw [h (k, ρ) (mem_singleton_self _)]⟩⟩,
    fun _ _ _ => ⟨fun _ _ _ _ => rfl, ⟨fun _ _ => ∅, fun _ _ => Nat.zero_le _, fun _ _ _ _ => rfl⟩,
      ⟨fun _ _ => ∅, fun _ _ => Nat.zero_le _, fun _ _ _ _ => rfl⟩⟩⟩

/-- `anonymity_main_sharedAll` for the `H₃`-reading adversary `mH3 k ρ` (trivial `εhide = 1`). -/
example (k : Pre) (ρ : ZK.Sim.Bytes 16) (idx : Rule) :=
  anonymity_main_sharedAll (mH3 k ρ) idx (mH3_cons k ρ) (εhide := 1)
    (fun _ _ _ => Audit.hidingAdv_le_one _ _ _)

/-- The prefix-collision term of either world is at most `2⁻¹²⁸`, for every adversary. -/
example (A : AdversaryH) (idx : Rule) (b : Bool) :=
  pr_coll_le A idx b

end Moussaka

section Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.Privacy.Ratatouille

/-- The malicious Issuer with one `H₃`, `T_init = 1`, a constant guess and no table reads. -/
def rH : AdversaryRH :=
  ⟨default, default, 1, fun _ _ => default, fun _ => 0, fun _ _ => default, fun _ _ => 0,
    fun _ _ _ => True, fun _ _ _ => ∅⟩

lemma rdTHR_const {X : Sort*} (x : X) : RdTHR (fun _ _ => x) (fun _ _ => ∅) 0 0 :=
  ⟨fun _ _ _ _ => rfl, ⟨fun _ _ => ∅, fun _ _ => le_rfl, fun _ _ _ _ => rfl⟩,
    ⟨fun _ _ => ∅, fun _ _ => le_rfl, fun _ _ _ _ => rfl⟩⟩

theorem rH_cons : rH.ConsH 0 0 := ⟨fun _ => rdTHR_const True, fun _ => rdTHR_const ∅⟩

/-- `unlinkability_main_sharedAll` for `rH`. -/
example [HasPrg] (b₁ b₂ b₁' b₂' : Bool) :=
  unlinkability_main_sharedAll rH rH_cons (εhide := 0)
    (fun _ _ _ _ => (Audit.hidingAdvR_true _).le) b₁ b₂ b₁' b₂'

/-- An Issuer whose guess reads the one `H₃` at the point `(k, ρ)`. -/
def rH3 (k : Pre) (ρ : ZK.Sim.Bytes 16) : AdversaryRH :=
  ⟨default, default, 1, fun _ _ => default, fun _ => 0, fun _ _ => default, fun _ _ => 0,
    fun _ _ T => T k ρ = fun _ => 0, fun _ _ _ => ∅⟩

theorem rH3_cons (k : Pre) (ρ : ZK.Sim.Bytes 16) : (rH3 k ρ).ConsH 1 0 :=
  ⟨fun _ => ⟨fun _ _ _ _ => rfl, ⟨fun _ _ => ∅, fun _ _ => Nat.zero_le _, fun _ _ _ _ => rfl⟩,
      ⟨fun _ _ => {(k, ρ)}, fun _ _ => le_rfl, fun _ T T' h => by
        show (T' k ρ = fun _ => 0) = (T k ρ = fun _ => 0)
        rw [h (k, ρ) (mem_singleton_self _)]⟩⟩,
    fun _ => ⟨fun _ _ _ _ => rfl, ⟨fun _ _ => ∅, fun _ _ => Nat.zero_le _, fun _ _ _ _ => rfl⟩,
      ⟨fun _ _ => ∅, fun _ _ => Nat.zero_le _, fun _ _ _ _ => rfl⟩⟩⟩

/-- `unlinkability_main_sharedAll` for the `H₃`-reading Issuer `rH3 k ρ`, for any bound on its
hiding reductions. -/
example [HasPrg] (k : Pre) (ρ : ZK.Sim.Bytes 16) (εhide : ℝ)
    (hh : ∀ T b₁ b₂ a, hidingAdv (rH3 k ρ).ctx (redSR23 ((rH3 k ρ).withH T) b₁ b₂ a) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :=
  unlinkability_main_sharedAll (rH3 k ρ) (rH3_cons k ρ) hh b₁ b₂ b₁' b₂'

/-- The prefix-collision term of either world is at most `2·2⁻¹²⁸`, for every Issuer. -/
example [HasPrg] (A : AdversaryRH) (b₁ b₂ : Bool) := pr_collR_le A b₁ b₂

end Ratatouille

section NCMain

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka VoleMole.Audit.Live

/-- A non-colluding Moderator on `main` with the key `keyI d` for both Anchors, a constant guess and
no table reads. -/
noncomputable def ncm (d : Spec.Bytes) : AdversaryNCM :=
  ⟨fun _ => 0, fun _ => 0, fun _ => keyI d, fun _ => (Audit.S0, []), fun _ _ _ => True,
    fun _ _ _ => ∅⟩

theorem ncm_cons (d : Spec.Bytes) : (ncm d).ConsH 0 0 :=
  ⟨fun _ => rdTH_const True, fun _ => rdTH_const ∅⟩

/-- **The abort term of the trapdoor signer is `0`**: it never fails. -/
theorem phi_skI (d : Spec.Bytes) (A : AdversaryNC) (c : Bool) : phi A (fun _ => skI d) c = 0 := by
  unfold phi
  rw [pr_congr (Q := fun _ => False) fun y => by simp [skI_some]]
  exact pr_false

/-- `anonymityNC_main` for `ncm d` with the trapdoor signers: every hypothesis holds, and the
abort term vanishes. -/
example (d : Spec.Bytes) (PI : NIZK IssueInstance) :
    |realNCM (ncm d) (Rule.ofIdx Audit.idxEval) PI (fun _ => skI d) false -
        realNCM (ncm d) (Rule.ofIdx Audit.idxEval) PI (fun _ => skI d) true| ≤
      30 * (εS 0 (0 + 8 * 4607) + Δ23 9) +
        15 * (8 * noHitProb + (4 * ((0 : ℕ) + 625) + 626) / 2 ^ 128) + 2 / 2 ^ 128 := by
  have h := anonymityNC_main (ncm d) (Rule.ofIdx Audit.idxEval) PI (fun _ => skI d)
    (fun _ => skI_correct d) (ruleNC_ofIdx _ _ Audit.idxEval_sound) (ncm_cons d) (q5 := 0)
    (fun _ _ _ => le_rfl)
  rw [phi_skI, phi_skI] at h
  simpa using h

end NCMain

end VoleMole.Audit.MainSharedAll
