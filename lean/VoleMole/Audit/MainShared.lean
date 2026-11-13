import VoleMole.Audit.MainPU
import VoleMole.Privacy.MoussakaMainSharedPU

/-!
# Audit of the shared-table results on `main` (`lean/docs/zk.md` §4.2)

* **`anonymity_main_shared` applies.** With the adversary `mS` (constant guess, empty `H₅` read
  set) every hypothesis holds (`AdversaryS.Cons 0 0`, hiding with `εhide = 0`); the four `puAdv`
  terms stay as they are, since they are terms of the bound and not hypotheses.
* **`AdversaryS.Cons` is satisfied by a guess that reads the shared `H₅` table**: `mR k₀` reads
  it at the key `k₀`, with read set `{k₀}` (`mR_cons`). So the consistency condition does not
  force a table-independent guess, and `anonymity_main_shared0` applies to `mR k₀` for every
  bound `εhide ≥ 1` on its hiding reductions (`hidingAdv_le_one`).
* **The predictors name few candidates**: `card_predS_le` at `q₅ = 0` for `mS`, at most `2498`.
* **(PU) is not vacuous and not unconditional**: the exhaustive predictor against the concrete
  `Com` has advantage `1` (`PU.puAdv_bruteForce`), so the `puAdv` terms cannot be bounded for all
  predictors.
* **`main_shared_le` and `prove_reads`** take the deterministic hypotheses of
  `zk_rom_ic_h23_main_num` only (`MainP`, `SmallParams`, `HashesWF`, valid statements,
  `GValid`): they are discharged for Moussaka's statements inside `real_sim_shared`.

No `sorry`, no `axiom`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.MainShared

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Privacy.PU VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka VoleMole.Arith

/-- The colluding adversary on `main` with shared tables, a constant guess and no table reads. -/
def mS : AdversaryS :=
  ⟨fun _ => 0, fun _ => 0, fun _ => Audit.k0, fun _ _ _ _ => 0, fun _ _ _ => (Audit.S0, []),
    fun _ _ _ _ => True, fun _ _ _ _ => ∅⟩

lemma rdT_const {X : Sort*} (x : X) :
    RdT (p₁ := pIm) (p₂ := pIm) (p₃ := pRm) (p₄ := pRm) (fun _ => x) (fun _ => ∅) 0 0 :=
  ⟨fun _ _ _ => rfl, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩⟩

theorem mS_cons : mS.Cons 0 0 := ⟨fun _ _ _ => rdT_const True, fun _ _ _ => rdT_const ∅⟩

/-- `anonymity_main_shared` for `mS`. -/
example (idx : AnchorSet → UOVKey → ℕ) :=
  anonymity_main_shared mS idx mS_cons (εhide := 0) (fun _ _ => (Audit.hidingAdv_true _ _).le)

/-- The predictors of `mS` name at most `2498` candidates. -/
example (idx : AnchorSet → UOVKey → ℕ) (b : Bool) (t₀ t₁ n₀ n₁ : Spec.Bytes) (a : AuxS) (c : Bool) :
    (predS mS idx b t₀ t₁ n₀ n₁ a c).card ≤ 2 * (0 + 1249) :=
  card_predS_le mS idx (q5 := 0) (fun _ _ _ _ => le_rfl) b t₀ t₁ n₀ n₁ a c

/-- An adversary whose guess reads the shared `H₅` table at the key `k₀`. -/
def mR (k₀ : ZK.Sim.Bytes 37) : AdversaryS :=
  ⟨fun _ => 0, fun _ => 0, fun _ => Audit.k0, fun _ _ _ _ => 0, fun _ _ _ => (Audit.S0, []),
    fun _ _ _ v => v.1.1 k₀ = fun _ => 0, fun _ _ _ _ => {k₀}⟩

/-- **`Cons` holds for a guess that reads `H₅`**: no slice or cipher reads, `H₅` at `{k₀}`. -/
theorem mR_cons (k₀ : ZK.Sim.Bytes 37) : (mR k₀).Cons 0 0 :=
  ⟨fun _ _ _ => ⟨fun t G5 h => by
      show (G5 k₀ = fun _ => 0) = (t.1.1 k₀ = fun _ => 0)
      rw [← h k₀ (mem_singleton_self _)],
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩⟩,
   fun _ _ _ => ⟨fun _ _ _ => rfl,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩⟩⟩

/-- `anonymity_main_shared` for the `H₅`-reading adversary `mR k₀` (with the trivial `εhide = 1`:
the theorem's hypotheses are satisfiable for an adversary that reads the shared table). -/
example (k₀ : ZK.Sim.Bytes 37) (idx : AnchorSet → UOVKey → ℕ) :=
  anonymity_main_shared (mR k₀) idx (mR_cons k₀) (εhide := 1)
    (fun _ _ => Audit.hidingAdv_le_one _ _ _)

/-- **(PU) for the concrete `Com` is computational**: the exhaustive predictor has advantage `1`. -/
example (A : AdversaryS) :
    puAdv (comM A.toM) (bruteForce (Aux := Unit) (comM A.toM)) = 1 :=
  puAdv_bruteForce _

end VoleMole.Audit.MainShared
