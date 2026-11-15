import VoleMole.Theft.JointProver
import VoleMole.Theft.JointNum
import VoleMole.Theft.DeltaBound

/-!
# Audit of the joint many-proof step with point charges (zk-point3)

* **The class of events is not empty**: a game reader with fixed read sets (`constG`) is
  consistent (`constG_cons`), and every event that depends on the slices, `H₅` and the cipher only
  at those sets is read by it (`constG_reads`); so `real_sim_leN_lean` applies to such events.
* **The real-prover confinement hypothesis holds for the Lean issuance prover** of Ratatouille:
  `realPtRd_conf` at `stI x`, for every instance with a witness (`rata_conf`).
* **The overlap factor does not break the target**: at `N = 2³¹`, with `J` up to
  `(1 + N²·2⁻⁶⁴)·zkB` (`5/4` of one hop's budget term), the joint bound plus `ROM/`'s error is still
  `≤ 2⁻⁵⁴` (`jointK_at_2pow31`).
* **Two different 16-byte `iv`s have disjoint gate inputs** (`gate5_disjoint`).

No `sorry`, no `axiom`.
-/

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.ZKPoint3

open VoleMole.Privacy VoleMole.ZK VoleMole.ZK.Sim VoleMole.ZK.IC VoleMole.Verifier
  VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.Theft

variable {Ω O : Type*} {p : Params} {X : Type} {N : ℕ}

/-- A game reader with fixed read sets. -/
def constG (S3 : Fin N → Finset (Bytes 16)) (S5 : Finset (Bytes 37)) (SE : Finset (Blk × Blk)) :
    GRd Ω O p X N := ⟨fun _ _ _ _ => S3, fun _ _ _ _ => S5, fun _ _ _ _ => SE⟩

lemma constG_cons (S3 : Fin N → Finset (Bytes 16)) (S5 : Finset (Bytes 37))
    (SE : Finset (Blk × Blk)) : (constG (Ω := Ω) (O := O) (p := p) (X := X) S3 S5 SE).Cons :=
  fun _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl⟩

/-- An event that depends on the tables only at the fixed sets is read by `constG`. -/
lemma constG_reads (S3 : Fin N → Finset (Bytes 16)) (S5 : Finset (Bytes 37))
    (SE : Finset (Blk × Blk)) (F : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X → Prop)
    (hF : ∀ ω l gs t gs' t', (constG S3 S5 SE).Agree ω l gs t gs' t' →
      (F (ω, l, gs', t') ↔ F (ω, l, gs, t))) :
    (constG S3 S5 SE).Reads F := hF

section Rata

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

/-- **The confinement of the real prover, for Ratatouille's Lean issuance prover.** -/
theorem rata_conf (x : IssueInstance) (w : IssueWitness) (hxw : IssueRel x w) (ρ : Sim.Bytes 16)
    (G3 : Tab3) :
    Conf (realPtRd Hashes.shake (stI x) (encI x w) hashesWF_shake ρ G3)
      (fun s => ivV Hashes.shake (stI x) (realRO (stI x).params Hashes.shake (stI x) (encI x w) ρ G3 s))
      624 4607 := by
  obtain ⟨hl1, -, -, hl2⟩ := labelRows_sizes (p := (stI x).params) rfl
  exact realPtRd_conf (zkHypI x w hxw) hashesWF_shake (by omega) ρ G3

end Rata

set_option exponentiation.threshold 1100 in
/-- **At `N = 2³¹` and the overlap factor, the target `2⁻⁵⁴` is reached.** -/
theorem jointK_at_2pow31 :
    (2 ^ 31 : ℕ) * zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50) < 1 ∧
      ((2 ^ 31 : ℕ) / 2 ^ 100 + (1 + ((2 ^ 31 : ℕ) : ℝ) ^ 2 / 2 ^ 64) *
        zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50)) /
        (1 - (2 ^ 31 : ℕ) * zkB (2 ^ 65) (2 ^ 65 + 2 ^ 41) (2 ^ 65 + 2 ^ 50)) + 13 / 2 ^ 63 ≤
      1 / 2 ^ 54 :=
  jointNumK_le le_rfl le_rfl le_rfl (zkB_nonneg _ _ _) le_rfl le_rfl

/-- **Two different 16-byte `iv`s have disjoint gate inputs.** -/
theorem gate5_disjoint {T : CrtTables} {a b : ByteArray} (ha : a.size = 16) (hb : b.size = 16)
    (hab : a ≠ b) (k : Bytes 37) : ¬ (Gate5 p T a k ∧ Gate5 p T b k) :=
  fun h => hab (gate5_iv_eq h.1 h.2 ha hb)

end VoleMole.Audit.ZKPoint3
