import VoleMole.ZK.ReadsROExp

/-!
# Audit of the one-proof theorem with expected point charges (`zk_ro_exp`)

* **The read model is satisfiable**: a reader with fixed read sets (`constReads`) is consistent
  and has the budgets of its sets; every event that depends on `H₃`, `H₅` and the cipher only at
  those sets is read by it (`constReads_reads`). So `zk_ro_exp` applies to every such
  distinguisher (`zk_ro_exp_const`).
* **The numerical hypotheses hold at the theft games' budgets**: at `q_E = 2⁶⁴`,
  `221·(q_E + 4607) < 2¹²⁸`, and at `q₅ = q_E = 2⁶⁴`, `βZK < 2⁻⁵⁵` (`βZK_le`).
* **The new bound is never much worse than the worst case**: the charge is at most the
  worst-case budget term, `chZK ≤ q₃/(2¹²⁸ − q₃) + 221·q_E/d_E + q₅·2⁻¹²⁸` (`chZK_le`).

No `sorry`, no `axiom`.
-/

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.ZKPoint2

open VoleMole.Privacy VoleMole.ZK VoleMole.ZK.Sim VoleMole.ZK.IC VoleMole.Verifier
  VoleMole.Verifier.Bridge VoleMole.Arith

variable {p : Params}

/-- A reader with fixed read sets. -/
def constReads (S3 : Finset (Bytes 16)) (S5 : Finset (Bytes 37)) (SE : Finset (Blk × Blk)) :
    PtReads p := ⟨fun _ => S3, fun _ => S5, fun _ => SE⟩

lemma constReads_cons (S3 : Finset (Bytes 16)) (S5 : Finset (Bytes 37)) (SE : Finset (Blk × Blk)) :
    (constReads (p := p) S3 S5 SE).Cons := fun _ _ _ _ _ => ⟨rfl, rfl, rfl⟩

lemma constReads_bnd (S3 : Finset (Bytes 16)) (S5 : Finset (Bytes 37)) (SE : Finset (Blk × Blk)) :
    (constReads (p := p) S3 S5 SE).Bnd S3.card S5.card SE.card :=
  ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ => Finset.card_image_le⟩

/-- An event that depends on the tables only at the fixed sets is read by `constReads`. -/
lemma constReads_reads (S3 : Finset (Bytes 16)) (S5 : Finset (Bytes 37)) (SE : Finset (Blk × Blk))
    (F : VwIC p → Prop)
    (hF : ∀ v G3 G5 E, (∀ k ∈ S3, v.2.1 k = G3 k) → (∀ k ∈ S5, v.2.2.2.1 k = G5 k) →
      (∀ kz ∈ SE, v.2.2.2.2 kz.1 kz.2 = E kz.1 kz.2) → (F (PtReads.withT v G3 G5 E) ↔ F v)) :
    (constReads S3 S5 SE).Reads F := fun v G3 G5 E h => hF v G3 G5 E h.1 h.2.1 h.2.2

/-- **`zk_ro_exp` for a distinguisher with fixed read sets.** -/
theorem zk_ro_exp_const (Hb : Hashes) (st : Statement) (w : ByteArray)
    {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (S3 : Finset (Bytes 16)) (S5 : Finset (Bytes 37)) (SE : Finset (Blk × Blk))
    (h3 : (S3.card : ℝ) < 2 ^ 128) (hE : 221 * ((SE.card + 4607 : ℕ) : ℝ) < 2 ^ 128)
    (hβ : βZK S5.card SE.card < 1)
    (D : Except String ByteArray → Tab3 → Sh st.params → Prop)
    (hD : ∀ (v : VwIC st.params) G3 G5 E, (∀ k ∈ S3, v.2.1 k = G3 k) → (∀ k ∈ S5, v.2.2.2.1 k = G5 k) →
      (∀ kz ∈ SE, v.2.2.2.2 kz.1 kz.2 = E kz.1 kz.2) →
      (D v.1 G3 (v.2.2.1, G5, E) ↔ D v.1 v.2.1 (v.2.2.1, v.2.2.2.1, v.2.2.2.2))) :
    |pr ((Bytes 16 × Tab3) × Sh st.params) (fun a =>
        D (realRO st.params Hb st w a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((SimCoins st.params × Tab3) × Sh st.params) (fun a =>
        D (simulate st.params a.1.1) a.1.2 (progRO st.params Hb st a.1.1 a.2))| ≤
      (εZK SE.card + exP ((Bytes 16 × Tab3) × Sh st.params) (fun a =>
        chZK (constReads S3 S5 SE) Hb st S3.card SE.card
          (toVw (realRO st.params Hb st w a.1.1 a.1.2 a.2) a.1.2 a.2))) /
        (1 - βZK S5.card SE.card) :=
  zk_ro_exp Hb st w hlr hzk hHb hp (constReads S3 S5 SE) (constReads_cons S3 S5 SE)
    (constReads_bnd S3 S5 SE) h3 hE hβ D (constReads_reads S3 S5 SE _ hD)

/-- The cipher hypothesis at `q_E = 2⁶⁴`. -/
example : 221 * (((2 ^ 64 : ℕ) + 4607 : ℕ) : ℝ) < 2 ^ 128 := by norm_num

/-- **The budget factor at `q₅ = q_E = 2⁶⁴`** is below `2⁻⁵⁵`. -/
theorem βZK_le : βZK (2 ^ 64) (2 ^ 64) < 1 / 2 ^ 55 := by
  unfold βZK dEZK
  push_cast
  rw [div_mul_eq_mul_div]
  have hd : (0 : ℝ) < 2 ^ 128 - 221 * (2 ^ 64 + 4607) := by norm_num
  have h1 : 221 * (2 : ℝ) ^ 64 / (2 ^ 128 - 221 * (2 ^ 64 + 4607)) < 1 / 2 ^ 56 := by
    rw [div_lt_div_iff₀ hd (by norm_num)]; norm_num
  have h2 : 1 / (2 : ℝ) ^ 128 * 2 ^ 64 < 1 / 2 ^ 56 := by norm_num
  have : (1 : ℝ) / 2 ^ 56 + 1 / 2 ^ 56 = 1 / 2 ^ 55 := by norm_num
  linarith

/-- **The expected charge is at most the worst-case budget term.** -/
theorem chZK_le (R : PtReads p) (Hb : Hashes) (st : Statement) {q3 q5 qE : ℕ} (hb : R.Bnd q3 q5 qE)
    (h3 : (q3 : ℝ) < 2 ^ 128) (hE : 221 * ((qE + 4607 : ℕ) : ℝ) < 2 ^ 128) (v : VwIC p) :
    chZK R Hb st q3 qE v ≤ q3 / (2 ^ 128 - q3) + 221 * qE / dEZK qE + q5 / 2 ^ 128 := by
  have hd : 0 < dEZK qE := by unfold dEZK; linarith
  unfold chZK
  have a := R.ch3_le hb v
  have b := R.chE_le Hb st hb v
  have c := R.ch5_le Hb CrtGen.tables st hb v
  gcongr

end VoleMole.Audit.ZKPoint2
