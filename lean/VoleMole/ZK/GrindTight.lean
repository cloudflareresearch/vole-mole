import VoleMole.ZK.AcceptVar
import VoleMole.ZK.GrindNum
import VoleMole.ZK.HopsICPerm
import VoleMole.ZK.TwoPhaseIC
import VoleMole.ZK.SimAcceptFull

/-!
# The grinding term with the second-moment bound (`lean/docs/zk.md` §10.1)

With `|A| ≥ 2¹¹⁴` (`Accept.card_accSet_ge_114`, `ZK/AcceptVar.lean`) in place of `2¹¹¹`:

* **`pr_hitZero_le_114`**: `Pr[the first accepted answer is 0] ≤ 1/|A| ≤ 2⁻¹¹⁴`. This is
  `Pr[Δ' = 0]` for the prover's (and the simulator's) accepted `Δ` (`tDL_eq_zero`).
* **`grindBad_num_114`**: `Pr[GrindBad] ≤ 2^{−2¹⁵} + 2⁻¹¹⁴`; **`grindBad_le_113`**: `≤ 2⁻¹¹³`.
* The numeric headline bounds with `2⁻¹¹³` in place of `2⁻¹¹⁰`: `zk_rom_ic_h23_num113`,
  `zk_rom_h23_num113`, `zk_rom_ic_h23_num113_perm`, `zk2_rom_ic_h23_num113`, and
  `pr_simulateRO_reject_114` / `pr_simulateRO_reject_113` for the simulator.

`Pr[Δ' = 0]` is `Pr[some answer is accepted]/|A|` exactly (given a hit, the accepted `Δ` is
uniform on `A`), and `|A| ≈ 0.397·2¹²⁰` by sampling, so its true value is `≈ 2⁻¹¹⁸·⁶⁷`, not the
`2⁻¹²⁰` of a uniform `Δ'`: grinding conditions `Δ'` on acceptance, and `|A| ≤ 2¹²⁰` makes
`2⁻¹²⁰` a lower bound, not an upper one. The proved `2⁻¹¹⁴` is the second-moment bound on `|A|`;
the remaining `≈ 4.7` bits are the box and the slack of Chebyshev (`ZK/AcceptVar.lean`).
-/

open Finset

-- (As in `ZK/HopsH23.lean`: the coin types' `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
open VoleMole.ZK.Accept VoleMole.ZK.IC

/-! ## The grinding term -/

/-- **`Pr[the first accepted answer is 0] ≤ 2⁻¹¹⁴`**. -/
theorem pr_hitZero_le_114 : pr Grind HitZero ≤ 1 / 2 ^ 114 := by
  refine pr_hitZero_le.trans ?_
  rw [div_le_div_iff₀ (by exact_mod_cast lt_of_lt_of_le (by positivity) card_accSet_ge)
    (by positivity), one_mul, one_mul]
  exact_mod_cast card_accSet_ge_114

/-- **`Pr[GrindBad] ≤ 2^{−2¹⁵} + 2⁻¹¹⁴`**, for faest-arch-opt's tables. -/
theorem grindBad_num_114 :
    pr Grind (GrindBad CrtGen.tables) ≤ (1 / 2) ^ (2 ^ 15) + 1 / 2 ^ 114 := by
  have h1 : pr Grind (GrindBad CrtGen.tables) ≤
      pr Grind (fun g => firstHit g = none) + pr Grind HitZero :=
    (pr_mono fun _ hg => grindBad_imp hg).trans (pr_or_le _ _)
  exact h1.trans (add_le_add noHitProb_le pr_hitZero_le_114)

lemma half_pow_le_114 : ((1 : ℝ) / 2) ^ (2 ^ 15) ≤ 1 / 2 ^ 114 := by
  rw [div_pow, one_pow]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))

/-- **`Pr[GrindBad] ≤ 2⁻¹¹³`.** -/
theorem grindBad_le_113 : pr Grind (GrindBad CrtGen.tables) ≤ 1 / 2 ^ 113 := by
  refine grindBad_num_114.trans ?_
  calc ((1 : ℝ) / 2) ^ (2 ^ 15) + 1 / 2 ^ 114 ≤ 1 / 2 ^ 114 + 1 / 2 ^ 114 :=
        add_le_add half_pow_le_114 le_rfl
    _ = 1 / 2 ^ 113 := by norm_num

/-! ## The simulator -/

section SimReject

variable [HasPrg]

/-- **`pr_simulateRO_reject` with the second-moment bound: `≤ 2^{−2¹⁵} + 2⁻¹¹⁴`.** -/
theorem pr_simulateRO_reject_114 (Hs : Hashes) (st : Statement) :
    pr (SimCoins st.params) (fun c => ¬ ∃ proof Hs',
        simulateRO Hs CrtGen.tables st c = .ok (proof, Hs') ∧
        (verify Hs' CrtGen.tables st proof).accept = true) ≤
      (1 / 2) ^ (2 ^ 15) + 1 / 2 ^ 114 := by
  refine (pr_mono fun c hc => simulateRO_bad Hs st c hc).trans ((pr_or_le _ _).trans ?_)
  rw [pr_simCoins_grind (fun g => firstHit g = none), pr_simCoins_grind HitZero]
  exact add_le_add noHitProb_le pr_hitZero_le_114

/-- **`pr_simulateRO_reject`: `≤ 2⁻¹¹³`.** -/
theorem pr_simulateRO_reject_113 (Hs : Hashes) (st : Statement) :
    pr (SimCoins st.params) (fun c => ¬ ∃ proof Hs',
        simulateRO Hs CrtGen.tables st c = .ok (proof, Hs') ∧
        (verify Hs' CrtGen.tables st proof).accept = true) ≤ 1 / 2 ^ 113 := by
  refine (pr_simulateRO_reject_114 Hs st).trans ?_
  calc ((1 : ℝ) / 2) ^ (2 ^ 15) + 1 / 2 ^ 114 ≤ 1 / 2 ^ 114 + 1 / 2 ^ 114 :=
        add_le_add half_pow_le_114 le_rfl
    _ = 1 / 2 ^ 113 := by norm_num

end SimReject

/-! ## The headline bounds -/

section Headline

variable (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- **`zk_rom_ic_h23_num` with `Pr[GrindBad] ≤ 2⁻¹¹³`** (`grindBad_le_113`): the executable prover
in the ROM and ideal-cipher model is `q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ +
(q₅ + 1)·2⁻¹²⁸`-close to the programming simulator (about `2⁻¹⁰⁷·⁰` at `q₃ = q₅ = q_E = 0`). -/
theorem zk_rom_ic_h23_num113 {cs : ByteArray → ByteArray → System GF128}
    (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 E, (∀ k ∈ Q3 o G3 G2 G5 E, G3 k = G3' k) →
      (D o G3 G2 G5 E ↔ D o G3' G2 G5 E))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 E, (Q3 o G3 G2 G5 E).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' E, (∀ k ∈ Q5 o G3 G2 G5 E, G5 k = G5' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5' E))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 E, (Q5 o G3 G2 G5 E).card ≤ q5)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@Prover.prove (icPrg c.2) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins st.params × Vis2 st.params) × Cipher) (fun c =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
            c.1.2.2.1) c.1.2.2.2 c.2)| ≤
      q3 / 2 ^ 128 + 1 / 2 ^ 113 + 221 * (4607 + (qE + 4607)) / 2 ^ 128 + (q5 + 1) / 2 ^ 128 :=
  (zk_rom_ic_h23 Hb st w hlr hzk hHb hp D Q3 hQ3 hq3 Q5 hQ5 hq5 QE hQE hqE).trans
    (add_le_add (add_le_add (add_le_add le_rfl grindBad_le_113) le_rfl) le_rfl)

/-- **`zk_rom_h23_num` with `Pr[GrindBad] ≤ 2⁻¹¹³`**: `q₃·2⁻¹²⁸ + 2⁻¹¹³ + ε_bavc + (q₅ + 1)·2⁻¹²⁸`. -/
theorem zk_rom_h23_num113 [HasPrg] {cs : ByteArray → ByteArray → System GF128}
    (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) {εb : ℝ} (hH : HideHyp st.params εb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5, (Q5 o G3 G2 G5).card ≤ q5) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (Prover.prove (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1))
          c.2.1 c.1.2 c.2.2) -
      pr (SimCoins st.params × Vis2 st.params) (fun c =>
        D (simulate st.params c.1) c.2.1
          (simTab Hb CrtGen.tables st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1)
          c.2.2.2)| ≤
      q3 / 2 ^ 128 + 1 / 2 ^ 113 + εb + (q5 + 1) / 2 ^ 128 :=
  (zk_rom_h23 Hb st w hlr hzk hHb hH D Q3 hQ3 hq3 Q5 hQ5 hq5).trans
    (add_le_add (add_le_add (add_le_add le_rfl grindBad_le_113) le_rfl) le_rfl)

/-- **`zk_rom_ic_h23_num_perm` with `Pr[GrindBad] ≤ 2⁻¹¹³`** (AES as uniformly random permutations). -/
theorem zk_rom_ic_h23_num113_perm {cs : ByteArray → ByteArray → System GF128}
    (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 π, (∀ k ∈ Q3 o G3 G2 G5 π, G3 k = G3' k) →
      (D o G3 G2 G5 π ↔ D o G3' G2 G5 π))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 π, (Q3 o G3 G2 G5 π).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' π, (∀ k ∈ Q5 o G3 G2 G5 π, G5 k = G5' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5' π))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 π, (Q5 o G3 G2 G5 π).card ≤ q5)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher) (fun c =>
        D (@Prover.prove (icPrg (cf c.2)) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins st.params × Vis2 st.params) × PCipher) (fun c =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg (cf c.2)) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1)
            c.1.1.1.2.1 c.1.2.2.1) c.1.2.2.2 c.2)| ≤
      q3 / 2 ^ 128 + 1 / 2 ^ 113 +
        (221 * (4607 + (qE + 4607)) / ((2 ^ 128 - (nHi st.params + 1) : ℕ) : ℝ) +
          switchEps st.params) + (q5 + 1) / 2 ^ 128 :=
  (zk_rom_ic_h23_perm Hb st w hlr hzk hHb hp D Q3 hQ3 hq3 Q5 hQ5 hq5 QE hQE hqE).trans
    (add_le_add (add_le_add (add_le_add le_rfl grindBad_le_113) le_rfl) le_rfl)

end Headline

section TwoPhase

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (K : Tab5F → Cipher → Cont2)

/-- **`zk2_rom_ic_h23_num` with `Pr[GrindBad] ≤ 2⁻¹¹³`** (the two-phase prover). -/
theorem zk2_rom_ic_h23_num113 (hh : ∀ G5 E, Hyp2 st r (K G5 E)) (hHb : HashesWF Hb)
    (hp : SmallParams st.params)
    (QK5 : Tab5F → Cipher → Finset (Bytes 37))
    (hQK5 : ∀ G5 G5' E, (∀ key ∈ QK5 G5 E, G5 key = G5' key) → K G5 E = K G5' E)
    {qk5 : ℕ} (hqk5 : ∀ G5 E, (QK5 G5 E).card ≤ qk5)
    (QKE : Tab5F → Cipher → Finset Blk)
    (hQKE : ∀ G5 E E', (∀ key ∈ QKE G5 E, E key = E' key) → K G5 E = K G5 E')
    {qkE : ℕ} (hqkE : ∀ G5 E, (QKE G5 E).card ≤ qkE)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (Q3 : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 E, (∀ k ∈ Q3 o G3 G2 G5 E, G3 k = G3' k) →
      (D o G3 G2 G5 E ↔ D o G3' G2 G5 E))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 E, (Q3 o G3 G2 G5 E).card ≤ q3)
    (Q5 : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' E, (∀ k ∈ Q5 o G3 G2 G5 E, G5 k = G5' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5' E))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 E, (Q5 o G3 G2 G5 E).card ≤ q5)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@realRun2 (icPrg c.2) (recH Hb (st1 st) r c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st r
          (K c.1.2.2 c.2) (ba c.1.1.1)) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins2 st.params × Vis2 st.params) × Cipher) (fun c =>
        D (@simRun2 (icPrg c.2) Hb st r.size (K c.1.2.2.2 c.2) c.1.1) c.1.2.1
          (@simTab2 (icPrg c.2) Hb CrtGen.tables st (K c.1.2.2.2 c.2) c.1.2.2.2
            (@simRun2 (icPrg c.2) Hb st r.size (K c.1.2.2.2 c.2) c.1.1) c.1.1.1.1.2.1 c.1.2.2.1)
          c.1.2.2.2 c.2)| ≤
      q3 / 2 ^ 128 + 1 / 2 ^ 113 + 221 * (4607 + ((qE + qkE : ℕ) + 4607)) / 2 ^ 128 +
        ((q5 + qk5 : ℕ) + 1) / 2 ^ 128 :=
  (zk2_rom_ic_h23 Hb st r K hh hHb hp QK5 hQK5 hqk5 QKE hQKE hqkE D Q3 hQ3 hq3 Q5 hQ5 hq5 QE hQE
    hqE).trans (add_le_add (add_le_add (add_le_add le_rfl grindBad_le_113) le_rfl) le_rfl)

end TwoPhase

end VoleMole.ZK.Sim
