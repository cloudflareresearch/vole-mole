import VoleMole.ZK.ReadsRO
import VoleMole.ZK.HopsICExp

/-!
# `zk_ro` with expected charges at the proof's points

`zk_ro` (`ZK/ReadsRO.lean`) is the one-proof theorem the theft and privacy games use: the real
prover `realRO` (a uniform `ρ`, the proof's `H₃` slice `G3`, the shared tables `s = (G2, G5, E)`)
against the simulator `simulate` with its programming `progRO`, for a distinguisher with
worst-case budgets (`Budget`). Here it is restated from `zk_rom_ic_h23_exp`
(`ZK/HopsICExp.lean`): a distinguisher read by a consistent point reader `R` (`PtReads`) has
advantage at most

    (εZK + E_real[chZK]) / (1 − βZK),

`εZK = Pr[GrindBad] + 221·9214/d_E + 2⁻¹²⁸` (constants), `βZK = 221·q_E/d_E + q₅·2⁻¹²⁸` (the
worst-case budgets, only here), `d_E = 2¹²⁸ − 221·(q_E + 4607)`, and `chZK` the expected charge:
`2⁻¹²⁸`-weighted reads of the proof's `H₃` slice, of `H₅` at gate inputs of the proof's `iv`, and
`221`-weighted cipher keys read at CTR blocks of the proof's `iv` (`zk_ro_exp`). This is the form
of `Theft.hyb_hop_exp`'s hypothesis for one hop: a constant plus the expectation, in the world
where the proof is real, of a function of the view.

* `toVw`: the view `(o, G3, s)` of `zk_ro`'s distinguisher as a `VwIC`.
* `chZK`, `εZK`, `βZK`: the charge, the constant and the budget factor.
* **`zk_ro_exp`**.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

variable {p : Params}

/-- `zk_ro`'s view `(o, G3, s)` as a `VwIC`. -/
def toVw (o : Except String ByteArray) (G3 : Tab3) (s : Sh p) : VwIC p := (o, G3, s.1, s.2.1, s.2.2)

/-- The worst-case cipher denominator `2¹²⁸ − 221·(q_E + 4607)`. -/
noncomputable def dEZK (qE : ℕ) : ℝ := 2 ^ 128 - 221 * ((qE + 4607 : ℕ) : ℝ)

/-- **The expected-charge integrand**: the `H₃` keys read over `2¹²⁸ − q₃`, `221` times the cipher
keys read at CTR blocks of the output's `iv` over `d_E`, the `H₅` keys read at its gate inputs
over `2¹²⁸`. -/
noncomputable def chZK (R : PtReads p) (Hb : Hashes) (st : Statement) (q3 qE : ℕ) (v : VwIC p) : ℝ :=
  (ch3 R v : ℝ) / (2 ^ 128 - q3) + 221 * (chE R Hb st v : ℝ) / dEZK qE +
    (ch5 R Hb CrtGen.tables st v : ℝ) / 2 ^ 128

/-- **The constant part of one proof's error.** -/
noncomputable def εZK (qE : ℕ) : ℝ :=
  pr Grind (GrindBad CrtGen.tables) + 221 * 9214 / dEZK qE + 1 / 2 ^ 128

/-- **The budget factor** (worst-case budgets enter only through `1 − βZK`). -/
noncomputable def βZK (q5 qE : ℕ) : ℝ := 221 / dEZK qE * qE + 1 / 2 ^ 128 * q5

variable (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- **`zk_ro` with expected charges at the proof's points.** For a consistent point reader `R`
with worst-case budgets `q₃`, `q₅`, `q_E` (`221·(q_E + 4607) < 2¹²⁸`, `βZK < 1`) and a
distinguisher `D` read by `R`:

    |Pr_real[D] − Pr_sim[D]| ≤ (εZK + E_real[chZK]) / (1 − βZK),

the expectation over the real prover's coins and the tables. -/
theorem zk_ro_exp {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (R : PtReads st.params) (hc : R.Cons) {q3 q5 qE : ℕ} (hb : R.Bnd q3 q5 qE)
    (h3 : (q3 : ℝ) < 2 ^ 128) (hE : 221 * ((qE + 4607 : ℕ) : ℝ) < 2 ^ 128) (hβ : βZK q5 qE < 1)
    (D : Except String ByteArray → Tab3 → Sh st.params → Prop)
    (hD : R.Reads (fun v => D v.1 v.2.1 (v.2.2.1, v.2.2.2.1, v.2.2.2.2))) :
    |pr ((Bytes 16 × Tab3) × Sh st.params) (fun a =>
        D (realRO st.params Hb st w a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((SimCoins st.params × Tab3) × Sh st.params) (fun a =>
        D (simulate st.params a.1.1) a.1.2 (progRO st.params Hb st a.1.1 a.2))| ≤
      (εZK qE + exP ((Bytes 16 × Tab3) × Sh st.params) (fun a =>
        chZK R Hb st q3 qE (toVw (realRO st.params Hb st w a.1.1 a.1.2 a.2) a.1.2 a.2))) /
        (1 - βZK q5 qE) := by
  have hβ' : 221 / (2 ^ 128 - 221 * ((qE + 4607 : ℕ) : ℝ)) * qE + 1 / 2 ^ 128 * q5 < 1 := hβ
  have key := zk_rom_ic_h23_exp Hb st w hlr hzk hHb hp R hc hb h3 hE hβ' _ hD
  have hv : ∀ c : Co0 st.params, toVw (realRO st.params Hb st w c.1.1.1 c.1.2.1 (c.1.1.2, c.1.2.2, c.2))
      c.1.2.1 (c.1.1.2, c.1.2.2, c.2) = view0 Hb st w c := fun c => rfl
  let e1 : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher ≃
      (Bytes 16 × Tab3) × Sh st.params :=
    { toFun := fun c => ((c.1.1.1, c.1.2.1), (c.1.1.2, c.1.2.2, c.2))
      invFun := fun c => (((c.1.1, c.2.1), (c.1.2, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (SimCoins st.params × Vis2 st.params) × Cipher ≃
      (SimCoins st.params × Tab3) × Sh st.params :=
    { toFun := fun c => ((c.1.1, c.1.2.1), (c.1.2.2.1, c.1.2.2.2, c.2))
      invFun := fun c => ((c.1.1, (c.1.2, c.2.1, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have eX : exP ((Bytes 16 × Tab3) × Sh st.params) (fun a =>
      chZK R Hb st q3 qE (toVw (realRO st.params Hb st w a.1.1 a.1.2 a.2) a.1.2 a.2)) =
      exP (Co0 st.params) (fun c => (ch3 R (view0 Hb st w c) : ℝ) / (2 ^ 128 - q3) +
          221 * (chE R Hb st (view0 Hb st w c) : ℝ) / (2 ^ 128 - 221 * ((qE + 4607 : ℕ) : ℝ)) +
          (ch5 R Hb CrtGen.tables st (view0 Hb st w c) : ℝ) / 2 ^ 128) := by
    rw [← exP_equiv e1]
    refine congrArg (exP _) (funext fun c => ?_)
    simp only [e1, Equiv.coe_fn_mk]
    rw [hv c]
    simp only [chZK, dEZK]
  rw [eX, show εZK qE = pr Grind (GrindBad CrtGen.tables) + 221 * 9214 /
      (2 ^ 128 - 221 * ((qE + 4607 : ℕ) : ℝ)) + 1 / 2 ^ 128 from rfl,
    show βZK q5 qE = 221 / (2 ^ 128 - 221 * ((qE + 4607 : ℕ) : ℝ)) * qE + 1 / 2 ^ 128 * q5 from rfl,
    sub_add_eq_sub_sub]
  have hl : pr ((Bytes 16 × Tab3) × Sh st.params) (fun a =>
      D (realRO st.params Hb st w a.1.1 a.1.2 a.2) a.1.2 a.2) =
      pr (Co0 st.params) (fun c => D (view0 Hb st w c).1 (view0 Hb st w c).2.1
        ((view0 Hb st w c).2.2.1, (view0 Hb st w c).2.2.2.1, (view0 Hb st w c).2.2.2.2)) :=
    (pr_equiv e1 _).symm
  have hr : pr ((SimCoins st.params × Tab3) × Sh st.params) (fun a =>
      D (simulate st.params a.1.1) a.1.2 (progRO st.params Hb st a.1.1 a.2)) =
      pr (Co7 st.params) (fun c => D (view7 Hb st CrtGen.tables c).1 (view7 Hb st CrtGen.tables c).2.1
        ((view7 Hb st CrtGen.tables c).2.2.1, (view7 Hb st CrtGen.tables c).2.2.2.1,
          (view7 Hb st CrtGen.tables c).2.2.2.2)) := by
    have hv7 : ∀ c : Co7 st.params, toVw (simulate st.params c.1.1) c.1.2.1
        (progRO st.params Hb st c.1.1 (c.1.2.2.1, c.1.2.2.2, c.2)) = view7 Hb st CrtGen.tables c :=
      fun c => rfl
    rw [← pr_equiv e2]
    refine pr_congr fun c => ?_
    rw [← hv7 c]
    simp only [e2, Equiv.coe_fn_mk, toVw]
  rw [hl, hr]
  exact key

end VoleMole.ZK.Sim
