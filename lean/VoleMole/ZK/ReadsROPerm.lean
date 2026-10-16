import VoleMole.ZK.ReadsRO
import VoleMole.ZK.HopsICPerm

/-!
# Zero knowledge with the tables visible and AES as random permutations, as `ZeroKnowledgeRO`

`zk_ro` and `lean_zeroKnowledgeRO` (`ZK/ReadsRO.lean`) state `zk_rom_ic_h23_num` with the shared
tables `Sh p = Tab2G p × Tab5F × Cipher` (the cipher a table of uniform functions). Here the same
with the cipher a table of uniform **permutations**: `ShPm p = Tab2G p × Tab5F × PCipher`, read by
the distinguisher at most at `q_E` keys (whole permutations: forward and inverse queries;
`RdEPm`), the prover and the simulator's programming running with the permutations' rows
(`realROPm`, `progROPm`: `realRO`, `progRO` at the rows `cf π`). The error is
`εROPm p q₃ q₅ q_E = q₃·2⁻¹²⁸ + 2⁻¹¹⁰ + 221·(4607 + q_E + 4607)/(2¹²⁸ − (nHi + 1)) + switchEps p +
(q₅ + 1)·2⁻¹²⁸` (`zk_rom_ic_h23_num_perm`).

The shared tables, their reads and the prover are those of `ZK/ReadsRO.lean` at the row type
`Equiv.Perm Blk` (`CipherRow.perm`): `ShPm p = ShG (Equiv.Perm Blk) p`, and `Rd5Pm`, `RdEPm`,
`BudgetPm`, `realROPm`, `progROPm` are `Rd5`, `RdE`, `Budget`, `realRO`, `progRO` there.
**`ZKRow.perm`** packages `zk_ro_perm`; the privacy games, stated for any row type with `ZKRow`,
instantiate with it (`Privacy/PermRO.lean`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

/-- **Permutation rows** (AES as uniformly random permutations, `IC.cf`). -/
instance CipherRow.perm : CipherRow (Equiv.Perm Blk) := ⟨fun σ => ⇑σ⟩

lemma rowFn_perm (π : PCipher) : rowFn π = cf π := rfl

/-- **The shared tables with the cipher as random permutations.** -/
abbrev ShPm (p : Params) := ShG (Equiv.Perm Blk) p

/-- The shared tables with the permutations' rows as the cipher. -/
def toSh {p : Params} (s : ShPm p) : Sh p := (s.1, s.2.1, cf s.2.2)

section Reads

variable {p : Params} {X : Sort*}

/-- `f` reads the `H₅` table at most at `q` keys (`Rd5` with permutation rows). -/
abbrev Rd5Pm (f : ShPm p → X) (q : ℕ) : Prop := Rd5 f q

/-- `f` reads the permutation table at most at `q` keys (whole permutations; `RdE` with
permutation rows). -/
abbrev RdEPm (f : ShPm p → X) (q : ℕ) : Prop := RdE f q

/-- **The budget of a distinguisher** with the permutation table (`Budget` with permutation
rows): it reads the `H₃` slice at `q3`, `H₅` at `q5` and the permutation table at `qE` keys, and
`H₂³` freely. -/
abbrev BudgetPm {O : Type*} (p : Params) (q3 q5 qE : ℕ) (D : O → Tab3 → ShPm p → Prop) : Prop :=
  Budget p q3 q5 qE D

end Reads

variable (p : Params) (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- The executable prover with the CTR PRG of the permutations' rows (`realRO` with permutation
rows). -/
noncomputable abbrev realROPm (ρ : Bytes 16) (G3 : Tab3) (s : ShPm p) : Except String ByteArray :=
  realRO p Hb st w ρ G3 s

lemma realROPm_eq (ρ : Bytes 16) (G3 : Tab3) (s : ShPm p) :
    realROPm p Hb st w ρ G3 s = realRO p Hb st w ρ G3 (toSh s) := rfl

/-- The simulator's programming of `H₂³`, recomputing the prefix with the permutations' rows
(`progRO` with permutation rows). -/
noncomputable abbrev progROPm (c : SimCoins p) (s : ShPm p) : ShPm p :=
  progRO p Hb st c s

lemma progROPm_eq (c : SimCoins p) (s : ShPm p) :
    progROPm p Hb st c s = ((progRO p Hb st c (toSh s)).1, s.2) := rfl

/-- **The error of `zk_rom_ic_h23_num_perm`** at budgets `q₃`, `q₅`, `q_E`. -/
noncomputable def εROPm (q3 q5 qE : ℕ) : ℝ :=
  q3 / 2 ^ 128 + 1 / 2 ^ 110 +
    (221 * (4607 + (qE + 4607)) / ((2 ^ 128 - (nHi p + 1) : ℕ) : ℝ) + switchEps p) +
      (q5 + 1) / 2 ^ 128

lemma εROPm_mono {q3 q5 qE q3' q5' qE' : ℕ} (h3 : q3 ≤ q3') (h5 : q5 ≤ q5') (hE : qE ≤ qE') :
    εROPm p q3 q5 qE ≤ εROPm p q3' q5' qE' := by
  unfold εROPm
  have h3' : (q3 : ℝ) ≤ q3' := by exact_mod_cast h3
  have h5' : (q5 : ℝ) ≤ q5' := by exact_mod_cast h5
  have hE' : (qE : ℝ) ≤ qE' := by exact_mod_cast hE
  gcongr

lemma εROPm_nonneg (q3 q5 qE : ℕ) : 0 ≤ εROPm p q3 q5 qE := by
  unfold εROPm switchEps; positivity

/-- **Zero knowledge in the ROM with AES as random permutations, with the tables visible**
(`zk_rom_ic_h23_num_perm` for a distinguisher with a `BudgetPm`). -/
theorem zk_ro_perm {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    {q3 q5 qE : ℕ} (D : Except String ByteArray → Tab3 → ShPm st.params → Prop)
    (hD : BudgetPm st.params q3 q5 qE D) :
    |pr ((Bytes 16 × Tab3) × ShPm st.params) (fun a =>
        D (realROPm st.params Hb st w a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((SimCoins st.params × Tab3) × ShPm st.params) (fun a =>
        D (simulate st.params a.1.1) a.1.2 (progROPm st.params Hb st a.1.1 a.2))| ≤
      εROPm st.params q3 q5 qE := by
  choose Q3 hQ3c hQ3 using hD.h3
  choose Q5 hQ5c hQ5 using hD.h5
  choose QE hQEc hQE using hD.hE
  have key := zk_rom_ic_h23_num_perm Hb st w hlr hzk hHb hp
    (fun o G3 G2 G5 π => D o G3 (G2, G5, π))
    (fun o G3 G2 G5 π => Q3 o (G2, G5, π) G3)
    (fun o G3 G3' G2 G5 π hk => Iff.of_eq (hQ3 o (G2, G5, π) G3 G3' hk).symm)
    (fun o G3 G2 G5 π => hQ3c o (G2, G5, π) G3)
    (fun o G3 G2 G5 π => Q5 o G3 (G2, G5, π))
    (fun o G3 G2 G5 G5' π hk => Iff.of_eq (hQ5 o G3 (G2, G5, π) G5' hk).symm)
    (fun o G3 G2 G5 π => hQ5c o G3 (G2, G5, π))
    (fun o G3 G2 G5 π => QE o G3 (G2, G5, π))
    (fun o G3 G2 G5 π π' hk => Iff.of_eq (hQE o G3 (G2, G5, π) π' hk).symm)
    (fun o G3 G2 G5 π => hQEc o G3 (G2, G5, π))
  let e1 : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher ≃
      (Bytes 16 × Tab3) × ShPm st.params :=
    { toFun := fun c => ((c.1.1.1, c.1.2.1), (c.1.1.2, c.1.2.2, c.2))
      invFun := fun c => (((c.1.1, c.2.1), (c.1.2, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (SimCoins st.params × Vis2 st.params) × PCipher ≃
      (SimCoins st.params × Tab3) × ShPm st.params :=
    { toFun := fun c => ((c.1.1, c.1.2.1), (c.1.2.2.1, c.1.2.2.2, c.2))
      invFun := fun c => ((c.1.1, (c.1.2, c.2.1, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e1, ← pr_equiv e2]
  exact key

/-- **The Lean prover is `ZeroKnowledgeRO` with AES as random permutations**, for every relation
whose statements have dedicated label rows (and parameters `p`) and whose witnesses satisfy the
deterministic hypotheses, against the distinguishers with budgets `(q₃, q₅, q_E)` on the tables
with the permutation table, with error `εROPm p q₃ q₅ q_E`. -/
theorem lean_zeroKnowledgeRO_perm {I W : Type*} (stOf : I → Statement)
    (hp : ∀ x, (stOf x).params = p) (hlr : p.labelRows = true) (enc : I → W → ByteArray)
    (R : I → W → Prop) (cs : I → ByteArray → ByteArray → System GF128)
    (h : ∀ x w, R x w → ZKHyp CrtGen.tables (stOf x) (enc x w) (cs x)) (hHb : HashesWF Hb)
    (hsp : SmallParams p) (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO R (fun x w ρ G3 s => realROPm p Hb (stOf x) (enc x w) ρ G3 s)
      (fun _ c => simulate p c) (fun x c s => progROPm p Hb (stOf x) c s) (BudgetPm p q3 q5 qE)
      (εROPm p q3 q5 qE) := by
  intro x w hxw D hD
  beta_reduce
  have hz := h x w hxw
  have hpx := hp x
  generalize stOf x = st at hz hpx ⊢
  subst hpx
  exact zk_ro_perm Hb st (enc x w) hlr hz hHb hsp D hD

/-- **Permutation rows have `ZKRow`**: `zk_ro_perm`, error `εROPm`. The privacy games, stated for
every row type with `ZKRow`, hold with AES as uniformly random permutations. -/
noncomputable instance ZKRow.perm : ZKRow (Equiv.Perm Blk) where
  εz := εROPm
  εz_mono p _ _ _ _ _ _ h3 h5 hE := εROPm_mono p h3 h5 hE
  εz_nonneg := εROPm_nonneg
  zk Hb st w _ hlr hzk hHb hp _ _ _ D hD := zk_ro_perm Hb st w hlr hzk hHb hp D hD

end VoleMole.ZK.Sim
