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

The privacy games (`Privacy/MoussakaRO.lean`, `Privacy/RatatouilleRO.lean`, the adaptive and
two-phase versions) are built on `Sh` and its read predicates; they are not restated here.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

/-- **The shared tables with the cipher as random permutations.** -/
abbrev ShPm (p : Params) := Tab2G p × Tab5F × PCipher

/-- The shared tables with the permutations' rows as the cipher. -/
def toSh {p : Params} (s : ShPm p) : Sh p := (s.1, s.2.1, cf s.2.2)

section Reads

variable {p : Params} {X : Sort*}

/-- `f` reads the `H₅` table at most at `q` keys. -/
def Rd5Pm (f : ShPm p → X) (q : ℕ) : Prop :=
  ∃ Q : ShPm p → Finset (Bytes 37), (∀ s, (Q s).card ≤ q) ∧
    ∀ s (G5 : Tab5F), (∀ k ∈ Q s, s.2.1 k = G5 k) → f (s.1, G5, s.2.2) = f s

/-- `f` reads the permutation table at most at `q` keys (whole permutations). -/
def RdEPm (f : ShPm p → X) (q : ℕ) : Prop :=
  ∃ Q : ShPm p → Finset Blk, (∀ s, (Q s).card ≤ q) ∧
    ∀ s (π : PCipher), (∀ k ∈ Q s, s.2.2 k = π k) → f (s.1, s.2.1, π) = f s

/-- **The budget of a distinguisher** with the permutation table: it reads the `H₃` slice at `q3`,
`H₅` at `q5` and the permutation table at `qE` keys, and `H₂³` freely. -/
structure BudgetPm {O : Type*} (p : Params) (q3 q5 qE : ℕ) (D : O → Tab3 → ShPm p → Prop) :
    Prop where
  h3 : ∀ o s, Rd3 (fun G3 => D o G3 s) q3
  h5 : ∀ o G3, Rd5Pm (D o G3) q5
  hE : ∀ o G3, RdEPm (D o G3) qE

end Reads

variable (p : Params) (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- The executable prover with the CTR PRG of the permutations' rows. -/
noncomputable def realROPm (ρ : Bytes 16) (G3 : Tab3) (s : ShPm p) : Except String ByteArray :=
  realRO p Hb st w ρ G3 (toSh s)

/-- The simulator's programming of `H₂³`, recomputing the prefix with the permutations' rows. -/
noncomputable def progROPm (c : SimCoins p) (s : ShPm p) : ShPm p :=
  ((progRO p Hb st c (toSh s)).1, s.2)

/-- **The error of `zk_rom_ic_h23_num_perm`** at budgets `q₃`, `q₅`, `q_E`. -/
noncomputable def εROPm (q3 q5 qE : ℕ) : ℝ :=
  q3 / 2 ^ 128 + 1 / 2 ^ 110 +
    (221 * (4607 + (qE + 4607)) / ((2 ^ 128 - (nHi p + 1) : ℕ) : ℝ) + switchEps p) +
      (q5 + 1) / 2 ^ 128

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

end VoleMole.ZK.Sim
