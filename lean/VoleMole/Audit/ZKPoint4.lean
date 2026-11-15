import VoleMole.Theft.JointExt
import VoleMole.Theft.JointSumA

/-!
# Audit of the theft games' pieces at points (zk-point4)

* **The programming's confinement holds for Ratatouille's Lean simulators** (issuance and spend,
  `SHAKE` base record): `rata_progI_conf`, `rata_progS_conf` (`progPtRd_conf`), so
  `real_sim_leN_lean`'s hypothesis `hRpg` is met (`lProgRd_conf`; `real_sim_leN_lean_pg`,
  `real_sim_leN_lean_full` discharge both honest-reader hypotheses).
* **Gate inputs do not depend on the parameters** (`gate5_params`): a spend proof's gate inputs
  (`pS`) are gate inputs at the issuance parameters `pI` (`rata_gate5_pS_pI`), so the two systems
  are charged alike (`chPt_params`).
* **Inactive slots are charged nothing** (`nZKA_inactive`): the correction of
  `real_sim_leN_leanA` for slots with no proof.
* **The game-reader pieces are non-vacuous**: the verifier's reader is within `(0, 312, 4607)`
  (`verPtRd_bnd`); a run of a computation with no query has the empty reads and is consistent
  (`runGRd_pure`).

The headline theorems' axioms are printed below: `propext`, `Classical.choice`, `Quot.sound` only.
No `sorry`, no `axiom`.
-/

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.ZKPoint4

open VoleMole.Privacy VoleMole.ZK VoleMole.ZK.Sim VoleMole.ZK.IC VoleMole.Verifier
  VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.Theft VoleMole.ROM VoleMole.ROM.IC
  VoleMole.ROM.Reads

section Rata

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

/-- **The issuance simulator's programming is confined to its `iv`.** -/
theorem rata_progI_conf (x : IssueInstance) (c : SimCoins pI) :
    Conf (progPtRd Hashes.shake (stI x) c) (fun _ => ivV Hashes.shake (stI x) (simulate pI c))
      312 4607 :=
  progPtRd_conf (p := pI) (st := stI x) hashesWF_shake rfl c

/-- **The spend simulator's programming is confined to its `iv`.** -/
theorem rata_progS_conf (x : SpendInstance) (c : SimCoins pS) :
    Conf (progPtRd Hashes.shake (stS x) c) (fun _ => ivV Hashes.shake (stS x) (simulate pS c))
      312 4607 :=
  progPtRd_conf (p := pS) (st := stS x) hashesWF_shake rfl c

/-- **A spend proof's gate inputs are gate inputs at the issuance parameters.** -/
theorem rata_gate5_pS_pI {T : CrtTables} {iv : ByteArray} {k : Sim.Bytes 37} (h : Gate5 pS T iv k) :
    Gate5 pI T iv k := gate5_params h

end Rata

/-- **An inactive slot is charged nothing.** -/
theorem nZKA_inactive {X : Type} {I O Ω : Type*} {p : Params} {N : ℕ} (act : I → Prop)
    [DecidablePred act] (ivO : X → I → O → Option ByteArray) (xOf : Ω → List O → I)
    (R : GRd Ω O p X N) (h5 hE i : ℕ) (k : Fin 3)
    (v : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X) (h : ¬ act (xOf v.1 (v.2.1.take i))) :
    nZKA act ivO xOf R h5 hE i k v = 0 := by
  unfold nZKA; simp [h]

/-- **The verifier's reader is within `(0, 312, 4607)`.** -/
theorem ver_bnd {p : Params} (Hb : Hashes) (st : Statement) (proof : ByteArray) :
    (verPtRd (p := p) Hb st proof).Bnd 0 312 4607 := verPtRd_bnd st proof

/-- **A run with no query reads nothing, and its reader is consistent.** -/
theorem runGRd_pure {Ω O : Type*} {p : Params} {L M N : ℕ} {α : Type} (a : Ω → List O → α) :
    (runGRd (p := p) (L := L) (M := M) (N := N) (fun ω l => (pure (a ω l) : OracleComp specIC α))).Cons ∧
      ∀ ω l gs t, (runGRd (p := p) (L := L) (M := M) (N := N)
        (fun ω l => (pure (a ω l) : OracleComp specIC α))).QE ω l gs t = ∅ :=
  ⟨runGRd_cons _, fun _ _ _ _ => rfl⟩

end VoleMole.Audit.ZKPoint4

#print axioms VoleMole.Theft.progPtRd_conf
#print axioms VoleMole.Theft.lProgRd_conf
#print axioms VoleMole.Theft.real_sim_leN_lean_pg
#print axioms VoleMole.Theft.real_sim_leN_lean_full
#print axioms VoleMole.Theft.real_sim_leN_leanG
#print axioms VoleMole.Theft.real_sim_leN_leanA
#print axioms VoleMole.Theft.ZKExp.osum
#print axioms VoleMole.Theft.lean_zkExpD
#print axioms VoleMole.Theft.gate5_params
#print axioms VoleMole.Theft.chPt_params
#print axioms VoleMole.Theft.exU_sum_nZKA_le
#print axioms VoleMole.Theft.verPt_cons
#print axioms VoleMole.Theft.verPtRd_bnd
#print axioms VoleMole.Theft.runT_agree
#print axioms VoleMole.Theft.runGRd_cons
#print axioms VoleMole.Theft.runGRd_reads
#print axioms VoleMole.Theft.runGRd_bnd
#print axioms VoleMole.Theft.GRd.seq_cons
#print axioms VoleMole.Theft.GRd.seq_reads
#print axioms VoleMole.Theft.GRd.ofTRd_cons
#print axioms VoleMole.Theft.Ratatouille.eRom_congrP
#print axioms VoleMole.Theft.Ratatouille.romPts_congr
#print axioms VoleMole.Audit.ZKPoint4.rata_progI_conf
#print axioms VoleMole.Audit.ZKPoint4.rata_progS_conf
