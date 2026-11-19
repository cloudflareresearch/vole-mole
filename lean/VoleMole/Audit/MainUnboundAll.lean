import VoleMole.Audit.MainUnbound
import VoleMole.Privacy.MoussakaUnboundMainAll

/-!
# Audit of Theorem U5 on `main` with all tables shared (`Privacy/MoussakaUnbound*MainAll.lean`)

* **`anonymityU_main_sharedAll_two` (U5(a)) applies**: for the adversary `uH` (two queries
  `uq S0`, `uq₁ S0` answered by different Clients in both worlds, a constant guess, no table reads)
  the reads are consistent at budgets `0`, the queries satisfy `TwoClientsU`, and every PRF
  reduction has advantage `0`, so the hypotheses hold with `εprf = 0`. The (PU) advantages are
  explicit probabilities, and the predictors output at most `4·(0 + 1249)` candidates.
* **`anonymityNC_main_U_sharedAll_two` (U5(b)) applies with a non-trivial signer and sets that
  contain both issuers**: the Moderator `uNCH` has the two keys `pkL c` of `Audit/Liveness.lean`
  (trapdoor signers `skI (digL c)`), queries the set `SL` of both (`uNCH_contains`), first with
  `i = false`, then with `i = true` (`TwoClients`); the reads and the PRF hypothesis (`εprf = 0`)
  hold.

No `sorry`, no `axiom`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.MainUnboundAll

open VoleMole.Spec VoleMole.Privacy VoleMole.Privacy.MoussakaUnbound VoleMole.ZK.Sim
open VoleMole.Privacy.MainChain VoleMole.Privacy.PU VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Audit.MainUnbound

/-- The second query: the other token, same swap flag, set and context. -/
def uq₁ (S : Spec.Moussaka.AnchorSet) : Query := ⟨true, true, S, fun _ => 0, []⟩

/-- A function that reads nothing reads the shared tables within any budget. -/
theorem rdUH_const {X : Sort*} (x : X) (R : USh → Tab2G pIu → H3T → Finset (ZK.Sim.Bytes 37)) :
    RdUH (fun _ _ _ => x) R 0 0 :=
  ⟨fun _ _ _ _ _ => rfl, ⟨fun _ _ _ => ∅, fun _ _ _ => by simp, fun _ _ _ _ _ => rfl⟩,
    ⟨fun _ _ _ => ∅, fun _ _ _ => by simp, fun _ _ _ _ _ => rfl⟩⟩

/-! ## U5(a) -/

/-- The colluding adversary with all tables shared: two queries answered by different Clients, a
constant guess and no table reads. -/
def uH : AdversaryUH :=
  ⟨fun _ => 0, fun _ => Audit.k0, fun _ _ _ => 0, fun _ _ j => ![Audit.uq Audit.S0, uq₁ Audit.S0] j,
    fun _ _ _ _ _ _ => True, fun _ _ _ _ _ _ => ∅⟩

theorem uH_cons : uH.ConsH 0 0 :=
  ⟨fun _ _ _ => rdUH_const True _, fun _ _ _ => rdUH_const ∅ _⟩

theorem uH_two : TwoClientsU uH := by
  intro b _ _
  show who b (Audit.uq Audit.S0) ≠ who b (uq₁ Audit.S0)
  cases b <;> simp [who, Audit.uq, uq₁]

/-- `anonymityU_main_sharedAll_two` for `uH`: every hypothesis holds, with `εprf = 0`. -/
example :=
  anonymityU_main_sharedAll_two uH uH_two uH_cons (εprf := 0)
    (fun _ _ => (prfAdv_true _).le)

/-- The predictors of `uH` output at most `4·1249` candidates. -/
example (b : Bool) (t₀ t₁ k₀ k₁ : Spec.Bytes) (a : AuxH) (T : H3T) :
    (candP uH b t₀ t₁ k₀ k₁ a T).card ≤ 4 * (0 + 1249) :=
  card_candP_le uH (q5 := 0) (fun _ _ _ _ _ _ => le_rfl) b t₀ t₁ k₀ k₁ a T

/-! ## U5(b) -/

section NC

open VoleMole.Audit.Live VoleMole.Spec.Moussaka

/-- A non-colluding Moderator on `main` with all tables shared: the keys `pkL`, both queries in
`SL` (first Client `false`'s token, then Client `true`'s), a constant guess and no table reads. -/
noncomputable def uNCH : AdversaryUNCH :=
  ⟨fun _ => 0, pkL, fun H => match H with
    | [] => Audit.uq SL
    | _ :: _ => uq₁ SL, fun _ _ _ _ => True, fun _ _ _ _ => ∅⟩

theorem uNCH_cons : uNCH.ConsH 0 0 :=
  ⟨fun _ => rdUH_const True _, fun _ => rdUH_const ∅ _⟩

/-- **Every query's set contains both issuers.** -/
theorem uNCH_contains : Contains uNCH.unc.nc := fun H c => by
  refine ⟨pkL c, ?_, rfl⟩
  cases H <;> cases c <;> simp [AdversaryUNCH.unc, AdversaryUNC.nc, uNCH, Audit.uq, uq₁, SL]

theorem uNCH_two : TwoClients uNCH := by
  intro b _
  show who b (uq₁ SL) ≠ who b (Audit.uq SL)
  cases b <;> simp [who, Audit.uq, uq₁]

/-- `anonymityNC_main_U_sharedAll_two` for `uNCH`: every hypothesis holds, with `εprf = 0`. -/
example (PI : NIZK MoussakaUnbound.IssueInstance) :=
  anonymityNC_main_U_sharedAll_two uNCH PI (fun c => skI (digL c)) (fun _ => skI_correct _)
    uNCH_contains uNCH_two uNCH_cons (q5 := 0) (fun _ _ _ _ => le_rfl) (εprf := 0)
    (fun _ _ => prfAdvNC_true.le)

end NC

end VoleMole.Audit.MainUnboundAll
