import VoleMole.Assumptions.UnboundLinks
import VoleMole.Audit.Nonvacuous

/-!
# Non-vacuity of unbound Moussaka Theorem U1

`ROM/MoussakaUnboundOMUF.lean`, `ROM/MoussakaUnboundOMUFSim.lean` and
`Assumptions/UnboundLinks.lean` instantiated as `Audit/Nonvacuous.lean` and
`Audit/SimExtract.lean` do for bound Moussaka: two honest Anchors with distinct 32-byte digests
(`pkU`), any signers, an OMUF-U adversary `aUU` that makes one bound and one unbound Issue query
and one redemption, the toy ideal-`Com` forger. Every hypothesis is discharged, the modelling
hypothesis `hmodel` of the OMPR corollaries included (for the toy forger, which wins the ideal game
with probability one). The request lengths the honest checks expect are the executable verifier's
proof sizes (`upfLenI_eq`, `upfLenR_eq`), so honest requests are not refused as malformed.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Audit.UnboundOMUF

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Verifier VoleMole.Audit
open VoleMole.ROM.IC.OMUF VoleMole.ROM.IC.OMUFU VoleMole.Assumptions.UOV
  VoleMole.Assumptions.UOV.Links

/-- An OMUF-U adversary: a bound Issue query, then an unbound one (both malformed), and one
redemption (empty Anchor Set). -/
def aUU : OMUFU.Adversary 2 1 where
  σ := Bool
  init := pure false
  query b := pure (true, if b then .inr ⟨0, ByteArray.empty, ByteArray.empty⟩
    else .inl ⟨0, ByteArray.empty, ByteArray.empty⟩)
  absorb b _ := b
  final _ := pure fun _ => ⟨[], ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩

theorem aUU_budget : aUU.Budget 0 0 0 := by
  refine ⟨trivial, trivial, trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial,
    fun _ => trivial, fun _ => trivial, fun _ => trivial⟩

/-- Theorem U1 with the single-proof extraction terms (`omufU_le_num`): its hypotheses hold. -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omufU_le_num lr pkU sk 2 aUU_budget pkU_digest pkU_inj

/-- Theorem U1 with simultaneous extraction (`omufU_le_num_sim`). -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omufU_le_num_sim (lr := lr) (sk := sk) (qI := 2) aUU_budget pkU_digest pkU_inj

/-- Theorem U1 with `Adv^{ct-uf-open}` over `Com ∪ UCom` (`omufU_le_num_open`). -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omufU_le_num_open lr pkU sk 2 aUU_budget pkU_digest pkU_inj

/-- The same with simultaneous extraction (`omufU_le_num_open_sim`). -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omufU_le_num_open_sim lr pkU sk 2 aUU_budget pkU_digest pkU_inj

/-- The toy forger meets the modelling hypothesis against any advantage. -/
theorem toy_hmodel (a : ℝ≥0∞) (ha : a ≤ 1) :
    a ≤ advCTUFIdealAt (fun k => toyTrap.IsPre ((fun _ : Fin 2 => ((), ())) k).1)
      (signers toyTrap.D fun k => ((fun _ : Fin 2 => ((), ())) k).2) (toyF 2) := by
  have := toyF_wins 2
  simp only [toyTrap] at this ⊢
  rw [this]
  exact ha

/-- Theorem U1 down to OMPR (`omufU_le_num_ompr`): its hypotheses, the modelling one included,
hold for the toy ideal forger. -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omufU_le_num_ompr lr pkU sk 2 toyTrap (fun _ => ((), ())) 0 0 aUU_budget pkU_digest pkU_inj
    (toyF 2) (toyF_budget 2) (toy_hmodel _ (prEvent_le_one _))

/-- Theorem U1 down to OMPR with simultaneous extraction (`omufU_le_num_ompr_sim`). -/
example (lr : Bool) (sk : Fin 2 → Spec.Signer) :=
  omufU_le_num_ompr_sim lr pkU sk 2 toyTrap (fun _ => ((), ())) 0 0 aUU_budget pkU_digest pkU_inj
    (toyF 2) (toyF_budget 2) (toy_hmodel _ (prEvent_le_one _))

/-- The honest checks' request lengths are the executable verifier's proof sizes, and on `main`
the C++ constants. -/
example (lr : Bool) :
    upfLenI lr = (Unbound.issueParams lr).proofBytes ∧
      upfLenR lr = (Unbound.redeemParams lr).proofBytes :=
  ⟨upfLenI_eq lr, upfLenR_eq lr⟩

example : upfLenI false = 6864 ∧ upfLenR false = 12423 := upfLen_main

/-- The deterministic core is not vacuous: one unbound issuance for `ctx_iss = 0` and two
accepted nullifiers in one context, each with its own extracted key, force a collision or an
unsigned commitment (here: the second commitment is unsigned). -/
example : (∃ x ∈ (Set.univ : Set (Bool × ℕ)), ∃ x' ∈ Set.univ, x ≠ x' ∧ x.2 = x'.2) ∨
    (∃ x ∈ (Set.univ : Set (Bool × ℕ)), x.2 ∉ [(0, 0)].map (·.1) ∧ x.2 ∉ ([] : List ℕ)) :=
  _root_.VoleMole.MoussakaUnbound.collision_or_forgery_unbound (X := Bool × ℕ)
    (fun x => x.2) (fun x => x.1 = true) (fun _ => (0 : ℕ)) (fun x => x.2) (fun k (_ : ℕ) => k)
    Set.univ Set.univ le_rfl [(0, 0)] [] [((0, 0), 0), ((0, 0), 1)]
    (fun q hq => ⟨(true, q.1), trivial, rfl, rfl, by simp at hq; simp [hq]⟩)
    (fun _ h => by simp at h)
    (fun j hj => ⟨(true, j.2), trivial, rfl, by simp at hj; rcases hj with rfl | rfl <;> rfl, rfl⟩)
    0 0 (by decide)

end VoleMole.Audit.UnboundOMUF
