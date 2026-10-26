import VoleMole.ROM.PermAdapt
import VoleMole.ZK.CompleteRO
import VoleMole.Privacy.LeanProver
import VoleMole.ZK.ReadsROPerm
import VoleMole.Privacy.MoussakaInterleaveOC
import VoleMole.Privacy.MoussakaNCFind
import VoleMole.Privacy.PomFRITInterleaveOC
import VoleMole.Privacy.RatatouilleInterleaveOC
import VoleMole.Privacy.PomFRITLin
import VoleMole.Privacy.SeedXOFNC
import VoleMole.ROM.SpecSound
import VoleMole.Privacy.PqovDelta
import VoleMole.Privacy.PqovKeys

/-!
# Non-vacuity checks for the headline theorems

Each `example` below instantiates a headline theorem's hypotheses on the adversary or on the
parameters with a concrete choice (a trivial adversary, a one-element instance family, the real
parameters), so that the theorem is not vacuous for that choice. This does not show the bound is
tight or that the event is meaningful; it rules out unsatisfiable hypotheses.

The soundness section also instantiates the spec-relation corollaries (`ROM/SpecSound.lean`,
`*_spec`: the decoded witness in the spec relation, not only in the arithmetized one) and
`hinj` for families with more than one instance: any injective Ratatouille issuance family with
fixed-length `c`, Moussaka redemption with the challenge digest chosen by the prover, Ratatouille
spends with the nullifier and amount chosen by the prover (`EndToEnd/SpecRelations.lean`).

Moussaka 4(b) is instantiated with the model of pqov's `derive_preimage` (`Spec/PqovSigner.lean`;
correct and with `hfail` proved, so `anonymityNC_vinegarRO` applies as stated with 256 attempts and
`anonymityNC_pqov` with pqov's 255) for keys of pqov's key generation with oil matrix `O = 0`
(`keyO0`), averaged over their `P2` parts with an abort term `≤ 4·(255⁻³⁷ + 1/(255·256³⁷))`
(`anonymityNC_pqov_keys`, `anonymityNCRO_pqov_keys`), and the games are shown to reach redemption
(`pr_refused_NCRO_pqov`, `pr_refused_NCSh_le`: refusal `≤ φ₀ + φ₁ + 2·2⁻¹¹³` with the honest
Anchors' Lean verifier). The same for **pqov's real key generation** with any oil matrices `O`
(`Spec.Pqov.pqovKey O P1 P2`: `P3` computed as `calculate_F2_P3` does; `P` vanishes on the oil
space, `oilSpace_pqovKey`): `anonymityNC_pqov_pqovKeys`, `anonymityNCRO_pqov_pqovKeys`,
`pr_refused_NCRO_pqov` and `avg_delta255_pqovKey` instantiated with keys `pqovKey (O c) (P1 c) _`.

What is not exhibited here: a redemption or spend witness (it needs a UOV preimage; the KAT
vectors give instances, checked by `lake exe verifier_vectors`, not by a theorem); `hinj` for a
redemption or spend family with two keys of the same digest (false: the encoding hashes digests
only; for keys from `UovPk.ofCompressed`, distinct digests is SHAKE256 collision freedom, not a
theorem); a fixed key with a proved small fraction `δ` of bad vinegars (the bounds on `δ` are on
average over the key; for one key `δ` is a count over `256⁷⁴` vinegars, and the zero key has
`δ = 1`; for the test key the KAT check of `lake exe spec_kats` finds a good vinegar at the first
attempt on six targets, which is evidence, not a bound); the uniformity of `P2` (AES-128-CTR of
`pk_seed`), which the real-key bounds take as their modelling step.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Audit

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Verifier

/-! ## Soundness (`*_accept_le_adaptive`) -/

/-- The trivial prover (no queries) satisfies both query-bound hypotheses with zero budgets. -/
theorem pure_queryBounds {α : Type} (x : α) :
    IsQueryBoundP (pure x : OracleComp specIC α) (fun t => t.isRight = true) 0 ∧
      IsKindQueryBoundIC (pure x : OracleComp specIC α) 0 :=
  ⟨trivial, trivial⟩

/-- A one-element instance family satisfies `hinj`. -/
theorem hinj_unit {β : Type} (f : Unit → β) (g : β → ByteArray) :
    Function.Injective fun s => g (f s) :=
  fun _ _ _ => rfl

theorem toL_injective {a b : ByteArray} (h : toL a = toL b) : a = b := by
  apply ByteArray.ext
  rw [← Array.toList_inj, ← VoleMole.Privacy.toL_eq, ← VoleMole.Privacy.toL_eq, h]

/-- **`hinj` for Moussaka issuance families with `t` of fixed length** (from
`Spec.Moussaka.issueEncode_inj`; the docstring of `moussakaIssue_accept_le_adaptive` cites it). -/
theorem hinj_moussakaIssue {ι : Type} (inst : ι → ByteArray × ByteArray) (lr : Bool) (n : ℕ)
    (hlen : ∀ s, (inst s).1.size = n) (hi : Function.Injective inst) :
    Function.Injective fun s =>
      (moussakaIssue (inst s).1 (inst s).2 lr).instEnc ByteArray.empty := by
  intro s s' h
  simp only [moussakaIssue, toBA] at h
  have h' := VoleMole.Spec.Moussaka.issueEncode_inj (x := ⟨toL (inst s).1, toL (inst s).2⟩)
    (y := ⟨toL (inst s').1, toL (inst s').2⟩) (by simp [VoleMole.Privacy.length_toL, hlen])
    (by simpa using h)
  exact hi (Prod.ext (toL_injective h'.1) (toL_injective h'.2))

/-- The adaptive Moussaka issuance bound for every injective family of instances with
45-byte `t` (the real commitment length), the prover arbitrary. -/
example {ι β : Type} (inst : ι → ByteArray × ByteArray) (lr : Bool)
    (hlen : ∀ s, (inst s).1.size = 45) (hi : Function.Injective inst)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :=
  moussakaIssue_accept_le_adaptive inst lr (hinj_moussakaIssue inst lr 45 hlen hi) P qE hqE q hq

example (t c pf : ByteArray) (lr : Bool) :=
  moussakaIssue_accept_le_adaptive (ι := Unit) (β := Unit) (fun _ => (t, c)) lr
    (hinj_unit _ _) (pure (pf, ((), ()))) 0 trivial 0 trivial

example (c ci pf : ByteArray) (t0 : ℕ) (lr : Bool) :=
  ratatouilleIssue_accept_le_adaptive (ι := Unit) (β := Unit) (fun _ => (c, t0, ci)) lr
    (hinj_unit _ _) (pure (pf, ((), ()))) 0 trivial 0 trivial

example (A : List UovPk) (hA : A.length ≤ 64) (nf ci cr cd pf : ByteArray) (lr : Bool) :=
  moussakaRedeem_accept_le_adaptive (ι := Unit) (β := Unit) (fun _ => A) (fun _ => hA)
    (fun _ => nf) (fun _ => ci) (fun _ => cr) (fun _ => cd) lr (hinj_unit _ _)
    (pure (pf, ((), ()))) 0 trivial 0 trivial 0 trivial

example (pk : UovPk) (nf cn ci pf : ByteArray) (d : ℕ) (hd : d < 2 ^ 64) (lr : Bool) :=
  ratatouilleSpend_accept_le_adaptive (ι := Unit) (β := Unit) (fun _ => pk) (fun _ => nf)
    (fun _ => d) (fun _ => hd) (fun _ => cn) (fun _ => ci) lr (hinj_unit _ _)
    (pure (pf, ((), ()))) 0 trivial 0 trivial 0 trivial

example (pk : UovPk) (sig msg pf : ByteArray) (lr : Bool) :=
  pomfritRedeem_accept_le_adaptive (ι := Unit) (β := Unit) pk (fun _ => sig) (fun _ => msg) lr
    (pure (pf, ((), ()))) 0 trivial 0 trivial 0 trivial

/-! The permutation model with inverse queries. -/

example (t c pf : ByteArray) (lr : Bool) :=
  moussakaIssue_accept_le_adaptive_perm (ι := Unit) (β := Unit) (fun _ => (t, c)) lr
    (hinj_unit _ _) (pure (pf, ((), ()))) 0 trivial 0 trivial

example (c ci pf : ByteArray) (t0 : ℕ) (lr : Bool) :=
  ratatouilleIssue_accept_le_adaptive_perm (ι := Unit) (β := Unit) (fun _ => (c, t0, ci)) lr
    (hinj_unit _ _) (pure (pf, ((), ()))) 0 trivial 0 trivial

example (A : List UovPk) (hA : A.length ≤ 64) (nf ci cr cd pf : ByteArray) (lr : Bool) :=
  moussakaRedeem_accept_le_adaptive_perm (ι := Unit) (β := Unit) (fun _ => A) (fun _ => hA)
    (fun _ => nf) (fun _ => ci) (fun _ => cr) (fun _ => cd) lr (hinj_unit _ _)
    (pure (pf, ((), ()))) 0 trivial 0 trivial 0 trivial

example (pk : UovPk) (nf cn ci pf : ByteArray) (d : ℕ) (hd : d < 2 ^ 64) (lr : Bool) :=
  ratatouilleSpend_accept_le_adaptive_perm (ι := Unit) (β := Unit) (fun _ => pk) (fun _ => nf)
    (fun _ => d) (fun _ => hd) (fun _ => cn) (fun _ => ci) lr (hinj_unit _ _)
    (pure (pf, ((), ()))) 0 trivial 0 trivial 0 trivial

example (pk : UovPk) (sig msg pf : ByteArray) (lr : Bool) :=
  pomfritRedeem_accept_le_adaptive_perm (ι := Unit) (β := Unit) pk (fun _ => sig) (fun _ => msg)
    lr (pure (pf, ((), ()))) 0 trivial 0 trivial 0 trivial

/-! ## `hinj` for redemption, spend and Ratatouille issuance families

Families with more than one instance (`EndToEnd/SpecRelations.lean`), each with the spec-relation
corollary (`ROM/SpecSound.lean`). -/

/-- The spec-relation bound for Moussaka issuance (`moussakaIssue_accept_le_full_spec`) at
well-formed byte arrays (`|t| = 45`, `|ctx_iss| = 16`), for the trivial prover. -/
example (lr : Bool) (pf : ByteArray) :=
  moussakaIssue_accept_le_full_spec (β := Unit) (toBA (List.replicate 45 0))
    (toBA (List.replicate 16 0)) (by rw [Privacy.size_toBA, List.length_replicate])
    (by rw [Privacy.size_toBA, List.length_replicate]) lr (pure (pf, ())) 0 trivial 0 trivial

/-- Any injective Ratatouille issuance family with fixed-length `c` and `t_init < 2⁶⁴`. -/
example {ι β : Type} (inst : ι → ByteArray × ℕ × ByteArray) (lr : Bool) (n : ℕ)
    (hc : ∀ s, (inst s).1.size = n) (ht : ∀ s, (inst s).2.1 < 2 ^ 64)
    (hi : Function.Injective inst) (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :=
  ratatouilleIssue_accept_le_adaptive_spec inst ht lr
    (EndToEnd.SpecRel.hinj_ratatouilleIssue inst lr n hc ht hi) P qE hqE q hq

/-- Moussaka redemption with the challenge digest chosen by the prover (fixed Anchors with 32-byte
digests, `nf` and contexts): the index is the challenge digest itself. -/
example {β : Type} (A : List UovPk) (hA : A.length ≤ 64) (hdig : ∀ pk ∈ A, pk.digest.size = 32)
    (nf ci cr : ByteArray) (hnf : nf.size = 24) (hci : ci.size = 16) (hcr : cr.size = 16)
    (lr : Bool) (P : OracleComp specIC (ByteArray × (ByteArray × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :=
  moussakaRedeem_accept_le_adaptive_spec (fun _ => A) (fun _ => hA) (fun _ => nf) (fun _ => ci)
    (fun _ => cr) id (fun _ => hnf) (fun _ => hci) (fun _ => hcr) lr
    (EndToEnd.SpecRel.hinj_moussakaRedeem _ _ _ _ id lr (fun _ => hdig) (fun _ => by omega)
      24 16 16 (fun _ => hnf) (fun _ => hci) (fun _ => hcr) (fun s s' h => by simpa using h))
    P qE hqE n hn q hq

/-- Ratatouille spends under a fixed key (32-byte digest), `c_next` and context, with the nullifier
and the amount chosen by the prover. -/
example {β : Type} (pk : UovPk) (hdig : pk.digest.size = 32) (cn ctx : ByteArray) (lr : Bool)
    (P : OracleComp specIC
      (ByteArray × ((Spec.Ratatouille.Nullifier × Spec.Ratatouille.Credits) × β)))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :=
  have hi := EndToEnd.SpecRel.hinj_ratatouilleSpend (fun _ => pk)
    (fun s : Spec.Ratatouille.Nullifier × Spec.Ratatouille.Credits => Privacy.Ratatouille.bOf s.1)
    (fun s => s.2.toNat) (fun _ => cn) (fun _ => ctx) lr 32 24 cn.size (fun _ => hdig)
    (fun s => by simp [Privacy.Ratatouille.bOf, Privacy.size_toBA]) (fun s => s.2.toNat_lt)
    (fun _ => rfl) (fun s s' h => by
      simp only [Prod.mk.injEq, true_and, and_true] at h
      exact Prod.ext (EndToEnd.SpecRel.bOf_inj h.1) (UInt64.toNat_inj.1 h.2))
  ratatouilleSpend_accept_le_adaptive_spec (fun _ => pk)
    (fun s : Spec.Ratatouille.Nullifier × Spec.Ratatouille.Credits => Privacy.Ratatouille.bOf s.1)
    (fun s => s.2.toNat) (fun s => s.2.toNat_lt) (fun _ => cn) (fun _ => ctx) lr hi
    P qE hqE n hn q hq

/-! ## A Moussaka issuance instance and witness in the relation

The issuance relation is satisfiable by construction (`t := Com(nf, ctx_iss, ctx_red, r)`), so the
completeness and zero-knowledge theorems below apply to a concrete statement. (`Com` is not
evaluated: the instance field is the term `com …`.) -/

section Issue

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy.Moussaka VoleMole.ZK.Sim
open VoleMole.Verifier.Bridge VoleMole.Privacy

/-- The all-zero issuance instance. -/
def issX : IssueInstance :=
  ⟨com (List.replicate 24 0) (List.replicate 16 0) (List.replicate 16 0) (List.replicate 16 0),
    List.replicate 16 0⟩

/-- Its witness. -/
def issW : Spec.Bytes :=
  encodeIssueWitness (List.replicate 24 0) (List.replicate 16 0) (List.replicate 16 0)
    (List.replicate 16 0)

theorem issW_rel : IssueRelW issX issW :=
  ⟨⟨List.replicate 24 0, List.replicate 16 0, List.replicate 16 0, by simp, by simp, by simp, rfl,
    rfl⟩, by simp [issX]⟩

/-- Completeness at the concrete witness (`ZKHyp` discharged by `zkHypI`). -/
example := moussakaIssue_complete_rom Hashes.shake hashesWF_shake issX issW issW_rel

/-- A distinguisher that looks at the proof (did the prover output one?) and reads no table. -/
def dOk {T₃ T₂ T₅ C : Type} : Except String ByteArray → T₃ → T₂ → T₅ → C → Prop :=
  fun o _ _ _ _ => ∃ b, o = .ok b

/-- `zk_rom_ic_h23_num` at the concrete witness, for `dOk` with empty read sets. -/
example := zk_rom_ic_h23_num Hashes.shake (stI issX) (toBA issW) (cs := csI issX) rfl
  (zkHypI issX issW issW_rel) hashesWF_shake (smallParams_of_le (by decide) (by decide)) dOk
  (fun _ _ _ _ _ => ∅) (fun _ _ _ _ _ _ _ => Iff.rfl) (q3 := 0) (fun _ _ _ _ _ => by simp)
  (fun _ _ _ _ _ => ∅) (fun _ _ _ _ _ _ _ => Iff.rfl) (q5 := 0) (fun _ _ _ _ _ => by simp)
  (fun _ _ _ _ _ => ∅) (fun _ _ _ _ _ _ _ => Iff.rfl) (qE := 0) (fun _ _ _ _ _ => by simp)

example := zk_rom_ic_h23_num_perm Hashes.shake (stI issX) (toBA issW) (cs := csI issX) rfl
  (zkHypI issX issW issW_rel) hashesWF_shake (smallParams_of_le (by decide) (by decide)) dOk
  (fun _ _ _ _ _ => ∅) (fun _ _ _ _ _ _ _ => Iff.rfl) (q3 := 0) (fun _ _ _ _ _ => by simp)
  (fun _ _ _ _ _ => ∅) (fun _ _ _ _ _ _ _ => Iff.rfl) (q5 := 0) (fun _ _ _ _ _ => by simp)
  (fun _ _ _ _ _ => ∅) (fun _ _ _ _ _ _ _ => Iff.rfl) (qE := 0) (fun _ _ _ _ _ => by simp)

/-- `lean_zeroKnowledgeRO` applied to the concrete witness and a budget-0 distinguisher. -/
example := lean_zeroKnowledgeRO Hashes.shake pI stI (fun _ => rfl) rfl (fun _ w => toBA w)
  IssueRelW csI zkHypI hashesWF_shake (smallParams_of_le (by decide) (by decide)) 0 0 0
  issX issW issW_rel (fun o _ _ => ∃ b, o = .ok b)
  ⟨fun _ _ => Rd3.const _, fun _ _ => Rd5.const _, fun _ _ => RdE.const _⟩

example := lean_zeroKnowledgeRO_perm pI Hashes.shake stI (fun _ => rfl) rfl (fun _ w => toBA w)
  IssueRelW csI zkHypI hashesWF_shake (smallParams_of_le (by decide) (by decide)) 0 0 0
  issX issW issW_rel (fun o _ _ => ∃ b, o = .ok b)
  ⟨fun _ _ => Rd3.const _, fun _ _ => Rd5.const _, fun _ _ => RdE.const _⟩

end Issue

/-! ## Privacy: Moussaka 4(a)

An adversary whose interaction ignores the tables and whose guess is constant meets every budget
at `0` and the hiding hypothesis at `εhide = 0` (its reductions are constant, so their hiding
advantage is `0`). The hypotheses are thus satisfiable with small `εhide`; for an adversary whose
guess depends on the commitments, `εhide` is its reduction's hiding advantage, computational. -/

section Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy VoleMole.Privacy.Moussaka
open VoleMole.ZK.Sim VoleMole.ZK VoleMole.ROM.Reads

theorem hidingAdv_true (ci cr : Spec.Bytes) : hidingAdv ci cr (fun _ => True) = 0 := by
  unfold hidingAdv; simp [pr_const]

/-- Every hiding advantage is at most `1`, so `εhide = 1` always satisfies the hiding hypotheses
(and makes the bound trivial): `εhide` is meaningful only as the reduction's actual advantage. -/
theorem hidingAdv_le_one (ci cr : Spec.Bytes) (D : Spec.Bytes × Spec.Bytes × Spec.Bytes × Spec.Bytes → Prop) :
    hidingAdv ci cr D ≤ 1 := by
  unfold hidingAdv
  rw [abs_le]
  constructor <;>
    linarith [pr_le_one (fun x => D (hideReal ci cr x)), pr_nonneg (fun x => D (hideReal ci cr x)),
      pr_le_one (fun x => D (hideIdeal ci cr x)), pr_nonneg (fun x => D (hideIdeal ci cr x))]

/-- The zero key and a one-key Anchor Set. -/
def k0 : UOVKey := ⟨[], fun _ => 0⟩
def S0 : AnchorSet := ⟨[k0], ⟨by simp, by simp [maxAnchors], by simp⟩⟩

/-- The two-session adversary with a constant guess. -/
def mRO {R : Type} : AdversaryRO R :=
  ⟨fun _ => 0, fun _ => 0, fun _ => k0, fun _ _ _ _ => 0, fun _ _ _ => (S0, []),
    fun _ _ _ _ _ => True⟩

theorem mRO_budget {R : Type} [Fintype R] [Nonempty R] : (mRO (R := R)).Budget 0 0 0 :=
  ⟨fun _ _ _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ _ _ => Rd3.const _,
    fun _ _ _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ _ _ => Rd3.const _,
    fun _ _ _ _ => Rd5.const _, fun _ _ _ _ => RdE.const _⟩

example (idx : AnchorSet → UOVKey → ℕ) := anonymityRO_lean_num mRO idx mRO_budget (εhide := 0)
  (fun _ _ => (hidingAdv_true _ _).le)

/-- The many-session adversary with a constant guess. -/
def mN (ι : Type) {R : Type} : AdversaryN R ι :=
  ⟨fun _ => 0, fun _ => 0, fun _ => k0, fun _ => k0, fun _ _ _ _ => 0, fun _ _ _ _ => 0,
    fun _ _ _ _ => (S0, []), fun _ _ _ _ => (S0, []), fun _ _ _ _ _ _ _ _ => True⟩

theorem mN_budget (ι : Type) {R : Type} [Fintype R] [Nonempty R] : (mN ι (R := R)).Budget 0 0 0 :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ _ _ _ _ _ => Rd3.const _,
    fun _ _ _ _ _ _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ _ _ _ _ _ => Rd3.const _,
    fun _ _ _ _ _ _ _ => Rd5.const _, fun _ _ _ _ _ _ _ => RdE.const _⟩

example (ι : Type) [Fintype ι] [DecidableEq ι] (idx : AnchorSet → UOVKey → ℕ) :=
  anonymityN_lean_le (mN ι) idx (mN_budget ι) (εhide := 0)
    (fun _ _ _ => (hidingAdv_true _ _).le)

/-- The interleaved adversary: no further sessions started, a constant guess. -/
def mIL {R : Type} : AdversaryILM R :=
  ⟨0, 0, 0, fun _ => .start (0, 0, k0), fun _ => 0, fun _ => 0, fun _ _ => k0, fun _ _ => 0,
    fun _ _ => (S0, []), fun _ _ _ => True⟩

theorem mIL_budget {R : Type} [Fintype R] [Nonempty R] : (mIL (R := R)).Budget 0 0 0 :=
  ⟨fun _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ => Rd3.const _,
    fun _ _ _ _ _ => Rd3.const _, fun _ _ => Rd5.const _, fun _ _ => RdE.const _⟩

example (n : ℕ) (idx : AnchorSet → UOVKey → ℕ) :=
  anonymityILO_lean_le (n := n) mIL.toO idx mIL_budget.toO mIL.toO_sBudget (εhide := 0)
    (fun _ _ _ => (hidingAdv_true _ _).le)

end Moussaka

/-! ## Privacy: PomFRIT (no hiding assumption) -/

section PomFRIT

open VoleMole.Spec VoleMole.Privacy VoleMole.Privacy.PomFRIT VoleMole.ZK.Sim VoleMole.ROM.Reads

def pk0 : UOVKey := ⟨[], fun _ => 0⟩

def pN (ι : Type) {R : Type} : AdversaryN R ι :=
  ⟨pk0, fun _ => [], fun _ => pk0, fun _ => [], fun _ _ _ _ => [], fun _ _ _ _ => [],
    fun _ _ _ _ _ _ _ _ => True⟩

theorem pN_budget (ι : Type) {R : Type} [Fintype R] [Nonempty R] : (pN ι (R := R)).Budget 0 0 0 :=
  ⟨fun _ _ _ _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ _ _ _ => Rd3.const _,
    fun _ _ _ _ _ _ _ => Rd5.const _, fun _ _ _ _ _ _ _ => RdE.const _⟩

example (ι : Type) [Fintype ι] [DecidableEq ι] := blindnessN_lean_le (pN ι) (pN_budget ι)

def pIL {R : Type} : AdversaryIL R :=
  ⟨0, 0, 0, fun _ => .start (pk0, []), fun _ => pk0, fun _ _ => [], fun _ _ => [],
    fun _ _ _ => True⟩

theorem pIL_budget {R : Type} [Fintype R] [Nonempty R] : (pIL (R := R)).Budget 0 0 0 :=
  ⟨fun _ _ _ => Rd3.const _, fun _ _ _ => Rd3.const _, fun _ _ => Rd5.const _,
    fun _ _ => RdE.const _⟩

example (n : ℕ) := blindnessILO_lean_le (n := n) pIL.toO pIL_budget.toO pIL.toO_sBudget

/-- With `H₄` a table (the adversary may depend on it). -/
example (ι : Type) [Fintype ι] [DecidableEq ι] :=
  blindnessNH_lean_le (fun _ => pN ι) (fun _ => pN_budget ι)

def pP (N : ℕ) {R : Type} : AdversaryP R N :=
  ⟨fun _ => pk0, fun _ _ => [], fun _ _ _ => [], fun _ _ _ _ => True⟩

example (N : ℕ) (w w' : Fin N → Bool) :=
  blindnessPH_lean_le (fun _ => pP N) (fun _ => (by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> first | exact Rd3.const _ | exact Rd5.const _ |
      exact RdE.const _)) w w'

end PomFRIT

/-! ## Privacy: Ratatouille -/

section Ratatouille

open VoleMole.Spec VoleMole.Spec.Ratatouille VoleMole.Privacy VoleMole.Privacy.Ratatouille
open VoleMole.ZK.Sim VoleMole.ROM.Reads

/-- The interleaved adversary: no further Clients started, a constant guess. -/
noncomputable def rIL {R : Type} : AdversaryILR R :=
  ⟨0, 0, 0, 0, fun _ => .start default, fun _ => default, fun _ => default, fun _ => default,
    fun _ _ => default, fun _ => default, fun _ => default, fun _ => default, fun _ _ _ => True⟩

theorem rIL_budget {R : Type} [Fintype R] [Nonempty R] : (rIL (R := R)).Budget 0 0 0 :=
  ⟨fun _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ => Rd3.const _,
    fun _ _ _ _ _ => Rd3.const _, fun _ _ => Rd5.const _, fun _ _ => RdE.const _⟩

theorem hidingAdvR_true (ctx : Context) : hidingAdv ctx (fun _ _ => True) = 0 := by
  unfold hidingAdv; simp [pr_const]

example (n K : ℕ) (b₁ b₂ b₁' b₂' : Bool) :=
  unlinkabilityILO_lean_le (n := n) (K := K) rIL.toO rIL_budget.toO rIL.toO_sBudget
    (εhide := 0) (fun _ _ _ _ => (hidingAdvR_true _).le) b₁ b₂ b₁' b₂'

end Ratatouille

/-! ## Privacy: Moussaka 4(b), non-colluding

`IdxSound` is satisfiable by a non-degenerate rule (the first key with the issuer's public map).
A digest lookup is not `IdxSound` in the model (`UOVKey`'s digest does not determine its map).
The signer hypothesis `Signer.Correct` alone also holds for the always-failing signer, for which
the abort term `φ` is `1` and the bound is trivial; pqov's signer with a small abort term is the
next section. -/

section NC

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy VoleMole.Privacy.Moussaka
open VoleMole.ZK.Sim

open Classical in
/-- The Client's index: the first Anchor key with its issuer's public map, else out of range. -/
noncomputable def idxEval (S : AnchorSet) (pk : UOVKey) : ℕ :=
  if h : ∃ i, ∃ k, S.keys[i]? = some k ∧ k.eval = pk.eval then Nat.find h else S.keys.length

open Classical in
theorem idxEval_sound : IdxSound idxEval := by
  intro S pk k hk
  unfold idxEval at hk
  split_ifs at hk with h
  · obtain ⟨k', hk', he⟩ := Nat.find_spec h
    rw [hk'] at hk
    cases hk
    exact he
  · simp at hk

/-- The always-failing signer: correct for every key. -/
def skNone : Signer := ⟨fun _ => none⟩

theorem skNone_correct (pk : UOVKey) : skNone.Correct pk := fun _ _ _ h => by cases h

/-- For it the abort term is `1`. -/
theorem phi_skNone (A : AdversaryNC) (c : Bool) : phi A (fun _ => skNone) c = 1 := by
  unfold phi; simp [skNone, pr_const]

def nc {R : Type} : AdversaryNCRO R :=
  ⟨fun _ => 0, fun _ => 0, fun _ => k0, fun _ => (S0, []), fun _ _ _ => True⟩

theorem nc_budget {R : Type} [Fintype R] [Nonempty R] : (nc (R := R)).Budget 0 0 0 :=
  ⟨fun _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ => Rd3.const _,
    fun _ _ _ _ _ => Rd3.const _, fun _ _ => Rd5.const _, fun _ _ => RdE.const _⟩

example := anonymityNCSh_num nc idxEval (fun _ => skNone) (fun _ => skNone_correct _)
  idxEval_sound nc_budget

example := anonymityNCSh_num_seed idxEval (fun _ => nc) (fun _ _ => skNone)
  (fun _ _ => skNone_correct _) idxEval_sound (fun _ => nc_budget) (fun _ => le_rfl)
  (fun _ _ => RdX.const _)

end NC

/-! ## Privacy: Moussaka 4(b) with pqov's signer

The signer is the model of pqov's `derive_preimage` (`Spec/PqovSigner.lean`; in the vinegar
random-oracle model `pqovRO`, 255 usable attempts as in pqov, or all 256), for keys of the family
`keyO0` (pqov's key generation with `O = 0`, `P3 = 0`; `P` vanishes on the oil space,
`oilSpace_keyO0`). Its correctness and `hfail` are theorems, so `anonymityNC_vinegarRO` applies as
stated (256 attempts) and `anonymityNC_pqov` with 255; averaged over the keys' `P2` parts the abort
term is `≤ 4·(255⁻³⁷ + 1/(255·256³⁷))` (`anonymityNC_pqov_keys`, `anonymityNCRO_pqov_keys`), and the
games reach redemption (`pr_refused_NCRO_pqov`, with the honest Anchors' Lean verifier). -/

section NCPqov

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.Privacy VoleMole.Privacy.Moussaka
open VoleMole.Spec.Pqov VoleMole.ZK.Sim VoleMole.Arith

/-- A key of the family `keyO0` with a one-byte digest. -/
def kq (P1 : ℕ → GF256) (P2 : P2Part) (d : UInt8) : UOVKey := ⟨[d], (keyO0 P1 P2).map⟩

theorem oilSpace_kq (P1 : ℕ → GF256) (P2 : P2Part) (d : UInt8) : OilSpace (kq P1 P2 d) 0 :=
  oilSpace_of_map_eq rfl 0 (oilSpace_keyO0 P1 P2)

/-- The two Anchors' keys (digests `0`, `1`). -/
def pkq (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) (c : Bool) : UOVKey :=
  kq (P1 c) (P2 c) (bif c then 1 else 0)

/-- The Anchor Set holding both keys. -/
def Sq (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) : AnchorSet :=
  ⟨[pkq P1 P2 false, pkq P1 P2 true], ⟨by simp, by simp [maxAnchors], by simp [pkq, kq]⟩⟩

/-- A Moderator with both keys in both sets (and a constant guess). -/
def ncq (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) : AdversaryNC :=
  ⟨fun _ => 0, fun _ => 0, pkq P1 P2, fun _ => (Sq P1 P2, []), fun _ => True⟩

/-- The random-oracle version. -/
def ncqRO {R : Type} (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) : AdversaryNCRO R :=
  ⟨fun _ => 0, fun _ => 0, pkq P1 P2, fun _ => (Sq P1 P2, []), fun _ _ _ => True⟩

theorem ncqRO_budget {R : Type} [Fintype R] [Nonempty R] (P1 : Bool → ℕ → GF256)
    (P2 : Bool → P2Part) : (ncqRO (R := R) P1 P2).Budget 0 0 0 :=
  ⟨fun _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ => Rd3.const _,
    fun _ _ _ _ _ => Rd3.const _, fun _ _ => Rd5.const _, fun _ _ => RdE.const _⟩

open Classical in
/-- The index rule `idxEval` finds a key whenever the set holds one with the issuer's map. -/
theorem foundNC_idxEval (A : AdversaryNC) (c side : Bool)
    (h : ∃ i : ℕ, ∃ k : UOVKey, (A.choose side).1.keys[i]? = some k ∧ k.eval = (A.pk c).eval) :
    foundNC A idxEval c side = true := by
  unfold foundNC idxEval
  split_ifs
  obtain ⟨k, hk, -⟩ := Nat.find_spec h
  rw [hk]
  rfl

theorem found_ncqRO {R : Type} (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) (c side : Bool) :
    foundNC (ncqRO (R := R) P1 P2).nc idxEval c side = true :=
  foundNC_idxEval _ c side ⟨bif c then 1 else 0, pkq P1 P2 c, by cases c <;> rfl, rfl⟩

/-- **`anonymityNC_vinegarRO` as stated, with pqov's signer** (all 256 attempts; `hfail` is
`pqovRO256_hfail`). -/
example (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) (PI : NIZK IssueInstance) {CR : Type}
    [Fintype CR] [Nonempty CR] (simR : RedeemInstance → CR → Bytes) (PR : NIZK RedeemInstance)
    {εR : ℝ} (hεR : 0 ≤ εR) (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :=
  anonymityNC_vinegarRO (fun c v => (sysMat (pkq P1 P2 c) 0 v).det ≠ 0) (ncq P1 P2) idxEval PI
    (pqovRO (ncq P1 P2).pk (fun _ => 0) 256) simR PR hεR
    (pqovRO_correct _ _ (fun _ => oilSpace_kq _ _ _) 256) idxEval_sound
    (fun w c t h i => pqovRO256_hfail _ _ w c t h i) hR

/-- The Moderator `ncq` chooses Anchor Sets with both issuers (`MoussakaFind.Contains`). -/
theorem contains_ncq (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) :
    VoleMole.Privacy.MoussakaFind.Contains (ncq P1 P2) := fun c _ =>
  ⟨pkq P1 P2 c, by cases c <;> simp [ncq, Sq], rfl⟩

/-- **Theorem 4(b) for `main`'s Client (`find_issuer`) with pqov's signer** (all 256 attempts). -/
example (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) (PI : NIZK IssueInstance) {CR : Type}
    [Fintype CR] [Nonempty CR] (simR : RedeemInstance → CR → Bytes) (PR : NIZK RedeemInstance)
    {εR : ℝ} (hεR : 0 ≤ εR) (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :=
  VoleMole.Privacy.MoussakaFind.anonymityNC_vinegarRO (fun c v => (sysMat (pkq P1 P2 c) 0 v).det ≠ 0)
    (ncq P1 P2) PI (pqovRO (ncq P1 P2).pk (fun _ => 0) 256) simR PR hεR
    (pqovRO_correct _ _ (fun _ => oilSpace_kq _ _ _) 256) (contains_ncq P1 P2)
    (fun w c t h i => pqovRO256_hfail _ _ w c t h i) hR

/-- **Theorem 4(b′) with pqov's signer (255 attempts)** for a concrete pair of keys:
`≤ 4εR + 2·(δ₀²⁵⁵ + δ₁²⁵⁵)`. -/
example (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) (PI : NIZK IssueInstance) {CR : Type}
    [Fintype CR] [Nonempty CR] (simR : RedeemInstance → CR → Bytes) (PR : NIZK RedeemInstance)
    {εR : ℝ} (hεR : 0 ≤ εR) (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :=
  anonymityNC_pqov (ncq P1 P2) idxEval PI (fun _ => 0) (fun _ => oilSpace_kq _ _ _) idxEval_sound
    simR PR hεR hR

/-- **Averaged over the Anchors' keys (`P2` uniform)**: the abort term is
`≤ 4·(255⁻³⁷ + 1/(255·256³⁷))` (about `2⁻²⁹³·⁸`). -/
example (P1 : Bool → ℕ → GF256) (PI : NIZK IssueInstance) {CR : Type} [Fintype CR] [Nonempty CR]
    (simR : RedeemInstance → CR → Bytes) (PR : NIZK RedeemInstance) {εR : ℝ} (hεR : 0 ≤ εR)
    (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :=
  anonymityNC_pqov_keys P1 (ncq P1) (fun _ _ => rfl) idxEval PI idxEval_sound simR PR hεR hR

/-- The same in the random-oracle and ideal-cipher model (the Lean prover and verifier). -/
example (P1 : Bool → ℕ → GF256) :=
  anonymityNCRO_pqov_keys (R := Blk → Blk) P1 (ncqRO P1) (fun _ _ => rfl) idxEval idxEval_sound
    (fun κ => ncqRO_budget P1 κ)

/-- **The game reaches redemption**: with pqov's signers and the honest Anchors' Lean verifier, the
redemptions are refused with probability `≤ δ₀²⁵⁵ + δ₁²⁵⁵ + 2·2⁻¹¹³` (averaged over the vinegar
tables). -/
example (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) :=
  pr_refused_NCRO_pqov (R := Blk → Blk) (ncqRO P1 P2) idxEval (fun _ => 0)
    (fun _ => oilSpace_kq _ _ _) idxEval_sound (found_ncqRO P1 P2)

/-- With one shared `H₃`, for any signers correct for their keys. -/
example (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) (sk : Bool → Signer)
    (hsk : ∀ c, (sk c).Correct (pkq P1 P2 c)) :=
  pr_refused_NCSh_le (R := Blk → Blk) (ncqRO P1 P2) idxEval sk hsk idxEval_sound (found_ncqRO P1 P2)

/-- The key-averaged fraction of bad vinegars: `E[δ] ≤ 1/255 + 256⁻⁷⁴`, `E[δ²⁵⁵] ≤ 255⁻³⁷ + …`. -/
example (P1 : ℕ → GF256) := avg_delta_keyO0 P1
example (P1 : ℕ → GF256) := avg_delta255_keyO0 P1

/-- For a fixed key the fraction of bad vinegars can be `1`. -/
example : delta ⟨[], fun _ => 0⟩ 0 = 1 := delta_zero_key 0

/-! ### With pqov's real key generation (any oil matrices) -/

/-- A key of pqov's key generation (`pqovKey O P1 P2`) with a one-byte digest. -/
noncomputable def kqR (O : OilMat) (P1 : ℕ → GF256) (P2 : P2Part) (d : UInt8) : UOVKey :=
  ⟨[d], (pqovKey O P1 P2).map⟩

theorem oilSpace_kqR (O : OilMat) (P1 : ℕ → GF256) (P2 : P2Part) (d : UInt8) :
    OilSpace (kqR O P1 P2 d) O :=
  oilSpace_of_map_eq rfl O (oilSpace_pqovKey O P1 P2)

/-- The two Anchors' keys (digests `0`, `1`), Anchor `c` with oil matrix `O c`. -/
noncomputable def pkqR (O : Bool → OilMat) (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part)
    (c : Bool) : UOVKey :=
  kqR (O c) (P1 c) (P2 c) (bif c then 1 else 0)

/-- The Anchor Set holding both keys. -/
noncomputable def SqR (O : Bool → OilMat) (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) :
    AnchorSet :=
  ⟨[pkqR O P1 P2 false, pkqR O P1 P2 true], ⟨by simp, by simp [maxAnchors], by simp [pkqR, kqR]⟩⟩

/-- A Moderator with both keys in both sets (and a constant guess). -/
noncomputable def ncqR (O : Bool → OilMat) (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) :
    AdversaryNC :=
  ⟨fun _ => 0, fun _ => 0, pkqR O P1 P2, fun _ => (SqR O P1 P2, []), fun _ => True⟩

/-- The random-oracle version. -/
noncomputable def ncqROR {R : Type} (O : Bool → OilMat) (P1 : Bool → ℕ → GF256)
    (P2 : Bool → P2Part) : AdversaryNCRO R :=
  ⟨fun _ => 0, fun _ => 0, pkqR O P1 P2, fun _ => (SqR O P1 P2, []), fun _ _ _ => True⟩

theorem ncqROR_budget {R : Type} [Fintype R] [Nonempty R] (O : Bool → OilMat)
    (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) : (ncqROR (R := R) O P1 P2).Budget 0 0 0 :=
  ⟨fun _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ => Rd3.const _, fun _ _ _ _ _ => Rd3.const _,
    fun _ _ _ _ _ => Rd3.const _, fun _ _ => Rd5.const _, fun _ _ => RdE.const _⟩

theorem found_ncqROR {R : Type} (O : Bool → OilMat) (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part)
    (c side : Bool) : foundNC (ncqROR (R := R) O P1 P2).nc idxEval c side = true :=
  foundNC_idxEval _ c side ⟨bif c then 1 else 0, pkqR O P1 P2 c, by cases c <;> rfl, rfl⟩

/-- **Theorem 4(b′) with pqov's real keys and signers**, averaged over the `P2` parts: abort term
`≤ 4·(255⁻³⁷ + 1/(255·256³⁷))`, for every choice of oil matrices and `P1` parts. -/
example (O : Bool → OilMat) (P1 : Bool → ℕ → GF256) (PI : NIZK IssueInstance) {CR : Type}
    [Fintype CR] [Nonempty CR] (simR : RedeemInstance → CR → Bytes) (PR : NIZK RedeemInstance)
    {εR : ℝ} (hεR : 0 ≤ εR) (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :=
  anonymityNC_pqov_pqovKeys O P1 (ncqR O P1) (fun _ _ => rfl) idxEval PI idxEval_sound simR PR
    hεR hR

/-- The same in the random-oracle and ideal-cipher model (the Lean prover and verifier). -/
example (O : Bool → OilMat) (P1 : Bool → ℕ → GF256) :=
  anonymityNCRO_pqov_pqovKeys (R := Blk → Blk) O P1 (ncqROR O P1) (fun _ _ => rfl) idxEval
    idxEval_sound (fun κ => ncqROR_budget O P1 κ)

/-- The game with pqov's real keys reaches redemption. -/
example (O : Bool → OilMat) (P1 : Bool → ℕ → GF256) (P2 : Bool → P2Part) :=
  pr_refused_NCRO_pqov (R := Blk → Blk) (ncqROR O P1 P2) idxEval O
    (fun _ => oilSpace_kqR _ _ _ _) idxEval_sound (found_ncqROR O P1 P2)

/-- The real-key-averaged fraction of bad vinegars. -/
example (O : OilMat) (P1 : ℕ → GF256) := avg_delta255_pqovKey O P1

end NCPqov

end VoleMole.Audit
