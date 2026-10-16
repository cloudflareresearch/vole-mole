import VoleMole.ROM.PermAdapt
import VoleMole.ZK.CompleteRO
import VoleMole.Privacy.LeanProver
import VoleMole.ZK.ReadsROPerm
import VoleMole.Privacy.MoussakaInterleaveOC
import VoleMole.Privacy.PomFRITInterleaveOC
import VoleMole.Privacy.RatatouilleInterleaveOC
import VoleMole.Privacy.PomFRITLin
import VoleMole.Privacy.SeedXOFNC

/-!
# Non-vacuity checks for the headline theorems

Each `example` below instantiates a headline theorem's hypotheses on the adversary or on the
parameters with a concrete choice (a trivial adversary, a one-element instance family, the real
parameters), so that the theorem is not vacuous for that choice. This does not show the bound is
tight or that the event is meaningful; it rules out unsatisfiable hypotheses.

What is not exhibited here: a redemption or spend witness (it needs a UOV preimage; the KAT
vectors give instances, checked by `lake exe verifier_vectors`, not by a theorem); `hinj` for a
redemption, spend or Ratatouille issuance family with more than one instance; a concrete signer
with small abort term `φ` for Moussaka 4(b); completeness of the honest Anchors' verifier in the
4(b) games.
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
The signer hypothesis `Signer.Correct` holds for the always-failing signer, for which the abort
term `φ` is `1` and the bound is trivial: no concrete signer with small `φ` is exhibited in Lean
(the paper bound `E[φ] ≤ δ²⁵⁶` is `anonymityNC_vinegarRO`, under the hypothesis `hfail`). -/

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

end VoleMole.Audit
