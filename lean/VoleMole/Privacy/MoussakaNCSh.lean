import VoleMole.Privacy.MoussakaNCRO
import VoleMole.Privacy.SharedH3RO

/-!
# Moussaka against a non-colluding Moderator with one shared `H₃`

`Privacy/MoussakaNCRO.lean` (Theorem 4(b′) in the random-oracle and ideal-cipher model) gives each
of the game's four proofs its own `H₃` slice, and the guess sees the four slices labelled by proof.
Here the game is stated with one shared `H₃` (`ZK/SharedH3.lean`, `Privacy/SharedH3RO.lean`): the
shared tables carry `H₃`'s columns in their rows, the issuance and redemption proofs read their
columns at their prefixes (`leanPISh`, `leanPRSh`); the honest Anchors' Lean verifier reads no `H₃`.
The slot slices are still drawn but no prover reads them.

## Why the `4·q₃·2⁻¹²⁸` slice term disappears

In the slice model the final swap exchanges the two Clients' tapes, slices included, while the
guess sees the slices labelled by Client; `sim_fresh_NC` first replaces the slices the guess sees by
independent ones, at `2·q₃·2⁻¹²⁸` per world (the guess may read a Client's slice at its `ρ`). With
one shared `H₃` there are no Client-labelled slices: the issuance proofs read the shared tables,
which are not exchanged, and the slot slices are read by nobody but the guess. So replacing the
slot slices the guess sees by independent ones is a relabelling of uniform coins, **exact**
(`pr_slice_free`, `sim_fresh_NC_free`), for any issuance prover that does not read its slot slice
(`SliceFreeP`). The guess's `H₃` reads are row reads, paid in the redemption hops' zero-knowledge
error (`q_E`), as in every shared-`H₃` game.

## Results

* `anonymityNCRO_free`, `unlinkabilityNCRO_free`: `anonymityNCRO`, `unlinkabilityNCRO` for an
  issuance prover that ignores its slot slice, without the `4·q₃·2⁻¹²⁸` term.
* **`anonymityNCSh_leanG`** (every row type), `anonymityNCSh_num` (function rows),
  `anonymityNCSh_num_perm` (permutation rows):

      |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pR; q_E + 23038, q₅ + 2496, q_E + 23038)
                          + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁),

  `23038 = 3·(4607 + 1) + 2·4607` (both issuance proofs, each reading its row `ρ`, both
  verifications, the other redemption with its row); `anonymityNCSh_vinegarRO` with the abort
  term averaged over the vinegar tables.
* `unlinkabilityNCSh_leanG`, `unlinkabilityNCSh_num`, `unlinkabilityNCSh_num_perm`: one Anchor, any
  index rule, without `2·(φ₀ + φ₁)`.

No prefix-collision term: the issuance and redemption prefixes have different lengths, and two
issuance proofs with equal prefixes read the same column at their own `ρ` (one row each, counted).
The collision term `deltaNC` is the slice model's (`deltaNC_sh`, by `pr_h3At_slice`).
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim

attribute [local irreducible] com UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R]

/-! ## An issuance prover that does not read its slot slice -/

section Free

/-- **The issuance prover does not read its slot slice** (with one shared `H₃` it reads its slice
off the shared tables). -/
def SliceFreeP (PI : ProverRO R IssueInstance) : Prop :=
  ∀ w x rho (g g' : Tab3) s, PI w x rho g s = PI w x rho g' s

variable {A : AdversaryNCRO R} {idx : AnchorSet → UOVKey → ℕ} {PI : ProverRO R IssueInstance}
  {V : VerifierRO R} {sk : Bool → Signer}

lemma nizkV_free (hPI : SliceFreeP PI) (g g' : Tab3) (v : ShM R) :
    nizkV PI V g v = nizkV PI V g' v := by
  unfold nizkV
  congr 1
  funext w x rho
  exact hPI w x rho g g' v

lemma goodV_free (hPI : SliceFreeP PI) (c : Bool) (n : NR) (ρ : Coins proveSeedBytes) (g g' : Tab3)
    (v : ShM R) : goodV A idx PI V sk c (n, (ρ, g)) v = goodV A idx PI V sk c (n, (ρ, g')) v := by
  unfold goodV issNC
  rw [nizkV_free hPI g g' v]
  rfl

/-- **The game does not read Client `0`'s slot slice** (only the guess sees it, as `h₀`). -/
lemma gameNCROS_free₀ (hPI : SliceFreeP PI) (b : Bool) (n : NR) (ρ : Coins proveSeedBytes)
    (g g' : Tab3) (x₁ : TIr) (sL sR : RedSlot R) (h₀ h₁ : Tab3) (t : ShM R) :
    gameNCROS A idx PI V sk b (n, (ρ, g)) x₁ sL sR h₀ h₁ t ↔
      gameNCROS A idx PI V sk b (n, (ρ, g')) x₁ sL sR h₀ h₁ t := by
  unfold gameNCROS GV
  simp only [okW_congr₀ (A := A) (idx := idx) (sk := sk) (x₀ := (n, (ρ, g))) (x₀' := (n, (ρ, g')))
    rfl x₁, ptW_congr₀ (A := A) (idx := idx) (sk := sk) (x₀ := (n, (ρ, g))) (x₀' := (n, (ρ, g')))
    rfl x₁, goodV_free (A := A) (idx := idx) (V := V) (sk := sk) hPI false n ρ g g']

/-- The same for Client `1`. -/
lemma gameNCROS_free₁ (hPI : SliceFreeP PI) (b : Bool) (x₀ : TIr) (n : NR) (ρ : Coins proveSeedBytes)
    (g g' : Tab3) (sL sR : RedSlot R) (h₀ h₁ : Tab3) (t : ShM R) :
    gameNCROS A idx PI V sk b x₀ (n, (ρ, g)) sL sR h₀ h₁ t ↔
      gameNCROS A idx PI V sk b x₀ (n, (ρ, g')) sL sR h₀ h₁ t := by
  unfold gameNCROS GV
  simp only [okW_congr₁ (A := A) (idx := idx) (sk := sk) x₀ (x₁ := (n, (ρ, g))) (x₁' := (n, (ρ, g')))
    rfl, ptW_congr₁ (A := A) (idx := idx) (sk := sk) x₀ (x₁ := (n, (ρ, g))) (x₁' := (n, (ρ, g')))
    rfl, goodV_free (A := A) (idx := idx) (V := V) (sk := sk) hPI true n ρ g g']

/-- **A slice read only by the guess can be replaced by an independent one, exactly**: if `W`
reads the tape's own slice nowhere but in its second argument, the tape's slice and an independent
one give the same probability. -/
theorem pr_slice_free {Rest : Type*} [Fintype Rest] (W : TIr → Tab3 → Rest → Prop)
    (hW : ∀ (n : NR) (ρ : Coins proveSeedBytes) (g g' : Tab3) h r,
      W (n, (ρ, g)) h r ↔ W (n, (ρ, g')) h r) :
    pr (TIr × Rest) (fun z => W z.1 z.1.2.2 z.2) =
      pr ((TIr × Tab3) × Rest) (fun z => W z.1.1 z.1.2 z.2) := by
  have e : pr ((TIr × Tab3) × Rest) (fun z => W z.1.1 z.1.2 z.2) =
      pr ((TIr × Tab3) × Rest) (fun z => W (z.1.1.1, (z.1.1.2.1, z.1.2)) z.1.2 z.2) :=
    pr_congr fun z => hW z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.1.2 z.2
  rw [e]
  let E : (TIr × Rest) × Tab3 ≃ (TIr × Tab3) × Rest :=
    { toFun := fun w => (((w.1.1.1, (w.1.1.2.1, w.2)), w.1.1.2.2), w.1.2)
      invFun := fun z => (((z.1.1.1, (z.1.1.2.1, z.1.2)), z.2), z.1.1.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E]
  exact (pr_prod_fst (β := Tab3) (fun z : TIr × Rest => W z.1 z.1.2.2 z.2)).symm

variable {CR : Type} {simR : RedeemInstance → CR → Bytes} {progR : RedeemInstance → CR → ShM R → ShM R}

/-- **Both slot slices the guess sees made independent, exactly** (the issuance prover reads no
slot slice). -/
theorem sim_fresh_NC_free [Fintype CR] (hPI : SliceFreeP PI) (b : Bool) :
    pr _ (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redSimRO A.ro simR progR)) =
      pr _ (simFreshNC A idx PI V sk simR progR b) := by
  have h0 := pr_slice_free (Rest := (TIr × (TRs CR × TRs CR)) × ShM R)
    (fun x₀ h r => gameNCROS A idx PI V sk b x₀ r.1.1 (redSimRO A.ro simR progR r.1.2.1)
      (redSimRO A.ro simR progR r.1.2.2) h r.1.1.2.2 r.2)
    (fun n ρ g g' h r => gameNCROS_free₀ hPI b n ρ g g' _ _ _ _ _ _)
  have h1 := pr_slice_free (Rest := ((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)
    (fun x₁ h r => gameNCROS A idx PI V sk b r.1.1.1 x₁ (redSimRO A.ro simR progR r.1.2.1)
      (redSimRO A.ro simR progR r.1.2.2) r.1.1.2 h r.2)
    (fun n ρ g g' h r => gameNCROS_free₁ hPI b _ n ρ g g' _ _ _ _ _)
  let e0 : TIr × ((TIr × (TRs CR × TRs CR)) × ShM R) ≃ ((TIr × TIr) × (TRs CR × TRs CR)) × ShM R :=
    { toFun := fun z => (((z.1, z.2.1.1), z.2.1.2), z.2.2)
      invFun := fun x => (x.1.1.1, ((x.1.1.2, x.1.2), x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e1 : TIr × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R) ≃
      (TIr × Tab3) × ((TIr × (TRs CR × TRs CR)) × ShM R) :=
    { toFun := fun z => ((z.2.1.1.1, z.2.1.1.2), ((z.1, z.2.1.2), z.2.2))
      invFun := fun y => (y.2.1.1, (((y.1.1, y.1.2), y.2.1.2), y.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have p0 : pr _ (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redSimRO A.ro simR progR)) =
      pr (TIr × ((TIr × (TRs CR × TRs CR)) × ShM R)) (fun z => gameNCROS A idx PI V sk b z.1 z.2.1.1
        (redSimRO A.ro simR progR z.2.1.2.1) (redSimRO A.ro simR progR z.2.1.2.2) z.1.2.2
        z.2.1.1.2.2 z.2.2) := by
    rw [← pr_equiv e0]
    rfl
  have p1 : pr ((TIr × Tab3) × ((TIr × (TRs CR × TRs CR)) × ShM R)) (fun z =>
        gameNCROS A idx PI V sk b z.1.1 z.2.1.1 (redSimRO A.ro simR progR z.2.1.2.1)
          (redSimRO A.ro simR progR z.2.1.2.2) z.1.2 z.2.1.1.2.2 z.2.2) =
      pr (TIr × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)) (fun z =>
        gameNCROS A idx PI V sk b z.2.1.1.1 z.1 (redSimRO A.ro simR progR z.2.1.2.1)
          (redSimRO A.ro simR progR z.2.1.2.2) z.2.1.1.2 z.1.2.2 z.2.2) := by
    rw [← pr_equiv e1]
    rfl
  have p2 : pr _ (simFreshNC A idx PI V sk simR progR b) =
      pr ((TIr × Tab3) × (((TIr × Tab3) × (TRs CR × TRs CR)) × ShM R)) (fun z =>
        gameNCROS A idx PI V sk b z.2.1.1.1 z.1.1 (redSimRO A.ro simR progR z.2.1.2.1)
          (redSimRO A.ro simR progR z.2.1.2.2) z.2.1.1.2 z.1.2 z.2.2) := rfl
  rw [p0, p2, h0, p1]
  exact h1

end Free

/-! ## Theorem 4(b′) for an issuance prover that reads no slot slice -/

section Main

variable {A : AdversaryNCRO R} {idx : AnchorSet → UOVKey → ℕ} {PI : ProverRO R IssueInstance}
  {V : VerifierRO R} {sk : Bool → Signer} {PR : ProverRO R RedeemInstance}
  {CR : Type} [Fintype CR] [Nonempty CR] {simR : RedeemInstance → CR → Bytes}
  {progR : RedeemInstance → CR → ShM R → ShM R} {q3 q5 qE r5 rE v5 vE m5 mE : ℕ}

/-- One world, the issuance prover reading no slot slice: no slice term. -/
theorem real_simFresh_NC_free (hsk : ∀ c, (sk c).Correct (A.pk c)) (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPIF : SliceFreeP PI)
    (hV5 : ∀ pf x, Rd5 (V pf x) v5) (hVE : ∀ pf x, RdE (V pf x) vE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpR : ∀ x c, IsProg (progR x c) m5 mE) {εR : ℕ → ℕ → ℝ}
    (hR : ∀ a c, ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR
      (Budget pR q3 a c) (εR a c)) (hεR : ∀ a c, 0 ≤ εR a c) (b : Bool) :
    |pr _ (realGameNCRO A idx PI V sk PR b) - pr _ (simFreshNC A idx PI V sk simR progR b)| ≤
      εR (r5 + v5 + (r5 + v5) + (0 + r5) + q5) (rE + vE + (rE + vE) + (0 + rE) + qE) +
        (εR (r5 + v5 + (r5 + v5) + (0 + 0) + q5 + m5) (rE + vE + (rE + vE) + (0 + 0) + qE + mE) +
          deltaNC A idx sk PR progR b) := by
  have e0 : pr _ (realGameNCRO A idx PI V sk PR b) =
      pr _ (gameNCROT A idx PI V sk b (redRealRO A.ro PR) (redRealRO A.ro PR)) :=
    pr_congr fun x => realGameNCRO_iff A idx PI V sk hsk PR b x
  have h1 := hopL_NCRO (idx := idx) (V := V) (simR := simR) hsk hA hPI5 hPIE hV5 hVE hPR5 hPRE
    (hεR _ _) (hR _ _) b
  have h2 := hopR_NCRO (idx := idx) (PI := PI) (V := V) (PR := PR) hsk hA hPI5 hPIE hV5 hVE hpR
    (hεR _ _) (hR _ _) b
  have h3 := sim_fresh_NC_free (A := A) (idx := idx) (V := V) (sk := sk) (simR := simR)
    (progR := progR) hPIF b
  rw [e0, ← h3]
  have := abs_sub_le (pr _ (gameNCROT A idx PI V sk b (redRealRO A.ro PR) (redRealRO A.ro PR)))
    (pr _ (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redRealRO A.ro PR)))
    (pr _ (gameNCROT A idx PI V sk b (redSimRO A.ro simR progR) (redSimRO A.ro simR progR)))
  linarith

/-- **Theorem 4(b′) in the random-oracle and ideal-cipher model for an issuance prover that reads
no slot slice** (`anonymityNCRO` without the `4·q₃·2⁻¹²⁸` slice term):

    2·(εR(hop L) + εR(hop R)) + Σ_b deltaNC b + 2·(φ false + φ true). -/
theorem anonymityNCRO_free (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx)
    (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPIF : SliceFreeP PI)
    (hV5 : ∀ pf x, Rd5 (V pf x) v5) (hVE : ∀ pf x, RdE (V pf x) vE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpR : ∀ x c, IsProg (progR x c) m5 mE) {εR : ℕ → ℕ → ℝ}
    (hR : ∀ a c, ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR
      (Budget pR q3 a c) (εR a c)) (hεR : ∀ a c, 0 ≤ εR a c) :
    |pr _ (realGameNCRO A idx PI V sk PR false) - pr _ (realGameNCRO A idx PI V sk PR true)| ≤
      2 * (εR (r5 + v5 + (r5 + v5) + (0 + r5) + q5) (rE + vE + (rE + vE) + (0 + rE) + qE) +
          εR (r5 + v5 + (r5 + v5) + (0 + 0) + q5 + m5) (rE + vE + (rE + vE) + (0 + 0) + qE + mE)) +
        (deltaNC A idx sk PR progR false + deltaNC A idx sk PR progR true) +
        2 * (phi A.nc sk false + phi A.nc sk true) := by
  have h0 := real_simFresh_NC_free (idx := idx) (V := V) (simR := simR) hsk hA hPI5 hPIE hPIF hV5
    hVE hPR5 hPRE hpR hR hεR false
  have h1 := real_simFresh_NC_free (idx := idx) (V := V) (simR := simR) hsk hA hPI5 hPIE hPIF hV5
    hVE hPR5 hPRE hpR hR hεR true
  have g0 := fresh_hyb_NC (PI := PI) (V := V) (simR := simR) (progR := progR) hsk hidx false
  have g1 := fresh_hyb_NC (PI := PI) (V := V) (simR := simR) (progR := progR) hsk hidx true
  have he := hybFresh_eq (A := A) (idx := idx) (PI := PI) (V := V) (simR := simR) (progR := progR)
  rw [abs_le] at h0 h1 g0 g1 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, g0.1, g0.2, g1.1, g1.2]

/-- **Unlinkability against a non-colluding Moderator for an issuance prover that reads no slot
slice**: one Anchor, any index rule, `2·(εR(hop L) + εR(hop R)) + Σ_b deltaNC b`. -/
theorem unlinkabilityNCRO_free (hsk : ∀ c, (sk c).Correct (A.pk c)) (hpk : A.pk false = A.pk true)
    (hs : sk false = sk true) (hA : A.Budget q3 q5 qE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPIF : SliceFreeP PI)
    (hV5 : ∀ pf x, Rd5 (V pf x) v5) (hVE : ∀ pf x, RdE (V pf x) vE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpR : ∀ x c, IsProg (progR x c) m5 mE) {εR : ℕ → ℕ → ℝ}
    (hR : ∀ a c, ZeroKnowledgeRO RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR
      (Budget pR q3 a c) (εR a c)) (hεR : ∀ a c, 0 ≤ εR a c) :
    |pr _ (realGameNCRO A idx PI V sk PR false) - pr _ (realGameNCRO A idx PI V sk PR true)| ≤
      2 * (εR (r5 + v5 + (r5 + v5) + (0 + r5) + q5) (rE + vE + (rE + vE) + (0 + rE) + qE) +
          εR (r5 + v5 + (r5 + v5) + (0 + 0) + q5 + m5) (rE + vE + (rE + vE) + (0 + 0) + qE + mE)) +
        (deltaNC A idx sk PR progR false + deltaNC A idx sk PR progR true) := by
  have h0 := real_simFresh_NC_free (idx := idx) (V := V) (simR := simR) hsk hA hPI5 hPIE hPIF hV5
    hVE hPR5 hPRE hpR hR hεR false
  have h1 := real_simFresh_NC_free (idx := idx) (V := V) (simR := simR) hsk hA hPI5 hPIE hPIF hV5
    hVE hPR5 hPRE hpR hR hεR true
  have he := simFresh_eq_one (idx := idx) (PI := PI) (V := V) (simR := simR) (progR := progR) hpk hs
  rw [abs_le] at h0 h1 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

end Main

/-! ## With one shared `H₃`: the Lean provers reading their columns -/

section Shared

open VoleMole.Verifier VoleMole.Verifier.Bridge

variable [CipherRow R] (A : AdversaryNCRO (RowH R)) (idx : AnchorSet → UOVKey → ℕ)
  (sk : Bool → Signer)

/-- **The real game of Theorem 4(b′) with one shared `H₃`**: `realGameNCRO` with the issuance and
redemption proofs reading their slices off the shared tables at their prefixes (`leanPISh`,
`leanPRSh`) and the honest Anchors' Lean verifier (`leanVI`, no `H₃`). -/
def realGameNCSh (b : Bool) : ((TIr × TIr) × (TRr × TRr)) × ShM (RowH R) → Prop :=
  realGameNCRO A idx leanPISh leanVI sk leanPRSh b

omit [Fintype R] [Nonempty R] in
lemma leanPISh_free : SliceFreeP (leanPISh (R := R)) := fun _ _ _ _ _ _ => rfl

omit [Fintype R] [Nonempty R] in
lemma LNC_setK (b : Bool) (γ : (TIr × TIr) × TRs (SimCoins pR)) (s : ShM (RowH R)) (k : Pre)
    (g : Tab3) : LNC A idx sk leanProgR b γ (setK s k g) = setK (LNC A idx sk leanProgR b γ s) k g := by
  unfold LNC
  split <;> rfl

omit [Fintype R] [Nonempty R] in
@[simp] lemma h3At_LNC (b : Bool) (γ : (TIr × TIr) × TRs (SimCoins pR)) (s : ShM (RowH R))
    (k : Pre) : h3At (LNC A idx sk leanProgR b γ s) k = h3At s k := by
  unfold LNC
  split <;> rfl

/-- **The collision term with one shared `H₃` is the slice model's** (`pr_h3At_slice`: the right
redemption's slice is its column, independent of the left simulation's programming). -/
theorem deltaNC_sh (b : Bool) :
    deltaNC A idx sk (leanPRSh (R := R)) leanProgR b = deltaNC A idx sk leanPR leanProgR b := by
  unfold deltaNC
  simp only [redRealRO_sh, h3At_LNC]
  refine pr_h3At_slice (R := R) (Γ := (TIr × TIr) × TRs (SimCoins pR)) (ρT := Coins proveSeedBytes)
    (p := pI) (fun γ => keyR (wROf A.ro (ptW A idx sk b γ.1.1 γ.1.2 true))
      (xROf A.ro (ptW A idx sk b γ.1.1 γ.1.2 true)))
    (fun γ ρ G s => (redRealRO A.ro leanPR (ρ, G)).out (ptW A idx sk b γ.1.1 γ.1.2 true)
        (LNC A idx sk leanProgR b γ s) ≠
      (redRealRO A.ro leanPR (ρ, G)).out (ptW A idx sk b γ.1.1 γ.1.2 true) s)
    fun _ _ _ _ _ _ => ?_
  rw [LNC_setK]
  simp only [redRealRO_setK]

/-- **Theorem 4(b′) with one shared `H₃`, the Lean provers and verifier, every type of cipher
rows** (`ZKRow R`): the adversary's guess reads the rows (cipher and `H₃`) at `q_E` keys, `H₅` at
`q₅`, `H₂³` freely (and the unused slot slices at `q₃`, free):

    4·εz(pR; q_E + 23038, q₅ + 2496, q_E + 23038) + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁). -/
theorem anonymityNCSh_leanG [ZKRow R] (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx)
    {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr _ (realGameNCSh A idx sk false) - pr _ (realGameNCSh A idx sk true)| ≤
      4 * ZKRow.εz R pR (qE + 23038) (q5 + 2496) (qE + 23038) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * (phi A.nc sk false + phi A.nc sk true) := by
  have h := anonymityNCRO_free (A := A) (idx := idx) (PI := leanPISh) (V := leanVI) (sk := sk)
    (PR := leanPRSh) (simR := leanSim pR) (progR := leanProgR)
    (εR := fun a c => ZKRow.εz R pR c a c) hsk hidx hA
    leanPISh_rd5 leanPISh_rdE leanPISh_free leanVI_rd5 leanVI_rdE leanPRSh_rd5 leanPRSh_rdE
    (fun x c => progRO_isProg c) (fun a c => leanPRSh_zkRO q3 a c)
    (fun a c => ZKRow.εz_nonneg _ _ _ _)
  beta_reduce at h
  rw [deltaNC_sh, deltaNC_sh] at h
  have m1 := ZKRow.εz_mono (R := R) pR
    (q3 := 4607 + 1 + 4607 + (4607 + 1 + 4607) + (0 + (4607 + 1)) + qE) (q3' := qE + 23038) (by omega)
    (show 624 + 312 + (624 + 312) + (0 + 624) + q5 ≤ q5 + 2496 by omega)
    (show 4607 + 1 + 4607 + (4607 + 1 + 4607) + (0 + (4607 + 1)) + qE ≤ qE + 23038 by omega)
  have m2 := ZKRow.εz_mono (R := R) pR
    (q3 := 4607 + 1 + 4607 + (4607 + 1 + 4607) + (0 + 0) + qE + 4607) (q3' := qE + 23038) (by omega)
    (show 624 + 312 + (624 + 312) + (0 + 0) + q5 + 312 ≤ q5 + 2496 by omega)
    (show 4607 + 1 + 4607 + (4607 + 1 + 4607) + (0 + 0) + qE + 4607 ≤ qE + 23038 by omega)
  have d0 := deltaNC_le A idx sk hsk false
  have d1 := deltaNC_le A idx sk hsk true
  generalize (2 : ℝ) ^ 1024 = K at d0 d1 ⊢
  unfold realGameNCSh
  linarith

/-- **Unlinkability against a non-colluding Moderator with one shared `H₃`**, every type of cipher
rows: one Anchor, any index rule,

    4·εz(pR; q_E + 23038, q₅ + 2496, q_E + 23038) + 2·(noHitProb + 2⁻¹⁰²⁴). -/
theorem unlinkabilityNCSh_leanG [ZKRow R] (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hpk : A.pk false = A.pk true) (hs : sk false = sk true) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr _ (realGameNCSh A idx sk false) - pr _ (realGameNCSh A idx sk true)| ≤
      4 * ZKRow.εz R pR (qE + 23038) (q5 + 2496) (qE + 23038) + 2 * (noHitProb + 1 / 2 ^ 1024) := by
  have h := unlinkabilityNCRO_free (A := A) (idx := idx) (PI := leanPISh) (V := leanVI) (sk := sk)
    (PR := leanPRSh) (simR := leanSim pR) (progR := leanProgR)
    (εR := fun a c => ZKRow.εz R pR c a c) hsk hpk hs hA
    leanPISh_rd5 leanPISh_rdE leanPISh_free leanVI_rd5 leanVI_rdE leanPRSh_rd5 leanPRSh_rdE
    (fun x c => progRO_isProg c) (fun a c => leanPRSh_zkRO q3 a c)
    (fun a c => ZKRow.εz_nonneg _ _ _ _)
  beta_reduce at h
  rw [deltaNC_sh, deltaNC_sh] at h
  have m1 := ZKRow.εz_mono (R := R) pR
    (q3 := 4607 + 1 + 4607 + (4607 + 1 + 4607) + (0 + (4607 + 1)) + qE) (q3' := qE + 23038) (by omega)
    (show 624 + 312 + (624 + 312) + (0 + 624) + q5 ≤ q5 + 2496 by omega)
    (show 4607 + 1 + 4607 + (4607 + 1 + 4607) + (0 + (4607 + 1)) + qE ≤ qE + 23038 by omega)
  have m2 := ZKRow.εz_mono (R := R) pR
    (q3 := 4607 + 1 + 4607 + (4607 + 1 + 4607) + (0 + 0) + qE + 4607) (q3' := qE + 23038) (by omega)
    (show 624 + 312 + (624 + 312) + (0 + 0) + q5 + 312 ≤ q5 + 2496 by omega)
    (show 4607 + 1 + 4607 + (4607 + 1 + 4607) + (0 + 0) + qE + 4607 ≤ qE + 23038 by omega)
  have d0 := deltaNC_le A idx sk hsk false
  have d1 := deltaNC_le A idx sk hsk true
  generalize (2 : ℝ) ^ 1024 = K at d0 d1 ⊢
  unfold realGameNCSh
  linarith

end Shared

/-! ## The two cipher row types -/

/-- **Theorem 4(b′) with one shared `H₃`** (function rows):

    4·εRO(q_E + 23038, q₅ + 2496, q_E + 23038) + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(φ₀ + φ₁). -/
theorem anonymityNCSh_num (A : AdversaryNCRO (RowH (Blk → Blk))) (idx : AnchorSet → UOVKey → ℕ)
    (sk : Bool → Signer) (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx)
    {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr _ (realGameNCSh A idx sk false) - pr _ (realGameNCSh A idx sk true)| ≤
      4 * εRO (qE + 23038) (q5 + 2496) (qE + 23038) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * (phi A.nc sk false + phi A.nc sk true) :=
  anonymityNCSh_leanG A idx sk hsk hidx hA

/-- **Theorem 4(b′) with one shared `H₃`, AES as uniformly random permutations.** -/
theorem anonymityNCSh_num_perm (A : AdversaryNCRO (RowH (Equiv.Perm Blk)))
    (idx : AnchorSet → UOVKey → ℕ) (sk : Bool → Signer) (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hidx : IdxSound idx) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr _ (realGameNCSh A idx sk false) - pr _ (realGameNCSh A idx sk true)| ≤
      4 * εROPm pR (qE + 23038) (q5 + 2496) (qE + 23038) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * (phi A.nc sk false + phi A.nc sk true) :=
  anonymityNCSh_leanG A idx sk hsk hidx hA

/-- **Unlinkability against a non-colluding Moderator with one shared `H₃`** (function rows). -/
theorem unlinkabilityNCSh_num (A : AdversaryNCRO (RowH (Blk → Blk))) (idx : AnchorSet → UOVKey → ℕ)
    (sk : Bool → Signer) (hsk : ∀ c, (sk c).Correct (A.pk c)) (hpk : A.pk false = A.pk true)
    (hs : sk false = sk true) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr _ (realGameNCSh A idx sk false) - pr _ (realGameNCSh A idx sk true)| ≤
      4 * εRO (qE + 23038) (q5 + 2496) (qE + 23038) + 2 * (noHitProb + 1 / 2 ^ 1024) :=
  unlinkabilityNCSh_leanG A idx sk hsk hpk hs hA

/-- Unlinkability with one shared `H₃` and AES as uniformly random permutations. -/
theorem unlinkabilityNCSh_num_perm (A : AdversaryNCRO (RowH (Equiv.Perm Blk)))
    (idx : AnchorSet → UOVKey → ℕ) (sk : Bool → Signer) (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hpk : A.pk false = A.pk true) (hs : sk false = sk true) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr _ (realGameNCSh A idx sk false) - pr _ (realGameNCSh A idx sk true)| ≤
      4 * εROPm pR (qE + 23038) (q5 + 2496) (qE + 23038) + 2 * (noHitProb + 1 / 2 ^ 1024) :=
  unlinkabilityNCSh_leanG A idx sk hsk hpk hs hA

/-- **Theorem 4(b′) with one shared `H₃` and the vinegar random-oracle model** (every type of
cipher rows): the abort term `2·(δ₀^256 + δ₁^256)` averaged over the Anchors' vinegar tables. -/
theorem anonymityNCSh_vinegarRO {R : Type} [Fintype R] [Nonempty R] [CipherRow R] [ZKRow R]
    {Vin : Type} [Fintype Vin] [Nonempty Vin] (Good : Bool → Vin → Prop)
    (A : AdversaryNCRO (RowH R)) (idx : AnchorSet → UOVKey → ℕ) (skW : VTab Vin → Bool → Signer)
    (hsk : ∀ w c, (skW w c).Correct (A.pk c)) (hidx : IdxSound idx)
    (hfail : ∀ w c t, (skW w c).derivePreimage t = none → ∀ i, ¬ Good c (w c (tkey t) i))
    {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr (VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM (RowH R))) (fun z =>
        realGameNCSh A idx (skW z.1) false z.2) -
      pr (VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM (RowH R))) (fun z =>
        realGameNCSh A idx (skW z.1) true z.2)| ≤
      4 * ZKRow.εz R pR (qE + 23038) (q5 + 2496) (qE + 23038) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * (pr Vin (fun v => ¬ Good false v) ^ 256 + pr Vin (fun v => ¬ Good true v) ^ 256) := by
  have hcard : (0 : ℝ) < Fintype.card (VTab Vin) := by exact_mod_cast Fintype.card_pos
  have hphi (c : Bool) : (∑ w, phi A.nc (skW w) c) / Fintype.card (VTab Vin) ≤
      pr Vin (fun v => ¬ Good c v) ^ 256 := by
    have := pr_fail_vinegar Good A.nc skW hfail c
    rw [pr_prod] at this
    exact this
  set K := 4 * ZKRow.εz R pR (qE + 23038) (q5 + 2496) (qE + 23038) +
    2 * (noHitProb + 1 / 2 ^ 1024) with hK
  have hw (w : VTab Vin) : |pr _ (realGameNCSh A idx (skW w) false) -
      pr _ (realGameNCSh A idx (skW w) true)| ≤
        K + 2 * (phi A.nc (skW w) false + phi A.nc (skW w) true) := by
    have := anonymityNCSh_leanG A idx (skW w) (hsk w) hidx hA
    rw [hK]
    exact this
  refine (abs_pr_prod_sub_le_avg (fun z : VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM (RowH R)) =>
      realGameNCSh A idx (skW z.1) false z.2)
    (fun z => realGameNCSh A idx (skW z.1) true z.2)
    (fun w => K + 2 * (phi A.nc (skW w) false + phi A.nc (skW w) true)) hw).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_div,
    mul_div_cancel_left₀ _ hcard.ne', ← Finset.mul_sum, mul_div_assoc, Finset.sum_add_distrib,
    add_div]
  have := hphi false
  have := hphi true
  gcongr

end VoleMole.Privacy.Moussaka
