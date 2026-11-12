import VoleMole.Privacy.RatatouilleMany
import VoleMole.Privacy.MoussakaLin

/-!
# Ratatouille with `N` challenge pairs: the other pairs on private tables

`unlinkabilityP_lean_num` (`Privacy/RatatouilleMany.lean`) is quadratic in `N`: each step of the
hybrid over the pairs is the two-session table-reading game of the Issuer `A.hop k c v` that runs
the other `N − 1` pairs itself (issuances and round-1 spends in its stages, round-2 spends in its
guess), so every hop charges their reads. Here, as for Moussaka (`Privacy/MoussakaLin.lean`), the
other pairs run on a private `(H₅, cipher)` pair, by the interleaved lazy-sampling lemma
`Privacy.pr_split_le`: their spends are proved for amounts and tokens that depend on the Issuer's
answers after pair `k`'s requests, which `pr_resample` does not allow.

* **Point read sets** (`rdIssR_cons`, `rdSpR_cons`, from `ZK.Sim.rdRO_cons`): an issuance and a
  spend (a proof only when the Client's checks pass) are consistent readers of their points.
* **The joint run** (`tauR`): pair `k`'s issuances and rounds on `a`, the other pairs' on `u`, the
  Issuer's stages in between; read sets `RAR`, `RBR` (both rounds of every other pair); jointly
  consistent (`tauR_cons`); the hop's game is the run with `a = u` (`realGameRA_hop_iff`,
  `Iff.rfl`).
* **The reduction** `A.hopS k c v u` (`AdversaryP.hopG` with the guess on the patched tables):
  its stages read only `H₂³` (`hopS_iBudget`: `(0, 3(N − 1)·2³², 0, 0)`), its guess has the
  Issuer's own budget (`hopS_gBudget`); its game is the split run (`realGameRA_hopS_iff`,
  `Iff.rfl`).
* **The step** (`hop_close_hopS`, `hop_step`) and the hybrid (`realGameP_hybrid_avg`, the steps
  averaged over the other pairs' tapes): **`unlinkabilityP_lin`**, if each step's bad event
  (`badR`: pair `k`'s points meet the other pairs' points in the split world) has probability
  `≤ β`, any two worlds differ by `≤ N·(εPair0R(q₃, q₅, q_E, N − 1) + 2β)`; in numbers
  (`εPair0R_le`, `unlinkabilityP_lin_le`) `≤ N·(2·2⁻¹⁰² + (N − 1)·2⁻¹²⁸ + 8·(q₃ + q₅ +
  221·q_E)·2⁻¹²⁸ + 2·εhide + 2β)`.

As for Moussaka, `β` is bounded on paper only (`H₄` a random oracle; `lean/docs/zk.md` §10.8,
"Linear in `N`": `β ≲ 64(N − 1)·2⁻¹²⁸`); in these games `H₄` is SHAKE.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Privacy.PomFRIT (T5 RdS AgR mixR Disj agR_mixR mixR_inv agR_mixR_of_disj)
open VoleMole.Privacy.Moussaka (rdNone rdUnion rdUnionI agR_rdNone agR_left agR_right agR_at Rw)

/-- The proof sizes of the Lean provers. -/
local notation "ZL" => Sizes.labelRows

/-! ## The Lean provers and the Clients read points -/

section Provers

/-- **The issuance prover's point read set.** -/
noncomputable def rdIR (x : IssueInstance) (w : IssueWitness) (ρ : Rho) (g3 : Tab3) (g : Tab2G pI)
    (t : T5) : RdS :=
  rdRO Hashes.shake (stI x) (encI x w) (bOf ρ) g3 g t

/-- **The spend prover's point read set.** -/
noncomputable def rdSR (x : SpendInstance) (w : SpendWitness) (ρ : Rho) (g3 : Tab3) (g : Tab2G pI)
    (t : T5) : RdS :=
  rdRO Hashes.shake (stS x) (encS x w) (bOf ρ) g3 g t

theorem rdIR_cons (x : IssueInstance) (w : IssueWitness) (ρ : Rho) (g3 : Tab3) (g : Tab2G pI)
    (t t' : T5) (h : AgR (rdIR x w ρ g3 g t) t t') :
    rdIR x w ρ g3 g t' = rdIR x w ρ g3 g t ∧
      leanPIR (R := Rw) x w ρ g3 (toSp g t') = leanPIR (R := Rw) x w ρ g3 (toSp g t) := by
  obtain ⟨e1, e2⟩ := rdRO_cons (st := stI x) (w := encI x w) hashesWF_shake (bOf ρ) g3 g t t' h
  exact ⟨e1, congrArg (vecOf _) e2⟩

theorem rdSR_cons (x : SpendInstance) (w : SpendWitness) (ρ : Rho) (g3 : Tab3) (g : Tab2G pI)
    (t t' : T5) (h : AgR (rdSR x w ρ g3 g t) t t') :
    rdSR x w ρ g3 g t' = rdSR x w ρ g3 g t ∧
      leanPSR (R := Rw) x w ρ g3 (toSp g t') = leanPSR (R := Rw) x w ρ g3 (toSp g t) := by
  obtain ⟨e1, e2⟩ := rdRO_cons (st := stS x) (w := encS x w) hashesWF_shake (bOf ρ) g3 g t t' h
  exact ⟨e1, congrArg (vecOf _) e2⟩

variable (pk : PublicKey) (ctx : Context) (tInit : Credits)

/-- **An issuance's read set**: its proof's. -/
noncomputable def rdIssR (x : TRe) (g : Tab2G pI) (t : T5) : RdS :=
  rdIR (xIX ctx tInit x) (wIX x) (vec x.2.1) x.2.2 g t

theorem rdIssR_cons (x : TRe) (g : Tab2G pI) (t t' : T5) (h : AgR (rdIssR ctx tInit x g t) t t') :
    rdIssR ctx tInit x g t' = rdIssR ctx tInit x g t ∧
      issXR (R := Rw) ctx tInit x (toSp g t') = issXR ctx tInit x (toSp g t) := by
  obtain ⟨e1, e2⟩ := rdIR_cons _ _ _ _ g t t' h
  exact ⟨e1, issXR_det ctx tInit x _ _ e2⟩

/-- **A spend's read set**: its proof's when the Client's checks pass, none otherwise. -/
noncomputable def rdSpR (tok : Option TokenS) (d : Credits) (y : TRe) (g : Tab2G pI) (t : T5) : RdS := by
  classical
  exact match tok with
  | none => rdNone
  | some τ => if τ.Valid pk ctx then
      (match clientCheck τ.t τ.x d with
        | none => rdNone
        | some t' => rdSR (xSX pk ctx τ d t' y) (wSX τ t' y) (vec y.2.1) y.2.2 g t)
    else rdNone

theorem rdSpR_cons (tok : Option TokenS) (d : Credits) (y : TRe) (g : Tab2G pI) (t t' : T5)
    (h : AgR (rdSpR pk ctx tok d y g t) t t') :
    rdSpR pk ctx tok d y g t' = rdSpR pk ctx tok d y g t ∧
      spXR (R := Rw) pk ctx tok d y (toSp g t') = spXR pk ctx tok d y (toSp g t) := by
  classical
  rcases tok with _ | τ
  · exact ⟨by simp only [rdSpR], by simp only [spXR, spendOf]⟩
  by_cases hv : τ.Valid pk ctx
  · rcases hc : clientCheck τ.t τ.x d with _ | t''
    · refine ⟨by simp only [rdSpR, hv, ↓reduceIte, hc], ?_⟩
      simp only [spXR, spendOf, hv, not_true_eq_false, ↓reduceIte, hc]
    · have h' : AgR (rdSR (xSX pk ctx τ d t'' y) (wSX τ t'' y) (vec y.2.1) y.2.2 g t) t t' := by
        simpa only [rdSpR, hv, ↓reduceIte, hc] using h
      obtain ⟨e1, e2⟩ := rdSR_cons _ _ _ _ g t t' h'
      refine ⟨by simp only [rdSpR, hv, ↓reduceIte, hc, e1], ?_⟩
      exact spXR_det pk ctx τ d t'' hv hc y _ _ e2
  · refine ⟨by simp only [rdSpR, hv, ↓reduceIte], ?_⟩
    simp only [spXR, spendOf, hv, not_false_eq_true, ↓reduceIte]

end Provers

/-! ## One step of the hybrid as two interleaved readers -/

section Step

variable {N : ℕ}

namespace AdversaryP

variable (A : AdversaryP Rw N) (k : Fin N) (c : {j : Fin N // j ≠ k} → PT)
  (v : {j : Fin N // j ≠ k} → Bool × Bool)

/-- **The hop with the other pairs on the pair `u`** (with the game's `H₂³`), its guess looking at
the game's tables through `φ`. With `u` the game's own pair and `φ = id` this is `A.hop k c v`. -/
noncomputable def hopG (u : T5) (φ : IssTr ZL → Rounds ZL → ShR Rw → ShR Rw) : AdversaryRA Rw ZL where
  pk := A.pk
  ctx := A.ctx
  tInit := A.tInit
  respondIss tr i _ s := A.respondIss (A.hopTR k c tr (toSp s.1 u)) k i
  d₁ tr _ s := A.d₁ (A.hopTR k c tr (toSp s.1 u)) k
  respond₁ tr rq _ s := A.respond₁ (A.hopTR k c tr (toSp s.1 u)) (A.hopQ k c v tr rq (toSp s.1 u)) k
  d₂ tr rq _ s := A.d₂ (A.hopTR k c tr (toSp s.1 u)) (A.hopQ k c v tr rq (toSp s.1 u)) k
  guess tr y sl s := A.guess (A.hopTR k c tr (toSp s.1 u)) (A.hopY k c v tr y (toSp s.1 u))
    (joinK k sl fun j => slOfR (c j)) (φ tr y s)

variable (b₁ b₂ : Bool)

/-- Pair `k`'s issuance transcript on the pair `a`. -/
noncomputable def trA (z : PT × Tab2G pI) (a : T5) : IssTr ZL := trOf A.keyRO z.1 (toSp z.2 a)

/-- All transcripts: pair `k`'s on `a`, the others' on `u`. -/
noncomputable def TRu (z : PT × Tab2G pI) (a u : T5) : Fin N → IssTr ZL :=
  A.hopTR k c (A.trA z a) (toSp z.2 u)

/-- Pair `k`'s messages: stage 1 from all transcripts, stage 2 also from the round-1 requests. -/
noncomputable def mA (z : PT × Tab2G pI) (a u : T5) : MsgR :=
  (A.M1 (A.TRu k c z a u) k,
    A.M2 (A.TRu k c z a u) (A.hopQ k c v (A.trA z a)
      (rq1 A.keyRO (A.M1 (A.TRu k c z a u) k) b₁ z.1 (toSp z.2 a)) (toSp z.2 u)) k)

/-- Pair `k`'s rounds on `a`. -/
noncomputable def yA (z : PT × Tab2G pI) (a u : T5) : Rounds ZL :=
  roundsOf A.keyRO (A.mA k c v b₁ z a u) b₁ b₂ z.1 (toSp z.2 a)

/-- What the guess receives besides the slices and the tables. -/
abbrev OutR (N : ℕ) := (Fin N → IssTr ZL) × (Fin N → Rounds ZL)

/-- **The joint run**: pair `k` on `a`, the other pairs on `u`. -/
noncomputable def tauR (z : PT × Tab2G pI) (a u : T5) : OutR N :=
  (A.TRu k c z a u, A.hopY k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u))

/-- The guess. -/
def guessR (z : PT × Tab2G pI) (X : OutR N) (t : T5) : Prop :=
  A.guess X.1 X.2 (joinK k (slOfR z.1) fun j => slOfR (c j)) (toSp z.2 t)

/-- **The real game is the joint run on one pair.** -/
theorem realGameRA_hop_iff (z : PT × Tab2G pI) (t : T5) :
    realGameRA (A.hop k c v) leanPIR leanPSR b₁ b₂ (z.1, toSp z.2 t) ↔
      A.guessR k c z (A.tauR k c v b₁ b₂ z t t) t :=
  Iff.rfl

/-- The two issuance results of pair `k` on `a`. -/
noncomputable def riA (z : PT × Tab2G pI) (a : T5) : IssRes × IssRes :=
  (issXR A.keyRO.ctx A.keyRO.tInit z.1.1.1 (toSp z.2 a), issXR A.keyRO.ctx A.keyRO.tInit z.1.1.2 (toSp z.2 a))

/-- Pair `k`'s round-1 spend result on `a`. -/
noncomputable def o1A (z : PT × Tab2G pI) (a u : T5) : SpRes :=
  spXR A.keyRO.pk A.keyRO.ctx (some (tau1R A.keyRO (A.mA k c v b₁ z a u) b₁ (A.riA z a)))
    (A.mA k c v b₁ z a u).1.2 z.1.2.1 (toSp z.2 a)

/-- **Pair `k`'s read set** (on `a`): its two issuances and two spends. -/
noncomputable def RAR (z : PT × Tab2G pI) (a u : T5) : RdS :=
  rdUnion (rdUnion (rdIssR A.keyRO.ctx A.keyRO.tInit z.1.1.1 z.2 a)
      (rdIssR A.keyRO.ctx A.keyRO.tInit z.1.1.2 z.2 a))
    (rdUnion (rdSpR A.keyRO.pk A.keyRO.ctx (some (tau1R A.keyRO (A.mA k c v b₁ z a u) b₁ (A.riA z a)))
        (A.mA k c v b₁ z a u).1.2 z.1.2.1 z.2 a)
      (rdSpR A.keyRO.pk A.keyRO.ctx
        (some (tau2R A.keyRO (A.mA k c v b₁ z a u) b₁ b₂ (A.riA z a) (A.o1A k c v b₁ z a u)))
        (A.mA k c v b₁ z a u).2.2 z.1.2.2 z.2 a))

/-- Another pair's messages, from pair `k`'s transcript `tr` and rounds `y`, on `w`. -/
noncomputable def mJ (tr : IssTr ZL) (y : Rounds ZL) (w : ShR Rw) (j : {j : Fin N // j ≠ k}) : MsgR :=
  (A.M1 (A.hopTR k c tr w) j, A.M2 (A.hopTR k c tr w) (joinK k (y.map Prod.fst) (A.hopRQ k c v tr w)) j)

/-- Another pair's issuance results on `w`. -/
noncomputable def riJ (w : ShR Rw) (j : {j : Fin N // j ≠ k}) : IssRes × IssRes :=
  (issXR A.keyRO.ctx A.keyRO.tInit (c j).1.1 w, issXR A.keyRO.ctx A.keyRO.tInit (c j).1.2 w)

/-- Another pair's round-1 spend result on `w`. -/
noncomputable def o1J (tr : IssTr ZL) (y : Rounds ZL) (w : ShR Rw) (j : {j : Fin N // j ≠ k}) : SpRes :=
  spXR A.keyRO.pk A.keyRO.ctx (some (tau1R A.keyRO (A.mJ k c v tr y w j) (v j).1 (A.riJ k c w j)))
    (A.mJ k c v tr y w j).1.2 (c j).2.1 w

/-- **The other pairs' read set** on `u` (with `H₂³` table `g`), from pair `k`'s transcript `tr`
and rounds `y`: their issuances and both spends. -/
noncomputable def RBf (tr : IssTr ZL) (y : Rounds ZL) (g : Tab2G pI) (u : T5) : RdS :=
  rdUnionI fun j => rdUnion
    (rdUnion (rdIssR A.keyRO.ctx A.keyRO.tInit (c j).1.1 g u) (rdIssR A.keyRO.ctx A.keyRO.tInit (c j).1.2 g u))
    (rdUnion
      (rdSpR A.keyRO.pk A.keyRO.ctx
        (some (tau1R A.keyRO (A.mJ k c v tr y (toSp g u) j) (v j).1 (A.riJ k c (toSp g u) j)))
        (A.mJ k c v tr y (toSp g u) j).1.2 (c j).2.1 g u)
      (rdSpR A.keyRO.pk A.keyRO.ctx
        (some (tau2R A.keyRO (A.mJ k c v tr y (toSp g u) j) (v j).1 (v j).2 (A.riJ k c (toSp g u) j)
          (A.o1J k c v tr y (toSp g u) j)))
        (A.mJ k c v tr y (toSp g u) j).2.2 (c j).2.2 g u))

/-- The other pairs' read set in the joint run. -/
noncomputable def RBR (z : PT × Tab2G pI) (a u : T5) : RdS :=
  A.RBf k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) z.2 u

/-- **The reduction**: the hop with the other pairs on the private pair `u`, its guess on the
tables patched with `u` at their points. -/
noncomputable def hopS (u : T5) : AdversaryRA Rw ZL :=
  A.hopG k c v u fun tr y s => toSp s.1 (mixR (A.RBf k c v tr y s.1 u) u (s.2.1, s.2.2))

/-- **The reduction's game is the split run.** -/
theorem realGameRA_hopS_iff (z : PT × Tab2G pI) (a u : T5) :
    realGameRA (A.hopS k c v u) leanPIR leanPSR b₁ b₂ (z.1, toSp z.2 a) ↔
      A.guessR k c z (A.tauR k c v b₁ b₂ z a u) (mixR (A.RBR k c v b₁ b₂ z a u) u a) :=
  Iff.rfl

/-- **The joint run is consistent.** -/
theorem tauR_cons (z : PT × Tab2G pI) (a u a' u' : T5) (hA : AgR (A.RAR k c v b₁ b₂ z a u) a a')
    (hB : AgR (A.RBR k c v b₁ b₂ z a u) u u') :
    A.tauR k c v b₁ b₂ z a' u' = A.tauR k c v b₁ b₂ z a u ∧
      A.RAR k c v b₁ b₂ z a' u' = A.RAR k c v b₁ b₂ z a u ∧
      A.RBR k c v b₁ b₂ z a' u' = A.RBR k c v b₁ b₂ z a u := by
  -- pair `k`'s issuances
  obtain ⟨r0, eI0⟩ := rdIssR_cons A.keyRO.ctx A.keyRO.tInit z.1.1.1 z.2 a a' (agR_left (agR_left hA))
  obtain ⟨r1, eI1⟩ := rdIssR_cons A.keyRO.ctx A.keyRO.tInit z.1.1.2 z.2 a a' (agR_right (agR_left hA))
  have eRi : A.riA z a' = A.riA z a := by unfold riA; rw [eI0, eI1]
  have etr : A.trA z a' = A.trA z a := by
    unfold trA trOf
    rw [issRealR_out, issRealR_out, issRealR_out, issRealR_out, eI0, eI1]
  -- the other pairs' issuances
  have eX : ∀ j : {j : Fin N // j ≠ k},
      issXR (R := Rw) A.keyRO.ctx A.keyRO.tInit (c j).1.1 (toSp z.2 u') =
        issXR A.keyRO.ctx A.keyRO.tInit (c j).1.1 (toSp z.2 u) ∧
      issXR (R := Rw) A.keyRO.ctx A.keyRO.tInit (c j).1.2 (toSp z.2 u') =
        issXR A.keyRO.ctx A.keyRO.tInit (c j).1.2 (toSp z.2 u) ∧
      rdIssR A.keyRO.ctx A.keyRO.tInit (c j).1.1 z.2 u' = rdIssR A.keyRO.ctx A.keyRO.tInit (c j).1.1 z.2 u ∧
      rdIssR A.keyRO.ctx A.keyRO.tInit (c j).1.2 z.2 u' = rdIssR A.keyRO.ctx A.keyRO.tInit (c j).1.2 z.2 u := by
    intro j
    obtain ⟨q0, f0⟩ := rdIssR_cons A.keyRO.ctx A.keyRO.tInit (c j).1.1 z.2 u u'
      (agR_left (agR_left (agR_at hB j)))
    obtain ⟨q1, f1⟩ := rdIssR_cons A.keyRO.ctx A.keyRO.tInit (c j).1.2 z.2 u u'
      (agR_right (agR_left (agR_at hB j)))
    exact ⟨f0, f1, q0, q1⟩
  have eRJ : ∀ j, A.riJ k c (toSp z.2 u') j = A.riJ k c (toSp z.2 u) j := fun j => by
    unfold riJ; rw [(eX j).1, (eX j).2.1]
  have eW : A.issFam k c (toSp z.2 u') = A.issFam k c (toSp z.2 u) := funext fun j => eRJ j
  have eTR : ∀ tr, A.hopTR k c tr (toSp z.2 u') = A.hopTR k c tr (toSp z.2 u) := fun tr => by
    rw [hopTR_eq, hopTR_eq, eW]
  -- the other pairs' round 1
  have eS1 : ∀ j : {j : Fin N // j ≠ k},
      spXR (R := Rw) A.keyRO.pk A.keyRO.ctx
          (some (tau1R A.keyRO (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j) (v j).1
            (A.riJ k c (toSp z.2 u) j)))
          (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j).1.2 (c j).2.1 (toSp z.2 u') =
        spXR A.keyRO.pk A.keyRO.ctx
          (some (tau1R A.keyRO (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j) (v j).1
            (A.riJ k c (toSp z.2 u) j)))
          (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j).1.2 (c j).2.1 (toSp z.2 u) ∧
      rdSpR A.keyRO.pk A.keyRO.ctx
          (some (tau1R A.keyRO (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j) (v j).1
            (A.riJ k c (toSp z.2 u) j)))
          (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j).1.2 (c j).2.1 z.2 u' =
        rdSpR A.keyRO.pk A.keyRO.ctx
          (some (tau1R A.keyRO (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j) (v j).1
            (A.riJ k c (toSp z.2 u) j)))
          (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j).1.2 (c j).2.1 z.2 u := fun j => by
    have h := rdSpR_cons A.keyRO.pk A.keyRO.ctx _ _ _ z.2 u u' (agR_left (agR_right (agR_at hB j)))
    exact ⟨h.2, h.1⟩
  have eSF : A.sp1Fam k c v (A.trA z a) (A.issFam k c (toSp z.2 u)) (toSp z.2 u') =
      A.sp1Fam k c v (A.trA z a) (A.issFam k c (toSp z.2 u)) (toSp z.2 u) :=
    funext fun j => (eS1 j).1
  have eRQ : A.hopRQ k c v (A.trA z a) (toSp z.2 u') = A.hopRQ k c v (A.trA z a) (toSp z.2 u) := by
    rw [hopRQ_eq, hopRQ_eq, eW, eSF]
  -- pair `k`'s round 1
  have hO1 := rdSpR_cons A.keyRO.pk A.keyRO.ctx _ _ _ z.2 a a' (agR_left (agR_right hA))
  have eO1 : spXR (R := Rw) A.keyRO.pk A.keyRO.ctx
        (some (tau1R A.keyRO (A.mA k c v b₁ z a u) b₁
          (issXR A.keyRO.ctx A.keyRO.tInit z.1.1.1 (toSp z.2 a), issXR A.keyRO.ctx A.keyRO.tInit z.1.1.2 (toSp z.2 a))))
        (A.mA k c v b₁ z a u).1.2 z.1.2.1 (toSp z.2 a') =
      spXR A.keyRO.pk A.keyRO.ctx
        (some (tau1R A.keyRO (A.mA k c v b₁ z a u) b₁
          (issXR A.keyRO.ctx A.keyRO.tInit z.1.1.1 (toSp z.2 a), issXR A.keyRO.ctx A.keyRO.tInit z.1.1.2 (toSp z.2 a))))
        (A.mA k c v b₁ z a u).1.2 z.1.2.1 (toSp z.2 a) := hO1.2
  have eRq : rq1 A.keyRO (A.M1 (A.hopTR k c (A.trA z a) (toSp z.2 u)) k) b₁ z.1 (toSp z.2 a') =
      rq1 A.keyRO (A.M1 (A.hopTR k c (A.trA z a) (toSp z.2 u)) k) b₁ z.1 (toSp z.2 a) := by
    have hm1 : (A.mA k c v b₁ z a u).1 = A.M1 (A.hopTR k c (A.trA z a) (toSp z.2 u)) k := rfl
    have e := eO1
    rw [tau1R_eq, hm1] at e
    dsimp only at e
    unfold rq1
    rw [spRealR_outX, spRealR_outX, issRealR_out, issRealR_out, issRealR_out, issRealR_out, eI0, eI1, e]
  have eQ : ∀ rq, A.hopQ k c v (A.trA z a) rq (toSp z.2 u') = A.hopQ k c v (A.trA z a) rq (toSp z.2 u) :=
    fun rq => by unfold hopQ; rw [eTR, eRQ]
  have emA : A.mA k c v b₁ z a' u' = A.mA k c v b₁ z a u := by
    unfold mA TRu
    rw [etr, eTR, eRq, eQ]
  -- pair `k`'s rounds
  have hO2 := rdSpR_cons A.keyRO.pk A.keyRO.ctx _ _ _ z.2 a a' (agR_right (agR_right hA))
  have eO2 : spXR (R := Rw) A.keyRO.pk A.keyRO.ctx
        (some (tau2R A.keyRO (A.mA k c v b₁ z a u) b₁ b₂
          (issXR A.keyRO.ctx A.keyRO.tInit z.1.1.1 (toSp z.2 a), issXR A.keyRO.ctx A.keyRO.tInit z.1.1.2 (toSp z.2 a))
          (spXR A.keyRO.pk A.keyRO.ctx
            (some (tau1R A.keyRO (A.mA k c v b₁ z a u) b₁
              (issXR A.keyRO.ctx A.keyRO.tInit z.1.1.1 (toSp z.2 a), issXR A.keyRO.ctx A.keyRO.tInit z.1.1.2 (toSp z.2 a))))
            (A.mA k c v b₁ z a u).1.2 z.1.2.1 (toSp z.2 a))))
        (A.mA k c v b₁ z a u).2.2 z.1.2.2 (toSp z.2 a') =
      spXR A.keyRO.pk A.keyRO.ctx
        (some (tau2R A.keyRO (A.mA k c v b₁ z a u) b₁ b₂
          (issXR A.keyRO.ctx A.keyRO.tInit z.1.1.1 (toSp z.2 a), issXR A.keyRO.ctx A.keyRO.tInit z.1.1.2 (toSp z.2 a))
          (spXR A.keyRO.pk A.keyRO.ctx
            (some (tau1R A.keyRO (A.mA k c v b₁ z a u) b₁
              (issXR A.keyRO.ctx A.keyRO.tInit z.1.1.1 (toSp z.2 a), issXR A.keyRO.ctx A.keyRO.tInit z.1.1.2 (toSp z.2 a))))
            (A.mA k c v b₁ z a u).1.2 z.1.2.1 (toSp z.2 a))))
        (A.mA k c v b₁ z a u).2.2 z.1.2.2 (toSp z.2 a) := hO2.2
  have eY : A.yA k c v b₁ b₂ z a' u' = A.yA k c v b₁ b₂ z a u := by
    unfold yA
    rw [emA, roundsOf_eq_W, roundsOf_eq_W, eI0, eI1, eO1, eO2]
  -- the other pairs' rounds
  have eS2 : ∀ j : {j : Fin N // j ≠ k},
      spXR (R := Rw) A.keyRO.pk A.keyRO.ctx
          (some (tau2R A.keyRO (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j) (v j).1 (v j).2
            (A.riJ k c (toSp z.2 u) j) (A.o1J k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j)))
          (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j).2.2 (c j).2.2 (toSp z.2 u') =
        spXR A.keyRO.pk A.keyRO.ctx
          (some (tau2R A.keyRO (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j) (v j).1 (v j).2
            (A.riJ k c (toSp z.2 u) j) (A.o1J k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j)))
          (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j).2.2 (c j).2.2 (toSp z.2 u) ∧
      rdSpR A.keyRO.pk A.keyRO.ctx
          (some (tau2R A.keyRO (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j) (v j).1 (v j).2
            (A.riJ k c (toSp z.2 u) j) (A.o1J k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j)))
          (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j).2.2 (c j).2.2 z.2 u' =
        rdSpR A.keyRO.pk A.keyRO.ctx
          (some (tau2R A.keyRO (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j) (v j).1 (v j).2
            (A.riJ k c (toSp z.2 u) j) (A.o1J k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j)))
          (A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j).2.2 (c j).2.2 z.2 u := fun j => by
    have h := rdSpR_cons A.keyRO.pk A.keyRO.ctx _ _ _ z.2 u u' (agR_right (agR_right (agR_at hB j)))
    exact ⟨h.2, h.1⟩
  have eHY : A.hopY k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u') =
      A.hopY k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) := by
    unfold hopY
    rw [eTR, eRQ]
    refine congrArg (joinK k _) (funext fun j => ?_)
    have e1 := (eS1 j).1
    have e2 := (eS2 j).1
    unfold mJ riJ at e1
    unfold o1J at e2
    unfold mJ riJ at e2
    rw [roundsOf_eq_W, roundsOf_eq_W, (eX j).1, (eX j).2.1, e1, e2]
  have emJ : ∀ j, A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u') j =
      A.mJ k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j := fun j => by
    unfold mJ; rw [eTR, eRQ]
  have eo1J : ∀ j, A.o1J k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u') j =
      A.o1J k c v (A.trA z a) (A.yA k c v b₁ b₂ z a u) (toSp z.2 u) j := fun j => by
    unfold o1J; rw [emJ, eRJ]; exact (eS1 j).1
  have eO1A : A.o1A k c v b₁ z a' u' = A.o1A k c v b₁ z a u := by
    unfold o1A; rw [emA, eRi]; exact hO1.2
  refine ⟨?_, ?_, ?_⟩
  · unfold tauR TRu
    rw [etr, eY, eTR, eHY]
  · unfold RAR
    rw [r0, r1, emA, eRi, eO1A, hO1.1, hO2.1]
  · unfold RBR
    rw [etr, eY]
    unfold RBf
    refine congrArg rdUnionI (funext fun j => ?_)
    rw [(eX j).2.2.1, (eX j).2.2.2, emJ j, eRJ j, eo1J j, (eS1 j).2, (eS2 j).2]

end AdversaryP

end Step

/-! ## The reduction's budgets -/

section Budgets

variable {N : ℕ}

open VoleMole.Privacy.Moussaka (sreads_fix)

namespace AdversaryP

variable (A : AdversaryP Rw N) (k : Fin N) (c : {j : Fin N // j ≠ k} → PT)
  (v : {j : Fin N // j ≠ k} → Bool × Bool)

lemma hopS_msg₁ (u : T5) (tr : IssTr ZL) (sl : SlicesR) (s : ShR Rw) :
    (A.hopS k c v u).msg₁ tr sl s =
      (fun W => ((A.respondIss (A.trW k tr W) k false, A.respondIss (A.trW k tr W) k true),
        A.d₁ (A.trW k tr W) k)) (A.issFam k c (toSp s.1 u)) := by
  simp only [AdversaryRA.msg₁, hopS, hopG, hopTR_eq]

lemma hopS_msg₂ (u : T5) (tr : IssTr ZL) (rq : SReq) (sl : SlicesR) (s : ShR Rw) :
    (A.hopS k c v u).msg₂ tr rq sl s =
      A.msg₂W k tr rq (A.issFam k c (toSp s.1 u)) (A.sp1Fam k c v tr (A.issFam k c (toSp s.1 u)) (toSp s.1 u)) := by
  simp only [AdversaryRA.msg₂, hopS, hopG, hopQ, hopTR_eq, hopRQ_eq, msg₂W]

/-- The other pairs' issuances on the private pair read only `H₂³`. -/
lemma issFam_fix_sreads (u : T5) :
    SReads pI (fun t : Tb Rw pI => A.issFam k c (toSp t.2.1 u)) 0
      (Fintype.card {j : Fin N // j ≠ k} * (nGrind + nGrind)) 0 0 :=
  sreads_fix (A.issFam_sreads k c) u.1 u.2

lemma sp1Fam_fix_sreads (u : T5) (tr : IssTr ZL) (W : {j : Fin N // j ≠ k} → IssRes × IssRes) :
    SReads pI (fun t : Tb Rw pI => A.sp1Fam k c v tr W (toSp t.2.1 u)) 0
      (Fintype.card {j : Fin N // j ≠ k} * nGrind) 0 0 :=
  sreads_fix (A.sp1Fam_sreads k c v tr W) u.1 u.2

lemma hopS_stage1 (u : T5) (tr : IssTr ZL) (σ : Tb Rw pI → SlicesR) :
    SReads pI (fun t : Tb Rw pI => (A.hopS k c v u).msg₁ tr (σ t) t.2) 0
      (3 * (Fintype.card {j : Fin N // j ≠ k} * nGrind)) 0 0 := by
  have h := (A.issFam_fix_sreads k c u).map fun W =>
    (((A.respondIss (A.trW k tr W) k false, A.respondIss (A.trW k tr W) k true),
      A.d₁ (A.trW k tr W) k) : M₁)
  refine ((congrArg (fun F => SReads pI F _ _ _ _) (funext fun t => ?_)).mp h).mono le_rfl
    (by rw [Nat.mul_add]; omega) le_rfl le_rfl
  exact (A.hopS_msg₁ k c v u tr (σ t) t.2).symm

lemma hopS_stage2 (u : T5) (tr : IssTr ZL) (rq : SReq) (σ : Tb Rw pI → SlicesR) :
    SReads pI (fun t : Tb Rw pI => (A.hopS k c v u).msg₂ tr rq (σ t) t.2) 0
      (3 * (Fintype.card {j : Fin N // j ≠ k} * nGrind)) 0 0 := by
  have h := (A.issFam_fix_sreads k c u).bind (g := fun W (t : Tb Rw pI) =>
      A.msg₂W k tr rq W (A.sp1Fam k c v tr W (toSp t.2.1 u)))
    fun W => (A.sp1Fam_fix_sreads k c v u tr W).map fun S => A.msg₂W k tr rq W S
  refine ((congrArg (fun F => SReads pI F _ _ _ _) (funext fun t => ?_)).mp h).mono (by simp)
    (by rw [Nat.mul_add]; omega) (by simp) (by simp)
  exact (A.hopS_msg₂ k c v u tr rq (σ t) t.2).symm

/-- **The reduction's interaction reads `H₂³` only.** -/
theorem hopS_iBudget (u : T5) :
    (A.hopS k c v u).IBudget 0 (3 * (Fintype.card {j : Fin N // j ≠ k} * nGrind)) 0 0 where
  a0 tr g₁ g₂ g₃ := A.hopS_stage1 k c v u tr fun t => ((t.1, g₁), (g₂, g₃))
  a1 tr g₀ g₂ g₃ := A.hopS_stage1 k c v u tr fun t => ((g₀, t.1), (g₂, g₃))
  a2 tr g₀ g₁ g₃ := A.hopS_stage1 k c v u tr fun t => ((g₀, g₁), (t.1, g₃))
  a3 tr g₀ g₁ g₂ := A.hopS_stage1 k c v u tr fun t => ((g₀, g₁), (g₂, t.1))
  b0 tr rq g₁ g₂ g₃ := A.hopS_stage2 k c v u tr rq fun t => ((t.1, g₁), (g₂, g₃))
  b1 tr rq g₀ g₂ g₃ := A.hopS_stage2 k c v u tr rq fun t => ((g₀, t.1), (g₂, g₃))
  b2 tr rq g₀ g₁ g₃ := A.hopS_stage2 k c v u tr rq fun t => ((g₀, g₁), (t.1, g₃))
  b3 tr rq g₀ g₁ g₂ := A.hopS_stage2 k c v u tr rq fun t => ((g₀, g₁), (g₂, t.1))

/-- **The reduction's guess has the Issuer's budget.** -/
theorem hopS_gBudget {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) (u : T5) :
    (A.hopS k c v u).GBudget q3 q5 qE := fun mm => by
  classical
  let S : {j : Fin N // j ≠ k} → SlicesR := fun j => slOfR (c j)
  let φ : IssTr ZL → Rounds ZL → ShR Rw → ShR Rw := fun tr y s =>
    toSp s.1 (mixR (A.RBf k c v tr y s.1 u) u (s.2.1, s.2.2))
  have hk : ∀ sl : SlicesR, joinK k sl S k = sl := fun sl => joinK_self _ _ _
  refine ⟨fun tr y g₁ g₂ g₃ s => ?_, fun tr y g₀ g₂ g₃ s => ?_, fun tr y g₀ g₁ g₃ s => ?_,
    fun tr y g₀ g₁ g₂ s => ?_, fun tr y sl => ?_, fun tr y sl => ?_⟩
  · have e : (fun g => ((A.hopS k c v u).fixR mm).guess tr y ((g, g₁), (g₂, g₃)) s) = fun g =>
        A.guess (A.hopTR k c tr (toSp s.1 u)) (A.hopY k c v tr y (toSp s.1 u))
          (Function.update (joinK k ((g₁, g₁), (g₂, g₃)) S) k
            ((g, (joinK k ((g₁, g₁), (g₂, g₃)) S k).1.2), (joinK k ((g₁, g₁), (g₂, g₃)) S k).2)) (φ tr y s) := by
      funext g
      rw [hk, ← joinK_update]
      rfl
    rw [e]; exact hA.h30 _ _ _ _ k
  · have e : (fun g => ((A.hopS k c v u).fixR mm).guess tr y ((g₀, g), (g₂, g₃)) s) = fun g =>
        A.guess (A.hopTR k c tr (toSp s.1 u)) (A.hopY k c v tr y (toSp s.1 u))
          (Function.update (joinK k ((g₀, g₀), (g₂, g₃)) S) k
            (((joinK k ((g₀, g₀), (g₂, g₃)) S k).1.1, g), (joinK k ((g₀, g₀), (g₂, g₃)) S k).2)) (φ tr y s) := by
      funext g
      rw [hk, ← joinK_update]
      rfl
    rw [e]; exact hA.h31 _ _ _ _ k
  · have e : (fun g => ((A.hopS k c v u).fixR mm).guess tr y ((g₀, g₁), (g, g₃)) s) = fun g =>
        A.guess (A.hopTR k c tr (toSp s.1 u)) (A.hopY k c v tr y (toSp s.1 u))
          (Function.update (joinK k ((g₀, g₁), (g₃, g₃)) S) k
            ((joinK k ((g₀, g₁), (g₃, g₃)) S k).1, (g, (joinK k ((g₀, g₁), (g₃, g₃)) S k).2.2))) (φ tr y s) := by
      funext g
      rw [hk, ← joinK_update]
      rfl
    rw [e]; exact hA.h32 _ _ _ _ k
  · have e : (fun g => ((A.hopS k c v u).fixR mm).guess tr y ((g₀, g₁), (g₂, g)) s) = fun g =>
        A.guess (A.hopTR k c tr (toSp s.1 u)) (A.hopY k c v tr y (toSp s.1 u))
          (Function.update (joinK k ((g₀, g₁), (g₂, g₂)) S) k
            ((joinK k ((g₀, g₁), (g₂, g₂)) S k).1, ((joinK k ((g₀, g₁), (g₂, g₂)) S k).2.1, g))) (φ tr y s) := by
      funext g
      rw [hk, ← joinK_update]
      rfl
    rw [e]; exact hA.h33 _ _ _ _ k
  · choose K hK hf using fun (T : Fin N → IssTr ZL) (Y : Fin N → Rounds ZL) =>
      hA.h5 T Y (joinK k sl S)
    refine ⟨fun s => K (A.hopTR k c tr (toSp s.1 u)) (A.hopY k c v tr y (toSp s.1 u)) (φ tr y s),
      fun s => hK _ _ _, fun s G5 hs => ?_⟩
    have hp : φ tr y (s.1, G5, s.2.2) =
        ((φ tr y s).1, (mixR (A.RBf k c v tr y s.1 u) u (G5, s.2.2)).1, (φ tr y s).2.2) := rfl
    change A.guess (A.hopTR k c tr (toSp s.1 u)) (A.hopY k c v tr y (toSp s.1 u)) (joinK k sl S)
        (φ tr y (s.1, G5, s.2.2)) =
      A.guess (A.hopTR k c tr (toSp s.1 u)) (A.hopY k c v tr y (toSp s.1 u)) (joinK k sl S) (φ tr y s)
    rw [hp]
    refine hf _ _ (φ tr y s) _ fun k' hk' => ?_
    show (if k' ∈ (A.RBf k c v tr y s.1 u).1 then u.1 k' else s.2.1 k') =
      (if k' ∈ (A.RBf k c v tr y s.1 u).1 then u.1 k' else G5 k')
    rw [hs k' hk']
  · choose K hK hf using fun (T : Fin N → IssTr ZL) (Y : Fin N → Rounds ZL) =>
      hA.hE T Y (joinK k sl S)
    refine ⟨fun s => K (A.hopTR k c tr (toSp s.1 u)) (A.hopY k c v tr y (toSp s.1 u)) (φ tr y s),
      fun s => hK _ _ _, fun s E hs => ?_⟩
    have hp : φ tr y (s.1, s.2.1, E) =
        ((φ tr y s).1, (φ tr y s).2.1, (mixR (A.RBf k c v tr y s.1 u) u (s.2.1, E)).2) := rfl
    change A.guess (A.hopTR k c tr (toSp s.1 u)) (A.hopY k c v tr y (toSp s.1 u)) (joinK k sl S)
        (φ tr y (s.1, s.2.1, E)) =
      A.guess (A.hopTR k c tr (toSp s.1 u)) (A.hopY k c v tr y (toSp s.1 u)) (joinK k sl S) (φ tr y s)
    rw [hp]
    refine hf _ _ (φ tr y s) _ fun k' hk' => funext fun z => ?_
    show (if (A.RBf k c v tr y s.1 u).2 k' z then u.2 k' z else s.2.2 k' z) =
      (if (A.RBf k c v tr y s.1 u).2 k' z then u.2 k' z else E k' z)
    rw [hs k' hk']

end AdversaryP

end Budgets

/-! ## The step and the hybrid -/

section Main

variable {N : ℕ}

open VoleMole.Privacy.PomFRIT (abs_pr_prod_sub_le_avg')

/-- **The bad event of the step**, in the split world: pair `k`'s points on the game's pair meet
the other pairs' points on the private pair. -/
def badR (A : AdversaryP Rw N) (k : Fin N) (c : {j : Fin N // j ≠ k} → PT)
    (v : {j : Fin N // j ≠ k} → Bool × Bool) (b₁ b₂ : Bool) (z : ((PT × Tab2G pI) × T5) × T5) : Prop :=
  ¬ Disj (A.RAR k c v b₁ b₂ z.1.1 z.1.2 z.2) (A.RBR k c v b₁ b₂ z.1.1 z.1.2 z.2)

/-- The game's coins split into the pair's tapes and `H₂³`, and the `(H₅, cipher)` pair. -/
def splitTR : PT × ShR Rw ≃ (PT × Tab2G pI) × T5 where
  toFun z := ((z.1, z.2.1), z.2.2)
  invFun w := (w.1.1, toSp w.1.2 w.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The split world's coins regrouped: the private pair first. -/
def regroupTR : ((PT × Tab2G pI) × T5) × T5 ≃ T5 × (PT × ShR Rw) where
  toFun z := (z.2, (z.1.1.1, toSp z.1.1.2 z.1.2))
  invFun w := (((w.2.1, w.2.2.1), (w.2.2.2.1, w.2.2.2.2)), w.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **One world of the step**: the hop's game is the reduction's game averaged over the private
pair, up to the bad event (`pr_split_le`). -/
theorem hop_close_hopS (A : AdversaryP Rw N) (k : Fin N) (c : {j : Fin N // j ≠ k} → PT)
    (v : {j : Fin N // j ≠ k} → Bool × Bool) (b₁ b₂ : Bool) :
    |pr (PT × ShR Rw) (realGameRA (A.hop k c v) leanPIR leanPSR b₁ b₂) -
        pr (T5 × (PT × ShR Rw)) (fun w => realGameRA (A.hopS k c v w.1) leanPIR leanPSR b₁ b₂ w.2)| ≤
      pr (((PT × Tab2G pI) × T5) × T5) (badR A k c v b₁ b₂) := by
  have h := pr_split_le (C := PT × Tab2G pI) (T := T5) mixR AgR Disj agR_mixR mixR_inv
    (fun r r' a b h => agR_mixR_of_disj h a b) (A.tauR k c v b₁ b₂) (A.RAR k c v b₁ b₂)
    (A.RBR k c v b₁ b₂) (fun z a u a' u' hA hB => A.tauR_cons k c v b₁ b₂ z a u a' u' hA hB) (A.guessR k c)
  have h1 : pr (PT × ShR Rw) (realGameRA (A.hop k c v) leanPIR leanPSR b₁ b₂) =
      pr ((PT × Tab2G pI) × T5) (fun z => A.guessR k c z.1 (A.tauR k c v b₁ b₂ z.1 z.2 z.2) z.2) := by
    rw [← pr_equiv splitTR.symm]
    exact pr_congr fun w => A.realGameRA_hop_iff k c v b₁ b₂ w.1 w.2
  have h2 : pr (T5 × (PT × ShR Rw)) (fun w => realGameRA (A.hopS k c v w.1) leanPIR leanPSR b₁ b₂ w.2) =
      pr (((PT × Tab2G pI) × T5) × T5) (fun z => A.guessR k c z.1.1 (A.tauR k c v b₁ b₂ z.1.1 z.1.2 z.2)
        (mixR (A.RBR k c v b₁ b₂ z.1.1 z.1.2 z.2) z.2 z.1.2)) := by
    rw [← pr_equiv regroupTR]
    exact pr_congr fun z => A.realGameRA_hopS_iff k c v b₁ b₂ z.1.1 z.1.2 z.2
  rw [h1, h2]
  exact h

/-- **The one-pair error with the other pairs on private tables**: `unlinkabilityRA_lean_num`
with the Issuer's own guess budget and an interaction that reads only `H₂³`. -/
noncomputable def εPair0R (q3 q5 qE m : ℕ) (εhide : ℝ) : ℝ :=
  4 * εRO (2 * 0 + q3) (q5 + 2 * 0 + 1872) (qE + 2 * 0 + 13821) +
    2 * εAd 9 (0 + q3) (q5 + 0 + 1248) (qE + 0 + 13821) 0 (3 * (m * nGrind)) (0 + 624) (0 + 9214) +
    2 * εAd 9 q3 (q5 + 936) (qE + 13821) (2 * 0) (2 * (3 * (m * nGrind))) (2 * 0 + 1560) (2 * 0 + 23035) +
    6 * ((0 : ℕ) / 2 ^ 128) + 4 * (1 / 2 ^ 113 + εROP 0 312 4607 (2 * 0 + 1560) (2 * 0 + 23035)) +
    6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide

/-- **The step bound, for fixed tapes of the other pairs.** -/
theorem hop_step (A : AdversaryP Rw N) {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE) (k : Fin N)
    (c : {j : Fin N // j ≠ k} → PT) (v : {j : Fin N // j ≠ k} → Bool × Bool)
    (hhide : ∀ u b₁ b₂ K, hidingAdv (A.hopS k c v u).ctx
      (reductionRA (A.hopS k c v u) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr (PT × ShR Rw) (realGameRA (A.hop k c v) leanPIR leanPSR b₁ b₂) -
        pr (PT × ShR Rw) (realGameRA (A.hop k c v) leanPIR leanPSR b₁' b₂')| ≤
      εPair0R q3 q5 qE (Fintype.card {j : Fin N // j ≠ k}) εhide +
        pr (((PT × Tab2G pI) × T5) × T5) (badR A k c v b₁ b₂) +
        pr (((PT × Tab2G pI) × T5) × T5) (badR A k c v b₁' b₂') := by
  have h0 := hop_close_hopS A k c v b₁ b₂
  have h1 := hop_close_hopS A k c v b₁' b₂'
  have hm : |pr (T5 × (PT × ShR Rw)) (fun w => realGameRA (A.hopS k c v w.1) leanPIR leanPSR b₁ b₂ w.2) -
      pr (T5 × (PT × ShR Rw)) (fun w => realGameRA (A.hopS k c v w.1) leanPIR leanPSR b₁' b₂' w.2)| ≤
      εPair0R q3 q5 qE (Fintype.card {j : Fin N // j ≠ k}) εhide :=
    abs_pr_prod_sub_le _ _ fun u => by
      have h := unlinkabilityRA_lean_num (A.hopS k c v u) (A.hopS_gBudget k c v hA u)
        (A.hopS_iBudget k c v u) (hhide u) b₁ b₂ b₁' b₂'
      unfold εPair0R
      exact h
  have := abs_sub_le (pr (PT × ShR Rw) (realGameRA (A.hop k c v) leanPIR leanPSR b₁ b₂))
    (pr (T5 × (PT × ShR Rw)) (fun w => realGameRA (A.hopS k c v w.1) leanPIR leanPSR b₁ b₂ w.2))
    (pr (PT × ShR Rw) (realGameRA (A.hop k c v) leanPIR leanPSR b₁' b₂'))
  have := abs_sub_le (pr (T5 × (PT × ShR Rw)) (fun w => realGameRA (A.hopS k c v w.1) leanPIR leanPSR b₁ b₂ w.2))
    (pr (T5 × (PT × ShR Rw)) (fun w => realGameRA (A.hopS k c v w.1) leanPIR leanPSR b₁' b₂' w.2))
    (pr (PT × ShR Rw) (realGameRA (A.hop k c v) leanPIR leanPSR b₁' b₂'))
  rw [abs_sub_comm] at h1
  linarith

/-- **The hybrid over the pairs, with the steps averaged over the other pairs' tapes.** -/
lemma realGameP_hybrid_avg {R : Type} [Fintype R] [Nonempty R] [CipherRow R] (A : AdversaryP R N) (ε : ℝ)
    (h : ∀ (k : Fin N) (v : {j : Fin N // j ≠ k} → Bool × Bool) (b₁ b₂ b₁' b₂' : Bool),
      |pr (({j : Fin N // j ≠ k} → PT) × (PT × ShR R))
          (fun q => realGameRA (A.hop k q.1 v) leanPIR leanPSR b₁ b₂ q.2) -
        pr (({j : Fin N // j ≠ k} → PT) × (PT × ShR R))
          (fun q => realGameRA (A.hop k q.1 v) leanPIR leanPSR b₁' b₂' q.2)| ≤ ε)
    (w w' : Fin N → Bool × Bool) :
    |pr ((Fin N → PT) × ShR R) (realGameP A w) - pr ((Fin N → PT) × ShR R) (realGameP A w')| ≤
      N * ε := by
  refine abs_sub_le_mul_of_worlds (fun u => pr ((Fin N → PT) × ShR R) (realGameP A u)) ε
    (fun k u u' hu => ?_) w w'
  have hv : (fun j : {j : Fin N // j ≠ k} => u j.1) = fun j => u' j.1 :=
    funext fun j => hu j.1 j.2
  show |pr _ (realGameP A u) - pr _ (realGameP A u')| ≤ ε
  rw [pr_realGameP_eq A k u, pr_realGameP_eq A k u', ← hv]
  exact h k _ _ _ _ _

/-- **Ratatouille unlinkability with `N` challenge pairs, linear in `N` up to the bad events**:
if in every step of the hybrid the bad event has probability at most `β` in each world (averaged
over the other pairs' tapes), any two worlds differ by at most `N·(εPair0R(q₃, q₅, q_E, N − 1) +
2β)`. -/
theorem unlinkabilityP_lin (A : AdversaryP Rw N) {q3 q5 qE : ℕ} {εhide β : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k c v u b₁ b₂ K, hidingAdv (A.hopS k c v u).ctx
      (reductionRA (A.hopS k c v u) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hβ : ∀ k v b₁ b₂, pr (({j : Fin N // j ≠ k} → PT) × (((PT × Tab2G pI) × T5) × T5))
      (fun z => badR A k z.1 v b₁ b₂ z.2) ≤ β)
    (w w' : Fin N → Bool × Bool) :
    |pr ((Fin N → PT) × ShR Rw) (realGameP A w) - pr ((Fin N → PT) × ShR Rw) (realGameP A w')| ≤
      N * (εPair0R q3 q5 qE (N - 1) εhide + 2 * β) := by
  refine realGameP_hybrid_avg A _ (fun k v b₁ b₂ b₁' b₂' => ?_) w w'
  have h := abs_pr_prod_sub_le_avg' (α := {j : Fin N // j ≠ k} → PT) (β := PT × ShR Rw)
    (β' := PT × ShR Rw) (fun q => realGameRA (A.hop k q.1 v) leanPIR leanPSR b₁ b₂ q.2)
    (fun q => realGameRA (A.hop k q.1 v) leanPIR leanPSR b₁' b₂' q.2)
    (fun c => εPair0R q3 q5 qE (Fintype.card {j : Fin N // j ≠ k}) εhide +
      pr (((PT × Tab2G pI) × T5) × T5) (badR A k c v b₁ b₂) +
      pr (((PT × Tab2G pI) × T5) × T5) (badR A k c v b₁' b₂'))
    fun c => hop_step A hA k c v (hhide k c v) b₁ b₂ b₁' b₂'
  refine h.trans ?_
  have hc : (0 : ℝ) < Fintype.card ({j : Fin N // j ≠ k} → PT) := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, add_div, add_div, mul_div_cancel_left₀ _ hc.ne',
    ← pr_prod (α := {j : Fin N // j ≠ k} → PT) (β := ((PT × Tab2G pI) × T5) × T5)
      (fun z => badR A k z.1 v b₁ b₂ z.2),
    ← pr_prod (α := {j : Fin N // j ≠ k} → PT) (β := ((PT × Tab2G pI) × T5) × T5)
      (fun z => badR A k z.1 v b₁' b₂' z.2), card_ne]
  have h0 := hβ k v b₁ b₂
  have h1 := hβ k v b₁' b₂'
  linarith

/-- **The one-pair error in numbers**: `≤ 2·2⁻¹⁰² + m·2⁻¹²⁸ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ +
2·εhide`; the other pairs enter only through their proofs' `H₂³` grinding keys
(`36m·2³²·2⁻¹⁰²⁴`, rounded up to `m·2⁻¹²⁸`). -/
theorem εPair0R_le (q3 q5 qE m : ℕ) (εhide : ℝ) :
    εPair0R q3 q5 qE m εhide ≤
      2 / 2 ^ 102 + m / 2 ^ 128 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 + 2 * εhide := by
  have hn := noHitProb_le_128
  have hn0 : 0 ≤ noHitProb := pr_nonneg _
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have e1024 : (2 : ℝ) ^ 1024 = 2 ^ 128 * 2 ^ 896 := by rw [← pow_add]
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have hG : 36 * ((m : ℝ) * (nGrind : ℝ) / 2 ^ 1024) ≤ m / 2 ^ 128 := by
    rw [show (nGrind : ℝ) = 2 ^ 32 by simp only [nGrind, Nat.cast_pow, Nat.cast_ofNat], e1024,
      mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have hb' : (36 : ℝ) * 2 ^ 32 ≤ 2 ^ 896 := by
      calc (36 : ℝ) * 2 ^ 32 ≤ 2 ^ 6 * 2 ^ 32 := by norm_num
        _ = 2 ^ 38 := by rw [← pow_add]
        _ ≤ 2 ^ 896 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    calc 36 * ((m : ℝ) * 2 ^ 32) * 2 ^ 128 = ((m : ℝ) * 2 ^ 128) * (36 * 2 ^ 32) := by ring
      _ ≤ ((m : ℝ) * 2 ^ 128) * 2 ^ 896 := mul_le_mul_of_nonneg_left hb' (mul_nonneg hm hp.le)
      _ = (m : ℝ) * (2 ^ 128 * 2 ^ 896) := mul_assoc _ _ _
  have hK : (12 : ℝ) / 2 ^ 1024 ≤ 1 / 2 ^ 128 := by
    rw [e1024, div_le_div_iff₀ (by positivity) (by positivity)]
    have hb : (2 : ℝ) ^ 32 ≤ 2 ^ 896 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h16 : (12 : ℝ) ≤ 2 ^ 32 := by norm_num
    calc (12 : ℝ) * 2 ^ 128 ≤ 2 ^ 896 * 2 ^ 128 :=
          mul_le_mul_of_nonneg_right (h16.trans hb) hp.le
      _ = 1 * (2 ^ 128 * 2 ^ 896) := by rw [one_mul, mul_comm]
  have hκ : (0 : ℝ) < 2 ^ 1024 := by positivity
  unfold εPair0R εAd h23Term
  generalize (2 : ℝ) ^ 1024 = κ at hK hG hκ ⊢
  have e : ∀ x : ℝ, x / 2 ^ 102 = x * 67108864 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have hG0 : (0 : ℝ) ≤ (m : ℝ) * (nGrind : ℝ) / κ := div_nonneg (mul_nonneg hm (Nat.cast_nonneg _)) hκ.le
  split_ifs <;>
  · unfold εROP εRO
    push_cast
    rw [e]
    have : (3 * ((m : ℝ) * (nGrind : ℝ))) / κ = 3 * ((m : ℝ) * (nGrind : ℝ) / κ) := by ring
    have : (2 * (3 * ((m : ℝ) * (nGrind : ℝ)))) / κ = 6 * ((m : ℝ) * (nGrind : ℝ) / κ) := by ring
    linarith

/-- **`N` pairs in numbers**: `≤ N·(2·2⁻¹⁰² + (N − 1)·2⁻¹²⁸ + 8·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸ +
2·εhide + 2β)`. -/
theorem unlinkabilityP_lin_le (A : AdversaryP Rw N) {q3 q5 qE : ℕ} {εhide β : ℝ} (hA : A.Budget q3 q5 qE)
    (hhide : ∀ k c v u b₁ b₂ K, hidingAdv (A.hopS k c v u).ctx
      (reductionRA (A.hopS k c v u) leanSimIR leanSimSR leanProgIR leanProgSR b₁ b₂ K) ≤ εhide)
    (hβ : ∀ k v b₁ b₂, pr (({j : Fin N // j ≠ k} → PT) × (((PT × Tab2G pI) × T5) × T5))
      (fun z => badR A k z.1 v b₁ b₂ z.2) ≤ β)
    (w w' : Fin N → Bool × Bool) :
    |pr ((Fin N → PT) × ShR Rw) (realGameP A w) - pr ((Fin N → PT) × ShR Rw) (realGameP A w')| ≤
      N * (2 / 2 ^ 102 + (N - 1 : ℕ) / 2 ^ 128 + 8 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 +
        2 * εhide + 2 * β) := by
  have h := unlinkabilityP_lin A hA hhide hβ w w'
  have h2 := εPair0R_le q3 q5 qE (N - 1) εhide
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hN)
  linarith

end Main

end VoleMole.Privacy.Ratatouille
