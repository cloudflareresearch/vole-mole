import VoleMole.Privacy.RatatouilleMany
import VoleMole.Privacy.MoussakaLin

/-!
# Ratatouille with `N` challenge pairs: the other pairs on private tables

PLACEHOLDER
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

end VoleMole.Privacy.Ratatouille
