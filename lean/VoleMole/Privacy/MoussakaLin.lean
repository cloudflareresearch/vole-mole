import VoleMole.Privacy.MoussakaMany
import VoleMole.ZK.ReadsPointRO
import VoleMole.Privacy.Split

/-!
# Moussaka with many Clients: the further Clients on private tables

PLACEHOLDER
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.Privacy.PomFRIT (T5 RdS AgR mixR Disj agR_mixR mixR_inv agR_mixR_of_disj)

attribute [local irreducible] com UOVKey.eval

/-! ## Read sets -/

section ReadSets

/-- The empty read set. -/
def rdNone : RdS := (∅, fun _ _ => False)

/-- The union of two read sets. -/
def rdUnion (r r' : RdS) : RdS := (r.1 ∪ r'.1, fun k z => r.2 k z ∨ r'.2 k z)

/-- The union of a family of read sets. -/
noncomputable def rdUnionI {ι : Type} [Fintype ι] (r : ι → RdS) : RdS :=
  (univ.biUnion fun j => (r j).1, fun k z => ∃ j, (r j).2 k z)

lemma agR_rdNone (a b : T5) : AgR rdNone a b := ⟨fun _ h => absurd h (Finset.notMem_empty _), fun _ _ h => h.elim⟩

lemma agR_left {r r' : RdS} {a b : T5} (h : AgR (rdUnion r r') a b) : AgR r a b :=
  ⟨fun k hk => h.1 k (mem_union_left _ hk), fun k z hk => h.2 k z (Or.inl hk)⟩

lemma agR_right {r r' : RdS} {a b : T5} (h : AgR (rdUnion r r') a b) : AgR r' a b :=
  ⟨fun k hk => h.1 k (mem_union_right _ hk), fun k z hk => h.2 k z (Or.inr hk)⟩

lemma agR_at {ι : Type} [Fintype ι] {r : ι → RdS} {a b : T5} (h : AgR (rdUnionI r) a b) (j : ι) :
    AgR (r j) a b :=
  ⟨fun k hk => h.1 k (mem_biUnion.2 ⟨j, mem_univ _, hk⟩), fun k z hk => h.2 k z ⟨j, hk⟩⟩

end ReadSets

/-! ## The Lean provers read points -/

section Provers

/-- **The issuance prover's point read set.** -/
noncomputable def rdPI (w : Bytes) (x : IssueInstance) (rho : Bytes) (g3 : Tab3) (g : Tab2G pI)
    (t : T5) : RdS :=
  rdRO Hashes.shake (stI x) (toBA w) (toBA rho) g3 g t

/-- **The redemption prover's point read set.** -/
noncomputable def rdPR (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g3 : Tab3) (g : Tab2G pI)
    (t : T5) : RdS :=
  rdRO Hashes.shake (stR x) (toBA w) (toBA rho) g3 g t

theorem rdPI_cons (w : Bytes) (x : IssueInstance) (rho : Bytes) (g3 : Tab3) (g : Tab2G pI)
    (t t' : T5) (h : AgR (rdPI w x rho g3 g t) t t') :
    rdPI w x rho g3 g t' = rdPI w x rho g3 g t ∧
      leanPI (R := Blk → Blk) w x rho g3 (toSp g t') = leanPI (R := Blk → Blk) w x rho g3 (toSp g t) := by
  obtain ⟨e1, e2⟩ := rdRO_cons (st := stI x) (w := toBA w) hashesWF_shake (toBA rho) g3 g t t' h
  refine ⟨e1, ?_⟩
  unfold leanPI
  exact congrArg (fun o => toL (o.toOption.getD .empty)) e2

theorem rdPR_cons (w : Bytes) (x : RedeemInstance) (rho : Bytes) (g3 : Tab3) (g : Tab2G pI)
    (t t' : T5) (h : AgR (rdPR w x rho g3 g t) t t') :
    rdPR w x rho g3 g t' = rdPR w x rho g3 g t ∧
      leanPR (R := Blk → Blk) w x rho g3 (toSp g t') = leanPR (R := Blk → Blk) w x rho g3 (toSp g t) := by
  obtain ⟨e1, e2⟩ := rdRO_cons (st := stR x) (w := toBA w) hashesWF_shake (toBA rho) g3 g t t' h
  refine ⟨e1, ?_⟩
  unfold leanPR
  exact congrArg (fun o => toL (o.toOption.getD .empty)) e2

variable (ci cr : Bytes)

/-- **An issuance request's read set**: its proof's. -/
noncomputable def rdIss (x : TIr) (g : Tab2G pI) (t : T5) : RdS :=
  rdPI (encodeIssueWitness (List.ofFn x.1.1) ci cr (List.ofFn x.1.2))
    ⟨com (List.ofFn x.1.1) ci cr (List.ofFn x.1.2), ci⟩ (List.ofFn x.2.1) x.2.2 g t

theorem rdIss_cons (x : TIr) (g : Tab2G pI) (t t' : T5) (h : AgR (rdIss ci cr x g t) t t') :
    rdIss ci cr x g t' = rdIss ci cr x g t ∧ issX (R := Blk → Blk) ci cr x (toSp g t') = issX ci cr x (toSp g t) := by
  obtain ⟨e1, e2⟩ := rdPI_cons _ _ _ _ g t t' h
  refine ⟨e1, ?_⟩
  unfold issX issueRequestOf nizkAt
  dsimp only
  rw [e2]

/-- **A redemption request's read set**: its proof's, at the witness and instance it would prove
(whether or not the Client's checks pass). -/
noncomputable def rdRedAt (tok : Token) (S : AnchorSet) (i : ℕ) (cd rho : Bytes) (g3 : Tab3)
    (g : Tab2G pI) (t : T5) : RdS :=
  rdPR (encodeRedeemWitness tok.nf ci cr tok.r tok.s i) ⟨S.keys, tok.nf, ci, cr, cd⟩ rho g3 g t

theorem rdRedAt_cons (tok : Token) (S : AnchorSet) (i : ℕ) (cd rho : Bytes) (g3 : Tab3)
    (g : Tab2G pI) (t t' : T5) (h : AgR (rdRedAt ci cr tok S i cd rho g3 g t) t t') :
    rdRedAt ci cr tok S i cd rho g3 g t' = rdRedAt ci cr tok S i cd rho g3 g t ∧
      redeemRequestOf (nizkAt (R := Blk → Blk) leanPR g3 (toSp g t')) tok S i ci cr cd rho =
        redeemRequestOf (nizkAt (R := Blk → Blk) leanPR g3 (toSp g t)) tok S i ci cr cd rho := by
  obtain ⟨e1, e2⟩ := rdPR_cons _ _ _ _ g t t' h
  refine ⟨e1, ?_⟩
  unfold redeemRequestOf nizkAt
  dsimp only
  rw [e2]

/-- **A further Client's redemption's read set** (`redX`): none if its token does not finalize. -/
noncomputable def rdRedX (idx : AnchorSet → UOVKey → ℕ) (pk : UOVKey) (i : PendingToken)
    (resp : Coins uovN) (S : AnchorSet × Bytes) (y : TRr) (g : Tab2G pI) (t : T5) : RdS :=
  match finalizeIssue pk i (List.ofFn resp) with
  | none => rdNone
  | some tok => rdRedAt ci cr tok S.1 (idx S.1 pk) S.2 (List.ofFn y.1) y.2 g t

theorem rdRedX_cons (idx : AnchorSet → UOVKey → ℕ) (pk : UOVKey) (i : PendingToken)
    (resp : Coins uovN) (S : AnchorSet × Bytes) (y : TRr) (g : Tab2G pI) (t t' : T5)
    (h : AgR (rdRedX ci cr idx pk i resp S y g t) t t') :
    rdRedX ci cr idx pk i resp S y g t' = rdRedX ci cr idx pk i resp S y g t ∧
      redX (R := Blk → Blk) ci cr idx pk i resp S y (toSp g t') = redX ci cr idx pk i resp S y (toSp g t) := by
  rcases hf : finalizeIssue pk i (List.ofFn resp) with _ | tok
  · refine ⟨?_, ?_⟩
    · simp only [rdRedX, hf]
    · simp only [redX, hf]
  · have h' : AgR (rdRedAt ci cr tok S.1 (idx S.1 pk) S.2 (List.ofFn y.1) y.2 g t) t t' := by
      simpa only [rdRedX, hf] using h
    obtain ⟨e1, e2⟩ := rdRedAt_cons ci cr tok _ _ _ _ _ g t t' h'
    refine ⟨?_, ?_⟩
    · simp only [rdRedX, hf, e1]
    · simp only [redX, hf, e2]

end Provers

/-! ## The many-Client game as two interleaved readers -/

/-- Function rows. -/
abbrev Rw := Blk → Blk

section Game

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace AdversaryN

variable (A : AdversaryN Rw ι) (idx : AnchorSet → UOVKey → ℕ) (c : ι → XC)

/-- The further Clients' issuance outputs with `H₂³` table `g` and `(H₅, cipher)` pair `u`. -/
noncomputable def issB (g : Tab2G pI) (u : T5) : ι → PendingToken × Bytes :=
  fun j => issX (R := Rw) A.ci A.cr (c j).1 (toSp g u)

/-- Their requests. -/
noncomputable def txB (g : Tab2G pI) (u : T5) : ι → Bytes := fun j => (A.issB c g u j).2

/-- The further Clients' redemptions, from the challenge requests `q₀`, `q₁` and their issuance
outputs `TX`. -/
noncomputable def redB (q₀ q₁ : Bytes) (TX : ι → PendingToken × Bytes) (g : Tab2G pI) (u : T5) :
    ι → Except Error Bytes := fun j =>
  redX (R := Rw) A.ci A.cr idx (A.pkX j) (TX j).1 (A.respondX q₀ q₁ (fun j => (TX j).2) j)
    (A.chooseX q₀ q₁ (fun j => (TX j).2) j) (c j).2 (toSp g u)

/-- **The further Clients' read set**: their issuance and redemption proofs' points. -/
noncomputable def QB (q₀ q₁ : Bytes) (TX : ι → PendingToken × Bytes) (g : Tab2G pI) (u : T5) : RdS :=
  rdUnionI fun j => rdUnion (rdIss A.ci A.cr (c j).1 g u)
    (rdRedX A.ci A.cr idx (A.pkX j) (TX j).1 (A.respondX q₀ q₁ (fun j => (TX j).2) j)
      (A.chooseX q₀ q₁ (fun j => (TX j).2) j) (c j).2 g u)

/-- **The adversary served by further Clients that run on the pair `u`** (with the game's
`H₂³`), its guess looking at the game's tables through `φ`. With `u` the game's own pair and
`φ = id` this is `A.withClients idx c` (`realGameRA_withClients_iff`). -/
noncomputable def redY (u : T5) (φ : Bytes → Bytes → ShM Rw → ShM Rw) : AdversaryRA Rw where
  ctxIss := A.ctxIss
  ctxRed := A.ctxRed
  pk := A.pk
  respond q₀ q₁ i _ v := A.respond q₀ q₁ (A.txB c v.1 u) i
  choose q₀ q₁ side _ v := A.choose q₀ q₁ (A.txB c v.1 u) side
  guess q₀ q₁ y sl v := A.guess q₀ q₁ (A.txB c v.1 u) y (A.redB idx c q₀ q₁ (A.issB c v.1 u) v.1 u) sl
    (fun j => ((c j).1.2.2, (c j).2.2)) (φ q₀ q₁ v)

/-- **The reduction**: the further Clients run on the **private** pair `u` (their issuance in the
interaction, their redemptions in the guess); the guess looks at the game's tables patched with
`u` at the further Clients' points. Its interaction reads only `H₂³` (the further issuance
proofs' grinding). -/
noncomputable def redS (u : T5) : AdversaryRA Rw :=
  A.redY idx c u fun q₀ q₁ v => toSp v.1 (mixR (A.QB idx c q₀ q₁ (A.issB c v.1 u) v.1 u) u (v.2.1, v.2.2))

end AdversaryN

variable (A : AdversaryN Rw ι) (idx : AnchorSet → UOVKey → ℕ) (c : ι → XC) (b : Bool)

/-- The two challenge issuance outputs. -/
noncomputable def chI (x : PT) (g : Tab2G pI) (a : T5) : (PendingToken × Bytes) × (PendingToken × Bytes) :=
  (issX (R := Rw) A.ci A.cr x.1.1 (toSp g a), issX (R := Rw) A.ci A.cr x.1.2 (toSp g a))

/-- The interaction (`Adversary`) at the challenge issuance outputs `i` and the further Clients'
issuance outputs `TX`. -/
def baseOf (i : (PendingToken × Bytes) × (PendingToken × Bytes)) (TX : ι → PendingToken × Bytes) :
    Adversary :=
  ⟨A.ctxIss, A.ctxRed, A.pk,
    fun _ _ c => bif c then A.respond i.1.2 i.2.2 (fun j => (TX j).2) true
      else A.respond i.1.2 i.2.2 (fun j => (TX j).2) false,
    fun _ _ side => bif side then A.choose i.1.2 i.2.2 (fun j => (TX j).2) true
      else A.choose i.1.2 i.2.2 (fun j => (TX j).2) false,
    fun _ _ _ => True⟩

/-- A challenge redemption tape by side. -/
def yOf (x : PT) (side : Bool) : TRr := bif side then x.2.2 else x.2.1

/-- **A challenge redemption** at side `side`. -/
noncomputable def chR (x : PT) (i : (PendingToken × Bytes) × (PendingToken × Bytes))
    (TX : ι → PendingToken × Bytes) (g : Tab2G pI) (a : T5) (side : Bool) : Except Error Bytes :=
  redeemRequestOf (nizkAt (R := Rw) leanPR (yOf x side).2 (toSp g a)) (pt (baseOf A i TX) idx b i.1 i.2 side).tok
    (pt (baseOf A i TX) idx b i.1 i.2 side).anchors (pt (baseOf A i TX) idx b i.1 i.2 side).i A.ci A.cr
    (pt (baseOf A i TX) idx b i.1 i.2 side).cd (List.ofFn (yOf x side).1)

/-- Its read set. -/
noncomputable def rdChR (x : PT) (i : (PendingToken × Bytes) × (PendingToken × Bytes))
    (TX : ι → PendingToken × Bytes) (g : Tab2G pI) (a : T5) (side : Bool) : RdS :=
  rdRedAt A.ci A.cr (pt (baseOf A i TX) idx b i.1 i.2 side).tok (pt (baseOf A i TX) idx b i.1 i.2 side).anchors
    (pt (baseOf A i TX) idx b i.1 i.2 side).i (pt (baseOf A i TX) idx b i.1 i.2 side).cd
    (List.ofFn (yOf x side).1) (yOf x side).2 g a

/-- What the guess receives besides the tables. -/
abbrev OutM (ι : Type) := ((PendingToken × Bytes) × (PendingToken × Bytes)) × (ι → Bytes) ×
  Option (Except Error Bytes × Except Error Bytes) × (ι → Except Error Bytes)

/-- **The joint run**: the challenge sessions on the pair `a`, the further Clients on `u`. -/
noncomputable def tauM (z : PT × Tab2G pI) (a u : T5) : OutM ι :=
  (chI A z.1 z.2 a, A.txB c z.2 u,
    bif allOk (baseOf A (chI A z.1 z.2 a) (A.issB c z.2 u)) idx (chI A z.1 z.2 a).1 (chI A z.1 z.2 a).2 then
      some (chR A idx b z.1 (chI A z.1 z.2 a) (A.issB c z.2 u) z.2 a false,
        chR A idx b z.1 (chI A z.1 z.2 a) (A.issB c z.2 u) z.2 a true) else none,
    A.redB idx c (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (A.issB c z.2 u) z.2 u)

/-- **The challenge sessions' read set** (on `a`). -/
noncomputable def RAM (z : PT × Tab2G pI) (a u : T5) : RdS :=
  rdUnion (rdUnion (rdIss A.ci A.cr z.1.1.1 z.2 a) (rdIss A.ci A.cr z.1.1.2 z.2 a))
    (rdUnion (rdChR A idx b z.1 (chI A z.1 z.2 a) (A.issB c z.2 u) z.2 a false)
      (rdChR A idx b z.1 (chI A z.1 z.2 a) (A.issB c z.2 u) z.2 a true))

/-- **The further Clients' read set** (on `u`). -/
noncomputable def RBM (z : PT × Tab2G pI) (a u : T5) : RdS :=
  A.QB idx c (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (A.issB c z.2 u) z.2 u

/-- The guess on what it receives and the pair `t`. -/
def guessM (z : PT × Tab2G pI) (X : OutM ι) (t : T5) : Prop :=
  A.guess X.1.1.2 X.1.2.2 X.2.1 X.2.2.1 X.2.2.2 (slOf z.1) (fun j => ((c j).1.2.2, (c j).2.2)) (toSp z.2 t)

/-- **The real game is the joint run on one pair.** -/
theorem realGameRA_withClients_iff (z : PT × Tab2G pI) (t : T5) :
    realGameRA (A.withClients idx c) idx leanPI leanPR b (z.1, toSp z.2 t) ↔
      guessM A c z (tauM A idx c b z t t) t :=
  Iff.rfl

/-- **The reduction's game is the split run**, the guess on the patched pair. -/
theorem realGameRA_redS_iff (z : PT × Tab2G pI) (a u : T5) :
    realGameRA (A.redS idx c u) idx leanPI leanPR b (z.1, toSp z.2 a) ↔
      guessM A c z (tauM A idx c b z a u) (mixR (RBM A idx c z a u) u a) :=
  Iff.rfl

/-- **The joint run is consistent**: pairs `a'`, `u'` that agree with `a` on the challenge
sessions' points and with `u` on the further Clients' points give the same run and the same read
sets. -/
theorem tauM_cons (z : PT × Tab2G pI) (a u a' u' : T5) (hA : AgR (RAM A idx c b z a u) a a')
    (hB : AgR (RBM A idx c z a u) u u') :
    tauM A idx c b z a' u' = tauM A idx c b z a u ∧ RAM A idx c b z a' u' = RAM A idx c b z a u ∧
      RBM A idx c z a' u' = RBM A idx c z a u := by
  obtain ⟨r0, i0⟩ := rdIss_cons A.ci A.cr z.1.1.1 z.2 a a' (agR_left (agR_left hA))
  obtain ⟨r1, i1⟩ := rdIss_cons A.ci A.cr z.1.1.2 z.2 a a' (agR_right (agR_left hA))
  have eI : chI A z.1 z.2 a' = chI A z.1 z.2 a := by
    unfold chI; rw [i0, i1]
  have eX : ∀ j, rdIss A.ci A.cr (c j).1 z.2 u' = rdIss A.ci A.cr (c j).1 z.2 u ∧
      issX (R := Rw) A.ci A.cr (c j).1 (toSp z.2 u') = issX A.ci A.cr (c j).1 (toSp z.2 u) :=
    fun j => rdIss_cons _ _ _ _ _ _ (agR_left (agR_at hB j))
  have eTX : A.issB c z.2 u' = A.issB c z.2 u := funext fun j => (eX j).2
  have etx : A.txB c z.2 u' = A.txB c z.2 u := by
    unfold AdversaryN.txB; rw [eTX]
  have hL := rdRedAt_cons A.ci A.cr _ _ _ _ _ _ z.2 a a' (agR_left (agR_right hA))
  have hR := rdRedAt_cons A.ci A.cr _ _ _ _ _ _ z.2 a a' (agR_right (agR_right hA))
  have eL : chR A idx b z.1 (chI A z.1 z.2 a) (A.issB c z.2 u) z.2 a' false =
      chR A idx b z.1 (chI A z.1 z.2 a) (A.issB c z.2 u) z.2 a false := hL.2
  have eR : chR A idx b z.1 (chI A z.1 z.2 a) (A.issB c z.2 u) z.2 a' true =
      chR A idx b z.1 (chI A z.1 z.2 a) (A.issB c z.2 u) z.2 a true := hR.2
  have fL : rdChR A idx b z.1 (chI A z.1 z.2 a) (A.issB c z.2 u) z.2 a' false =
      rdChR A idx b z.1 (chI A z.1 z.2 a) (A.issB c z.2 u) z.2 a false := hL.1
  have fR : rdChR A idx b z.1 (chI A z.1 z.2 a) (A.issB c z.2 u) z.2 a' true =
      rdChR A idx b z.1 (chI A z.1 z.2 a) (A.issB c z.2 u) z.2 a true := hR.1
  have eRX : ∀ j,
      rdRedX A.ci A.cr idx (A.pkX j) (A.issB c z.2 u j).1
        (A.respondX (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (fun j => (A.issB c z.2 u j).2) j)
        (A.chooseX (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (fun j => (A.issB c z.2 u j).2) j)
        (c j).2 z.2 u' =
      rdRedX A.ci A.cr idx (A.pkX j) (A.issB c z.2 u j).1
        (A.respondX (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (fun j => (A.issB c z.2 u j).2) j)
        (A.chooseX (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (fun j => (A.issB c z.2 u j).2) j)
        (c j).2 z.2 u ∧
      redX (R := Rw) A.ci A.cr idx (A.pkX j) (A.issB c z.2 u j).1
        (A.respondX (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (fun j => (A.issB c z.2 u j).2) j)
        (A.chooseX (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (fun j => (A.issB c z.2 u j).2) j)
        (c j).2 (toSp z.2 u') =
      redX A.ci A.cr idx (A.pkX j) (A.issB c z.2 u j).1
        (A.respondX (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (fun j => (A.issB c z.2 u j).2) j)
        (A.chooseX (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (fun j => (A.issB c z.2 u j).2) j)
        (c j).2 (toSp z.2 u) :=
    fun j => rdRedX_cons _ _ _ _ _ _ _ _ z.2 u u' (agR_right (agR_at hB j))
  have eRB : A.redB idx c (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (A.issB c z.2 u) z.2 u' =
      A.redB idx c (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (A.issB c z.2 u) z.2 u :=
    funext fun j => (eRX j).2
  have eQB : A.QB idx c (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (A.issB c z.2 u) z.2 u' =
      A.QB idx c (chI A z.1 z.2 a).1.2 (chI A z.1 z.2 a).2.2 (A.issB c z.2 u) z.2 u := by
    unfold AdversaryN.QB
    refine congrArg rdUnionI (funext fun j => ?_)
    rw [(eX j).1, (eRX j).1]
  refine ⟨?_, ?_, ?_⟩
  · unfold tauM
    rw [eI, eTX, etx, eRB, eL, eR]
  · unfold RAM
    rw [eI, eTX, r0, r1, fL, fR]
  · unfold RBM
    rw [eI, eTX, eQB]

end Game

/-! ## The reduction's budgets -/

section Budgets

/-- **A reader with `H₅` and the cipher fixed** reads neither. -/
lemma sreads_fix {R : Type} {p : Params} {X : Type*} {f : Tb R p → X} {a3 a2 a5 aE : ℕ}
    (h : SReads p f a3 a2 a5 aE) (b5 : Tab5F) (bE : Blk → R) :
    SReads p (fun t : Tb R p => f (t.1, t.2.1, b5, bE)) a3 a2 0 0 := by
  obtain ⟨Q, hQ, hc⟩ := h
  refine ⟨fun t => ((Q (t.1, t.2.1, b5, bE)).1, (Q (t.1, t.2.1, b5, bE)).2.1, ∅, ∅),
    fun t t' ht => ?_, fun t => ⟨(hc _).1, (hc _).2.1, by simp, by simp⟩⟩
  have := hQ (t.1, t.2.1, b5, bE) (t'.1, t'.2.1, b5, bE) ⟨ht.1, ht.2.1, fun _ _ => rfl, fun _ _ => rfl⟩
  refine ⟨?_, this.2⟩
  simp only [this.1]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The further Clients' requests on the private pair `u` read only `H₂³`. -/
lemma txB_sreads (A : AdversaryN Rw ι) (c : ι → XC) (u : T5) :
    SReads pI (fun t : Tb Rw pI => A.txB c t.2.1 u) 0 (Fintype.card ι * nGrind) 0 0 := by
  have h := SReads.pi (ι := ι) (f := fun j (t : Tb Rw pI) => (issX A.ci A.cr (c j).1 t.2).2)
    fun j => issX_req_sreads A.ci A.cr (ci_length A) (cr_length A) (c j).1
  exact (sreads_fix h u.1 u.2).mono (by simp) le_rfl le_rfl le_rfl

/-- **The reduction's interaction reads `H₂³` only**, at the further issuance proofs' grinding
points. -/
theorem redS_iBudget (A : AdversaryN Rw ι) (idx : AnchorSet → UOVKey → ℕ) (c : ι → XC) (u : T5) :
    (A.redS idx c u).IBudget 0 (Fintype.card ι * nGrind) 0 0 where
  s0 q₀ q₁ _ _ _ := (txB_sreads A c u).map fun y =>
    ((A.respond q₀ q₁ y false, A.respond q₀ q₁ y true), (A.choose q₀ q₁ y false, A.choose q₀ q₁ y true))
  s1 q₀ q₁ _ _ _ := (txB_sreads A c u).map fun y =>
    ((A.respond q₀ q₁ y false, A.respond q₀ q₁ y true), (A.choose q₀ q₁ y false, A.choose q₀ q₁ y true))
  sL q₀ q₁ _ _ _ := (txB_sreads A c u).map fun y =>
    ((A.respond q₀ q₁ y false, A.respond q₀ q₁ y true), (A.choose q₀ q₁ y false, A.choose q₀ q₁ y true))
  sR q₀ q₁ _ _ _ := (txB_sreads A c u).map fun y =>
    ((A.respond q₀ q₁ y false, A.respond q₀ q₁ y true), (A.choose q₀ q₁ y false, A.choose q₀ q₁ y true))

/-- **The reduction's guess has the adversary's budget**: the further Clients run on the private
pair, and the patched tables agree with the game's off their points. -/
theorem redS_gBudget (A : AdversaryN Rw ι) (idx : AnchorSet → UOVKey → ℕ) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (c : ι → XC) (u : T5) : (A.redS idx c u).GBudget q3 q5 qE := fun _ =>
  { h30 := fun q₀ q₁ y g₁ gL gR s => hA.h30 _ _ _ y _ g₁ gL gR _ _
    h31 := fun q₀ q₁ y g₀ gL gR s => hA.h31 _ _ _ y _ g₀ gL gR _ _
    h3L := fun q₀ q₁ y g₀ g₁ gR s => hA.h3L _ _ _ y _ g₀ g₁ gR _ _
    h3R := fun q₀ q₁ y g₀ g₁ gL s => hA.h3R _ _ _ y _ g₀ g₁ gL _ _
    h5 := fun q₀ q₁ y sl => by
      classical
      let slx : ι → Tab3 × Tab3 := fun j => ((c j).1.2.2, (c j).2.2)
      let Q : Tab2G pI → RdS := fun g => A.QB idx c q₀ q₁ (A.issB c g u) g u
      let φ : ShM Rw → ShM Rw := fun v => toSp v.1 (mixR (Q v.1) u (v.2.1, v.2.2))
      choose K hK hf using fun (tx : ι → Bytes) (ox : ι → Except Error Bytes) =>
        hA.h5 q₀ q₁ tx y ox sl slx
      refine ⟨fun s => K (A.txB c s.1 u) (A.redB idx c q₀ q₁ (A.issB c s.1 u) s.1 u) (φ s),
        fun s => hK _ _ _, fun s G5 hs => ?_⟩
      have hp : φ (s.1, G5, s.2.2) = ((φ s).1, (mixR (Q s.1) u (G5, s.2.2)).1, (φ s).2.2) := rfl
      change A.guess q₀ q₁ (A.txB c s.1 u) y (A.redB idx c q₀ q₁ (A.issB c s.1 u) s.1 u) sl slx
          (φ (s.1, G5, s.2.2)) =
        A.guess q₀ q₁ (A.txB c s.1 u) y (A.redB idx c q₀ q₁ (A.issB c s.1 u) s.1 u) sl slx (φ s)
      rw [hp]
      refine hf _ _ (φ s) _ fun k hk => ?_
      show (if k ∈ (Q s.1).1 then u.1 k else s.2.1 k) = (if k ∈ (Q s.1).1 then u.1 k else G5 k)
      rw [hs k hk]
    hE := fun q₀ q₁ y sl => by
      classical
      let slx : ι → Tab3 × Tab3 := fun j => ((c j).1.2.2, (c j).2.2)
      let Q : Tab2G pI → RdS := fun g => A.QB idx c q₀ q₁ (A.issB c g u) g u
      let φ : ShM Rw → ShM Rw := fun v => toSp v.1 (mixR (Q v.1) u (v.2.1, v.2.2))
      choose K hK hf using fun (tx : ι → Bytes) (ox : ι → Except Error Bytes) =>
        hA.hE q₀ q₁ tx y ox sl slx
      refine ⟨fun s => K (A.txB c s.1 u) (A.redB idx c q₀ q₁ (A.issB c s.1 u) s.1 u) (φ s),
        fun s => hK _ _ _, fun s E hs => ?_⟩
      have hp : φ (s.1, s.2.1, E) = ((φ s).1, (φ s).2.1, (mixR (Q s.1) u (s.2.1, E)).2) := rfl
      change A.guess q₀ q₁ (A.txB c s.1 u) y (A.redB idx c q₀ q₁ (A.issB c s.1 u) s.1 u) sl slx
          (φ (s.1, s.2.1, E)) =
        A.guess q₀ q₁ (A.txB c s.1 u) y (A.redB idx c q₀ q₁ (A.issB c s.1 u) s.1 u) sl slx (φ s)
      rw [hp]
      refine hf _ _ (φ s) _ fun k hk => funext fun z => ?_
      show (if (Q s.1).2 k z then u.2 k z else s.2.2 k z) = (if (Q s.1).2 k z then u.2 k z else E k z)
      rw [hs k hk] }

end Budgets

/-! ## One step: the further Clients moved to private tables -/

section Step

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (A : AdversaryN Rw ι) (idx : AnchorSet → UOVKey → ℕ)

/-- **The bad event of the step**, in the split world: the challenge sessions' points on the
game's pair `z.1.2` meet the further Clients' points on the private pair `z.2`. -/
def badM (c : ι → XC) (b : Bool) (z : ((PT × Tab2G pI) × T5) × T5) : Prop :=
  ¬ Disj (RAM A idx c b z.1.1 z.1.2 z.2) (RBM A idx c z.1.1 z.1.2 z.2)

/-- The game's coins split into the challenge tapes and `H₂³`, and the `(H₅, cipher)` pair. -/
def splitTM : PT × ShM Rw ≃ (PT × Tab2G pI) × T5 where
  toFun z := ((z.1, z.2.1), z.2.2)
  invFun w := (w.1.1, toSp w.1.2 w.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The split world's coins regrouped: the private pair first. -/
def regroupTM : ((PT × Tab2G pI) × T5) × T5 ≃ T5 × (PT × ShM Rw) where
  toFun z := (z.2, (z.1.1.1, toSp z.1.1.2 z.1.2))
  invFun w := (((w.2.1, w.2.2.1), (w.2.2.2.1, w.2.2.2.2)), w.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **One world of the step**: the game of `A.withClients idx c` is the reduction's game averaged
over the private pair, up to the bad event (`pr_split_le`). -/
theorem withClients_close_redS (c : ι → XC) (b : Bool) :
    |pr (PT × ShM Rw) (realGameRA (A.withClients idx c) idx leanPI leanPR b) -
        pr (T5 × (PT × ShM Rw)) (fun w => realGameRA (A.redS idx c w.1) idx leanPI leanPR b w.2)| ≤
      pr (((PT × Tab2G pI) × T5) × T5) (badM A idx c b) := by
  have h := pr_split_le (C := PT × Tab2G pI) (T := T5) mixR AgR Disj agR_mixR mixR_inv
    (fun r r' a b h => agR_mixR_of_disj h a b) (tauM A idx c b) (RAM A idx c b) (RBM A idx c)
    (fun z a u a' u' hA hB => tauM_cons A idx c b z a u a' u' hA hB) (guessM A c)
  have h1 : pr (PT × ShM Rw) (realGameRA (A.withClients idx c) idx leanPI leanPR b) =
      pr ((PT × Tab2G pI) × T5) (fun z => guessM A c z.1 (tauM A idx c b z.1 z.2 z.2) z.2) := by
    rw [← pr_equiv splitTM.symm]
    exact pr_congr fun w => realGameRA_withClients_iff A idx c b w.1 w.2
  have h2 : pr (T5 × (PT × ShM Rw)) (fun w => realGameRA (A.redS idx c w.1) idx leanPI leanPR b w.2) =
      pr (((PT × Tab2G pI) × T5) × T5) (fun z => guessM A c z.1.1 (tauM A idx c b z.1.1 z.1.2 z.2)
        (mixR (RBM A idx c z.1.1 z.1.2 z.2) z.2 z.1.2)) := by
    rw [← pr_equiv regroupTM]
    exact pr_congr fun z => realGameRA_redS_iff A idx c b z.1.1 z.1.2 z.2
  rw [h1, h2]
  exact h

/-- **The one-pair error with the further Clients on private tables**: `anonymityRA_lean_num`
with the adversary's own guess budget and an interaction that reads only `H₂³` (`m·2³²` keys). -/
noncomputable def εPair0M (q3 q5 qE m : ℕ) (εhide : ℝ) : ℝ :=
  4 * εRO (0 + q3) (q5 + 0 + 1872) (qE + 0 + 13821) +
    4 * εAd 9 q3 (q5 + 1248) (qE + 13821) 0 (m * nGrind) (0 + 624) (0 + 9214) +
    4 * ((0 : ℕ) / 2 ^ 128 + 1 / 2 ^ 113 + εROP 0 312 4607 (0 + 624) (0 + 9214)) +
    6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide

/-- **The step bound, for fixed further tapes**: the two worlds of `A.withClients idx c` differ by
at most `εPair0M` plus the bad event in each world. -/
theorem withClients_step {q3 q5 qE : ℕ} {εhide : ℝ} (hA : A.Budget q3 q5 qE) (c : ι → XC)
    (hhide : ∀ u b cc, hidingAdv (A.redS idx c u).ctxRO.base.ci (A.redS idx c u).ctxRO.base.cr
      (reductionRA (A.redS idx c u) idx (leanSim pI) (leanSim pR) leanProgI leanProgR b cc) ≤ εhide) :
    |pr (PT × ShM Rw) (realGameRA (A.withClients idx c) idx leanPI leanPR false) -
        pr (PT × ShM Rw) (realGameRA (A.withClients idx c) idx leanPI leanPR true)| ≤
      εPair0M q3 q5 qE (Fintype.card ι) εhide + pr (((PT × Tab2G pI) × T5) × T5) (badM A idx c false) +
        pr (((PT × Tab2G pI) × T5) × T5) (badM A idx c true) := by
  have h0 := withClients_close_redS A idx c false
  have h1 := withClients_close_redS A idx c true
  have hm : |pr (T5 × (PT × ShM Rw)) (fun w => realGameRA (A.redS idx c w.1) idx leanPI leanPR false w.2) -
      pr (T5 × (PT × ShM Rw)) (fun w => realGameRA (A.redS idx c w.1) idx leanPI leanPR true w.2)| ≤
      εPair0M q3 q5 qE (Fintype.card ι) εhide :=
    abs_pr_prod_sub_le _ _ fun u => by
      have h := anonymityRA_lean_num idx (A.redS idx c u) (redS_gBudget A idx hA c u)
        (redS_iBudget A idx c u) (hhide u)
      unfold εPair0M
      exact h
  have := abs_sub_le (pr (PT × ShM Rw) (realGameRA (A.withClients idx c) idx leanPI leanPR false))
    (pr (T5 × (PT × ShM Rw)) (fun w => realGameRA (A.redS idx c w.1) idx leanPI leanPR false w.2))
    (pr (PT × ShM Rw) (realGameRA (A.withClients idx c) idx leanPI leanPR true))
  have := abs_sub_le (pr (T5 × (PT × ShM Rw)) (fun w => realGameRA (A.redS idx c w.1) idx leanPI leanPR false w.2))
    (pr (T5 × (PT × ShM Rw)) (fun w => realGameRA (A.redS idx c w.1) idx leanPI leanPR true w.2))
    (pr (PT × ShM Rw) (realGameRA (A.withClients idx c) idx leanPI leanPR true))
  rw [abs_sub_comm] at h1
  linarith

end Step

end VoleMole.Privacy.Moussaka
