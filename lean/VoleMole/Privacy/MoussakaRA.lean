import VoleMole.Privacy.MoussakaDelta
import VoleMole.ZK.AdaptRO

/-!
# Moussaka issuer hiding and unlinkability with an interaction that reads the tables

`anonymityRO_lean_num` (`Privacy/MoussakaRO.lean`, `Privacy/MoussakaDelta.lean`) assumes that the
adversary's interaction (the Issuer's responses, the Anchor Sets and digests) does not read the
random tables; only its final guess does. Here it does (`AdversaryRA`): after seeing the two
issuance requests, the adversary reads the four `H₃` slices and the shared tables (`H₂³`, `H₅`,
the cipher), with a budget per message, and its responses and choices are functions of what it
read.

## The model

* **The interaction** (`AdversaryRA.trans`): the two responses and the two `(Anchor Set, digest)`
  choices, from the two requests, the slices and the tables `u` the game runs on after the
  issuances (programmed by the issuance simulations, in the hybrids). Its budget
  (`AdversaryRA.IBudget i₃ i₂ i₅ i_E`): as a function of each slice and the shared tables (the other
  slices fixed), it reads at most `i₃` slice keys, `i₂` `H₂³` keys, `i₅` `H₅` keys and `i_E` cipher
  keys, adaptively and **consistently** (`ZK.Sim.SReads`: a table that agrees on its reads gives
  the same reads and the same messages; any deterministic query algorithm is consistent).
* **The game** (`viewRA`): `viewRO` for the adversary with the interaction fixed to the transcript
  computed on `u` (`AdversaryRA.fixT`). With real slots this is the spec's protocol with every hash
  and the cipher a uniform table and the adversary querying them (`realGameRA`).

## The hybrids

As in `anonymityRO`: issuance `0`, issuance `1`, redemption left, redemption right. The issuance
hops are `hop_ro` with the fixed-statement theorem (the interaction is part of the distinguisher:
its reads are added to the budget). The redemption hops are **`hop_roA`** with the
adaptive-statement theorem (`ZK.Sim.lean_zeroKnowledgeROA`): the redemption statement is read off
the transcript, which reads the tables through the issuance simulations' programming
(`SReads.comp_prog`, `progRO_cprog`): the reader's budget is `(i₃, i₂, i₅ + 624, i_E + 9214)`.
The collision terms of the redemption hops are bounded with `ZK.Sim.pr_collide_adaptive` (the
statement is adaptive, so this is the adaptive collision bound, at the same reader budget); the
one of issuance `1` is `deltaI1_le` (its statement is fixed by the coins). The simulated world is
a function of the commitments, the nullifiers, the coins, the slices and the tables
(`simGameRA_iff`), and hiding and the exchange of the fresh nullifiers finish as before.

**`anonymityRA_lean_num`**: see its statement; with `i₂ = 0` (no `H₂³` reads by the interaction)
the redemption hops' extra second application of zero knowledge disappears.

**Cipher rows.** Everything here is stated for every type of cipher rows `R` (the shared
tables `ZK.Sim.ShG R p`, `ZK/ReadsRO.lean`) with `ZKRow R`, `ZKPRow R`; `anonymityRA_lean_numG` is the generic
Lean-prover bound and `anonymityRA_lean_num` its instance at function rows (`Blk → Blk`, the PRF
view); `Privacy/PermRA.lean` instantiates it at permutation rows (AES as uniformly random
permutations, the adversary reading whole rows: forward and inverse queries).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

/-! ## The model -/

variable {R : Type} [Fintype R] [Nonempty R] [Inhabited R]

/-- **The interaction's transcript** at one pair of requests: the responses to Clients `false`,
`true`, the `(Anchor Set, digest)` of the left and right redemptions. -/
abbrev Trans := (Coins uovN × Coins uovN) × ((AnchorSet × Bytes) × (AnchorSet × Bytes))

/-- **The colluding adversary whose interaction reads the tables**: contexts, keys, responses and
choices from the two requests, the four `H₃` slices and the shared tables, and the guess. -/
structure AdversaryRA (R : Type) where
  ctxIss : Coins ctxBytes
  ctxRed : Coins ctxBytes
  pk : Bool → UOVKey
  respond : Bytes → Bytes → Bool → Slices → ShM R → Coins uovN
  choose : Bytes → Bytes → Bool → Slices → ShM R → AnchorSet × Bytes
  guess : Bytes → Bytes → Option (Except Error Bytes × Except Error Bytes) → Slices → ShM R → Prop

namespace AdversaryRA

variable (A : AdversaryRA R)

/-- The transcript at the requests `q₀`, `q₁`, on the slices `sl` and the tables `u`. -/
def trans (q₀ q₁ : Bytes) (sl : Slices) (u : ShM R) : Trans :=
  ((A.respond q₀ q₁ false sl u, A.respond q₀ q₁ true sl u),
    (A.choose q₀ q₁ false sl u, A.choose q₀ q₁ true sl u))

/-- **The adversary with its interaction fixed to a transcript**, as an `AdversaryRO`. -/
def fixT (tr : Trans) : AdversaryRO R :=
  ⟨A.ctxIss, A.ctxRed, A.pk, fun _ _ c => bif c then tr.1.2 else tr.1.1,
    fun _ _ side => bif side then tr.2.2 else tr.2.1, A.guess⟩

/-- The adversary's contexts, as an `AdversaryRO` (for the slots, which read only the contexts). -/
def ctxRO : AdversaryRO R := A.fixT (A.trans [] [] default default)

/-- **The interaction's budget**: as a function of each proof's slice and the shared tables (the
other slices fixed), the transcript reads at most `i₃` slice keys, `i₂` `H₂³` keys, `i₅` `H₅` keys
and `i_E` cipher keys, consistently. -/
structure IBudget (i3 i2 i5 iE : ℕ) : Prop where
  s0 : ∀ q₀ q₁ (g₁ gL gR : Tab3),
    SReads pI (fun t : Tb R pI => A.trans q₀ q₁ ((t.1, g₁), (gL, gR)) t.2) i3 i2 i5 iE
  s1 : ∀ q₀ q₁ (g₀ gL gR : Tab3),
    SReads pI (fun t : Tb R pI => A.trans q₀ q₁ ((g₀, t.1), (gL, gR)) t.2) i3 i2 i5 iE
  sL : ∀ q₀ q₁ (g₀ g₁ gR : Tab3),
    SReads pR (fun t : Tb R pR => A.trans q₀ q₁ ((g₀, g₁), (t.1, gR)) t.2) i3 i2 i5 iE
  sR : ∀ q₀ q₁ (g₀ g₁ gL : Tab3),
    SReads pR (fun t : Tb R pR => A.trans q₀ q₁ ((g₀, g₁), (gL, t.1)) t.2) i3 i2 i5 iE

/-- **The guess's budget** (`AdversaryRO.Budget`, for every transcript). -/
def GBudget (q3 q5 qE : ℕ) : Prop := ∀ tr, (A.fixT tr).Budget q3 q5 qE

end AdversaryRA

variable (A : AdversaryRA R) (idx : AnchorSet → UOVKey → ℕ)

/-- The transcript of a game: at the issuance outputs on the tables `u`. -/
def transOf (s₀ s₁ : IssSlot R) (sL sR : RedSlot R) (t : ShM R) : Trans :=
  A.trans (s₀.out (s₀.prog (s₁.prog t))).2 (s₁.out (s₀.prog (s₁.prog t))).2
    ((s₀.slice, s₁.slice), (sL.slice, sR.slice)) (s₀.prog (s₁.prog t))

/-- **The view in world `b`**: `viewRO` for the adversary with its interaction fixed to the
transcript computed on the slices and on the tables after the issuances. -/
def viewRA (b : Bool) (s₀ s₁ : IssSlot R) (sL sR : RedSlot R) (t : ShM R) : Prop :=
  viewRO (A.fixT (transOf A s₀ s₁ sL sR t)) idx b s₀ s₁ sL sR t

/-- The game with the slots drawn by `g₀ g₁ gL gR` from their parts of the tape. -/
def gameRA {T₀ T₁ TL TR : Type} (b : Bool) (g₀ : T₀ → IssSlot R) (g₁ : T₁ → IssSlot R)
    (gL : TL → RedSlot R) (gR : TR → RedSlot R) (x : ((T₀ × T₁) × (TL × TR)) × ShM R) : Prop :=
  viewRA A idx b (g₀ x.1.1.1) (g₁ x.1.1.2) (gL x.1.2.1) (gR x.1.2.2) x.2

/-- **The real game**: the spec's protocol with every proof computed on the shared uniform tables,
the adversary's interaction and guess reading them. -/
def realGameRA (PI : ProverRO R IssueInstance) (PR : ProverRO R RedeemInstance) (b : Bool) :
    ((TIr × TIr) × (TRr × TRr)) × ShM R → Prop :=
  gameRA A idx b (issRealRO A.ctxRO PI) (issRealRO A.ctxRO PI) (redRealRO A.ctxRO PR)
    (redRealRO A.ctxRO PR)

/-! ## All proofs simulated -/

variable {CI CR : Type} (simI : IssueInstance → CI → Bytes) (simR : RedeemInstance → CR → Bytes)
  (progI : IssueInstance → CI → ShM R → ShM R) (progR : RedeemInstance → CR → ShM R → ShM R)

/-- The game with all four proofs simulated. -/
def simGameRA (b : Bool) : ((TIs CI × TIs CI) × (TRs CR × TRs CR)) × ShM R → Prop :=
  gameRA A idx b (issSimRO A.ctxRO simI progI) (issSimRO A.ctxRO simI progI)
    (redSimRO A.ctxRO simR progR) (redSimRO A.ctxRO simR progR)

/-- **The simulated view** as a function of the commitments, the nullifiers, the simulator coins,
the slices and the tables: the transcript is computed from the simulated requests, the slices and
the tables programmed by the issuance simulations. -/
def hviewRA (b : Bool) (t₀ t₁ n₀ n₁ : Bytes) (cI₀ cI₁ : CI) (cL cR : CR) (sl : Slices) (s : ShM R) :
    Prop :=
  hviewRO (A.fixT (A.trans (t₀ ++ simI ⟨t₀, A.ctxRO.base.ci⟩ cI₀)
      (t₁ ++ simI ⟨t₁, A.ctxRO.base.ci⟩ cI₁) sl
      (progI ⟨t₀, A.ctxRO.base.ci⟩ cI₀ (progI ⟨t₁, A.ctxRO.base.ci⟩ cI₁ s))))
    idx simI simR progI progR b t₀ t₁ n₀ n₁ cI₀ cI₁ cL cR sl s

theorem simGameRA_iff (b : Bool) (x : ((TIs CI × TIs CI) × (TRs CR × TRs CR)) × ShM R) :
    simGameRA A idx simI simR progI progR b x ↔
      hviewRA A idx simI simR progI progR b (tOf A.ctxRO x.1.1.1.1) (tOf A.ctxRO x.1.1.2.1)
        (List.ofFn x.1.1.1.1.1) (List.ofFn x.1.1.2.1.1) x.1.1.1.2.1 x.1.1.2.2.1 x.1.2.1.1 x.1.2.2.1
        ((x.1.1.1.2.2, x.1.1.2.2.2), (x.1.2.1.2, x.1.2.2.2)) x.2 :=
  simGameRO_iff (A.fixT (transOf A (issSimRO A.ctxRO simI progI x.1.1.1)
    (issSimRO A.ctxRO simI progI x.1.1.2) (redSimRO A.ctxRO simR progR x.1.2.1)
    (redSimRO A.ctxRO simR progR x.1.2.2) x.2)) idx simI simR progI progR b x

/-- **The reduction to hiding**: the adversary, with the simulator coins, the slices and the tables
fixed, run on the commitments and nullifiers it is given. -/
def reductionRA (b : Bool) (c : ((CI × CI) × (CR × CR)) × (Slices × ShM R))
    (z : Bytes × Bytes × Bytes × Bytes) : Prop :=
  hviewRA A idx simI simR progI progR b z.1 z.2.1 z.2.2.1 z.2.2.2 c.1.1.1 c.1.1.2 c.1.2.1 c.1.2.2
    c.2.1 c.2.2

/-- The game after the hiding hop: fresh nullifiers are revealed at redemption. -/
def idealGameRA (b : Bool)
    (x : (HTape × (Coins nfBytes × Coins nfBytes)) × (((CI × CI) × (CR × CR)) × (Slices × ShM R))) :
    Prop :=
  reductionRA A idx simI simR progI progR b x.2 (hideIdeal A.ctxRO.base.ci A.ctxRO.base.cr x.1)

theorem hiding_hopRA [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (b : Bool) {εhide : ℝ}
    (hhide : ∀ c, hidingAdv A.ctxRO.base.ci A.ctxRO.base.cr
      (reductionRA A idx simI simR progI progR b c) ≤ εhide) :
    |pr _ (simGameRA A idx simI simR progI progR b) -
      pr _ (idealGameRA A idx simI simR progI progR b)| ≤ εhide := by
  rw [← pr_equiv regroupRO.symm (simGameRA A idx simI simR progI progR b),
    pr_congr fun y => simGameRA_iff A idx simI simR progI progR b (regroupRO.symm y)]
  exact abs_pr_prod_sub_le' _ _ fun c => hhide c

/-- **After the hiding hop the worlds coincide**, tables included. -/
theorem idealGameRA_eq [Fintype CI] [Fintype CR] :
    pr _ (idealGameRA A idx simI simR progI progR false) =
      pr _ (idealGameRA A idx simI simR progI progR true) := by
  rw [← pr_equiv swapNRO]
  exact pr_congr fun x => Iff.rfl

/-! ## The hybrids -/

section Hops

variable {A idx}
variable (PI : ProverRO R IssueInstance) (PR : ProverRO R RedeemInstance)

/-- The rest of the game around issuance `0`'s proof `o` (slice `g`), on the tables `u`: the
transcript on `u`, issuance `1` and both redemptions real. -/
def F0A (b : Bool) (γ : NR × (TIr × (TRr × TRr))) (o : Bytes) (g : Tab3) (u : ShM R) : Prop :=
  F0 (A.fixT (A.trans (tOf A.ctxRO γ.1 ++ o) ((issRealRO A.ctxRO PI γ.2.1).out u).2
    ((g, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2)) u)) idx PI PR b γ o g u

/-- The rest of the game around issuance `1`'s proof: issuance `0` simulated. -/
def F1A (b : Bool) (γ : TIs CI × (NR × (TRr × TRr))) (o : Bytes) (g : Tab3) (u : ShM R) : Prop :=
  F1 (A.fixT (A.trans (issSimOut A.ctxRO simI (γ.1.1, γ.1.2.1)).2 (tOf A.ctxRO γ.2.1 ++ o)
    ((γ.1.2.2, g), (γ.2.2.1.2, γ.2.2.2.2)) u)) idx simI PR b γ o g u

variable {q3 q5 qE i3 i2 i5 iE r5 rE m5 mE : ℕ}

/-- **The budget of hop 0's distinguisher**: the guess, the transcript, issuance `1` and both
redemptions run for real. -/
lemma F0A_budget (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (b : Bool) (γ : NR × (TIr × (TRr × TRr))) :
    Budget pI (i3 + q3) (r5 + (i5 + (r5 + r5 + q5))) (rE + (iE + (rE + rE + qE)))
      (fun o g s => F0A (A := A) (idx := idx) PI PR b γ o g s) := by
  refine ⟨fun o s => ?_, fun o g => ?_, fun o g => ?_⟩
  · exact Rd3.bind (m := fun g => A.trans (tOf A.ctxRO γ.1 ++ o)
        ((issRealRO A.ctxRO PI γ.2.1).out s).2 ((g, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2)) s)
      (f := fun x g => F0 (A.fixT x) idx PI PR b γ o g s)
      (SReads.rd3 (hI.s0 _ _ _ _ _) s) fun x => (hA x).h30 _ _ _ _ _ _ _
  · exact Rd5.bind (m := fun s => (issRealRO A.ctxRO PI γ.2.1).out s)
      (f := fun i s => (fun x s => postRO (A.fixT x) idx (pendOf A.ctxRO γ.1, tOf A.ctxRO γ.1 ++ o) i
          ((redRealRO A.ctxRO PR γ.2.2.1).out (pt (A.fixT x).base idx b
            (pendOf A.ctxRO γ.1, tOf A.ctxRO γ.1 ++ o) i false) s)
          ((redRealRO A.ctxRO PR γ.2.2.2).out (pt (A.fixT x).base idx b
            (pendOf A.ctxRO γ.1, tOf A.ctxRO γ.1 ++ o) i true) s)
          ((g, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2)) s)
        (A.trans (tOf A.ctxRO γ.1 ++ o) i.2 ((g, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2)) s) s)
      (rd5_issReal hPI5 γ.2.1) fun i => Rd5.bind
        (m := fun s => A.trans (tOf A.ctxRO γ.1 ++ o) i.2 ((g, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2)) s)
        (f := fun x s => postRO (A.fixT x) idx (pendOf A.ctxRO γ.1, tOf A.ctxRO γ.1 ++ o) i
          ((redRealRO A.ctxRO PR γ.2.2.1).out (pt (A.fixT x).base idx b
            (pendOf A.ctxRO γ.1, tOf A.ctxRO γ.1 ++ o) i false) s)
          ((redRealRO A.ctxRO PR γ.2.2.2).out (pt (A.fixT x).base idx b
            (pendOf A.ctxRO γ.1, tOf A.ctxRO γ.1 ++ o) i true) s)
          ((g, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2)) s)
        (SReads.rd5 (hI.s0 _ _ _ _ _) g) fun x =>
          rd5_postRO (A := A.fixT x) (idx := idx) (hA x) _ i (rd5_redReal hPR5 γ.2.2.1 _)
            (rd5_redReal hPR5 γ.2.2.2 _) _
  · exact RdE.bind (m := fun s => (issRealRO A.ctxRO PI γ.2.1).out s)
      (f := fun i s => (fun x s => postRO (A.fixT x) idx (pendOf A.ctxRO γ.1, tOf A.ctxRO γ.1 ++ o) i
          ((redRealRO A.ctxRO PR γ.2.2.1).out (pt (A.fixT x).base idx b
            (pendOf A.ctxRO γ.1, tOf A.ctxRO γ.1 ++ o) i false) s)
          ((redRealRO A.ctxRO PR γ.2.2.2).out (pt (A.fixT x).base idx b
            (pendOf A.ctxRO γ.1, tOf A.ctxRO γ.1 ++ o) i true) s)
          ((g, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2)) s)
        (A.trans (tOf A.ctxRO γ.1 ++ o) i.2 ((g, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2)) s) s)
      (rdE_issReal hPIE γ.2.1) fun i => RdE.bind
        (m := fun s => A.trans (tOf A.ctxRO γ.1 ++ o) i.2 ((g, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2)) s)
        (f := fun x s => postRO (A.fixT x) idx (pendOf A.ctxRO γ.1, tOf A.ctxRO γ.1 ++ o) i
          ((redRealRO A.ctxRO PR γ.2.2.1).out (pt (A.fixT x).base idx b
            (pendOf A.ctxRO γ.1, tOf A.ctxRO γ.1 ++ o) i false) s)
          ((redRealRO A.ctxRO PR γ.2.2.2).out (pt (A.fixT x).base idx b
            (pendOf A.ctxRO γ.1, tOf A.ctxRO γ.1 ++ o) i true) s)
          ((g, γ.2.1.2.2), (γ.2.2.1.2, γ.2.2.2.2)) s)
        (SReads.rdE (hI.s0 _ _ _ _ _) g) fun x =>
          rdE_postRO (A := A.fixT x) (idx := idx) (hA x) _ i (rdE_redReal hPRE γ.2.2.1 _)
            (rdE_redReal hPRE γ.2.2.2 _) _

theorem hop0RA [Fintype CI] [Nonempty CI] (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    {ε : ℝ} (hIzk : ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI
      (Budget pI (i3 + q3) (r5 + (i5 + (r5 + r5 + q5))) (rE + (iE + (rE + rE + qE)))) ε)
    (b : Bool) :
    |pr _ (gameRA A idx b (issRealRO A.ctxRO PI) (issRealRO A.ctxRO PI) (redRealRO A.ctxRO PR)
        (redRealRO A.ctxRO PR)) -
      pr _ (gameRA A idx b (issSimRO A.ctxRO simI progI) (issRealRO A.ctxRO PI)
        (redRealRO A.ctxRO PR) (redRealRO A.ctxRO PR))| ≤ ε := by
  have h := hop_ro (Γ := NR × (TIr × (TRr × TRr))) (ρ := Coins proveSeedBytes) (G := Tab3)
    (C := CI) (S := ShM R)
    (fun γ ρ g s => PI (wIOf A.ctxRO γ.1) (xIOf A.ctxRO γ.1) (List.ofFn ρ) g s)
    (fun γ c => simI (xIOf A.ctxRO γ.1) c) (fun γ c => progI (xIOf A.ctxRO γ.1) c) (fun _ s => s)
    (F0A (A := A) (idx := idx) PI PR b) (ε := ε) fun γ => hIzk (xIOf A.ctxRO γ.1)
      (wIOf A.ctxRO γ.1) (issueRelW_of A.ctxRO γ.1)
      (fun o g s => F0A (A := A) (idx := idx) PI PR b γ o g s)
      (F0A_budget (PI := PI) (PR := PR) hA hI hPI5 hPIE hPR5 hPRE b γ)
  have hδ : pr ((NR × (TIr × (TRr × TRr))) × ((Coins proveSeedBytes × Tab3) × ShM R)) (fun z =>
      PI (wIOf A.ctxRO z.1.1) (xIOf A.ctxRO z.1.1) (List.ofFn z.2.1.1) z.2.1.2 z.2.2 ≠
        PI (wIOf A.ctxRO z.1.1) (xIOf A.ctxRO z.1.1) (List.ofFn z.2.1.1) z.2.1.2 z.2.2) = 0 := by
    rw [pr_congr (Q := fun _ => False) fun z => by simp, pr_const]
    simp
  rw [hδ, add_zero] at h
  rw [← pr_equiv eqv0 (gameRA A idx b (issRealRO A.ctxRO PI) (issRealRO A.ctxRO PI)
      (redRealRO A.ctxRO PR) (redRealRO A.ctxRO PR)), ← pr_equiv eqv0 (gameRA A idx b
      (issSimRO A.ctxRO simI progI) (issRealRO A.ctxRO PI) (redRealRO A.ctxRO PR)
      (redRealRO A.ctxRO PR))]
  exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
    (pr_congr fun z => Iff.rfl)) h

/-- **The budget of hop 1's distinguisher on the tables `u`**: the guess, the transcript and both
redemptions run for real. -/
lemma F1A_budget (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (b : Bool) (γ : TIs CI × (NR × (TRr × TRr))) :
    Budget pI (i3 + q3) (i5 + (r5 + r5 + q5) + m5) (iE + (rE + rE + qE) + mE)
      (fun o g s => F1A (A := A) (idx := idx) simI PR b γ o g
        (progI (xIOf A.ctxRO γ.1.1) γ.1.2.1 s)) := by
  refine ⟨fun o s => ?_, fun o g => ?_, fun o g => ?_⟩
  · exact Rd3.bind (m := fun g => A.trans (issSimOut A.ctxRO simI (γ.1.1, γ.1.2.1)).2
        (tOf A.ctxRO γ.2.1 ++ o) ((γ.1.2.2, g), (γ.2.2.1.2, γ.2.2.2.2))
        (progI (xIOf A.ctxRO γ.1.1) γ.1.2.1 s))
      (f := fun x g => F1 (A.fixT x) idx simI PR b γ o g (progI (xIOf A.ctxRO γ.1.1) γ.1.2.1 s))
      (SReads.rd3 (hI.s1 _ _ _ _ _) _) fun x => (hA x).h31 _ _ _ _ _ _ _
  · refine Rd5.comp_prog (f := fun u => F1A (A := A) (idx := idx) simI PR b γ o g u) ?_ (hpI _ _)
    exact Rd5.bind (m := fun u => A.trans (issSimOut A.ctxRO simI (γ.1.1, γ.1.2.1)).2
        (tOf A.ctxRO γ.2.1 ++ o) ((γ.1.2.2, g), (γ.2.2.1.2, γ.2.2.2.2)) u)
      (f := fun x u => F1 (A.fixT x) idx simI PR b γ o g u)
      (SReads.rd5 (hI.s1 _ _ _ _ _) g) fun x =>
        rd5_postRO (A := A.fixT x) (idx := idx) (hA x) _ _ (rd5_redReal hPR5 γ.2.2.1 _)
          (rd5_redReal hPR5 γ.2.2.2 _) _
  · refine RdE.comp_prog (f := fun u => F1A (A := A) (idx := idx) simI PR b γ o g u) ?_ (hpI _ _)
    exact RdE.bind (m := fun u => A.trans (issSimOut A.ctxRO simI (γ.1.1, γ.1.2.1)).2
        (tOf A.ctxRO γ.2.1 ++ o) ((γ.1.2.2, g), (γ.2.2.1.2, γ.2.2.2.2)) u)
      (f := fun x u => F1 (A.fixT x) idx simI PR b γ o g u)
      (SReads.rdE (hI.s1 _ _ _ _ _) g) fun x =>
        rdE_postRO (A := A.fixT x) (idx := idx) (hA x) _ _ (rdE_redReal hPRE γ.2.2.1 _)
          (rdE_redReal hPRE γ.2.2.2 _) _

theorem hop1RA [Fintype CI] [Nonempty CI] (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE)
    {ε : ℝ} (hIzk : ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI
      (Budget pI (i3 + q3) (i5 + (r5 + r5 + q5) + m5) (iE + (rE + rE + qE) + mE)) ε) (b : Bool) :
    |pr _ (gameRA A idx b (issSimRO A.ctxRO simI progI) (issRealRO A.ctxRO PI)
        (redRealRO A.ctxRO PR) (redRealRO A.ctxRO PR)) -
      pr _ (gameRA A idx b (issSimRO A.ctxRO simI progI) (issSimRO A.ctxRO simI progI)
        (redRealRO A.ctxRO PR) (redRealRO A.ctxRO PR))| ≤ ε + deltaI1 A.ctxRO progI PI := by
  have h := hop_ro (Γ := TIs CI × (NR × (TRr × TRr))) (ρ := Coins proveSeedBytes) (G := Tab3)
    (C := CI) (S := ShM R)
    (fun γ ρ g s => PI (wIOf A.ctxRO γ.2.1) (xIOf A.ctxRO γ.2.1) (List.ofFn ρ) g s)
    (fun γ c => simI (xIOf A.ctxRO γ.2.1) c) (fun γ c => progI (xIOf A.ctxRO γ.2.1) c)
    (fun γ s => progI (xIOf A.ctxRO γ.1.1) γ.1.2.1 s)
    (F1A (A := A) (idx := idx) simI PR b) (ε := ε) fun γ => hIzk (xIOf A.ctxRO γ.2.1)
      (wIOf A.ctxRO γ.2.1) (issueRelW_of A.ctxRO γ.2.1)
      (fun o g s => F1A (A := A) (idx := idx) simI PR b γ o g (progI (xIOf A.ctxRO γ.1.1) γ.1.2.1 s))
      (F1A_budget (simI := simI) (PR := PR) (progI := progI) hA hI hPR5 hPRE hpI b γ)
  rw [← pr_equiv eqv1 (gameRA A idx b (issSimRO A.ctxRO simI progI) (issRealRO A.ctxRO PI)
      (redRealRO A.ctxRO PR) (redRealRO A.ctxRO PR)), ← pr_equiv eqv1 (gameRA A idx b
      (issSimRO A.ctxRO simI progI) (issSimRO A.ctxRO simI progI) (redRealRO A.ctxRO PR)
      (redRealRO A.ctxRO PR))]
  exact le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun z => Iff.rfl)
    (pr_congr fun z => Iff.rfl)) h

/-- With the redemptions not allowed, the guess does not see them. -/
lemma postRO_not_ok {A' : AdversaryRO R} {i₀ i₁ : PendingToken × Bytes}
    (h : allOk A'.base idx i₀ i₁ = false) (o₁ o₂ o₃ o₄ : Except Error Bytes) (sl : Slices) (v : ShM R) :
    postRO A' idx i₀ i₁ o₁ o₂ sl v ↔ postRO A' idx i₀ i₁ o₃ o₄ sl v := by
  simp only [postRO, h, Bool.cond_false]

/-! ### The left redemption -/

/-- The context of hop L: the simulated issuances and the right redemption's real tape. -/
abbrev ΓL (CI : Type) := (TIs CI × TIs CI) × TRr

/-- **The transcript in hop L**, read off the left redemption's slice and the shared tables
(through the issuance simulations' programming). -/
def SxL (γ : ΓL CI) (t : Tab3 × ShM R) : Trans :=
  A.trans (i₀Of A.ctxRO simI γ).2 (i₁Of A.ctxRO simI γ).2 ((γ.1.1.2.2, γ.1.2.2.2), (t.1, γ.2.2))
    (PIOf A.ctxRO progI γ t.2)

/-- The redemptions happen (`allOk`) at the transcript `x`. -/
def okA {α : Type} (γ : (TIs CI × TIs CI) × α) (x : Trans) : Bool :=
  allOk (A.fixT x).base idx (i₀Of A.ctxRO simI γ) (i₁Of A.ctxRO simI γ)

/-- The redemption point of side `side` at the transcript `x`. -/
def ptA {α : Type} (b : Bool) (γ : (TIs CI × TIs CI) × α) (x : Trans) (side : Bool) : RedeemPt :=
  pt (A.fixT x).base idx b (i₀Of A.ctxRO simI γ) (i₁Of A.ctxRO simI γ) side

/-- The real redemption of side `side`, computed only if the redemptions happen. -/
def PA {α : Type} (b : Bool) (side : Bool) (γ : (TIs CI × TIs CI) × α) (x : Trans)
    (ρ : Coins proveSeedBytes) (g : Tab3) (s : ShM R) : Except Error Bytes :=
  if okA (A := A) (idx := idx) simI γ x = true then
    (redRealRO A.ctxRO PR (ρ, g)).out (ptA (A := A) (idx := idx) simI b γ x side) s
  else .error .malformed

/-- The simulated redemption of side `side`. -/
def SmA {α : Type} (b : Bool) (side : Bool) (γ : (TIs CI × TIs CI) × α) (x : Trans) (c : CR) :
    Except Error Bytes :=
  redSim A.ctxRO.base simR c (ptA (A := A) (idx := idx) simI b γ x side)

/-- The simulator's programming of side `side`, if the redemptions happen. -/
def progA {α : Type} (b : Bool) (side : Bool) (γ : (TIs CI × TIs CI) × α) (x : Trans) (c : CR)
    (s : ShM R) : ShM R :=
  if okA (A := A) (idx := idx) simI γ x = true then
    progR (xROf A.ctxRO (ptA (A := A) (idx := idx) simI b γ x side)) c s else s

/-- The rest of the game around the left redemption's output. -/
def FLA (b : Bool) (γ : ΓL CI) (x : Trans) (o : Except Error Bytes) (g : Tab3) (u : ShM R) : Prop :=
  postRO (A.fixT x) idx (i₀Of A.ctxRO simI γ) (i₁Of A.ctxRO simI γ) o
    ((redRealRO A.ctxRO PR γ.2).out (ptA (A := A) (idx := idx) simI b γ x true) u)
    ((γ.1.1.2.2, γ.1.2.2.2), (g, γ.2.2)) u

/-- **The collision term of hop L**: the left redemption's real proof (of the statement read off
the tables) on the tables programmed by the issuance simulations differs from the one on the
original tables. -/
noncomputable def deltaLA [Fintype CI] (b : Bool) : ℝ :=
  pr (ΓL CI × (Coins proveSeedBytes × (Tab3 × ShM R))) fun z =>
    PA (A := A) (idx := idx) simI PR b false z.1 (SxL (A := A) simI progI z.1 z.2.2) z.2.1 z.2.2.1
        (PIOf A.ctxRO progI z.1 z.2.2.2) ≠
      PA (A := A) (idx := idx) simI PR b false z.1 (SxL (A := A) simI progI z.1 z.2.2) z.2.1 z.2.2.1
        z.2.2.2

/-- The redemption facts at a point of the transcript where the redemptions happen. -/
lemma redeem_factsA {α : Type} (b side : Bool) (γ : (TIs CI × TIs CI) × α) (x : Trans)
    (hok : okA (A := A) (idx := idx) simI γ x = true) :
    RedeemRelW (xROf A.ctxRO (ptA (A := A) (idx := idx) simI b γ x side))
        (wROf A.ctxRO (ptA (A := A) (idx := idx) simI b γ x side)) ∧
      (∀ (y : TRr) u, (redRealRO A.ctxRO PR y).out (ptA (A := A) (idx := idx) simI b γ x side) u =
        .ok ((ptA (A := A) (idx := idx) simI b γ x side).tok.nf ++
          PR (wROf A.ctxRO (ptA (A := A) (idx := idx) simI b γ x side))
            (xROf A.ctxRO (ptA (A := A) (idx := idx) simI b γ x side)) (List.ofFn y.1) y.2 u)) ∧
      ∀ c, redSim A.ctxRO.base simR c (ptA (A := A) (idx := idx) simI b γ x side) =
        .ok ((ptA (A := A) (idx := idx) simI b γ x side).tok.nf ++
          simR (xROf A.ctxRO (ptA (A := A) (idx := idx) simI b γ x side)) c) := by
  have hwf := tokD_wf (A.fixT x).base (i₀ := i₀Of A.ctxRO simI γ) (i₁ := i₁Of A.ctxRO simI γ)
    (issSimOut_wf A.ctxRO simI _) (issSimOut_wf A.ctxRO simI _) (b ^^ side)
  exact redeem_facts A.ctxRO simR PR _ hwf.1 hwf.2.1 hwf.2.2
    (redeemOk_pt_of_allOk idx (A.fixT x).base hok b side)

/-- The statement and witness of side `side` at the transcript `x`, if the redemptions happen. -/
def stwA {α : Type} (b side : Bool) (γ : (TIs CI × TIs CI) × α) (x : Trans) :
    Option (RedeemInstance × Bytes) :=
  if okA (A := A) (idx := idx) simI γ x = true then
    some (xROf A.ctxRO (ptA (A := A) (idx := idx) simI b γ x side),
      wROf A.ctxRO (ptA (A := A) (idx := idx) simI b γ x side))
  else none

lemma stwA_rel {α : Type} (b side : Bool) (γ : (TIs CI × TIs CI) × α) :
    ∀ x i w, stwA (A := A) (idx := idx) simI b side γ x = some (i, w) → RedeemRelW i w := by
  intro x i w h
  unfold stwA at h
  split_ifs at h with hok
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hwf := tokD_wf (A.fixT x).base (i₀ := i₀Of A.ctxRO simI γ) (i₁ := i₁Of A.ctxRO simI γ)
      (issSimOut_wf A.ctxRO simI _) (issSimOut_wf A.ctxRO simI _) (b ^^ side)
    exact (redeem_facts A.ctxRO (fun _ (_ : Unit) => ([] : Bytes)) (fun _ _ _ _ _ => []) _ hwf.1
      hwf.2.1 hwf.2.2 (redeemOk_pt_of_allOk idx (A.fixT x).base hok b side)).1

theorem hopLRA [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (hA : A.GBudget q3 q5 qE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE)
    {AdmS : (X : Type) → (Tab3 × ShM R → X) → Prop}
    (hS : ∀ γ : ΓL CI, AdmS Trans (SxL (A := A) simI progI γ))
    {ε : ℝ} (hR : ZeroKnowledgeROA RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmS
      (Budget pR q3 (0 + r5 + q5 + (m5 + m5)) (0 + rE + qE + (mE + mE))) ε) (b : Bool) :
    |pr _ (gameRA A idx b (issSimRO A.ctxRO simI progI) (issSimRO A.ctxRO simI progI)
        (redRealRO A.ctxRO PR) (redRealRO A.ctxRO PR)) -
      pr _ (gameRA A idx b (issSimRO A.ctxRO simI progI) (issSimRO A.ctxRO simI progI)
        (redSimRO A.ctxRO simR progR) (redRealRO A.ctxRO PR))| ≤
      ε + deltaLA (A := A) (idx := idx) (simI := simI) (progI := progI) (PR := PR) b := by
  have h := hop_roA (Γ := ΓL CI) (ρ := Coins proveSeedBytes) (G := Tab3) (C := CR) (S := ShM R)
    (SxL (A := A) simI progI) (PA (A := A) (idx := idx) simI PR b false)
    (SmA (A := A) (idx := idx) simI simR b false) (progA (A := A) (idx := idx) simI progR b false)
    (fun γ _ s => PIOf A.ctxRO progI γ s) (FLA (A := A) (idx := idx) simI PR b) (ε := ε)
    fun γ => ?_
  · -- From the hop to the games.
    let e : (((TIs CI × TIs CI) × ((Coins proveSeedBytes × Tab3) × TRr)) × ShM R) ≃
        (ΓL CI × (Coins proveSeedBytes × (Tab3 × ShM R))) :=
      { toFun := fun z => ((z.1.1, z.1.2.2), (z.1.2.1.1, (z.1.2.1.2, z.2)))
        invFun := fun z => ((z.1.1, ((z.2.1, z.2.2.1), z.1.2)), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let e' : (((TIs CI × TIs CI) × ((CR × Tab3) × TRr)) × ShM R) ≃
        (ΓL CI × (CR × (Tab3 × ShM R))) :=
      { toFun := fun z => ((z.1.1, z.1.2.2), (z.1.2.1.1, (z.1.2.1.2, z.2)))
        invFun := fun z => ((z.1.1, ((z.2.1, z.2.2.1), z.1.2)), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e1 : pr _ (gameRA A idx b (issSimRO A.ctxRO simI progI) (issSimRO A.ctxRO simI progI)
        (redRealRO A.ctxRO PR) (redRealRO A.ctxRO PR)) =
        pr (ΓL CI × (Coins proveSeedBytes × (Tab3 × ShM R))) (fun z =>
          FLA (A := A) (idx := idx) simI PR b z.1 (SxL (A := A) simI progI z.1 z.2.2)
            (PA (A := A) (idx := idx) simI PR b false z.1 (SxL (A := A) simI progI z.1 z.2.2) z.2.1
              z.2.2.1 (PIOf A.ctxRO progI z.1 z.2.2.2)) z.2.2.1 (PIOf A.ctxRO progI z.1 z.2.2.2)) := by
      rw [← pr_equiv e.symm]
      refine pr_congr fun z => ?_
      show FLA (A := A) (idx := idx) simI PR b z.1 (SxL (A := A) simI progI z.1 z.2.2)
          ((redRealRO A.ctxRO PR (z.2.1, z.2.2.1)).out (ptA (A := A) (idx := idx) simI b z.1
            (SxL (A := A) simI progI z.1 z.2.2) false) (PIOf A.ctxRO progI z.1 z.2.2.2)) z.2.2.1
          (PIOf A.ctxRO progI z.1 z.2.2.2) ↔ _
      unfold PA
      split_ifs with hok
      · exact Iff.rfl
      · exact postRO_not_ok (Bool.of_not_eq_true hok) _ _ _ _ _ _
    have e2 : pr _ (gameRA A idx b (issSimRO A.ctxRO simI progI) (issSimRO A.ctxRO simI progI)
        (redSimRO A.ctxRO simR progR) (redRealRO A.ctxRO PR)) =
        pr (ΓL CI × (CR × (Tab3 × ShM R))) (fun z =>
          FLA (A := A) (idx := idx) simI PR b z.1 (SxL (A := A) simI progI z.1 z.2.2)
            (SmA (A := A) (idx := idx) simI simR b false z.1 (SxL (A := A) simI progI z.1 z.2.2) z.2.1)
            z.2.2.1 (PIOf A.ctxRO progI z.1 (progA (A := A) (idx := idx) simI progR b false z.1
              (SxL (A := A) simI progI z.1 z.2.2) z.2.1 z.2.2.2))) := by
      rw [← pr_equiv e'.symm]
      exact pr_congr fun z => Iff.rfl
    rw [e1, e2]
    exact h
  · -- The zero-knowledge step, from `ZeroKnowledgeROA`.
    have hz := hR Trans (SxL (A := A) simI progI γ) (stwA (A := A) (idx := idx) simI b false γ)
      (hS γ) (stwA_rel (A := A) (idx := idx) simI b false γ) []
      (fun x o g s => FLA (A := A) (idx := idx) simI PR b γ x
        (.ok ((ptA (A := A) (idx := idx) simI b γ x false).tok.nf ++ o)) g (PIOf A.ctxRO progI γ s))
      fun x => ⟨fun o s => (hA x).h3L _ _ _ _ _ _ _,
        fun o g => (rd5_postRO (A := A.fixT x) (idx := idx) (hA x) _ _ (Rd5.const _)
          (rd5_redReal hPR5 _ _) _).comp_prog ((hpI _ _).comp (hpI _ _)),
        fun o g => (rdE_postRO (A := A.fixT x) (idx := idx) (hA x) _ _ (RdE.const _)
          (rdE_redReal hPRE _ _) _).comp_prog ((hpI _ _).comp (hpI _ _))⟩
    refine le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun a => ?_)
      (pr_congr fun a => ?_)) hz
    · show FLA (A := A) (idx := idx) simI PR b γ (SxL (A := A) simI progI γ a.2)
          (PA (A := A) (idx := idx) simI PR b false γ (SxL (A := A) simI progI γ a.2) a.1 a.2.1
            a.2.2) a.2.1 (PIOf A.ctxRO progI γ a.2.2) ↔ _
      unfold PA outReal stwA
      split_ifs with hok
      · rw [(redeem_factsA (A := A) (idx := idx) simI simR PR b false γ _ hok).2.1]
        rfl
      · exact postRO_not_ok (Bool.of_not_eq_true hok) _ _ _ _ _ _
    · show FLA (A := A) (idx := idx) simI PR b γ (SxL (A := A) simI progI γ a.2)
          (SmA (A := A) (idx := idx) simI simR b false γ (SxL (A := A) simI progI γ a.2) a.1) a.2.1
          (PIOf A.ctxRO progI γ (progA (A := A) (idx := idx) simI progR b false γ
            (SxL (A := A) simI progI γ a.2) a.1 a.2.2)) ↔ _
      unfold SmA progA outSim progSim stwA
      split_ifs with hok
      · rw [(redeem_factsA (A := A) (idx := idx) simI simR PR b false γ _ hok).2.2]
        rfl
      · exact postRO_not_ok (Bool.of_not_eq_true hok) _ _ _ _ _ _

/-! ### The right redemption -/

/-- The context of hop R: the simulated issuances and the simulated left redemption. -/
abbrev ΓR (CI CR : Type) := (TIs CI × TIs CI) × TRs CR

/-- **The transcript in hop R**, read off the right redemption's slice and the shared tables. -/
def SxR (γ : ΓR CI CR) (t : Tab3 × ShM R) : Trans :=
  A.trans (i₀Of A.ctxRO simI γ).2 (i₁Of A.ctxRO simI γ).2 ((γ.1.1.2.2, γ.1.2.2.2), (γ.2.2, t.1))
    (PIOf A.ctxRO progI γ t.2)

/-- The programming before the right redemption's: the left redemption's (if the redemptions
happen), then the issuances'. -/
def LRA (b : Bool) (γ : ΓR CI CR) (x : Trans) (s : ShM R) : ShM R :=
  PIOf A.ctxRO progI γ (progA (A := A) (idx := idx) simI progR b false γ x γ.2.1 s)

/-- The rest of the game around the right redemption's output. -/
def FRA (b : Bool) (γ : ΓR CI CR) (x : Trans) (o : Except Error Bytes) (g : Tab3) (u : ShM R) :
    Prop :=
  postRO (A.fixT x) idx (i₀Of A.ctxRO simI γ) (i₁Of A.ctxRO simI γ)
    (SmA (A := A) (idx := idx) simI simR b false γ x γ.2.1) o ((γ.1.1.2.2, γ.1.2.2.2), (γ.2.2, g)) u

/-- **The collision term of hop R**: the right redemption's real proof on the tables programmed by
the other three simulations differs from the one on the original tables. -/
noncomputable def deltaRA [Fintype CI] [Fintype CR] (b : Bool) : ℝ :=
  pr (ΓR CI CR × (Coins proveSeedBytes × (Tab3 × ShM R))) fun z =>
    PA (A := A) (idx := idx) simI PR b true z.1 (SxR (A := A) simI progI z.1 z.2.2) z.2.1 z.2.2.1
        (LRA (A := A) (idx := idx) simI progI progR b z.1 (SxR (A := A) simI progI z.1 z.2.2)
          z.2.2.2) ≠
      PA (A := A) (idx := idx) simI PR b true z.1 (SxR (A := A) simI progI z.1 z.2.2) z.2.1 z.2.2.1
        z.2.2.2

theorem hopRRA [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR] (hA : A.GBudget q3 q5 qE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpR : ∀ x c, IsProg (progR x c) m5 mE)
    {AdmS : (X : Type) → (Tab3 × ShM R → X) → Prop}
    (hS : ∀ γ : ΓR CI CR, AdmS Trans (SxR (A := A) simI progI γ))
    {ε : ℝ} (hR : ZeroKnowledgeROA RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmS
      (Budget pR q3 (0 + 0 + q5 + (m5 + (m5 + m5))) (0 + 0 + qE + (mE + (mE + mE)))) ε)
    (b : Bool) :
    |pr _ (gameRA A idx b (issSimRO A.ctxRO simI progI) (issSimRO A.ctxRO simI progI)
        (redSimRO A.ctxRO simR progR) (redRealRO A.ctxRO PR)) -
      pr _ (simGameRA A idx simI simR progI progR b)| ≤
      ε + deltaRA (A := A) (idx := idx) (simI := simI) (progI := progI) (progR := progR) (PR := PR)
        b := by
  have h := hop_roA (Γ := ΓR CI CR) (ρ := Coins proveSeedBytes) (G := Tab3) (C := CR) (S := ShM R)
    (SxR (A := A) simI progI) (PA (A := A) (idx := idx) simI PR b true)
    (SmA (A := A) (idx := idx) simI simR b true) (progA (A := A) (idx := idx) simI progR b true)
    (LRA (A := A) (idx := idx) simI progI progR b) (FRA (A := A) (idx := idx) simI simR b) (ε := ε)
    fun γ => ?_
  · let e : (((TIs CI × TIs CI) × (TRs CR × (Coins proveSeedBytes × Tab3))) × ShM R) ≃
        (ΓR CI CR × (Coins proveSeedBytes × (Tab3 × ShM R))) :=
      { toFun := fun z => ((z.1.1, z.1.2.1), (z.1.2.2.1, (z.1.2.2.2, z.2)))
        invFun := fun z => ((z.1.1, (z.1.2, (z.2.1, z.2.2.1))), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let e' : (((TIs CI × TIs CI) × (TRs CR × (CR × Tab3))) × ShM R) ≃
        (ΓR CI CR × (CR × (Tab3 × ShM R))) :=
      { toFun := fun z => ((z.1.1, z.1.2.1), (z.1.2.2.1, (z.1.2.2.2, z.2)))
        invFun := fun z => ((z.1.1, (z.1.2, (z.2.1, z.2.2.1))), z.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e1 : pr _ (gameRA A idx b (issSimRO A.ctxRO simI progI) (issSimRO A.ctxRO simI progI)
        (redSimRO A.ctxRO simR progR) (redRealRO A.ctxRO PR)) =
        pr (ΓR CI CR × (Coins proveSeedBytes × (Tab3 × ShM R))) (fun z =>
          FRA (A := A) (idx := idx) simI simR b z.1 (SxR (A := A) simI progI z.1 z.2.2)
            (PA (A := A) (idx := idx) simI PR b true z.1 (SxR (A := A) simI progI z.1 z.2.2) z.2.1
              z.2.2.1 (LRA (A := A) (idx := idx) simI progI progR b z.1
                (SxR (A := A) simI progI z.1 z.2.2) z.2.2.2)) z.2.2.1
            (LRA (A := A) (idx := idx) simI progI progR b z.1 (SxR (A := A) simI progI z.1 z.2.2)
              z.2.2.2)) := by
      rw [← pr_equiv e.symm]
      refine pr_congr fun z => ?_
      show FRA (A := A) (idx := idx) simI simR b z.1 (SxR (A := A) simI progI z.1 z.2.2)
          ((redRealRO A.ctxRO PR (z.2.1, z.2.2.1)).out (ptA (A := A) (idx := idx) simI b z.1
            (SxR (A := A) simI progI z.1 z.2.2) true) (LRA (A := A) (idx := idx) simI progI progR b
              z.1 (SxR (A := A) simI progI z.1 z.2.2) z.2.2.2)) z.2.2.1
          (LRA (A := A) (idx := idx) simI progI progR b z.1 (SxR (A := A) simI progI z.1 z.2.2)
            z.2.2.2) ↔ _
      unfold PA
      split_ifs with hok
      · exact Iff.rfl
      · exact postRO_not_ok (Bool.of_not_eq_true hok) _ _ _ _ _ _
    have e2 : pr _ (simGameRA A idx simI simR progI progR b) =
        pr (ΓR CI CR × (CR × (Tab3 × ShM R))) (fun z =>
          FRA (A := A) (idx := idx) simI simR b z.1 (SxR (A := A) simI progI z.1 z.2.2)
            (SmA (A := A) (idx := idx) simI simR b true z.1 (SxR (A := A) simI progI z.1 z.2.2) z.2.1)
            z.2.2.1 (LRA (A := A) (idx := idx) simI progI progR b z.1
              (SxR (A := A) simI progI z.1 z.2.2) (progA (A := A) (idx := idx) simI progR b true z.1
                (SxR (A := A) simI progI z.1 z.2.2) z.2.1 z.2.2.2))) := by
      rw [← pr_equiv e'.symm]
      exact pr_congr fun z => Iff.rfl
    rw [e1, e2]
    exact h
  · have hL : ∀ x, IsProg (LRA (A := A) (idx := idx) simI progI progR b γ x) (m5 + (m5 + m5))
        (mE + (mE + mE)) := fun x =>
      (hpI _ _).comp ((hpI _ _).comp (IsProg.ite _ (hpR _ _) (IsProg.id.mono (Nat.zero_le _)
        (Nat.zero_le _))))
    have hz := hR Trans (SxR (A := A) simI progI γ) (stwA (A := A) (idx := idx) simI b true γ)
      (hS γ) (stwA_rel (A := A) (idx := idx) simI b true γ) []
      (fun x o g s => FRA (A := A) (idx := idx) simI simR b γ x
        (.ok ((ptA (A := A) (idx := idx) simI b γ x true).tok.nf ++ o)) g
        (LRA (A := A) (idx := idx) simI progI progR b γ x s))
      fun x => ⟨fun o s => (hA x).h3R _ _ _ _ _ _ _,
        fun o g => (rd5_postRO (A := A.fixT x) (idx := idx) (hA x) _ _ (Rd5.const _)
          (Rd5.const _) _).comp_prog (hL x),
        fun o g => (rdE_postRO (A := A.fixT x) (idx := idx) (hA x) _ _ (RdE.const _)
          (RdE.const _) _).comp_prog (hL x)⟩
    refine le_of_eq_of_le (congrArg₂ (fun a c => |a - c|) (pr_congr fun a => ?_)
      (pr_congr fun a => ?_)) hz
    · show FRA (A := A) (idx := idx) simI simR b γ (SxR (A := A) simI progI γ a.2)
          (PA (A := A) (idx := idx) simI PR b true γ (SxR (A := A) simI progI γ a.2) a.1 a.2.1
            a.2.2) a.2.1 (LRA (A := A) (idx := idx) simI progI progR b γ
              (SxR (A := A) simI progI γ a.2) a.2.2) ↔ _
      unfold PA outReal stwA
      split_ifs with hok
      · rw [(redeem_factsA (A := A) (idx := idx) simI simR PR b true γ _ hok).2.1]
        rfl
      · exact postRO_not_ok (Bool.of_not_eq_true hok) _ _ _ _ _ _
    · show FRA (A := A) (idx := idx) simI simR b γ (SxR (A := A) simI progI γ a.2)
          (SmA (A := A) (idx := idx) simI simR b true γ (SxR (A := A) simI progI γ a.2) a.1) a.2.1
          (LRA (A := A) (idx := idx) simI progI progR b γ (SxR (A := A) simI progI γ a.2)
            (progA (A := A) (idx := idx) simI progR b true γ (SxR (A := A) simI progI γ a.2) a.1
              a.2.2)) ↔ _
      unfold SmA progA outSim progSim stwA
      split_ifs with hok
      · rw [(redeem_factsA (A := A) (idx := idx) simI simR PR b true γ _ hok).2.2]
        rfl
      · exact postRO_not_ok (Bool.of_not_eq_true hok) _ _ _ _ _ _

end Hops

/-! ## Issuer hiding and unlinkability with a table-reading interaction -/

variable {A idx PI PR simI simR progI progR} in
/-- **Theorem 4(a) in the random-oracle and ideal-cipher model, the interaction reading the tables,
for any proof systems.** The adversary's guess has the budget `(q₃, q₅, q_E)` (`GBudget`), its
interaction `(i₃, i₂, i₅, i_E)` (`IBudget`). If the issuance proofs are `ZeroKnowledgeRO` and the
redemption proofs `ZeroKnowledgeROA` (for the readers `AdmS`, which contain the transcripts read
through the issuance simulations' programming), the provers read `H₅`, the cipher at `r₅`, `r_E`
keys and the programmings at `m₅`, `m_E` keys, and the hiding reductions have advantage
`≤ εhide`, then the worlds differ by at most twice the four zero-knowledge errors, plus the
collision terms of both worlds, plus `2εhide`. -/
theorem anonymityRA [Fintype CI] [Nonempty CI] [Fintype CR] [Nonempty CR]
    {q3 q5 qE i3 i2 i5 iE r5 rE m5 mE : ℕ} {εI εR : ℕ → ℕ → ℝ} {εhide : ℝ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hPI5 : ∀ w x rho g, Rd5 (PI w x rho g) r5) (hPIE : ∀ w x rho g, RdE (PI w x rho g) rE)
    (hPR5 : ∀ w x rho g, Rd5 (PR w x rho g) r5) (hPRE : ∀ w x rho g, RdE (PR w x rho g) rE)
    (hpI : ∀ x c, IsProg (progI x c) m5 mE) (hpR : ∀ x c, IsProg (progR x c) m5 mE)
    {AdmS : (X : Type) → (Tab3 × ShM R → X) → Prop}
    (hSL : ∀ γ : ΓL CI, AdmS Trans (SxL (A := A) simI progI γ))
    (hSR : ∀ γ : ΓR CI CR, AdmS Trans (SxR (A := A) simI progI γ))
    (hIzk : ∀ a c, ZeroKnowledgeRO IssueRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PI w x (List.ofFn ρ) g s) simI progI
      (Budget pI (i3 + q3) a c) (εI a c))
    (hRzk : ∀ a c, ZeroKnowledgeROA RedeemRelW
      (fun x w (ρ : Coins proveSeedBytes) g s => PR w x (List.ofFn ρ) g s) simR progR AdmS
      (Budget pR q3 a c) (εR a c))
    (hhide : ∀ b c, hidingAdv A.ctxRO.base.ci A.ctxRO.base.cr
      (reductionRA A idx simI simR progI progR b c) ≤ εhide) :
    |pr _ (realGameRA A idx PI PR false) - pr _ (realGameRA A idx PI PR true)| ≤
      2 * (εI (r5 + (i5 + (r5 + r5 + q5))) (rE + (iE + (rE + rE + qE))) +
          εI (i5 + (r5 + r5 + q5) + m5) (iE + (rE + rE + qE) + mE) +
          εR (0 + r5 + q5 + (m5 + m5)) (0 + rE + qE + (mE + mE)) +
          εR (0 + 0 + q5 + (m5 + (m5 + m5))) (0 + 0 + qE + (mE + (mE + mE)))) +
        2 * deltaI1 A.ctxRO progI PI +
        (deltaLA (A := A) (idx := idx) (simI := simI) (progI := progI) (PR := PR) false +
          deltaLA (A := A) (idx := idx) (simI := simI) (progI := progI) (PR := PR) true) +
        (deltaRA (A := A) (idx := idx) (simI := simI) (progI := progI) (progR := progR) (PR := PR)
            false +
          deltaRA (A := A) (idx := idx) (simI := simI) (progI := progI) (progR := progR) (PR := PR)
            true) +
        2 * εhide := by
  have hw (b : Bool) : |pr _ (realGameRA A idx PI PR b) -
      pr _ (idealGameRA A idx simI simR progI progR b)| ≤
      εI (r5 + (i5 + (r5 + r5 + q5))) (rE + (iE + (rE + rE + qE))) +
        (εI (i5 + (r5 + r5 + q5) + m5) (iE + (rE + rE + qE) + mE) + deltaI1 A.ctxRO progI PI) +
        (εR (0 + r5 + q5 + (m5 + m5)) (0 + rE + qE + (mE + mE)) +
          deltaLA (A := A) (idx := idx) (simI := simI) (progI := progI) (PR := PR) b) +
        (εR (0 + 0 + q5 + (m5 + (m5 + m5))) (0 + 0 + qE + (mE + (mE + mE))) +
          deltaRA (A := A) (idx := idx) (simI := simI) (progI := progI) (progR := progR) (PR := PR)
            b) + εhide := by
    have h1 := hop0RA (idx := idx) (simI := simI) (progI := progI) (PI := PI) (PR := PR) hA hI hPI5
      hPIE hPR5 hPRE (hIzk _ _) b
    have h2 := hop1RA (idx := idx) (simI := simI) (progI := progI) (PI := PI) (PR := PR) hA hI hPR5
      hPRE hpI (hIzk _ _) b
    have h3 := hopLRA (idx := idx) (simI := simI) (progI := progI) (simR := simR) (progR := progR)
      (PR := PR) hA hPR5 hPRE hpI hSL (hRzk _ _) b
    have h4 := hopRRA (idx := idx) (simI := simI) (progI := progI) (simR := simR) (progR := progR)
      (PR := PR) hA hpI hpR hSR (hRzk _ _) b
    have h5 := hiding_hopRA A idx simI simR progI progR b (hhide b)
    unfold realGameRA
    set p0 := pr _ (gameRA A idx b (issRealRO A.ctxRO PI) (issRealRO A.ctxRO PI)
      (redRealRO A.ctxRO PR) (redRealRO A.ctxRO PR))
    set p1 := pr _ (gameRA A idx b (issSimRO A.ctxRO simI progI) (issRealRO A.ctxRO PI)
      (redRealRO A.ctxRO PR) (redRealRO A.ctxRO PR))
    set p2 := pr _ (gameRA A idx b (issSimRO A.ctxRO simI progI) (issSimRO A.ctxRO simI progI)
      (redRealRO A.ctxRO PR) (redRealRO A.ctxRO PR))
    set p3 := pr _ (gameRA A idx b (issSimRO A.ctxRO simI progI) (issSimRO A.ctxRO simI progI)
      (redSimRO A.ctxRO simR progR) (redRealRO A.ctxRO PR))
    set p4 := pr _ (simGameRA A idx simI simR progI progR b)
    set p5 := pr _ (idealGameRA A idx simI simR progI progR b)
    have := abs_sub_le p0 p1 p5
    have := abs_sub_le p1 p2 p5
    have := abs_sub_le p2 p3 p5
    have := abs_sub_le p3 p4 p5
    linarith
  have h0 := hw false
  have h1 := hw true
  rw [idealGameRA_eq] at h0
  rw [abs_sub_comm] at h1
  have := abs_sub_le (pr _ (realGameRA A idx PI PR false))
    (pr _ (idealGameRA A idx simI simR progI progR true)) (pr _ (realGameRA A idx PI PR true))
  linarith

/-! ## With the Lean prover -/

section Lean

open VoleMole.Verifier VoleMole.Verifier.Bridge

variable [CipherRow R] (A : AdversaryRA R) (idx : AnchorSet → UOVKey → ℕ)

/-- **Adaptive zero knowledge of the Lean redemption prover** (`ZK.Sim.lean_zeroKnowledgeROA`). -/
theorem leanPR_zkROA [ZKPRow R] (q3 q5 qE s3 s2 s5 sE : ℕ) : ZeroKnowledgeROA RedeemRelW
    (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPR w x (List.ofFn ρ) g s) (leanSim pR)
    leanProgR (fun _ Sx => SReads pR Sx s3 s2 s5 sE) (Budget pR q3 q5 qE)
    (εAdG R pR pR.qsDegree q3 q5 qE s3 s2 s5 sE) := by
  have h := lean_zeroKnowledgeROA (R := R) Hashes.shake pR stR (fun _ => rfl) rfl (fun _ w => toBA w)
    RedeemRelW csR zkHypR hashesWF_shake smallParams_pR q3 q5 qE s3 s2 s5 sE
    (fun o => toL (o.toOption.getD .empty))
  have e : (fun x w (ρ : Coins proveSeedBytes) g (s : ShM R) => leanPR w x (List.ofFn ρ) g s) =
      fun x w r g s => toL ((realRO pR Hashes.shake (stR x) (toBA w) r g s).toOption.getD .empty) := by
    funext x w ρ g s
    exact leanPR_ofFn w x ρ g s
  rw [e]
  exact h

/-- The issuance programming is a consistent programming of the redemption tables. -/
lemma cprog_leanProgI (x : IssueInstance) (c : SimCoins pI) :
    CProg (p := pR) (leanProgI (R := R) x c) 312 4607 :=
  progRO_cprog (p := pI) (Hb := Hashes.shake) (st := stI x) c

/-- **The transcript of hop L reads** `(i₃, i₂, i₅ + 624, i_E + 9214)`. -/
lemma sReads_SxL {i3 i2 i5 iE : ℕ} (hI : A.IBudget i3 i2 i5 iE) (γ : ΓL (SimCoins pI)) :
    SReads pR (SxL (A := A) (leanSim pI) leanProgI γ) i3 i2 (i5 + 312 + 312) (iE + 4607 + 4607) :=
  SReads.comp_prog (SReads.comp_prog (hI.sL _ _ _ _ _) (cprog_leanProgI _ _)) (cprog_leanProgI _ _)

/-- **The transcript of hop R reads** `(i₃, i₂, i₅ + 624, i_E + 9214)`. -/
lemma sReads_SxR {i3 i2 i5 iE : ℕ} (hI : A.IBudget i3 i2 i5 iE)
    (γ : ΓR (SimCoins pI) (SimCoins pR)) :
    SReads pR (SxR (A := A) (leanSim pI) leanProgI γ) i3 i2 (i5 + 312 + 312) (iE + 4607 + 4607) :=
  SReads.comp_prog (SReads.comp_prog (hI.sR _ _ _ _ _) (cprog_leanProgI _ _)) (cprog_leanProgI _ _)

/-- The Lean statement and witness of side `side` at a transcript. -/
def stwL {α : Type} (b side : Bool) (γ : (TIs (SimCoins pI) × TIs (SimCoins pI)) × α) (x : Trans) :
    Option (Statement × ByteArray) :=
  (stwA (A := A) (idx := idx) (leanSim pI) b side γ x).map fun iw => (stR iw.1, toBA iw.2)

lemma stwL_hyp {α : Type} (b side : Bool) (γ : (TIs (SimCoins pI) × TIs (SimCoins pI)) × α) :
    ∀ x st w, stwL A idx b side γ x = some (st, w) →
      st.params = pR ∧ ZKHyp CrtGen.tables st w
        (csR (xROf A.ctxRO (ptA (A := A) (idx := idx) (leanSim pI) b γ x side))) := by
  intro x st w h
  unfold stwL at h
  rcases hx : stwA (A := A) (idx := idx) (leanSim pI) b side γ x with _ | ⟨i, w'⟩
  · simp [hx] at h
  · simp only [hx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hrel := stwA_rel (A := A) (idx := idx) (leanSim pI) b side γ x i w' hx
    have hi : i = xROf A.ctxRO (ptA (A := A) (idx := idx) (leanSim pI) b γ x side) := by
      unfold stwA at hx
      split_ifs at hx
      · simp only [Option.some.injEq, Prod.mk.injEq] at hx
        exact hx.1.symm
    subst hi
    exact ⟨rfl, zkHypR _ _ hrel⟩

/-- A real redemption that changes with the programming changes the Lean prover's output. -/
lemma PA_ne {α : Type} (b side : Bool) (γ : (TIs (SimCoins pI) × TIs (SimCoins pI)) × α)
    (x : Trans) (ρ : Coins proveSeedBytes) (g : Tab3) (u u' : ShM R)
    (h : PA (A := A) (idx := idx) (leanSim pI) leanPR b side γ x ρ g u ≠
      PA (A := A) (idx := idx) (leanSim pI) leanPR b side γ x ρ g u') :
    (stwL A idx b side γ x).elim False fun sw =>
      realRO pR Hashes.shake sw.1 sw.2 ρ g u ≠ realRO pR Hashes.shake sw.1 sw.2 ρ g u' := by
  unfold PA at h
  split_ifs at h with hok
  · have hf := (redeem_factsA (A := A) (idx := idx) (leanSim pI) (leanSim pR) leanPR b side γ x
      hok).2.1 (ρ, g)
    rw [hf, hf, leanPR_ofFn, leanPR_ofFn] at h
    have hs : stwL A idx b side γ x = some (stR (xROf A.ctxRO (ptA (A := A) (idx := idx)
        (leanSim pI) b γ x side)), toBA (wROf A.ctxRO (ptA (A := A) (idx := idx) (leanSim pI) b γ x
          side))) := by
      simp only [stwL, stwA, hok, ↓reduceIte, Option.map_some]
    rw [hs]
    intro e
    exact h (by rw [e])
  · exact absurd rfl h

/-- **The collision term of hop L**, with the statement read off the tables:
`δL b ≤ i₃·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607, i₅ + 624, i_E + 9214) + noHitProb + 2·2⁻¹⁰²⁴`. -/
theorem deltaLA_le [ZKPRow R] {i3 i2 i5 iE : ℕ} (hI : A.IBudget i3 i2 i5 iE) (b : Bool) :
    deltaLA (A := A) (idx := idx) (simI := leanSim pI) (progI := leanProgI) (PR := leanPR) b ≤
      i3 / 2 ^ 128 + (1 / 2 ^ 113 + ZKPRow.εP R pR 0 312 4607 (i5 + 312 + 312) (iE + 4607 + 4607) +
        (noHitProb + 2 / 2 ^ 1024)) := by
  unfold deltaLA
  refine pr_le_of_fst fun γ => ?_
  refine (pr_mono fun z hz => PA_ne A idx b false γ _ z.1 z.2.1 _ _ hz).trans ?_
  refine (pr_collide_adaptive Hashes.shake pR rfl smallParams_pR hashesWF_shake
    (stwL A idx b false γ)
    (fun x => csR (xROf A.ctxRO (ptA (A := A) (idx := idx) (leanSim pI) b γ x false)))
    (stwL_hyp A idx b false γ) (SxL (A := A) (leanSim pI) leanProgI γ) (sReads_SxL A hI γ)
    (fun _ => PIOf A.ctxRO leanProgI γ) _ (fun _ => progAt_PIOf A.ctxRO γ) _
    (fun _ => tails_PIOf A.ctxRO γ)).trans ?_
  have hc : (({simTail γ.1.1.2.1, simTail γ.1.2.2.1} : Finset ByteArray).card : ℝ) ≤ 2 := by
    exact_mod_cast Finset.card_le_two
  rw [tail_pR]
  gcongr

/-- **The collision term of hop R**: `δR b ≤ i₃·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607, i₅ + 624,
i_E + 9214) + noHitProb + 3·2⁻¹⁰²⁴`. -/
theorem deltaRA_le [ZKPRow R] {i3 i2 i5 iE : ℕ} (hI : A.IBudget i3 i2 i5 iE) (b : Bool) :
    deltaRA (A := A) (idx := idx) (simI := leanSim pI) (progI := leanProgI) (progR := leanProgR)
        (PR := leanPR) b ≤
      i3 / 2 ^ 128 + (1 / 2 ^ 113 + ZKPRow.εP R pR 0 312 4607 (i5 + 312 + 312) (iE + 4607 + 4607) +
        (noHitProb + 3 / 2 ^ 1024)) := by
  unfold deltaRA
  refine pr_le_of_fst fun γ => ?_
  refine (pr_mono fun z hz => PA_ne A idx b true γ _ z.1 z.2.1 _ _ hz).trans ?_
  -- The programming before the right redemption's, at three blocks.
  let Bx : Trans → ShM R → Finset (Bytes (preLen pI)) := fun x s =>
    {simBlk Hashes.shake (stI (xIOf A.ctxRO γ.1.1.1)) γ.1.1.2.1
        (progRO pI Hashes.shake (stI (xIOf A.ctxRO γ.1.2.1)) γ.1.2.2.1
          (progA (A := A) (idx := idx) (leanSim pI) leanProgR b false γ x γ.2.1 s))} ∪
      {simBlk Hashes.shake (stI (xIOf A.ctxRO γ.1.2.1)) γ.1.2.2.1
        (progA (A := A) (idx := idx) (leanSim pI) leanProgR b false γ x γ.2.1 s)} ∪
      (if okA (A := A) (idx := idx) (leanSim pI) γ x = true then
        {simBlk Hashes.shake (stR (xROf A.ctxRO (ptA (A := A) (idx := idx) (leanSim pI) b γ x false)))
          γ.2.1 s} else ∅)
  have hL : ∀ x, ProgAt (LRA (A := A) (idx := idx) (leanSim pI) leanProgI leanProgR b γ x) (Bx x) :=
    fun x => (progAt_PIOf A.ctxRO γ).comp (ProgAt.ite (okA (A := A) (idx := idx) (leanSim pI) γ x =
      true) (progRO_progAt (R := R) Hashes.shake _ γ.2.1))
  have hT : ∀ x s, ∀ b' ∈ Bx x s, preTail b' ∈
      ({simTail γ.2.1, simTail γ.1.1.2.1, simTail γ.1.2.2.1} : Finset ByteArray) := by
    intro x s b' hb
    rcases Finset.mem_union.1 hb with hb | hb
    · exact Finset.mem_insert.2 (Or.inr (tails_PIOf A.ctxRO γ _ b' hb))
    · by_cases hc : okA (A := A) (idx := idx) (leanSim pI) γ x = true
      · simp only [hc, ↓reduceIte] at hb
        rw [Finset.mem_singleton.1 hb]
        exact Finset.mem_insert.2 (Or.inl (preTail_simBlk hashesWF_shake rfl _ _))
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hb
        exact absurd hb (Finset.notMem_empty _)
  refine (pr_collide_adaptive Hashes.shake pR rfl smallParams_pR hashesWF_shake
    (stwL A idx b true γ)
    (fun x => csR (xROf A.ctxRO (ptA (A := A) (idx := idx) (leanSim pI) b γ x true)))
    (stwL_hyp A idx b true γ) (SxR (A := A) (leanSim pI) leanProgI γ) (sReads_SxR A hI γ)
    (LRA (A := A) (idx := idx) (leanSim pI) leanProgI leanProgR b γ) Bx hL _ hT).trans ?_
  have hc : (({simTail γ.2.1, simTail γ.1.1.2.1, simTail γ.1.2.2.1} :
      Finset ByteArray).card : ℝ) ≤ 3 := by
    exact_mod_cast Finset.card_le_three
  rw [tail_pR]
  gcongr

/-- **Theorem 4(a) with the Lean prover, the adversary's interaction reading the tables, for every
type of cipher rows** (`ZKPRow R`; `anonymityRA_lean_num` at function rows). The guess reads each `H₃`
slice at `q₃` keys, `H₅` at `q₅`, the cipher at `q_E` and `H₂³` freely; the interaction (the
responses, the Anchor Sets and digests) reads, as a function of each slice and the shared tables,
at most `i₃` slice keys, `i₂` `H₂³` keys, `i₅` `H₅` keys and `i_E` cipher keys, consistently. Then
the two worlds differ by at most

    4·εRO(i₃ + q₃, q₅ + i₅ + 1872, q_E + i_E + 13821)
      + 4·εAd(9; q₃, q₅ + 1248, q_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214)
      + 4·(i₃·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607; i₅ + 624, i_E + 9214))
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

The issuance hops pay the interaction's reads as the distinguisher's (`εRO`); the redemption hops
are the adaptive theorem (`εAd`), the transcript reading the tables through the two issuance
simulations' programming (`+ 2·312`, `+ 2·4607`); the collision terms of the redemption hops are
the adaptive collision bound. -/
theorem anonymityRA_lean_numG [ZKRow R] [ZKPRow R] {q3 q5 qE i3 i2 i5 iE : ℕ} {εhide : ℝ} (hA : A.GBudget q3 q5 qE)
    (hI : A.IBudget i3 i2 i5 iE)
    (hhide : ∀ b c, hidingAdv A.ctxRO.base.ci A.ctxRO.base.cr
      (reductionRA A idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRA A idx leanPI leanPR false) - pr _ (realGameRA A idx leanPI leanPR true)| ≤
      4 * ZKRow.εz R pI (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) +
        4 * εAdG R pR 9 q3 (q5 + 1248) (qE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        4 * (i3 / 2 ^ 128 + 1 / 2 ^ 113 + ZKPRow.εP R pR 0 312 4607 (i5 + 624) (iE + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide := by
  have hPI5 : ∀ w x rho g, Rd5 (leanPI (R := R) w x rho g) 624 := fun w x rho g =>
    (realROb_rd5 (p := pI) (Hb := Hashes.shake) (st := stI x) (w := toBA w) (toBA rho) g).map
      fun o => toL (o.toOption.getD .empty)
  have hPIE : ∀ w x rho g, RdE (leanPI (R := R) w x rho g) 4607 := fun w x rho g =>
    (realROb_rdE (p := pI) (st := stI x) (w := toBA w) hashesWF_shake (toBA rho) g).map
      fun o => toL (o.toOption.getD .empty)
  have hPR5 : ∀ w x rho g, Rd5 (leanPR (R := R) w x rho g) 624 := fun w x rho g =>
    (realROb_rd5 (p := pR) (Hb := Hashes.shake) (st := stR x) (w := toBA w) (toBA rho) g).map
      fun o => toL (o.toOption.getD .empty)
  have hPRE : ∀ w x rho g, RdE (leanPR (R := R) w x rho g) 4607 := fun w x rho g =>
    (realROb_rdE (p := pR) (st := stR x) (w := toBA w) hashesWF_shake (toBA rho) g).map
      fun o => toL (o.toOption.getD .empty)
  have h := anonymityRA (A := A) (idx := idx) (PI := leanPI) (PR := leanPR) (simI := leanSim pI)
    (simR := leanSim pR) (progI := leanProgI) (progR := leanProgR)
    (εI := fun a c => ZKRow.εz R pI (i3 + q3) a c)
    (εR := fun a c => εAdG R pR pR.qsDegree q3 a c i3 i2 (i5 + 312 + 312) (iE + 4607 + 4607))
    (AdmS := fun _ Sx => SReads pR Sx i3 i2 (i5 + 312 + 312) (iE + 4607 + 4607))
    hA hI hPI5 hPIE hPR5 hPRE (fun x c => progRO_isProg c) (fun x c => progRO_isProg c)
    (sReads_SxL A hI) (sReads_SxR A hI) (fun a c => leanPI_zkRO (i3 + q3) a c)
    (fun a c => leanPR_zkROA q3 a c i3 i2 (i5 + 312 + 312) (iE + 4607 + 4607)) hhide
  have mI : ∀ a c, a ≤ q5 + i5 + 1872 → c ≤ qE + iE + 13821 →
      ZKRow.εz R pI (i3 + q3) a c ≤ ZKRow.εz R pI (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) :=
    fun a c ha hc => ZKRow.εz_mono pI le_rfl ha hc
  have mR : ∀ a c, a ≤ q5 + 1248 → c ≤ qE + 13821 →
      εAdG R pR pR.qsDegree q3 a c i3 i2 (i5 + 312 + 312) (iE + 4607 + 4607) ≤
        εAdG R pR 9 q3 (q5 + 1248) (qE + 13821) i3 i2 (i5 + 624) (iE + 9214) :=
    fun a c ha hc => εAdG_mono pR le_rfl ha hc le_rfl le_rfl (by omega) (by omega)
  have m1 := mI (624 + (i5 + (624 + 624 + q5))) (4607 + (iE + (4607 + 4607 + qE))) (by omega)
    (by omega)
  have m2 := mI (i5 + (624 + 624 + q5) + 312) (iE + (4607 + 4607 + qE) + 4607) (by omega) (by omega)
  have m3 := mR (0 + 624 + q5 + (312 + 312)) (0 + 4607 + qE + (4607 + 4607)) (by omega) (by omega)
  have m4 := mR (0 + 0 + q5 + (312 + (312 + 312))) (0 + 0 + qE + (4607 + (4607 + 4607))) (by omega)
    (by omega)
  have d1 := deltaI1_le A.ctxRO
  have dL0 := deltaLA_le A idx hI false
  have dL1 := deltaLA_le A idx hI true
  have dR0 := deltaRA_le A idx hI false
  have dR1 := deltaRA_le A idx hI true
  have e1 : ZKPRow.εP R pR 0 312 4607 (i5 + 312 + 312) (iE + 4607 + 4607) =
      ZKPRow.εP R pR 0 312 4607 (i5 + 624) (iE + 9214) := by
    rw [show i5 + 312 + 312 = i5 + 624 by omega, show iE + 4607 + 4607 = iE + 9214 by omega]
  rw [e1] at dL0 dL1 dR0 dR1
  refine h.trans ?_
  rw [div_eq_mul_one_div (2 : ℝ) ((2 : ℝ) ^ 1024)] at dL0 dL1
  rw [div_eq_mul_one_div (3 : ℝ) ((2 : ℝ) ^ 1024)] at dR0 dR1
  rw [div_eq_mul_one_div (12 : ℝ) ((2 : ℝ) ^ 1024)]
  generalize (1 : ℝ) / 2 ^ 1024 = κ at d1 dL0 dL1 dR0 dR1 ⊢
  linarith

/-- **Theorem 4(a) with the Lean prover, in the random-oracle and ideal-cipher model, the
adversary's interaction reading the tables, with every term explicit.** The guess reads each `H₃`
slice at `q₃` keys, `H₅` at `q₅`, the cipher at `q_E` and `H₂³` freely; the interaction (the
responses, the Anchor Sets and digests) reads, as a function of each slice and the shared tables,
at most `i₃` slice keys, `i₂` `H₂³` keys, `i₅` `H₅` keys and `i_E` cipher keys, consistently. Then
the two worlds differ by at most

    4·εRO(i₃ + q₃, q₅ + i₅ + 1872, q_E + i_E + 13821)
      + 4·εAd(9; q₃, q₅ + 1248, q_E + 13821; i₃, i₂, i₅ + 624, i_E + 9214)
      + 4·(i₃·2⁻¹²⁸ + 2⁻¹¹³ + εROP(0, 312, 4607; i₅ + 624, i_E + 9214))
      + 6·noHitProb + 12·2⁻¹⁰²⁴ + 2·εhide.

The issuance hops pay the interaction's reads as the distinguisher's (`εRO`); the redemption hops
are the adaptive theorem (`εAd`), the transcript reading the tables through the two issuance
simulations' programming (`+ 2·312`, `+ 2·4607`); the collision terms of the redemption hops are
the adaptive collision bound. (`anonymityRA_lean_numG` at function rows.) -/
theorem anonymityRA_lean_num (A : AdversaryRA (Blk → Blk)) {q3 q5 qE i3 i2 i5 iE : ℕ} {εhide : ℝ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i2 i5 iE)
    (hhide : ∀ b c, hidingAdv A.ctxRO.base.ci A.ctxRO.base.cr
      (reductionRA A idx (leanSim pI) (leanSim pR) leanProgI leanProgR b c) ≤ εhide) :
    |pr _ (realGameRA A idx leanPI leanPR false) - pr _ (realGameRA A idx leanPI leanPR true)| ≤
      4 * εRO (i3 + q3) (q5 + i5 + 1872) (qE + iE + 13821) +
        4 * εAd 9 q3 (q5 + 1248) (qE + 13821) i3 i2 (i5 + 624) (iE + 9214) +
        4 * (i3 / 2 ^ 128 + 1 / 2 ^ 113 + εROP 0 312 4607 (i5 + 624) (iE + 9214)) +
        6 * noHitProb + 12 / 2 ^ 1024 + 2 * εhide :=
  anonymityRA_lean_numG A idx hA hI hhide

end Lean

end VoleMole.Privacy.Moussaka
