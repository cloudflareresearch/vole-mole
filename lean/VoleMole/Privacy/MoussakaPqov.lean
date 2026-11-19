import VoleMole.Privacy.MoussakaNCSh
import VoleMole.Privacy.SeedXOFNC
import VoleMole.ZK.CompleteRO
import VoleMole.Spec.PqovSigner

/-!
# Theorem 4(b′) with pqov's signer, and completeness of the honest Anchors' verification

The non-colluding games (`Privacy/MoussakaNC.lean`, `MoussakaNCRO.lean`, `MoussakaNCSh.lean`)
take the Anchors' signers abstract (`Spec.Signer`, `Signer.Correct` their only hypothesis), so
their abort term `2·(φ₀ + φ₁)` is not bounded for any concrete signer, and the theorems hold for
any issuance verifier, so they do not show that the redemptions take place. This file supplies both.

## The issuance request length (a modelling fix)

`Spec.Moussaka.issueResponse` checks `main`'s request length `45 + 7272`; the Lean issuance prover
of the random-oracle games (dedicated label rows) emits `7528`-byte proofs (`leanPI_length`). So
with `main`'s Anchor **every** honest request of those games is rejected as malformed
(`issueResponse_leanPI_malformed`), the refusal is certain and the games are vacuous. The games
now use the label-row Anchor `issueResponseLR` (`Spec/MoussakaLabelRows.lean`, `45 + 7528`), and
completeness below shows that they reach redemption.

## Completeness (`leanI_complete`, `accNC_lean_complete`, `pr_refused_NCRO_le`)

* `leanI_complete`: for every issuance instance and witness in the relation, over the prover's
  randomness, its `H₃` slice and the shared tables (`H₂³`, `H₅`, any cipher table), the Lean
  prover's proof fails to have `7528` bytes or is rejected by the Anchors' Lean verifier
  `leanVI` on the same tables with probability `≤ 2⁻¹¹³` (`ZK.Sim.complete_rom`, the verifier
  reading no `H₃`).
* `accNC_lean_complete`, `accNC_leanSh_complete` (one shared `H₃`, the slice at the prefix
  uniform): so in the games each honest Anchor rejects its Client's request with probability
  `≤ 2⁻¹¹³`.
* `pr_refused_le` (any issuance prover with such a bound), **`pr_refused_NCRO_le`**,
  **`pr_refused_NCSh_le`**: when both issuers' keys are found at the Clients' indices in both
  sets (`foundNC`), the games of `anonymityNCRO_lean_num` and `anonymityNCSh_num` refuse the
  redemptions with probability `≤ φ₀ + φ₁ + 2·2⁻¹¹³`; `pr_refused_NCRO_pqov`: with pqov's signers
  averaged over the vinegar tables, `≤ δ₀²⁵⁵ + δ₁²⁵⁵ + 2·2⁻¹¹³`.

## pqov's signer (`Spec/PqovSigner.lean`)

* `pqovRO pk O w c`: Anchor `c`'s `derive_preimage` (`Spec.Pqov.signer`, 255 attempts as in pqov)
  with its vinegars read from the vinegar table `w c` at the target's key (SHAKE256 as a random
  oracle, as in `anonymityNC_vinegarRO`). It is correct for `pk c` when `P` vanishes on the oil
  space (`OilSpace`, `pqovRO_correct`) and fails only if the first 255 vinegars all give a
  singular system (`pqovRO_fail`), i.e. `hfail` with 255 in place of 256.
* `anonymityNC_pqov`, `anonymityNCRO_pqov`, `anonymityNCSh_pqov`: the abort term is
  `2·(δ₀²⁵⁵ + δ₁²⁵⁵)` on average over the vinegar tables, `δ_c` the fraction of vinegars whose
  system `L_v` is singular for Anchor `c`'s key (`pr_fail_vinegar_lt`).
* `pqovRO256_hfail`: the signer with all 256 attempts satisfies the original `hfail`, so
  `anonymityNC_vinegarRO` applies to it as stated (`Audit/Nonvacuous.lean`).
* The bounds on `δ` (on average over the key, `E[δ²⁵⁵] ≈ 2⁻²⁹⁵·⁸` for pqov's key generation with
  `O = 0`) and the key-averaged theorems are in `Privacy/PqovDelta.lean`.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Verifier

/-- **A proof the prover returns has the parameters' size.** -/
theorem proveCommit_ok_size [HasPrg] {Hs : Hashes} {st : Statement} {wS : ByteArray}
    {s : Prover.Pending} {b : ByteArray} (h : Prover.proveCommit Hs st wS s = .ok b) :
    b.size = s.params.proofBytes := by
  unfold Prover.proveCommit at h
  simp only at h
  split_ifs at h with hw
  · cases h
  · generalize Prover.qsProve _ _ _ _ _ _ _ = q at h
    cases q with
    | error e => cases h
    | ok r =>
      obtain ⟨check, aT⟩ := r
      simp only [bind, Except.bind] at h
      generalize Prover.findFirst _ _ _ = ff at h
      cases ff with
      | none => cases h
      | some t =>
        obtain ⟨ctr, delta, opening⟩ := t
        simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [← h]
        exact (Bridge.fields_assemble _ _).2.2.2.2.2.2.2.2.2

theorem prove_ok_size [HasPrg] {Hs : Hashes} {T : CrtTables} {st : Statement} {w rho : ByteArray}
    {n : ℕ} {b : ByteArray} (h : Prover.prove Hs T st w rho n = .ok b) :
    b.size = st.params.proofBytes := by
  unfold Prover.prove at h
  rw [proveCommit_ok_size h]
  rfl

lemma toBA_toL (b : ByteArray) : toBA (toL b) = b := by
  rw [Privacy.toL_eq]
  cases b
  rfl

end VoleMole.Verifier

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

attribute [local irreducible] com UOVKey.eval

/-! ## The label-row proof length -/

/-- The label-row issuance parameters' proof size. -/
theorem pI_proofBytes : pI.proofBytes = issueProofBytesLR := by decide

section Length

variable {R : Type} [CipherRow R]

/-- **The Lean issuance prover's output has `0` or `7528` bytes.** -/
theorem leanPI_length (w : Bytes) (x : IssueInstance) (rho : Bytes) (g : Tab3) (s : ShM R) :
    (leanPI w x rho g s).length = 0 ∨ (leanPI w x rho g s).length = issueProofBytesLR := by
  unfold leanPI
  cases h : realROb pI Hashes.shake (stI x) (toBA w) (toBA rho) g s with
  | error e => left; simp [Except.toOption, length_toL, ByteArray.size]
  | ok b =>
    right
    simp only [Except.toOption, Option.getD_some, length_toL]
    exact (@prove_ok_size (icPrg (rowFn s.2.2)) _ _ _ _ _ _ _ h).trans pI_proofBytes

/-- **With `main`'s Anchor every request of the label-row prover is malformed**: its length is
`45` or `45 + 7528`, never `45 + 7272`. (This is why the games use `issueResponseLR`.) -/
theorem issueResponse_leanPI_malformed (V : VerifierRO R) (sk : Signer) (t w : Bytes)
    (x : IssueInstance) (rho : Bytes) (g : Tab3) (s : ShM R) (ci : Bytes) (ht : t.length = uovM) :
    issueResponse (nizkV leanPI V g s) sk (t ++ leanPI w x rho g s) ci = .error .malformed := by
  have hl : (t ++ leanPI w x rho g s).length ≠ issueRequestBytes := by
    rw [List.length_append, ht]
    rcases leanPI_length w x rho g s with h | h <;> rw [h] <;> decide
  have h' : (t ++ leanPI w x rho g s).length ≠ issueRequestBytes ∨ ci.length ≠ ctxBytes := Or.inl hl
  unfold issueResponse
  simp only [h', ↓reduceIte]

end Length

/-! ## Completeness of the honest Anchors' verification -/

section Complete

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

lemma recH_agreeOff_recV (Hb : Hashes) (st : Statement) (w : ByteArray) (G3 : Tab3)
    (G2 : Tab2G st.params) (G5 : Tab5F) :
    (recH Hb st w G3 G2 G5).AgreeOff .h3 (recV st.params Hb G2 G5) := by
  intro k hk
  funext y
  by_cases h5 : k = .h5
  · subst h5
    simp only [recH, recV, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
    congr 1
  by_cases h23 : k = .h23
  · subst h23; simp only [recH, recV, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
  · simp only [recH, recV, Hashes.withTable, h5, h23, hk, ite_false]

/-- The coins of one issuance proof and the shared tables, rearranged as in `complete_rom`. -/
def cplEquiv : ((VoleMole.ZK.Sim.Bytes 16 × Tab2G pI) × (Tab3 × Tab5F)) × (Blk → R) ≃
    (Coins proveSeedBytes × Tab3) × ShM R where
  toFun z := ((z.1.1.1, z.1.2.1), (z.1.1.2, z.1.2.2, z.2))
  invFun z := (((z.1.1, z.2.1), (z.1.2, z.2.2.1)), z.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Completeness of the Lean issuance proofs under the honest Anchors' Lean verifier on the
shared tables**: for every instance and witness in the relation, over the prover's randomness, its
`H₃` slice, `H₂³`, `H₅` (uniform) and any cipher table, the proof has the label-row length and
`leanVI` accepts it, except with probability `≤ 2⁻¹¹³`. -/
theorem leanI_complete (x : IssueInstance) (w : Bytes) (hw : IssueRelW x w) :
    pr ((Coins proveSeedBytes × Tab3) × ShM R) (fun z =>
      ¬ ((leanPI w x (List.ofFn z.1.1) z.1.2 z.2).length = issueProofBytesLR ∧
        leanVI (leanPI w x (List.ofFn z.1.1) z.1.2 z.2) x z.2 = true)) ≤ 1 / 2 ^ 113 := by
  rw [← pr_equiv cplEquiv]
  refine pr_le_of_snd fun E => ?_
  have h := @moussakaIssue_complete_rom (icPrg (rowFn E)) Hashes.shake hashesWF_shake x w hw
  refine (pr_mono fun c hc => ?_).trans h
  intro hex
  obtain ⟨proof, hp, hv⟩ := hex
  apply hc
  have hpf : leanPI w x (List.ofFn (cplEquiv (c, E)).1.1) (cplEquiv (c, E)).1.2
      (cplEquiv (c, E)).2 = toL proof := by
    rw [leanPI_ofFn]
    exact congrArg (fun o : Except String ByteArray => toL (o.toOption.getD .empty)) hp
  rw [hpf, length_toL]
  refine ⟨(@prove_ok_size (icPrg (rowFn E)) _ _ _ _ _ _ _ hp).trans pI_proofBytes, ?_⟩
  have hv' := hv
  rw [@verify_agreeOff_h3 (icPrg (rowFn E)) _ _ (recH_agreeOff_recV Hashes.shake (stI x)
    (toBA w) c.2.1 c.1.2 c.2.2)] at hv'
  unfold leanVI verRO
  rw [toBA_toL]
  exact hv'

/-- The honest Client's issuance witness is in the relation. -/
lemma issueRelW_honest (A : AdversaryNCRO R) (n : NR) :
    IssueRelW ⟨tNC A.nc (n.1, n.2, fun _ => 0), A.nc.base.ci⟩
      (encodeIssueWitness (List.ofFn n.1) A.nc.base.ci A.nc.base.cr (List.ofFn n.2)) :=
  ⟨⟨List.ofFn n.1, List.ofFn n.2, A.nc.base.cr, by simp, by simp, by simp [Adversary.cr], rfl, rfl⟩,
    length_ci A.nc⟩

variable (A : AdversaryNCRO R) (idx : AnchorSet → UOVKey → ℕ) (sk : Bool → Signer)

/-- `TIr × ShM R ≃ NR × ((ρ, slice) × ShM R)`. -/
def tirEquiv : NR × ((Coins proveSeedBytes × Tab3) × ShM R) ≃ TIr × ShM R where
  toFun z := ((z.1, z.2.1), z.2.2)
  invFun z := (z.1.1, (z.1.2, z.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Each honest Anchor accepts its Client's request** except with probability `≤ 2⁻¹¹³`. -/
theorem accNC_lean_complete :
    pr (TIr × ShM R) (fun z => accNC A.nc (nizkV leanPI leanVI z.1.2.2 z.2)
      (issNC A leanPI leanVI z.1 z.2).2 = false) ≤ 1 / 2 ^ 113 := by
  rw [← pr_equiv tirEquiv]
  refine pr_le_of_fst fun n => ?_
  refine (pr_mono fun z hz => ?_).trans (leanI_complete (R := R) _ _ (issueRelW_honest A n))
  rintro ⟨hl, hv⟩
  set t := tNC A.nc (n.1, n.2, fun _ => 0) with htdef
  have ht : t.length = uovM := length_com _ _ _ _
  have hq : (issNC A leanPI leanVI (tirEquiv (n, z)).1 (tirEquiv (n, z)).2).2 =
      t ++ leanPI (encodeIssueWitness (List.ofFn n.1) A.nc.base.ci A.nc.base.cr (List.ofFn n.2))
        ⟨t, A.nc.base.ci⟩ (List.ofFn z.1.1) z.1.2 z.2 := rfl
  have hacc : accNC A.nc (nizkV leanPI leanVI (tirEquiv (n, z)).1.2.2 (tirEquiv (n, z)).2)
      (issNC A leanPI leanVI (tirEquiv (n, z)).1 (tirEquiv (n, z)).2).2 = true := by
    rw [hq]
    unfold accNC
    rw [take_append_eq ht, drop_append_eq ht]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_append, ht, hl]
    exact ⟨trivial, hv⟩
  exact absurd hz (by rw [hacc]; decide)

end Complete

/-! ### The games reach redemption -/

section Refusal

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]
variable (A : AdversaryNCRO R) (idx : AnchorSet → UOVKey → ℕ) (sk : Bool → Signer)

/-- The marginal of Client `false`'s tape and the tables. -/
lemma pr_tape₀ (Q : TIr × ShM R → Prop) :
    pr (((TIr × TIr) × (TRr × TRr)) × ShM R) (fun x => Q (x.1.1.1, x.2)) = pr (TIr × ShM R) Q := by
  let e : (TIr × ShM R) × (TIr × (TRr × TRr)) ≃ ((TIr × TIr) × (TRr × TRr)) × ShM R :=
    { toFun := fun a => (((a.1.1, a.2.1), a.2.2), a.1.2)
      invFun := fun x => ((x.1.1.1, x.2), (x.1.1.2, x.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  exact pr_prod_fst Q

/-- The marginal of Client `true`'s tape and the tables. -/
lemma pr_tape₁ (Q : TIr × ShM R → Prop) :
    pr (((TIr × TIr) × (TRr × TRr)) × ShM R) (fun x => Q (x.1.1.2, x.2)) = pr (TIr × ShM R) Q := by
  let e : (TIr × ShM R) × (TIr × (TRr × TRr)) ≃ ((TIr × TIr) × (TRr × TRr)) × ShM R :=
    { toFun := fun a => (((a.2.1, a.1.1), a.2.2), a.1.2)
      invFun := fun x => ((x.1.1.2, x.2), (x.1.1.1, x.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  exact pr_prod_fst Q

/-- `derive_preimage` fails on a Client's commitment with probability `φ`. -/
lemma pr_derive_tir (c : Bool) :
    pr (TIr × ShM R) (fun z => (sk c).derivePreimage (tNC A.nc (issCoins z.1)) = none) =
      phi A.nc sk c := by
  rw [pr_prod_fst (fun y : TIr => (sk c).derivePreimage (tNC A.nc (issCoins y)) = none)]
  exact pr_prod_fst (fun n : NR => (sk c).derivePreimage (tNC A.nc (n.1, n.2, fun _ => 0)) = none)

/-- The event that the honest Anchor rejects its Client's request (issuance prover `PI`, the Lean
verifier on the tables). -/
def RejNC (PI : ProverRO R IssueInstance) (z : TIr × ShM R) : Prop :=
  accNC A.nc (nizkV PI leanVI z.1.2.2 z.2) (issNC A PI leanVI z.1 z.2).2 = false

/-- **The games reach redemption, for any issuance prover with an acceptance bound**: if both
issuers' keys are found at the Clients' indices in both sets and each honest Anchor rejects its
Client's request with probability `≤ ε`, the redemptions are refused with probability
`≤ φ₀ + φ₁ + 2ε`. -/
theorem pr_refused_le (PI : ProverRO R IssueInstance) {ε : ℝ}
    (hacc : pr (TIr × ShM R) (RejNC A PI) ≤ ε) (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hidx : IdxSound idx) (hK : ∀ c side, foundNC A.nc idx c side = true) :
    pr (((TIr × TIr) × (TRr × TRr)) × ShM R) (fun x =>
      (goodNC A.nc idx (nizkC PI leanVI x false) sk false (issC A PI leanVI x false) &&
        goodNC A.nc idx (nizkC PI leanVI x true) sk true (issC A PI leanVI x true)) = false) ≤
      phi A.nc sk false + phi A.nc sk true + 2 * ε := by
  let D : Bool → TIr × ShM R → Prop := fun c z =>
    (sk c).derivePreimage (tNC A.nc (issCoins z.1)) = none
  have hsub : ∀ x : ((TIr × TIr) × (TRr × TRr)) × ShM R,
      (goodNC A.nc idx (nizkC PI leanVI x false) sk false (issC A PI leanVI x false) &&
        goodNC A.nc idx (nizkC PI leanVI x true) sk true (issC A PI leanVI x true)) = false →
      ((D false (x.1.1.1, x.2) ∨ D true (x.1.1.2, x.2)) ∨
        (RejNC A PI (x.1.1.1, x.2) ∨ RejNC A PI (x.1.1.2, x.2))) := by
    intro x hx
    by_contra hn
    simp only [not_or] at hn
    obtain ⟨⟨hd₀, hd₁⟩, hr₀, hr₁⟩ := hn
    have g₀ := good_eq_of_derive A.nc idx (nizkC PI leanVI x false) sk hsk hidx false
      (issCoins x.1.1.1) hd₀
    have g₁ := good_eq_of_derive A.nc idx (nizkC PI leanVI x true) sk hsk hidx true
      (issCoins x.1.1.2) hd₁
    have e₀ : issC A PI leanVI x false =
        issReal A.nc.base (nizkC PI leanVI x false) (issCoins x.1.1.1) := rfl
    have e₁ : issC A PI leanVI x true =
        issReal A.nc.base (nizkC PI leanVI x true) (issCoins x.1.1.2) := rfl
    rw [e₀, e₁, g₀, g₁, hK, hK, hK, hK] at hx
    simp only [Bool.and_true, Bool.and_eq_false_iff] at hx
    rcases hx with h | h
    · exact hr₀ h
    · exact hr₁ h
  refine (pr_mono hsub).trans ((pr_or_le _ _).trans ?_)
  have h1 := pr_or_le (fun x : ((TIr × TIr) × (TRr × TRr)) × ShM R => D false (x.1.1.1, x.2))
    (fun x => D true (x.1.1.2, x.2))
  have h2 := pr_or_le (fun x : ((TIr × TIr) × (TRr × TRr)) × ShM R => RejNC A PI (x.1.1.1, x.2))
    (fun x => RejNC A PI (x.1.1.2, x.2))
  rw [pr_tape₀, pr_tape₁] at h1 h2
  rw [show pr (TIr × ShM R) (D false) = phi A.nc sk false from pr_derive_tir A sk false,
    show pr (TIr × ShM R) (D true) = phi A.nc sk true from pr_derive_tir A sk true] at h1
  linarith

/-- **The games reach redemption.** In the game of `anonymityNCRO_lean_num` (the Lean issuance
prover, the honest Anchors' Lean verifier on the shared tables, any signers correct for their keys,
a sound index rule), if both issuers' keys are found at the Clients' indices in both sets, the
redemptions are refused with probability `≤ φ₀ + φ₁ + 2·2⁻¹¹³`: an issuance fails only if an
Anchor's `derive_preimage` fails or its verification rejects the honest request
(`accNC_lean_complete`). -/
theorem pr_refused_NCRO_le (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx)
    (hK : ∀ c side, foundNC A.nc idx c side = true) :
    pr (((TIr × TIr) × (TRr × TRr)) × ShM R) (fun x =>
      (goodNC A.nc idx (nizkC leanPI leanVI x false) sk false (issC A leanPI leanVI x false) &&
        goodNC A.nc idx (nizkC leanPI leanVI x true) sk true (issC A leanPI leanVI x true)) =
          false) ≤
      phi A.nc sk false + phi A.nc sk true + 2 / 2 ^ 113 := by
  have h := pr_refused_le A idx sk leanPI (accNC_lean_complete A) hsk hidx hK
  have e : (2 : ℝ) * (1 / 2 ^ 113) = 2 / 2 ^ 113 := by ring
  linarith

end Refusal

/-! ### With one shared `H₃` -/

section ShComplete

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-- **Each honest Anchor accepts its Client's request with one shared `H₃`** (the issuance proof
reading its slice off the shared tables at its prefix, `leanPISh`) except with probability
`≤ 2⁻¹¹³`: the slice at the prefix is uniform (`pr_h3At_slice`). -/
theorem accNC_leanSh_complete (A : AdversaryNCRO (RowH R)) :
    pr (TIr × ShM (RowH R)) (RejNC A leanPISh) ≤ 1 / 2 ^ 113 := by
  rw [← pr_equiv tirEquiv]
  let W : NR → Bytes := fun n =>
    encodeIssueWitness (List.ofFn n.1) A.nc.base.ci A.nc.base.cr (List.ofFn n.2)
  let X : NR → IssueInstance := fun n => ⟨tNC A.nc (n.1, n.2, fun _ => 0), A.nc.base.ci⟩
  let C : NR → Coins proveSeedBytes → Tab3 → ShM (RowH R) → Prop := fun n ρ G s =>
    ¬ ((leanPI (W n) (X n) (List.ofFn ρ) G s).length = issueProofBytesLR ∧
      leanVI (leanPI (W n) (X n) (List.ofFn ρ) G s) (X n) s = true)
  have hC : ∀ n ρ G s k g, C n ρ G (setK s k g) ↔ C n ρ G s := fun _ _ _ _ _ _ => Iff.rfl
  have hsl := pr_h3At_slice (fun n => keyI (W n) (X n)) C hC
  refine (pr_mono fun z hz => ?_).trans ((le_of_eq hsl).trans ?_)
  · show C z.1 z.2.1.1 (h3At z.2.2 (keyI (W z.1) (X z.1))) z.2.2
    rintro ⟨hl, hv⟩
    have ht : (tNC A.nc (z.1.1, z.1.2, fun _ => 0)).length = uovM := length_com _ _ _ _
    have hq : (issNC A leanPISh leanVI (tirEquiv z).1 (tirEquiv z).2).2 =
        tNC A.nc (z.1.1, z.1.2, fun _ => 0) ++ leanPI (W z.1) (X z.1) (List.ofFn z.2.1.1)
          (h3At z.2.2 (keyI (W z.1) (X z.1))) z.2.2 := rfl
    have hacc : accNC A.nc (nizkV leanPISh leanVI (tirEquiv z).1.2.2 (tirEquiv z).2)
        (issNC A leanPISh leanVI (tirEquiv z).1 (tirEquiv z).2).2 = true := by
      rw [hq]
      unfold accNC
      rw [take_append_eq ht, drop_append_eq ht]
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_append, ht, hl]
      exact ⟨trivial, hv⟩
    exact absurd hz (by unfold RejNC; rw [hacc]; decide)
  · refine pr_le_of_fst fun n => ?_
    exact leanI_complete (X n) (W n) (issueRelW_honest A n)

/-- **The games with one shared `H₃` reach redemption**: in the game of `anonymityNCSh_num`, if
both issuers' keys are found at the Clients' indices in both sets, the redemptions are refused
with probability `≤ φ₀ + φ₁ + 2·2⁻¹¹³`. -/
theorem pr_refused_NCSh_le (A : AdversaryNCRO (RowH R)) (idx : AnchorSet → UOVKey → ℕ)
    (sk : Bool → Signer) (hsk : ∀ c, (sk c).Correct (A.pk c)) (hidx : IdxSound idx)
    (hK : ∀ c side, foundNC A.nc idx c side = true) :
    pr (((TIr × TIr) × (TRr × TRr)) × ShM (RowH R)) (fun x =>
      (goodNC A.nc idx (nizkC leanPISh leanVI x false) sk false (issC A leanPISh leanVI x false) &&
        goodNC A.nc idx (nizkC leanPISh leanVI x true) sk true (issC A leanPISh leanVI x true)) =
          false) ≤
      phi A.nc sk false + phi A.nc sk true + 2 / 2 ^ 113 := by
  have h := pr_refused_le A idx sk leanPISh (accNC_leanSh_complete A) hsk hidx hK
  have e : (2 : ℝ) * (1 / 2 ^ 113) = 2 / 2 ^ 113 := by ring
  linarith

end ShComplete

/-! ## pqov's signer in the games -/

section Vinegar

open VoleMole.Spec.Pqov

/-- `n` independent uniform draws whose first `k` all satisfy `P`: probability `Pr[P]^k`. -/
lemma pr_forall_lt {V : Type*} [Fintype V] [Nonempty V] (n k : ℕ) (hk : k ≤ n) (P : V → Prop) :
    pr (Fin n → V) (fun v => ∀ i : Fin n, i.val < k → P (v i)) = pr V P ^ k := by
  classical
  have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rw [pr_def, pr_def, Fintype.card_fun, Fintype.card_fin]
  have hset : (univ.filter fun v : Fin n → V => ∀ i : Fin n, i.val < k → P (v i)) =
      Fintype.piFinset fun i : Fin n => if i.val < k then univ.filter P else univ := by
    ext v
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    refine ⟨fun h i => ?_, fun h i hi => ?_⟩
    · split_ifs with hi
      · exact mem_filter.2 ⟨mem_univ _, h i hi⟩
      · exact mem_univ _
    · have := h i
      simp only [hi, ↓reduceIte] at this
      exact (mem_filter.1 this).2
  rw [hset, Fintype.card_piFinset]
  have hprod : ∏ i : Fin n, (if i.val < k then univ.filter P else univ).card =
      (univ.filter P).card ^ k * Fintype.card V ^ (n - k) := by
    simp only [apply_ite Finset.card]
    rw [Fin.prod_univ_eq_prod_range (fun i => if i < k then (univ.filter P).card else
      (univ : Finset V).card)]
    rw [prod_ite, prod_const, prod_const, card_univ]
    have h1 : ((range n).filter fun i => i < k) = range k := by
      ext i; simp only [mem_filter, mem_range]; omega
    have h2 : ((range n).filter fun i => ¬ i < k).card = n - k := by
      rw [show ((range n).filter fun i => ¬ i < k) = Ico k n by
        ext i; simp only [mem_filter, mem_range, mem_Ico]; omega, Nat.card_Ico]
    rw [h1, card_range, h2]
  rw [hprod]
  push_cast
  rw [div_pow, show (Fintype.card V : ℝ) ^ n = Fintype.card V ^ k * Fintype.card V ^ (n - k) by
    rw [← pow_add, Nat.add_sub_cancel' hk]]
  field_simp

variable {Vin : Type} [Fintype Vin] [Nonempty Vin] (Good : Bool → Vin → Prop)
  (A : AdversaryNC) (skW : VTab Vin → Bool → Signer)

/-- **The vinegar-RO abort bound with `k` usable attempts**: if Anchor `c`'s signer fails on a
target only when the first `k` vinegars of its table there are all bad, then averaged over the
table it fails on a uniform Client's commitment with probability `≤ δ_c^k`. -/
theorem pr_fail_vinegar_lt (k : ℕ) (hk : k ≤ 256)
    (hfail : ∀ w c t, (skW w c).derivePreimage t = none →
      ∀ i : Fin 256, i.val < k → ¬ Good c (w c (tkey t) i))
    (c : Bool) :
    pr (VTab Vin × (Coins nfBytes × Coins rBytes)) (fun z =>
        (skW z.1 c).derivePreimage (com (List.ofFn z.2.1) A.base.ci A.base.cr (List.ofFn z.2.2)) =
          none) ≤
      pr Vin (fun v => ¬ Good c v) ^ k := by
  rw [← pr_equiv (Equiv.prodComm _ _)]
  refine pr_le_of_forall_fst fun y => ?_
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  refine (pr_mono fun w hw => hfail w c _ hw).trans (le_of_eq ?_)
  rw [pr_eval c (fun g : Coins uovM → Fin 256 → Vin => ∀ i : Fin 256, i.val < k → ¬ Good c
      (g (tkey (com (List.ofFn y.1) A.base.ci A.base.cr (List.ofFn y.2))) i)),
    pr_eval (tkey (com (List.ofFn y.1) A.base.ci A.base.cr (List.ofFn y.2)))
      (fun g : Fin 256 → Vin => ∀ i : Fin 256, i.val < k → ¬ Good c (g i))]
  exact pr_forall_lt 256 k hk (fun v => ¬ Good c v)

/-- The average of the abort probability over the vinegar tables, from `pr_fail_vinegar_lt`. -/
theorem avg_phi_le (k : ℕ) (hk : k ≤ 256)
    (hfail : ∀ w c t, (skW w c).derivePreimage t = none →
      ∀ i : Fin 256, i.val < k → ¬ Good c (w c (tkey t) i)) (c : Bool) :
    (∑ w, phi A (skW w) c) / Fintype.card (VTab Vin) ≤ pr Vin (fun v => ¬ Good c v) ^ k := by
  have := pr_fail_vinegar_lt Good A skW k hk hfail c
  rw [pr_prod] at this
  exact this

end Vinegar

/-- **Averaging an abort bound** over a uniform first coordinate. -/
lemma abs_pr_avg_abort {W T T' : Type*} [Fintype W] [Nonempty W] [Fintype T] [Fintype T']
    (P : W → T → Prop) (Q : W → T' → Prop) (K : ℝ) (φ : W → Bool → ℝ) (β : Bool → ℝ)
    (h : ∀ w, |pr T (P w) - pr T' (Q w)| ≤ K + 2 * (φ w false + φ w true))
    (hβ : ∀ c, (∑ w, φ w c) / Fintype.card W ≤ β c) :
    |pr (W × T) (fun z => P z.1 z.2) - pr (W × T') (fun z => Q z.1 z.2)| ≤
      K + 2 * (β false + β true) := by
  have hcard : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  refine (abs_pr_prod_sub_le_avg (fun z : W × T => P z.1 z.2) (fun z : W × T' => Q z.1 z.2)
    (fun w => K + 2 * (φ w false + φ w true)) h).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_div,
    mul_div_cancel_left₀ _ hcard.ne', ← Finset.mul_sum, mul_div_assoc, Finset.sum_add_distrib,
    add_div]
  have := hβ false
  have := hβ true
  gcongr

section Pqov

open VoleMole.Spec.Pqov

/-- **The Anchors' pqov signers in the vinegar random-oracle model**: Anchor `c`'s
`derive_preimage` (`Spec.Pqov.signer`, `tries` attempts: pqov uses 255) for the key `pk c` with oil
matrix `O c`, its vinegar of attempt `i` at target `t` read from the table `w c` at `tkey t`
(`SHAKE256(t ‖ sk_seed_c ‖ DST ‖ i)` as a random oracle, independent per Anchor). -/
noncomputable def pqovRO (pk : Bool → UOVKey) (O : Bool → OilMat) (tries : ℕ) (w : VTab Vin)
    (c : Bool) : Signer :=
  signer (pk c) (O c) (fun t i => w c (tkey t) i) tries

/-- The fraction of vinegars whose system is singular, for the key `(pk, O)`. -/
noncomputable def delta (pk : UOVKey) (O : OilMat) : ℝ := pr Vin fun v => (sysMat pk O v).det = 0

variable (pk : Bool → UOVKey) (O : Bool → OilMat)

theorem pqovRO_correct (hO : ∀ c, OilSpace (pk c) (O c)) (tries : ℕ) (w : VTab Vin) (c : Bool) :
    (pqovRO pk O tries w c).Correct (pk c) :=
  signer_correct _ _ (hO c) _ _

/-- **pqov's signer fails only if every usable vinegar gives a singular system.** -/
theorem pqovRO_fail (tries : ℕ) (w : VTab Vin) (c : Bool) (t : Bytes)
    (h : (pqovRO pk O tries w c).derivePreimage t = none) (i : Fin 256) (hi : i.val < tries) :
    ¬ (sysMat (pk c) (O c) (w c (tkey t) i)).det ≠ 0 :=
  not_not.2 (signer_fail _ _ _ _ t h i hi)

/-- **With all 256 attempts, `hfail` of `anonymityNC_vinegarRO` holds as stated.** -/
theorem pqovRO256_hfail (w : VTab Vin) (c : Bool) (t : Bytes)
    (h : (pqovRO pk O 256 w c).derivePreimage t = none) (i : Fin 256) :
    ¬ (sysMat (pk c) (O c) (w c (tkey t) i)).det ≠ 0 :=
  pqovRO_fail pk O 256 w c t h i i.isLt

lemma pr_not_good (c : Bool) :
    pr Vin (fun v => ¬ (sysMat (pk c) (O c) v).det ≠ 0) = delta (pk c) (O c) :=
  pr_congr fun _ => not_not

/-- The average abort probability of pqov's signer (255 attempts) is `≤ δ_c^255`. -/
theorem avg_phi_pqov (A : AdversaryNC) (c : Bool) :
    (∑ w, phi A (pqovRO pk O 255 w) c) / Fintype.card (VTab Vin) ≤ delta (pk c) (O c) ^ 255 := by
  rw [← pr_not_good]
  exact avg_phi_le (fun c v => (sysMat (pk c) (O c) v).det ≠ 0) A (pqovRO pk O 255) 255
    (by norm_num) (fun w c t h i hi => pqovRO_fail pk O 255 w c t h i hi) c

/-- **Theorem 4(b′) with pqov's signers** (255 attempts, the vinegars a random oracle), for any
issuance proof system and redemption proofs `εR`-zero-knowledge: averaged over the vinegar tables,
`≤ 4εR + 2·(δ₀²⁵⁵ + δ₁²⁵⁵)`, `δ_c = delta (pk c) (O c)`. The signers are correct when `P` vanishes
on the Anchors' oil spaces (`OilSpace`). -/
theorem anonymityNC_pqov (A : AdversaryNC) (idx : AnchorSet → UOVKey → ℕ) (PI : NIZK IssueInstance)
    (O : Bool → OilMat) (hO : ∀ c, OilSpace (A.pk c) (O c)) (hidx : IdxSound idx) {CR : Type}
    [Fintype CR] [Nonempty CR] (simR : RedeemInstance → CR → Bytes) (PR : NIZK RedeemInstance)
    {εR : ℝ} (hεR : 0 ≤ εR) (hR : ZeroKnowledge RedeemRelW (proveR PR) simR εR) :
    |pr (VTab Vin × TapeNC) (fun z => realGameNC A idx PI (pqovRO A.pk O 255 z.1) PR false z.2) -
        pr (VTab Vin × TapeNC) (fun z => realGameNC A idx PI (pqovRO A.pk O 255 z.1) PR true z.2)| ≤
      4 * εR + 2 * (delta (A.pk false) (O false) ^ 255 + delta (A.pk true) (O true) ^ 255) := by
  have hw (w : VTab Vin) := anonymityNC A idx PI (pqovRO A.pk O 255 w) simR PR hεR
    (pqovRO_correct A.pk O hO 255 w) hidx hR
  exact abs_pr_avg_abort (fun w => realGameNC A idx PI (pqovRO A.pk O 255 w) PR false)
    (fun w => realGameNC A idx PI (pqovRO A.pk O 255 w) PR true) (4 * εR)
    (fun w c => phi A (pqovRO A.pk O 255 w) c) (fun c => delta (A.pk c) (O c) ^ 255) hw
    (fun c => avg_phi_pqov A.pk O A c)

/-- **Theorem 4(b′) in the random-oracle and ideal-cipher model with pqov's signers** (every type of
cipher rows; the Lean prover and verifier on the shared tables): averaged over the vinegar tables,

    4·εz(pR; q₃, q₅ + 2496, q_E + 23035) + 2·(noHitProb + 2⁻¹⁰²⁴) + 4·q₃·2⁻¹²⁸
      + 2·(δ₀²⁵⁵ + δ₁²⁵⁵). -/
theorem anonymityNCRO_pqov {R : Type} [Fintype R] [Nonempty R] [CipherRow R] [ZKRow R]
    (A : AdversaryNCRO R) (idx : AnchorSet → UOVKey → ℕ) (O : Bool → OilMat)
    (hO : ∀ c, OilSpace (A.pk c) (O c)) (hidx : IdxSound idx) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr (VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R)) (fun z =>
        realGameNCRO A idx leanPI leanVI (pqovRO A.pk O 255 z.1) leanPR false z.2) -
      pr (VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R)) (fun z =>
        realGameNCRO A idx leanPI leanVI (pqovRO A.pk O 255 z.1) leanPR true z.2)| ≤
      4 * ZKRow.εz R pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        4 * (q3 / 2 ^ 128) +
        2 * (delta (A.pk false) (O false) ^ 255 + delta (A.pk true) (O true) ^ 255) := by
  have hw (w : VTab Vin) := anonymityNCRO_leanG A idx (pqovRO A.pk O 255 w)
    (pqovRO_correct A.pk O hO 255 w) hidx hA
  generalize (2 : ℝ) ^ 1024 = M at hw ⊢
  have := abs_pr_avg_abort
    (fun w => realGameNCRO A idx leanPI leanVI (pqovRO A.pk O 255 w) leanPR false)
    (fun w => realGameNCRO A idx leanPI leanVI (pqovRO A.pk O 255 w) leanPR true)
    (4 * ZKRow.εz R pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / M) +
      4 * (q3 / 2 ^ 128))
    (fun w c => phi A.nc (pqovRO A.pk O 255 w) c) (fun c => delta (A.pk c) (O c) ^ 255)
    (fun w => (hw w).trans (le_of_eq (by ring))) (fun c => avg_phi_pqov A.pk O A.nc c)
  exact this

/-- **Theorem 4(b′) with one shared `H₃` and pqov's signers** (every type of cipher rows):
averaged over the vinegar tables,

    4·εz(pR; q_E + 23038, q₅ + 2496, q_E + 23038) + 2·(noHitProb + 2⁻¹⁰²⁴) + 2·(δ₀²⁵⁵ + δ₁²⁵⁵). -/
theorem anonymityNCSh_pqov {R : Type} [Fintype R] [Nonempty R] [CipherRow R] [ZKRow R]
    (A : AdversaryNCRO (RowH R)) (idx : AnchorSet → UOVKey → ℕ) (O : Bool → OilMat)
    (hO : ∀ c, OilSpace (A.pk c) (O c)) (hidx : IdxSound idx) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr (VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM (RowH R))) (fun z =>
        realGameNCSh A idx (pqovRO A.pk O 255 z.1) false z.2) -
      pr (VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM (RowH R))) (fun z =>
        realGameNCSh A idx (pqovRO A.pk O 255 z.1) true z.2)| ≤
      4 * ZKRow.εz R pR (qE + 23038) (q5 + 2496) (qE + 23038) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * (delta (A.pk false) (O false) ^ 255 + delta (A.pk true) (O true) ^ 255) := by
  have hw (w : VTab Vin) := anonymityNCSh_leanG A idx (pqovRO A.pk O 255 w)
    (pqovRO_correct A.pk O hO 255 w) hidx hA
  generalize (2 : ℝ) ^ 1024 = M at hw ⊢
  exact abs_pr_avg_abort (fun w => realGameNCSh A idx (pqovRO A.pk O 255 w) false)
    (fun w => realGameNCSh A idx (pqovRO A.pk O 255 w) true)
    (4 * ZKRow.εz R pR (qE + 23038) (q5 + 2496) (qE + 23038) + 2 * (noHitProb + 1 / M))
    (fun w c => phi A.nc (pqovRO A.pk O 255 w) c) (fun c => delta (A.pk c) (O c) ^ 255) hw
    (fun c => avg_phi_pqov A.pk O A.nc c)

/-- **The games reach redemption with pqov's signers**: averaged over the vinegar tables, the game
of `anonymityNCRO_pqov` refuses the redemptions with probability `≤ δ₀²⁵⁵ + δ₁²⁵⁵ + 2·2⁻¹¹³`
when both issuers' keys are found at the Clients' indices in both sets. -/
theorem pr_refused_NCRO_pqov {R : Type} [Fintype R] [Nonempty R] [CipherRow R]
    (A : AdversaryNCRO R) (idx : AnchorSet → UOVKey → ℕ) (O : Bool → OilMat)
    (hO : ∀ c, OilSpace (A.pk c) (O c)) (hidx : IdxSound idx)
    (hK : ∀ c side, foundNC A.nc idx c side = true) :
    pr (VTab Vin × (((TIr × TIr) × (TRr × TRr)) × ShM R)) (fun z =>
      (goodNC A.nc idx (nizkC leanPI leanVI z.2 false) (pqovRO A.pk O 255 z.1) false
          (issC A leanPI leanVI z.2 false) &&
        goodNC A.nc idx (nizkC leanPI leanVI z.2 true) (pqovRO A.pk O 255 z.1) true
          (issC A leanPI leanVI z.2 true)) = false) ≤
      delta (A.pk false) (O false) ^ 255 + delta (A.pk true) (O true) ^ 255 + 2 / 2 ^ 113 := by
  have hcard : (0 : ℝ) < Fintype.card (VTab Vin) := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, div_le_iff₀ hcard]
  have h := fun w : VTab Vin => pr_refused_NCRO_le A idx (pqovRO A.pk O 255 w)
    (pqovRO_correct A.pk O hO 255 w) hidx hK
  refine (Finset.sum_le_sum fun w _ => h w).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have h0 := avg_phi_pqov A.pk O A.nc false
  have h1 := avg_phi_pqov A.pk O A.nc true
  rw [div_le_iff₀ hcard] at h0 h1
  nlinarith

end Pqov

end VoleMole.Privacy.Moussaka
