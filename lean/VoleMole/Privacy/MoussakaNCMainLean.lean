import VoleMole.Privacy.MoussakaNCMain
import VoleMole.ZK.CompleteRO

/-!
# Moussaka 4(b') on `main` with the Lean issuance prover and the Anchor's Lean verifier

`anonymityNC_main` (`Privacy/MoussakaNCMain.lean`) takes the issuance proofs from an abstract
proof system `PI` that does not read the game's tables. Here the issuance proofs are **`main`'s
Lean prover**, run on the shared tables of `ZK/MainSharedAll.lean` (one `H₃`, whose column at the
proof's prefix `wPrefix ‖ μ₁` is the proof's slice, the raw `H₂³` table, the `H₅` table and the
cipher), and the honest Anchor checks the request with `main`'s `issue_response`: the length
`issueRequestBytes`, then the Lean verifier on the same tables. This is the route of
`lean/docs/zk.md` §4.2.

* **Length** (`issueProof_size`, `issueReq_length`): `main`'s Lean issuance proof has
  `pIm.proofBytes = 7272 = issueRequestBytes − 45` bytes, so an honest request passes the
  Anchor's length check.
* **Completeness on the shared tables** (`issue_complete_shared`): `complete_rom_ic` restated for
  the shared-table model: the column of a uniform `H₃` at a fixed prefix is a uniform slice, so
  the prover fails or the verifier rejects with probability `≤ 2⁻¹¹³`.
* **The game** (`realNCML`): the issuance proofs are computed before any redemption, on the raw
  shared tables, and never shown; they enter the view only through the Anchors' verdicts. If both
  Anchors accept, the game is `realNCM` for the proof system `PIacc` that accepts every request of
  the right length (`κ = 0`); otherwise a token is missing and the redemptions are refused, which is
  `realNCM` for `PIrej`, which rejects every request (the view of a refusal does not depend on the
  proof system).
* **The hop** (`realNCML_close`): replacing both verdicts by `true` costs `2·2⁻¹¹³` per world.

    anonymityNC_main_lean:  |Pr[W₀] − Pr[W₁]| ≤ (the bound of anonymityNC_main) + 4·2⁻¹¹³
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK

-- `Com` evaluates Keccak-p[800]; nothing below needs to unfold it.
attribute [local irreducible] com UOVKey.eval

/-! ## The length of `main`'s Lean issuance proof -/

/-- **A Lean proof has its parameters' proof length.** -/
lemma prove_size [HasPrg] {Hs : Hashes} {T : CrtTables} {st : Statement} {w rho : ByteArray}
    {k : ℕ} {proof : ByteArray} (h : Prover.prove Hs T st w rho k = .ok proof) :
    proof.size = st.params.proofBytes := by
  obtain ⟨-, check, aT, ctr, delta, opening, -, -, hproof⟩ := proveCommit_inv h
  rw [hproof]
  exact (fields_assemble _ _).2.2.2.2.2.2.2.2.2

/-- **`main`'s issuance proof has `issueRequestBytes − 45 = 7272` bytes.** -/
theorem issueProof_size [HasPrg] {Hs : Hashes} {T : CrtTables} {st : Statement}
    {w rho : ByteArray} {k : ℕ} {proof : ByteArray}
    (h : Prover.prove Hs T (withP st pIm) w rho k = .ok proof) :
    proof.size = issueRequestBytes - uovM := by
  rw [prove_size h]
  show pIm.proofBytes = _
  decide

/-- **An honest request with `main`'s Lean proof has the length `main`'s Anchor checks.** -/
theorem issueReq_length [HasPrg] {Hs : Hashes} {T : CrtTables} {st : Statement}
    {w rho : ByteArray} {k : ℕ} {proof : ByteArray}
    (h : Prover.prove Hs T (withP st pIm) w rho k = .ok proof) (t : Bytes) (ht : t.length = uovM) :
    (t ++ proof.data.toList).length = issueRequestBytes := by
  have hs := issueProof_size h
  rw [List.length_append, ht, Array.length_toList]
  have : proof.data.size = proof.size := rfl
  rw [this, hs]
  decide

/-! ## Completeness on the shared tables -/

/-- The column of a uniform `H₃` at a fixed prefix is a uniform slice. -/
theorem pr_col (k : Pre) (P : Tab3 → Prop) : pr H3T (fun T => P (T k)) = pr Tab3 P := by
  let e : Tab3 × ({j : Pre // j ≠ k} → Tab3) ≃ H3T := (Equiv.piSplitAt k (fun _ => Tab3)).symm
  rw [← pr_equiv e]
  have h : ∀ z : Tab3 × ({j : Pre // j ≠ k} → Tab3), e z k = z.1 := fun z => by
    simp [e, Equiv.piSplitAt_symm_apply]
  rw [pr_congr (Q := fun z => P z.1) fun z => by rw [h z]]
  exact pr_prod_fst P

/-- **The failure event of `complete_rom_ic`** for the statement `st` and witness `w`, at the
prover's randomness, the `H₂³` table, the `H₃` slice, the `H₅` table and the cipher. -/
def failC [HasPrg] (st : Statement) (w : ByteArray)
    (c : ((ZK.Sim.Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) : Prop :=
  ¬ ∃ proof, @Prover.prove (icPrg c.2) (recH Hashes.shake st w c.1.2.1 c.1.1.2 c.1.2.2)
      CrtGen.tables st w (ba c.1.1.1) st.params.witnessBytes = .ok proof ∧
    (@verify (icPrg c.2) (recH Hashes.shake st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st
      proof).accept = true

/-- **The executable prover and the Anchor's verifier on the shared tables fail**: `main`'s prover
for `y` with randomness `ρ`, `H₃` the column of `T` at the proof's prefix, `H₂³` the raw table,
`H₅` and the cipher the shared ones; the verifier on the same tables. -/
def issFail [HasPrg] (y : SW) (ρ : ZK.Sim.Bytes 16) (G2 : Tab2G pIm) (u : USh) (T : H3T) : Prop :=
  failC (withP y.1 pIm) y.2 (((ρ, G2), (T (preOf Hashes.shake pIm y), u.1)), u.2)

set_option maxRecDepth 8192 in
/-- **`complete_rom_ic` for the shared-table model**: for a statement of `main`'s issuance
relation (`ValidZK`), the Lean prover fails or the Anchor's Lean verifier rejects with
probability at most `2⁻¹¹³`, over the prover's randomness, the raw `H₂³` table, `H₃`, the `H₅`
table and the cipher. -/
theorem issue_complete_shared [HasPrg] (y : SW) (hv : ValidZK CrtGen.tables pIm y) :
    pr (((ZK.Sim.Bytes 16 × Tab2G pIm) × (H3T × Tab5F)) × Cipher)
      (fun c => issFail y c.1.1.1 c.1.1.2 (c.1.2.2, c.2) c.1.2.1) ≤ 1 / 2 ^ 113 := by
  obtain ⟨cs, hzk⟩ := hv
  have h : pr (((ZK.Sim.Bytes 16 × Tab2G pIm) × (Tab3 × Tab5F)) × Cipher)
      (failC (withP y.1 pIm) y.2) ≤ 1 / 2 ^ 113 :=
    complete_rom_ic Hashes.shake (withP y.1 pIm) y.2 hzk hashesWF_shake mainP_pIm.hlab
  obtain ⟨k, hk0⟩ : ∃ k, preOf Hashes.shake pIm y = k := ⟨_, rfl⟩
  have hsk : ∀ (g : Tab3) (f : {j : Pre // j ≠ k} → Tab3),
      (Equiv.piSplitAt k (fun _ : Pre => Tab3)).symm (g, f) k = g := fun g f => by
    simp [Equiv.piSplitAt_symm_apply]
  have hsj : ∀ (g : Tab3) (f : {j : Pre // j ≠ k} → Tab3) (j : {j : Pre // j ≠ k}),
      (Equiv.piSplitAt k (fun _ : Pre => Tab3)).symm (g, f) j.1 = f j := fun g f j => by
    simp [Equiv.piSplitAt_symm_apply, j.2]
  have hT : ∀ T : H3T, (Equiv.piSplitAt k (fun _ : Pre => Tab3)).symm (T k, fun j => T j.1) = T :=
    fun T => by
      funext j
      by_cases hj : j = k
      · subst hj; exact hsk _ _
      · exact hsj (T k) (fun j => T j.1) ⟨j, hj⟩
  let e : (((ZK.Sim.Bytes 16 × Tab2G pIm) × (Tab3 × Tab5F)) × Cipher) ×
      ({j : Pre // j ≠ k} → Tab3) ≃ ((ZK.Sim.Bytes 16 × Tab2G pIm) × (H3T × Tab5F)) × Cipher :=
    { toFun := fun z => ((z.1.1.1, ((Equiv.piSplitAt k (fun _ : Pre => Tab3)).symm (z.1.1.2.1, z.2),
        z.1.1.2.2)), z.1.2)
      invFun := fun c => (((c.1.1, (c.1.2.1 k, c.1.2.2)), c.2), fun j => c.1.2.1 j.1)
      left_inv := fun z => by
        rcases z with ⟨⟨⟨a, g, g5⟩, E⟩, f⟩
        show (((a, ((Equiv.piSplitAt k (fun _ : Pre => Tab3)).symm (g, f) k, g5)), E),
          fun j => (Equiv.piSplitAt k (fun _ : Pre => Tab3)).symm (g, f) j.1) = (((a, (g, g5)), E), f)
        rw [hsk]
        congr 1
        funext j
        exact hsj g f j
      right_inv := fun c => by
        rcases c with ⟨⟨a, T, g5⟩, E⟩
        show ((a, ((Equiv.piSplitAt k (fun _ : Pre => Tab3)).symm (T k, fun j => T j.1), g5)), E) =
          ((a, (T, g5)), E)
        rw [hT] }
  have e1 : pr (((ZK.Sim.Bytes 16 × Tab2G pIm) × (H3T × Tab5F)) × Cipher)
      (fun c => issFail y c.1.1.1 c.1.1.2 (c.1.2.2, c.2) c.1.2.1) =
      pr ((((ZK.Sim.Bytes 16 × Tab2G pIm) × (Tab3 × Tab5F)) × Cipher) ×
        ({j : Pre // j ≠ k} → Tab3)) (fun z => issFail y (e z).1.1.1 (e z).1.1.2
          ((e z).1.2.2, (e z).2) (e z).1.2.1) :=
    (pr_equiv e _).symm
  have e2 : pr ((((ZK.Sim.Bytes 16 × Tab2G pIm) × (Tab3 × Tab5F)) × Cipher) ×
        ({j : Pre // j ≠ k} → Tab3)) (fun z => issFail y (e z).1.1.1 (e z).1.1.2
          ((e z).1.2.2, (e z).2) (e z).1.2.1) =
      pr ((((ZK.Sim.Bytes 16 × Tab2G pIm) × (Tab3 × Tab5F)) × Cipher) ×
        ({j : Pre // j ≠ k} → Tab3)) (fun z => failC (withP y.1 pIm) y.2 z.1) := by
    refine pr_congr fun z => ?_
    rcases z with ⟨⟨⟨a, g, g5⟩, E⟩, f⟩
    show failC (withP y.1 pIm) y.2 ((a, ((Equiv.piSplitAt k (fun _ : Pre => Tab3)).symm (g, f)
      (preOf Hashes.shake pIm y), g5)), E) ↔ failC (withP y.1 pIm) y.2 ((a, (g, g5)), E)
    rw [hk0, hsk]
  rw [e1, e2, pr_prod_fst]
  exact h

/-! ## The game with `main`'s Lean issuance prover -/

section GameL

variable [HasPrg] (A : AdversaryNCM) (idx : Rule) (sk : Bool → Signer)

/-- The issuance proof system that accepts every request (of the right length): `κ = 0`. -/
def PIacc : NIZK IssueInstance := ⟨fun _ _ _ => List.replicate issueProofBytes 0, fun _ _ => true⟩

/-- The issuance proof system that rejects every request. -/
def PIrej : NIZK IssueInstance := ⟨fun _ _ _ => List.replicate issueProofBytes 0, fun _ _ => false⟩

/-- The tape of the shared game (`realAll`'s). -/
abbrev TapeN := GTape SecNC (pw pIm 256) (pw pIm 256) (pw pIm 343) (pw pIm 343)

/-- The two Clients' `(nf, r)`. -/
def secOf (s : SecNC) : SecM :=
  (((xOf s false).1, (xOf s false).2.1), ((xOf s true).1, (xOf s true).2.1))

/-- **Client `c`'s issuance statement and witness on `main`.** -/
def issY (s : SecNC) (c : Bool) : SW := issStmt A.m (secOf s) c

/-- **Client `c`'s Lean issuance proof**, on the raw shared tables of tape `z`: randomness the
Client's `ρ_iss`, `H₃` the column at the proof's prefix. -/
noncomputable def proveL (z : TapeN × H3T) (c : Bool) :
    Except String ByteArray :=
  @Prover.prove (icPrg z.1.2.1.2) (recH Hashes.shake (withP (issY A z.1.1 c).1 pIm)
      (issY A z.1.1 c).2 (z.2 (preOf Hashes.shake pIm (issY A z.1.1 c))) z.1.2.2.1.2.2 z.1.2.1.1)
    CrtGen.tables (withP (issY A z.1.1 c).1 pIm) (issY A z.1.1 c).2 (ba (xOf z.1.1 c).2.2)
    (withP (issY A z.1.1 c).1 pIm).params.witnessBytes

/-- **Anchor `c`'s verdict** on Client `c`'s request `t ‖ π` (`main`'s `issue_response`): the
Client's Lean prover output a proof `π`, the request has the length `issueRequestBytes`, and the
Lean verifier on the same tables accepts `π`. -/
def AccL (z : TapeN × H3T) (c : Bool) : Prop :=
  ∃ proof, proveL A z c = .ok proof ∧
    (tM A.m (secOf z.1.1) c ++ proof.data.toList).length = issueRequestBytes ∧
    (@verify (icPrg z.1.2.1.2) (recH Hashes.shake (withP (issY A z.1.1 c).1 pIm)
      (issY A z.1.1 c).2 (z.2 (preOf Hashes.shake pIm (issY A z.1.1 c))) z.1.2.2.1.2.2
      z.1.2.1.1) CrtGen.tables (withP (issY A z.1.1 c).1 pIm) proof).accept = true

/-- **The Anchor accepts unless the issuance fails** (the prover's failure or the verifier's
rejection, the event of `complete_rom_ic`): an honest request has the right length. -/
lemma accL_of (z : TapeN × H3T) (c : Bool)
    (h : ¬ issFail (issY A z.1.1 c) (xOf z.1.1 c).2.2 z.1.2.2.1.2.2 z.1.2.1 z.2) :
    AccL A z c := by
  have h' : ∃ proof, proveL A z c = .ok proof ∧
      (@verify (icPrg z.1.2.1.2) (recH Hashes.shake (withP (issY A z.1.1 c).1 pIm)
        (issY A z.1.1 c).2 (z.2 (preOf Hashes.shake pIm (issY A z.1.1 c))) z.1.2.2.1.2.2
        z.1.2.1.1) CrtGen.tables (withP (issY A z.1.1 c).1 pIm) proof).accept = true :=
    not_not.1 h
  obtain ⟨proof, hp, hv⟩ := h'
  exact ⟨proof, hp, @issueReq_length (icPrg z.1.2.1.2) _ _ _ _ _ _ _ hp _ (length_com _ _ _ _), hv⟩

open scoped Classical in
/-- **The real game with `main`'s Lean issuance prover** in world `b`: the issuance proofs on the
raw shared tables, judged by the honest Anchors; if both accept, the rest of the game is
`realNCM`'s for a proof system that accepts the honest requests (`PIacc`), otherwise a token is
missing and the redemptions are refused (`PIrej`: the refusal's view). The issuance proofs are
never shown. -/
noncomputable def realNCML (b : Bool) : ℝ :=
  pr (TapeN × H3T) (fun z =>
    if AccL A z false ∧ AccL A z true then
      evNCM A idx PIacc sk b (hybVAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
        Hashes.shake (gameNCM A idx PIacc sk b) z.1 z.2) z.2
    else
      evNCM A idx PIrej sk b (hybVAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
        Hashes.shake (gameNCM A idx PIrej sk b) z.1 z.2) z.2)

set_option maxRecDepth 8192 in
/-- **Client `c`'s issuance fails with probability `≤ 2⁻¹¹³`** (`issue_complete_shared`, the
other coordinates of the tape fixed). -/
theorem pr_issFail_le (c : Bool) :
    pr (TapeN × H3T) (fun z =>
      issFail (issY A z.1.1 c) (xOf z.1.1 c).2.2 z.1.2.2.1.2.2 z.1.2.1 z.2) ≤ 1 / 2 ^ 113 := by
  cases c
  · let e : (((ZK.Sim.Bytes 16 × Tab2G pIm) × (H3T × Tab5F)) × Cipher) ×
        (((Coins nfBytes × Coins rBytes) × IssT) × ((ZK.Sim.Bytes 16 × SimCoins (pw pIm 256)) × Tab3) ×
          KS (pw pIm 256) × KS (pw pIm 343) × KS (pw pIm 343)) ≃ TapeN × H3T :=
      { toFun := fun w => ((((w.2.1.1.1, (w.2.1.1.2, w.1.1.1.1)), w.2.1.2), ((w.1.1.2.2, w.1.2),
          ((w.2.2.1.1, (w.2.2.1.2, w.1.1.1.2)), w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2))), w.1.1.2.1)
        invFun := fun z => ((((z.1.1.1.2.2, z.1.2.2.1.2.2), (z.2, z.1.2.1.1)), z.1.2.1.2),
          (((z.1.1.1.1, z.1.1.1.2.1), z.1.1.2), ((z.1.2.2.1.1, z.1.2.2.1.2.1), z.1.2.2.2.1,
            z.1.2.2.2.2.1, z.1.2.2.2.2.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e]
    refine pr_le_of_snd fun o => ?_
    exact issue_complete_shared (issY A (((o.1.1.1, (o.1.1.2, fun _ => 0)), o.1.2)) false)
      (issStmt_valid A.m _ false)
  · let e : (((ZK.Sim.Bytes 16 × Tab2G pIm) × (H3T × Tab5F)) × Cipher) ×
        ((IssT × (Coins nfBytes × Coins rBytes)) × ((ZK.Sim.Bytes 16 × SimCoins (pw pIm 256)) × Tab3) ×
          KS (pw pIm 256) × KS (pw pIm 343) × KS (pw pIm 343)) ≃ TapeN × H3T :=
      { toFun := fun w => (((w.2.1.1, (w.2.1.2.1, (w.2.1.2.2, w.1.1.1.1))), ((w.1.1.2.2, w.1.2),
          ((w.2.2.1.1, (w.2.2.1.2, w.1.1.1.2)), w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2))), w.1.1.2.1)
        invFun := fun z => ((((z.1.1.2.2.2, z.1.2.2.1.2.2), (z.2, z.1.2.1.1)), z.1.2.1.2),
          ((z.1.1.1, (z.1.1.2.1, z.1.1.2.2.1)), ((z.1.2.2.1.1, z.1.2.2.1.2.1), z.1.2.2.2.1,
            z.1.2.2.2.2.1, z.1.2.2.2.2.2)))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e]
    refine pr_le_of_snd fun o => ?_
    exact issue_complete_shared (issY A ((o.1.1, (o.1.2.1, (o.1.2.2, fun _ => 0)))) true)
      (issStmt_valid A.m _ true)

open scoped Classical in
set_option maxRecDepth 8192 in
/-- **Replacing the Anchors' verdicts by `true` costs `2·2⁻¹¹³`**: the real game with `main`'s
Lean issuance prover against `realNCM` for `PIacc`. -/
theorem realNCML_close (b : Bool) :
    |realNCML A idx sk b - realNCM A idx PIacc sk b| ≤ 2 / 2 ^ 113 := by
  unfold realNCML realNCM realAll
  refine (abs_pr_sub_le_of_agree
    (fun z : TapeN × H3T =>
      if AccL A z false ∧ AccL A z true then
        evNCM A idx PIacc sk b (hybVAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
          Hashes.shake (gameNCM A idx PIacc sk b) z.1 z.2) z.2
      else
        evNCM A idx PIrej sk b (hybVAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343) (n₄ := 343)
          Hashes.shake (gameNCM A idx PIrej sk b) z.1 z.2) z.2)
    (fun z => evNCM A idx PIacc sk b (hybVAll (p₀ := pIm) (n₁ := 256) (n₂ := 256) (n₃ := 343)
      (n₄ := 343) Hashes.shake (gameNCM A idx PIacc sk b) z.1 z.2) z.2)
    (fun z => issFail (issY A z.1.1 false) (xOf z.1.1 false).2.2 z.1.2.2.1.2.2 z.1.2.1 z.2 ∨
      issFail (issY A z.1.1 true) (xOf z.1.1 true).2.2 z.1.2.2.1.2.2 z.1.2.1 z.2)
    fun z hz => ?_).trans ((pr_or_le _ _).trans ?_)
  · simp only [not_or] at hz
    have h0 := accL_of A z false hz.1
    have h1 := accL_of A z true hz.2
    simp only [h0, h1, and_self, ↓reduceIte]
  · have h0 := pr_issFail_le A false
    have h1 := pr_issFail_le A true
    have : (2 : ℝ) / 2 ^ 113 = 1 / 2 ^ 113 + 1 / 2 ^ 113 := by ring
    linarith

/-- **Theorem 4(b') on `main` with the Lean issuance prover and the Anchors' Lean verifier, all
tables shared.** For the Moderator, the Anchors and the rule of `anonymityNC_main`, with the
issuance proofs `main`'s executable prover on the shared tables (one `H₃`, the raw `H₂³` table,
the `H₅` table, the cipher) and the Anchors' verdicts `main`'s `issue_response` with the Lean
verifier on the same tables,

    |Pr[W₀] − Pr[W₁]| ≤ 30·(εS(q₃, q_E + 8·4607) + Δ23)
        + 15·(8·noHitProb + (4·(q₅ + 625) + 626)·2⁻¹²⁸) + 2·2⁻¹²⁸ + 2·(φ false + φ true)
        + 4·2⁻¹¹³.

No abstract issuance proof system remains: `PIacc` is a device of the proof (the game with both
verdicts `true`). -/
theorem anonymityNC_main_lean (hsk : ∀ c, (sk c).Correct (A.pk c)) {f : Bool → Bool → Bool}
    (hidx : RuleNC A.nc idx f) {q3 qE q5 : ℕ}
    (hC : A.ConsH q3 qE) (h5 : ∀ y t T, (A.R5 y t T).card ≤ q5) :
    |realNCML A idx sk false - realNCML A idx sk true| ≤
      30 * (εS q3 (qE + 8 * 4607) + Δ23 9) +
        15 * (8 * noHitProb + (4 * (q5 + 625) + 626) / 2 ^ 128) + 2 / 2 ^ 128 +
        2 * (phi A.nc sk false + phi A.nc sk true) + 4 / 2 ^ 113 := by
  have h := anonymityNC_main A idx PIacc sk hsk hidx hC h5
  have c0 := realNCML_close A idx sk false
  have c1 := realNCML_close A idx sk true
  have := abs_sub_le_iff.1 h; have := abs_sub_le_iff.1 c0; have := abs_sub_le_iff.1 c1
  rw [abs_sub_le_iff]
  constructor <;> linarith

end GameL

end VoleMole.Privacy.Moussaka
