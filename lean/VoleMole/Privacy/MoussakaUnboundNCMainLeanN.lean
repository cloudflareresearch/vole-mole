import VoleMole.Privacy.MoussakaUnboundNCMainN
import VoleMole.Privacy.MoussakaNCMainLean

/-!
# Unbound Moussaka U5(b) on `main` with the Lean issuance prover, `n` adaptive queries

`anonymityNC_main_U_sharedAllN` (`Privacy/MoussakaUnboundNCMainN.lean`) takes the issuance proofs
from an abstract proof system `PI` that does not read the game's tables. Here, as for the bound
protocol's 4(b') (`Privacy/MoussakaNCMainLean.lean`), the issuance proofs are **`main`'s Lean
prover** for the unbound issuance relation (`pIu`), run on the shared tables (one `H₃`, whose
column at the proof's prefix is the proof's slice, the raw `H₂³` table, the `H₅` table, the
cipher), and each honest Anchor runs `unbound_issue_response` (`src/ihat/ihat.cpp:369-380`) with
the Lean verifier on the same tables.

* `unbound_issue_response` has **no length check**: the Anchor verifies the bytes after the
  commitment, which are the Client's proof. So only completeness is needed
  (`issue_complete_sharedU`: `complete_rom_ic` on the shared tables, `≤ 2⁻¹¹³` per Client).
* **The game** (`realNNL`): the issuance proofs are computed first, on the raw shared tables, and
  never shown. If both Anchors accept, the rest is `realNN`'s integrand for `PIaccU`, which
  accepts every request; otherwise a token is missing and every query is refused, which is
  `realNN`'s integrand for `PIrejU` (the view of a refusal does not depend on the proof system).
* **The hop** (`realNNL_close`): replacing both verdicts by `true` costs `2·2⁻¹¹³` per world, and
  `PIaccU` is complete, so its `κ` is `0` and `ψ c ≤ φ c` (`psi_le`, `kappa_eq_zero`).

    anonymityNC_main_U_leanN:  |Pr[W₀] − Pr[W₁]| ≤ 2·(2ⁿ − 1)·(εS(q₃ + n, q_E + 2n·4607) + Δ23N(9, n))
        + 2·(2ⁿ − 1)·(n·noHitProb + 2n·(q₅ + 312n + 1)·2⁻¹²⁸ + n²·313·2⁻¹²⁸)
        + 2·(φ false + φ true) + 2·εprf + 4·2⁻¹¹³.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.MoussakaUnbound

open VoleMole.Spec VoleMole.Spec.MoussakaUnbound VoleMole.ZK.Sim VoleMole.Privacy.MainChain
open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK
open VoleMole.Spec.Moussaka (NIZK AnchorSet Error ctxBytes proveSeedBytes rBytes nfBytes maxAnchors)
open VoleMole.Privacy.Moussaka (failC)

-- `UCom` and `Derive` evaluate Keccak-p[800]; nothing below needs to unfold them.
attribute [local irreducible] ucom derive UOVKey.eval

/-! ## Completeness of the unbound issuance proof on the shared tables -/

/-- **The executable prover and the Anchor's verifier on the shared tables fail** for the unbound
issuance statement `y`: `main`'s prover with randomness `ρ`, `H₃` the column of `T` at the
proof's prefix, `H₂³` the raw table, `H₅` and the cipher the shared ones. -/
def issFailU [HasPrg] (y : SW) (ρ : ZK.Sim.Bytes 16) (G2 : Tab2G pIu) (u : USh) (T : H3T) :
    Prop :=
  failC (withP y.1 pIu) y.2 (((ρ, G2), (T (preOf Hashes.shake pIu y), u.1)), u.2)

set_option maxRecDepth 8192 in
/-- **`complete_rom_ic` for the unbound issuance relation on the shared tables**: `≤ 2⁻¹¹³`. -/
theorem issue_complete_sharedU [HasPrg] (y : SW) (hv : ValidZK CrtGen.tables pIu y) :
    pr (((ZK.Sim.Bytes 16 × Tab2G pIu) × (H3T × Tab5F)) × Cipher)
      (fun c => issFailU y c.1.1.1 c.1.1.2 (c.1.2.2, c.2) c.1.2.1) ≤ 1 / 2 ^ 113 := by
  obtain ⟨cs, hzk⟩ := hv
  have h : pr (((ZK.Sim.Bytes 16 × Tab2G pIu) × (Tab3 × Tab5F)) × Cipher)
      (failC (withP y.1 pIu) y.2) ≤ 1 / 2 ^ 113 :=
    complete_rom_ic Hashes.shake (withP y.1 pIu) y.2 hzk hashesWF_shake mainP_pIu.hlab
  obtain ⟨k, hk0⟩ : ∃ k, preOf Hashes.shake pIu y = k := ⟨_, rfl⟩
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
  let e : (((ZK.Sim.Bytes 16 × Tab2G pIu) × (Tab3 × Tab5F)) × Cipher) ×
      ({j : Pre // j ≠ k} → Tab3) ≃ ((ZK.Sim.Bytes 16 × Tab2G pIu) × (H3T × Tab5F)) × Cipher :=
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
  have e1 : pr (((ZK.Sim.Bytes 16 × Tab2G pIu) × (H3T × Tab5F)) × Cipher)
      (fun c => issFailU y c.1.1.1 c.1.1.2 (c.1.2.2, c.2) c.1.2.1) =
      pr ((((ZK.Sim.Bytes 16 × Tab2G pIu) × (Tab3 × Tab5F)) × Cipher) ×
        ({j : Pre // j ≠ k} → Tab3)) (fun z => issFailU y (e z).1.1.1 (e z).1.1.2
          ((e z).1.2.2, (e z).2) (e z).1.2.1) :=
    (pr_equiv e _).symm
  have e2 : pr ((((ZK.Sim.Bytes 16 × Tab2G pIu) × (Tab3 × Tab5F)) × Cipher) ×
        ({j : Pre // j ≠ k} → Tab3)) (fun z => issFailU y (e z).1.1.1 (e z).1.1.2
          ((e z).1.2.2, (e z).2) (e z).1.2.1) =
      pr ((((ZK.Sim.Bytes 16 × Tab2G pIu) × (Tab3 × Tab5F)) × Cipher) ×
        ({j : Pre // j ≠ k} → Tab3)) (fun z => failC (withP y.1 pIu) y.2 z.1) := by
    refine pr_congr fun z => ?_
    rcases z with ⟨⟨⟨a, g, g5⟩, E⟩, f⟩
    show failC (withP y.1 pIu) y.2 ((a, ((Equiv.piSplitAt k (fun _ : Pre => Tab3)).symm (g, f)
      (preOf Hashes.shake pIu y), g5)), E) ↔ failC (withP y.1 pIu) y.2 ((a, (g, g5)), E)
    rw [hk0, hsk]
  rw [e1, e2, pr_prod_fst]
  exact h

/-! ## The game with `main`'s Lean issuance prover -/

/-- The unbound issuance proof system that accepts every request. -/
def PIaccU : NIZK IssueInstance :=
  ⟨fun _ _ _ => List.replicate issueProofBytes 0, fun _ _ => true⟩

/-- The unbound issuance proof system that rejects every request. -/
def PIrejU : NIZK IssueInstance :=
  ⟨fun _ _ _ => List.replicate issueProofBytes 0, fun _ _ => false⟩

lemma PIaccU_correct : PIaccU.Correct IssueRel issueProofBytes := fun _ _ _ _ _ =>
  ⟨List.length_replicate, rfl⟩

section GameL

variable [HasPrg] (A : AdversaryUNCH) (sk : Bool → Signer) (n : ℕ)

/-- The two Clients' `(nf_key, r)`. -/
def secOfN (s : SecN) : SecU := ((s.1.1, s.1.2.1), (s.2.1, s.2.2.1))

/-- **Client `c`'s unbound issuance statement and witness on `main`.** -/
def issYU (s : SecN) (c : Bool) : SW := issStmtU A.unc.um (secOfN s) c

/-- **Client `c`'s Lean issuance proof** on the raw shared tables of tape `x`: randomness the
Client's `ρ_iss`, `H₃` the column at the proof's prefix. -/
noncomputable def proveLU (x : NTU n) (c : Bool) : Except String ByteArray :=
  @Prover.prove (icPrg x.2.2.2.1.2) (recH Hashes.shake (withP (issYU A x.1 c).1 pIu)
      (issYU A x.1 c).2 (x.2.2.1 (preOf Hashes.shake pIu (issYU A x.1 c))) x.2.2.2.2 x.2.2.2.1.1)
    CrtGen.tables (withP (issYU A x.1 c).1 pIu) (issYU A x.1 c).2
    (ba (bif c then x.1.2 else x.1.1).2.2) (withP (issYU A x.1 c).1 pIu).params.witnessBytes

/-- **Anchor `c`'s verdict** on Client `c`'s request (`unbound_issue_response`, which has no length
check): the Client's Lean prover output a proof and the Lean verifier on the same tables accepts
it. -/
def AccLU (x : NTU n) (c : Bool) : Prop :=
  ∃ proof, proveLU A n x c = .ok proof ∧
    (@verify (icPrg x.2.2.2.1.2) (recH Hashes.shake (withP (issYU A x.1 c).1 pIu)
      (issYU A x.1 c).2 (x.2.2.1 (preOf Hashes.shake pIu (issYU A x.1 c))) x.2.2.2.2
      x.2.2.2.1.1) CrtGen.tables (withP (issYU A x.1 c).1 pIu) proof).accept = true

/-- The Anchor accepts unless the issuance fails (the event of `complete_rom_ic`). -/
lemma accLU_of (x : NTU n) (c : Bool)
    (h : ¬ issFailU (issYU A x.1 c) (bif c then x.1.2 else x.1.1).2.2 x.2.2.2.2 x.2.2.2.1
      x.2.2.1) : AccLU A n x c :=
  not_not.1 h

open scoped Classical in
/-- **The real game with `main`'s Lean issuance prover** in world `b`: the issuance proofs on the
raw shared tables, judged by the honest Anchors; if both accept, the rest is `realNN`'s integrand
for `PIaccU`, otherwise every query is refused (`PIrejU`). The issuance proofs are never shown. -/
noncomputable def realNNL (b : Bool) : ℝ :=
  pr (NTU n) (fun x =>
    if AccLU A n x false ∧ AccLU A n x true then
      evNN A PIaccU sk n b (hybVN Hashes.shake pIu (nsU n) (gameNN A PIaccU sk n b) 0 x)
    else
      evNN A PIrejU sk n b (hybVN Hashes.shake pIu (nsU n) (gameNN A PIrejU sk n b) 0 x))

set_option maxRecDepth 8192 in
/-- **Client `c`'s issuance fails with probability `≤ 2⁻¹¹³`.** -/
theorem pr_issFailU_le (c : Bool) :
    pr (NTU n) (fun x => issFailU (issYU A x.1 c) (bif c then x.1.2 else x.1.1).2.2 x.2.2.2.2
      x.2.2.2.1 x.2.2.1) ≤ 1 / 2 ^ 113 := by
  cases c
  · let e : (((ZK.Sim.Bytes 16 × Tab2G pIu) × (H3T × Tab5F)) × Cipher) ×
        (((Coins nfKeyBytes × Coins rBytes) × IssT) × CoinsN pIu (nsU n)) ≃ NTU n :=
      { toFun := fun w => (((w.2.1.1.1, (w.2.1.1.2, w.1.1.1.1)), w.2.1.2),
          (w.2.2, (w.1.1.2.1, ((w.1.1.2.2, w.1.2), w.1.1.1.2))))
        invFun := fun x => ((((x.1.1.2.2, x.2.2.2.2), (x.2.2.1, x.2.2.2.1.1)), x.2.2.2.1.2),
          (((x.1.1.1, x.1.1.2.1), x.1.2), x.2.1))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e]
    refine pr_le_of_snd fun o => ?_
    exact issue_complete_sharedU (issYU A ((o.1.1.1, (o.1.1.2, fun _ => 0)), o.1.2) false)
      (issStmtU_valid A.unc.um _ false)
  · let e : (((ZK.Sim.Bytes 16 × Tab2G pIu) × (H3T × Tab5F)) × Cipher) ×
        ((IssT × (Coins nfKeyBytes × Coins rBytes)) × CoinsN pIu (nsU n)) ≃ NTU n :=
      { toFun := fun w => ((w.2.1.1, (w.2.1.2.1, (w.2.1.2.2, w.1.1.1.1))),
          (w.2.2, (w.1.1.2.1, ((w.1.1.2.2, w.1.2), w.1.1.1.2))))
        invFun := fun x => ((((x.1.2.2.2, x.2.2.2.2), (x.2.2.1, x.2.2.2.1.1)), x.2.2.2.1.2),
          ((x.1.1, (x.1.2.1, x.1.2.2.1)), x.2.1))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← pr_equiv e]
    refine pr_le_of_snd fun o => ?_
    exact issue_complete_sharedU (issYU A (o.1.1, (o.1.2.1, (o.1.2.2, fun _ => 0))) true)
      (issStmtU_valid A.unc.um _ true)

open scoped Classical in
set_option maxRecDepth 8192 in
/-- **Replacing the Anchors' verdicts by `true` costs `2·2⁻¹¹³`.** -/
theorem realNNL_close (b : Bool) :
    |realNNL A sk n b - realNN A PIaccU sk n b| ≤ 2 / 2 ^ 113 := by
  unfold realNNL realNN hybN
  refine (abs_pr_sub_le_of_agree
    (fun x : NTU n =>
      if AccLU A n x false ∧ AccLU A n x true then
        evNN A PIaccU sk n b (hybVN Hashes.shake pIu (nsU n) (gameNN A PIaccU sk n b) 0 x)
      else
        evNN A PIrejU sk n b (hybVN Hashes.shake pIu (nsU n) (gameNN A PIrejU sk n b) 0 x))
    (fun x => evNN A PIaccU sk n b (hybVN Hashes.shake pIu (nsU n) (gameNN A PIaccU sk n b) 0 x))
    (fun x => issFailU (issYU A x.1 false) (bif false then x.1.2 else x.1.1).2.2 x.2.2.2.2
        x.2.2.2.1 x.2.2.1 ∨
      issFailU (issYU A x.1 true) (bif true then x.1.2 else x.1.1).2.2 x.2.2.2.2 x.2.2.2.1
        x.2.2.1)
    fun x hx => ?_).trans ((pr_or_le _ _).trans ?_)
  · simp only [not_or] at hx
    have h0 := accLU_of A n x false hx.1
    have h1 := accLU_of A n x true hx.2
    simp only [h0, h1, and_self, ↓reduceIte]
  · have h0 := pr_issFailU_le A n false
    have h1 := pr_issFailU_le A n true
    have : (2 : ℝ) / 2 ^ 113 = 1 / 2 ^ 113 + 1 / 2 ^ 113 := by ring
    linarith

/-- **Unbound Moussaka U5(b) on `main` with the Lean issuance prover and the Anchors' Lean
verifier**, `n` adaptive redemption queries, all tables shared. For signers correct for their
keys, Anchor Sets with both issuers, a guess with consistent reads and the PRF reductions at fixed
rest of the tape,

    |Pr[W₀] − Pr[W₁]| ≤ 2·(2ⁿ − 1)·(εS(q₃ + n, q_E + 2n·4607) + Δ23N(9, n))
        + 2·(2ⁿ − 1)·(n·noHitProb + 2n·(q₅ + 312n + 1)·2⁻¹²⁸ + n²·313·2⁻¹²⁸)
        + 2·(φ false + φ true) + 2·εprf + 4·2⁻¹¹³.

No abstract proof system remains (`PIaccU` is a device of the proof), and no assumption on `UCom`. -/
theorem anonymityNC_main_U_leanN (hsk : ∀ c, (sk c).Correct (A.pk c))
    (hK : Contains A.unc.nc) {q3 qE q5 : ℕ} (hC : A.ConsH q3 qE)
    (h5 : ∀ y u G2 T, (A.R5 y u G2 T).card ≤ q5) {εprf : ℝ}
    (hprf : ∀ b z, prfAdvNC (redNN A n b z) ≤ εprf) :
    |realNNL A sk n false - realNNL A sk n true| ≤
      2 * ((2 ^ n - 1) * (εS (q3 + n) (qE + 2 * n * 4607) + Δ23N 9 n)) +
        2 * ((2 ^ n - 1) * (n * noHitProb + n * (2 * (((q5 + n * 312 : ℕ) + 1) / 2 ^ 128)) +
          n * n * (((312 : ℕ) + 1) / 2 ^ 128))) +
        2 * (phiU A.unc.nc sk false + phiU A.unc.nc sk true) + 2 * εprf + 4 / 2 ^ 113 := by
  have h := anonymityNC_main_U_sharedAllN A PIaccU sk n hsk hK hC h5 hprf
  have k0 := kappa_eq_zero A.unc.nc PIaccU PIaccU_correct
  have p0 := psi_le A.unc.nc PIaccU sk false
  have p1 := psi_le A.unc.nc PIaccU sk true
  have c0 := realNNL_close A sk n false
  have c1 := realNNL_close A sk n true
  rw [k0] at p0 p1
  rw [abs_sub_le_iff] at h c0 c1 ⊢
  constructor <;> linarith

end GameL

end VoleMole.Privacy.MoussakaUnbound
