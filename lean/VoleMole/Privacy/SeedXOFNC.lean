import VoleMole.Privacy.SeedXOFGames
import VoleMole.Privacy.MoussakaNCSh

/-!
# Moussaka's non-colluding games with the seed XOF

`Privacy/SeedXOFGames.lean`'s hop for Theorem 4(b′) in the random-oracle and ideal-cipher model
(`Privacy/MoussakaNCRO.lean`, per-proof slices; `Privacy/MoussakaNCSh.lean`, one shared `H₃`). The
non-colluding game has the tape of the 4(a) game (two issuance tapes `(nf, r, ρ_iss)`, two
redemption tapes `ρ_red`, the slices and the shared tables), so the real Clients' seeds enter as in
`seedGameM`: the issue XOF's cell `(nf ‖ r, ρ_iss)` at `(false, seed)`, the redeem XOF's `ρ_red` at
`(true, seed')`. The Moderator at XOF table `g` is `A g`, the honest Anchors' signers `sk g` (correct
for `A g`'s keys); its run reads at most `q_g` cells (`hg`).

Each theorem is the existing bound plus `2·(2q_g + 2)·2⁻²⁵⁶`; for anonymity the abort term is
bounded uniformly in the table (`hφ`: `φ₀ + φ₁ ≤ φ` at every `g`).

* Per-proof slices: `anonymityNCRO_lean_num_seed`, `unlinkabilityNCRO_lean_num_seed` (and `_perm`).
* One shared `H₃`: `anonymityNCSh_num_seed`, `unlinkabilityNCSh_num_seed` (and `_perm`).
-/

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.Moussaka

open VoleMole.Spec VoleMole.Spec.Moussaka VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge

section Games

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R] (idx : AnchorSet → UOVKey → ℕ)

/-- **`realGameNCRO` (Lean provers and verifier, per-proof slices) with the seeds.** -/
noncomputable def seedGameNCRO (A : XofM → AdversaryNCRO R) (sk : XofM → Bool → Signer) (b : Bool) :
    (Bool × Bool → SeedB) × (T4 (ShM R) × XofM) → Prop :=
  seedGameM (fun g => realGameNCRO (A g) idx leanPI leanVI (sk g) leanPR) b

/-- **`realGameNCSh` (one shared `H₃`) with the seeds.** -/
noncomputable def seedGameNCSh (A : XofM → AdversaryNCRO (RowH R)) (sk : XofM → Bool → Signer)
    (b : Bool) : (Bool × Bool → SeedB) × (T4 (ShM (RowH R)) × XofM) → Prop :=
  seedGameM (fun g => realGameNCSh (A g) idx (sk g)) b

end Games

section Thms

variable (idx : AnchorSet → UOVKey → ℕ)

/-- **`anonymityNCRO_lean_num` (Theorem 4(b′), per-proof slices) with the seed XOF.** -/
theorem anonymityNCRO_lean_num_seed (A : XofM → AdversaryNCRO (Blk → Blk))
    (sk : XofM → Bool → Signer) (hsk : ∀ g c, (sk g c).Correct ((A g).pk c)) (hidx : IdxSound idx)
    {q3 q5 qE qg : ℕ} {φ : ℝ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hφ : ∀ g, phi (A g).nc (sk g) false + phi (A g).nc (sk g) true ≤ φ)
    (hg : ∀ b z, RdX (fun g => realGameNCRO (A g) idx leanPI leanVI (sk g) leanPR b z) qg) :
    |pr _ (seedGameNCRO idx A sk false) - pr _ (seedGameNCRO idx A sk true)| ≤
      4 * εRO q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) + 2 * φ +
        4 * (q3 / 2 ^ 128) + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameNCRO (A g) idx leanPI leanVI (sk g) leanPR) hg fun g => by
    have h := anonymityNCRO_lean_num (A g) idx (sk g) (hsk g) hidx (hA g)
    have := hφ g
    generalize (2 : ℝ) ^ 1024 = K at h ⊢
    linarith

/-- **`anonymityNCRO_lean_num_perm` with the seed XOF.** -/
theorem anonymityNCRO_lean_num_perm_seed (A : XofM → AdversaryNCRO (Equiv.Perm Blk))
    (sk : XofM → Bool → Signer) (hsk : ∀ g c, (sk g c).Correct ((A g).pk c)) (hidx : IdxSound idx)
    {q3 q5 qE qg : ℕ} {φ : ℝ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hφ : ∀ g, phi (A g).nc (sk g) false + phi (A g).nc (sk g) true ≤ φ)
    (hg : ∀ b z, RdX (fun g => realGameNCRO (A g) idx leanPI leanVI (sk g) leanPR b z) qg) :
    |pr _ (seedGameNCRO idx A sk false) - pr _ (seedGameNCRO idx A sk true)| ≤
      4 * εROPm pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) + 2 * φ +
        4 * (q3 / 2 ^ 128) + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameNCRO (A g) idx leanPI leanVI (sk g) leanPR) hg fun g => by
    have h := anonymityNCRO_lean_num_perm (A g) idx (sk g) (hsk g) hidx (hA g)
    have := hφ g
    generalize (2 : ℝ) ^ 1024 = K at h ⊢
    linarith

/-- **`unlinkabilityNCRO_lean_num` (one Anchor, per-proof slices) with the seed XOF.** -/
theorem unlinkabilityNCRO_lean_num_seed (A : XofM → AdversaryNCRO (Blk → Blk))
    (sk : XofM → Bool → Signer) (hsk : ∀ g c, (sk g c).Correct ((A g).pk c))
    (hpk : ∀ g, (A g).pk false = (A g).pk true) (hs : ∀ g, sk g false = sk g true)
    {q3 q5 qE qg : ℕ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hg : ∀ b z, RdX (fun g => realGameNCRO (A g) idx leanPI leanVI (sk g) leanPR b z) qg) :
    |pr _ (seedGameNCRO idx A sk false) - pr _ (seedGameNCRO idx A sk true)| ≤
      4 * εRO q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) + 4 * (q3 / 2 ^ 128) +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameNCRO (A g) idx leanPI leanVI (sk g) leanPR) hg fun g =>
    unlinkabilityNCRO_lean_num (A g) idx (sk g) (hsk g) (hpk g) (hs g) (hA g)

/-- **`unlinkabilityNCRO_lean_num_perm` with the seed XOF.** -/
theorem unlinkabilityNCRO_lean_num_perm_seed (A : XofM → AdversaryNCRO (Equiv.Perm Blk))
    (sk : XofM → Bool → Signer) (hsk : ∀ g c, (sk g c).Correct ((A g).pk c))
    (hpk : ∀ g, (A g).pk false = (A g).pk true) (hs : ∀ g, sk g false = sk g true)
    {q3 q5 qE qg : ℕ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hg : ∀ b z, RdX (fun g => realGameNCRO (A g) idx leanPI leanVI (sk g) leanPR b z) qg) :
    |pr _ (seedGameNCRO idx A sk false) - pr _ (seedGameNCRO idx A sk true)| ≤
      4 * εROPm pR q3 (q5 + 2496) (qE + 23035) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        4 * (q3 / 2 ^ 128) + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameNCRO (A g) idx leanPI leanVI (sk g) leanPR) hg fun g =>
    unlinkabilityNCRO_lean_num_perm (A g) idx (sk g) (hsk g) (hpk g) (hs g) (hA g)

/-- **`anonymityNCSh_num` (Theorem 4(b′), one shared `H₃`) with the seed XOF.** -/
theorem anonymityNCSh_num_seed (A : XofM → AdversaryNCRO (RowH (Blk → Blk)))
    (sk : XofM → Bool → Signer) (hsk : ∀ g c, (sk g c).Correct ((A g).pk c)) (hidx : IdxSound idx)
    {q3 q5 qE qg : ℕ} {φ : ℝ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hφ : ∀ g, phi (A g).nc (sk g) false + phi (A g).nc (sk g) true ≤ φ)
    (hg : ∀ b z, RdX (fun g => realGameNCSh (A g) idx (sk g) b z) qg) :
    |pr _ (seedGameNCSh idx A sk false) - pr _ (seedGameNCSh idx A sk true)| ≤
      4 * εRO (qE + 23038) (q5 + 2496) (qE + 23038) + 2 * (noHitProb + 1 / 2 ^ 1024) + 2 * φ +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameNCSh (A g) idx (sk g)) hg fun g => by
    have h := anonymityNCSh_num (A g) idx (sk g) (hsk g) hidx (hA g)
    have := hφ g
    generalize (2 : ℝ) ^ 1024 = K at h ⊢
    linarith

/-- **`anonymityNCSh_num_perm` with the seed XOF.** -/
theorem anonymityNCSh_num_perm_seed (A : XofM → AdversaryNCRO (RowH (Equiv.Perm Blk)))
    (sk : XofM → Bool → Signer) (hsk : ∀ g c, (sk g c).Correct ((A g).pk c)) (hidx : IdxSound idx)
    {q3 q5 qE qg : ℕ} {φ : ℝ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hφ : ∀ g, phi (A g).nc (sk g) false + phi (A g).nc (sk g) true ≤ φ)
    (hg : ∀ b z, RdX (fun g => realGameNCSh (A g) idx (sk g) b z) qg) :
    |pr _ (seedGameNCSh idx A sk false) - pr _ (seedGameNCSh idx A sk true)| ≤
      4 * εROPm pR (qE + 23038) (q5 + 2496) (qE + 23038) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * φ + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameNCSh (A g) idx (sk g)) hg fun g => by
    have h := anonymityNCSh_num_perm (A g) idx (sk g) (hsk g) hidx (hA g)
    have := hφ g
    generalize (2 : ℝ) ^ 1024 = K at h ⊢
    linarith

/-- **`unlinkabilityNCSh_num` (one Anchor, one shared `H₃`) with the seed XOF.** -/
theorem unlinkabilityNCSh_num_seed (A : XofM → AdversaryNCRO (RowH (Blk → Blk)))
    (sk : XofM → Bool → Signer) (hsk : ∀ g c, (sk g c).Correct ((A g).pk c))
    (hpk : ∀ g, (A g).pk false = (A g).pk true) (hs : ∀ g, sk g false = sk g true)
    {q3 q5 qE qg : ℕ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hg : ∀ b z, RdX (fun g => realGameNCSh (A g) idx (sk g) b z) qg) :
    |pr _ (seedGameNCSh idx A sk false) - pr _ (seedGameNCSh idx A sk true)| ≤
      4 * εRO (qE + 23038) (q5 + 2496) (qE + 23038) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameNCSh (A g) idx (sk g)) hg fun g =>
    unlinkabilityNCSh_num (A g) idx (sk g) (hsk g) (hpk g) (hs g) (hA g)

/-- **`unlinkabilityNCSh_num_perm` with the seed XOF.** -/
theorem unlinkabilityNCSh_num_perm_seed (A : XofM → AdversaryNCRO (RowH (Equiv.Perm Blk)))
    (sk : XofM → Bool → Signer) (hsk : ∀ g c, (sk g c).Correct ((A g).pk c))
    (hpk : ∀ g, (A g).pk false = (A g).pk true) (hs : ∀ g, sk g false = sk g true)
    {q3 q5 qE qg : ℕ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hg : ∀ b z, RdX (fun g => realGameNCSh (A g) idx (sk g) b z) qg) :
    |pr _ (seedGameNCSh idx A sk false) - pr _ (seedGameNCSh idx A sk true)| ≤
      4 * εROPm pR (qE + 23038) (q5 + 2496) (qE + 23038) + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameNCSh (A g) idx (sk g)) hg fun g =>
    unlinkabilityNCSh_num_perm (A g) idx (sk g) (hsk g) (hpk g) (hs g) (hA g)

end Thms

end VoleMole.Privacy.Moussaka
