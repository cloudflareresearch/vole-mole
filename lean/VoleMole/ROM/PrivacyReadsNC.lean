import VoleMole.ROM.PrivacyReads
import VoleMole.Privacy.MoussakaNCRA
import VoleMole.Privacy.SeedXOFNC

/-!
# Moussaka's non-colluding game with the Moderator's choices an oracle computation

`Privacy/MoussakaNCRA.lean` takes the non-colluding Moderator's setup (its contexts, keys, Anchor
Sets and digests, read off the tables) as a function of the slices and the shared tables, with
the semantic budget `KBudget` (consistent table readers, `ZK.Sim.SReads`). Here the setup is a
VCVio oracle computation over the four slices and the shared tables (`ROM.Reads.TSpec`), run on
the game's tables (`ROM.Reads.runT`), and its budget is the syntactic query bound
`ROM.Reads.QBudget`. `KBudget` is then a theorem (`AdversaryNCOC.kBudget`, from
`ROM.Reads.sReads_runT`): consistency holds by construction.

**`anonymityNCOC_lean_num`**, **`unlinkabilityNCOC_lean_num`** and their `_perm` versions are the
`*NCRA_lean_num(_perm)` bounds, unchanged, for `A.toRA`, with `QBudget` in place of `KBudget`.

**With the real Clients' seeds** (`Privacy/SeedXOFNC.lean`'s `seedGameM`): the Moderator at XOF
table `g` is `A g`, the Anchors' signers `sk g`; `anonymityNCRA_lean_num_seed`,
`unlinkabilityNCRA_lean_num_seed`, `anonymityNCOC_lean_num_seed` (and `_perm_seed` for anonymity)
add `2·(2q_g + 2)·2⁻²⁵⁶`, the abort term bounded uniformly in the table and the state.
-/

open OracleComp OracleSpec

set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy.Moussaka

open VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ROM.Reads
open VoleMole.Spec VoleMole.Spec.Moussaka

/-- **The non-colluding Moderator whose choices are an oracle computation over the tables**: the
setup queries the four `H₃` slices and the shared tables and returns a state `σ`; the contexts,
keys, Anchor Sets, digests and the guess are those of `adv σ`. -/
structure AdversaryNCOC (R : Type) (Sg : Type) where
  setup : OracleComp (TSpec (Bool × Bool) R (preLen pI)) Sg
  adv : Sg → AdversaryNCRO R

namespace AdversaryNCOC

variable {R Sg : Type} (A : AdversaryNCOC R Sg)

/-- **The Moderator as a function of the tables**: the setup is the run of `setup` on the game's
slices and tables. -/
def toRA : AdversaryNCRA R Sg where
  setup sl u := runT (TKey.read (sl4 sl) u) A.setup
  adv := A.adv

variable {A}

/-- **The query budget gives the setup's budget** (`KBudget`): consistency by construction. -/
theorem kBudget {k3 k2 k5 kE : ℕ} (h : QBudget A.setup k3 k2 k5 kE) :
    A.toRA.KBudget k3 k2 k5 kE where
  s0 g₁ gL gR := sReads_of_eq h (sl4 ((g₁, g₁), (gL, gR))) (false, false)
    fun t => by rw [readAt, sl4_ff]; rfl
  s1 g₀ gL gR := sReads_of_eq h (sl4 ((g₀, g₀), (gL, gR))) (false, true)
    fun t => by rw [readAt, sl4_ft]; rfl
  sL g₀ g₁ gR := sReads_of_eq (p := pR) h (sl4 ((g₀, g₁), (gR, gR))) (true, false)
    fun t => by rw [readAt, sl4_tf]; rfl
  sR g₀ g₁ gL := sReads_of_eq (p := pR) h (sl4 ((g₀, g₁), (gL, gL))) (true, true)
    fun t => by rw [readAt, sl4_tt]; rfl

end AdversaryNCOC

variable {Sg : Type} (idx : AnchorSet → UOVKey → ℕ) (sk : Sg → Bool → Signer)

/-- **Theorem 4(b′) with the Moderator's choices an oracle computation over the tables**
(`anonymityNCRA_lean_num` for `A.toRA`, function rows): the setup makes at most `k₃` queries to
each slice, `k₂` to `H₂³`, `k₅` to `H₅` and `k_E` to the cipher (`QBudget`); no consistency
hypothesis. -/
theorem anonymityNCOC_lean_num (A : AdversaryNCOC (Blk → Blk) Sg)
    (hsk : ∀ σ c, (sk σ c).Correct ((A.adv σ).pk c)) (hidx : IdxSound idx)
    {q3 q5 qE k3 k2 k5 kE : ℕ} (hA : A.toRA.Budget q3 q5 qE) (hK : QBudget A.setup k3 k2 k5 kE)
    {φ : Bool → ℝ} (hφ : ∀ σ c, phi (A.adv σ).nc (sk σ) c ≤ φ c) :
    |pr _ (realGameNCRA A.toRA idx leanPI leanVI sk leanPR false) -
        pr _ (realGameNCRA A.toRA idx leanPI leanVI sk leanPR true)| ≤
      4 * εAd 9 q3 (q5 + 2496) (qE + 23035) k3 k2 k5 kE + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * (φ false + φ true) + 4 * ((k3 + q3 : ℕ) / 2 ^ 128) :=
  anonymityNCRA_lean_num A.toRA idx sk hsk hidx hA (AdversaryNCOC.kBudget hK) hφ

/-- **`anonymityNCOC_lean_num` with AES as uniformly random permutations**. -/
theorem anonymityNCOC_lean_num_perm (A : AdversaryNCOC (Equiv.Perm Blk) Sg)
    (hsk : ∀ σ c, (sk σ c).Correct ((A.adv σ).pk c)) (hidx : IdxSound idx)
    {q3 q5 qE k3 k2 k5 kE : ℕ} (hA : A.toRA.Budget q3 q5 qE) (hK : QBudget A.setup k3 k2 k5 kE)
    {φ : Bool → ℝ} (hφ : ∀ σ c, phi (A.adv σ).nc (sk σ) c ≤ φ c) :
    |pr _ (realGameNCRA A.toRA idx leanPI leanVI sk leanPR false) -
        pr _ (realGameNCRA A.toRA idx leanPI leanVI sk leanPR true)| ≤
      4 * εAdPm pR 9 q3 (q5 + 2496) (qE + 23035) k3 k2 k5 kE + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * (φ false + φ true) + 4 * ((k3 + q3 : ℕ) / 2 ^ 128) :=
  anonymityNCRA_lean_num_perm A.toRA idx sk hsk hidx hA (AdversaryNCOC.kBudget hK) hφ

/-- **Unlinkability with the Moderator's choices an oracle computation over the tables**
(function rows; one Anchor at every state, any index rule). -/
theorem unlinkabilityNCOC_lean_num (A : AdversaryNCOC (Blk → Blk) Sg)
    (hsk : ∀ σ c, (sk σ c).Correct ((A.adv σ).pk c))
    (hpk : ∀ σ, (A.adv σ).pk false = (A.adv σ).pk true) (hs : ∀ σ, sk σ false = sk σ true)
    {q3 q5 qE k3 k2 k5 kE : ℕ} (hA : A.toRA.Budget q3 q5 qE) (hK : QBudget A.setup k3 k2 k5 kE) :
    |pr _ (realGameNCRA A.toRA idx leanPI leanVI sk leanPR false) -
        pr _ (realGameNCRA A.toRA idx leanPI leanVI sk leanPR true)| ≤
      4 * εAd 9 q3 (q5 + 2496) (qE + 23035) k3 k2 k5 kE + 2 * (noHitProb + 1 / 2 ^ 1024) +
        4 * ((k3 + q3 : ℕ) / 2 ^ 128) :=
  unlinkabilityNCRA_lean_num A.toRA idx sk hsk hpk hs hA (AdversaryNCOC.kBudget hK)

/-- Unlinkability with the setup an oracle computation and AES as random permutations. -/
theorem unlinkabilityNCOC_lean_num_perm (A : AdversaryNCOC (Equiv.Perm Blk) Sg)
    (hsk : ∀ σ c, (sk σ c).Correct ((A.adv σ).pk c))
    (hpk : ∀ σ, (A.adv σ).pk false = (A.adv σ).pk true) (hs : ∀ σ, sk σ false = sk σ true)
    {q3 q5 qE k3 k2 k5 kE : ℕ} (hA : A.toRA.Budget q3 q5 qE) (hK : QBudget A.setup k3 k2 k5 kE) :
    |pr _ (realGameNCRA A.toRA idx leanPI leanVI sk leanPR false) -
        pr _ (realGameNCRA A.toRA idx leanPI leanVI sk leanPR true)| ≤
      4 * εAdPm pR 9 q3 (q5 + 2496) (qE + 23035) k3 k2 k5 kE + 2 * (noHitProb + 1 / 2 ^ 1024) +
        4 * ((k3 + q3 : ℕ) / 2 ^ 128) :=
  unlinkabilityNCRA_lean_num_perm A.toRA idx sk hsk hpk hs hA (AdversaryNCOC.kBudget hK)

/-! ## With the real Clients' seeds -/

/-- **`realGameNCRA` (the Lean provers and verifier) with the seeds.** -/
noncomputable def seedGameNCRA {R : Type} [Fintype R] [Nonempty R] [CipherRow R]
    (A : XofM → AdversaryNCRA R Sg) (sk : XofM → Sg → Bool → Signer) (b : Bool) :
    (Bool × Bool → SeedB) × (T4 (ShM R) × XofM) → Prop :=
  seedGameM (fun g => realGameNCRA (A g) idx leanPI leanVI (sk g) leanPR) b

/-- **`anonymityNCRA_lean_num` with the seed XOF.** -/
theorem anonymityNCRA_lean_num_seed (A : XofM → AdversaryNCRA (Blk → Blk) Sg)
    (sk : XofM → Sg → Bool → Signer) (hsk : ∀ g σ c, (sk g σ c).Correct (((A g).adv σ).pk c))
    (hidx : IdxSound idx) {q3 q5 qE k3 k2 k5 kE qg : ℕ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hK : ∀ g, (A g).KBudget k3 k2 k5 kE) {φ : Bool → ℝ}
    (hφ : ∀ g σ c, phi ((A g).adv σ).nc (sk g σ) c ≤ φ c)
    (hg : ∀ b z, RdX (fun g => realGameNCRA (A g) idx leanPI leanVI (sk g) leanPR b z) qg) :
    |pr _ (seedGameNCRA idx A sk false) - pr _ (seedGameNCRA idx A sk true)| ≤
      4 * εAd 9 q3 (q5 + 2496) (qE + 23035) k3 k2 k5 kE + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * (φ false + φ true) + 4 * ((k3 + q3 : ℕ) / 2 ^ 128) +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameNCRA (A g) idx leanPI leanVI (sk g) leanPR) hg fun g =>
    anonymityNCRA_lean_num (A g) idx (sk g) (hsk g) hidx (hA g) (hK g) (hφ g)

/-- **`anonymityNCRA_lean_num_perm` with the seed XOF.** -/
theorem anonymityNCRA_lean_num_perm_seed (A : XofM → AdversaryNCRA (Equiv.Perm Blk) Sg)
    (sk : XofM → Sg → Bool → Signer) (hsk : ∀ g σ c, (sk g σ c).Correct (((A g).adv σ).pk c))
    (hidx : IdxSound idx) {q3 q5 qE k3 k2 k5 kE qg : ℕ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hK : ∀ g, (A g).KBudget k3 k2 k5 kE) {φ : Bool → ℝ}
    (hφ : ∀ g σ c, phi ((A g).adv σ).nc (sk g σ) c ≤ φ c)
    (hg : ∀ b z, RdX (fun g => realGameNCRA (A g) idx leanPI leanVI (sk g) leanPR b z) qg) :
    |pr _ (seedGameNCRA idx A sk false) - pr _ (seedGameNCRA idx A sk true)| ≤
      4 * εAdPm pR 9 q3 (q5 + 2496) (qE + 23035) k3 k2 k5 kE + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * (φ false + φ true) + 4 * ((k3 + q3 : ℕ) / 2 ^ 128) +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameNCRA (A g) idx leanPI leanVI (sk g) leanPR) hg fun g =>
    anonymityNCRA_lean_num_perm (A g) idx (sk g) (hsk g) hidx (hA g) (hK g) (hφ g)

/-- **`unlinkabilityNCRA_lean_num` with the seed XOF.** -/
theorem unlinkabilityNCRA_lean_num_seed (A : XofM → AdversaryNCRA (Blk → Blk) Sg)
    (sk : XofM → Sg → Bool → Signer) (hsk : ∀ g σ c, (sk g σ c).Correct (((A g).adv σ).pk c))
    (hpk : ∀ g σ, ((A g).adv σ).pk false = ((A g).adv σ).pk true)
    (hs : ∀ g σ, sk g σ false = sk g σ true)
    {q3 q5 qE k3 k2 k5 kE qg : ℕ} (hA : ∀ g, (A g).Budget q3 q5 qE)
    (hK : ∀ g, (A g).KBudget k3 k2 k5 kE)
    (hg : ∀ b z, RdX (fun g => realGameNCRA (A g) idx leanPI leanVI (sk g) leanPR b z) qg) :
    |pr _ (seedGameNCRA idx A sk false) - pr _ (seedGameNCRA idx A sk true)| ≤
      4 * εAd 9 q3 (q5 + 2496) (qE + 23035) k3 k2 k5 kE + 2 * (noHitProb + 1 / 2 ^ 1024) +
        4 * ((k3 + q3 : ℕ) / 2 ^ 128) + 2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  abs_seedGameM_sub_le (fun g => realGameNCRA (A g) idx leanPI leanVI (sk g) leanPR) hg fun g =>
    unlinkabilityNCRA_lean_num (A g) idx (sk g) (hsk g) (hpk g) (hs g) (hA g) (hK g)

/-- **`anonymityNCOC_lean_num` (the setup an oracle computation) with the seed XOF.** -/
theorem anonymityNCOC_lean_num_seed (A : XofM → AdversaryNCOC (Blk → Blk) Sg)
    (sk : XofM → Sg → Bool → Signer) (hsk : ∀ g σ c, (sk g σ c).Correct (((A g).adv σ).pk c))
    (hidx : IdxSound idx) {q3 q5 qE k3 k2 k5 kE qg : ℕ} (hA : ∀ g, (A g).toRA.Budget q3 q5 qE)
    (hK : ∀ g, QBudget (A g).setup k3 k2 k5 kE) {φ : Bool → ℝ}
    (hφ : ∀ g σ c, phi ((A g).adv σ).nc (sk g σ) c ≤ φ c)
    (hg : ∀ b z, RdX (fun g => realGameNCRA (A g).toRA idx leanPI leanVI (sk g) leanPR b z) qg) :
    |pr _ (seedGameNCRA idx (fun g => (A g).toRA) sk false) -
        pr _ (seedGameNCRA idx (fun g => (A g).toRA) sk true)| ≤
      4 * εAd 9 q3 (q5 + 2496) (qE + 23035) k3 k2 k5 kE + 2 * (noHitProb + 1 / 2 ^ 1024) +
        2 * (φ false + φ true) + 4 * ((k3 + q3 : ℕ) / 2 ^ 128) +
        2 * ((2 * qg + 2 : ℕ) / 2 ^ 256) :=
  anonymityNCRA_lean_num_seed idx (fun g => (A g).toRA) sk hsk hidx hA
    (fun g => AdversaryNCOC.kBudget (hK g)) hφ hg

end VoleMole.Privacy.Moussaka
