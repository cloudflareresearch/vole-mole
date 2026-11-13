import VoleMole.Assumptions.FDHPerm
import VoleMole.Assumptions.SimLinks

/-!
# Ratatouille's balance under OMPR, with `Tag` a random permutation with inverse queries

`Assumptions/RatatouilleOMPR.lean` (`balance_le_ompr`) and `Assumptions/SimLinks.lean`
(`balance_le_ompr_sim`) with the modelling step moved from the random-function model of `Tag` to
the permutation model (`Assumptions/FDHPerm.lean`, `uov-assumptions.md` §5.8): `KP800` is a random
permutation of the blocks `Target × Z`, with forward and inverse queries, in the standalone UF-Tag
game, and `Tag(c, x)` is the first component of `π(emb (c, x))` for an injective encoding `emb`.

* `TagIdealP`: **the modelling hypothesis.** The strict UF-Tag advantage of the forger `B` is at
  most the permutation-model det-FDH advantage `advFDHPerm` of some forger `A'` (with `q_f`
  forward, `q_i` inverse and `q_S` signing queries). As `TagIdeal`, it is a hypothesis, not proved;
  it replaces the random-function heuristic by the permutation one, as the paper's Lemma 2.1 does.
* **`balance_le_ompr_perm`**, `balance_le_ompr_rate_perm` (per-relation extraction),
  **`balance_le_ompr_sim_perm`**, `balance_le_ompr_rate_sim_perm` (simultaneous extraction):

      Pr[win BAL] ≤ ε_bal + (Adv^{ompr}(B'; k + 1 + q_S, q_S) + Pr[σ errs on one of k + 1 + q_S targets]
                             + permEps + failAdv(B)) + Adv^{coll}(C),

  `k = q_f + 1 + 2q_S`, `permEps = (q_f + q_i + q_S + 1)²/|Target × Z| + q_i·|M|/|Target × Z|`
  (`M` the pairs `(c, x)`). For KP800, `|Target × Z| = 2^{800}` and `|M| = 2^{320}`, so the
  inverse term is `q_i·2^{−480}` (the paper's `q_K·2^{−479}`) and the switching term
  `(q_f + q_i + q_S + 1)²·2^{−800}` (the paper's `q_K²·2^{−799}`).

The cipher of the proofs (AES) is the ideal cipher of the PRF view here (`CTable`); with AES as
random permutations: `Assumptions/RatatouillePermSim.lean` (`balance_le_ompr_simP`,
`balance_le_ompr_sim_permP`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.IdealTag.Rat

open VoleMole.Prob VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.IC.RatBalance
open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Assumptions.UOV
open VoleMole.Assumptions.IdealTag VoleMole.ROM.OneMore VoleMole.Assumptions.UOV.FDHPerm

/-- The permutation-model det-FDH adversaries for Ratatouille's messages `(c, x)`, the blocks
`Target × Z` and the world `specR AR`. -/
abbrev FDHPermAdv {DR : Type} (AR : DR → Type) (Z : Type) :=
  PublicKey → ProbComp (OracleComp (specFP AR (Commitment × Credits) Target Z (Option Preimage))
    ((Commitment × Credits) × Option Preimage))

/-- **The modelling hypothesis `TagIdealP`**: the strict UF-Tag advantage of the forger `B`
against the concrete `Tag` is at most the det-FDH advantage of the forger `A'` with `Tag` the
first component of a random permutation with inverse queries (`advFDHPerm`). -/
def TagIdealP {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
    {Z : Type} [DecidableEq Z] [SampleableType Z] [Fintype Z]
    {Tb : Type} [SampleableType Tb] (pk : PublicKey) (σ : Signer) (B : TagForger Tb)
    (emb : Commitment × Credits → Target × Z)
    (A' : FDHPermAdv AR Z) : Prop :=
  ufTagStrictAdv pk σ B ≤ advFDHPerm (ratTrap pk σ) emb A'

section Balance

variable {Zs : Sizes} {S : Type} (lr : Bool) (pkU : UovPk) (A : RoundAdv S (Op Zs) Resp) (N : ℕ)
  {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Z : Type} [DecidableEq Z] [SampleableType Z] [Fintype Z]
  {emb : Commitment × Credits → Target × Z} [SampleableType (Bc emb)]

/-- **The forgery term in the permutation model of `Tag`**: under `TagIdealP`,
`Adv^{uf-tag}(B) ≤ Adv^{ompr}(B') + Pr[σ errs] + permEps + failAdv(B)`. -/
theorem ufTag_le_ompr_perm {Tb : Type} [SampleableType Tb] (σ : Signer) (τ : Target → Preimage)
    (B : TagForger Tb)
    (hemb : Function.Injective emb) (A' : FDHPermAdv AR Z) {qf qi qS : ℕ}
    (hA' : ∀ pk, ∀ a ∈ support (A' pk), FPBudget qf qi qS a)
    (hTag : TagIdealP pkU.map σ (B.noProbe τ) emb A') :
    ufTagAdv pkU.map σ B ≤
      advOMPR (ratTrap pkU.map σ) (qf + 1 + qS + qS + 1 + qS) qS
          (ompiRed (ARF AR emb) (qf + 1 + qS + qS + 1) qS (fdhRed (ARF AR emb) (fdhPermRed emb A'))) +
        badTargets (ratTrap pkU.map σ) (qf + 1 + qS + qS + 1 + qS) +
        CTUFPerm.permEps (qf + qi + qS + 1) qi (Fintype.card (Commitment × Credits))
          (Fintype.card (Target × Z)) +
        failAdv σ B :=
  (ufTagAdv_le_strict pkU.map σ B τ).trans
    (add_le_add (hTag.trans (advFDHPerm_le_ompr hemb (ratTrap pkU.map σ) A' hA')) le_rfl)

/-- **Theorem 1 (balance) under one-more-UOV, `Tag` a random permutation with inverse queries**:
for every completion `τ` of the signer and every permutation-model forger `A'` (at most `q_f`
forward, `q_i` inverse and `q_S` signing queries) for which the modelling hypothesis `TagIdealP`
holds for the reduction's probe-free forger,

    Pr[win BAL] ≤ N·ε_iss + N·ε_spend
      + (Adv^{ompr}(B'; k + 1 + q_S, q_S) + Pr[σ errs on one of k + 1 + q_S targets] + permEps
         + failAdv(B)) + Adv^{coll}(C),

`k = q_f + 1 + 2q_S`, `B' = ompiRed (k + 1) q_S (fdhRed (fdhPermRed A'))`, the OMPR game at the
Issuer's key `(pkU, σ)`. -/
theorem balance_le_ompr_perm (σ : Signer) (τ : Target → Preimage)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
    (hemb : Function.Injective emb) (A' : FDHPermAdv AR Z) {qf qi qS : ℕ}
    (hA' : ∀ pk, ∀ a ∈ support (A' pk), FPBudget qf qi qS a)
    (hTag : TagIdealP pkU.map σ
      ((forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)).noProbe τ) emb A') :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      N * epsIss (N * (eA + eVR lr pkU verifyCellBound)) (N • (qA + (extractorQueries + verifierQueries))) +
        N * epsSpend (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) +
        (advOMPR (ratTrap pkU.map σ) (qf + 1 + qS + qS + 1 + qS) qS
            (ompiRed (ARF AR emb) (qf + 1 + qS + qS + 1) qS (fdhRed (ARF AR emb) (fdhPermRed emb A'))) +
          badTargets (ratTrap pkU.map σ) (qf + 1 + qS + qS + 1 + qS) +
          CTUFPerm.permEps (qf + qi + qS + 1) qi (Fintype.card (Commitment × Credits))
            (Fintype.card (Target × Z)) +
          failAdv σ (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdv lr pkU verQL A N σ := by
  refine le_trans (balance_le_ufTag lr pkU A N σ hdig hqA hnA heA) ?_
  gcongr
  exact ufTag_le_ompr_perm pkU σ τ _ hemb A' hA' hTag

/-- **The same with the failure rate**: `(k + 1 + q_S)·ρ(σ)` in place of `Pr[σ errs]`. -/
theorem balance_le_ompr_rate_perm (σ : Signer) (τ : Target → Preimage)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
    (hemb : Function.Injective emb) (A' : FDHPermAdv AR Z) {qf qi qS : ℕ}
    (hA' : ∀ pk, ∀ a ∈ support (A' pk), FPBudget qf qi qS a)
    (hTag : TagIdealP pkU.map σ
      ((forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)).noProbe τ) emb A') :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      N * epsIss (N * (eA + eVR lr pkU verifyCellBound)) (N • (qA + (extractorQueries + verifierQueries))) +
        N * epsSpend (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) +
        (advOMPR (ratTrap pkU.map σ) (qf + 1 + qS + qS + 1 + qS) qS
            (ompiRed (ARF AR emb) (qf + 1 + qS + qS + 1) qS (fdhRed (ARF AR emb) (fdhPermRed emb A'))) +
          ((qf + 1 + qS + qS + 1 + qS : ℕ) : ℝ≥0∞) * failRate (ratTrap pkU.map σ) +
          CTUFPerm.permEps (qf + qi + qS + 1) qi (Fintype.card (Commitment × Credits))
            (Fintype.card (Target × Z)) +
          failAdv σ (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdv lr pkU verQL A N σ := by
  refine (balance_le_ompr_perm lr pkU A N σ τ hdig hqA hnA heA hemb A' hA' hTag).trans ?_
  gcongr
  exact badTargets_le _ _

/-- **Theorem 1 (balance) under one-more-UOV with simultaneous extraction, `Tag` a random
permutation with inverse queries** (`balance_le_ompr_perm` with `ε_bal^sim` in place of
`N·ε_iss + N·ε_spend`). -/
theorem balance_le_ompr_sim_perm (σ : Signer) (τ : Target → Preimage)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
    (hemb : Function.Injective emb) (A' : FDHPermAdv AR Z) {qf qi qS : ℕ}
    (hA' : ∀ pk, ∀ a ∈ support (A' pk), FPBudget qf qi qS a)
    (hTag : TagIdealP pkU.map σ
      ((forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)).noProbe τ) emb A') :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      epsBalSim (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        (advOMPR (ratTrap pkU.map σ) (qf + 1 + qS + qS + 1 + qS) qS
            (ompiRed (ARF AR emb) (qf + 1 + qS + qS + 1) qS (fdhRed (ARF AR emb) (fdhPermRed emb A'))) +
          badTargets (ratTrap pkU.map σ) (qf + 1 + qS + qS + 1 + qS) +
          CTUFPerm.permEps (qf + qi + qS + 1) qi (Fintype.card (Commitment × Credits))
            (Fintype.card (Target × Z)) +
          failAdv σ (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdv lr pkU verQL A N σ := by
  refine le_trans (balance_le_ufTag_sim lr pkU A N σ hdig hqA hnA heA) ?_
  gcongr
  exact ufTag_le_ompr_perm pkU σ τ _ hemb A' hA' hTag

/-- **The same with the failure rate** (simultaneous extraction). -/
theorem balance_le_ompr_rate_sim_perm (σ : Signer) (τ : Target → Preimage)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
    (hemb : Function.Injective emb) (A' : FDHPermAdv AR Z) {qf qi qS : ℕ}
    (hA' : ∀ pk, ∀ a ∈ support (A' pk), FPBudget qf qi qS a)
    (hTag : TagIdealP pkU.map σ
      ((forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)).noProbe τ) emb A') :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      epsBalSim (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        (advOMPR (ratTrap pkU.map σ) (qf + 1 + qS + qS + 1 + qS) qS
            (ompiRed (ARF AR emb) (qf + 1 + qS + qS + 1) qS (fdhRed (ARF AR emb) (fdhPermRed emb A'))) +
          ((qf + 1 + qS + qS + 1 + qS : ℕ) : ℝ≥0∞) * failRate (ratTrap pkU.map σ) +
          CTUFPerm.permEps (qf + qi + qS + 1) qi (Fintype.card (Commitment × Credits))
            (Fintype.card (Target × Z)) +
          failAdv σ (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdv lr pkU verQL A N σ := by
  refine (balance_le_ompr_sim_perm lr pkU A N σ τ hdig hqA hnA heA hemb A' hA' hTag).trans ?_
  gcongr
  exact badTargets_le _ _

end Balance

end VoleMole.Assumptions.IdealTag.Rat
