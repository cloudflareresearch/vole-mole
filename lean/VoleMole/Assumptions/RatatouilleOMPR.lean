import VoleMole.ROM.RatatouilleProbe
import VoleMole.Assumptions.IdealTag

/-!
# Ratatouille's balance under one-more-UOV (OMPR)

`lean/docs/security/uov-assumptions.md` §5.8 ("Final statement under A-OMPR"), `ratatouille.md`
§2.3, §4. `ROM/RatatouilleProbe.lean` bounds the forgery term of Theorem 1 by the UF-Tag advantage
of a probe-free forger `B.noProbe τ` plus the signer's failure term `failAdv(B)`. Here:

* `StrictWin`, `ufTagStrictAdv`: UF-Tag with the paper's win (item 12): a valid signature on a pair
  that was **never** signed. `ufTagAdv_le_strict`: the UF-Tag-with-probe advantage of `B` is at most
  the strict advantage of `B.noProbe τ` plus `failAdv(B)` (a win on a pair whose signing failed is a
  failure). `ufTagStrictAdv_le`: the strict win is a win.
* `ratTrap pk σ`: the trapdoor of the Issuer's key, as a point-mass key generator (the per-key
  games), `IsPre pk s t ↔ s = some x ∧ P(x) = t`, `D = σ`.
* `TagIdeal`: **the modelling hypothesis.** The concrete `Tag` (KP800 truncated) is a function that
  the protocol game, its proofs and the forger evaluate; it cannot be an oracle there (`moussaka.md`
  F3). The paper idealises it *in the standalone UF-Tag game only*. `TagIdeal pk σ B qH qS A'`
  states that the strict UF-Tag advantage of the forger `B` is at most the det-FDH advantage of an
  ideal-model forger `A'` (`H = Tag` a random function: det-FDH is UF-Tag in that model,
  `Assumptions/IdealTag.lean`). This is the random-oracle heuristic for `Tag`, for this forger; it
  is a hypothesis, not proved.
* **`balance_le_ompr`**: Theorem 1 with the OMPR term:

      Pr[win BAL] ≤ N·ε_iss + N·ε_spend
        + (Adv^{ompr}(ompiRed (fdhRed A'); k + 1 + N, N) + Pr[σ errs on one of k + 1 + N targets]
           + failAdv(B)) + Adv^{coll}(C),

  for every completion `τ`, every ideal-model forger `A'` with at most `k` hash and signing queries
  for which `TagIdeal` holds with `q_S = N` (`B` logs at most `N` pairs, `forger_logs_le`).
  `balance_le_ompr_rate`: the error term as `(k + 1 + N)·ρ(σ)`, `ρ` the probability that `σ` errs on
  a uniform target (`δ(sk)^{255}` for pqov's `derive_preimage`, `uov-assumptions.md` §2).

The OMPR game is the per-key one (the key fixed, as the balance theorem's). The terms
`q_K·2^{−479} + q_K²·2^{−799}` of the paper's Lemma 2.1 (KP800 a permutation with inverse queries)
are not here: `Tag` is modelled as a random function (with `Tag` a random permutation:
`Assumptions/RatatouillePerm.lean`).

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.IdealTag.Rat

open VoleMole.Prob VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.IC.RatBalance
open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Assumptions.UOV
open VoleMole.Assumptions.IdealTag VoleMole.ROM.OneMore

/-! ## UF-Tag with the strict win -/

/-- **The strict UF-Tag win** (item 12): a valid signature on a pair never signed. -/
def StrictWin (pk : PublicKey) (r : ForgerOut) : Prop :=
  ∃ c x s, r.1 = some (c, x, s) ∧ uovEval pk s = tag c x ∧ (c, x) ∉ r.2.1

/-- **`Adv^{uf-tag}` with the strict win.** -/
noncomputable def ufTagStrictAdv (pk : PublicKey) (σ : Signer) (B : TagForger) : ℝ≥0∞ :=
  Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (B.run σ E)).run' ∅}[StrictWin pk r]

/-- A strict win is a win. -/
theorem ufTagStrictAdv_le (pk : PublicKey) (σ : Signer) (B : TagForger) :
    ufTagStrictAdv pk σ B ≤ ufTagAdv pk σ B :=
  prEvent_bind_mono_of_support _ _ _ fun _ _ => prEvent_mono _ _ _ fun _ ⟨c, x, s, h1, h2, h3⟩ =>
    ⟨c, x, s, h1, h2, fun _ hq hqe => absurd (hqe ▸ hq) h3⟩

/-- Per table: a win of `B` is a strict win of `B.noProbe τ` or a failure. -/
theorem strictWin_noProbe (pk : PublicKey) (B : TagForger) (σ : Signer) (τ : Target → Preimage)
    (E : CTable) (g : Table) (hW : RatBalance.UFWin pk σ (B.out σ E g)) :
    StrictWin pk ((B.noProbe τ).out σ E g) ∨ FailOut σ (B.out σ E g) := by
  by_cases hF : FailOut σ (B.out σ E g)
  · exact .inr hF
  · left
    have h := run_patch_of_not_fail B σ τ E g hF
    obtain ⟨c, x, s, h1, h2, h3⟩ := hW
    refine ⟨c, x, s, ?_, h2, fun hm => ?_⟩
    · simp only [TagForger.out, TagForger.noProbe, evalWithAnswerFn_map] at h ⊢
      rw [h]; exact h1
    · simp only [TagForger.out, TagForger.noProbe, evalWithAnswerFn_map] at h hm
      rw [h] at hm
      exact hF ⟨(c, x), List.mem_append_left _ hm, h3 _ hm rfl⟩

/-- **The probe and the failed signings cost at most the failure event**:
`Adv^{uf-tag+probe}(B) ≤ Adv^{uf-tag}_{strict}(B.noProbe τ) + failAdv(B)`. -/
theorem ufTagAdv_le_strict (pk : PublicKey) (σ : Signer) (B : TagForger)
    (τ : Target → Preimage) :
    ufTagAdv pk σ B ≤ ufTagStrictAdv pk σ (B.noProbe τ) + failAdv σ B := by
  unfold ufTagAdv ufTagStrictAdv failAdv
  let : MeasurableSpace CTable := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete, prEvent_bind_of_discrete,
    ← MeasureTheory.lintegral_add_left measurable_from_top]
  refine MeasureTheory.lintegral_mono fun E => ?_
  have h := prEvent_le_sum_of_table (B.run σ E) (Finset.univ : Finset Bool)
    (Y := fun _ => ForgerOut) (fun b => if b then (B.noProbe τ).run σ E else B.run σ E)
    (RatBalance.UFWin pk σ) (fun b r => if b then StrictWin pk r else FailOut σ r) (fun g hW => by
      rcases strictWin_noProbe pk B σ τ E g hW with h | h
      · exact ⟨true, Finset.mem_univ _, by simpa using h⟩
      · exact ⟨false, Finset.mem_univ _, by simpa using h⟩)
  simpa [add_comm] using h

/-! ## The Issuer's trapdoor, and the modelling hypothesis -/

/-- **The Issuer's trapdoor at a fixed key**: key `(pk, σ)` with probability one, `P = uovEval pk`,
`D = σ` (which may fail). -/
def ratTrap (pk : PublicKey) (σ : Signer) : Trapdoor PublicKey Signer Target (Option Preimage) :=
  Trapdoor.ofEval (pure (pk, σ)) uovEval fun σ => σ

/-- The det-FDH adversaries for Ratatouille's messages `(c, x)` and the world `specR AR`. -/
abbrev FDHAdv {DR : Type} (AR : DR → Type) :=
  PublicKey → ProbComp (OracleComp (specF AR (Commitment × Credits) Target (Option Preimage))
    ((Commitment × Credits) × Option Preimage))

/-- **The modelling hypothesis `TagIdeal`**: the strict UF-Tag advantage of the forger `B` against
the concrete `Tag` is at most the det-FDH advantage (`Tag` a random function) of the ideal-model
forger `A'`, with `q_H` hash and `q_S` signing queries. -/
def TagIdeal {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
    (pk : PublicKey) (σ : Signer) (B : TagForger) (qH qS : ℕ) (A' : FDHAdv AR) : Prop :=
  ufTagStrictAdv pk σ B ≤ advFDH (ratTrap pk σ) qH qS A'

/-! ## Theorem 1 under OMPR -/

section Balance

variable {Z : Sizes} {S : Type} (lr : Bool) (pkU : UovPk) (A : RoundAdv S (Op Z) Resp) (N : ℕ)
  {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]

/-- **Theorem 1 (balance) under one-more-UOV**: for every completion `τ` of the signer and every
ideal-model forger `A'` (at most `k` hash and signing queries) for which the modelling hypothesis
`TagIdeal` holds for the reduction's probe-free forger with `q_S = N`,

    Pr[win BAL] ≤ N·ε_iss + N·ε_spend
      + (Adv^{ompr}(ompiRed (fdhRed A'); k + 1 + N, N) + Pr[σ errs on one of k + 1 + N targets]
         + failAdv(B)) + Adv^{coll}(C),

the OMPR game at the Issuer's key `(pkU, σ)`. -/
theorem balance_le_ompr (σ : Signer) (τ : Target → Preimage)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
    (qH k : ℕ) (A' : FDHAdv AR) (hA' : ∀ pk, ∀ a ∈ support (A' pk), IsQueryBoundP a isHS k)
    (hTag : TagIdeal pkU.map σ ((forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)).noProbe τ)
      qH N A') :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      N * epsIss (N * (eA + eVR lr pkU verifyCellBound)) (N • (qA + (extractorQueries + verifierQueries))) +
        N * epsSpend (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) +
        (advOMPR (ratTrap pkU.map σ) (k + 1 + N) N (ompiRed AR (k + 1) N (fdhRed AR A')) +
          badTargets (ratTrap pkU.map σ) (k + 1 + N) +
          failAdv σ (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdv lr pkU verQL A N σ := by
  refine le_trans (balance_le_ufTag lr pkU A N σ hdig hqA hnA heA) ?_
  have h1 := ufTagAdv_le_strict pkU.map σ
    (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)) τ
  have h2 := hTag.trans (advFDH_le_ompr (ratTrap pkU.map σ) qH N k A' hA')
  gcongr
  exact h1.trans (add_le_add h2 le_rfl)

/-- **Theorem 1 under one-more-UOV, with the failure rate**: the error term is
`(k + 1 + N)·ρ(σ)`, `ρ(σ) = Pr_y[σ(y) is not a preimage of y]` (`δ(sk)^{255}` for pqov's signer). -/
theorem balance_le_ompr_rate (σ : Signer) (τ : Target → Preimage)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
    (qH k : ℕ) (A' : FDHAdv AR) (hA' : ∀ pk, ∀ a ∈ support (A' pk), IsQueryBoundP a isHS k)
    (hTag : TagIdeal pkU.map σ ((forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)).noProbe τ)
      qH N A') :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      N * epsIss (N * (eA + eVR lr pkU verifyCellBound)) (N • (qA + (extractorQueries + verifierQueries))) +
        N * epsSpend (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) +
        (advOMPR (ratTrap pkU.map σ) (k + 1 + N) N (ompiRed AR (k + 1) N (fdhRed AR A')) +
          (k + 1 + N : ℕ) * failRate (ratTrap pkU.map σ) +
          failAdv σ (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdv lr pkU verQL A N σ := by
  refine (balance_le_ompr lr pkU A N σ τ hdig hqA hnA heA qH k A' hA' hTag).trans ?_
  gcongr
  exact badTargets_le _ _

end Balance

end VoleMole.Assumptions.IdealTag.Rat
