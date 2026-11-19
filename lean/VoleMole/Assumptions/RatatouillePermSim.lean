import VoleMole.Assumptions.RatatouillePerm
import VoleMole.Assumptions.PermSimLinks
import VoleMole.ROM.RatatouilleBalanceSimPerm

/-!
# Ratatouille's balance under OMPR with AES as random permutations with inverse queries

`ROM/RatatouilleBalanceSimPerm.lean` (`balance_le_lean_simP`: AES as random permutations, the
adversary with forward and inverse cipher queries, simultaneous extraction) with its forgery term
`forgeAdvP` made the UF-Tag advantage of an explicit forger, and then the UF-Tag-to-OMPR steps of
`Assumptions/RatatouilleOMPR.lean` (`Tag` a random function, `TagIdeal`) and
`Assumptions/RatatouillePerm.lean` (`Tag` a random permutation with inverse queries, `TagIdealP`).

* **The forger** `forgerP lr pkU verQ A N hver : TagForger PTable`: a UF-Tag forger with a
  signability probe whose common randomness is the permutation table `π` of AES (`TagForger` is
  generic in the table type). It runs `masterP` (the permutation-model game and every extraction
  game, jointly normalized provers) and outputs `bOut` at the forward table.
* Its `reads` property (**`bOut_readsP`**): the generic `bOut_reads_of`
  (`ROM/RatatouilleBalance.lean`), with `games_congrP`: the jointly normalized `j`-th provers
  have the same output and the same log against two signers that agree on the run's first `j`
  calls. A jointly normalized prover is the PRF-view prover of the normalized adversary
  (`nJ_proverAtP`); the Issuer's calls, lifted and normalized, make the same queries whatever the
  signer (`tableQueryLog_normJ`, `tableQueryLog_liftP`).
* `forgeAdvP_le_ufTag`: `forgeAdvP ≤ Adv^{uf-tag}(forgerP)` (`forge_ufwin_of`).
  `forgerP_logs_le`: `forgerP` logs at most `N` pairs.
* **`balance_le_ufTag_simP`**: `Pr[win BAL] ≤ ε_bal^simP + Adv^{uf-tag}(forgerP) + collAdvP`.
* **`balance_le_ompr_simP`** (`Tag` a random function, hypothesis `TagIdeal` for
  `(forgerP …).noProbe τ`) and **`balance_le_ompr_sim_permP`** (`Tag` a random permutation,
  hypothesis `TagIdealP`), with `_rate` forms:

      Pr[win BAL] ≤ ε_bal^simP + (Adv^{ompr}(B') + Pr[σ errs] [+ permEps] + failAdv(forgerP))
                    + collAdvP.

The modelling hypotheses are those of the PRF-view results, now for a forger whose randomness is
the permutation table; they stay hypotheses.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC.RatBalance

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ROM VoleMole.ROM.IC
open VoleMole.Spec.Ratatouille VoleMole.EndToEnd VoleMole.ZK.Sim

/-! ## The jointly normalized provers are PRF-view provers -/

section Norm

variable (pI pR : Params) (π : PTable) {S Q R W : Type}

/-- **The joint normalization of `n` rounds** is `n` rounds of the normalized parties. -/
theorem normJ_roundsM (next : S → OracleComp specP (Q × S))
    (serve : W → Q → OracleComp specP (R × W)) (recv : S → R → S) (n : ℕ)
    (x : S × W × List (Q × R)) :
    normJ pI pR π (roundsM next serve recv n x) =
      roundsM (fun s => normJ pI pR π (next s)) (fun w q => normJ pI pR π (serve w q)) recv n
        x := by
  induction n generalizing x with
  | zero => simp [roundsM, normJ, addIV_pure, normP_pure]
  | succ n ih =>
    simp only [roundsM]
    rw [normJ_bind, ih]
    refine congrArg _ (funext fun y => ?_)
    simp only [roundM, normJ_bind]
    simp [normJ, addIV_pure, normP_pure]

/-- **A jointly normalized `j`-th prover of the permutation model** is the `j`-th prover of the
PRF view, for the normalized adversary and Issuer. -/
theorem nJ_proverAtP (lr : Bool) {Z : Sizes} {S : Type} (A : RoundAdvP S (Op Z) Resp)
    (serve : W → Op Z → OracleComp specP (Resp × W)) {ι β : Type} (w₀ : W)
    (pick : Op Z → ByteArray × (ι × β)) (j : ℕ) :
    nJ lr π (proverAtP A serve w₀ pick j) =
      proverAt (A.toIC lr π) (fun w q => nJ lr π (serve w q)) w₀ pick j := by
  simp only [nJ, proverAtP, proverAt, normJ_bind, normJ_roundsM]
  simp [normJ, addIV_pure, normP_pure, RoundAdvP.toIC]

end Norm

variable {Z : Sizes} {S : Type} (lr : Bool) (pkU : UovPk)
  (verQ : Statement → ByteArray → OracleComp specIC Bool)

/-! ## The forger of the permutation model reads the signer only through its logs -/

section Reads

variable (A : RoundAdvP S (Op Z) Resp) (N : ℕ) {qV : Kind → ℕ} {nV : ℕ} {eV : Params → ℕ}

/-- **The extraction games of the permutation model depend on the signer only through the run's
first calls** (`games_congr`, permutation model). -/
theorem games_congrP (hver : VerifierIC CrtGen.tables verQ qV nV eV) (σ σ' : Signer) (g : Table)
    (π : PTable) (k : ℕ)
    (hy : ∀ k' ≤ k, yG lr pkU (A.toIC lr π) σ' g π.fwd k' = yG lr pkU (A.toIC lr π) σ g π.fwd k') :
    evalWithAnswerFn (QueryImpl.ofFn g) (gameIP lr pkU verQ A σ' k π) =
        evalWithAnswerFn (QueryImpl.ofFn g) (gameIP lr pkU verQ A σ k π) ∧
      evalWithAnswerFn (QueryImpl.ofFn g) (gameSP lr pkU verQ A σ' k π) =
        evalWithAnswerFn (QueryImpl.ofFn g) (gameSP lr pkU verQ A σ k π) := by
  have hs : ∀ (τ : Signer) (w : IssuerState) (q : Op Z),
      evalWithAnswerFn (QueryImpl.ofFn (join g π.fwd)) (nJ lr π (serveL lr pkU verQ τ w q)) =
        serveP lr pkU (verT g π.fwd) τ w q := fun τ w q => by
    rw [nJ, evalWithAnswerFn_normJ, serveL, evalWithAnswerFn_liftP]
    exact evalWithAnswerFn_serveM lr pkU _ verQ _ (fun st pf => hver.eval g π.fwd st pf) τ w q
  have hlog : ∀ (w w' : IssuerState) (q : Op Z),
      tableQueryLog (nJ lr π (serveL lr pkU verQ σ' w q)) (join g π.fwd) =
        tableQueryLog (nJ lr π (serveL lr pkU verQ σ w' q)) (join g π.fwd) := by
    intro w w' q
    have h : tableQueryLog (serveM lr pkU verQ σ' w q) (join g π.fwd) =
        tableQueryLog (serveM lr pkU verQ σ w' q) (join g π.fwd) := by
      simp only [serveM, tableQueryLog_bind, tableQueryLog_pure]
    rw [nJ, nJ, tableQueryLog_normJ, tableQueryLog_normJ, serveL, serveL, tableQueryLog_liftP,
      tableQueryLog_liftP, h]
  have hst : ∀ k' ≤ k, (roundsT (nextT (A.toIC lr π) g π.fwd) (serveP lr pkU (verT g π.fwd) σ')
      A.recv k' (A.init, (⟨[]⟩ : IssuerState), [])).1 =
      (roundsT (nextT (A.toIC lr π) g π.fwd) (serveP lr pkU (verT g π.fwd) σ) A.recv k'
      (A.init, (⟨[]⟩ : IssuerState), [])).1 := fun k' hk' => congrArg Prod.fst (hy k' hk')
  constructor
  · obtain ⟨h1, h2⟩ := proverAt_congr (A.toIC lr π) (fun w q => nJ lr π (serveL lr pkU verQ σ' w q))
      (fun w q => nJ lr π (serveL lr pkU verQ σ w q)) (join g π.fwd) (nextT (A.toIC lr π) g π.fwd)
      _ _ (fun _ => rfl) (hs σ') (hs σ) hlog _ pickI k hst
    rw [gameIP, gameIP, provIP, provIP, nJ_proverAtP, nJ_proverAtP]
    exact gameA_congr _ _ π.fwd g h1 h2
  · obtain ⟨h1, h2⟩ := proverAt_congr (A.toIC lr π) (fun w q => nJ lr π (serveL lr pkU verQ σ' w q))
      (fun w q => nJ lr π (serveL lr pkU verQ σ w q)) (join g π.fwd) (nextT (A.toIC lr π) g π.fwd)
      _ _ (fun _ => rfl) (hs σ') (hs σ) hlog _ pickS k hst
    rw [gameSP, gameSP, provSP, provSP, nJ_proverAtP, nJ_proverAtP]
    exact gameA_congr _ _ π.fwd g h1 h2

/-- **`B` of the permutation model uses the signer only through its logs** (`bOut_reads`,
permutation model). -/
theorem bOut_readsP (hver : VerifierIC CrtGen.tables verQ qV nV eV) (σ σ' : Signer) (g : Table)
    (π : PTable)
    (hs : ∀ q ∈ (bOut lr pkU π.fwd (evalWithAnswerFn (QueryImpl.ofFn g)
      (masterP lr pkU verQ A N σ π))).2.1, σ' (tag q.1 q.2) = σ (tag q.1 q.2))
    (hp : ∀ q ∈ (bOut lr pkU π.fwd (evalWithAnswerFn (QueryImpl.ofFn g)
      (masterP lr pkU verQ A N σ π))).2.2, (σ' (tag q.1 q.2)).isSome = (σ (tag q.1 q.2)).isSome) :
    bOut lr pkU π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (masterP lr pkU verQ A N σ' π)) =
      bOut lr pkU π.fwd (evalWithAnswerFn (QueryImpl.ofFn g) (masterP lr pkU verQ A N σ π)) := by
  rw [evalWithAnswerFn_masterP] at hs hp ⊢
  rw [evalWithAnswerFn_masterP]
  exact bOut_reads_of lr pkU (A.toIC lr π) N
    (fun τ k => evalWithAnswerFn (QueryImpl.ofFn g) (gameIP lr pkU verQ A τ k π))
    (fun τ k => evalWithAnswerFn (QueryImpl.ofFn g) (gameSP lr pkU verQ A τ k π)) σ σ' g π.fwd
    (fun k hy => games_congrP lr pkU verQ A hver σ σ' g π k hy) hs hp

end Reads

/-! ## The forger and the balance bound with its UF-Tag advantage -/

/-- **The forger `B` of the permutation model**: it runs the permutation-model game and the
extraction games with the Issuer's signer, its common randomness the permutation table `π`, and
outputs `bOut` at the forward table. -/
noncomputable def forgerP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) {qV : Kind → ℕ} {nV : ℕ}
    {eV : Params → ℕ} (hver : VerifierIC CrtGen.tables verQ qV nV eV) : TagForger PTable where
  run σ π := bOut lr pkU π.fwd <$> masterP lr pkU verQ A N σ π
  reads σ σ' π g hs hp := by
    rw [evalWithAnswerFn_map] at hs hp ⊢
    rw [evalWithAnswerFn_map]
    exact bOut_readsP lr pkU verQ A N hver σ σ' g π hs hp

section Forger

variable (A : RoundAdvP S (Op Z) Resp) (N : ℕ) {qV : Kind → ℕ} {nV : ℕ} {eV : Params → ℕ}
  (hver : VerifierIC CrtGen.tables verQ qV nV eV)

/-- **The reduction's forgery event is bounded by `forgerP`'s UF-Tag advantage** (permutation
model). -/
theorem forgeAdvP_le_ufTag (σ : Signer) :
    forgeAdvP lr pkU verQ A N σ ≤ ufTagAdv pkU.map σ (forgerP lr pkU verQ A N hver) := by
  unfold forgeAdvP ufTagAdv
  let : MeasurableSpace PTable := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  refine MeasureTheory.lintegral_mono fun π => ?_
  refine prEvent_le_of_table (masterP lr pkU verQ A N σ π)
    ((forgerP lr pkU verQ A N hver).run σ π) _ _ fun g hF => ?_
  simp only [forgerP, evalWithAnswerFn_map]
  rw [evalWithAnswerFn_masterP] at hF ⊢
  exact forge_ufwin_of lr pkU (A.toIC lr π) N σ g π.fwd _ _ hF

/-- **`forgerP` logs at most `N` pairs** (signed and probed together). -/
theorem forgerP_logs_le (σ : Signer) (π : PTable) (g : Table) :
    ((forgerP lr pkU verQ A N hver).out σ π g).2.1.length +
      ((forgerP lr pkU verQ A N hver).out σ π g).2.2.length ≤ N := by
  simp only [TagForger.out, forgerP, evalWithAnswerFn_map]
  generalize hm : evalWithAnswerFn (QueryImpl.ofFn g) (masterP lr pkU verQ A N σ π) = m
  have hm1 : m.1 = (yG lr pkU (A.toIC lr π) σ g π.fwd N).2.2 := by
    rw [← hm, evalWithAnswerFn_masterP]; rfl
  have hlen : m.1.length = N := hm1 ▸ length_trace lr pkU (A.toIC lr π) N σ g π.fwd
  unfold bOut
  split
  · refine (logs_length_le _).trans ?_
    rw [List.length_take]; omega
  · exact hlen ▸ logs_length_le _

end Forger

/-- **Theorem 1 (balance) with simultaneous extraction, AES as random permutations, with the
UF-Tag advantage of the explicit forger `forgerP`**:

    Pr[win BAL] ≤ ε_bal^simP(q', q'_E, n', N) + Adv^{uf-tag}(forgerP) + collAdvP. -/
theorem balance_le_ufTag_simP (A : RoundAdvP S (Op Z) Resp) (N : ℕ) (σ : Signer)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundP (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (balQP lr pkU A N σ π)).run' ∅}[
        Win r.2.2] ≤
      epsBalSimP (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        ufTagAdv pkU.map σ (forgerP lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)) +
        collAdvP lr pkU verQL A N σ :=
  (balance_le_lean_simP lr pkU A N σ hdig hqA hnA heA).trans (add_le_add (add_le_add le_rfl
    (forgeAdvP_le_ufTag lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables) σ)) le_rfl)

end VoleMole.ROM.IC.RatBalance

namespace VoleMole.Assumptions.IdealTag.Rat

open VoleMole.Prob VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.IC.RatBalance
open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Assumptions.UOV
open VoleMole.Assumptions.IdealTag VoleMole.ROM.OneMore VoleMole.Assumptions.UOV.FDHPerm

section Balance

variable {Zs : Sizes} {S : Type} (lr : Bool) (pkU : UovPk) (A : RoundAdvP S (Op Zs) Resp) (N : ℕ)
  {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]

/-- **Theorem 1 (balance) under one-more-UOV, AES as random permutations with inverse queries,
`Tag` a random function** (simultaneous extraction): for every completion `τ` of the signer and
every ideal-model forger `A'` (at most `k` hash and signing queries) for which the modelling
hypothesis `TagIdeal` holds for the probe-free forger `(forgerP …).noProbe τ` with `q_S = N`,

    Pr[win BAL] ≤ ε_bal^simP(q', q'_E, n', N)
      + (Adv^{ompr}(ompiRed (fdhRed A'); k + 1 + N, N) + Pr[σ errs on one of k + 1 + N targets]
         + failAdv(forgerP)) + collAdvP,

the OMPR game at the Issuer's key `(pkU, σ)`. -/
theorem balance_le_ompr_simP (σ : Signer) (τ : Target → Preimage)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundP (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
    (qH k : ℕ) (A' : FDHAdv AR) (hA' : ∀ pk, ∀ a ∈ support (A' pk), IsQueryBoundP a isHS k)
    (hTag : TagIdeal pkU.map σ
      ((forgerP lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)).noProbe τ) qH N A') :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (balQP lr pkU A N σ π)).run' ∅}[
        Win r.2.2] ≤
      epsBalSimP (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        (advOMPR (ratTrap pkU.map σ) (k + 1 + N) N (ompiRed AR (k + 1) N (fdhRed AR A')) +
          badTargets (ratTrap pkU.map σ) (k + 1 + N) +
          failAdv σ (forgerP lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdvP lr pkU verQL A N σ := by
  refine le_trans (balance_le_ufTag_simP lr pkU A N σ hdig hqA hnA heA) ?_
  have h1 := ufTagAdv_le_strict pkU.map σ
    (forgerP lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)) τ
  have h2 := hTag.trans (advFDH_le_ompr (ratTrap pkU.map σ) qH N k A' hA')
  gcongr
  exact h1.trans (add_le_add h2 le_rfl)

/-- **The same with the failure rate**: `(k + 1 + N)·ρ(σ)` in place of `Pr[σ errs]`. -/
theorem balance_le_ompr_rate_simP (σ : Signer) (τ : Target → Preimage)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundP (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
    (qH k : ℕ) (A' : FDHAdv AR) (hA' : ∀ pk, ∀ a ∈ support (A' pk), IsQueryBoundP a isHS k)
    (hTag : TagIdeal pkU.map σ
      ((forgerP lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)).noProbe τ) qH N A') :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (balQP lr pkU A N σ π)).run' ∅}[
        Win r.2.2] ≤
      epsBalSimP (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        (advOMPR (ratTrap pkU.map σ) (k + 1 + N) N (ompiRed AR (k + 1) N (fdhRed AR A')) +
          (k + 1 + N : ℕ) * failRate (ratTrap pkU.map σ) +
          failAdv σ (forgerP lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdvP lr pkU verQL A N σ := by
  refine (balance_le_ompr_simP lr pkU A N σ τ hdig hqA hnA heA qH k A' hA' hTag).trans ?_
  gcongr
  exact badTargets_le _ _

variable {Z : Type} [DecidableEq Z] [SampleableType Z] [Fintype Z]
  {emb : Commitment × Credits → Target × Z} [SampleableType (Bc emb)]

/-- **Theorem 1 (balance) under one-more-UOV, AES and `Tag` random permutations with inverse
queries** (simultaneous extraction): for every completion `τ` of the signer and every
permutation-model forger `A'` (at most `q_f` forward, `q_i` inverse and `q_S` signing queries) for
which the modelling hypothesis `TagIdealP` holds for `(forgerP …).noProbe τ`,

    Pr[win BAL] ≤ ε_bal^simP(q', q'_E, n', N)
      + (Adv^{ompr}(B'; k + 1 + q_S, q_S) + Pr[σ errs on one of k + 1 + q_S targets] + permEps
         + failAdv(forgerP)) + collAdvP,

`k = q_f + 1 + 2q_S`, `B' = ompiRed (k + 1) q_S (fdhRed (fdhPermRed A'))`. -/
theorem balance_le_ompr_sim_permP (σ : Signer) (τ : Target → Preimage)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundP (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
    (hemb : Function.Injective emb) (A' : FDHPermAdv AR Z) {qf qi qS : ℕ}
    (hA' : ∀ pk, ∀ a ∈ support (A' pk), FPBudget qf qi qS a)
    (hTag : TagIdealP pkU.map σ
      ((forgerP lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)).noProbe τ) emb A') :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (balQP lr pkU A N σ π)).run' ∅}[
        Win r.2.2] ≤
      epsBalSimP (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        (advOMPR (ratTrap pkU.map σ) (qf + 1 + qS + qS + 1 + qS) qS
            (ompiRed (ARF AR emb) (qf + 1 + qS + qS + 1) qS (fdhRed (ARF AR emb) (fdhPermRed emb A'))) +
          badTargets (ratTrap pkU.map σ) (qf + 1 + qS + qS + 1 + qS) +
          CTUFPerm.permEps (qf + qi + qS + 1) qi (Fintype.card (Commitment × Credits))
            (Fintype.card (Target × Z)) +
          failAdv σ (forgerP lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdvP lr pkU verQL A N σ := by
  refine le_trans (balance_le_ufTag_simP lr pkU A N σ hdig hqA hnA heA) ?_
  gcongr
  exact ufTag_le_ompr_perm pkU σ τ _ hemb A' hA' hTag

/-- **The same with the failure rate**: `(k + 1 + q_S)·ρ(σ)` in place of `Pr[σ errs]`. -/
theorem balance_le_ompr_rate_sim_permP (σ : Signer) (τ : Target → Preimage)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundP (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
    (hemb : Function.Injective emb) (A' : FDHPermAdv AR Z) {qf qi qS : ℕ}
    (hA' : ∀ pk, ∀ a ∈ support (A' pk), FPBudget qf qi qS a)
    (hTag : TagIdealP pkU.map σ
      ((forgerP lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)).noProbe τ) emb A') :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (balQP lr pkU A N σ π)).run' ∅}[
        Win r.2.2] ≤
      epsBalSimP (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        (advOMPR (ratTrap pkU.map σ) (qf + 1 + qS + qS + 1 + qS) qS
            (ompiRed (ARF AR emb) (qf + 1 + qS + qS + 1) qS (fdhRed (ARF AR emb) (fdhPermRed emb A'))) +
          ((qf + 1 + qS + qS + 1 + qS : ℕ) : ℝ≥0∞) * failRate (ratTrap pkU.map σ) +
          CTUFPerm.permEps (qf + qi + qS + 1) qi (Fintype.card (Commitment × Credits))
            (Fintype.card (Target × Z)) +
          failAdv σ (forgerP lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdvP lr pkU verQL A N σ := by
  refine (balance_le_ompr_sim_permP lr pkU A N σ τ hdig hqA hnA heA hemb A' hA' hTag).trans ?_
  gcongr
  exact badTargets_le _ _

end Balance

end VoleMole.Assumptions.IdealTag.Rat
