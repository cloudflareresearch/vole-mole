import VoleMole.Assumptions.UOVLinks
import VoleMole.Assumptions.RatatouilleOMPR
import VoleMole.ROM.MoussakaOMUFSim
import VoleMole.ROM.RatatouilleBalanceSim

/-!
# The protocol theorems down to one-more-UOV, with simultaneous extraction

`Assumptions/UOVLinks.lean` (`omuf_le_num_open`, `omuf_le_num_ompr`) and
`Assumptions/RatatouilleOMPR.lean` (`balance_le_ompr`, `balance_le_ompr_rate`) with their
extraction terms replaced by the simultaneous ones (`ROM/MoussakaOMUFSim.lean`,
`ROM/RatatouilleBalanceSim.lean`): `εI^sim + εR^sim` in place of `qI·εI + qR·εR`, and
`ε_iss^sim + ε_spend^sim` in place of `N·ε_iss + N·ε_spend`. The other terms and the modelling
hypotheses (`hmodel`, `TagIdeal`) are unchanged.

* `omuf_le_open_sim`, `omuf_le_num_open_sim`, **`omuf_le_num_ompr_sim`** (Moussaka).
* **`balance_le_ompr_sim`**, `balance_le_ompr_rate_sim` (Ratatouille).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier VoleMole.ZK.Sim

section Moussaka

open VoleMole.ROM.IC.OMUF CTUFOpen

variable {K qR : ℕ} (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)

/-- **Theorem 1 with `B₂`'s standalone CT-UF^open advantage, simultaneous extraction events**
(`omuf_le_open` with `omuf_le_sim`'s events). -/
theorem omuf_le_open_sim (A : Adversary K qR) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (OMUF.game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        SimI lr E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        SimR lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      advCTUFOpenAt (verK pk) comO WFO (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForger lr pk qI A) := by
  rw [advCTUFOpenAt_ctufForger]
  have h := prEvent_bind_le_sum4_of_table ($ᵗ CTable) (fun E => runE E (OMUF.game lr pk sk qI A))
    (fun _ r => Win r.1) {0} {0} (fun _ E => extAll lr pk sk qI A E) (fun E v => SimI lr E v)
    (fun _ E => extAll lr pk sk qI A E) (fun E v => SimR lr pk E v)
    (fun E => extAll lr pk sk qI A E) (fun E v => Coll lr pk E v)
    (fun E v => CTOpenWin (verK pk) comO WFO (ctufOut lr pk E v)) fun E g hw => by
      rw [evalWithAnswerFn_runE] at hw
      rcases win_imp_open lr pk sk qI A g E hw with hI | hR | hC | hF
      · exact Or.inl ⟨0, Finset.mem_singleton_self 0, simI_of lr pk sk qI A g E hI⟩
      · exact Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, simR_of lr pk sk qI A g E hR⟩)
      · exact Or.inr (Or.inr (Or.inl hC))
      · exact Or.inr (Or.inr (Or.inr hF))
  simpa only [Finset.sum_singleton] using h

variable {A : Adversary K qR} {q : Kind → ℕ} {qE n : ℕ}

/-- **Theorem 1 (`omuf_le_num_sim`) with `Adv^{ct-uf-open}_K` in place of `AdvCTUF(B₂)`.** -/
theorem omuf_le_num_open_sim (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (OMUF.game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      epsIsim (gameK q qI qR) (gameE lr qE qI qR) qI +
      epsRsim (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qR +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      advCTUFOpenAt (verK pk) comO WFO (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForger lr pk qI A) :=
  (omuf_le_open_sim lr pk sk qI A).trans (add_le_add (add_le_add (add_le_add
    (prEvent_simI_le hA) (prEvent_simR_le hA hdig hdinj)) le_rfl) le_rfl)

variable {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Xc T S PK SK : Type} [DecidableEq Xc] [DecidableEq T] [Inhabited T] [SampleableType T]
  (tr : Trapdoor PK SK T S) (ks : Fin K → PK × SK) (qf qS : ℕ)

/-- **Theorem 1 down to OMPR with simultaneous extraction** (`omuf_le_num_ompr` with `εI^sim +
εR^sim` in place of `qI·εI + qR·εR`; the same modelling hypothesis `hmodel`):

    Pr[Win] ≤ εI^sim + εR^sim + AdvBind(B₁)
              + Σ_j (Adv^{ompr}_{key j}(B_j; q_f + 2q_S + 1, q_S) + (q_f + 2q_S + 1)·failPr_{key j}). -/
theorem omuf_le_num_ompr_sim (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest)
    (F : ProbComp (OracleComp (specCI AR K Xc T S) (CTOut K S Xc)))
    (hF : ∀ f ∈ support F, CIBudget qf qS f)
    (hmodel : advCTUFOpenAt (verK pk) comO WFO
        (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk) (ctufForger lr pk qI A) ≤
      advCTUFIdealAt (fun k => tr.IsPre (ks k).1) (signers tr.D fun k => (ks k).2) F) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (OMUF.game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      epsIsim (gameK q qI qR) (gameE lr qE qI qR) qI +
      epsRsim (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qR +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      ∑ j : Fin K, (advOMPR (tr.atKey (ks j)) (qf + 2 * qS + 1) qS
          (ompRed qS fun _ => guessF j (signers tr.D fun k => (ks k).2) <$> F) +
        ((qf + 2 * qS + 1 : ℕ) : ℝ≥0∞) * preFailPr (tr.atKey (ks j))) :=
  (omuf_le_num_open_sim lr pk sk qI hA hdig hdinj).trans
    (add_le_add le_rfl (hmodel.trans (advCTUFIdealAt_le_ompr tr qf qS ks F hF)))

end Moussaka

end VoleMole.Assumptions.UOV.Links

namespace VoleMole.Assumptions.IdealTag.Rat

open VoleMole.Prob VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.IC.RatBalance
open VoleMole.Spec.Ratatouille VoleMole.ZK.Sim VoleMole.Assumptions.UOV
open VoleMole.Assumptions.IdealTag VoleMole.ROM.OneMore

section Balance

variable {Z : Sizes} {S : Type} (lr : Bool) (pkU : UovPk) (A : RoundAdv S (Op Z) Resp) (N : ℕ)
  {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]

/-- **Theorem 1 (balance) under one-more-UOV, with simultaneous extraction** (`balance_le_ompr`
with `ε_iss^sim + ε_spend^sim` in place of `N·ε_iss + N·ε_spend`; the same hypothesis
`TagIdeal`). -/
theorem balance_le_ompr_sim (σ : Signer) (τ : Target → Preimage)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
    (qH k : ℕ) (A' : FDHAdv AR) (hA' : ∀ pk, ∀ a ∈ support (A' pk), IsQueryBoundP a isHS k)
    (hTag : TagIdeal pkU.map σ ((forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)).noProbe τ)
      qH N A') :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      epsIssSim (N * (eA + eVR lr pkU verifyCellBound))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        epsSpendSim (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        (advOMPR (ratTrap pkU.map σ) (k + 1 + N) N (ompiRed AR (k + 1) N (fdhRed AR A')) +
          badTargets (ratTrap pkU.map σ) (k + 1 + N) +
          failAdv σ (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdv lr pkU verQL A N σ := by
  refine le_trans (balance_le_ufTag_sim lr pkU A N σ hdig hqA hnA heA) ?_
  have h1 := ufTagAdv_le_strict pkU.map σ
    (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)) τ
  have h2 := hTag.trans (advFDH_le_ompr (ratTrap pkU.map σ) qH N k A' hA')
  gcongr
  exact h1.trans (add_le_add h2 le_rfl)

/-- **The same with the failure rate** (`balance_le_ompr_rate` with simultaneous extraction). -/
theorem balance_le_ompr_rate_sim (σ : Signer) (τ : Target → Preimage)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
    (qH k : ℕ) (A' : FDHAdv AR) (hA' : ∀ pk, ∀ a ∈ support (A' pk), IsQueryBoundP a isHS k)
    (hTag : TagIdeal pkU.map σ ((forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)).noProbe τ)
      qH N A') :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      epsIssSim (N * (eA + eVR lr pkU verifyCellBound))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        epsSpendSim (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        (advOMPR (ratTrap pkU.map σ) (k + 1 + N) N (ompiRed AR (k + 1) N (fdhRed AR A')) +
          (k + 1 + N : ℕ) * failRate (ratTrap pkU.map σ) +
          failAdv σ (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables))) +
        collAdv lr pkU verQL A N σ := by
  refine (balance_le_ompr_sim lr pkU A N σ τ hdig hqA hnA heA qH k A' hA' hTag).trans ?_
  gcongr
  exact badTargets_le _ _

end Balance

end VoleMole.Assumptions.IdealTag.Rat
