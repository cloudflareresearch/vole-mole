import VoleMole.ROM.SimJointSpec
import VoleMole.ROM.RatatouilleBalance

/-!
# Ratatouille balance (Theorem 1) with simultaneous extraction

`ROM/RatatouilleBalance.lean`'s `balance_le` charges the extraction failure of each round's
request separately (`N·ε_iss + N·ε_spend`, each `ε` the single-proof bound at the budget of `N`
rounds), through the `j`-th prover `proverAt` (the game up to round `j`, then the `j`-th
request). The `j`-th prover's run is a prefix of the full run of `N` rounds (`fullI`, `fullS`,
which are one run), so `ROM/SimJointSpec.lean`'s simultaneous bound applies (`PrefixRuns`): each
query of the full run is charged once, for both relations, and per request only the extraction
game's own extractor and verifier queries and the failure events.

* `prefixRuns_of_joint`: prefix joint logs give `PrefixRuns` (`runE`'s log is the hash part of
  the joint log, `ROM/PermPost.lean`'s `tableQueryLog_runE_eq`).
* `roundsM_prefix`, `proverAt_prefix`: the `j`-th prover's log is a prefix of the log of `N > j`
  rounds.
* `SimIss`, `SimSp`: some round's request fails extraction (an event of the reduction's run
  `master`); `SimIS`: either. `prEvent_simIss_le`, `prEvent_simSp_le`: each relation alone
  (`ROM/SimSpec.lean`, the run charged once per relation); **`prEvent_simIS_le`**: both together.
* **`balance_le_sim`** (the reduction), **`balance_le_sim_num`**, **`balance_le_lean_sim`**,
  **`balance_le_ufTag_sim`** (with the terms):

      Pr[win BAL] ≤ ε_bal^sim(q', q'_E, n', N) + Adv^{uf-tag}(B) + Adv^{coll}(C),

  `ε_bal^sim = (q'₂₁+2N)·2⁻¹⁵⁰ + (q'₂₂+2N)·(ε_QS(12282) + 2⁻¹²⁸ + (n'+339)·2⁻⁴⁴⁸)
  + (q'₂₃+2N)·9·2⁻¹²⁸ + chainHitEpsCombSim q' M 2N + stmtBindEpsSim q' 2N + 2N·failEps q' q'_E`,
  at the budgets of `balance_le` (`q' = N•(qA + qV)`, `q'_E = N(eA + eVR)`, `n' = N(nA + nV)`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Verifier VoleMole.ROM

/-! ## Prefix runs from prefix joint logs -/

/-- **Prefix joint logs give prefix runs.** -/
theorem prefixRuns_of_joint {ι' ι β : Type} (E : CTable) (P₀ : OracleComp specIC (ByteArray × (ι × β)))
    (P : ι' → OracleComp specIC (ByteArray × (ι × β))) (J : Finset ι')
    (h : ∀ j ∈ J, ∀ g, tableQueryLog (P j) (join g E) <+: tableQueryLog P₀ (join g E)) :
    PrefixRuns E P₀ P J := fun j hj g => by
  obtain ⟨Y, hY⟩ := h j hj g
  refine ⟨⟨hashEnt Y, ?_⟩, Y, hY.symm⟩
  rw [tableQueryLog_runE_eq, tableQueryLog_runE_eq, ← hY, hashEnt_append]

/-! ## The `j`-th prover's log is a prefix of the run's -/

section Rounds

variable {S Q R W : Type} (A : RoundAdv S Q R) (serve : W → Q → OracleComp specIC (R × W))

theorem roundsM_prefix (f : (d : DomIC) → AnsIC d) (x : S × W × List (Q × R)) {k n : ℕ}
    (hkn : k ≤ n) :
    tableQueryLog (roundsM A.next serve A.recv k x) f <+:
      tableQueryLog (roundsM A.next serve A.recv n x) f := by
  induction n with
  | zero => rw [Nat.le_zero.1 hkn]
  | succ n ih =>
    rcases Nat.lt_or_ge k (n + 1) with hk | hk
    · refine (ih (by omega)).trans ?_
      show _ <+: tableQueryLog (roundsM A.next serve A.recv n x >>= roundM A.next serve A.recv) f
      rw [tableQueryLog_bind]
      exact List.prefix_append _ _
    · rw [show k = n + 1 by omega]

theorem proverAt_prefix {ι β : Type} (w₀ : W) (pick : Q → ByteArray × (ι × β))
    (f : (d : DomIC) → AnsIC d) {k n : ℕ} (hk : k < n) :
    tableQueryLog (proverAt A serve w₀ pick k) f <+:
      tableQueryLog (roundsM A.next serve A.recv n (A.init, w₀, [])) f := by
  refine List.IsPrefix.trans ?_ (roundsM_prefix A serve f _ (Nat.succ_le_of_lt hk))
  show tableQueryLog (roundsM A.next serve A.recv k (A.init, w₀, []) >>= fun x =>
      A.next x.1 >>= fun a => (pure (pick a.1) : OracleComp specIC _)) f <+:
    tableQueryLog (roundsM A.next serve A.recv k (A.init, w₀, []) >>=
      roundM A.next serve A.recv) f
  simp only [tableQueryLog_bind]
  refine (List.prefix_append_right_inj _).2 ?_
  unfold roundM
  simp only [tableQueryLog_bind, tableQueryLog_pure, List.append_nil]
  exact List.prefix_append _ _

end Rounds

namespace RatBalance

open VoleMole.Verifier.Bridge VoleMole.Spec.Ratatouille VoleMole.EndToEnd VoleMole.ZK.Sim

variable {Z : Sizes} {S : Type} (lr : Bool) (pkU : UovPk)
  (verQ : Statement → ByteArray → OracleComp specIC Bool)

/-! ## The full run and the simultaneous events -/

/-- **The full run of `N` rounds as an issuance prover** (the reference run; its output is
irrelevant). -/
def fullI (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) :
    OracleComp specIC (ByteArray × (IIdx × Unit)) :=
  (fun _ => (ByteArray.empty, (zI, ()))) <$>
    roundsM A.next (serveM lr pkU verQ σ) A.recv N (A.init, (⟨[]⟩ : IssuerState), [])

/-- The full run as a spend prover. -/
def fullS (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) :
    OracleComp specIC (ByteArray × (SIdx × Unit)) :=
  (fun _ => (ByteArray.empty, (zS, ()))) <$>
    roundsM A.next (serveM lr pkU verQ σ) A.recv N (A.init, (⟨[]⟩ : IssuerState), [])

theorem prefixRuns_I (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) (E : CTable) :
    PrefixRuns E (fullI lr pkU verQ A N σ) (provI lr pkU verQ A σ) (Finset.range N) :=
  prefixRuns_of_joint E _ _ _ fun k hk g => by
    rw [fullI, tableQueryLog_map']
    exact proverAt_prefix A _ _ _ _ (Finset.mem_range.1 hk)

theorem prefixRuns_S (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) (E : CTable) :
    PrefixRuns E (fullS lr pkU verQ A N σ) (provS lr pkU verQ A σ) (Finset.range N) :=
  prefixRuns_of_joint E _ _ _ fun k hk g => by
    rw [fullS, tableQueryLog_map']
    exact proverAt_prefix A _ _ _ _ (Finset.mem_range.1 hk)

/-- **Some round's issuance request fails extraction** (an event of the reduction's run). -/
def SimIss (E : CTable) (m : List (Op Z × Resp) × List OutI × List OutS) : Prop :=
  ∃ r ∈ m.2.1, failI lr E r

/-- **Some round's spend request fails extraction.** -/
def SimSp (E : CTable) (m : List (Op Z × Resp) × List OutI × List OutS) : Prop :=
  ∃ r ∈ m.2.2, failS lr pkU E r

/-- **Some round's issuance or spend request fails extraction.** -/
def SimIS (E : CTable) (m : List (Op Z × Resp) × List OutI × List OutS) : Prop :=
  SimIss lr E m ∨ SimSp lr pkU E m

/-- **Theorem 1 (balance), the reduction, with one simultaneous extraction event.** -/
theorem balance_le_sim (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) {qV : Kind → ℕ}
    {nV : ℕ} {eV : Params → ℕ} (hver : VerifierIC CrtGen.tables verQ qV nV eV) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      Pr{let E ← $ᵗ CTable; let m ← (simulateQ randomOracle (master lr pkU verQ A N σ E)).run' ∅}[
        SimIS lr pkU E m] +
      forgeAdv lr pkU verQ A N σ + collAdv lr pkU verQ A N σ := by
  classical
  have h := prEvent_bind_le_sum4_of_table ($ᵗ CTable) (balQ lr pkU A N σ)
    (fun _ r => Win r.2.2) {0} ∅ (fun _ E => master lr pkU verQ A N σ E)
    (fun E m => SimIS lr pkU E m) (fun _ E => master lr pkU verQ A N σ E)
    (fun _ _ => False) (fun E => master lr pkU verQ A N σ E)
    (fun E m => ForgeEv lr pkU E m) (fun E m => CollEv lr pkU E m) fun E g hw => by
      obtain ⟨i, hi, hev⟩ := win_imp lr pkU verQ A N σ hver E g hw
      rcases i with (k | k) | b
      · simp only [Finset.mem_disjSum, Finset.mem_range] at hi
        simp only [exps, evalWithAnswerFn_map, decide_eq_true_eq] at hev
        refine Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inl ?_⟩
        rw [evalWithAnswerFn_master]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (by simpa using hi)), hev⟩
      · simp only [Finset.mem_disjSum, Finset.mem_range] at hi
        simp only [exps, evalWithAnswerFn_map, decide_eq_true_eq] at hev
        refine Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inr ?_⟩
        rw [evalWithAnswerFn_master]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (by simpa using hi)), hev⟩
      · cases b
        · simp only [exps, evalWithAnswerFn_map, decide_eq_true_eq] at hev
          exact Or.inr (Or.inr (Or.inr hev))
        · simp only [exps, evalWithAnswerFn_map, decide_eq_true_eq] at hev
          exact Or.inr (Or.inr (Or.inl hev))
  simpa only [Finset.sum_singleton, Finset.sum_empty, add_zero, forgeAdv, collAdv] using h

/-! ## The simultaneous bounds -/

/-- **The simultaneous extraction failure of the issuance requests** (`m` of them), for runs
with `q_E` cipher queries and `q k` hash queries of kind `k`. -/
noncomputable def epsIssSim (qE : ℕ) (q : Kind → ℕ) (m : ℕ) : ℝ≥0∞ :=
  (q .h21 + m) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + m) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
    (q .h23 + m) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsSim q m + stmtBindEpsSim q m +
    m * failEps q qE

/-- **The simultaneous extraction failure of the spend requests** (`n` hash queries in all). -/
noncomputable def epsSpendSim (qE n : ℕ) (q : Kind → ℕ) (m : ℕ) : ℝ≥0∞ :=
  (q .h21 + m) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + m) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + m) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsCombSim q Arith.Ratatouille.uovM m +
    stmtBindEpsSim q m + m * failEps q qE

/-- **The simultaneous extraction failure of the issuance and spend requests together** (`m`
requests of each relation from one run, `n` hash queries in all): each query of the run charged
once, at the spend relation's charge. -/
noncomputable def epsBalSim (qE n : ℕ) (q : Kind → ℕ) (m : ℕ) : ℝ≥0∞ :=
  (q .h21 + (m + m)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + (m + m)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + (m + m)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    chainHitEpsCombSim q Arith.Ratatouille.uovM (m + m) + stmtBindEpsSim q (m + m) +
    m * failEps q qE + m * failEps q qE

section Bounds

variable (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) {qV : Kind → ℕ} {nV : ℕ}
  {eV : Params → ℕ} (hver : VerifierIC CrtGen.tables verQ qV nV eV) {qA : Kind → ℕ} {nA eA : ℕ}
  (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
  (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
  (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
include hver hqA hnA

/-- The full run's budget: that of `N` rounds. -/
theorem full_bounds {ι β : Type} (o : ByteArray × (ι × β)) :
    IsKindQueryBoundIC ((fun _ => o) <$>
        roundsM A.next (serveM lr pkU verQ σ) A.recv N (A.init, (⟨[]⟩ : IssuerState), []))
        (N • (qA + qV)) ∧
      IsQueryBoundP ((fun _ => o) <$>
        roundsM A.next (serveM lr pkU verQ σ) A.recv N (A.init, (⟨[]⟩ : IssuerState), []))
        (fun t => t.isLeft = true) (N * (nA + nV)) := by
  refine ⟨(isQueryBound_map_iff _ _ _ _ _).2 ?_, (isQueryBoundP_map_iff _ _ _).2 ?_⟩
  · have h := isKindQueryBoundIC_roundsM A _ hqA (fun st op => by
      simpa using serveM_kinds lr pkU verQ hver σ st op) N (A.init, (⟨[]⟩ : IssuerState), [])
    exact h
  · simpa using isQueryBoundP_roundsM A _ _ hnA (fun st op => by
      simpa using serveM_P lr pkU verQ _ hver.hashes σ st op) N _

include heA

/-- **The issuance requests, simultaneously** (`ratatouilleIssue_sim_spec` for the `N` provers,
the full run as the reference). -/
theorem prEvent_simIss_le :
    Pr{let E ← $ᵗ CTable; let m ← (simulateQ randomOracle (master lr pkU verQ A N σ E)).run' ∅}[
      SimIss lr E m] ≤ epsIssSim (N * (eA + eVR lr pkU eV)) (N • (qA + qV)) N := by
  have h := ratatouilleIssue_sim_spec instI (fun s => UInt64.toNat_lt _) lr
    (SpecRel.hinj_ratatouilleIssue_spec (fun i : IIdx => (⟨i.1, i.2.1, i.2.2⟩ : IssueInstance)) lr
      (fun a b h => by simpa [Prod.ext_iff] using h))
    (fullI lr pkU verQ A N σ) (provI lr pkU verQ A σ) (Finset.range N) _
    (fun k hk => (prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickI
      (Finset.mem_range.1 hk)).2.2) _
    (full_bounds lr pkU verQ A N σ hver hqA hnA _).1
    (fun k hk => (prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickI
      (Finset.mem_range.1 hk)).1) _
    (full_bounds lr pkU verQ A N σ hver hqA hnA _).2
    (fun k hk => (prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickI
      (Finset.mem_range.1 hk)).2.1)
    (prefixRuns_I lr pkU verQ A N σ) (master lr pkU verQ A N σ) (fun E m => SimIss lr E m)
    fun E g hev => by
      obtain ⟨r, hr, hb⟩ := hev
      rw [evalWithAnswerFn_master] at hr
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
      exact ⟨k, Finset.mem_range.2 (List.mem_range.1 hk), hb⟩
  simpa only [Finset.card_range, epsIssSim] using h

/-- **The spend requests, simultaneously.** -/
theorem prEvent_simSp_le (hdig : pkU.digest.size = 32) :
    Pr{let E ← $ᵗ CTable; let m ← (simulateQ randomOracle (master lr pkU verQ A N σ E)).run' ∅}[
      SimSp lr pkU E m] ≤
      epsSpendSim (N * (eA + eVR lr pkU eV)) (N * (nA + nV)) (N • (qA + qV)) N := by
  have h := ratatouilleSpend_sim_spec (fun _ => pkU) (fun i : SIdx => bOf i.1)
    (fun i => i.2.1.toNat) (fun i => UInt64.toNat_lt _) (fun i => bOf i.2.2.1)
    (fun i => bOf i.2.2.2) lr
    (SpecRel.hinj_ratatouilleSpend_spec
      (fun i : SIdx => (⟨pkU.map, i.1, i.2.1, i.2.2.1, i.2.2.2⟩ : SpendInstance)) (fun _ => pkU) lr
      (fun _ => hdig) (fun a b h => by simpa [Prod.ext_iff] using h))
    (fullS lr pkU verQ A N σ) (provS lr pkU verQ A σ) (Finset.range N) _
    (fun k hk => (prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickS
      (Finset.mem_range.1 hk)).2.2) _
    (full_bounds lr pkU verQ A N σ hver hqA hnA _).1
    (fun k hk => (prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickS
      (Finset.mem_range.1 hk)).1) _
    (full_bounds lr pkU verQ A N σ hver hqA hnA _).2
    (fun k hk => (prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickS
      (Finset.mem_range.1 hk)).2.1)
    (prefixRuns_S lr pkU verQ A N σ) (master lr pkU verQ A N σ) (fun E m => SimSp lr pkU E m)
    fun E g hev => by
      obtain ⟨r, hr, hb⟩ := hev
      rw [evalWithAnswerFn_master] at hr
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
      exact ⟨k, Finset.mem_range.2 (List.mem_range.1 hk), hb⟩
  simpa only [Finset.card_range, epsSpendSim] using h

/-- **The issuance and spend requests, simultaneously and together**
(`ratatouille_sim_joint_spec`: the reference runs `fullI`, `fullS` are one run). -/
theorem prEvent_simIS_le (hdig : pkU.digest.size = 32) :
    Pr{let E ← $ᵗ CTable; let m ← (simulateQ randomOracle (master lr pkU verQ A N σ E)).run' ∅}[
      SimIS lr pkU E m] ≤
      epsBalSim (N * (eA + eVR lr pkU eV)) (N * (nA + nV)) (N • (qA + qV)) N := by
  have h := ratatouille_sim_joint_spec instI (fun s => UInt64.toNat_lt _) lr
    (SpecRel.hinj_ratatouilleIssue_spec (fun i : IIdx => (⟨i.1, i.2.1, i.2.2⟩ : IssueInstance)) lr
      (fun a b h => by simpa [Prod.ext_iff] using h))
    (fun _ => pkU) (fun i : SIdx => bOf i.1)
    (fun i => i.2.1.toNat) (fun i => UInt64.toNat_lt _) (fun i => bOf i.2.2.1)
    (fun i => bOf i.2.2.2)
    (SpecRel.hinj_ratatouilleSpend_spec
      (fun i : SIdx => (⟨pkU.map, i.1, i.2.1, i.2.2.1, i.2.2.2⟩ : SpendInstance)) (fun _ => pkU) lr
      (fun _ => hdig) (fun a b h => by simpa [Prod.ext_iff] using h))
    (fullI lr pkU verQ A N σ) (provI lr pkU verQ A σ)
    (fullS lr pkU verQ A N σ) (provS lr pkU verQ A σ) (Finset.range N) (Finset.range N) _
    (fun k hk => (prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickI
      (Finset.mem_range.1 hk)).2.2)
    (fun k hk => (prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickS
      (Finset.mem_range.1 hk)).2.2) _
    (fun k hk => (prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickI
      (Finset.mem_range.1 hk)).1)
    (full_bounds lr pkU verQ A N σ hver hqA hnA _).1
    (fun k hk => (prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickS
      (Finset.mem_range.1 hk)).1) _
    (fun k hk => (prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickI
      (Finset.mem_range.1 hk)).2.1)
    (full_bounds lr pkU verQ A N σ hver hqA hnA _).2
    (fun k hk => (prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickS
      (Finset.mem_range.1 hk)).2.1)
    (prefixRuns_I lr pkU verQ A N σ) (prefixRuns_S lr pkU verQ A N σ)
    (fun E g => by rw [fullI, fullS, tableQueryLog_runE_map, tableQueryLog_runE_map])
    (master lr pkU verQ A N σ) (fun E m => SimIS lr pkU E m)
    fun E g hev => by
      rcases hev with ⟨r, hr, hb⟩ | ⟨r, hr, hb⟩
      · rw [evalWithAnswerFn_master] at hr
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
        exact Or.inl ⟨k, Finset.mem_range.2 (List.mem_range.1 hk), hb⟩
      · rw [evalWithAnswerFn_master] at hr
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
        exact Or.inr ⟨k, Finset.mem_range.2 (List.mem_range.1 hk), hb⟩
  simpa only [Finset.card_range, epsBalSim] using h

end Bounds

/-- **Theorem 1 (balance) with simultaneous extraction**, for a cipher-querying verifier (as
`balance_le`):

    Pr[win BAL] ≤ ε_bal^sim(q', q'_E, n', N) + Adv^{uf-tag}(B) + Adv^{coll}_{Com}(C),

`q' = N•(qA + qV)`, `q'_E = N(eA + eVR)`, `n' = N(nA + nV)`: each query of the run charged once
for both relations (`epsBalSim`); against `balance_le`'s `N·ε_iss + N·ε_spend` at the same
budgets. -/
theorem balance_le_sim_num (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer)
    (hdig : pkU.digest.size = 32) {qV : Kind → ℕ} {nV : ℕ} {eV : Params → ℕ}
    (hver : VerifierIC CrtGen.tables verQ qV nV eV) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      epsBalSim (N * (eA + eVR lr pkU eV)) (N * (nA + nV)) (N • (qA + qV)) N +
        forgeAdv lr pkU verQ A N σ + collAdv lr pkU verQ A N σ :=
  (balance_le_sim lr pkU verQ A N σ hver).trans (add_le_add (add_le_add
    (prEvent_simIS_le lr pkU verQ A N σ hver hqA hnA heA hdig) le_rfl) le_rfl)

/-- **Theorem 1 (balance) with simultaneous extraction and no hypothesis on the verifier**
(`verifyIC`, as `balance_le_lean`). -/
theorem balance_le_lean_sim (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      epsBalSim (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        forgeAdv lr pkU verQL A N σ + collAdv lr pkU verQL A N σ :=
  balance_le_sim_num lr pkU verQL A N σ hdig (verifierIC_verifyIC CrtGen.tables) hqA hnA heA

/-- **Theorem 1 (balance) with simultaneous extraction and the UF-Tag advantage of the explicit
forger `B`** (as `balance_le_ufTag`). -/
theorem balance_le_ufTag_sim (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      epsBalSim (N * (eA + eVR lr pkU verifyCellBound)) (N * (nA + (2 + verifierTotal)))
          (N • (qA + (extractorQueries + verifierQueries))) N +
        ufTagAdv pkU.map σ (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)) +
        collAdv lr pkU verQL A N σ := by
  refine le_trans (balance_le_lean_sim lr pkU A N σ hdig hqA hnA heA) ?_
  have h := forgeAdv_le_ufTag lr pkU verQL A N σ (verifierIC_verifyIC CrtGen.tables)
  generalize forgeAdv lr pkU verQL A N σ = a at h ⊢
  generalize ufTagAdv pkU.map σ (forger lr pkU verQL A N (verifierIC_verifyIC CrtGen.tables)) = b
    at h ⊢
  gcongr

end RatBalance

end VoleMole.ROM.IC
