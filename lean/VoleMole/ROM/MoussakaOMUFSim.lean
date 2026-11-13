import VoleMole.ROM.SimSpec
import VoleMole.ROM.MoussakaOMUF

/-!
# Moussaka Theorem 1 with simultaneous extraction

`ROM/MoussakaOMUF.lean`'s `omuf_le_num` charges the extraction failure of each of the `qI`
issuance and `qR` redemption proofs separately (`qI·εI + qR·εR`, each `ε` the single-proof bound
at the whole game's budget). The proofs all come from **one** run of the game (`PI j`, `PR j` are
projections of `game`), so their extraction failures are bounded **together**
(`ROM/SimSpec.lean`): the per-query bad events of the run are charged once per relation, and per
proof only the extraction game's own extractor and verifier queries and the failure events.

* `SimI`, `SimR`: some issuance (redemption) proof of the reductions' view is accepted and not
  extracted; `simI_of`, `simR_of`: the per-table link with `win_imp`'s disjuncts.
* `prEvent_simI_le`, `prEvent_simR_le`: the simultaneous bounds `εI^sim`, `εR^sim`.
* **`omuf_le_sim`** (the reduction) and **`omuf_le_num_sim`** (with the terms):

      Pr[Win] ≤ εI^sim(q', q'_E, qI) + εR^sim(q', q'_E, n', qR) + AdvBind(B₁) + AdvCTUF(B₂),

  `εI^sim(q', q'_E, m) = (q'₂₁+m)·2⁻¹⁵⁰ + (q'₂₂+m)·ε_QS(4008) + (q'₂₃+m)·9·2⁻¹²⁸
  + chainHitEpsSim q' m + stmtBindEpsSim q' m + m·failEps q' q'_E` (`εR^sim` likewise, with the
  redemption relation's `H₂²` charge), at the same budgets `q' = gameK q qI qR`,
  `q'_E = gameE lr qE qI qR`, `n' = gameH n qI qR` as `omuf_le_num`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC.OMUF

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ROM
  VoleMole.ROM.IC

variable {K qR : ℕ} (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
  (A : Adversary K qR)

/-! ## The simultaneous events -/

/-- **Some issuance proof of the view is accepted and not extracted.** -/
def SimI (E : CTable) (v : View K) : Prop := ∃ r ∈ v.2.1, BadI E lr r

/-- **Some redemption proof of the view is accepted and not extracted.** -/
def SimR (E : CTable) (v : View K) : Prop := ∃ r ∈ v.2.2, BadR E lr pk r

theorem simI_of (g : Table) (E : CTable)
    (h : ∃ j ∈ Finset.range qI, BadI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stI lr) (PI lr pk sk qI A j) E))) :
    SimI lr E (evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E)) := by
  obtain ⟨j, hj, hb⟩ := h
  rw [extAll_eval]
  exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩

theorem simR_of (g : Table) (E : CTable)
    (h : ∃ j ∈ Finset.range qR, BadR E lr pk (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stR lr pk) (PR lr pk sk qI A j) E))) :
    SimR lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E)) := by
  obtain ⟨j, hj, hb⟩ := h
  rw [extAll_eval]
  exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩

/-- **Theorem 1, the reduction, with simultaneous extraction events**: `omuf_le` with the
extraction failures of all issuance (redemption) proofs as one event of the reductions' run. -/
theorem omuf_le_sim :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        SimI lr E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        SimR lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Forge lr pk E v] := by
  have h := prEvent_bind_le_sum4_of_table ($ᵗ CTable) (fun E => runE E (game lr pk sk qI A))
    (fun _ r => Win r.1) {0} {0} (fun _ E => extAll lr pk sk qI A E) (fun E v => SimI lr E v)
    (fun _ E => extAll lr pk sk qI A E) (fun E v => SimR lr pk E v)
    (fun E => extAll lr pk sk qI A E) (fun E v => Coll lr pk E v) (fun E v => Forge lr pk E v)
    fun E g hw => by
      rw [evalWithAnswerFn_runE] at hw
      rcases win_imp lr pk sk qI A g E hw with hI | hR | hC | hF
      · exact Or.inl ⟨0, Finset.mem_singleton_self 0, simI_of lr pk sk qI A g E hI⟩
      · exact Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, simR_of lr pk sk qI A g E hR⟩)
      · exact Or.inr (Or.inr (Or.inl hC))
      · exact Or.inr (Or.inr (Or.inr hF))
  simpa only [Finset.sum_singleton] using h

/-! ## The simultaneous bounds -/

/-- **The simultaneous extraction failure of the issuance proofs**, for a run with `q k` hash
queries of kind `k` and `qE` cipher queries, and `m` proofs. -/
noncomputable def epsIsim (q : Kind → ℕ) (qE m : ℕ) : ℝ≥0∞ :=
  (q .h21 + m) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + m) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
    (q .h23 + m) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsSim q m + stmtBindEpsSim q m +
    m * failEps q qE

/-- **The simultaneous extraction failure of the redemption proofs** (`n` the run's hash queries
in all). -/
noncomputable def epsRsim (q : Kind → ℕ) (qE n m : ℕ) : ℝ≥0∞ :=
  (q .h21 + m) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + m) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + m) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsCombSim q Arith.Moussaka.M m +
    stmtBindEpsSim q m + m * failEps q qE

variable {lr pk sk qI A} {q : Kind → ℕ} {qE n : ℕ}

theorem prEvent_simI_le (hA : A.Budget q qE n) :
    Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        SimI lr E v] ≤ epsIsim (gameK q qI qR) (gameE lr qE qI qR) qI := by
  have h := moussakaIssue_sim_spec (ι := ιI) (β := GOut K) (fun s => s.1) (fun s => s.2.1)
    (fun s => s.2.2) lr (hinjI lr) (projI 0 <$> game lr pk sk qI A)
    (fun j => projI j <$> game lr pk sk qI A) (Finset.range qI) _
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (game_e lr pk sk hA qI)) _
    ((isQueryBound_map_iff _ _ _ _ _).2 (game_k lr pk sk hA qI))
    (fun _ _ => (isQueryBound_map_iff _ _ _ _ _).2 (game_k lr pk sk hA qI)) _
    ((isQueryBoundP_map_iff _ _ _).2 (game_h lr pk sk hA qI))
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (game_h lr pk sk hA qI))
    (fun E => prefixRuns_map E (game lr pk sk qI A) projI 0 _)
    (extAll lr pk sk qI A) (fun E v => SimI lr E v) fun E g hev => by
      obtain ⟨r, hr, hb⟩ := hev
      rw [extAll_eval] at hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
      exact ⟨j, Finset.mem_range.2 (List.mem_range.1 hj), hb⟩
  simpa only [Finset.card_range, epsIsim] using h

theorem prEvent_simR_le (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        SimR lr pk E v] ≤ epsRsim (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qR := by
  have h := moussakaRedeem_sim_spec (ι := ιR K) (β := GOut K) (fun s => ancR pk s)
    (fun s => by simpa using s.2.1) (fun s => s.1.2.1) (fun s => s.1.2.2.1)
    (fun s => s.1.2.2.2.1) (fun s => s.1.2.2.2.2) (fun s => s.2.2.1) (fun s => s.2.2.2.1)
    (fun s => s.2.2.2.2) lr (hinjR lr pk hdig hdinj) (projR 0 <$> game lr pk sk qI A)
    (fun j => projR j <$> game lr pk sk qI A) (Finset.range qR) _
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (game_e lr pk sk hA qI)) _
    ((isQueryBound_map_iff _ _ _ _ _).2 (game_k lr pk sk hA qI))
    (fun _ _ => (isQueryBound_map_iff _ _ _ _ _).2 (game_k lr pk sk hA qI)) _
    ((isQueryBoundP_map_iff _ _ _).2 (game_h lr pk sk hA qI))
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (game_h lr pk sk hA qI))
    (fun E => prefixRuns_map E (game lr pk sk qI A) projR 0 _)
    (extAll lr pk sk qI A) (fun E v => SimR lr pk E v) fun E g hev => by
      obtain ⟨r, hr, hb⟩ := hev
      rw [extAll_eval] at hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
      exact ⟨j, Finset.mem_range.2 (List.mem_range.1 hj), hb⟩
  simpa only [Finset.card_range, epsRsim] using h

/-- **Theorem 1 (one-more unforgeability) with simultaneous extraction.** For an adversary within
its budget and honest Anchors with distinct 32-byte key digests (as `omuf_le_num`):

    Pr[Win] ≤ εI^sim(q', q'_E, qI) + εR^sim(q', q'_E, n', qR) + AdvBind(B₁) + AdvCTUF(B₂),

at the budgets of `omuf_le_num` (`q' = gameK q qI qR`, `q'_E = gameE lr qE qI qR`,
`n' = gameH n qI qR`). The per-query terms are charged once over the game's queries plus one
verification per proof (`q'₂₃ + qI`, not `qI·(q'₂₃ + 1)`); the failure terms stay per proof. -/
theorem omuf_le_num_sim (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      epsIsim (gameK q qI qR) (gameE lr qE qI qR) qI +
      epsRsim (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qR +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Forge lr pk E v] :=
  (omuf_le_sim lr pk sk qI A).trans (add_le_add (add_le_add (add_le_add
    (prEvent_simI_le hA) (prEvent_simR_le hA hdig hdinj)) le_rfl) le_rfl)

end VoleMole.ROM.IC.OMUF
