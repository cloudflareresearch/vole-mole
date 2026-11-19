import VoleMole.ROM.MoussakaUnboundOMUF
import VoleMole.ROM.MoussakaUnboundSim
import VoleMole.ROM.MoussakaOMUFSim

/-!
# Unbound Moussaka Theorem U1 with simultaneous extraction

`ROM/MoussakaUnboundOMUF.lean`'s `omufU_le_num` charges the extraction failure of each proof
separately (`qI·εI + qI·εUI + qR·εUR`, each `ε` the single-proof bound at the whole game's
budget). All proofs come from **one** run of the game (`PBI j`, `PUI j`, `PUR j` are projections
of `game`), so their extraction failures are bounded together:

* the unbound issuance and unbound redemption proofs **jointly**
  (`moussakaUnbound_sim_joint_spec`, `ROM/MoussakaUnboundSim.lean`): each query of the run charged
  once for both relations, at the redemption relation's charge (`εU^sim`, `m = qI + qR`);
* the bound issuance proofs (`ε_ext^{iss}`) as a **third family**, by their own simultaneous
  bound (`moussakaIssue_sim_spec`, `ROM/SimSpec.lean`; `OMUF.epsIsim`, `m = qI`). This charges the
  run a second time. The note (§3.1) charges `ε_ext^{iss}` this way; a joint bound over the three
  families would need a three-family version of `ROM/SimJoint.lean`.

* `SimBI`, `SimUI`, `SimUR`: some proof of the family in the reductions' view is accepted and not
  extracted; `SimU = SimUI ∨ SimUR`.
* `omufU_le_sim` (the reduction, two simultaneous events) and **`omufU_le_num_sim`**:

      Pr[Win] ≤ εI^sim(q', q'_E, qI) + εU^sim(q', q'_E, n', qI, qR) + AdvBind(B₁) + AdvCTUF(B₂),

  at the budgets of `omufU_le_num` (`q' = gameK q qI qR`, `q'_E = gameE lr qE qI qR`,
  `n' = gameH n qI qR`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC.OMUFU

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ROM
  VoleMole.ROM.IC VoleMole.ROM.IC.OMUF

variable {K qR : ℕ} (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
  (A : Adversary K qR)

/-! ## The simultaneous events -/

/-- **Some bound issuance proof of the view is accepted and not extracted.** -/
def SimBI (E : CTable) (v : View K) : Prop := ∃ r ∈ v.2.1, BadBI E lr r

/-- **Some unbound issuance proof of the view is accepted and not extracted.** -/
def SimUI (E : CTable) (v : View K) : Prop := ∃ r ∈ v.2.2.1, BadUI E lr r

/-- **Some unbound redemption proof of the view is accepted and not extracted.** -/
def SimUR (E : CTable) (v : View K) : Prop := ∃ r ∈ v.2.2.2, BadUR E lr pk r

/-- **Some unbound proof (issuance or redemption) of the view is accepted and not extracted.** -/
def SimU (E : CTable) (v : View K) : Prop := SimUI lr E v ∨ SimUR lr pk E v

/-- **Theorem U1, the reduction, with simultaneous extraction events**: `omufU_le` with the
extraction failures of the bound issuance proofs as one event and those of the unbound proofs as
another, both of the reductions' run. -/
theorem omufU_le_sim :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        SimBI lr E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        SimU lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Forge lr pk E v] := by
  have h := prEvent_bind_le_sum4_of_table ($ᵗ CTable) (fun E => runE E (game lr pk sk qI A))
    (fun _ r => Win r.1) {0} {0} (fun _ E => extAll lr pk sk qI A E) (fun E v => SimBI lr E v)
    (fun _ E => extAll lr pk sk qI A E) (fun E v => SimU lr pk E v)
    (fun E => extAll lr pk sk qI A E) (fun E v => Coll lr pk E v) (fun E v => Forge lr pk E v)
    fun E g hw => by
      rw [evalWithAnswerFn_runE] at hw
      rcases win_imp lr pk sk qI A g E hw with ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | hC | hF
      · refine Or.inl ⟨0, Finset.mem_singleton_self 0, ?_⟩
        rw [extAll_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inl ?_⟩)
        rw [extAll_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inr ?_⟩)
        rw [extAll_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · exact Or.inr (Or.inr (Or.inl hC))
      · exact Or.inr (Or.inr (Or.inr hF))
  simpa only [Finset.sum_singleton] using h

/-! ## The simultaneous bounds -/

/-- **The simultaneous extraction failure of the unbound issuance and redemption proofs
together** (`mI` issuance and `mR` redemption proofs from one run, `n` the run's hash queries in
all; `moussakaUnbound_sim_joint_spec`): each query of the run charged once, at the unbound
redemption relation's charge. -/
noncomputable def epsUsim (q : Kind → ℕ) (qE n mI mR : ℕ) : ℝ≥0∞ :=
  (q .h21 + (mI + mR)) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + (mI + mR)) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 7929) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + (mI + mR)) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    chainHitEpsCombSim q Arith.Moussaka.M (mI + mR) + stmtBindEpsSim q (mI + mR) +
    mI * failEps q qE + mR * failEps q qE

variable {lr pk sk qI A} {q : Kind → ℕ} {qE n : ℕ}

/-- **The bound issuance proofs, simultaneously** (`moussakaIssue_sim_spec`). -/
theorem prEvent_simBI_le (hA : A.Budget q qE n) :
    Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        SimBI lr E v] ≤ epsIsim (gameK q qI qR) (gameE lr qE qI qR) qI := by
  have h := moussakaIssue_sim_spec (ι := ιI) (β := GOut K) (fun s => s.1) (fun s => s.2.1)
    (fun s => s.2.2) lr (hinjI lr) (projBI 0 <$> game lr pk sk qI A)
    (fun j => projBI j <$> game lr pk sk qI A) (Finset.range qI) _
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (game_e lr pk sk hA qI)) _
    ((isQueryBound_map_iff _ _ _ _ _).2 (game_k lr pk sk hA qI))
    (fun _ _ => (isQueryBound_map_iff _ _ _ _ _).2 (game_k lr pk sk hA qI)) _
    ((isQueryBoundP_map_iff _ _ _).2 (game_h lr pk sk hA qI))
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (game_h lr pk sk hA qI))
    (fun E => prefixRuns_map E (game lr pk sk qI A) projBI 0 _)
    (extAll lr pk sk qI A) (fun E v => SimBI lr E v) fun E g hev => by
      obtain ⟨r, hr, hb⟩ := hev
      rw [extAll_eval] at hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
      exact ⟨j, Finset.mem_range.2 (List.mem_range.1 hj), hb⟩
  simpa only [Finset.card_range, epsIsim] using h

/-- **The unbound issuance and redemption proofs, simultaneously and together**
(`moussakaUnbound_sim_joint_spec`: both relations' provers are projections of the one game). -/
theorem prEvent_simU_le (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        SimU lr pk E v] ≤ epsUsim (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qI qR := by
  have h := moussakaUnbound_sim_joint_spec (ιI := ιI) (βI := GOut K) (ιR := ιR K) (βR := GOut K)
    (stUI lr) lr (fun s => s.1) (fun s => Unbound.moussakaUnboundIssue_stmt _ _ lr)
    (fun s => s.2.1) (hinjUI lr)
    (stUR lr pk) (fun s => ancR pk s) (fun s => by simpa using s.2.1) (fun s => s.1.2.1)
    (fun s => s.1.2.2.1) (fun s => s.1.2.2.2.1) (fun s => s.1.2.2.2.2)
    (fun s => Unbound.moussakaUnboundRedeem_stmt _ _ _ _ _ lr) (fun s => s.2.2.1)
    (hinjUR lr pk hdig hdinj)
    (projUI 0 <$> game lr pk sk qI A) (fun j => projUI j <$> game lr pk sk qI A)
    (projUR 0 <$> game lr pk sk qI A) (fun j => projUR j <$> game lr pk sk qI A)
    (Finset.range qI) (Finset.range qR) _
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (game_e lr pk sk hA qI))
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (game_e lr pk sk hA qI)) _
    (fun _ _ => (isQueryBound_map_iff _ _ _ _ _).2 (game_k lr pk sk hA qI))
    ((isQueryBound_map_iff _ _ _ _ _).2 (game_k lr pk sk hA qI))
    (fun _ _ => (isQueryBound_map_iff _ _ _ _ _).2 (game_k lr pk sk hA qI)) _
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (game_h lr pk sk hA qI))
    ((isQueryBoundP_map_iff _ _ _).2 (game_h lr pk sk hA qI))
    (fun _ _ => (isQueryBoundP_map_iff _ _ _).2 (game_h lr pk sk hA qI))
    (fun E => prefixRuns_map E (game lr pk sk qI A) projUI 0 _)
    (fun E => prefixRuns_map E (game lr pk sk qI A) projUR 0 _)
    (fun E g => by rw [tableQueryLog_runE_map, tableQueryLog_runE_map])
    (extAll lr pk sk qI A) (fun E v => SimU lr pk E v) fun E g hev => by
      rcases hev with ⟨r, hr, hb⟩ | ⟨r, hr, hb⟩
      · rw [extAll_eval] at hr
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
        exact Or.inl ⟨j, Finset.mem_range.2 (List.mem_range.1 hj), hb⟩
      · rw [extAll_eval] at hr
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
        exact Or.inr ⟨j, Finset.mem_range.2 (List.mem_range.1 hj), hb⟩
  simpa only [Finset.card_range, epsUsim] using h

/-- **Theorem U1 (unforgeability per redemption context) with simultaneous extraction.** For an
adversary within its budget and honest Anchors with distinct 32-byte key digests (as
`omufU_le_num`):

    Pr[Win] ≤ εI^sim(q', q'_E, qI) + εU^sim(q', q'_E, n', qI, qR) + AdvBind(B₁) + AdvCTUF(B₂),

at the budgets of `omufU_le_num`. The unbound proofs are charged jointly (each query of the run
once for both unbound relations); the bound issuance proofs, a third relation family, by their own
simultaneous bound. -/
theorem omufU_le_num_sim (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (runE E (game lr pk sk qI A))).run' ∅}[
        Win r.1] ≤
      epsIsim (gameK q qI qR) (gameE lr qE qI qR) qI +
      epsUsim (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qI qR +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Forge lr pk E v] :=
  (omufU_le_sim lr pk sk qI A).trans (add_le_add (add_le_add (add_le_add
    (prEvent_simBI_le hA) (prEvent_simU_le hA hdig hdinj)) le_rfl) le_rfl)

end VoleMole.ROM.IC.OMUFU
