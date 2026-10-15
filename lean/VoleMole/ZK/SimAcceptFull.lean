import VoleMole.ZK.SimAccept
import VoleMole.ZK.CollideRO

/-!
# The verifier accepts simulated proofs, with the run-time checks discharged (`lean/docs/zk.md` §5, H8)

`simulateRO_accept` (`ZK/SimAccept.lean`) assumes that the verifier's run on the simulated proof
with the original hashes reaches `chal3` (`Reaches`: `check_format` passes, the opening
reconstructs, the lifted `Δ'` is nonzero). Here those conditions are proved, for faest-arch-opt's
CRT tables (`CrtGen.tables`):

* `simulate_checkFormat`: **every simulated proof passes `check_format`** (its size is
  `proofBytes`, `fields_assemble`; its `Δ` is accepted, so the grinding byte is zero).
* `simulate_reconstruct`: **its opening reconstructs** (`reconstruct_openingOf`), for any `iv`.
* `simulate_reaches`: **the run reaches `chal3` unless `Δ = 0`**: `Δ' = Δ·W_CRT` is zero only for
  `Δ = 0` among the accepted values (`tDL_eq_zero`).
* `simulateRO_accept'`: so the simulated proof is accepted under the programmed oracle whenever
  the simulation succeeds and its `Δ` is not `0` (`¬ HitZero`), with no other assumption.
* `pr_simulateRO_reject`: **the simulation fails or its proof is rejected with probability
  `≤ noHitProb + 1/|A| ≤ 2^{−2¹⁵} + 2⁻¹¹¹`** over the simulator's coins (`pr_hitZero_le`,
  `noHitProb_le`), and `≤ 2⁻¹¹⁰` (`pr_simulateRO_reject_110`). This is the same event `GrindBad`
  as for the real prover.

So `zk_sim`'s run-time checks of `check_format`, of the reconstruction and of `Δ' ≠ 0` on the
simulated proofs are implied (the last except for `Δ = 0`, which grinding reaches with probability
`≤ 2⁻¹¹¹`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

variable [VoleMole.Verifier.HasPrg]
set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-- The simulated proof, when grinding hits. -/
lemma simulate_eq {p : Params} (c : SimCoins p) {ctr : ℕ} {δ : Bytes 16}
    (hf : firstHit c.1.2.1 = some (ctr, δ)) :
    simulate p c = .ok (simAssemble p c.1 ctr δ c.2) := by
  simp only [simulate, hf, simAssemble]

/-- A simulation produces a proof iff grinding hits, and then it is `simAssemble`. -/
lemma simulate_ok {p : Params} {c : SimCoins p} {proof : ByteArray}
    (h : simulate p c = .ok proof) :
    ∃ ctr δ, firstHit c.1.2.1 = some (ctr, δ) ∧ proof = simAssemble p c.1 ctr δ c.2 := by
  rcases hf : firstHit c.1.2.1 with _ | ⟨ctr, δ⟩
  · simp only [simulate, hf] at h; cases h
  · rw [simulate_eq c hf] at h
    exact ⟨ctr, δ, rfl, (Except.ok.inj h).symm⟩

lemma accepts_spec {δ : Bytes 16} (h : accepts (ba δ) = true) :
    (ba δ).get! 15 = 0 ∧ openCount (ba δ) ≤ 105 := by
  unfold accepts at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h

/-- The fields of a simulated proof that the verifier reads before `chal3`. -/
lemma simAssemble_fields (p : Params) (s : Shared) (ctr : ℕ) (δ : Bytes 16) (f : SimFields p)
    (hoc : openCount (ba δ) ≤ 105) :
    let pf : Proof := { params := p, bytes := simAssemble p s ctr δ f }
    pf.bytes.size = p.proofBytes ∧ pf.delta = ba δ ∧
      pf.opening = openingOf (ba δ) s.2.2.1 s.2.2.2 :=
  ⟨(fields_assemble p _).2.2.2.2.2.2.2.2.2,
    (fields_assemble p _).2.2.2.2.2.2.1.trans (fit_of_size (size_ba _)),
    (fields_assemble p _).2.2.2.2.2.1.trans (fit_of_size (openingOf_size _ _ _ hoc))⟩

/-- **Every simulated proof passes `check_format`.** -/
theorem simulate_checkFormat {p : Params} {c : SimCoins p} {proof : ByteArray}
    (h : simulate p c = .ok proof) : ({ params := p, bytes := proof } : Proof).checkFormat = true := by
  obtain ⟨ctr, δ, hf, rfl⟩ := simulate_ok h
  obtain ⟨h15, hoc⟩ := accepts_spec (firstHit_accepts hf)
  obtain ⟨hs, hd, -⟩ := simAssemble_fields p c.1 ctr δ c.2 hoc
  simp only [Proof.checkFormat, Bool.and_eq_true, beq_iff_eq]
  exact ⟨hs, by rw [hd, h15]⟩

/-- **The opening of every simulated proof reconstructs**, for any `iv`. -/
theorem simulate_reconstruct {p : Params} {c : SimCoins p} {proof : ByteArray}
    (h : simulate p c = .ok proof) (iv : ByteArray) :
    let pf : Proof := { params := p, bytes := proof }
    (BAVC.reconstruct iv pf.opening pf.delta).isSome := by
  obtain ⟨ctr, δ, hf, rfl⟩ := simulate_ok h
  obtain ⟨-, hoc⟩ := accepts_spec (firstHit_accepts hf)
  obtain ⟨-, hd, ho⟩ := simAssemble_fields p c.1 ctr δ c.2 hoc
  intro pf
  show (BAVC.reconstruct iv pf.opening pf.delta).isSome
  rw [show pf.opening = _ from ho, show pf.delta = _ from hd]
  exact reconstruct_openingOf iv (ba δ) c.1.2.2.1 c.1.2.2.2 hoc

/-- **The verifier's run on a simulated proof reaches `chal3`** (with any hashes), unless the
simulator's `Δ` is `0`. -/
theorem simulate_reaches (Hs : Hashes) (st : Statement) (c : SimCoins st.params)
    {proof : ByteArray} (h : simulate st.params c = .ok proof) (hz : ¬ HitZero c.1.2.1) :
    Reaches Hs CrtGen.tables st proof := by
  obtain ⟨ctr, δ, hf, hp⟩ := simulate_ok h
  have hacc := firstHit_accepts hf
  have hδ : δ ≠ 0 := fun e => hz ⟨ctr, e ▸ hf⟩
  refine ⟨simulate_checkFormat h, ?_⟩
  obtain ⟨leaves, hl⟩ := Option.isSome_iff_exists.1
    (simulate_reconstruct h (ivOf Hs { params := st.params, bytes := proof } (st.mu1 Hs)))
  refine ⟨leaves, hl, fun h0 => hδ (tDL_eq_zero hacc ?_)⟩
  subst hp
  obtain ⟨-, hd, -⟩ := simAssemble_fields st.params c.1 ctr δ c.2 (accepts_spec hacc).2
  rw [← h0, tDL]
  show _ = (W128.rowMul (BAVC.deltaBit _) 120 CrtGen.tables.wCrt).toGF
  rw [hd]

/-- **The simulator's programmed oracle makes the verifier accept its proof**, with no
assumption beyond `Δ ≠ 0` (`¬ HitZero`): `check_format`, the reconstruction and `Δ' ≠ 0` are
proved (`simulate_reaches`). -/
theorem simulateRO_accept' (Hs : Hashes) (st : Statement) (c : SimCoins st.params)
    {proof : ByteArray} {Hs' : Hashes} (h : simulateRO Hs CrtGen.tables st c = .ok (proof, Hs'))
    (hz : ¬ HitZero c.1.2.1) : (verify Hs' CrtGen.tables st proof).accept = true := by
  refine simulateRO_accept Hs CrtGen.tables st c h (simulate_reaches Hs st c ?_ hz)
  unfold simulateRO at h
  cases hs : simulate st.params c with
  | error e => rw [hs] at h; cases h
  | ok pf =>
    rw [hs] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [h.1]

/-- A simulation that fails, or whose proof the programmed verifier rejects, had no grinding hit
or hit `Δ = 0`. -/
lemma simulateRO_bad (Hs : Hashes) (st : Statement) (c : SimCoins st.params)
    (h : ¬ ∃ proof Hs', simulateRO Hs CrtGen.tables st c = .ok (proof, Hs') ∧
      (verify Hs' CrtGen.tables st proof).accept = true) :
    firstHit c.1.2.1 = none ∨ HitZero c.1.2.1 := by
  rcases hf : firstHit c.1.2.1 with _ | ⟨ctr, δ⟩
  · exact Or.inl rfl
  · refine Or.inr (by_contra fun hz => h ?_)
    have hs := simulate_eq c hf
    have hro : simulateRO Hs CrtGen.tables st c = .ok (simAssemble st.params c.1 ctr δ c.2,
        program Hs (programPoints Hs CrtGen.tables st (simAssemble st.params c.1 ctr δ c.2)
          c.1.2.1 (((firstHit c.1.2.1).map (·.1)).getD 0))) := by
      unfold simulateRO; rw [hs]; rfl
    exact ⟨_, _, hro, simulateRO_accept' Hs st c hro hz⟩

/-- `Pr` over the simulator's coins of an event of its grinding answers is `Pr` over `Grind`. -/
lemma pr_simCoins_grind {p : Params} (P : Grind → Prop) :
    pr (SimCoins p) (fun c => P c.1.2.1) = pr Grind P := by
  have e1 := pr_prod_fst (β := SimFields p) (fun s : Shared => P s.2.1)
  have e2 := pr_prod_snd (α := Bytes 16)
    (fun x : Grind × (Fin BAVC.tau → Bytes 32) × (Fin 105 → Bytes 16) => P x.1)
  have e3 := pr_prod_fst (β := (Fin BAVC.tau → Bytes 32) × (Fin 105 → Bytes 16)) P
  exact e1.trans (e2.trans e3)

/-- **The simulated proof is accepted under the programmed oracle except with probability
`≤ noHitProb + 1/|A|`**: the simulation fails (no grinding hit) or hits `Δ = 0`. -/
theorem pr_simulateRO_reject (Hs : Hashes) (st : Statement) :
    pr (SimCoins st.params) (fun c => ¬ ∃ proof Hs',
        simulateRO Hs CrtGen.tables st c = .ok (proof, Hs') ∧
        (verify Hs' CrtGen.tables st proof).accept = true) ≤
      noHitProb + 1 / (#Accept.accSet : ℝ) := by
  refine (pr_mono fun c hc => simulateRO_bad Hs st c hc).trans ((pr_or_le _ _).trans ?_)
  rw [pr_simCoins_grind (fun g => firstHit g = none), pr_simCoins_grind HitZero]
  exact add_le_add le_rfl pr_hitZero_le

/-- **`pr_simulateRO_reject`, numerically: `≤ 2^{−2¹⁵} + 2⁻¹¹¹`.** -/
theorem pr_simulateRO_reject_num (Hs : Hashes) (st : Statement) :
    pr (SimCoins st.params) (fun c => ¬ ∃ proof Hs',
        simulateRO Hs CrtGen.tables st c = .ok (proof, Hs') ∧
        (verify Hs' CrtGen.tables st proof).accept = true) ≤
      (1 / 2) ^ (2 ^ 15) + 1 / 2 ^ 111 := by
  refine (pr_mono fun c hc => simulateRO_bad Hs st c hc).trans ((pr_or_le _ _).trans ?_)
  rw [pr_simCoins_grind (fun g => firstHit g = none), pr_simCoins_grind HitZero]
  refine add_le_add noHitProb_le (pr_hitZero_le.trans ?_)
  rw [div_le_div_iff₀ (by exact_mod_cast lt_of_lt_of_le (by positivity) Accept.card_accSet_ge)
    (by positivity), one_mul, one_mul]
  exact_mod_cast Accept.card_accSet_ge

/-- **`pr_simulateRO_reject`: `≤ 2⁻¹¹⁰`.** -/
theorem pr_simulateRO_reject_110 (Hs : Hashes) (st : Statement) :
    pr (SimCoins st.params) (fun c => ¬ ∃ proof Hs',
        simulateRO Hs CrtGen.tables st c = .ok (proof, Hs') ∧
        (verify Hs' CrtGen.tables st proof).accept = true) ≤ 1 / 2 ^ 110 := by
  refine (pr_simulateRO_reject_num Hs st).trans ?_
  have : ((1 : ℝ) / 2) ^ (2 ^ 15) ≤ 1 / 2 ^ 111 := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by norm_num))
  calc ((1 : ℝ) / 2) ^ (2 ^ 15) + 1 / 2 ^ 111 ≤ 1 / 2 ^ 111 + 1 / 2 ^ 111 := add_le_add this le_rfl
    _ = 1 / 2 ^ 110 := by norm_num

end VoleMole.ZK.Sim
