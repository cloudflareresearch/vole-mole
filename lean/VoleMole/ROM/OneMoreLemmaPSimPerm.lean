import VoleMole.ROM.OneMorePerm

/-!
# PomFRIT's Theorem U1 with simultaneous extraction, AES as random permutations

`lean/docs/security/pomfrit.md` §6.4, `lean/docs/probabilistic-plan.md` §2o. `pomfrit_U1_sim`
(`ROM/OneMoreLemmaPSim.lean`) with the cipher a uniform permutation table and a forger that makes
forward and inverse cipher queries (`ROM/OneMorePerm.lean`).

* **The game** (`gameP`): `game` with the composed adversary drawing a permutation table `π`, the
  forger normalized at `π` (`ForgerP.toIC`: inverse queries recorded as forward records, the
  reduction's hidden `H₄` query of the `iv` before every `H₂¹` query), the reduction, verifier and
  extractor reading `π.fwd`. `pomfrit_U1_boundP`: as `pomfrit_U1_bound`,
  `Pr[PomWin] ≤ Adv^{ompr}(red …) + Pr[∃ i ≤ ℓ, PFail i]`.
* **Per table** (`prEvent_pfailZ_sim_le_Ec` at `E = π.fwd` for the normalized forger, with the
  point-tied Post `PostPOut` in place of `PostOut`; `KeysPre` outside it from N1,
  `keysPre_proverP`). The shared-run and per-forgery query terms do not depend on `π`.
* **Averaged over `π`** (`prEvent_pfailZ_sim_leP`): the failure terms of each forgery's derived
  game by `sum_fail_le_fam` (the derived provers are a `RecFamily`, `recFamily_proverP`):
  `failEpsP` for `failEps`; the verifier's `H₂³` input unqueried by `prEvent_zUnqueried_le_A`.
* **Theorem U1** (`prEvent_pfail_sim_leP`, `pomfrit_U1_simP`):

      Pr[PomWin] ≤ Adv^{ompr}(red …; Q_T + ℓ + 1, ℓ) + pfailSimEpsP(q', q_E', n', ℓ),
      pfailSimEpsP = Σ_k (q'_k + (ℓ+1)·r_k)·simEps_k + (ℓ+1)·(failEpsP(q', q_E') + 2⁻¹²⁸),

  `q' = qP (addH4 qA) Q_T ℓ` (one more `H₄` query per `H₂¹` query of the forger, which no charge
  reads), `q_E' = eP lr q_E ℓ` (`q_E` forward and inverse queries), `n' = nP (nA + qA₂₁) Q_T ℓ`.
  `pfailSimEpsP` is `pfailSimEps` with `failEpsP` in place of `failEps`.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.ZK.Sim VoleMole.Verifier.Bridge

/-! ## The game -/

section Games

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (n ℓ : ℕ) (T : CrtTables)
  (lr : Bool) (A : ForgerP)

/-- The composed adversary with its permutation table drawn uniformly, the forger normalized at
the table, for the hint rule `hint` at the forward table. -/
noncomputable def advCP {Hn : Type} (hint : CTable → QueryLog specIC → ByteArray → Hn)
    (tgts : TG × Hn → List TG) (pk : UovPk) :
    ProbComp (OracleComp (specC Hn) (List (ByteArray × SIss) × Bool)) := do
  let π ← $ᵗ PTable
  pure (Acomp T lr π.fwd (hint π.fwd) tgts pk ℓ (A.toIC lr π))

/-- **The one-more forgery game for PomFRIT, AES as random permutations**: the forger runs against
a uniform permutation table `π` (forward and inverse cipher queries), the hashes, `hash_to_target`
and the Issuer; its forgeries are verified and extracted with the forward table `π.fwd`. -/
noncomputable def gameP {Hn : Type} (φ : Hn → TG ≃ TG)
    (hint : CTable → QueryLog specIC → ByteArray → Hn) (tgts : TG × Hn → List TG) :=
  omuf KG pre n φ (advCP ℓ T lr A hint tgts)

set_option linter.constructorNameAsVariable false in
lemma pomWin_forgesP {Hn : Type} (φ : Hn → TG ≃ TG)
    (hint : CTable → QueryLog specIC → ByteArray → Hn) (tgts : TG × Hn → List TG)
    {r : UovPk × (List (ByteArray × SIss) × Bool) × (ByteArray → Option (TG × Hn)) ×
      Ch Ans ByteArray Hn TG} (hr : r ∈ support (gameP KG pre n ℓ T lr A φ hint tgts))
    (hw : PomWin ℓ r) : Forges ℓ r.2.1 r.2.2.2 := by
  simp only [gameP, omuf, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨kp, -, a, ha, L, -, r', hr', rfl⟩ := hr
  simp only [advCP, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ha
  obtain ⟨π, -, rfl⟩ := ha
  have h1 : r'.1 ∈ support (Acomp T lr π.fwd (hint π.fwd) tgts kp.1 ℓ (A.toIC lr π)) := by
    refine support_simulateQ_run'_subset (realImpl φ (pre kp.2))
      (Acomp T lr π.fwd (hint π.fwd) tgts kp.1 ℓ (A.toIC lr π)) (fun _ => none, ch0 L) ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨r', hr', rfl⟩
  obtain ⟨hlen, hnd⟩ := acomp_support T lr π.fwd (hint π.fwd) tgts kp.1 ℓ _ h1 hw.1
  exact ⟨hw.1, hlen, hnd, hw.2⟩

set_option linter.constructorNameAsVariable false in
lemma advCP_bound {Hn : Type} (QT : ℕ) (hint : CTable → QueryLog specIC → ByteArray → Hn)
    (tgts : TG × Hn → List TG) (hA : ∀ pk, IsQueryBoundP (A pk) (fun q => isHTP q = true) QT)
    (pk : UovPk) : ∀ a ∈ support (advCP ℓ T lr A hint tgts pk),
      IsQueryBoundP a (fun q => isTgt q = true) (QT + (ℓ + 1)) := by
  intro a ha
  simp only [advCP, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ha
  obtain ⟨π, -, rfl⟩ := ha
  exact acomp_bound (E := π.fwd) (hint := hint π.fwd) T lr tgts pk ℓ QT _
    (ht_normU _ π (hA pk))

set_option linter.constructorNameAsVariable false in
/-- **Theorem U1 in the permutation model, the reduction**: as `pomfrit_U1_bound`. -/
theorem pomfrit_U1_boundP (QT : ℕ) (e1 : CTable → QueryLog specIC → ByteArray → TG)
    (hA : ∀ pk, IsQueryBoundP (A pk) (fun q => isHTP q = true) QT) :
    Pr{let r ← gameP KG pre (QT + (ℓ + 1)) ℓ T lr A addHint e1 tgts1}[PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre (QT + (ℓ + 1)) (red addHint (advCP ℓ T lr A e1 tgts1))}[
        Wins ℓ (goodPre relP) r.1 r.2.1 r.2.2] +
      Pr{let r ← gameP KG pre (QT + (ℓ + 1)) ℓ T lr A addHint e1 tgts1}[
        ∃ i : Fin (ℓ + 1), PFail i.val r] := by
  refine (prEvent_mono_of_support _ _ _ fun _ hr hw =>
    pomWin_forgesP KG pre _ ℓ T lr A _ _ _ hr hw).trans ?_
  refine (omuf_le_of_bound KG pre _ ℓ addHint _ (advCP_bound ℓ T lr A QT _ _ hA)
    (goodPre relP)).trans (add_le_add le_rfl (prEvent_mono _ _ _ fun r ⟨i, hr⟩ => ⟨i, ?_⟩))
  obtain ⟨hacc, ⟨x, σ⟩, hp, hng⟩ := hr
  refine ⟨hacc, x, σ, hp, fun ⟨a, e, hs, hrel⟩ => hng ?_⟩
  simp only [hs, Option.map_some]
  exact ⟨_, _, rfl, hrel⟩

set_option linter.constructorNameAsVariable false in
/-- **Theorem U2 in the permutation model, the reduction**: as `pomfrit_U2_bound`. -/
theorem pomfrit_U2_boundP (QT : ℕ) (τ : ℕ) (sh : CTable → QueryLog specIC → ByteArray → List TG)
    (hA : ∀ pk, IsQueryBoundP (A pk) (fun q => isHTP q = true) QT) :
    Pr{let r ← gameP KG pre (QT + (ℓ + 1)) ℓ T lr A noHint (hint2 τ sh) tgts2}[PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre (QT + (ℓ + 1)) (red noHint (advCP ℓ T lr A (hint2 τ sh) tgts2))}[
        Wins ℓ (goodShift τ relP) r.1 r.2.1 r.2.2] +
      Pr{let r ← gameP KG pre (QT + (ℓ + 1)) ℓ T lr A noHint (hint2 τ sh) tgts2}[
        ∃ i : Fin (ℓ + 1), ShiftFail τ i.val r] := by
  refine (prEvent_mono_of_support _ _ _ fun _ hr hw =>
    pomWin_forgesP KG pre _ ℓ T lr A _ _ _ hr hw).trans ?_
  refine (omuf_le_of_bound KG pre _ ℓ noHint _ (advCP_bound ℓ T lr A QT _ _ hA)
    (goodShift τ relP)).trans (add_le_add le_rfl (prEvent_mono _ _ _ fun r ⟨i, hr⟩ => ⟨i, ?_⟩))
  obtain ⟨hacc, ⟨x, σ⟩, hp, hng⟩ := hr
  refine ⟨hacc, x, σ, hp, fun ⟨a, δs, hs, hlen, hrel⟩ => hng ?_⟩
  simp only [hs, Option.map_some]
  exact ⟨_, _, rfl, hlen, hrel⟩

end Games

/-! ## Averaging over permutation tables -/

/-- **Averaging a per-permutation-table bound with per-output failure events** (four of them;
`prEvent_avg_le_sum4` for `PTable`). -/
theorem prEvent_avgP_le_sum4 {ι' X Y : Type} (m : PTable → ProbComp X) (ev : PTable → X → Prop)
    (c : ℝ≥0∞) (J : Finset ι') (m' : ι' → PTable → ProbComp Y)
    (Q₁ Q₂ Q₃ Q₄ : PTable → Y → Prop)
    (h : ∀ π, Pr{let r ← m π}[ev π r] ≤
      c + ∑ j ∈ J, Pr{let r ← m' j π}[Q₁ π r ∨ Q₂ π r ∨ Q₃ π r ∨ Q₄ π r]) :
    Pr{let π ← $ᵗ PTable; let r ← m π}[ev π r] ≤
      c + ∑ j ∈ J, (Pr{let π ← $ᵗ PTable; let r ← m' j π}[Q₁ π r] +
        Pr{let π ← $ᵗ PTable; let r ← m' j π}[Q₂ π r] +
        Pr{let π ← $ᵗ PTable; let r ← m' j π}[Q₃ π r] +
        Pr{let π ← $ᵗ PTable; let r ← m' j π}[Q₄ π r]) := by
  let : MeasurableSpace PTable := ⊤
  have h4 : ∀ j π, Pr{let r ← m' j π}[Q₁ π r ∨ Q₂ π r ∨ Q₃ π r ∨ Q₄ π r] ≤
      Pr{let r ← m' j π}[Q₁ π r] + Pr{let r ← m' j π}[Q₂ π r] + Pr{let r ← m' j π}[Q₃ π r] +
        Pr{let r ← m' j π}[Q₄ π r] :=
    fun j π => (prEvent_or_le _ _ _).trans (by
      rw [add_assoc, add_assoc]
      exact add_le_add le_rfl ((prEvent_or_le _ _ _).trans
        (add_le_add le_rfl (prEvent_or_le _ _ _))))
  rw [prEvent_bind_of_discrete]
  simp only [prEvent_bind_of_discrete]
  calc ∫⁻ π, Pr{let r ← m π}[ev π r] ∂𝒟[$ᵗ PTable]
      ≤ ∫⁻ π, (c + ∑ j ∈ J, (Pr{let r ← m' j π}[Q₁ π r] + Pr{let r ← m' j π}[Q₂ π r] +
          Pr{let r ← m' j π}[Q₃ π r] + Pr{let r ← m' j π}[Q₄ π r])) ∂𝒟[$ᵗ PTable] :=
        MeasureTheory.lintegral_mono fun π => (h π).trans
          (add_le_add le_rfl (Finset.sum_le_sum fun j _ => h4 j π))
    _ = c * 𝒟[$ᵗ PTable] Set.univ + ∑ j ∈ J, (∫⁻ π, Pr{let r ← m' j π}[Q₁ π r] ∂𝒟[$ᵗ PTable] +
          ∫⁻ π, Pr{let r ← m' j π}[Q₂ π r] ∂𝒟[$ᵗ PTable] +
          ∫⁻ π, Pr{let r ← m' j π}[Q₃ π r] ∂𝒟[$ᵗ PTable] +
          ∫⁻ π, Pr{let r ← m' j π}[Q₄ π r] ∂𝒟[$ᵗ PTable]) := by
        rw [MeasureTheory.lintegral_add_left measurable_const, MeasureTheory.lintegral_const,
          MeasureTheory.lintegral_finsetSum _ fun _ _ => measurable_from_top]
        refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
        rw [MeasureTheory.lintegral_add_left measurable_from_top,
          MeasureTheory.lintegral_add_left measurable_from_top,
          MeasureTheory.lintegral_add_left measurable_from_top]
    _ ≤ _ := add_le_add (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)) le_rfl

/-! ## U1's term, averaged over the permutation table -/

/-- **`pfailSimEps` in the permutation model**: the failure terms `failEpsP` (`L0-L2` with
`p = 1/(2¹²⁸ − q_E)`). -/
noncomputable def pfailSimEpsP (q : Kind → ℕ) (qE n ℓ : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ adaptKinds, ((q k : ℝ≥0∞) + (ℓ + 1) * ((extractorQueries + verifierQueries) k : ℝ≥0∞)) *
      simEps (n + (2 + verifierTotal)) (q + extractorQueries + verifierQueries) k +
    (ℓ + 1) * (failEpsP q qE + (2 ^ 128 : ℝ≥0∞)⁻¹)

variable (lr : Bool) (pk : UovPk) (pre : TG → SIss) (A : ForgerP) (Lst : List TG) (ℓ : ℕ)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **U1's term with simultaneous extraction, permutation model, for a fixed key and target
stream**: over the permutation table and the hash table, some forgery fails with probability at
most `pfailSimEpsP`. -/
theorem prEvent_pfailZ_sim_leP (hd : pk.digest.size = 32) {qA : Kind → ℕ} {nA qE QT : ℕ}
    (hA : ForgerBoundP A qA nA qE QT) :
    Pr{let π ← $ᵗ PTable; let z ← (simulateQ randomOracle
        ((simulateQ (htW (AR := Ans) addHint pre) (Acomp CrtGen.tables lr π.fwd (e1P lr π.fwd)
          tgts1 pk ℓ (A.toIC lr π))).run (hs0 Lst))).run' ∅}[∃ i : Fin (ℓ + 1), PFailZ pk i.val z] ≤
      pfailSimEpsP (qP (addH4 qA) QT ℓ) (eP lr qE ℓ) (nP (nA + qA .h21) QT ℓ) ℓ := by
  classical
  set q := qP (addH4 qA) QT ℓ
  set e := eP lr qE ℓ
  set ε := simEps (nP (nA + qA .h21) QT ℓ + (2 + verifierTotal))
    (q + extractorQueries + verifierQueries)
  set c := ∑ k ∈ adaptKinds, (q k : ℝ≥0∞) * ε k +
      ∑ _j : Fin (ℓ + 1), ∑ k ∈ adaptKinds, ((extractorQueries + verifierQueries) k : ℝ≥0∞) * ε k
  set pL := pomfritParams lr
  have hb : ∀ (π : PTable) (j : Fin (ℓ + 1)),
      IsKindQueryBoundIC (proverP lr pk pre (A.toIC lr π) Lst j.val) q ∧
      IsQueryBoundP (proverP lr pk pre (A.toIC lr π) Lst j.val) (fun t => t.isLeft = true)
        (nP (nA + qA .h21) QT ℓ) ∧
      IsQueryBoundP (proverP lr pk pre (A.toIC lr π) Lst j.val) (fun t => t.isRight = true) e :=
    fun π j => proverP_bounds lr pre pk (hA.toIC lr π) Lst (Nat.lt_succ_iff.1 j.isLt)
  have havg := prEvent_avgP_le_sum4 _ (fun _ z => ∃ i : Fin (ℓ + 1), PFailZ pk i.val z) c
    (Finset.univ : Finset (Fin (ℓ + 1)))
    (fun j π => (simulateQ randomOracle (gameDP lr π.fwd pk pre (A.toIC lr π) Lst j.val)).run' ∅)
    (fun π r => bindFailA (stG lr pk) π.fwd r) (fun π r => deadOpenA (stG lr pk) π.fwd r)
    (fun π r => PostPOut pL π.fwd r)
    (fun _ r => r.2.2.accept = true ∧
      ((.h23, zOut (stG lr pk (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2)
    (fun π => prEvent_pfailZ_sim_le_Ec lr pk pre (A.toIC lr π) Lst ℓ hd (hA.toIC lr π) π.fwd
      (PostPOut pL π.fwd) fun j s g h => keysPre_proverP lr pk pre A Lst π j.val s g h)
  refine havg.trans ?_
  have h3 := sum_fail_le_fam CrtGen.tables (stG lr pk) pL (fun _ => rfl)
    (fun (j : Fin (ℓ + 1)) π => proverP lr pk pre (A.toIC lr π) Lst j.val) Finset.univ
    (fun j _ => recFamily_proverP lr pk pre A Lst j.val) e (fun j _ π => (hb π j).2.2) q
    (fun j _ π => (hb π j).1)
  rw [Finset.sum_add_distrib]
  refine (add_le_add le_rfl (add_le_add h3
    (Finset.sum_le_card_nsmul _ _ (2 ^ 128 : ℝ≥0∞)⁻¹ fun j _ => ?_))).trans_eq ?_
  · exact prEvent_avgP_le _ _ _ fun π =>
      prEvent_zUnqueried_le_A CrtGen.tables (stG lr pk) (proverP lr pk pre (A.toIC lr π) Lst j.val)
        π.fwd
  simp only [c, pfailSimEpsP, Finset.card_univ, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  simp only [add_mul, mul_assoc, mul_add]
  ring

section Game

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (lr : Bool) (A : ForgerP)

/-- **Lemma P's term with simultaneous extraction, permutation model** (`prEvent_pfail_sim_le`
with AES as random permutations and inverse queries). -/
theorem prEvent_pfail_sim_leP (n ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBoundP A qA nA qE QT) :
    Pr{let r ← gameP KG pre n ℓ CrtGen.tables lr A addHint (e1P lr) tgts1}[
        ∃ i : Fin (ℓ + 1), PFail i.val r] ≤
      pfailSimEpsP (qP (addH4 qA) QT ℓ) (eP lr qE ℓ) (nP (nA + qA .h21) QT ℓ) ℓ := by
  unfold gameP omuf advCP
  simp only [bind_assoc, pure_bind]
  apply prEvent_bind_le_of_forall_le_of_support KG _ (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)
  intro kp hkp
  rw [eqd_swap ($ᵗ PTable) (unifList TG n) (fun π L => (do
    let r ← (simulateQ (realImpl addHint (pre kp.2))
      (Acomp CrtGen.tables lr π.fwd (e1P lr π.fwd) tgts1 kp.1 ℓ (A.toIC lr π))).run
        (fun _ => none, ch0 L)
    pure (kp.1, r.1, r.2))) (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)]
  apply prEvent_bind_le_of_forall_le _ _ (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)
  intro L
  refine le_trans (le_of_eq ?_) (prEvent_pfailZ_sim_leP lr kp.1 (pre kp.2) A L ℓ (hdig kp hkp) hA)
  have key : ∀ π : PTable, (simulateQ (realImpl addHint (pre kp.2))
      (Acomp CrtGen.tables lr π.fwd (e1P lr π.fwd) tgts1 kp.1 ℓ (A.toIC lr π))).run
        (fun _ => none, ch0 L) =
      (fun z => (z.1.1, (z.1.2.1, chOf z.1.2.2 z.2))) <$>
        (simulateQ randomOracle ((simulateQ (htW (AR := Ans) addHint (pre kp.2))
          (Acomp CrtGen.tables lr π.fwd (e1P lr π.fwd) tgts1 kp.1 ℓ (A.toIC lr π))).run
            (hs0 L))).run ∅ := fun π =>
    realImpl_run_eq addHint (pre kp.2) _ (fun _ => none) (ch0 L)
  simp only [key, StateT.run'_eq, map_bind, Functor.map_map, bind_pure_comp]
  have hev : ∀ a : ((List (ByteArray × SIss) × Bool) × HTS) × (specR Ans).QueryCache,
      (∃ i : Fin (ℓ + 1), PFail i.val (kp.1, a.1.1, a.1.2.1, chOf a.1.2.2 a.2)) =
        (∃ i : Fin (ℓ + 1), PFailZ kp.1 i.val a.1) := fun a => rfl
  simp only [hev]

/-- **Theorem U1 with simultaneous extraction, AES as random permutations with inverse queries**
(`pomfrit.md` §6.1, §6.4; G8): for a key generation with 32-byte key digests, any Issuer and a
forger of the permutation model with budget `qA`, `nA`, `q_E` (forward and inverse), `Q_T`, with
Lemma P's `E₁` as the reduction's first-phase rule,

    Pr[PomWin] ≤ Adv^{ompr}(red …; Q_T + ℓ + 1, ℓ) + pfailSimEpsP(q', q_E', n', ℓ),

`q' = qP (addH4 qA) Q_T ℓ`, `q_E' = eP lr q_E ℓ`, `n' = nP (nA + qA₂₁) Q_T ℓ`. -/
theorem pomfrit_U1_simP (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBoundP A qA nA qE QT) :
    Pr{let r ← gameP KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A addHint (e1P lr) tgts1}[
        PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre (QT + (ℓ + 1))
          (red addHint (advCP ℓ CrtGen.tables lr A (e1P lr) tgts1))}[
        Wins ℓ (goodPre relP) r.1 r.2.1 r.2.2] +
      pfailSimEpsP (qP (addH4 qA) QT ℓ) (eP lr qE ℓ) (nP (nA + qA .h21) QT ℓ) ℓ :=
  (pomfrit_U1_boundP KG pre ℓ CrtGen.tables lr A QT (e1P lr) hA.ht).trans
    (add_le_add le_rfl (prEvent_pfail_sim_leP KG pre lr A _ ℓ hdig hA))

end Game

end VoleMole.ROM.OneMore.Pomfrit
