import VoleMole.ROM.PermFull
import VoleMole.ROM.AdaptFull
import VoleMole.ROM.AdaptComb
import VoleMole.ROM.AdaptPomfrit

/-!
# Adaptively chosen statements with the ideal cipher as random permutations (plan M6, §2g)

`ROM/AdaptFull.lean`, `ROM/AdaptComb.lean`, `ROM/AdaptPomfrit.lean` in the permutation model of
`ROM/PermModel.lean`: the prover makes forward and inverse cipher queries and chooses the
statement (the index of a family `stF` with common parameters `p`); the normalized prover
`normP p π P` records its queries, and the adaptive game `gameA` runs at its records.

* The per-table adaptive bounds (`prEvent_accept_le_adaptive_E`, `_comb_E`, `_pomfrit_E`) take
  any failure event `cf` that implies `KeysPre` (`ROM/CipherSame.lean`); here `cf := PostPOut p`
  (`keysPre_of_not_postP_gen`).
* The failure events, adaptively and averaged over the permutation table:
  `prEvent_jointP_bindFail_le_A` (`2·q_E²·p²` + an opened dead leaf),
  `prEvent_jointP_deadOpen_le_A` (`openHashEps q + q₁·p'²`; the dead leaf's statement is the one
  the normalized prover's output names, `prEvent_perm_deadQueried_le_g`),
  `prEvent_jointP_postP_le_A` (`q_E·4608·q₂₁·p²`).
* **`moussakaIssue_accept_le_adaptive_perm`, `ratatouilleIssue_accept_le_adaptive_perm`,
  `moussakaRedeem_accept_le_adaptive_perm`, `ratatouilleSpend_accept_le_adaptive_perm`,
  `pomfritRedeem_accept_le_adaptive_perm`**: the bounds of `ROM/PermFull.lean` plus the
  statement-binding term (`stmtBindEps q`, `stmtBindEpsD q` for PomFRIT), as in the PRF view.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## The failure events, adaptively, in the permutation model -/

section Fails

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement) (p : Params)
  (P : OracleComp specP (ByteArray × (ι × β)))

/-- **Post (point-tied), adaptively**: `≤ q_E·4608·q₂₁·p²` (it reads the normalized prover's log
only). -/
theorem prEvent_jointP_postP_le_A (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameA T stF (normP p π P) π.fwd)).run' ∅}[PostPOut p π.fwd r] ≤
      qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
  have h := prEvent_jointP_le_add (fun π => gameA T stF (normP p π P) π.fwd)
    (fun π r => PostPOut p π.fwd r) (fun _ _ => False)
    (qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2) fun g => by
      refine le_trans ?_ le_self_add
      simp only [PostPOut, evalWithAnswerFn_gameA, gameIC_aux]
      exact prEvent_perm_postP_le p g P qE hqE q hq
  rwa [prEvent_jointP_false, add_zero] at h

/-- **Binding, adaptively**: `≤ 2·q_E²·p²` plus an opened dead leaf. -/
theorem prEvent_jointP_bindFail_le_A (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameA T stF (normP p π P) π.fwd)).run' ∅}[bindFailA stF π.fwd r] ≤
      2 * qE ^ 2 * pE qE ^ 2 +
        Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
          (gameA T stF (normP p π P) π.fwd)).run' ∅}[deadOpenA stF π.fwd r] := by
  refine prEvent_jointP_le_add (fun π => gameA T stF (normP p π P) π.fwd)
    (fun π r => bindFailA stF π.fwd r) (fun π r => deadOpenA stF π.fwd r) _ fun g => ?_
  have hpt : ∀ π : PTable, bindFailA stF π.fwd
      (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF (normP p π P) π.fwd)) →
      freshBadC (runH g (normP p π P)) ∅ π.fwd collBad ∨
        deadOpenA stF π.fwd
          (evalWithAnswerFn (QueryImpl.ofFn g) (gameA T stF (normP p π P) π.fwd)) := by
    intro π hb
    simp only [bindFailA, deadOpenA, evalWithAnswerFn_gameA, stOut_gameIC] at hb ⊢
    exact bindFail_imp T _ (normP p π P) g π.fwd hb
  refine (prEvent_mono _ _ _ hpt).trans ((prEvent_or_le _ _ _).trans (add_le_add ?_ le_rfl))
  exact prEvent_perm_coll_le p g P qE hqE

/-- **`ε_open`, adaptively**: `≤ openHashEps q + q₁·p'²`, `p' = 1/(2¹²⁸ − q_E − 4607)`. -/
theorem prEvent_jointP_deadOpen_le_A (hparams : ∀ s, (stF s).params = p) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameA T stF (normP p π P) π.fwd)).run' ∅}[deadOpenA stF π.fwd r] ≤
      openHashEps q + q .h1 * pE (qE + 4607) ^ 2 := by
  let m : PTable → ProbComp (Out ((ι × β) × QueryLog specIC)) := fun π =>
    (simulateQ randomOracle (gameA T stF (normP p π P) π.fwd)).run' ∅
  let A : PTable → Out ((ι × β) × QueryLog specIC) → Prop := fun π r =>
    r.2.2.accept = true ∧
      @LeafUnqueried (icPrg π.fwd.cipher) _ (stF (stOut r)) (hashLog r.2.1.aux.2) r
  have hA : ∀ π, Pr{let r ← m π}[A π r] ≤ openHashEps q := fun π => by
    have hqW := isKindQueryBound_normP p π hq
    rw [← openHashEps_addH4]
    refine (prEvent_mono _ _ (fun r => (r.2.2.accept = true ∧
        @LeafUnqueried (icPrg π.fwd.cipher) _ (stF (stOut r)) (hashLog r.2.1.aux.2) r ∧
          ((.h23, zOut (stF (stOut r)) r) : Dom) ∈ hashLog r.2.1.aux.2) ∨
        (r.2.2.accept = true ∧ ((.h23, zOut (stF (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2))
        fun r h => (em (((.h23, zOut (stF (stOut r)) r) : Dom) ∈ hashLog r.2.1.aux.2)).elim
          (fun hz => Or.inl ⟨h.1, h.2, hz⟩) fun hz => Or.inr ⟨h.1, hz⟩).trans
      ((prEvent_or_le _ _ _).trans (add_le_add
        (prEvent_leafUnqueried_z_le_A T stF (normP p π P) p hparams (addH4 q) hqW π.fwd)
        (prEvent_zUnqueried_le_A T stF (normP p π P) π.fwd)))
  have h1 : Pr{let π ← $ᵗ PTable; let r ← m π}[A π r] ≤ openHashEps q :=
    prEvent_avgP_le m A _ hA
  have h2 : Pr{let π ← $ᵗ PTable; let r ← m π}[deadOpenA stF π.fwd r ∧ ¬A π r] ≤
      q .h1 * pE (qE + 4607) ^ 2 := by
    have h := prEvent_jointP_le_add (fun π => gameA T stF (normP p π P) π.fwd)
      (fun π r => deadOpenA stF π.fwd r ∧ ¬A π r) (fun _ _ => False)
      (q .h1 * pE (qE + 4607) ^ 2) fun g =>
        ((prEvent_mono _ _ _ fun π h => by
          simp only [A, deadOpenA, evalWithAnswerFn_gameA, stOut_gameIC] at h
          exact deadQueried_of_deadOpen T _ (normP p π P) g π.fwd h.1
            fun hL => h.2 ⟨h.1.1, hL⟩).trans
          (prEvent_perm_deadQueried_le_g g p (fun π => stF (sA g (normP p π P) π.fwd)) P
            (fun σ π hO => by simp only [sA, hO]) qE hqE q hq)).trans le_self_add
    rwa [prEvent_jointP_false, add_zero] at h
  calc Pr{let π ← $ᵗ PTable; let r ← m π}[deadOpenA stF π.fwd r]
      ≤ Pr{let π ← $ᵗ PTable; let r ← m π}[A π r ∨ (deadOpenA stF π.fwd r ∧ ¬A π r)] :=
        prEvent_jointP_mono m _ _ fun π r h => (em (A π r)).elim Or.inl fun hA => Or.inr ⟨h, hA⟩
    _ ≤ _ := (prEvent_jointP_or_le m _ _).trans (add_le_add h1 h2)

/-- Outside the point-tied Post, the keys committed at the `H₂¹` inputs are found before them,
at every statement of the family (the normalized prover's parameters are the family's). -/
theorem keysPre_A {s : ι} (hp : (stF s).params = p) (π : PTable) (g : Table)
    (h : ¬PostPOut p π.fwd
      (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stF s) (normP p π P) π.fwd))) :
    KeysPre (stF s) π.fwd (jOf g (normP p π P) π.fwd) (gLog T (stF s) (normP p π P) π.fwd g)
      g := by
  refine keysPre_of_not_postP_gen T (stF s) P p hp π g ?_
  unfold PostPOut at h
  rwa [gameIC_aux] at h

end Fails

lemma stmtBindEps_addH4 (q : Kind → ℕ) : stmtBindEps (addH4 q) = stmtBindEps q := by
  simp only [stmtBindEps, addH4_of_ne q (show Kind.mu ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide)]

lemma stmtBindEpsD_addH4 (q : Kind → ℕ) : stmtBindEpsD (addH4 q) = stmtBindEpsD q := by
  simp only [stmtBindEpsD, addH4_of_ne q (show Kind.mu ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h22 ≠ .h4 by decide)]

/-! ## The adaptive bounds in the joint experiment -/

section Joint

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
  (sys : ι → System GF128) (P : OracleComp specP (ByteArray × (ι × β)))

/-- **The adaptive bound (issue relations) in the permutation model**: `prEvent_accept_le_adaptive_E`
for the normalized prover at each permutation table, averaged, with the failure events bounded
adaptively in the permutation model. -/
theorem prEvent_accept_le_adaptiveP (hT : liftInvOk T = true) (st₀ : Statement)
    (hparams : ∀ s, (stF s).params = st₀.params) (hdel : ∀ s, (stF s).delayed = false)
    (cb : Option (ℕ × ByteArray)) (hcomb : ∀ s, (stF s).comb = cb)
    (hdec : ∀ s, dec (muIn (stF s)) = some s) {n : ℕ} (hn : ∀ s, (sys s).length = n) (N : ℕ)
    (Wit : ι → ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ s c1 lb w, (stF s).values c1 lb w = (sys s).values w)
    (hdet : ∀ (E : CTable) s, @ChainDet (icPrg E.cipher) T (stF s) (sys s) N (Wit s))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    let n' := addH4 q + extractorQueries + verifierQueries
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameA T stF (normP st₀.params π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧
          ¬@Extracted (icPrg π.fwd.cipher) _ (stF (stOut r)) (Wit (stOut r)) r] ≤
      n' .h21 * epsKOS #chal3Blocks (Chain.kosL st₀) +
        n' .h22 * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) +
        n' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) + hitSum n' (hitEps n' (combCount cb n')) +
        n' .mu * stmtEps n' .mu +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
  intro n'
  have hE := fun π : PTable => prEvent_accept_le_adaptive_E T stF dec sys
    (normP st₀.params π P) π.fwd hT st₀ hparams hdel cb hcomb hdec hn N Wit hvals (hdet π.fwd)
    (fun r => PostPOut st₀.params π.fwd r)
    (fun s g h => keysPre_A T stF st₀.params P (hparams s) π g h) (addH4 q)
    (isKindQueryBound_normP st₀.params π hq)
  have hdo := prEvent_jointP_deadOpen_le_A T stF st₀.params P hparams qE hqE q hq
  refine (prEvent_avgP_le_add3 _ _ (fun π r => bindFailA stF π.fwd r)
    (fun π r => deadOpenA stF π.fwd r) (fun π r => PostPOut st₀.params π.fwd r) _ hE).trans ?_
  gcongr
  · exact (prEvent_jointP_bindFail_le_A T stF st₀.params P qE hqE).trans (add_le_add le_rfl hdo)
  · exact prEvent_jointP_postP_le_A T stF st₀.params P qE hqE q hq

end Joint

section JointComb

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
  (P : OracleComp specP (ByteArray × (ι × β))) {M : ℕ}
  (sysL : ι → (Fin M → GF128) → System GF128) (witL : ι → (ℕ → GF128) → Prop) (dst : ByteArray)

/-- **The adaptive bound for the combined relations in the permutation model** (the normalized
prover's total hash count is `n + q₂₁`). -/
theorem prEvent_accept_le_adaptive_combP (hT : liftInvOk T = true) (st₀ : Statement)
    (hparams : ∀ s, (stF s).params = st₀.params) (hdel : ∀ s, (stF s).delayed = false)
    (hcomb : ∀ s, (stF s).comb = some (M, dst)) (hdec : ∀ s, dec (muIn (stF s)) = some s)
    {n' : ℕ} (hn' : ∀ s l, (sysL s l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ s w, prU (Fin M → GF128) (fun l => (sysL s l).Holds w ∧ ¬witL s w) ≤ εc)
    (N : ℕ) (Wit : ι → ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ s c1 (v : Prob.Bytes (16 * M)) w,
      (stF s).values c1 v.ba w = (sysL s (combDec v)).values w)
    (hdet : ∀ (E : CTable) s, @CombDet (icPrg E.cipher) M T (stF s) (sysL s) (witL s) N (Wit s))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    let n'' := addH4 q + extractorQueries + verifierQueries
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameA T stF (normP st₀.params π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧
          ¬@Extracted (icPrg π.fwd.cipher) _ (stF (stOut r)) (Wit (stOut r)) r] ≤
      n'' .h21 * epsKOS #chal3Blocks (Chain.kosL st₀) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (M, dst)) n'')) + n'' .mu * stmtEps n'' .mu +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
  intro n''
  have hE := fun π : PTable => prEvent_accept_le_adaptive_comb_E T stF dec
    (normP st₀.params π P) π.fwd sysL witL dst hT st₀ hparams hdel hcomb hdec hn' hεc N Wit hvals
    (hdet π.fwd) (fun r => PostPOut st₀.params π.fwd r)
    (fun s g h => keysPre_A T stF st₀.params P (hparams s) π g h) (n + q .h21)
    (isQueryBoundP_left_normP st₀.params π hn hq) (addH4 q)
    (isKindQueryBound_normP st₀.params π hq)
  have hdo := prEvent_jointP_deadOpen_le_A T stF st₀.params P hparams qE hqE q hq
  refine (prEvent_avgP_le_add3 _ _ (fun π r => bindFailA stF π.fwd r)
    (fun π r => deadOpenA stF π.fwd r) (fun π r => PostPOut st₀.params π.fwd r) _ hE).trans ?_
  gcongr
  · exact (prEvent_jointP_bindFail_le_A T stF st₀.params P qE hqE).trans (add_le_add le_rfl hdo)
  · exact prEvent_jointP_postP_le_A T stF st₀.params P qE hqE q hq

end JointComb

section PomJoint

variable {ι β : Type} (pk : UovPk) (sigF msgF : ι → ByteArray) (lr : Bool) (T : CrtTables)
  (P : OracleComp specP (ByteArray × (ι × β)))

/-- **PomFRIT's adaptive bound in the permutation model.** -/
theorem prEvent_accept_le_adaptive_pomfritP (hT : liftInvOk T = true) (N : ℕ) {n' : ℕ}
    (hn' : ∀ o c1 l, (sysKP pk sigF msgF lr o c1 l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ o c1 w, prU (Fin 45 → GF128)
      (fun l => (sysKP pk sigF msgF lr o c1 l).Holds w ∧ ¬witKP pk sigF msgF lr o c1 w) ≤ εc)
    (hdet : ∀ (E : CTable) s, @CombDetD (icPrg E.cipher) 45 T (stP pk sigF msgF lr s)
      (sysKP pk sigF msgF lr (some s)) (witKP pk sigF msgF lr (some s)) N
      (witKP pk sigF msgF lr (some s)))
    (qE : ℕ) (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    let n'' := addH4 q + extractorQueries + verifierQueries
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle
      (gameA T (stP pk sigF msgF lr) (normP (pomfritParams lr) π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _ (stP pk sigF msgF lr (stOut r))
          (witKP pk sigF msgF lr (some (stOut r))) r] ≤
      n'' .h21 * epsKOS #chal3Blocks (Chain.kosL (stKP pk sigF msgF lr none)) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (45, dstP)) n'')) + n'' .mu * stmtEpsD n'' .mu +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
  intro n''
  have hE := fun π : PTable => prEvent_accept_le_adaptive_pomfrit_E pk sigF msgF lr T
    (normP (pomfritParams lr) π P) π.fwd hT N hn' hεc (hdet π.fwd)
    (fun r => PostPOut (pomfritParams lr) π.fwd r)
    (fun s g h => keysPre_A T (stP pk sigF msgF lr) (pomfritParams lr) P (s := s) rfl π g h)
    (n + q .h21) (isQueryBoundP_left_normP (pomfritParams lr) π hn hq) (addH4 q)
    (isKindQueryBound_normP (pomfritParams lr) π hq)
  have hdo := prEvent_jointP_deadOpen_le_A T (stP pk sigF msgF lr) (pomfritParams lr) P
    (fun _ => rfl) qE hqE q hq
  refine (prEvent_avgP_le_add3 _ _ (fun π r => bindFailA (stP pk sigF msgF lr) π.fwd r)
    (fun π r => deadOpenA (stP pk sigF msgF lr) π.fwd r)
    (fun π r => PostPOut (pomfritParams lr) π.fwd r) _ hE).trans ?_
  gcongr
  · exact (prEvent_jointP_bindFail_le_A T (stP pk sigF msgF lr) (pomfritParams lr) P qE
      hqE).trans (add_le_add le_rfl hdo)
  · exact prEvent_jointP_postP_le_A T (stP pk sigF msgF lr) (pomfritParams lr) P qE hqE q hq

end PomJoint

/-! ## The five relations -/

section Rel

variable {ι β : Type}

/-- **Moussaka issuance with an adaptively chosen instance and the ideal cipher as random
permutations** (forward and inverse queries): `moussakaIssue_accept_le_perm` plus the
statement-binding term,

    ≤ (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε_QS(4008) + (q₂₃+1)·9·2⁻¹²⁸ + 2·q_E²·p²
      + 2·(openHashEps q + q₁·p'²) + q_E·4608·q₂₁·p² + chainHitEps q + stmtBindEps q. -/
theorem moussakaIssue_accept_le_adaptive_perm (inst : ι → ByteArray × ByteArray) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (moussakaIssue (inst s).1 (inst s).2 labelRows).instEnc ByteArray.empty)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => moussakaIssue (inst s).1 (inst s).2 labelRows)
      (normP (moussakaIssue ByteArray.empty ByteArray.empty labelRows).params π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (moussakaIssue (inst (stOut r)).1 (inst (stOut r)).2 labelRows)
          (fun _ => moussakaIssueWit (fun k => fnOf (inst (stOut r)).1 k.val)
            (fnOf (inst (stOut r)).2)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEps q + stmtBindEps q := by
  classical
  set stF : ι → Statement := fun s => moussakaIssue (inst s).1 (inst s).2 labelRows
  set st₀ := moussakaIssue ByteArray.empty ByteArray.empty labelRows
  have hmu := muIn_injective (stF := stF) (dst := st₀.dst) (fun _ => rfl) hinj
  have h := prEvent_accept_le_adaptiveP CrtGen.tables stF (decOf fun s => muIn (stF s))
    (fun s => moussakaIssueSys (inst s).1 (inst s).2) P liftInvOk_tables st₀ (fun _ => rfl)
    (fun _ => rfl) none (fun _ => rfl) (fun s => decOf_apply hmu s)
    (fun s => Moussaka.issueSystem_length _ _) 9
    (fun s _ => moussakaIssueWit (fun k => fnOf (inst s).1 k.val) (fnOf (inst s).2))
    (fun s c1 lb w => moussakaIssue_values (inst s).1 (inst s).2 labelRows c1 lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        moussakaIssue_extract_chain (inst s).1 (inst s).2 labelRows ch hv hA hAS hkos hP.1 hQS
          admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    qE hqE q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps_perm q rfl, stmtEps_game, stmtBindEps_addH4]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, moussakaIssue]) (by norm_num [st₀, moussakaIssue])
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
          ((q .h23 : ℝ≥0∞) + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEps q + stmtBindEps q +
          (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
          (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
          qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
        gcongr
    _ = _ := by ring

/-- **Ratatouille issuance with an adaptively chosen instance and the ideal cipher as random
permutations** (as `moussakaIssue_accept_le_adaptive_perm`, with `ε_QS(3776)`). -/
theorem ratatouilleIssue_accept_le_adaptive_perm (inst : ι → ByteArray × ℕ × ByteArray)
    (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows).instEnc ByteArray.empty)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows)
      (normP (ratatouilleIssue .empty 0 .empty labelRows).params π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (ratatouilleIssue (inst (stOut r)).1 (inst (stOut r)).2.1 (inst (stOut r)).2.2 labelRows)
          (fun _ => ratatouilleIssueWit (fnOf (inst (stOut r)).1) (inst (stOut r)).2.1
            (fnOf (inst (stOut r)).2.2)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEps q + stmtBindEps q := by
  classical
  set stF : ι → Statement := fun s =>
    ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 labelRows
  set st₀ := ratatouilleIssue ByteArray.empty 0 ByteArray.empty labelRows
  have hmu := muIn_injective (stF := stF) (dst := st₀.dst) (fun _ => rfl) hinj
  have h := prEvent_accept_le_adaptiveP CrtGen.tables stF (decOf fun s => muIn (stF s))
    (fun s => ratatouilleIssueSys (inst s).1 (inst s).2.1 (inst s).2.2) P liftInvOk_tables st₀
    (fun _ => rfl) (fun _ => rfl) none (fun _ => rfl) (fun s => decOf_apply hmu s)
    (fun s => Ratatouille.issueSystem_length _ _ _) 9
    (fun s _ => ratatouilleIssueWit (fnOf (inst s).1) (inst s).2.1 (fnOf (inst s).2.2))
    (fun s c1 lb w => ratatouilleIssue_values (inst s).1 (inst s).2.1 (inst s).2.2 labelRows c1
      lb w)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc hv A hA hAS hkos hQS hP =>
        ratatouilleIssue_extract_chain (inst s).1 (inst s).2.1 (inst s).2.2 labelRows ch hv hA hAS
          hkos hP.1 hQS admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    qE hqE q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps_perm q rfl, stmtEps_game, stmtBindEps_addH4]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, ratatouilleIssue])
      (by norm_num [st₀, ratatouilleIssue])
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
          ((q .h23 : ℝ≥0∞) + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEps q + stmtBindEps q +
          (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
          (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
          qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
        gcongr
    _ = _ := by ring

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Moussaka redemption with an adaptively chosen instance and the ideal cipher as random
permutations** (`moussakaRedeem_accept_le_perm` plus `stmtBindEps q`). -/
theorem moussakaRedeem_accept_le_adaptive_perm (anc : ι → List UovPk)
    (hn64 : ∀ s, (anc s).length ≤ 64) (nf ctxIss ctxRed cd : ι → ByteArray) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows).instEnc
        ByteArray.empty)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows)
      (normP (moussakaRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty ByteArray.empty
        labelRows).params π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (moussakaRedeem (anc (stOut r)) (nf (stOut r)) (ctxIss (stOut r)) (ctxRed (stOut r))
            (cd (stOut r)) labelRows)
          (fun _ => moussakaRedeemWit GF256.ofBits ((anc (stOut r)).map UovPk.map)
            (fnOf (nf (stOut r))) (fnOf (ctxIss (stOut r))) (fnOf (ctxRed (stOut r)))) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q Moussaka.M +
        stmtBindEps q := by
  classical
  set stF : ι → Statement := fun s =>
    moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows
  set st₀ := moussakaRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty ByteArray.empty
    labelRows
  have hmu := muIn_injective (stF := stF) (dst := st₀.dst) (fun _ => rfl) hinj
  have h := prEvent_accept_le_adaptive_combP CrtGen.tables stF (decOf fun s => muIn (stF s)) P
    (fun s => moussakaRedeemSysL (anc s) (nf s) (ctxIss s) (ctxRed s))
    (fun s => moussakaRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    (toBA (VoleMole.Spec.makeDst "mous" 0 'l' '0')) liftInvOk_tables st₀ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun s => decOf_apply hmu s)
    (fun s _ => Moussaka.redeemSystem_length _ _ _ _ _ _ _)
    (fun s w => prU_comb_bad_le _ _ w fun hW =>
      moussaka_redeem_comb_bad_gf128 _ (by simpa using hn64 s) _ _ _ w hW) 9
    (fun s _ => moussakaRedeemWit GF256.ofBits ((anc s).map UovPk.map) (fnOf (nf s))
      (fnOf (ctxIss s)) (fnOf (ctxRed s)))
    (fun s c1 v w => by
      rw [moussakaRedeem_values]; simp only [moussakaRedeemSys, ofArr_combinationOf_ba])
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc l hv A hA hAS hkos hQS hcb hP =>
        moussakaRedeem_extract_chain (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows ch l hv
          hA hAS hkos hP.1 hQS hcb admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    qE hqE n hn q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb_perm q Moussaka.M rfl, stmtEps_game,
    stmtBindEps_addH4]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, moussakaRedeem]) (by norm_num [st₀, moussakaRedeem])
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ +
            ((n : ℝ≥0∞) + (q .h21 : ℝ≥0∞) + 2 + (verifierTotal : ℝ≥0∞)) / 2 ^ 448) +
          ((q .h23 : ℝ≥0∞) + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q Moussaka.M +
          stmtBindEps q +
          (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
          (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
          qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
        gcongr
    _ = _ := by push_cast; ring

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Ratatouille spend with an adaptively chosen instance and the ideal cipher as random
permutations** (`ratatouilleSpend_accept_le_perm` plus `stmtBindEps q`). -/
theorem ratatouilleSpend_accept_le_adaptive_perm (pk : ι → UovPk) (nf : ι → ByteArray)
    (d : ι → ℕ) (hd : ∀ s, d s < 2 ^ 64) (cNext ctxIss : ι → ByteArray) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows).instEnc
        ByteArray.empty)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows)
      (normP (ratatouilleSpend ⟨ByteArray.empty, ByteArray.empty⟩ ByteArray.empty 0
        ByteArray.empty ByteArray.empty labelRows).params π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (ratatouilleSpend (pk (stOut r)) (nf (stOut r)) (d (stOut r)) (cNext (stOut r))
            (ctxIss (stOut r)) labelRows)
          (fun _ => ratatouilleSpendWit GF256.ofBits (pk (stOut r)).map (fnOf (nf (stOut r)))
            (d (stOut r)) (fnOf (cNext (stOut r))) (fnOf (ctxIss (stOut r)))) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q Ratatouille.uovM +
        stmtBindEps q := by
  classical
  set stF : ι → Statement := fun s =>
    ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows
  set st₀ := ratatouilleSpend ⟨ByteArray.empty, ByteArray.empty⟩ ByteArray.empty 0 ByteArray.empty
    ByteArray.empty labelRows
  have hmu := muIn_injective (stF := stF) (dst := st₀.dst) (fun _ => rfl) hinj
  have h := prEvent_accept_le_adaptive_combP CrtGen.tables stF (decOf fun s => muIn (stF s)) P
    (fun s => ratatouilleSpendSysL (pk s) (nf s) (d s) (cNext s) (ctxIss s))
    (fun s => ratatouilleSpendWit GF256.ofBits (pk s).map (fnOf (nf s)) (d s) (fnOf (cNext s))
      (fnOf (ctxIss s)))
    (toBA (VoleMole.Spec.makeDst "rata" 0 'l' '0')) liftInvOk_tables st₀ (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun s => decOf_apply hmu s)
    (fun s _ => Ratatouille.spendSystem_length _ _ _ _ _ _ _ _)
    (fun s w => prU_comb_bad_le _ _ w fun hW =>
      ratatouille_spend_comb_bad_gf128 _ _ (hd s) _ _ w hW) 9
    (fun s _ => ratatouilleSpendWit GF256.ofBits (pk s).map (fnOf (nf s)) (d s) (fnOf (cNext s))
      (fnOf (ctxIss s)))
    (fun s c1 v w => by
      rw [ratatouilleSpend_values]; simp only [ratatouilleSpendSys, ofArr_combinationOf_ba])
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      exact fun ch known acc l hv A hA hAS hkos hQS hcb hP =>
        ratatouilleSpend_extract_chain (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows ch l hv
          hA hAS hkos hP.1 hQS hcb admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    qE hqE n hn q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb_perm q Ratatouille.uovM rfl, stmtEps_game,
    stmtBindEps_addH4]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, ratatouilleSpend])
      (by norm_num [st₀, ratatouilleSpend])
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ +
            ((n : ℝ≥0∞) + (q .h21 : ℝ≥0∞) + 2 + (verifierTotal : ℝ≥0∞)) / 2 ^ 448) +
          ((q .h23 : ℝ≥0∞) + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q Ratatouille.uovM +
          stmtBindEps q +
          (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
          (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
          qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
        gcongr
    _ = _ := by push_cast; ring

end Rel

section PomRel

variable {ι β : Type} (pk : UovPk)

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **PomFRIT redemption with an adaptively chosen signature and message and the ideal cipher as
random permutations** (`pomfritRedeem_accept_le_perm` plus `stmtBindEpsD q`). -/
theorem pomfritRedeem_accept_le_adaptive_perm (sigF msgF : ι → ByteArray) (labelRows : Bool)
    (P : OracleComp specP (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundP P q) :
    Pr{let π ← $ᵗ PTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => pomfritRedeem pk (sigF s) (msgF s) labelRows)
      (normP (pomfritParams labelRows) π P) π.fwd)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg π.fwd.cipher) _
          (pomfritRedeem pk (sigF (stOut r)) (msgF (stOut r)) labelRows)
          (fun c1 => pomfritWit GF256.ofBits 119 45 pk.map
            (fun k => ⟨fnOf (pomfritTarget (pomfritParams labelRows) pk.digest c1 (sigF (stOut r))
              (msgF (stOut r))) k.val⟩)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + q .h21 + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
        (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
        qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 + chainHitEpsComb q 45 +
        stmtBindEpsD q := by
  classical
  have h := prEvent_accept_le_adaptive_pomfritP pk sigF msgF labelRows CrtGen.tables P
    liftInvOk_tables 2 (n' := 1313)
    (fun o c1 l => (PomFRIT.pomfritRedeemSystem_length _ _ _ _ _ _ _).trans (by norm_num))
    (fun o c1 w => prU_comb_bad_le _ _ w fun hW => pomfrit_comb_bad_gf128 _ _ _ _ w hW)
    (fun E s => by
      let _ : HasPrg := icPrg E.cipher
      intro ch known acc l c1 hch1 hv A hA hAS hkos hQS hcb hP
      subst hch1
      exact pomfritRedeem_extract_chain pk (sigF s) (msgF s) labelRows ch _ l hv hA hAS hkos hP.1
        hQS hcb admissible deltaBlocks deltaBlocks_injOn acc hP.2)
    qE hqE n hn q hq
  refine h.trans ?_
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb_perm q 45 rfl, stmtEpsD_game,
    stmtBindEpsD_addH4]
  have hkos : epsKOS #chal3Blocks (Chain.kosL (stKP pk sigF msgF labelRows none)) ≤
      (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [stKP, pomfritRedeem, pomfritParams])
      (by norm_num [stKP, pomfritRedeem, pomfritParams])
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    addH4_of_ne q (show Kind.h21 ≠ .h4 by decide), addH4_of_ne q (show Kind.h22 ≠ .h4 by decide),
    addH4_of_ne q (show Kind.h23 ≠ .h4 by decide)]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ +
            ((n : ℝ≥0∞) + (q .h21 : ℝ≥0∞) + 2 + (verifierTotal : ℝ≥0∞)) / 2 ^ 448) +
          ((q .h23 : ℝ≥0∞) + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q 45 +
          stmtBindEpsD q +
          (2 * qE ^ 2 * pE qE ^ 2 + (openHashEps q + q .h1 * pE (qE + 4607) ^ 2)) +
          (openHashEps q + q .h1 * pE (qE + 4607) ^ 2) +
          qE * ((4608 * q .h21 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
        gcongr
    _ = _ := by push_cast; ring

end PomRel

end VoleMole.ROM.IC
