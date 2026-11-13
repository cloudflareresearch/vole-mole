import VoleMole.ROM.OneMoreLemmaPBound
import VoleMole.ROM.OneMoreShiftFail

/-!
# U2's term in the one-more game, bounded (gap G8): Theorem U2 with every term explicit

`lean/docs/security/pomfrit.md` §6.2, §6.4. This file bounds `Pr[∃ i ≤ ℓ, ShiftFail i]` in
PomFRIT's one-more game with U2's shift rule (`hintS`, `ROM/OneMoreShiftFail.lean`), every term
explicit, and plugs it into Theorem U2 (`pomfrit_U2_bound`). The assembly is U1's
(`ROM/OneMoreLemmaPBound.lean`) with `shiftFail_events` for `pfail_events` and Lemma P's bound
without `Shift` (`pomfritT_accept_le_some`, `ROM/LemmaPSome.lean`) for `pomfritT_accept_le_major`:
the `H₂³` charge is `2·2⁻¹²⁸` per query instead of `2⁻⁷¹`.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC

section Fixed

/-- **Lemma P's extraction term without `Shift`** (`pomfritT_accept_le_some`'s bound) for a prover with `q k` hash
queries of kind `k`, `n` hash queries in all and `qE` cipher queries. -/
noncomputable def someEps (q : Kind → ℕ) (qE n : ℕ) : ℝ≥0∞ :=
  (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((2 : ℝ≥0∞) / 2 ^ 128) +
    (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
    (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    chainHitEpsComb q 45 + stmtBindEpsD q

/-- **U2's failure per forgery**, every term explicit, for derived provers with `q`, `n`, `qE`
queries: the extraction term, Post (`1024·q_E·q₁·2⁻²⁵⁶`), the verifier's `H₂³` input unqueried
(`2⁻¹²⁸`), and the chain hits and order hits of the derived game (`n''` its queries per kind). -/
noncomputable def sfailEps (q : Kind → ℕ) (qE n : ℕ) : ℝ≥0∞ :=
  someEps q qE n + ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    (2 ^ 128 : ℝ≥0∞)⁻¹ +
    ∑ k ∈ hitKinds, (q + extractorQueries + verifierQueries) k *
      (hitEps (q + extractorQueries + verifierQueries)
        (combCount cbP (q + extractorQueries + verifierQueries)) k +
        orderEps (q + extractorQueries + verifierQueries) k)

/-- The four events of `shiftFail_events`, on the logged output of the derived game. -/
def evJS (E : CTable) (lr : Bool) (pk : UovPk) :
    ℕ → Out (((TG × ByteArray × ByteArray) × AuxP) × QueryLog specIC) × QueryLog spec → Prop
  | 0, o => o.1.2.2.accept = true ∧ ¬SomeExtracted E (stG lr pk (stOut o.1))
      (witKT pk hG (some (stOut o.1))) o.1
  | 1, o => PostOut E o.1
  | 2, o => o.1.2.2.accept = true ∧
      ((.h23, zOut (stG lr pk (stOut o.1)) o.1) : Dom) ∉ hashLog o.1.2.1.aux.2
  | _, o => HitOut o

variable (lr : Bool) (pk : UovPk) (pre : TG → SIss) (A : Forger) (Lst : List TG) (ℓ : ℕ)

/-- **U2's term for a fixed key and target stream**: over the cipher table and the hash
table, some forgery fails with probability at most `(ℓ + 1)·sfailEps`. -/
theorem prEvent_shiftFailZ_le (hd : pk.digest.size = 32) {qA : Kind → ℕ} {nA qE QT : ℕ}
    (hA : ForgerBound A qA nA qE QT) :
    Pr{let E ← $ᵗ CTable; let z ← (simulateQ randomOracle ((simulateQ (htW (AR := Ans) noHint pre)
        (Acomp CrtGen.tables lr E (hintS lr E) tgts2 pk ℓ A)).run (hs0G Lst))).run' ∅}[
        ∃ i : Fin (ℓ + 1), ShiftFailZ pk i.val z] ≤
      (ℓ + 1) * sfailEps (qP qA QT ℓ) (eP lr qE ℓ) (nP nA QT ℓ) := by
  classical
  set q := qP qA QT ℓ
  set e := eP lr qE ℓ
  set n := nP nA QT ℓ
  refine (prEvent_bind_le_sum_of_table ($ᵗ CTable) _ (Finset.univ : Finset (Fin (ℓ + 1) × Fin 4))
    (fun ij E => withLogQ (gameDP lr E pk pre A Lst ij.1.val)) _
    (fun ij E o => evJS E lr pk ij.2.val o) fun E g h => ?_).trans ?_
  · obtain ⟨i, hi⟩ := h
    have hev := shiftFail_events g E pk lr pre A Lst ℓ i.val hd hi
    simp only [evalWithAnswerFn_withLogQ]
    rcases hev with h0 | h1 | h2 | ⟨e', he', hb⟩
    · exact ⟨(i, 0), mem_univ _, h0⟩
    · exact ⟨(i, 1), mem_univ _, h1⟩
    · exact ⟨(i, 2), mem_univ _, h2⟩
    · refine ⟨(i, 3), mem_univ _, e', he', ?_⟩
      have hea : e' = ⟨e'.1, g e'.1⟩ := tableQueryLog_answer _ g e' he'
      have hans : (e'.2 : Ans e'.1).ba = (g e'.1).ba := by rw [hea]
      rcases hb with hb | ⟨hk, hb⟩
      · left; rw [hans]; exact hb
      · right; exact ⟨hk, by rw [hans]; exact hb⟩
  · rw [Fintype.sum_prod_type]
    refine le_trans (Finset.sum_le_sum (g := fun _ => sfailEps q e n) fun i _ => ?_) (by simp)
    have hb := proverP_bounds lr pre pk hA Lst (Nat.lt_succ_iff.1 i.isLt)
    set P := proverP lr pk pre A Lst i.val with hP
    have t0 : Pr{let E ← $ᵗ CTable; let o ← (simulateQ randomOracle
        (withLogQ (gameA CrtGen.tables (stG lr pk) P E))).run' ∅}[evJS E lr pk 0 o] ≤ someEps q e n := by
      refine (prEvent_withLogQ_le ($ᵗ CTable) (fun E => gameA CrtGen.tables (stG lr pk) P E)
        (fun E r => r.2.2.accept = true ∧
          ¬SomeExtracted E (stG lr pk (stOut r)) (witKT pk hG (some (stOut r))) r)).trans ?_
      exact pomfritT_accept_le_some pk hG (fun s => s.2.1) (fun s => s.2.2) lr P e hb.2.2 n hb.2.1 q
        hb.1
    have t1 : Pr{let E ← $ᵗ CTable; let o ← (simulateQ randomOracle
        (withLogQ (gameA CrtGen.tables (stG lr pk) P E))).run' ∅}[evJS E lr pk 1 o] ≤
        ((e * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
      refine (prEvent_withLogQ_le ($ᵗ CTable) (fun E => gameA CrtGen.tables (stG lr pk) P E)
        (fun E r => PostOut E r)).trans ?_
      exact prEvent_joint_postOut_le_A CrtGen.tables (stG lr pk) P e hb.2.2 q hb.1
    have t2 : Pr{let E ← $ᵗ CTable; let o ← (simulateQ randomOracle
        (withLogQ (gameA CrtGen.tables (stG lr pk) P E))).run' ∅}[evJS E lr pk 2 o] ≤
        (2 ^ 128 : ℝ≥0∞)⁻¹ := by
      refine (prEvent_withLogQ_le ($ᵗ CTable) (fun E => gameA CrtGen.tables (stG lr pk) P E)
        (fun E r => r.2.2.accept = true ∧
          ((.h23, zOut (stG lr pk (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2)).trans ?_
      exact prEvent_joint_le_of_forall (fun E => (simulateQ randomOracle
        (gameA CrtGen.tables (stG lr pk) P E)).run' ∅) _ fun E =>
        prEvent_zUnqueried_le_A CrtGen.tables (stG lr pk) P E
    have t3 : Pr{let E ← $ᵗ CTable; let o ← (simulateQ randomOracle
        (withLogQ (gameA CrtGen.tables (stG lr pk) P E))).run' ∅}[evJS E lr pk 3 o] ≤
        ∑ k ∈ hitKinds, (q + extractorQueries + verifierQueries) k *
          (hitEps (q + extractorQueries + verifierQueries)
            (combCount cbP (q + extractorQueries + verifierQueries)) k +
            orderEps (q + extractorQueries + verifierQueries) k) :=
      prEvent_joint_le_of_forall (fun E => (simulateQ randomOracle
        (withLogQ (gameA CrtGen.tables (stG lr pk) P E))).run' ∅) (fun E o => evJS E lr pk 3 o) fun E =>
        prEvent_hitOrder_le _ _ (isKindQueryBound_gameA CrtGen.tables (stG lr pk) P E hb.1)
    rw [Fin.sum_univ_four]
    exact add_le_add (add_le_add (add_le_add t0 t1) t2) t3

end Fixed

/-! ## U2's term in the one-more game -/

section Game

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (lr : Bool) (A : Forger)

/-- **U2's term, bounded** (`pomfrit.md` §6.2, §6.4, G8): in PomFRIT's one-more game with U2's
shift rule (`hintS`: the alive trees' prefixes), for a key generation whose public keys have 32-byte digests and a forger with budget
`qA`, `nA`, `qE`, `Q_T`, some forgery `i ≤ ℓ` is accepted with a claim that is a preimage of none of its
shifted targets with probability at most `(ℓ + 1)·sfailEps`, for any number `n` of targets. -/
theorem prEvent_shiftFail_le (n ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) :
    Pr{let r ← game KG pre n ℓ CrtGen.tables lr A noHint (hintS lr) tgts2}[
        ∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val r] ≤
      (ℓ + 1) * sfailEps (qP qA QT ℓ) (eP lr qE ℓ) (nP nA QT ℓ) := by
  unfold game omuf advC
  simp only [bind_assoc, pure_bind]
  apply prEvent_bind_le_of_forall_le_of_support KG _ (fun r => ∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val r)
  intro kp hkp
  rw [eqd_swap ($ᵗ CTable) (unifList TG n) (fun E L => (do
    let r ← (simulateQ (realImpl noHint (pre kp.2))
      (Acomp CrtGen.tables lr E (hintS lr E) tgts2 kp.1 ℓ A)).run (fun _ => none, ch0 L)
    pure (kp.1, r.1, r.2))) (fun r => ∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val r)]
  apply prEvent_bind_le_of_forall_le _ _ (fun r => ∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val r)
  intro L
  refine le_trans (le_of_eq ?_) (prEvent_shiftFailZ_le lr kp.1 (pre kp.2) A L ℓ (hdig kp hkp) hA)
  have key : ∀ E : CTable, (simulateQ (realImpl noHint (pre kp.2))
      (Acomp CrtGen.tables lr E (hintS lr E) tgts2 kp.1 ℓ A)).run (fun _ => none, ch0 L) =
      (fun z => (z.1.1, (z.1.2.1, chOf z.1.2.2 z.2))) <$>
        (simulateQ randomOracle ((simulateQ (htW (AR := Ans) noHint (pre kp.2))
          (Acomp CrtGen.tables lr E (hintS lr E) tgts2 kp.1 ℓ A)).run (hs0G L))).run ∅ := fun E =>
    realImpl_run_eq noHint (pre kp.2) _ (fun _ => none) (ch0 L)
  simp only [key, StateT.run'_eq, map_bind, Functor.map_map, bind_pure_comp]
  have hev : ∀ a : ((List (ByteArray × SIss) × Bool) × HTSG (List TG)) × (specR Ans).QueryCache,
      (∃ i : Fin (ℓ + 1), ShiftFail BAVC.tau i.val (kp.1, a.1.1, a.1.2.1, chOf a.1.2.2 a.2)) =
        (∃ i : Fin (ℓ + 1), ShiftFailZ kp.1 i.val a.1) := fun a => rfl
  simp only [hev]

/-- **Theorem U2 with every term explicit** (`pomfrit.md` §6.2, §6.4; G8 closed for U2): for a
key generation with 32-byte key digests, any Issuer and a forger with budget `qA` (hash queries per
kind), `nA` (hash queries), `qE` (cipher queries), `Q_T` (`hash_to_target` queries), with U2's
shift rule (`hintS`: the prefixes of all alive trees, at most `τ = 17`) as the reduction's hint,

    Pr[PomWin] ≤ Adv^{ompr⊕17}(red …; Q_T + ℓ + 1, ℓ) + (ℓ + 1)·sfailEps(q', q_E', n'),

with the derived provers' budgets `q'`, `q_E'`, `n'` (`qP`, `eP`, `nP`) as in `pomfrit_U1_explicit`.
`sfailEps` is `pfailEps` with Lemma P's `2⁻⁷¹` per `H₂³` query replaced by `2·2⁻¹²⁸`. -/
theorem pomfrit_U2_explicit (ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A noHint (hintS lr) tgts2}[
        PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre (QT + (ℓ + 1))
          (red noHint (advC ℓ CrtGen.tables lr A (hintS lr) tgts2))}[
        Wins ℓ (goodShift BAVC.tau relP) r.1 r.2.1 r.2.2] +
      (ℓ + 1) * sfailEps (qP qA QT ℓ) (eP lr qE ℓ) (nP nA QT ℓ) :=
  (pomfrit_U2_bound KG pre ℓ QT CrtGen.tables lr A BAVC.tau (shP lr) hA.ht).trans
    (add_le_add le_rfl (prEvent_shiftFail_le KG pre lr A _ ℓ hdig hA))

end Game

end VoleMole.ROM.OneMore.Pomfrit
