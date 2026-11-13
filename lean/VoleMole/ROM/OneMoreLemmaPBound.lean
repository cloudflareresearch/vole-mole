import VoleMole.ROM.OneMoreLemmaPFail

/-!
# Lemma P's term in the one-more game, bounded (gap G8)

`lean/docs/security/pomfrit.md` §6.4. This file bounds `Pr[∃ i ≤ ℓ, PFail i]` in PomFRIT's one-more
game with Lemma P's `E₁` (`e1P`), every term explicit, and plugs it into Theorem U1.

* **Logged computations** (`withLogQ`): a computation returning its own query log, so that the hits
  of `pfail_events` (events of the table and the log) are events of an output.
* **The hit and order-hit union bound** (`prEvent_hitOrder_le`): a chain hit or an order hit among
  the queries of a computation with `n k` queries of kind `k` has probability at most
  `Σ_k n k · (hitEps n … k + orderEps n k)`, with `orderEps n .h21 = n .h3 / 2^1088`.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM

open VoleMole.Prob VoleMole.Verifier

/-! ## A computation with its query log -/

section WithLog

variable {α : Type}

/-- **A computation returning its query log** (against a table, the log of `tableQueryLog`). -/
def withLogQ (oa : OracleComp spec α) : OracleComp spec (α × QueryLog spec) :=
  OracleComp.construct (C := fun _ => OracleComp spec (α × QueryLog spec))
    (fun a => pure (a, []))
    (fun t _ rec => liftM (spec.query t) >>= fun u => (fun r => (r.1, ⟨t, u⟩ :: r.2)) <$> rec u) oa

@[simp] lemma withLogQ_pure (a : α) : withLogQ (pure a : OracleComp spec α) = pure (a, []) := rfl

lemma withLogQ_query_bind (t : Dom) (k : Ans t → OracleComp spec α) :
    withLogQ (liftM (spec.query t) >>= k) =
      liftM (spec.query t) >>= fun u => (fun r => (r.1, ⟨t, u⟩ :: r.2)) <$> withLogQ (k u) := rfl

/-- Per table, the logged computation returns the output and the log. -/
theorem evalWithAnswerFn_withLogQ (g : Table) (oa : OracleComp spec α) :
    evalWithAnswerFn (QueryImpl.ofFn g) (withLogQ oa) =
      (evalWithAnswerFn (QueryImpl.ofFn g) oa, tableQueryLog oa g) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [withLogQ_query_bind]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_map, evalWithAnswerFn_liftM_query,
      QueryImpl.ofFn_apply, tableQueryLog_query_bind]
    rw [ih (g t)]

theorem tableQueryLog_withLogQ (g : Table) (oa : OracleComp spec α) :
    tableQueryLog (withLogQ oa) g = tableQueryLog oa g := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [withLogQ_query_bind, tableQueryLog_query_bind, tableQueryLog_query_bind,
      IC.tableQueryLog_map', ih (g t)]

theorem isKindQueryBound_withLogQ {oa : OracleComp spec α} {q : Kind → ℕ}
    (h : IsKindQueryBound oa q) : IsKindQueryBound (withLogQ oa) q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isKindQueryBound_query_bind_iff] at h
    rw [withLogQ_query_bind, isKindQueryBound_query_bind_iff]
    exact ⟨h.1, fun u => (isQueryBound_map_iff _ _ _ _ _).2 (ih u (h.2 u))⟩

end WithLog

end VoleMole.ROM

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC

/-! ## Chain hits and order hits, union bound -/

section HitOrder

variable {α : Type}

/-- **A chain hit or an order hit** in a logged output: a logged answer that is a target of the
log before it (`hitTargets`), or an `H₂¹` answer that is the `chal1` field of an earlier marker
query `H₃(x)`. -/
def HitOut (o : α × QueryLog spec) : Prop :=
  ∃ e ∈ o.2, (e.2 : Ans e.1).ba ∈ hitTargets cbP (logBefore e.1 o.2) e.1.1 ∨
    (e.1.1 = .h21 ∧ (e.2 : Ans e.1).ba ∈ (kindIns .h3 ((logBefore e.1 o.2).map Sigma.fst)).map xChal1)

/-- The per-query bound of an order hit: `n₃ / 2¹⁰⁸⁸` for an `H₂¹` query. -/
noncomputable def orderEps (n : Kind → ℕ) : Kind → ℝ≥0∞ := fun k =>
  if k = .h21 then (n .h3 : ℝ≥0∞) / 2 ^ 1088 else 0

lemma prEvent_orderHitL_le (oa : OracleComp spec α) (n : Kind → ℕ) (hn : IsKindQueryBound oa n)
    (t : Dom) (g : Table) :
    Pr{let u ← $ᵗ (Ans t)}[orderHitL (tableQueryLog oa) t (Function.update g t u)] ≤
      orderEps n t.1 := by
  have h : ∀ u : Ans t, orderHitL (tableQueryLog oa) t (Function.update g t u) ↔
      t.1 = .h21 ∧ u.ba ∈ (kindIns .h3 ((logBefore t (tableQueryLog oa g)).map Sigma.fst)).map
        xChal1 := fun u => by
    simp only [orderHitL, Function.update_self, logBefore_tableQueryLog_update]
  simp_rw [h]
  unfold orderEps
  split_ifs with ht
  · simp only [ht, true_and]
    refine (prEvent_ba_mem_le t.1.outLen _).trans ?_
    rw [ht]
    have hl : ((kindIns .h3 ((logBefore t (tableQueryLog oa g)).map Sigma.fst)).map xChal1).length
        ≤ n .h3 := by
      rw [List.length_map]
      exact (length_kindIns_le_of_sublist ((logBefore_sublist _ _).map _)).trans
        (length_kindIns_tableQueryLog_le _ hn g .h3)
    have h8 : (2 : ℝ≥0∞) ^ (8 * Kind.h21.outLen) = 2 ^ 1088 := by norm_num [Kind.outLen]
    rw [h8]
    exact ENNReal.div_le_div_right (by exact_mod_cast hl) _
  · simp only [ht, false_and]
    rw [prEvent_false]

/-- **The union bound for chain hits and order hits** among the queries of a computation with
`n k` queries of kind `k`. -/
theorem prEvent_hitOrder_le (oa : OracleComp spec α) (n : Kind → ℕ) (hn : IsKindQueryBound oa n) :
    Pr{let o ← (simulateQ randomOracle (withLogQ oa)).run' ∅}[HitOut o] ≤
      ∑ k ∈ hitKinds, n k * (hitEps n (combCount cbP n) k + orderEps n k) := by
  refine prEvent_exists_bad_query_le (withLogQ oa) n (isKindQueryBound_withLogQ hn) HitOut
    (fun t g => chainHitL cbP (tableQueryLog oa) t g ∨ orderHitL (tableQueryLog oa) t g)
    hitKinds (fun k => hitEps n (combCount cbP n) k + orderEps n k) (fun k hk => ?_)
    (fun t g => ?_) (fun g hg => ?_)
  · rw [hitEps_eq_zero n _ k hk, zero_add]
    unfold orderEps
    rw [ite_eq_right (fun h => hk (by rw [h]; simp [hitKinds]))]
  · exact (prEvent_or_le _ _ _).trans (add_le_add (prEvent_chainHitL_le cbP oa n hn t g)
      (prEvent_orderHitL_le oa n hn t g))
  · rw [evalWithAnswerFn_withLogQ] at hg
    obtain ⟨e, he, hb⟩ := hg
    refine ⟨e, by rw [tableQueryLog_withLogQ]; exact he, ?_⟩
    have hea : e = ⟨e.1, g e.1⟩ := tableQueryLog_answer oa g e he
    have hans : (e.2 : Ans e.1).ba = (g e.1).ba := by rw [hea]
    rcases hb with hb | ⟨hk, hb⟩
    · left; show (g e.1).ba ∈ _; rw [← hans]; exact hb
    · right; refine ⟨hk, ?_⟩; show (g e.1).ba ∈ _; rw [← hans]; exact hb

end HitOrder

/-! ## The bound for fixed key and target stream -/

section Fixed

/-- An event of a logged output's first component has at most the probability of the event of the
computation. -/
lemma prEvent_withLogQ_le {X α : Type} (mT : ProbComp X) (oa : X → OracleComp spec α)
    (Q : X → α → Prop) :
    Pr{let E ← mT; let o ← (simulateQ randomOracle (withLogQ (oa E))).run' ∅}[Q E o.1] ≤
      Pr{let E ← mT; let r ← (simulateQ randomOracle (oa E)).run' ∅}[Q E r] := by
  refine (prEvent_bind_le_sum_of_table mT (fun E => withLogQ (oa E)) (Finset.univ : Finset Unit)
    (fun _ E => oa E) (fun E o => Q E o.1) (fun _ E r => Q E r) fun E g h => ⟨(), mem_univ _, ?_⟩).trans
    (by simp)
  rwa [evalWithAnswerFn_withLogQ] at h

/-- A bound for every cipher table bounds the joint experiment. -/
lemma prEvent_joint_le_of_forall {X : Type} (m : CTable → ProbComp X) (p : CTable → X → Prop)
    {ε : ℝ≥0∞} (h : ∀ E, Pr{let r ← m E}[p E r] ≤ ε) :
    Pr{let E ← $ᵗ CTable; let r ← m E}[p E r] ≤ ε := by
  let : MeasurableSpace CTable := ⊤
  rw [prEvent_bind_of_discrete]
  calc ∫⁻ E, Pr{let r ← m E}[p E r] ∂𝒟[$ᵗ CTable] ≤ ∫⁻ _, ε ∂𝒟[$ᵗ CTable] := MeasureTheory.lintegral_mono h
    _ = ε * 𝒟[$ᵗ CTable] Set.univ := MeasureTheory.lintegral_const ε
    _ ≤ ε := mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)

/-- **Lemma P's extraction term** (`pomfritT_accept_le_major`'s bound) for a prover with `q k` hash
queries of kind `k`, `n` hash queries in all and `qE` cipher queries. -/
noncomputable def majEps (q : Kind → ℕ) (qE n : ℕ) : ℝ≥0∞ :=
  (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((2 ^ 57 : ℝ≥0∞) / 2 ^ 128) +
    (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
    (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    chainHitEpsComb q 45 + stmtBindEpsD q

/-- **Lemma P's failure per forgery**, every term explicit, for derived provers with `q`, `n`, `qE`
queries: the extraction term, Post (`1024·q_E·q₁·2⁻²⁵⁶`), the verifier's `H₂³` input unqueried
(`2⁻¹²⁸`), and the chain hits and order hits of the derived game (`n''` its queries per kind). -/
noncomputable def pfailEps (q : Kind → ℕ) (qE n : ℕ) : ℝ≥0∞ :=
  majEps q qE n + ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    (2 ^ 128 : ℝ≥0∞)⁻¹ +
    ∑ k ∈ hitKinds, (q + extractorQueries + verifierQueries) k *
      (hitEps (q + extractorQueries + verifierQueries)
        (combCount cbP (q + extractorQueries + verifierQueries)) k +
        orderEps (q + extractorQueries + verifierQueries) k)

/-- The four events of `pfail_events`, on the logged output of the derived game. -/
def evJ (E : CTable) (lr : Bool) (pk : UovPk) :
    ℕ → Out (((TG × ByteArray × ByteArray) × AuxP) × QueryLog specIC) × QueryLog spec → Prop
  | 0, o => o.1.2.2.accept = true ∧ ¬MajorExtracted E (stG lr pk (stOut o.1))
      (witKT pk hG (some (stOut o.1))) o.1
  | 1, o => PostOut E o.1
  | 2, o => o.1.2.2.accept = true ∧
      ((.h23, zOut (stG lr pk (stOut o.1)) o.1) : Dom) ∉ hashLog o.1.2.1.aux.2
  | _, o => HitOut o

lemma stG_eq_stT (lr : Bool) (pk : UovPk) :
    stG lr pk = stT pk hG (fun s : TG × ByteArray × ByteArray => s.2.1) (fun s => s.2.2) lr := rfl

variable (lr : Bool) (pk : UovPk) (pre : TG → SIss) (A : Forger) (Lst : List TG) (ℓ : ℕ)

/-- **Lemma P's term for a fixed key and target stream**: over the cipher table and the hash
table, some forgery fails with probability at most `(ℓ + 1)·pfailEps`. -/
theorem prEvent_pfailZ_le (hd : pk.digest.size = 32) {qA : Kind → ℕ} {nA qE QT : ℕ}
    (hA : ForgerBound A qA nA qE QT) :
    Pr{let E ← $ᵗ CTable; let z ← (simulateQ randomOracle ((simulateQ (htW (AR := Ans) addHint pre)
        (Acomp CrtGen.tables lr E (e1P lr E) tgts1 pk ℓ A)).run (hs0 Lst))).run' ∅}[
        ∃ i : Fin (ℓ + 1), PFailZ pk i.val z] ≤
      (ℓ + 1) * pfailEps (qP qA QT ℓ) (eP lr qE ℓ) (nP nA QT ℓ) := by
  classical
  set q := qP qA QT ℓ
  set e := eP lr qE ℓ
  set n := nP nA QT ℓ
  refine (prEvent_bind_le_sum_of_table ($ᵗ CTable) _ (Finset.univ : Finset (Fin (ℓ + 1) × Fin 4))
    (fun ij E => withLogQ (gameP lr E pk pre A Lst ij.1.val)) _
    (fun ij E o => evJ E lr pk ij.2.val o) fun E g h => ?_).trans ?_
  · obtain ⟨i, hi⟩ := h
    have hev := pfail_events g lr E pk pre A Lst ℓ i.val hd hi
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
    refine le_trans (Finset.sum_le_sum (g := fun _ => pfailEps q e n) fun i _ => ?_) (by simp)
    have hb := proverP_bounds lr pre pk hA Lst (Nat.lt_succ_iff.1 i.isLt)
    set P := proverP lr pk pre A Lst i.val with hP
    have t0 : Pr{let E ← $ᵗ CTable; let o ← (simulateQ randomOracle
        (withLogQ (gameA CrtGen.tables (stG lr pk) P E))).run' ∅}[evJ E lr pk 0 o] ≤ majEps q e n := by
      refine (prEvent_withLogQ_le ($ᵗ CTable) (fun E => gameA CrtGen.tables (stG lr pk) P E)
        (fun E r => r.2.2.accept = true ∧
          ¬MajorExtracted E (stG lr pk (stOut r)) (witKT pk hG (some (stOut r))) r)).trans ?_
      exact pomfritT_accept_le_major pk hG (fun s => s.2.1) (fun s => s.2.2) lr P e hb.2.2 n hb.2.1 q
        hb.1
    have t1 : Pr{let E ← $ᵗ CTable; let o ← (simulateQ randomOracle
        (withLogQ (gameA CrtGen.tables (stG lr pk) P E))).run' ∅}[evJ E lr pk 1 o] ≤
        ((e * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
      refine (prEvent_withLogQ_le ($ᵗ CTable) (fun E => gameA CrtGen.tables (stG lr pk) P E)
        (fun E r => PostOut E r)).trans ?_
      exact prEvent_joint_postOut_le_A CrtGen.tables (stG lr pk) P e hb.2.2 q hb.1
    have t2 : Pr{let E ← $ᵗ CTable; let o ← (simulateQ randomOracle
        (withLogQ (gameA CrtGen.tables (stG lr pk) P E))).run' ∅}[evJ E lr pk 2 o] ≤
        (2 ^ 128 : ℝ≥0∞)⁻¹ := by
      refine (prEvent_withLogQ_le ($ᵗ CTable) (fun E => gameA CrtGen.tables (stG lr pk) P E)
        (fun E r => r.2.2.accept = true ∧
          ((.h23, zOut (stG lr pk (stOut r)) r) : Dom) ∉ hashLog r.2.1.aux.2)).trans ?_
      exact prEvent_joint_le_of_forall (fun E => (simulateQ randomOracle
        (gameA CrtGen.tables (stG lr pk) P E)).run' ∅) _ fun E =>
        prEvent_zUnqueried_le_A CrtGen.tables (stG lr pk) P E
    have t3 : Pr{let E ← $ᵗ CTable; let o ← (simulateQ randomOracle
        (withLogQ (gameA CrtGen.tables (stG lr pk) P E))).run' ∅}[evJ E lr pk 3 o] ≤
        ∑ k ∈ hitKinds, (q + extractorQueries + verifierQueries) k *
          (hitEps (q + extractorQueries + verifierQueries)
            (combCount cbP (q + extractorQueries + verifierQueries)) k +
            orderEps (q + extractorQueries + verifierQueries) k) :=
      prEvent_joint_le_of_forall (fun E => (simulateQ randomOracle
        (withLogQ (gameA CrtGen.tables (stG lr pk) P E))).run' ∅) (fun E o => evJ E lr pk 3 o) fun E =>
        prEvent_hitOrder_le _ _ (isKindQueryBound_gameA CrtGen.tables (stG lr pk) P E hb.1)
    rw [Fin.sum_univ_four]
    exact add_le_add (add_le_add (add_le_add t0 t1) t2) t3

end Fixed

/-! ## Lemma P's term in the one-more game -/

section Game

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (lr : Bool) (A : Forger)

/-- **Lemma P's term, bounded** (`pomfrit.md` §6.4, G8): in PomFRIT's one-more game with Lemma P's
`E₁` (`e1P`), for a key generation whose public keys have 32-byte digests and a forger with budget
`qA`, `nA`, `qE`, `Q_T`, some forgery `i ≤ ℓ` is accepted with a claim that is not a preimage of its
programmed target with probability at most `(ℓ + 1)·pfailEps`, for any number `n` of targets. -/
theorem prEvent_pfail_le (n ℓ : ℕ) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) :
    Pr{let r ← game KG pre n ℓ CrtGen.tables lr A addHint (e1P lr) tgts1}[
        ∃ i : Fin (ℓ + 1), PFail i.val r] ≤
      (ℓ + 1) * pfailEps (qP qA QT ℓ) (eP lr qE ℓ) (nP nA QT ℓ) := by
  unfold game omuf advC
  simp only [bind_assoc, pure_bind]
  apply prEvent_bind_le_of_forall_le_of_support KG _ (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)
  intro kp hkp
  rw [eqd_swap ($ᵗ CTable) (unifList TG n) (fun E L => (do
    let r ← (simulateQ (realImpl addHint (pre kp.2))
      (Acomp CrtGen.tables lr E (e1P lr E) tgts1 kp.1 ℓ A)).run (fun _ => none, ch0 L)
    pure (kp.1, r.1, r.2))) (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)]
  apply prEvent_bind_le_of_forall_le _ _ (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)
  intro L
  refine le_trans (le_of_eq ?_) (prEvent_pfailZ_le lr kp.1 (pre kp.2) A L ℓ (hdig kp hkp) hA)
  have key : ∀ E : CTable, (simulateQ (realImpl addHint (pre kp.2))
      (Acomp CrtGen.tables lr E (e1P lr E) tgts1 kp.1 ℓ A)).run (fun _ => none, ch0 L) =
      (fun z => (z.1.1, (z.1.2.1, chOf z.1.2.2 z.2))) <$>
        (simulateQ randomOracle ((simulateQ (htW (AR := Ans) addHint (pre kp.2))
          (Acomp CrtGen.tables lr E (e1P lr E) tgts1 kp.1 ℓ A)).run (hs0 L))).run ∅ := fun E =>
    realImpl_run_eq addHint (pre kp.2) _ (fun _ => none) (ch0 L)
  simp only [key, StateT.run'_eq, map_bind, Functor.map_map, bind_pure_comp]
  have hev : ∀ a : ((List (ByteArray × SIss) × Bool) × HTS) × (specR Ans).QueryCache,
      (∃ i : Fin (ℓ + 1), PFail i.val (kp.1, a.1.1, a.1.2.1, chOf a.1.2.2 a.2)) =
        (∃ i : Fin (ℓ + 1), PFailZ kp.1 i.val a.1) := fun a => rfl
  simp only [hev]

end Game

end VoleMole.ROM.OneMore.Pomfrit
