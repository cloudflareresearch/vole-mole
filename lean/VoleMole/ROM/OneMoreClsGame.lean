import VoleMole.ROM.OneMoreClsBound

/-!
# Theorem U1^cls in the one-more game

`lean/docs/security/pomfrit.md` §6.4 (gap G8-cls). The reduction of U1^cls runs the forger wrapped
(`wrapE`, reading the cipher table that the reduction samples) with the hint `E₁^cls` (`e1C`).

* **The game with a forger that depends on the cipher table** (`advCE`, `gameE`) and U1's reduction
  for it (`pomfrit_U1_boundE`, `pomWin_forgesE`): `pomfrit_U1_bound` with `A` replaced by `AE E`.
* **The wrapper does not change the win** (`pomWin_le_wrapE`): table by table the wrapped forger
  outputs the same forgeries, the target oracle gives the same answers and the Issuer is asked as
  often (`eval_wrapE`), so the verifications accept the same forgeries (`verAll_flags_sameG`).
* `prEvent_clsFail_le`: U1^cls's term in the game.

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.ZK.Sim VoleMole.Verifier.Bridge

/-! ## The verifications accept the same forgeries for states with the same answers -/

section Flags

variable (g : Table) (T : CrtTables) (lr : Bool) (E : CTable) (φ : TG → TG ≃ TG)
  (hint : QueryLog specIC → ByteArray → TG) (tgts : TG × TG → List TG) (pk : UovPk)
  (pre : TG → SIss)

/-- **The verifications' decisions and the Issuer count read the target oracle's answers only.** -/
theorem verAll_flags_sameG (L₁ L₂ : QueryLog specIC) :
    ∀ (outs : List (ByteArray × ByteArray)) (s₁ s₂ : HTSG TG) (t : HTS), SameG s₁ t → SameG s₂ t →
      let a := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
        (verAll T lr E hint tgts pk L₁ outs)).run s₁)
      let b := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
        (verAll T lr E hint tgts pk L₂ outs)).run s₂)
      a.1.map Prod.snd = b.1.map Prod.snd ∧ a.2.2.2.2 = b.2.2.2.2
  | [], s₁, s₂, t, h₁, h₂ => by
    simp only [verAll, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure, List.map_nil,
      true_and]
    exact h₁.2.2.trans h₂.2.2.symm
  | (m, sg) :: rest, s₁, s₂, t, h₁, h₂ => by
    simp only [verAll, eval_htW_bindG, simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure,
      List.map_cons]
    rw [eval_verOneG, eval_verOneG]
    split_ifs with hr
    · simp only
      obtain ⟨f1, f2⟩ := verAll_flags_sameG L₁ L₂ rest s₁ s₂ t h₁ h₂
      exact ⟨by rw [f1], f2⟩
    · cases c1T g lr E pk sg with
      | none =>
        simp only
        obtain ⟨f1, f2⟩ := verAll_flags_sameG L₁ L₂ rest s₁ s₂ t h₁ h₂
        exact ⟨by rw [f1], f2⟩
      | some c1 =>
        simp only
        set x := tgtIn pk lr sg m c1
        obtain ⟨a1, a2⟩ := tStep_sameG φ h₁ x (hint (L₁ ++ axT g lr L₁ x) x) 0
        obtain ⟨b1, b2⟩ := tStep_sameG φ h₂ x (hint (L₂ ++ axT g lr L₂ x) x) 0
        obtain ⟨f1, f2⟩ := verAll_flags_sameG L₁ L₂ rest _ _ _ a2 b2
        refine ⟨?_, f2⟩
        rw [f1, a1, b1]

/-- **The wrapped forger wins exactly when the forger does, table by table**: the same flag and
Issuer count in the game with any hint rule. -/
theorem flag_wrapE (A : Forger) (ℓ : ℕ) (Lst : List TG) :
    let zA := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (Acomp T lr E hint tgts pk ℓ A)).run (hs0G Lst))
    let zW := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
      (Acomp T lr E hint tgts pk ℓ (wrapE lr E A))).run (hs0G Lst))
    zA.1.2 = zW.1.2 ∧ zA.2.2.2.2 = zW.2.2.2.2 := by
  obtain ⟨a1, a2, a3⟩ := eval_forgerG g E lr φ hint pre (A pk) [] (hs0G Lst) (hs0 Lst)
    (fun _ => none) (InvG.init hint Lst)
  obtain ⟨c1, c2, c3⟩ := eval_forgerG g E lr φ hint pre (wrapE lr E A pk) [] (hs0G Lst) (hs0 Lst)
    (fun _ => none) (InvG.init hint Lst)
  obtain ⟨w1, w2, -, -⟩ := eval_wrapE g E lr pre A pk (hs0 Lst)
  simp only [Acomp]
  rw [eval_htW_bindG, eval_htW_bindG]
  set fA := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
    ((simulateQ (wrapImpl lr E hint) (A pk)).run [])).run (hs0G Lst))
  set fW := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss) φ pre)
    ((simulateQ (wrapImpl lr E hint) (wrapE lr E A pk)).run [])).run (hs0G Lst))
  have ho : fA.1.1 = fW.1.1 := by rw [a1, c1, w1]
  have hsA : SameG fA.2 _ := a3.1
  have hsW : SameG fW.2 _ := c3.1
  rw [w2] at hsW
  rw [← ho]
  split_ifs with hlen
  · rw [eval_htW_bindG, eval_htW_bindG]
    simp only [simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure]
    obtain ⟨f1, f2⟩ := verAll_flags_sameG g T lr E φ hint tgts pk pre fA.1.2 fW.1.2 fA.1.1 _ _ _
      hsA hsW
    refine ⟨?_, f2⟩
    have hall : ∀ (l : List ((ByteArray × SIss) × Bool)), (∀ v ∈ l, v.2 = true) ↔
        ∀ b ∈ l.map Prod.snd, b = true := fun l => by simp
    simp only [hall, f1]
  · simp only [simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure, true_and]
    exact hsA.2.2.trans hsW.2.2.symm

end Flags

/-! ## The game with a forger that reads the cipher table -/

section GameE

variable {K : Type} (KG : ProbComp (UovPk × K)) (pre : K → TG → SIss) (n ℓ : ℕ) (T : CrtTables)
  (lr : Bool)

/-- The composed adversary for a forger `AE E` that depends on the cipher table. -/
noncomputable def advCE {Hn : Type} (AE : CTable → Forger)
    (hint : CTable → QueryLog specIC → ByteArray → Hn) (tgts : TG × Hn → List TG) (pk : UovPk) :
    ProbComp (OracleComp (specC Hn) (List (ByteArray × SIss) × Bool)) := do
  let E ← $ᵗ CTable
  pure (Acomp T lr E (hint E) tgts pk ℓ (AE E))

/-- **The one-more game with a forger that depends on the cipher table** (`game` with `AE E`). -/
noncomputable def gameE {Hn : Type} (AE : CTable → Forger) (φ : Hn → TG ≃ TG)
    (hint : CTable → QueryLog specIC → ByteArray → Hn) (tgts : TG × Hn → List TG) :=
  omuf KG pre n φ (advCE ℓ T lr AE hint tgts)

set_option linter.constructorNameAsVariable false in
lemma pomWin_forgesE {Hn : Type} (AE : CTable → Forger) (φ : Hn → TG ≃ TG)
    (hint : CTable → QueryLog specIC → ByteArray → Hn) (tgts : TG × Hn → List TG)
    {r : UovPk × (List (ByteArray × SIss) × Bool) × (ByteArray → Option (TG × Hn)) ×
      Ch Ans ByteArray Hn TG} (hr : r ∈ support (gameE KG pre n ℓ T lr AE φ hint tgts))
    (hw : PomWin ℓ r) : Forges ℓ r.2.1 r.2.2.2 := by
  simp only [gameE, omuf, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨kp, -, a, ha, L, -, r', hr', rfl⟩ := hr
  simp only [advCE, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ha
  obtain ⟨E, -, rfl⟩ := ha
  have h1 : r'.1 ∈ support (Acomp T lr E (hint E) tgts kp.1 ℓ (AE E)) := by
    refine support_simulateQ_run'_subset (realImpl φ (pre kp.2))
      (Acomp T lr E (hint E) tgts kp.1 ℓ (AE E)) (fun _ => none, ch0 L) ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨r', hr', rfl⟩
  obtain ⟨hlen, hnd⟩ := acomp_support T lr E (hint E) tgts kp.1 ℓ (AE E) h1 hw.1
  exact ⟨hw.1, hlen, hnd, hw.2⟩

set_option linter.constructorNameAsVariable false in
lemma advCE_bound {Hn : Type} (QT : ℕ) (AE : CTable → Forger)
    (hint : CTable → QueryLog specIC → ByteArray → Hn) (tgts : TG × Hn → List TG)
    (hA : ∀ E pk, IsQueryBoundP (AE E pk) (fun q => isHT q = true) QT)
    (pk : UovPk) : ∀ a ∈ support (advCE ℓ T lr AE hint tgts pk),
      IsQueryBoundP a (fun q => isTgt q = true) (QT + (ℓ + 1)) := by
  intro a ha
  simp only [advCE, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ha
  obtain ⟨E, -, rfl⟩ := ha
  exact acomp_bound (E := E) (hint := hint E) T lr tgts pk ℓ QT (AE E) (hA E pk)

set_option linter.constructorNameAsVariable false in
/-- **Theorem U1 with the forger's budget, for a forger that depends on the cipher table**
(`pomfrit_U1_bound` with `AE E`). -/
theorem pomfrit_U1_boundE (QT : ℕ) (AE : CTable → Forger)
    (e1 : CTable → QueryLog specIC → ByteArray → TG)
    (hA : ∀ E pk, IsQueryBoundP (AE E pk) (fun q => isHT q = true) QT) :
    Pr{let r ← gameE KG pre (QT + (ℓ + 1)) ℓ T lr AE addHint e1 tgts1}[PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre (QT + (ℓ + 1)) (red addHint (advCE ℓ T lr AE e1 tgts1))}[
        Wins ℓ (goodPre relP) r.1 r.2.1 r.2.2] +
      Pr{let r ← gameE KG pre (QT + (ℓ + 1)) ℓ T lr AE addHint e1 tgts1}[
        ∃ i : Fin (ℓ + 1), PFail i.val r] := by
  refine (prEvent_mono_of_support _ _ _ fun _ hr hw =>
    pomWin_forgesE KG pre _ ℓ T lr AE _ _ _ hr hw).trans ?_
  refine (omuf_le_of_bound KG pre _ ℓ addHint _ (advCE_bound ℓ T lr QT AE _ _ hA)
    (goodPre relP)).trans (add_le_add le_rfl (prEvent_mono _ _ _ fun r ⟨i, hr⟩ => ⟨i, ?_⟩))
  obtain ⟨hacc, ⟨x, σ⟩, hp, hng⟩ := hr
  refine ⟨hacc, x, σ, hp, fun ⟨a, e, hs, hrel⟩ => hng ?_⟩
  simp only [hs, Option.map_some]
  exact ⟨_, _, rfl, hrel⟩

/-- **U1^cls's term in the game** (gap G8-cls): with the wrapped forger and `E₁^cls`, for a key
generation with 32-byte key digests and any number of targets, some forgery fails with probability
at most `(ℓ + 1)·clsFailEps`. -/
theorem prEvent_clsFail_le (A : Forger) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) {Nd : ℕ}
    (hW : ∀ E, ForgerBound (wrapE lr E A) (qW qA Nd) (nW nA qA Nd) qE QT) :
    Pr{let r ← gameE KG pre n ℓ CrtGen.tables lr (fun E => wrapE lr E A) addHint (e1C lr) tgts1}[
        ∃ i : Fin (ℓ + 1), PFail i.val r] ≤
      (ℓ + 1) * clsFailEps (qP (qW qA Nd) QT ℓ) (eP lr qE ℓ) (nP (nW nA qA Nd) QT ℓ) := by
  unfold gameE omuf advCE
  simp only [bind_assoc, pure_bind]
  apply prEvent_bind_le_of_forall_le_of_support KG _ (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)
  intro kp hkp
  rw [eqd_swap ($ᵗ CTable) (unifList TG n) (fun E L => (do
    let r ← (simulateQ (realImpl addHint (pre kp.2))
      (Acomp CrtGen.tables lr E (e1C lr E) tgts1 kp.1 ℓ (wrapE lr E A))).run (fun _ => none, ch0 L)
    pure (kp.1, r.1, r.2))) (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)]
  apply prEvent_bind_le_of_forall_le _ _ (fun r => ∃ i : Fin (ℓ + 1), PFail i.val r)
  intro L
  refine le_trans (le_of_eq ?_) (prEvent_clsFailZ_le lr kp.1 (pre kp.2) A L ℓ (hdig kp hkp) hA hW)
  have key : ∀ E : CTable, (simulateQ (realImpl addHint (pre kp.2))
      (Acomp CrtGen.tables lr E (e1C lr E) tgts1 kp.1 ℓ (wrapE lr E A))).run (fun _ => none, ch0 L) =
      (fun z => (z.1.1, (z.1.2.1, chOf z.1.2.2 z.2))) <$>
        (simulateQ randomOracle ((simulateQ (htW (AR := Ans) addHint (pre kp.2))
          (Acomp CrtGen.tables lr E (e1C lr E) tgts1 kp.1 ℓ (wrapE lr E A))).run (hs0 L))).run ∅ :=
    fun E => realImpl_run_eq addHint (pre kp.2) _ (fun _ => none) (ch0 L)
  simp only [key, StateT.run'_eq, map_bind, Functor.map_map, bind_pure_comp]
  have hev : ∀ a : ((List (ByteArray × SIss) × Bool) × HTS) × (specR Ans).QueryCache,
      (∃ i : Fin (ℓ + 1), PFail i.val (kp.1, a.1.1, a.1.2.1, chOf a.1.2.2 a.2)) =
        (∃ i : Fin (ℓ + 1), PFailZ kp.1 i.val a.1) := fun a => rfl
  simp only [hev]

/-- **The wrapper does not change the forger's win** (any number of targets): the wrapped forger
of the reduction of U1^cls wins at least as often as the forger. -/
theorem pomWin_le_wrapE (A : Forger) :
    Pr{let r ← game KG pre n ℓ CrtGen.tables lr A addHint (e1C lr) tgts1}[PomWin ℓ r] ≤
      Pr{let r ← gameE KG pre n ℓ CrtGen.tables lr (fun E => wrapE lr E A) addHint
          (e1C lr) tgts1}[PomWin ℓ r] := by
  unfold game gameE omuf advC advCE
  simp only [bind_assoc, pure_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun kp => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun E => ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun L => ?_
  have key : ∀ A' : Forger, (simulateQ (realImpl addHint (pre kp.2))
      (Acomp CrtGen.tables lr E (e1C lr E) tgts1 kp.1 ℓ A')).run (fun _ => none, ch0 L) =
      (fun z => (z.1.1, (z.1.2.1, chOf z.1.2.2 z.2))) <$>
        (simulateQ randomOracle ((simulateQ (htW (AR := Ans) addHint (pre kp.2))
          (Acomp CrtGen.tables lr E (e1C lr E) tgts1 kp.1 ℓ A')).run (hs0 L))).run ∅ :=
    fun A' => realImpl_run_eq addHint (pre kp.2) _ (fun _ => none) (ch0 L)
  have h := prEvent_le_of_table
    ((simulateQ (htW (AR := Ans) addHint (pre kp.2))
      (Acomp CrtGen.tables lr E (e1C lr E) tgts1 kp.1 ℓ A)).run (hs0 L))
    ((simulateQ (htW (AR := Ans) addHint (pre kp.2))
      (Acomp CrtGen.tables lr E (e1C lr E) tgts1 kp.1 ℓ (wrapE lr E A))).run (hs0 L))
    (fun z => z.1.2 = true ∧ z.2.2.2.2 ≤ ℓ) (fun z => z.1.2 = true ∧ z.2.2.2.2 ≤ ℓ)
    fun g hz => by
      obtain ⟨f1, f2⟩ := flag_wrapE g CrtGen.tables lr E addHint (e1C lr E) tgts1 kp.1 (pre kp.2)
        A ℓ L
      exact ⟨f1 ▸ hz.1, f2 ▸ hz.2⟩
  simp only [key, StateT.run'_eq, map_bind, Functor.map_map, bind_pure_comp] at h ⊢
  exact h

/-- **Theorem U1^cls, union over the forgeries** (gap G8-cls): for a key generation with 32-byte
key digests, any Issuer and a forger `A` with budget `qA`, `nA`, `qE`, `Q_T` whose wrapped forger has
the budget `qW qA Nd`, `nW nA qA Nd`, `qE`, `Q_T` (`Nd` the wrapper's `H₅` queries per `H₂¹` query),
the forger's win probability is at most the advantage of U1's reduction run with the wrapped forger
and `E₁^cls`, plus `(ℓ + 1)·clsFailEps`. -/
theorem pomfrit_U1_cls (A : Forger) (hdig : ∀ kp ∈ support KG, kp.1.digest.size = 32)
    {qA : Kind → ℕ} {nA qE QT : ℕ} (hA : ForgerBound A qA nA qE QT) {Nd : ℕ}
    (hW : ∀ E, ForgerBound (wrapE lr E A) (qW qA Nd) (nW nA qA Nd) qE QT) :
    Pr{let r ← game KG pre (QT + (ℓ + 1)) ℓ CrtGen.tables lr A addHint (e1C lr) tgts1}[
        PomWin ℓ r] ≤
      Pr{let r ← omExp KG pre (QT + (ℓ + 1)) (red addHint
          (advCE ℓ CrtGen.tables lr (fun E => wrapE lr E A) (e1C lr) tgts1))}[
        Wins ℓ (goodPre relP) r.1 r.2.1 r.2.2] +
      (ℓ + 1) * clsFailEps (qP (qW qA Nd) QT ℓ) (eP lr qE ℓ) (nP (nW nA qA Nd) QT ℓ) :=
  (pomWin_le_wrapE KG pre _ ℓ lr A).trans ((pomfrit_U1_boundE KG pre ℓ CrtGen.tables lr QT _ (e1C lr)
    fun E => (hW E).ht).trans
    (add_le_add le_rfl (prEvent_clsFail_le KG pre _ ℓ lr A hdig hA hW)))

end GameE

end VoleMole.ROM.OneMore.Pomfrit
