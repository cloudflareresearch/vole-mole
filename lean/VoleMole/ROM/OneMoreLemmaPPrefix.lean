import VoleMole.ROM.OneMoreLemmaPFail

/-!
# The derived provers' runs are prefixes of one run

`lean/docs/security/pomfrit.md` §6.4 (gap G8, simultaneous extraction). The derived prover of the
`i`-th forgery (`proverP … i`, `ROM/OneMoreLemmaPIC.lean`) runs the forger, the earlier forgeries'
verifications up to their target queries (`verPreIC`), then the `i`-th forgery's (`verLastIC`).
`verPreIC` skips a forgery whose refresher check fails; `verLastIC` does not check the refresher.
Otherwise the two make the same queries. So where forgery `i` passes the refresher check, the joint
log of `proverP … i` is a prefix of that of `proverP … ℓ` (`jOf_proverP_prefix`), and so is its
hash log (`runE_proverP_prefix`). A failed forgery (`PFailZ`) passes it (`pfail_refresh`: the game
verified every forgery).

* `log_verPreIC_state`, `log_verPreAll_state`: the verifications' queries do not depend on the
  target oracle's state.
* `log_verPreIC_eq_last`: with the refresher check passed, `verPreIC` and `verLastIC` make the same
  queries.
* `log_verPreAll_append`, `log_contP`: the verifications' logs, concatenated.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.ZK.Sim

/-! ## The verifications' logs -/

section Logs

variable (lr : Bool) (pk : UovPk) (h : (d : DomIC) → AnsIC d)

/-- The refresher check of a signature passes. -/
def RefreshOk (sg : ByteArray) : Prop :=
  (toBA (Spec.PomFRIT.commitRefresher (toL (sB2 lr sg))) != sB1 lr sg) = false

set_option maxRecDepth 4000 in
/-- **An earlier forgery's verification makes the same queries from any state.** -/
lemma log_verPreIC_state (L : QueryLog specIC) (m sg : ByteArray) (s s' : HTS × Gh) :
    tableQueryLog (verPreIC lr pk L m sg s) h = tableQueryLog (verPreIC lr pk L m sg s') h := by
  unfold verPreIC
  split_ifs
  · simp
  · rw [tableQueryLog_bind, tableQueryLog_bind]
    cases evalWithAnswerFn (QueryImpl.ofFn h) (chal1PreIC (st0 lr pk sg) (sProof lr sg)) with
    | none => simp
    | some c1 =>
      simp only [tableQueryLog_bind, tableQueryLog_pure]

set_option maxRecDepth 4000 in
/-- **With the refresher check passed, an earlier forgery's verification makes the queries of the
last one** (`verLastIC`). -/
lemma log_verPreIC_eq_last (L : QueryLog specIC) (m sg : ByteArray) (s s' : HTS × Gh)
    (hrf : RefreshOk lr sg) :
    tableQueryLog (verPreIC lr pk L m sg s) h = tableQueryLog (verLastIC lr pk L (m, sg) s') h := by
  unfold verPreIC verLastIC
  unfold RefreshOk at hrf
  simp only [hrf, Bool.false_eq_true, ↓reduceIte]
  rw [tableQueryLog_bind, tableQueryLog_bind]
  cases evalWithAnswerFn (QueryImpl.ofFn h) (chal1PreIC (st0 lr pk sg) (sProof lr sg)) with
  | none => simp
  | some c1 =>
    simp only [tableQueryLog_bind, tableQueryLog_pure]

/-- **The earlier verifications make the same queries from any state.** -/
lemma log_verPreAll_state (L : QueryLog specIC) :
    ∀ (l : List (ByteArray × ByteArray)) (s s' : HTS × Gh),
      tableQueryLog (verPreAll lr pk L l s) h = tableQueryLog (verPreAll lr pk L l s') h
  | [], s, s' => by simp [verPreAll]
  | (m, sg) :: rest, s, s' => by
    simp only [verPreAll, tableQueryLog_bind]
    rw [log_verPreIC_state lr pk h L m sg s s', log_verPreAll_state L rest _
      (evalWithAnswerFn (QueryImpl.ofFn h) (verPreIC lr pk L m sg s'))]

/-- **The earlier verifications' log, split.** -/
lemma log_verPreAll_append (L : QueryLog specIC) :
    ∀ (l₁ l₂ : List (ByteArray × ByteArray)) (s s' : HTS × Gh),
      tableQueryLog (verPreAll lr pk L (l₁ ++ l₂) s) h =
        tableQueryLog (verPreAll lr pk L l₁ s) h ++ tableQueryLog (verPreAll lr pk L l₂ s') h
  | [], l₂, s, s' => by simp [verPreAll, log_verPreAll_state lr pk h L l₂ s s']
  | (m, sg) :: rest, l₂, s, s' => by
    simp only [List.cons_append, verPreAll, tableQueryLog_bind]
    rw [log_verPreAll_append L rest l₂ _ s', List.append_assoc]

set_option maxRecDepth 4000 in
/-- **The verification part's log**: the earlier verifications', then the last one's. -/
lemma log_contP (i : ℕ) (r : List (ByteArray × ByteArray) × QueryLog specIC × HTS × Gh)
    (s : HTS × Gh) :
    tableQueryLog (contP lr pk i r) h =
      tableQueryLog (verPreAll lr pk r.2.1 (r.1.take i) (r.2.2.1, r.2.2.2)) h ++
        tableQueryLog (verLastIC lr pk r.2.1 (r.1.getD i (ByteArray.empty, ByteArray.empty)) s) h := by
  unfold contP
  rw [tableQueryLog_bind]
  congr 1
  unfold verLastIC
  rw [tableQueryLog_bind, tableQueryLog_bind]
  cases evalWithAnswerFn (QueryImpl.ofFn h)
      (chal1PreIC (st0 lr pk (r.1.getD i (ByteArray.empty, ByteArray.empty)).2)
        (sProof lr (r.1.getD i (ByteArray.empty, ByteArray.empty)).2)) with
  | none => simp
  | some c1 => simp only [tableQueryLog_bind, tableQueryLog_pure]

set_option maxRecDepth 4000 in
/-- **The `i`-th verification part's log is a prefix of the `ℓ`-th's** (`i < ℓ`), if forgery `i`
passes the refresher check. -/
theorem log_contP_prefix (r : List (ByteArray × ByteArray) × QueryLog specIC × HTS × Gh)
    {i ℓ : ℕ} (hiℓ : i < ℓ) (hi : i < r.1.length)
    (hrf : RefreshOk lr (r.1.getD i (ByteArray.empty, ByteArray.empty)).2) :
    tableQueryLog (contP lr pk i r) h <+: tableQueryLog (contP lr pk ℓ r) h := by
  set s0 : HTS × Gh := (r.2.2.1, r.2.2.2)
  rw [log_contP lr pk h i r s0, log_contP lr pk h ℓ r s0]
  have htake : r.1.take ℓ = r.1.take i ++ (r.1[i] :: (r.1.take ℓ).drop (i + 1)) :=
    calc r.1.take ℓ = (r.1.take ℓ).take (i + 1) ++ (r.1.take ℓ).drop (i + 1) :=
          (List.take_append_drop _ _).symm
      _ = r.1.take (i + 1) ++ (r.1.take ℓ).drop (i + 1) := by
          rw [List.take_take, Nat.min_eq_left (by omega)]
      _ = _ := by
          rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
            List.append_assoc, List.singleton_append]
  have hgetD : r.1.getD i (ByteArray.empty, ByteArray.empty) = r.1[i] :=
    List.getD_eq_getElem _ _ hi
  rw [htake, log_verPreAll_append lr pk h _ _ _ _ s0]
  simp only [verPreAll, tableQueryLog_bind]
  rw [← hgetD, log_verPreIC_eq_last lr pk h r.2.1 _ _ s0 s0 hrf, List.append_assoc]
  refine (List.prefix_append_right_inj _).2 ?_
  simp only [Prod.mk.eta, List.append_assoc]
  exact List.prefix_append _ _

end Logs

/-! ## The derived provers -/

section Prover

variable (g : Table) (lr : Bool) (E : CTable) (pk : UovPk) (pre : TG → SIss) (A : Forger)
  (Lst : List TG)

/-- The forger with the void hint, at the tables `g`, `E`. -/
noncomputable abbrev forgerOut : List (ByteArray × ByteArray) × QueryLog specIC × HTS × Gh :=
  evalWithAnswerFn (QueryImpl.ofFn (join g E))
    ((simulateQ (wrapIC lr hintVoid pre) (A pk)).run ([], hs0 Lst, fun _ => none))

/-- **The `i`-th derived prover's joint log is a prefix of the `ℓ`-th's** (`i ≤ ℓ`), if forgery `i`
passes the refresher check. -/
theorem jOf_proverP_prefix {i ℓ : ℕ} (hiℓ : i ≤ ℓ) (hi : i < (forgerOut g lr E pk pre A Lst).1.length)
    (hrf : RefreshOk lr ((forgerOut g lr E pk pre A Lst).1.getD i (ByteArray.empty, ByteArray.empty)).2) :
    ∃ Y, jOf g (proverP lr pk pre A Lst ℓ) E = jOf g (proverP lr pk pre A Lst i) E ++ Y := by
  rcases Nat.lt_or_eq_of_le hiℓ with hlt | rfl
  · obtain ⟨Y, hY⟩ := log_contP_prefix lr pk (join g E) (forgerOut g lr E pk pre A Lst) hlt hi hrf
    refine ⟨Y, ?_⟩
    simp only [jOf]
    rw [log_proverP, log_proverP, List.append_assoc, hY]
  · exact ⟨[], (List.append_nil _).symm⟩

/-- **The hash logs, likewise.** -/
theorem runE_proverP_prefix {i ℓ : ℕ}
    (hJ : ∃ Y, jOf g (proverP lr pk pre A Lst ℓ) E = jOf g (proverP lr pk pre A Lst i) E ++ Y) :
    ∃ Y, tableQueryLog (runE E (proverP lr pk pre A Lst ℓ)) g =
      tableQueryLog (runE E (proverP lr pk pre A Lst i)) g ++ Y := by
  obtain ⟨Y, hY⟩ := hJ
  refine ⟨hashEnt Y, ?_⟩
  rw [tableQueryLog_runE_eq, tableQueryLog_runE_eq]
  have hY' : tableQueryLog (proverP lr pk pre A Lst ℓ) (join g E) =
      tableQueryLog (proverP lr pk pre A Lst i) (join g E) ++ Y := hY
  rw [hY', hashEnt_append]

end Prover

/-! ## A failed forgery passes the refresher check -/

section Refresh

variable (g : Table) (T : CrtTables) (lr : Bool) (E : CTable)
  (hint : QueryLog specIC → ByteArray → TG) (pk : UovPk) (pre : TG → SIss) (A : Forger)
  (Lst : List TG) (ℓ : ℕ)

/-- **A failed forgery passed the game's verification**, so the forger output `ℓ + 1` forgeries and
the `i`-th passes the refresher check. -/
theorem pfail_refresh (i : ℕ)
    (h : PFailZ pk i (evalWithAnswerFn (QueryImpl.ofFn g)
      ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
        (Acomp T lr E hint tgts1 pk ℓ A)).run (hs0 Lst)))) :
    let outs := (evalWithAnswerFn (QueryImpl.ofFn (join g E))
      ((simulateQ (wrapIC lr hint pre) (A pk)).run ([], hs0 Lst, fun _ => none))).1
    i < outs.length ∧ outs.length = ℓ + 1 ∧
      RefreshOk lr (outs.getD i (ByteArray.empty, ByteArray.empty)).2 := by
  intro outs
  set b := evalWithAnswerFn (QueryImpl.ofFn (join g E))
    ((simulateQ (wrapIC lr hint pre) (A pk)).run ([], hs0 Lst, fun _ => none)) with hb
  have hF := eval_forger g E lr hint pre (A pk) [] (hs0 Lst) (fun _ => none)
  unfold Acomp at h
  rw [eval_htW_bind, hF] at h
  dsimp only at h
  split_ifs at h with hlen
  swap
  · simp [PFailZ] at h
  rw [eval_htW_bind] at h
  simp only [simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure] at h
  obtain ⟨hflag, x, σ, hcl, -⟩ := h
  rw [← hb] at hlen hflag hcl
  set L := b.2.1 with hL
  set hs := b.2.2.1 with hhs
  set vsS := evalWithAnswerFn (QueryImpl.ofFn g) ((simulateQ (htW (AR := Ans) (S := SIss)
    addHint pre) (verAll T lr E hint tgts1 pk L outs)).run hs) with hvsS
  simp only [decide_eq_true_eq] at hflag
  rw [List.getElem?_map] at hcl
  obtain ⟨v, hv⟩ : ∃ v, vsS.1[i]? = some v := by
    cases hvi : vsS.1[i]? with
    | none => rw [hvi] at hcl; cases hcl
    | some v => exact ⟨v, rfl⟩
  have hi : i < outs.length := by
    have := (List.getElem?_eq_some_iff.1 hv).1
    rwa [hvsS, eval_verAll_length] at this
  have hvacc : v.2 = true := hflag.1 v (List.mem_of_getElem? hv)
  have hsplit := eval_verAll_split g T lr E hint pk pre L outs hs i hi
  rw [← hvsS, hv] at hsplit
  simp only [Option.some.injEq] at hsplit
  rw [eval_verOne] at hsplit
  refine ⟨hi, hlen, ?_⟩
  rw [List.getD_eq_getElem _ _ hi]
  unfold RefreshOk
  split_ifs at hsplit with hrf
  · rw [hsplit] at hvacc; cases hvacc
  · simpa using hrf

/-- **The derived provers of a failed forgery `i ≤ ℓ` and of the last forgery**: the former's joint
and hash logs are prefixes of the latter's, at the same tables (Lemma P's `E₁` as the game's hint
rule). -/
theorem prefix_of_pfail {i : ℕ} (hiℓ : i ≤ ℓ)
    (h : PFailZ pk i (evalWithAnswerFn (QueryImpl.ofFn g)
      ((simulateQ (htW (AR := Ans) (S := SIss) addHint pre)
        (Acomp CrtGen.tables lr E (e1P lr E) tgts1 pk ℓ A)).run (hs0 Lst)))) :
    (∃ Y, tableQueryLog (runE E (proverP lr pk pre A Lst ℓ)) g =
      tableQueryLog (runE E (proverP lr pk pre A Lst i)) g ++ Y) ∧
    ∃ Y, jOf g (proverP lr pk pre A Lst ℓ) E = jOf g (proverP lr pk pre A Lst i) E ++ Y := by
  obtain ⟨hi, -, hrf⟩ := pfail_refresh g CrtGen.tables lr E (e1P lr E) pk pre A Lst ℓ i h
  have hinv0 : InvH (e1P lr E) (hs0 Lst) (hs0 Lst) (fun _ => none) :=
    ⟨SameT.refl _, fun x a e hx => by simp [hs0] at hx⟩
  obtain ⟨e1, -, -, -⟩ := eval_wrapIC_hint g E lr (e1P lr E) pre (A pk) [] _ _ _ hinv0
  rw [e1] at hi hrf
  have hJ := jOf_proverP_prefix g lr E pk pre A Lst hiℓ hi hrf
  exact ⟨runE_proverP_prefix g lr E pk pre A Lst hJ, hJ⟩

end Refresh

end VoleMole.ROM.OneMore.Pomfrit
