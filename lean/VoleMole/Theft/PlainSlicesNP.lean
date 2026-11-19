import VoleMole.Theft.PlainPerm
import VoleMole.Theft.PlainEagerP

/-!
# The theft tables with `N` slices as `ROM/`'s permutation-model oracle

`Theft/PlainSlicesN.lean` for `specP` (forward and inverse cipher queries, permutation rows):

* `locHQ P a`: hash queries `d` with `P d` answered locally by `a d` (`locHQ_run`); it keeps the
  query bounds (`qBudP_locHQ`).
* **`ansPNQ g t`**: `slAns g` at the slice points, `ansQ` elsewhere (`ansPNQ_eq`).
* **`runT_locNQ`**: on any two slices, the run of `locNQ g oa` is the run of `oa` on the `N`
  slices, and its queries are `oa`'s without the slice queries (so the same cipher records).
* **`stageBudgetNX_runTNQ`**, **`admHitN_runTNQ`**: the read budget and the decision trees of a run
  on `ansPNQ`.
* `noH3_ansPNQ`: a computation without `H₃` queries runs on `ansPNQ g t` as on `ansQ g₁ g₂ t`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open OracleComp OracleSpec

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## Local answers -/

section Loc

variable {α : Type}

open Classical in
/-- **Local answers** (permutation model): a hash query `d` with `P d` is answered by `a d`
without a query; every other query is made. -/
noncomputable def locHQ (P : Dom → Prop) (a : (d : Dom) → Ans d) :
    OracleComp specP α → OracleComp specP α
  | .pure x => pure x
  | .queryBind (.inl d) k => if P d then locHQ P a (k (a d)) else
      liftM (specP.query (.inl d)) >>= fun u => locHQ P a (k u)
  | .queryBind (.inr c) k => liftM (specP.query (.inr c)) >>= fun u => locHQ P a (k u)

open Classical in
/-- The queries `locHQ P a` makes: hash queries off `P`, cipher queries. -/
noncomputable def offLQ (P : Dom → Prop) : DomP → Bool
  | .inl d => !decide (P d)
  | .inr _ => true

lemma locHQ_local {P : Dom → Prop} {a : (d : Dom) → Ans d} {d : Dom}
    {k : specP.Range (Sum.inl d) → OracleComp specP α} (hd : P d) :
    locHQ P a (.queryBind (.inl d) k) = locHQ P a (k (a d)) := by
  classical
  simp only [locHQ, hd, ite_true]

lemma locHQ_made {P : Dom → Prop} {a : (d : Dom) → Ans d} {d : Dom}
    {k : specP.Range (Sum.inl d) → OracleComp specP α} (hd : ¬ P d) :
    locHQ P a (.queryBind (.inl d) k) =
      liftM (specP.query (.inl d)) >>= fun u => locHQ P a (k u) := by
  classical
  simp only [locHQ, hd, ite_false]

/-- **The run with local answers**, as `locH_run`. -/
theorem locHQ_run (P : Dom → Prop) (a : (d : Dom) → Ans d) (f f' : (d : DomP) → AnsP d)
    (hP : ∀ d, P d → f' (.inl d) = a d) (hQ : ∀ d, ¬ P d → f (.inl d) = f' (.inl d))
    (hc : ∀ c, f (.inr c) = f' (.inr c)) (oa : OracleComp specP α) :
    runT f (locHQ P a oa) = runT f' oa ∧
      qlog f (locHQ P a oa) = (qlog f' oa).filter (offLQ P) := by
  classical
  induction oa with
  | pure x => exact ⟨rfl, rfl⟩
  | queryBind t k ih =>
    rcases t with d | c
    · by_cases hd : P d
      · rw [locHQ_local hd]
        have e : f' (.inl d) = a d := hP d hd
        refine ⟨?_, ?_⟩
        · show runT f (locHQ P a (k (a d))) = runT f' (k (f' (.inl d)))
          rw [e]; exact (ih _).1
        · show qlog f (locHQ P a (k (a d))) =
            List.filter _ ((Sum.inl d) :: qlog f' (k (f' (.inl d))))
          rw [List.filter_cons_of_neg (by simp [offLQ, hd]), e]
          exact (ih _).2
      · rw [locHQ_made hd]
        have e : f (.inl d) = f' (.inl d) := hQ d hd
        refine ⟨?_, ?_⟩
        · show runT f (locHQ P a (k (f (.inl d)))) = runT f' (k (f' (.inl d)))
          rw [e]; exact (ih _).1
        · show (Sum.inl d) :: qlog f (locHQ P a (k (f (.inl d)))) =
            List.filter _ ((Sum.inl d) :: qlog f' (k (f' (.inl d))))
          rw [List.filter_cons_of_pos (by simp [offLQ, hd]), e, (ih _).2]
    · refine ⟨?_, ?_⟩
      · show runT f (locHQ P a (k (f (.inr c)))) = runT f' (k (f' (.inr c)))
        rw [hc]; exact (ih _).1
      · show (Sum.inr c) :: qlog f (locHQ P a (k (f (.inr c)))) =
          List.filter _ ((Sum.inr c) :: qlog f' (k (f' (.inr c))))
        rw [List.filter_cons_of_pos (by simp [offLQ]), hc, (ih _).2]

/-- Local answers keep every query bound of a class. -/
theorem isQueryBoundP_locHQ (P : Dom → Prop) (a : (d : Dom) → Ans d) {Q : DomP → Prop}
    [DecidablePred Q] {oa : OracleComp specP α} {n : ℕ} (h : IsQueryBoundP oa Q n) :
    IsQueryBoundP (locHQ P a oa) Q n := by
  induction oa generalizing n with
  | pure x => trivial
  | queryBind t k ih =>
    have h' := (isQueryBoundP_query_bind_iff Q t k n).1 h
    rcases t with d | c
    · by_cases hd : P d
      · rw [locHQ_local hd]
        exact ih _ ((h'.2 _).mono (by split <;> omega))
      · rw [locHQ_made hd]
        exact (isQueryBoundP_query_bind_iff Q _ _ n).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩
    · exact (isQueryBoundP_query_bind_iff Q _ _ n).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩

/-- Local answers keep the per-kind hash bounds. -/
theorem isKindQueryBoundP_locHQ (P : Dom → Prop) (a : (d : Dom) → Ans d)
    {oa : OracleComp specP α} {q : Kind → ℕ} (h : IsKindQueryBoundP oa q) :
    IsKindQueryBoundP (locHQ P a oa) q := by
  induction oa generalizing q with
  | pure x => trivial
  | queryBind t k ih =>
    have h' := (isQueryBound_query_bind_iff t k q _ _).1 h
    rcases t with d | c
    · by_cases hd : P d
      · rw [locHQ_local hd]
        refine ih _ ((show IsKindQueryBoundP (k (a d)) (Function.update q d.1 (q d.1 - 1))
          from h'.2 _).mono fun k' => ?_)
        by_cases hk : k' = d.1
        · subst hk; simp
        · simp [Function.update_of_ne hk]
      · rw [locHQ_made hd]
        exact (isQueryBound_query_bind_iff _ _ q _ _).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩
    · exact (isQueryBound_query_bind_iff _ _ q _ _).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩

theorem qBudP_locHQ (P : Dom → Prop) (a : (d : Dom) → Ans d) {oa : OracleComp specP α}
    {q : Kind → ℕ} {qE : ℕ} (h : QBudP q qE oa) : QBudP q qE (locHQ P a oa) :=
  ⟨isKindQueryBoundP_locHQ P a h.1, isQueryBoundP_locHQ P a h.2⟩

/-- The cells of a list of queries without some hash queries. -/
lemma cLog_offLQ (π : PTable) (P : Dom → Prop) (l : List DomP) :
    cLog π.fwd ((l.filter (offLQ P)).map (toIC π)) = cLog π.fwd (l.map (toIC π)) :=
  cLog_map_filter π _ (fun _ => rfl) l

end Loc

/-! ## The slices -/

section Slices

variable {N : ℕ} {p : Params} {L M : ℕ}

open Classical in
/-- **The answers of `specP` with `N` slices**: `slAns g` at the slice points, `ansQ` elsewhere. -/
noncomputable def ansPNQ (g : Fin N → Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M)) :
    (d : DomP) → AnsP d
  | .inl d => if SlPt N d then slAns g d else tabP zT zT t d
  | .inr c => pans t.2.1.2 c

lemma ansPNQ_inl (g : Fin N → Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M)) (d : Dom) :
    ansPNQ g t (.inl d) = ansPN g t (.inl d) := rfl

lemma ansPNQ_slPt (g : Fin N → Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M)) {d : Dom}
    (hd : SlPt N d) : ansPNQ g t (.inl d) = slAns g d :=
  ansPN_slPt g t hd

/-- **Off the slice points, `ansPNQ` is `ansQ`** (on any two slices). -/
lemma ansPNQ_eq (g : Fin N → Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M)) (g₁ g₂ : Tab3)
    {d : DomP} (hd : ∀ d', d = .inl d' → ¬ SlPt N d') : ansPNQ g t d = ansQ g₁ g₂ t d := by
  rcases d with d | c
  · exact ansPN_notSl g t (hd d rfl) g₁ g₂
  · rfl

/-- **The computation with the slice queries answered locally.** -/
noncomputable def locNQ (g : Fin N → Tab3) {α : Type} (oa : OracleComp specP α) :
    OracleComp specP α :=
  locHQ (SlPt N) (slAns g) oa

/-- **The run on two slices of `locNQ g oa` is the run of `oa` on the `N` slices `g`.** -/
theorem runT_locNQ (g : Fin N → Tab3) (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M))
    {α : Type} (oa : OracleComp specP α) :
    runT (ansQ g₁ g₂ t) (locNQ g oa) = runT (ansPNQ g t) oa ∧
      qlog (ansQ g₁ g₂ t) (locNQ g oa) = (qlog (ansPNQ g t) oa).filter (offLQ (SlPt N)) :=
  locHQ_run (SlPt N) (slAns g) (ansQ g₁ g₂ t) (ansPNQ g t) (fun _ hd => ansPNQ_slPt g t hd)
    (fun _ hd => (ansPN_notSl g t hd g₁ g₂).symm) (fun _ => rfl) oa

lemma cLog_locNQ (g : Fin N → Tab3) (g₁ g₂ : Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M))
    {α : Type} (oa : OracleComp specP α) (π : PTable) :
    cLog π.fwd ((qlog (ansQ g₁ g₂ t) (locNQ g oa)).map (toIC π)) =
      cLog π.fwd ((qlog (ansPNQ g t) oa).map (toIC π)) := by
  rw [(runT_locNQ g g₁ g₂ t oa).2, cLog_offLQ]

/-- The key of a query to slice `j` of the `N`. -/
noncomputable def dec3NQ (j : Fin N) : DomP → Option (Bytes 16)
  | .inl d => dec3N j (.inl d)
  | .inr _ => none

lemma dec3NQ_kind {j : Fin N} {d : DomP} {k : Bytes 16} (h : dec3NQ j d = some k) :
    kindBP .h3 d = true := by
  rcases d with d | c
  · simpa [kindBP, kindB] using dec3N_kind (d := .inl d) h
  · simp [dec3NQ] at h

lemma ansPNQ_h3 (g : Fin N → Tab3) (j : Fin N) (u u' : Tab3)
    (t : ShX (Equiv.Perm Blk) p (XTab L M)) (d : DomP)
    (hd : ∀ k, dec3NQ j d = some k → u k = u' k) :
    ansPNQ (Function.update g j u) t d = ansPNQ (Function.update g j u') t d := by
  rcases d with d | c
  · exact ansPN_h3 (R := Equiv.Perm Blk) g j u u' t (.inl d) hd
  · rfl

/-- **The read budget of a run on the `N` slices and the permutation tables.** -/
theorem stageBudgetNX_runTNQ {α : Type} {oa : OracleComp specP α} {q : Kind → ℕ} {qE : ℕ}
    (h : QBudP q qE oa) :
    StageBudgetNX (R := Equiv.Perm Blk) (p := p) (X := XTab L M) (N := N)
      (fun g t => runT (ansPNQ g t) oa) (q .h3) (q .h5) qE := by
  classical
  intro x
  refine ⟨fun g j s => ?_, fun g => ?_, fun g => ?_⟩
  · refine ⟨fun u => ((qlog (ansPNQ (Function.update g j u) (atX s x)) oa).filterMap
        (dec3NQ j)).toFinset,
      fun u => card_dec_leG _ _ _ _ (isQueryBoundP_kindP h.1 .h3) fun _ _ => dec3NQ_kind,
      fun u u' hg => ?_⟩
    exact runT_congr_decG oa _ _ (dec3NQ j) _ (fun d hd k hk => mem_decG hd hk)
      fun d hd => ansPNQ_h3 g j u u' _ d fun k hk => hg k (hd k hk)
  · have hB := (stageBudgetX_runTQ (p := p) (L := L) (M := M)
      (qBudP_locHQ (SlPt N) (slAns g) h) x).h5 zT zT
    have e : (fun s : ShG (Equiv.Perm Blk) p => runT (ansQ zT zT (atX s x)) (locNQ g oa)) =
        fun s => runT (ansPNQ g (atX s x)) oa := funext fun s => (runT_locNQ g zT zT _ oa).1
    exact e ▸ hB
  · have hB := (stageBudgetX_runTQ (p := p) (L := L) (M := M)
      (qBudP_locHQ (SlPt N) (slAns g) h) x).hE zT zT
    have e : (fun s : ShG (Equiv.Perm Blk) p => runT (ansQ zT zT (atX s x)) (locNQ g oa)) =
        fun s => runT (ansPNQ g (atX s x)) oa := funext fun s => (runT_locNQ g zT zT _ oa).1
    exact e ▸ hB

/-- **A run on the `N` slices reads the chain tables by decision trees** (`AdmHitN`). -/
theorem admHitN_runTNQ {α : Type} {oa : OracleComp specP α} {q : Kind → ℕ} {qE : ℕ}
    (h : QBudP q qE oa) :
    Hit.AdmHitN (R := Equiv.Perm Blk) (p := p) (L := L) (M := M) (N := N) (q .mu) (q .h21)
      (q .h22) (fun g t => runT (ansPNQ g t) oa) := by
  intro g
  have hB := admHit_runTQ (p := p) (L := L) (M := M) (qBudP_locHQ (SlPt N) (slAns g) h) zT zT
  have e : (fun t : ShX (Equiv.Perm Blk) p (XTab L M) => runT (ansQ zT zT t) (locNQ g oa)) =
      fun t => runT (ansPNQ g t) oa :=
    funext fun t => (runT_locNQ g zT zT t oa).1
  show Hit.TreeT _ _ _ (fun t => runT (ansPNQ g t) oa)
  exact e ▸ hB

/-- **A computation that makes no `H₃` query** has the same run and queries on `ansPNQ g t` and
on `ansQ g₁ g₂ t`. -/
theorem noH3_ansPNQ {α : Type} (oa : OracleComp specP α) (g : Fin N → Tab3) (g₁ g₂ : Tab3)
    (t : ShX (Equiv.Perm Blk) p (XTab L M))
    (h : ∀ d ∈ qlog (ansQ g₁ g₂ t) oa, kindBP .h3 d = false) :
    qlog (ansPNQ g t) oa = qlog (ansQ g₁ g₂ t) oa ∧
      runT (ansPNQ g t) oa = runT (ansQ g₁ g₂ t) oa :=
  runT_congr oa _ _ fun d hd => (ansPNQ_eq g t g₁ g₂ fun d' hd' hs => by
    have := h d hd
    subst hd'
    simp [kindBP, hs.1] at this).symm

/-- A computation with no `H₃` query in its per-kind budget makes none. -/
lemma noH3_of_kindP {α : Type} {oa : OracleComp specP α} {q : Kind → ℕ}
    (h : IsKindQueryBoundP oa q) (h3 : q .h3 = 0) (f : (d : DomP) → AnsP d) :
    ∀ d ∈ qlog f oa, kindBP .h3 d = false := by
  have h0 := countP_qlog_le oa f (kindBP .h3) (isQueryBoundP_kindP h .h3)
  rw [h3, Nat.le_zero, List.countP_eq_zero] at h0
  simpa using h0

lemma ansPNQ_h5 (g : Fin N → Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M)) (G5 : Tab5F) (d : DomP)
    (hd : ∀ k, dec5P d = some k → t.2.1.1 k = G5 k) :
    ansPNQ g t d = ansPNQ g (t.1, ((G5, t.2.1.2), t.2.2)) d := by
  by_cases hs : ∃ d', d = .inl d' ∧ SlPt N d'
  · obtain ⟨d', rfl, hs⟩ := hs
    rw [ansPNQ_slPt _ _ hs, ansPNQ_slPt _ _ hs]
  · have hd' : ∀ d', d = .inl d' → ¬ SlPt N d' := fun d' h1 h2 => hs ⟨d', h1, h2⟩
    rw [ansPNQ_eq g _ zT zT hd', ansPNQ_eq g _ zT zT hd']
    exact ansQ_h5 zT zT t G5 d hd

lemma ansPNQ_E (g : Fin N → Tab3) (t : ShX (Equiv.Perm Blk) p (XTab L M))
    (E : Blk → Equiv.Perm Blk) (d : DomP) (hd : ∀ k, decEP d = some k → t.2.1.2 k = E k) :
    ansPNQ g t d = ansPNQ g (t.1, ((t.2.1.1, E), t.2.2)) d := by
  by_cases hs : ∃ d', d = .inl d' ∧ SlPt N d'
  · obtain ⟨d', rfl, hs⟩ := hs
    rw [ansPNQ_slPt _ _ hs, ansPNQ_slPt _ _ hs]
  · have hd' : ∀ d', d = .inl d' → ¬ SlPt N d' := fun d' h1 h2 => hs ⟨d', h1, h2⟩
    rw [ansPNQ_eq g _ zT zT hd', ansPNQ_eq g _ zT zT hd']
    exact ansQ_E zT zT t E d hd

end Slices

end VoleMole.Theft
