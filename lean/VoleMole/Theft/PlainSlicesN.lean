import VoleMole.Theft.PlainRataRom
import VoleMole.Theft.ManyTables
import VoleMole.Theft.HitMany

/-!
# The theft tables with `N` slices as `ROM/`'s oracle

`ansP g₁ g₂ t` (`Theft/PlainOracle.lean`) answers `ROM/`'s oracle `specIC` on the two `H₃` slices
of the one-token games and the shared tables. The many-token games have `N` slices
`g : Fin N → Tab3`. Here they are answered at other `H₃` inputs, and a computation on the `N`
slices is reduced to one on two slices by answering the slice queries locally:

* `locH P a`: an oracle computation with every hash query `d` with `P d` answered locally by
  `a d` (`normT` is the case of SHAKE off the table points). `locH_run`: its run and queries;
  it keeps every query bound (`isQueryBoundP_locH`, `isKindQueryBoundIC_locH`).
* `encSlN`: the `H₃` inputs of the `N` slices (`18 + j` bytes for slice `j`: no other party of
  the games queries them, and they are not the two slices' 17-byte inputs `encSl`). `SlPt N`:
  the slice points, the `H₃` queries at `encSl` or `encSlN`. `slAns g`: their answers, the
  slices at `encSlN` and SHAKE at `encSl`.
* **`ansPN g t`**: the answers with `N` slices: `slAns g` at the slice points, `ansP` elsewhere
  (which does not depend on its two slices there, `ansP_notSl`).
* **`runT_locN`**: on any two slices, the run of `locN g oa` (the slice queries answered by
  `slAns g`) is the run of `oa` on `ansPN g t`, and its queries are `oa`'s without the slice
  queries. The cipher cells of the two lists agree (`cLog_locN`).
* `qBudT_locN`: `locN g` keeps the budget. **`stageBudgetNX_runTN`**, **`admHitN_runTN`**: an oracle
  computation within `QBud q q_E`, run on `ansPN`, has the read budget `StageBudgetNX (q h3) (q h5)
  q_E` and reads each chain table by a decision tree (`AdmHitN`).
* `noH3_ansPN`: a computation that makes no `H₃` query (the prefix computation `vPreIC`,
  `noH3_vPreIC`) has the same run and queries on `ansPN g t` and on `ansP g₁ g₂ t`.
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
/-- **Local answers**: a hash query `d` with `P d` is answered by `a d` without a query; every
other query is made. -/
noncomputable def locH (P : Dom → Prop) (a : (d : Dom) → Ans d) :
    OracleComp specIC α → OracleComp specIC α
  | .pure x => pure x
  | .queryBind (.inl d) k => if P d then locH P a (k (a d)) else
      liftM (specIC.query (.inl d)) >>= fun u => locH P a (k u)
  | .queryBind (.inr c) k => liftM (specIC.query (.inr c)) >>= fun u => locH P a (k u)

open Classical in
/-- The queries `locH P a` makes: hash queries off `P`, cells. -/
noncomputable def offL (P : Dom → Prop) : DomIC → Bool
  | .inl d => !decide (P d)
  | .inr _ => true

lemma locH_local {P : Dom → Prop} {a : (d : Dom) → Ans d} {d : Dom}
    {k : specIC.Range (Sum.inl d) → OracleComp specIC α} (hd : P d) :
    locH P a (.queryBind (.inl d) k) = locH P a (k (a d)) := by
  classical
  simp only [locH, hd, ite_true]

lemma locH_made {P : Dom → Prop} {a : (d : Dom) → Ans d} {d : Dom}
    {k : specIC.Range (Sum.inl d) → OracleComp specIC α} (hd : ¬ P d) :
    locH P a (.queryBind (.inl d) k) =
      liftM (specIC.query (.inl d)) >>= fun u => locH P a (k u) := by
  classical
  simp only [locH, hd, ite_false]

/-- **The run with local answers**: if `f'` answers `P` by `a` and agrees with `f` elsewhere, the
run of `locH P a oa` on `f` is the run of `oa` on `f'`, and its queries are `oa`'s off `P`. -/
theorem locH_run (P : Dom → Prop) (a : (d : Dom) → Ans d) (f f' : (d : DomIC) → AnsIC d)
    (hP : ∀ d, P d → f' (.inl d) = a d) (hQ : ∀ d, ¬ P d → f (.inl d) = f' (.inl d))
    (hc : ∀ c, f (.inr c) = f' (.inr c)) (oa : OracleComp specIC α) :
    runT f (locH P a oa) = runT f' oa ∧ qlog f (locH P a oa) = (qlog f' oa).filter (offL P) := by
  classical
  induction oa with
  | pure x => exact ⟨rfl, rfl⟩
  | queryBind t k ih =>
    rcases t with d | c
    · by_cases hd : P d
      · rw [locH_local hd]
        have e : f' (.inl d) = a d := hP d hd
        refine ⟨?_, ?_⟩
        · show runT f (locH P a (k (a d))) = runT f' (k (f' (.inl d)))
          rw [e]; exact (ih _).1
        · show qlog f (locH P a (k (a d))) = List.filter _ ((Sum.inl d) :: qlog f' (k (f' (.inl d))))
          rw [List.filter_cons_of_neg (by simp [offL, hd]), e]
          exact (ih _).2
      · rw [locH_made hd]
        have e : f (.inl d) = f' (.inl d) := hQ d hd
        refine ⟨?_, ?_⟩
        · show runT f (locH P a (k (f (.inl d)))) = runT f' (k (f' (.inl d)))
          rw [e]; exact (ih _).1
        · show (Sum.inl d) :: qlog f (locH P a (k (f (.inl d)))) =
            List.filter _ ((Sum.inl d) :: qlog f' (k (f' (.inl d))))
          rw [List.filter_cons_of_pos (by simp [offL, hd]), e, (ih _).2]
    · refine ⟨?_, ?_⟩
      · show runT f (locH P a (k (f (.inr c)))) = runT f' (k (f' (.inr c)))
        rw [hc]; exact (ih _).1
      · show (Sum.inr c) :: qlog f (locH P a (k (f (.inr c)))) =
          List.filter _ ((Sum.inr c) :: qlog f' (k (f' (.inr c))))
        rw [List.filter_cons_of_pos (by simp [offL]), hc, (ih _).2]

/-- **Local answers keep every query bound of a class.** -/
theorem isQueryBoundP_locH (P : Dom → Prop) (a : (d : Dom) → Ans d) {Q : DomIC → Prop}
    [DecidablePred Q] {oa : OracleComp specIC α} {n : ℕ} (h : IsQueryBoundP oa Q n) :
    IsQueryBoundP (locH P a oa) Q n := by
  induction oa generalizing n with
  | pure x => trivial
  | queryBind t k ih =>
    have h' := (isQueryBoundP_query_bind_iff Q t k n).1 h
    rcases t with d | c
    · by_cases hd : P d
      · rw [locH_local hd]
        exact ih _ ((h'.2 _).mono (by split <;> omega))
      · rw [locH_made hd]
        exact (isQueryBoundP_query_bind_iff Q _ _ n).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩
    · exact (isQueryBoundP_query_bind_iff Q _ _ n).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩

/-- **Local answers keep the per-kind hash bounds.** -/
theorem isKindQueryBoundIC_locH (P : Dom → Prop) (a : (d : Dom) → Ans d)
    {oa : OracleComp specIC α} {q : Kind → ℕ} (h : IsKindQueryBoundIC oa q) :
    IsKindQueryBoundIC (locH P a oa) q := by
  induction oa generalizing q with
  | pure x => trivial
  | queryBind t k ih =>
    have h' := (isQueryBound_query_bind_iff t k q _ _).1 h
    rcases t with d | c
    · by_cases hd : P d
      · rw [locH_local hd]
        refine ih _ ((show IsKindQueryBoundIC (k (a d)) (Function.update q d.1 (q d.1 - 1))
          from h'.2 _).mono fun k' => ?_)
        by_cases hk : k' = d.1
        · subst hk; simp
        · simp [Function.update_of_ne hk]
      · rw [locH_made hd]
        exact (isQueryBound_query_bind_iff _ _ q _ _).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩
    · exact (isQueryBound_query_bind_iff _ _ q _ _).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩

/-- Local answers keep the budget with a total. -/
theorem qBud_locH (P : Dom → Prop) (a : (d : Dom) → Ans d) {oa : OracleComp specIC α}
    {q : Kind → ℕ} {qE : ℕ} (h : QBud q qE oa) : QBud q qE (locH P a oa) :=
  ⟨isKindQueryBoundIC_locH P a h.1, isQueryBoundP_locH P a h.2⟩

/-- The cipher cells of a list of queries without some hash queries. -/
lemma cLog_offL (E : CTable) (P : Dom → Prop) (l : List DomIC) :
    cLog E (l.filter (offL P)) = cLog E l :=
  cLog_filter E _ (fun _ => rfl) l

end Loc

/-! ## The slices -/

section Slices

variable {N : ℕ}

/-- Slice `j`'s key as `18 + j` bytes: the 16-byte key, then the byte `7`. -/
def slvN (jk : Fin N × Bytes 16) : Bytes (18 + jk.1.val) :=
  fun i => if h : i.val < 16 then jk.2 ⟨i, h⟩ else 7

/-- **The `H₃` inputs of the `N` slices.** -/
def encSlN (jk : Fin N × Bytes 16) : ByteArray := ba (slvN jk)

lemma encSlN_size (jk : Fin N × Bytes 16) : (encSlN jk).size = 18 + jk.1.val := size_ba _

lemma encSlN_injective : Function.Injective (encSlN (N := N)) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  have hj : j = j' := Fin.ext (by
    have := congrArg ByteArray.size h
    rw [encSlN_size, encSlN_size] at this
    simpa using this)
  subst hj
  have hk : slvN (j, k) = slvN (j, k') := ba_injective h
  have : k = k' := funext fun i => by
    have := congrFun hk ⟨i, by omega⟩
    simpa [slvN, i.isLt] using this
  rw [this]

lemma encSlN_ne_encSl (jk : Fin N × Bytes 16) (a : Bool × Bytes 16) : encSlN jk ≠ encSl a := by
  intro h
  have := congrArg ByteArray.size h
  rw [encSlN_size] at this
  simp [encSl] at this
  omega

/-- **The slice points**: `H₃` at the two slices' inputs or at the `N` slices'. -/
def SlPt (N : ℕ) (d : Dom) : Prop :=
  d.1 = .h3 ∧ ((∃ a, encSl a = d.2) ∨ ∃ jk : Fin N × Bytes 16, encSlN jk = d.2)

open Classical in
/-- **The answers at the slice points**: slice `j` at `encSlN (j, k)`, SHAKE at `encSl`. -/
noncomputable def slAns (g : Fin N → Tab3) (d : Dom) : Ans d :=
  blk d.1.outLen (if h : ∃ jk : Fin N × Bytes 16, encSlN jk = d.2 then ba (g h.choose.1 h.choose.2)
    else Hashes.shake.hash d.1 d.2)

variable {R : Type} [CipherRow R] {p : Params} {L M : ℕ}

/-- The two slices of the reduction (any value; `ansP` does not read them off the slice points). -/
def zT : Tab3 := fun _ => 0

open Classical in
/-- **The answers of `specIC` with `N` slices**: `slAns g` at the slice points, `ansP` elsewhere. -/
noncomputable def ansPN (g : Fin N → Tab3) (t : ShX R p (XTab L M)) : (d : DomIC) → AnsIC d
  | .inl d => if SlPt N d then slAns g d else tabP zT zT t d
  | .inr c => cellP t c

omit [CipherRow R] in
/-- **Off the slice points, `ansP` does not read its slices.** -/
lemma tabP_notSl (g₁ g₂ g₁' g₂' : Tab3) (t : ShX R p (XTab L M)) {d : Dom}
    (hd : ¬ (d.1 = .h3 ∧ ∃ a, encSl a = d.2)) : tabP g₁ g₂ t d = tabP g₁' g₂' t d := by
  classical
  obtain ⟨k, b⟩ := d
  show blk _ ((recP g₁ g₂ t).hash k b) = blk _ ((recP g₁' g₂' t).hash k b)
  by_cases hk : k = .h3
  · subst hk
    have hn : ¬ ∃ a, encSl a = b := fun h => hd ⟨rfl, h⟩
    rw [recP_h3, recP_h3, dite_eq_right hn, dite_eq_right hn]
  · unfold recP
    rw [Hashes.withTable_ne _ _ _ hk, Hashes.withTable_ne _ _ _ hk]

lemma ansPN_slPt (g : Fin N → Tab3) (t : ShX R p (XTab L M)) {d : Dom} (hd : SlPt N d) :
    ansPN g t (.inl d) = slAns g d := by
  classical
  show (if SlPt N d then _ else _) = _
  exact ite_eq_left_of_eq_true _ _ (eq_true hd)

lemma ansPN_notSl (g : Fin N → Tab3) (t : ShX R p (XTab L M)) {d : Dom} (hd : ¬ SlPt N d)
    (g₁ g₂ : Tab3) : ansPN g t (.inl d) = ansP g₁ g₂ t (.inl d) := by
  classical
  show (if SlPt N d then _ else _) = _
  refine (ite_eq_right_of_eq_false _ _ (eq_false hd)).trans ?_
  exact tabP_notSl _ _ _ _ t fun h => hd ⟨h.1, Or.inl h.2⟩

/-- **Off the slice points, `ansPN` is `ansP`** (on any two slices). -/
lemma ansPN_eq (g : Fin N → Tab3) (t : ShX R p (XTab L M)) (g₁ g₂ : Tab3) {d : DomIC}
    (hd : ∀ d', d = .inl d' → ¬ SlPt N d') : ansPN g t d = ansP g₁ g₂ t d := by
  rcases d with d | c
  · exact ansPN_notSl g t (hd d rfl) g₁ g₂
  · rfl

/-- **The computation with the slice queries answered locally.** -/
noncomputable def locN (g : Fin N → Tab3) {α : Type} (oa : OracleComp specIC α) :
    OracleComp specIC α :=
  locH (SlPt N) (slAns g) oa

/-- **The run on two slices of `locN g oa` is the run of `oa` on the `N` slices `g`**, and its
queries are `oa`'s without the slice queries. -/
theorem runT_locN (g : Fin N → Tab3) (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) {α : Type}
    (oa : OracleComp specIC α) :
    runT (ansP g₁ g₂ t) (locN g oa) = runT (ansPN g t) oa ∧
      qlog (ansP g₁ g₂ t) (locN g oa) = (qlog (ansPN g t) oa).filter (offL (SlPt N)) :=
  locH_run _ _ _ _ (fun _ hd => ansPN_slPt g t hd)
    (fun _ hd => (ansPN_notSl g t hd g₁ g₂).symm) (fun _ => rfl) oa

lemma cLog_locN (g : Fin N → Tab3) (g₁ g₂ : Tab3) (t : ShX R p (XTab L M)) {α : Type}
    (oa : OracleComp specIC α) (E : CTable) :
    cLog E (qlog (ansP g₁ g₂ t) (locN g oa)) = cLog E (qlog (ansPN g t) oa) := by
  rw [(runT_locN g g₁ g₂ t oa).2, cLog_offL]

lemma qBudT_locN {α : Type} {oa : OracleComp specIC α} {q : Kind → ℕ} {qE nG : ℕ}
    (h : QBudT q qE nG oa) (g : Fin N → Tab3) : QBudT q qE nG (locN g oa) :=
  ⟨qBud_locH _ _ h.1, isQueryBoundP_locH _ _ h.2⟩

/-! ## Read budgets of a run with `N` slices -/

open Classical in
/-- The key of a query to slice `j` of the `N`. -/
noncomputable def dec3N (j : Fin N) : DomIC → Option (Bytes 16)
  | .inl d => if d.1 = .h3 then (if h : ∃ jk : Fin N × Bytes 16, encSlN jk = d.2 then
      (if h.choose.1 = j then some h.choose.2 else none) else none) else none
  | .inr _ => none

lemma dec3N_kind {j : Fin N} {d : DomIC} {k : Bytes 16} (h : dec3N j d = some k) :
    kindB .h3 d = true := by
  rcases d with ⟨k', b⟩ | c
  · simp only [dec3N] at h
    split_ifs at h with h1
    simp [kindB, h1]
  · simp [dec3N] at h

/-- The answers with another slice `j` agree at every query whose slice-`j` key they agree at. -/
lemma ansPN_h3 (g : Fin N → Tab3) (j : Fin N) (u u' : Tab3) (t : ShX R p (XTab L M)) (d : DomIC)
    (hd : ∀ k, dec3N j d = some k → u k = u' k) :
    ansPN (Function.update g j u) t d = ansPN (Function.update g j u') t d := by
  classical
  rcases d with ⟨k, b⟩ | c
  · by_cases hs : SlPt N (k, b)
    · rw [ansPN_slPt _ _ hs, ansPN_slPt _ _ hs]
      unfold slAns
      by_cases h : ∃ jk : Fin N × Bytes 16, encSlN jk = (k, b).2
      · rw [dite_eq_left h, dite_eq_left h]
        by_cases hj : h.choose.1 = j
        · rw [hj, Function.update_self, Function.update_self]
          have hk : k = .h3 := hs.1
          rw [hd h.choose.2 (by
            simp only [dec3N, hk, ite_true, dite_eq_left h, hj])]
        · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      · rw [dite_eq_right h, dite_eq_right h]
    · rw [ansPN_notSl _ _ hs zT zT, ansPN_notSl _ _ hs zT zT]
  · rfl

/-- **The read budget of a run on the `N` slices and the tables**: each slice at its `H₃` queries,
`H₅` at its `H₅` queries, the cipher at the rows of its cell queries. -/
theorem stageBudgetNX_runTN {α : Type} {oa : OracleComp specIC α} {q : Kind → ℕ} {qE : ℕ}
    (h : QBud q qE oa) :
    StageBudgetNX (R := R) (p := p) (X := XTab L M) (N := N)
      (fun g t => runT (ansPN g t) oa) (q .h3) (q .h5) qE := by
  classical
  intro x
  refine ⟨fun g j s => ?_, fun g => ?_, fun g => ?_⟩
  · refine ⟨fun u => ((qlog (ansPN (Function.update g j u) (atX s x)) oa).filterMap
        (dec3N j)).toFinset,
      fun u => card_dec_le _ _ _ _ (isQueryBoundP_kind h.1 .h3) fun _ _ => dec3N_kind,
      fun u u' hg => ?_⟩
    exact runT_congr_dec oa _ _ (dec3N j) _ (fun d hd k hk => mem_dec hd hk)
      fun d hd => ansPN_h3 g j u u' _ d fun k hk => hg k (hd k hk)
  · have hB := (stageBudgetX_runT (R := R) (p := p) (L := L) (M := M)
      (qBud_locH (SlPt N) (slAns g) h) x).h5 zT zT
    have e : (fun s : ShG R p => runT (ansP zT zT (atX s x)) (locN g oa)) =
        fun s => runT (ansPN g (atX s x)) oa := funext fun s => (runT_locN g zT zT _ oa).1
    exact e ▸ hB
  · have hB := (stageBudgetX_runT (R := R) (p := p) (L := L) (M := M)
      (qBud_locH (SlPt N) (slAns g) h) x).hE zT zT
    have e : (fun s : ShG R p => runT (ansP zT zT (atX s x)) (locN g oa)) =
        fun s => runT (ansPN g (atX s x)) oa := funext fun s => (runT_locN g zT zT _ oa).1
    exact e ▸ hB

/-- **A run on the `N` slices reads the chain tables by decision trees** (`AdmHitN`). -/
theorem admHitN_runTN {α : Type} {oa : OracleComp specIC α} {q : Kind → ℕ} {qE : ℕ}
    (h : QBud q qE oa) :
    Hit.AdmHitN (R := R) (p := p) (L := L) (M := M) (N := N) (q .mu) (q .h21) (q .h22)
      (fun g t => runT (ansPN g t) oa) := by
  intro g
  have hB := admHit_runT (R := R) (p := p) (L := L) (M := M) (qBud_locH (SlPt N) (slAns g) h) zT zT
  have e : (fun t : ShX R p (XTab L M) => runT (ansP zT zT t) (locN g oa)) =
      fun t => runT (ansPN g t) oa :=
    funext fun t => (runT_locN g zT zT t oa).1
  show Hit.TreeT _ _ _ (fun t => runT (ansPN g t) oa)
  exact e ▸ hB

/-! ## Computations without `H₃` queries -/

/-- **A computation that makes no `H₃` query** has the same run and queries on `ansPN g t` and on
`ansP g₁ g₂ t`. -/
theorem noH3_ansPN {α : Type} (oa : OracleComp specIC α) (g : Fin N → Tab3) (g₁ g₂ : Tab3)
    (t : ShX R p (XTab L M)) (h : ∀ d ∈ qlog (ansP g₁ g₂ t) oa, kindB .h3 d = false) :
    qlog (ansPN g t) oa = qlog (ansP g₁ g₂ t) oa ∧ runT (ansPN g t) oa = runT (ansP g₁ g₂ t) oa :=
  runT_congr oa _ _ fun d hd => (ansPN_eq g t g₁ g₂ fun d' hd' hs => by
    have := h d hd
    subst hd'
    simp [kindB, hs.1] at this).symm

omit [CipherRow R] in
/-- A computation with no `H₃` query in its per-kind budget makes none. -/
lemma noH3_of_kind {α : Type} {oa : OracleComp specIC α} {q : Kind → ℕ}
    (h : IsKindQueryBoundIC oa q) (h3 : q .h3 = 0) (f : (d : DomIC) → AnsIC d) :
    ∀ d ∈ qlog f oa, kindB .h3 d = false := by
  have h0 := countP_kind_le h .h3 f
  rw [h3, Nat.le_zero, List.countP_eq_zero] at h0
  simpa using h0

end Slices

end VoleMole.Theft
