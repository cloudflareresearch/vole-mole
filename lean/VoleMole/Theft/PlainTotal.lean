import VoleMole.Theft.PlainSlicesN
import VoleMole.Theft.PlainRataRom
import VoleMole.Theft.ManyPlainLog

/-!
# The total hash budget follows from the per-kind budgets

`ROM/`'s extraction bounds charge the total number `n_G` of hash queries, and the `*_lean_rom'`
theorems therefore ask the adversary for a total budget (`QBudT q q_E n_G`). Per-kind bounds do not
bound the total in general: `Kind.comb` has a parameter, so there are infinitely many kinds. But
in the theft games `M` is fixed (`XTab L M`), and every hash query the tables answer other than by
SHAKE is of one of ten kinds (`kindsT M`: `H₃`, `H₂³`, `H₅`, `H₁`, `H₂⁰`, `H₂⁴`, `H₄`, `H₂¹`,
`H₂²`, `H_comb` with `M`). A query off those points the adversary can answer itself, by SHAKE.
So the last stage is also the run of a computation that makes only the table queries, and its
total is at most `Σ_{k ∈ kindsT M} q k` (`totK M q`):

* `normS S oa`: `oa` with every hash query outside `S` answered locally by SHAKE
  (`runT_normS`: on answers that are SHAKE outside `S`, the run is `oa`'s).
* `isQueryBoundP_left_of_kinds`: a computation whose hash queries all have kinds in `K` makes at
  most `Σ_{k ∈ K} q k` hash queries.
* **`admL_qBudT`**, **`admLN_qBudT`**: a last stage within the per-kind budget `QBud q q_E` (one
  slice pair, `ansP`; `N` slices, `ansPN`) is within `QBudT q q_E (totK M q)`.

The corollaries without a total budget are in `Theft/PlainTotalRom.lean`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset OracleComp OracleSpec

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## The kinds of the table points -/

section Kinds

/-- **The kinds of the table points** (and of the slice points, `H₃`). -/
def kindsT (M : ℕ) : Finset Kind :=
  {.h3, .h23, .h5, .h1, .mu, .muDelayed, .h4, .h21, .h22, .comb M}

/-- **The total hash budget from the per-kind budgets**: the sum over `kindsT M`. -/
def totK (M : ℕ) (q : Kind → ℕ) : ℕ := ∑ k ∈ kindsT M, q k

lemma totK_add (M : ℕ) (q q' : Kind → ℕ) : totK M (q + q') = totK M q + totK M q' := by
  simp [totK, Finset.sum_add_distrib]

lemma totK_nsmul (M n : ℕ) (q : Kind → ℕ) : totK M (n • q) = n * totK M q := by
  simp [totK, Finset.mul_sum]

variable {p : Params} {L M : ℕ}

set_option maxRecDepth 10000 in
lemma kind_mem_of_TPts {d : Dom} (hd : d ∈ TPts p L M) : d.1 ∈ kindsT M := by
  obtain ⟨k, rfl⟩ := (mem_TPts p L M).1 hd
  rcases k with a | a | a | a | a | a | a | a | a | a <;> simp [tpt, kindsT]

lemma kind_mem_of_slPt {N : ℕ} {d : Dom} (hd : SlPt N d) : d.1 ∈ kindsT M := by
  rw [hd.1]; simp [kindsT]

end Kinds

/-! ## The total from the kinds -/

section Total

variable {α : Type}

/-- A hash query of a kind in `K` (cipher queries are not restricted). -/
def KindIn (K : Finset Kind) : DomIC → Prop
  | .inl d => d.1 ∈ K
  | .inr _ => True

/-- **A computation whose hash queries all have kinds in `K` makes at most `Σ_{k ∈ K} q k` hash
queries.** -/
theorem isQueryBoundP_left_of_kinds {K : Finset Kind} {oa : OracleComp specIC α} {q : Kind → ℕ}
    (hK : AllQueriesSatisfy oa (KindIn K)) (h : IsKindQueryBoundIC oa q) :
    IsQueryBoundP oa (fun t => t.isLeft = true) (∑ k ∈ K, q k) := by
  classical
  induction oa generalizing q with
  | pure x => trivial
  | queryBind t k ih =>
    obtain ⟨ht, hk⟩ := (allQueriesSatisfy_query_bind_iff t k _).1 hK
    have h' := (isQueryBound_query_bind_iff t k q _ _).1 h
    rcases t with d | c
    · have hd : d.1 ∈ K := ht
      have hpos : 0 < q d.1 := h'.1
      have hsum : ∑ j ∈ K, Function.update q d.1 (q d.1 - 1) j = ∑ j ∈ K, q j - 1 := by
        rw [Finset.sum_update_of_mem hd, ← Finset.add_sum_erase K q hd,
          Finset.sdiff_singleton_eq_erase]
        omega
      refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr ?_, fun u => ?_⟩
      · exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hd)
      · have := ih u (hk u) (h'.2 u)
        rw [hsum] at this
        simpa using this
    · refine (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp), fun u => ?_⟩
      simpa using ih u (hk u) (h'.2 u)

end Total

/-! ## SHAKE answered locally off a set of points -/

section Norm

variable (S : Dom → Prop) [DecidablePred S] {α : Type}

/-- **`oa` with every hash query outside `S` answered locally by SHAKE** (cipher queries and hash
queries in `S` are made). -/
noncomputable def normS : OracleComp specIC α → OracleComp specIC α
  | .pure x => pure x
  | .queryBind (.inl d) k => if S d then
      liftM (specIC.query (.inl d)) >>= fun u => normS (k u) else normS (k (shakeAns d))
  | .queryBind (.inr c) k => liftM (specIC.query (.inr c)) >>= fun u => normS (k u)

variable {S}

lemma normS_inl_pos {d : Dom} (hd : S d) (k : AnsIC (.inl d) → OracleComp specIC α) :
    normS S (.queryBind (.inl d) k) = liftM (specIC.query (.inl d)) >>= fun u => normS S (k u) := by
  simp only [normS, hd, ite_true]

lemma normS_inl_neg {d : Dom} (hd : ¬ S d) (k : AnsIC (.inl d) → OracleComp specIC α) :
    normS S (.queryBind (.inl d) k) = normS S (k (shakeAns d)) := by
  simp only [normS, hd, ite_false]

/-- **On answers that are SHAKE outside `S`, the normalized run is the computation's.** -/
theorem runT_normS (f : (d : DomIC) → AnsIC d) (hf : ∀ d, ¬ S d → f (.inl d) = shakeAns d)
    (oa : OracleComp specIC α) : runT f (normS S oa) = runT f oa := by
  induction oa with
  | pure x => rfl
  | queryBind t k ih =>
    rcases t with d | c
    · by_cases hd : S d
      · rw [normS_inl_pos hd]
        exact ih (f (.inl d))
      · rw [normS_inl_neg hd]
        show runT f (normS S (k (shakeAns d))) = runT f (k (f (.inl d)))
        rw [hf d hd]
        exact ih _
    · exact ih (f (.inr c))

/-- The normalized computation makes hash queries in `S` only. -/
theorem allQueriesSatisfy_normS (oa : OracleComp specIC α) :
    AllQueriesSatisfy (normS S oa) fun t => match t with | .inl d => S d | .inr _ => True := by
  induction oa with
  | pure x => exact allQueriesSatisfy_pure _ _
  | queryBind t k ih =>
    rcases t with d | c
    · by_cases hd : S d
      · rw [normS_inl_pos hd]
        exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨hd, fun u => ih u⟩
      · rw [normS_inl_neg hd]
        exact ih _
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨trivial, fun u => ih u⟩

/-- The normalized computation keeps every query bound of a class. -/
theorem isQueryBoundP_normS {P : DomIC → Prop} [DecidablePred P] {oa : OracleComp specIC α}
    {n : ℕ} (h : IsQueryBoundP oa P n) : IsQueryBoundP (normS S oa) P n := by
  induction oa generalizing n with
  | pure x => trivial
  | queryBind t k ih =>
    have h' := (isQueryBoundP_query_bind_iff P t k n).1 h
    rcases t with d | c
    · by_cases hd : S d
      · rw [normS_inl_pos hd]
        exact (isQueryBoundP_query_bind_iff P _ _ n).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩
      · rw [normS_inl_neg hd]
        exact ih _ ((h'.2 _).mono (by split <;> omega))
    · exact (isQueryBoundP_query_bind_iff P _ _ n).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩

/-- The normalized computation keeps the per-kind hash bounds. -/
theorem isKindQueryBoundIC_normS {oa : OracleComp specIC α} {q : Kind → ℕ}
    (h : IsKindQueryBoundIC oa q) : IsKindQueryBoundIC (normS S oa) q := by
  induction oa generalizing q with
  | pure x => trivial
  | queryBind t k ih =>
    have h' := (isQueryBound_query_bind_iff t k q _ _).1 h
    rcases t with d | c
    · by_cases hd : S d
      · rw [normS_inl_pos hd]
        exact (isQueryBound_query_bind_iff _ _ q _ _).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩
      · rw [normS_inl_neg hd]
        refine ih _ ((show IsKindQueryBoundIC (k (shakeAns d)) (Function.update q d.1 (q d.1 - 1))
          from h'.2 _).mono fun k' => ?_)
        by_cases hk : k' = d.1
        · subst hk; simp
        · simp [Function.update_of_ne hk]
    · exact (isQueryBound_query_bind_iff _ _ q _ _).2 ⟨h'.1, fun u => ih u (h'.2 u)⟩

/-- **The normalized computation is within the total budget of its kinds.** -/
theorem qBudT_normS {K : Finset Kind} (hSK : ∀ d, S d → d.1 ∈ K) {oa : OracleComp specIC α}
    {q : Kind → ℕ} {qE : ℕ} (h : QBud q qE oa) : QBudT q qE (∑ k ∈ K, q k) (normS S oa) := by
  refine ⟨⟨isKindQueryBoundIC_normS h.1, isQueryBoundP_normS h.2⟩, ?_⟩
  refine isQueryBoundP_left_of_kinds ?_ (isKindQueryBoundIC_normS h.1)
  refine (allQueriesSatisfy_normS oa).mono ?_
  rintro (d | c) hd
  · exact hSK d hd
  · trivial

end Norm

/-! ## Last stages within the per-kind budget are within the total -/

section Adm

variable {R : Type} [CipherRow R] {p : Params} {L M : ℕ} {Out : Type}

/-- **One slice pair**: a last stage within `QBud q q_E` is within `QBudT q q_E (totK M q)`
(realized by the computation with the queries off the table points answered by SHAKE). -/
theorem admL_qBudT {q : Kind → ℕ} {qE : ℕ} {F : Tab3 → Tab3 → ShX R p (XTab L M) → Out}
    (h : AdmL (QBud q qE) ansP F) : AdmL (QBudT q qE (totK M q)) ansP F := by
  classical
  obtain ⟨oa, hb, rfl⟩ := h
  refine ⟨normS (· ∈ TPts p L M) oa, qBudT_normS (fun d hd => kind_mem_of_TPts hd) hb, ?_⟩
  funext g₁ g₂ t
  exact (runT_normS _ (fun d hd => tabP_off g₁ g₂ t hd) oa).symm

/-- **`N` slices**: a last stage within `QBud q q_E` is within `QBudT q q_E (totK M q)`. -/
theorem admLN_qBudT {N : ℕ} {q : Kind → ℕ} {qE : ℕ}
    {F : (Fin N → Tab3) → ShX R p (XTab L M) → Out}
    (h : AdmLN (QBud q qE) ansPN F) : AdmLN (QBudT q qE (totK M q)) ansPN F := by
  classical
  obtain ⟨oa, hb, rfl⟩ := h
  refine ⟨normS (fun d => d ∈ TPts p L M ∨ SlPt N d) oa,
    qBudT_normS (fun d hd => hd.elim kind_mem_of_TPts kind_mem_of_slPt) hb, ?_⟩
  funext g t
  refine (runT_normS _ (fun d hd => ?_) oa).symm
  have h1 : ¬ SlPt N d := fun h => hd (Or.inr h)
  show (if SlPt N d then slAns g d else tabP zT zT t d) = shakeAns d
  simp only [h1, ↓reduceIte]
  exact tabP_off _ _ _ fun h => hd (Or.inl h)

end Adm

end VoleMole.Theft
