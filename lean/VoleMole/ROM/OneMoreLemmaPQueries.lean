import VoleMole.ROM.OneMoreLemmaPIC

/-!
# The derived prover's queries

`lean/docs/security/pomfrit.md` §6.4 (gap G8). Query bounds of the verification part of the derived
prover `proverP … i` (`ROM/OneMoreLemmaPIC.lean`, `contP`): per verification, the hash queries of
`chal1PreIC` (`mu₁` and `iv` twice, the 18 `H₁` queries and `H₂¹`) and of the reduction's own
queries (`H₃`, `mu₁`, `iv`), so no `H₂²` and no `H₂³` query; at most 26 hash queries and
`verifyCellBound` cipher queries.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.OneMore.Pomfrit

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.ROM VoleMole.ROM.IC
open VoleMole.EndToEnd VoleMole.ZK.Sim

/-! ## Budgets -/

/-- The hash queries of `chal1Pre` per kind: `mu₁` (`H₂⁰` or `H₂⁴`), `iv`, the 17 leaf hashes and
`com` (`H₁`), `chal1` (`H₂¹`). -/
def c1Queries : Kind → ℕ
  | .mu => 1
  | .muDelayed => 1
  | .h4 => 1
  | .h1 => 18
  | .h21 => 1
  | _ => 0

/-- The reduction's own queries at a target query: `H₃`, `mu₁` (`H₂⁴`), `iv` (`H₄`). -/
def auxQueries : Kind → ℕ
  | .h3 => 1
  | .muDelayed => 1
  | .h4 => 1
  | _ => 0

/-- The hash queries of one verification of the derived prover. -/
def vQueries : Kind → ℕ := extractorQueries + c1Queries + auxQueries

lemma vQueries_h22 : vQueries .h22 = 0 := rfl
lemma vQueries_h23 : vQueries .h23 = 0 := rfl

/-! ## The pieces -/

section Pieces

lemma isKindQueryBound_chal1Pre [HasPrg] (st : Statement) (proof : ByteArray) :
    IsKindQueryBound (chal1Pre st proof) c1Queries := by
  unfold chal1Pre
  dsimp only
  split
  · trivial
  have hmu : ∀ {f : ByteArray → OracleComp spec (Option ByteArray)} {q : Kind → ℕ}, 0 < q .mu →
      0 < q .muDelayed → (∀ u, IsKindQueryBound (f u) (Function.update q .mu (q .mu - 1))) →
      (∀ u, IsKindQueryBound (f u) (Function.update q .muDelayed (q .muDelayed - 1))) →
      IsKindQueryBound (mu1Q st >>= f) q := by
    intro f q h1 h2 hf1 hf2
    unfold mu1Q
    split
    · exact isKindQueryBound_hashQ_bind_iff.2 ⟨h2, fun u => hf2 _⟩
    · exact isKindQueryBound_hashQ_bind_iff.2 ⟨h1, fun u => hf1 _⟩
  refine hmu (by decide) (by decide) (fun mu1 => ?_) (fun mu1 => ?_)
  all_goals
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [c1Queries], fun iv => ?_⟩
    split
    · trivial
    refine isKindQueryBound_mapM_hashQ_bind _ _
      (by simp [c1Queries, length_leafHashInputs]) fun lh => ?_
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨by
      simp [c1Queries, length_leafHashInputs], fun com => ?_⟩
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [c1Queries], fun c1 => trivial⟩

lemma isTotalQueryBound_chal1Pre [HasPrg] (st : Statement) (proof : ByteArray) :
    IsTotalQueryBound (chal1Pre st proof) 21 := by
  unfold chal1Pre
  dsimp only
  split
  · trivial
  have hmu : ∀ {f : ByteArray → OracleComp spec (Option ByteArray)} {n : ℕ}, 0 < n →
      (∀ u, IsTotalQueryBound (f u) (n - 1)) → IsTotalQueryBound (mu1Q st >>= f) n := by
    intro f n h hf
    unfold mu1Q
    split <;> exact isTotalQueryBound_hashQ_bind_iff.2 ⟨h, fun u => hf _⟩
  refine hmu (by decide) fun mu1 => ?_
  refine isTotalQueryBound_hashQ_bind_iff.2 ⟨by decide, fun iv => ?_⟩
  split
  · trivial
  refine isTotalQueryBound_mapM_hashQ_bind _ _ (by simp [length_leafHashInputs]) fun lh => ?_
  simp only [length_leafHashInputs]
  refine isTotalQueryBound_hashQ_bind_iff.2 ⟨by decide, fun com => ?_⟩
  exact isTotalQueryBound_hashQ_bind_iff.2 ⟨by decide, fun c1 => trivial⟩

lemma isKindQueryBound_auxSpec (lr : Bool) (L : QueryLog specIC) (x : ByteArray) :
    IsKindQueryBound (auxSpec lr L x) auxQueries := by
  unfold auxSpec
  refine isKindQueryBound_query_bind_iff.2 ⟨by simp [auxQueries], fun u3 => ?_⟩
  refine isKindQueryBound_query_bind_iff.2 ⟨by simp [auxQueries, muCell], fun um => ?_⟩
  split
  · exact isKindQueryBound_query_bind_iff.2 ⟨by simp [auxQueries, muCell, ivCell], fun ui => trivial⟩
  · trivial

lemma isTotalQueryBound_auxSpec (lr : Bool) (L : QueryLog specIC) (x : ByteArray) :
    IsTotalQueryBound (auxSpec lr L x) 3 := by
  unfold auxSpec
  refine isTotalQueryBound_query_bind_iff.2 ⟨by decide, fun u3 => ?_⟩
  refine isTotalQueryBound_query_bind_iff.2 ⟨by decide, fun um => ?_⟩
  split
  · exact isTotalQueryBound_query_bind_iff.2 ⟨by decide, fun ui => trivial⟩
  · trivial

lemma toHIC_eq_liftIC {α : Type} (oa : OracleComp spec α) : toHIC oa = liftIC oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [liftIC_query_bind]
    simp only [toHIC, simulateQ_bind, simulateQ_spec_query, liftHIC] at ih ⊢
    refine congrArg _ (funext fun u => ih u)

lemma isKindQueryBoundIC_chal1PreIC (st : Statement) (proof : ByteArray) :
    IsKindQueryBoundIC (chal1PreIC st proof) (extractorQueries + c1Queries) := by
  unfold chal1PreIC
  refine isKindQueryBoundIC_bind (isKindQueryBoundIC_liftIC (isKindQueryBound_ivQ st proof))
    fun iv => ?_
  refine (isKindQueryBoundIC_bind (q₁ := 0) (q₂ := c1Queries)
    (isKindQueryBoundIC_treeQ _ _ _) fun A => ?_).mono (by simp only [zero_add, le_refl])
  refine (isKindQueryBoundIC_bind (q₁ := 0) (q₂ := c1Queries)
    (isKindQueryBoundIC_cellsQ _ _ _) fun M => ?_).mono (by simp only [zero_add, le_refl])
  exact isKindQueryBoundIC_liftIC (@isKindQueryBound_chal1Pre (icPrg (fillC M)) st proof)

lemma isQueryBoundP_left_chal1PreIC (st : Statement) (proof : ByteArray) :
    IsQueryBoundP (chal1PreIC st proof) (fun t => t.isLeft = true) (2 + 21) := by
  unfold chal1PreIC
  refine isQueryBoundP_bind (isQueryBoundP_left_liftIC (isTotalQueryBound_ivQ st proof))
    fun iv _ => ?_
  refine (isQueryBoundP_bind (n := 0) (m := 21) (isQueryBoundP_left_treeQ _ _ _)
    fun A _ => ?_).mono (by simp only [zero_add, le_refl])
  refine (isQueryBoundP_bind (n := 0) (m := 21) (isQueryBoundP_left_cellsQ _ _ _)
    fun M _ => ?_).mono (by simp only [zero_add, le_refl])
  exact isQueryBoundP_left_liftIC (@isTotalQueryBound_chal1Pre (icPrg (fillC M)) st proof)

lemma isQueryBoundP_right_chal1PreIC (st : Statement) (proof : ByteArray) :
    IsQueryBoundP (chal1PreIC st proof) (fun t => t.isRight = true) (verifyCellBound st.params) := by
  unfold chal1PreIC
  refine (isQueryBoundP_bind (n := 0) (m := verifyCellBound st.params)
    (isQueryBoundP_right_liftIC (ivQ st proof)) fun iv _ => ?_).mono
    (by simp only [zero_add, le_refl])
  refine isQueryBoundP_bind (n := 2 * (BAVC.numLeaves - 1)) (isQueryBoundP_right_treeQ _ _ _)
    fun A _ => ?_
  exact (isQueryBoundP_bind (m := 0) (isQueryBoundP_right_cellsQ _ _ _) fun M _ =>
      isQueryBoundP_right_liftIC _).mono (by simp only [add_zero, le_refl])

end Pieces

/-! ## One verification, the verification part -/

section Ver

variable (lr : Bool) (pk : UovPk)

/-- The cipher queries of one verification. -/
abbrev vCells (lr : Bool) : ℕ := verifyCellBound (pomfritParams lr)

lemma isKindQueryBoundIC_toHIC_auxSpec (L : QueryLog specIC) (x : ByteArray) :
    IsKindQueryBoundIC (toHIC (auxSpec lr L x)) auxQueries := by
  rw [toHIC_eq_liftIC]; exact isKindQueryBoundIC_liftIC (isKindQueryBound_auxSpec lr L x)

lemma isQueryBoundP_left_toHIC_auxSpec (L : QueryLog specIC) (x : ByteArray) :
    IsQueryBoundP (toHIC (auxSpec lr L x)) (fun t => t.isLeft = true) 3 := by
  rw [toHIC_eq_liftIC]; exact isQueryBoundP_left_liftIC (isTotalQueryBound_auxSpec lr L x)

lemma isQueryBoundP_right_toHIC_auxSpec (L : QueryLog specIC) (x : ByteArray) :
    IsQueryBoundP (toHIC (auxSpec lr L x)) (fun t => t.isRight = true) 0 := by
  rw [toHIC_eq_liftIC]; exact isQueryBoundP_right_liftIC _

/-- A query bound of `chal1PreIC` followed by a computation that, on `some`, makes the reduction's
queries. -/
lemma isKindQueryBoundIC_c1_aux {γ : Type} (st : Statement) (proof : ByteArray) (L : QueryLog specIC)
    (xf : ByteArray → ByteArray) (dflt : γ) (f : ByteArray → QueryLog specIC → γ) :
    IsKindQueryBoundIC (chal1PreIC st proof >>= fun oc1 => match oc1 with
      | none => pure dflt
      | some c1 => toHIC (auxSpec lr L (xf c1)) >>= fun ax => pure (f c1 ax)) vQueries := by
  refine isKindQueryBoundIC_bind (isKindQueryBoundIC_chal1PreIC st proof) fun oc1 => ?_
  cases oc1 with
  | none => trivial
  | some c1 =>
    refine (isKindQueryBoundIC_bind (q₂ := 0) (isKindQueryBoundIC_toHIC_auxSpec lr L _)
      fun _ => ?_).mono (by simp only [add_zero, le_refl])
    trivial

lemma isQueryBoundP_left_c1_aux {γ : Type} (st : Statement) (proof : ByteArray) (L : QueryLog specIC)
    (xf : ByteArray → ByteArray) (dflt : γ) (f : ByteArray → QueryLog specIC → γ) :
    IsQueryBoundP (chal1PreIC st proof >>= fun oc1 => match oc1 with
      | none => pure dflt
      | some c1 => toHIC (auxSpec lr L (xf c1)) >>= fun ax => pure (f c1 ax))
      (fun t => t.isLeft = true) 26 := by
  refine isQueryBoundP_bind (n := 2 + 21) (m := 3) (isQueryBoundP_left_chal1PreIC st proof)
    fun oc1 _ => ?_
  cases oc1 with
  | none => exact isQueryBoundP_pure _ _ _
  | some c1 =>
    exact (isQueryBoundP_bind (n := 3) (m := 0) (isQueryBoundP_left_toHIC_auxSpec lr L _)
      fun _ _ => isQueryBoundP_pure _ _ _).mono (by omega)

lemma isQueryBoundP_right_c1_aux {γ : Type} (st : Statement) (proof : ByteArray) (L : QueryLog specIC)
    (xf : ByteArray → ByteArray) (dflt : γ) (f : ByteArray → QueryLog specIC → γ) :
    IsQueryBoundP (chal1PreIC st proof >>= fun oc1 => match oc1 with
      | none => pure dflt
      | some c1 => toHIC (auxSpec lr L (xf c1)) >>= fun ax => pure (f c1 ax))
      (fun t => t.isRight = true) (verifyCellBound st.params) := by
  refine (isQueryBoundP_bind (m := 0) (isQueryBoundP_right_chal1PreIC st proof)
    fun oc1 _ => ?_).mono (by simp only [add_zero, le_refl])
  cases oc1 with
  | none => exact isQueryBoundP_pure _ _ _
  | some c1 =>
    exact (isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_right_toHIC_auxSpec lr L _)
      fun _ _ => isQueryBoundP_pure _ _ _)

/-- The three query bounds of one verification. -/
structure VBound {γ : Type} (oa : OracleComp specIC γ) (k : ℕ) (lr : Bool) : Prop where
  kinds : IsKindQueryBoundIC oa (fun j => k * vQueries j)
  left : IsQueryBoundP oa (fun t => t.isLeft = true) (k * 26)
  right : IsQueryBoundP oa (fun t => t.isRight = true) (k * vCells lr)

lemma VBound.bind {γ δ : Type} {oa : OracleComp specIC γ} {ob : γ → OracleComp specIC δ}
    {k m : ℕ} (h : VBound oa k lr) (h' : ∀ c, VBound (ob c) m lr) : VBound (oa >>= ob) (k + m) lr where
  kinds := (isKindQueryBoundIC_bind h.kinds fun c => (h' c).kinds).mono fun j => by
    simp only [Pi.add_apply]; rw [Nat.add_mul]
  left := (isQueryBoundP_bind h.left fun c _ => (h' c).left).mono (by rw [Nat.add_mul])
  right := (isQueryBoundP_bind h.right fun c _ => (h' c).right).mono (by rw [Nat.add_mul])

lemma VBound.mono {γ : Type} {oa : OracleComp specIC γ} {k m : ℕ} (h : VBound oa k lr)
    (hkm : k ≤ m) : VBound oa m lr where
  kinds := h.kinds.mono fun _ => Nat.mul_le_mul_right _ hkm
  left := h.left.mono (Nat.mul_le_mul_right _ hkm)
  right := h.right.mono (Nat.mul_le_mul_right _ hkm)

lemma vBound_pure {γ : Type} (c : γ) (k : ℕ) : VBound (pure c : OracleComp specIC γ) k lr :=
  ⟨trivial, isQueryBoundP_pure _ _ _, isQueryBoundP_pure _ _ _⟩

lemma vBound_c1_aux {γ : Type} (st : Statement) (hst : st.params = pomfritParams lr)
    (proof : ByteArray) (L : QueryLog specIC)
    (xf : ByteArray → ByteArray) (dflt : γ) (f : ByteArray → QueryLog specIC → γ) :
    VBound (chal1PreIC st proof >>= fun oc1 => match oc1 with
      | none => pure dflt
      | some c1 => toHIC (auxSpec lr L (xf c1)) >>= fun ax => pure (f c1 ax)) 1 lr where
  kinds := (isKindQueryBoundIC_c1_aux lr st proof L xf dflt f).mono fun j => by simp
  left := (isQueryBoundP_left_c1_aux lr st proof L xf dflt f).mono (by simp)
  right := (isQueryBoundP_right_c1_aux lr st proof L xf dflt f).mono (by simp [vCells, hst])

lemma vBound_verPreIC (L : QueryLog specIC) (m sg : ByteArray) (s : HTS × Gh) :
    VBound (verPreIC lr pk L m sg s) 1 lr := by
  unfold verPreIC
  split
  · exact vBound_pure lr _ _
  · exact vBound_c1_aux lr _ rfl _ L (fun c1 => tgtIn pk lr sg m c1) s
      (fun c1 ax => ((tStep addHint (tgtIn pk lr sg m c1) 0 s.1).2,
        ghStep s.1 s.2 (tgtIn pk lr sg m c1) (L ++ ax)))

lemma vBound_verPreAll (L : QueryLog specIC) :
    ∀ (l : List (ByteArray × ByteArray)) (s : HTS × Gh), VBound (verPreAll lr pk L l s) l.length lr
  | [], s => vBound_pure lr _ _
  | (m, sg) :: rest, s => by
    simp only [verPreAll, List.length_cons]
    rw [Nat.add_comm]
    exact (vBound_verPreIC lr pk L m sg s).bind lr fun s' => vBound_verPreAll L rest s'

lemma vBound_verLastIC (L : QueryLog specIC) (ms : ByteArray × ByteArray) (s : HTS × Gh) :
    VBound (verLastIC lr pk L ms s) 1 lr :=
  vBound_c1_aux lr _ rfl _ L (fun c1 => tgtIn pk lr ms.2 ms.1 c1) _ _

/-- **The verification part of the derived prover makes at most `i + 1` verifications' queries.** -/
theorem vBound_contP (i : ℕ) (r : List (ByteArray × ByteArray) × QueryLog specIC × HTS × Gh) :
    VBound (contP lr pk i r) (i + 1) lr :=
  ((vBound_verPreAll lr pk r.2.1 (r.1.take i) (r.2.2.1, r.2.2.2)).bind lr fun s =>
    vBound_verLastIC lr pk r.2.1 _ s).mono lr (by simp)

/-- **The verification part makes no `H₂²` and no `H₂³` query.** -/
theorem not_mem_hashLog_contP (i : ℕ) (r : List (ByteArray × ByteArray) × QueryLog specIC × HTS × Gh)
    (f : (t : DomIC) → AnsIC t) (z : ByteArray) :
    ((.h23, z) : Dom) ∉ hashLog (tableQueryLog (contP lr pk i r) f) := by
  intro hz
  have h := length_kindIns_hashLog_le _ (vBound_contP lr pk i r).kinds f .h23
  have h0 : kindIns .h23 (hashLog (tableQueryLog (contP lr pk i r) f)) = [] :=
    List.length_eq_zero_iff.1 (by simpa [vQueries_h23] using h)
  have := mem_kindIns hz
  rw [h0] at this
  exact List.not_mem_nil this

end Ver

end VoleMole.ROM.OneMore.Pomfrit
