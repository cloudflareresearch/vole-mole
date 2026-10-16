import VoleMole.ROM.Chains
import VoleMole.ROM.Fresh

/-!
# The combined relations: `chal2` and `l = H(chal2 ‖ dst)` over all queries (plan M5)

For the combined relations (Moussaka and Ratatouille redemption/spend, PomFRIT) the system checked
at an `H₂²` query depends on the UOV combination `l = H_comb(chal2 ‖ dst)`, the answer of a
second cell chosen by the `H₂²` answer. `ROM/Chains.lean`'s single-cell bound does not apply.
Here the `H₂²` query is bad if, at the canonical witness `w*` and `l` read from the table,
* the system fails and `zkHash = 0` (L4, `hQS`), or
* the system holds but the relation does not (L4, `hcomb`).

**The bound** (`prEvent_combBad_h22_le`): at a fresh `H₂²` query, over the answer table with a
cache of fewer than `n` cells, this has probability `≤ ε_QS(n') + ε_c + n·2⁻⁴⁴⁸`. Proof: expose the
`H₂²` cell `u` and then the cell `u ‖ dst` (`prEvent_completeTable_le_two_cells`); the second cell
is cached with probability `≤ n·2⁻⁴⁴⁸` (`u ↦ u ‖ dst` is injective; this is the freshness term of
L0 §2.2), and otherwise `(chal2, l)` are independent uniform answers and M2's
`prU_qs_bad_le`, `prU_comb_bad_le` apply (QS with `u` drawn last, the combination with `l` drawn
last).

**The assembled bound** (`prEvent_le_comb_terms`), through `ROM/Fresh.lean`:

  `Pr[event] ≤ q₁·ε_KOS + q₂·(ε_QS(n') + ε_c + n·2⁻⁴⁴⁸) + Q·N·2⁻¹²⁸ + ε_bind + ε_dead`

for an adversary with at most `n` queries in total and `q₁`, `q₂`, `Q` to `H₂¹`, `H₂²`, `H₂³`.

The chain data at an `H₂²` query (`midOf`, the system at a free `l`, the witness predicate) must
read neither the `H₂²` answer nor any combination cell.

**The relations**: `moussakaRedeem_prEvent_le`, `ratatouilleSpend_prEvent_le`,
`pomfritRedeem_prEvent_le` (`ε_c = 2⁻¹²⁸` from `*_comb_bad_gf128`; PomFRIT's system and target
read the chain's `chal1`), and the deterministic per-chain step `comb_good_of_not_bad`,
`pomfritRedeem_good_of_not_bad` (as `ROM/Chains.lean`'s, with `l` read from the table).
-/

open Finset ENNReal

namespace VoleMole.ROM

-- The statements hold for any CTR PRG (`HasPrg`, `Verifier/Prg.lean`), AES included.
variable [VoleMole.Verifier.HasPrg]

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.EndToEnd VoleMole.SeedExtraction OracleComp OracleSpec

/-- The combination cell `H_comb(chal2 ‖ dst)` of a relation combining `M` equations. -/
def combKey (M : ℕ) (dst : ByteArray) (u : Bytes 56) : Dom := (.comb M, u.ba ++ dst)

omit [VoleMole.Verifier.HasPrg] in
theorem Bytes.ba_injective {n : ℕ} : Function.Injective (Bytes.ba (n := n)) := by
  intro b b' h
  have : Array.ofFn b = Array.ofFn b' := congrArg ByteArray.data h
  funext i
  have := congrArg (fun a : Array UInt8 => a[i.val]!) this
  simpa using this

omit [VoleMole.Verifier.HasPrg] in
theorem combKey_injective (M : ℕ) (dst : ByteArray) : Function.Injective (combKey M dst) := by
  intro u u' h
  simp only [combKey, Prod.mk.injEq, true_and] at h
  exact Bytes.ba_injective ((ByteArray.append_left_inj dst).1 h)

/-- The data a combined relation's random-oracle queries commit to (`ChainData`, with the system
at a free combination vector and the witness predicate of `hcomb`). -/
structure CombData (st : Statement) (M : ℕ) where
  /-- The chain prefix committed at an `H₂¹` query. -/
  preOf : ByteArray → Table → Chain
  /-- The chain data up to `chal2` committed at an `H₂²` query. -/
  midOf : ByteArray → Table → Chain
  /-- The system checked at an `H₂²` query, at a combination vector `l`. -/
  sysOf : ByteArray → Table → (Fin M → GF128) → System GF128
  /-- The relation the combined system stands for, at a witness. -/
  witOf : ByteArray → Table → (ℕ → GF128) → Prop
  /-- The accepted `chal3` values at an `H₂³` query. -/
  accOf : ByteArray → Table → Bytes 16 → Prop
  /-- The relation's combination domain separator. -/
  dst : ByteArray

namespace CombData

variable {st : Statement} {M : ℕ} (C : CombData st M)

/-- The data at each query reads neither the query's own answer nor, at `H₂²`, a combination
cell. -/
structure Committed : Prop where
  pre : ∀ x (g : Table) u, C.preOf x (Function.update g (.h21, x) u) = C.preOf x g
  acc : ∀ z (g : Table) u, C.accOf z (Function.update g (.h23, z) u) = C.accOf z g
  mid : ∀ y (g : Table) u, C.midOf y (Function.update g (.h22, y) u) = C.midOf y g
  midComb : ∀ y (g : Table) x v, C.midOf y (Function.update g (.comb M, x) v) = C.midOf y g
  sys : ∀ y (g : Table) u, C.sysOf y (Function.update g (.h22, y) u) = C.sysOf y g
  sysComb : ∀ y (g : Table) x v, C.sysOf y (Function.update g (.comb M, x) v) = C.sysOf y g
  wit : ∀ y (g : Table) u, C.witOf y (Function.update g (.h22, y) u) = C.witOf y g
  witComb : ∀ y (g : Table) x v, C.witOf y (Function.update g (.comb M, x) v) = C.witOf y g

/-- The `H₂¹` and `H₂³` parts, as a `ChainData` (its system is unused). -/
def toChainData : ChainData st where
  preOf := C.preOf
  midOf := C.midOf
  csOf := fun _ _ => []
  accOf := C.accOf

omit [VoleMole.Verifier.HasPrg] in
lemma toChainData_committed (hC : C.Committed) : C.toChainData.Committed where
  pre := hC.pre
  mid := hC.mid
  cs := fun _ _ _ => rfl
  acc := hC.acc

/-- The canonical witness `w* = uCanon + d` at an `H₂²` query. -/
noncomputable def wC (T : CrtTables) (S : Finset Blocks) (y : ByteArray) (g : Table) :
    ℕ → GF128 :=
  wStar ((C.midOf y g).uCanon st T S) ((C.midOf y g).dc st)

/-- The `H₂²` event at `chal2 = u` and combination bytes `v`, for the chain data of table `g`. -/
def qsComb (T : CrtTables) (S : Finset Blocks) (y : ByteArray) (g : Table) (u : Bytes 56)
    (v : Bytes (16 * M)) : Prop :=
  (¬(C.sysOf y g (combDec v)).Holds (C.wC T S y g) ∧
    Seed.zkHash (C.sysOf y g (combDec v)).length (gfOfBytes u.ba 0) (gfOfBytes u.ba 16)
      (gfOfBytes u.ba 32) ⟨W128.word u.ba 48, 0⟩
      (valVec (C.sysOf y g (combDec v)) (C.wC T S y g)) = 0) ∨
  ((C.sysOf y g (combDec v)).Holds (C.wC T S y g) ∧ ¬C.witOf y g (C.wC T S y g))

end CombData

/-- **The bad queries of a combined relation**: at `H₂²`, the QS or combination failure at
`chal2 = g(H₂², y)` and `l = g(H_comb, chal2 ‖ dst)`; elsewhere those of `chainBad`. -/
def combBad {st : Statement} {M : ℕ} (C : CombData st M) (T : CrtTables) (S : Finset Blocks)
    (N : ℕ) (t : Dom) (g : Table) : Prop :=
  if t.1 = .h22 then C.qsComb T S t.2 g (g (.h22, t.2)) (g (combKey M C.dst (g (.h22, t.2))))
  else chainBad C.toChainData T S N t g

/-! ## The `H₂²` bound -/

section Keys

variable {st : Statement} {M : ℕ} (C : CombData st M) (K : Finset Dom)

/-- The `H₂²` event at a table `Y` whose `H₂²(y)` answer is `u`, whose `H_comb(u ‖ dst)` answer is
`v`, and whose chain data are those of `X`. -/
lemma combBad_h22_iff (T : CrtTables) (S : Finset Blocks) (N : ℕ) {y : ByteArray} {Y X : Table}
    {u : Bytes 56} {v : Ans (combKey M C.dst u)} (hu : Y (.h22, y) = u)
    (hv : Y (combKey M C.dst u) = v) (hmid : C.midOf y Y = C.midOf y X)
    (hsys : C.sysOf y Y = C.sysOf y X) (hwit : C.witOf y Y = C.witOf y X) :
    combBad C T S N (.h22, y) Y ↔ C.qsComb T S y X u v := by
  subst hv hu
  simp only [combBad, ite_true, CombData.qsComb, CombData.wC]
  rw [hmid, hsys, hwit]

/-- The `H₂²` event at a table where the cells `H₂²(y)` and `H_comb(u ‖ dst)`, both uncached,
were set to `u` and `v`: the chain data are those of the table without them. -/
lemma combBad_h22_update (hC : C.Committed) (T : CrtTables) (S : Finset Blocks) (N : ℕ)
    (hK : ∀ u, combKey M C.dst u ∈ K) {y : ByteArray} (hy : ((.h22, y) : Dom) ∈ K)
    (c : (ofFn fun d : K => Ans d.val).QueryCache) (hc : c ⟨_, hy⟩ = none) (u : Ans (.h22, y))
    (v : Ans (combKey M C.dst u)) (hv : c ⟨_, hK u⟩ = none) (g : (d : K) → Ans d.val) :
    combBad C T S N (.h22, y) (extendTable K (completeTable c
        (Function.update (Function.update g ⟨_, hK u⟩ v) ⟨_, hy⟩ u))) ↔
      C.qsComb T S y (extendTable K (completeTable c g)) u v := by
  rw [← completeTable_update_of_none c _ hc, ← completeTable_update_of_none c _ hv,
    extendTable_update, extendTable_update]
  have hne : combKey M C.dst u ≠ (.h22, y) := fun h => by cases congrArg Prod.fst h
  refine combBad_h22_iff C T S N (Function.update_self _ _ _) ?_ ?_ ?_ ?_
  · exact (Function.update_of_ne hne _ _).trans (Function.update_self _ _ _)
  · exact (hC.mid _ _ _).trans (hC.midComb _ _ _ _)
  · exact (hC.sys _ _ _).trans (hC.sysComb _ _ _ _)
  · exact (hC.wit _ _ _).trans (hC.witComb _ _ _ _)

set_option exponentiation.threshold 500 in
/-- **The `H₂²` bound of a combined relation**, on the tables over a finite key set `K` holding
every combination cell: at a fresh `H₂²` query, with fewer than `n` cached cells, the QS or
combination failure has probability `≤ ε_QS(n') + ε_c + n·2⁻⁴⁴⁸`. -/
theorem prEvent_combBad_h22_le (hC : C.Committed) (T : CrtTables) (S : Finset Blocks) (N : ℕ)
    {n' : ℕ} (hn' : ∀ y g l, (C.sysOf y g l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ y g w, prU (Fin M → GF128) (fun l => (C.sysOf y g l).Holds w ∧ ¬C.witOf y g w) ≤ εc)
    [SampleableType ((d : K) → Ans d.val)] (hK : ∀ u, combKey M C.dst u ∈ K) {y : ByteArray}
    (hy : ((.h22, y) : Dom) ∈ K) (c : (ofFn fun d : K => Ans d.val).QueryCache)
    (hc : c ⟨_, hy⟩ = none) {n : ℕ} (hcard : (cachedKeys c).card < n) :
    Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[
      combBad C T S N (.h22, y) (extendTable K (completeTable c g))] ≤
      ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc + (n : ℝ≥0∞) / 2 ^ 448 := by
  let t : K := ⟨_, hy⟩
  let p : Ans t.val → K := fun u => ⟨combKey M C.dst u, hK u⟩
  have hp : Function.Injective p := fun u u' h =>
    combKey_injective M C.dst (congrArg Subtype.val h)
  refine (prEvent_completeTable_le_two_cells c t p
    (fun G => combBad C T S N (.h22, y) (extendTable K G))).trans ?_
  rw [add_comm (ENNReal.ofReal _ + εc)]
  refine add_le_add ?_ ?_
  · refine (prEvent_isSome_le c p hp).trans ?_
    have hcardU : Fintype.card (Ans t.val) = 2 ^ 448 := card_bytes 56
    rw [hcardU, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.div_le_div_right (by exact_mod_cast hcard.le) _
  · let X : ((d : K) → Ans d.val) → Table := fun g => extendTable K (completeTable c g)
    change Pr{let u ← $ᵗ (Bytes 56); let v ← $ᵗ (Bytes (16 * M)); let g ← $ᵗ ((d : K) → Ans d.val)}[
          c (p u) = none ∧ combBad C T S N (.h22, y)
          (extendTable K (completeTable c (Function.update (Function.update g (p u) v) t u)))] ≤ _
    refine (prEvent_three_mono (Q := fun u v g =>
      (¬(C.sysOf y (X g) (combDec v)).Holds (C.wC T S y (X g)) ∧
        Seed.zkHash (C.sysOf y (X g) (combDec v)).length (gfOfBytes u.ba 0) (gfOfBytes u.ba 16)
          (gfOfBytes u.ba 32) ⟨W128.word u.ba 48, 0⟩
          (valVec (C.sysOf y (X g) (combDec v)) (C.wC T S y (X g))) = 0) ∨
      ((C.sysOf y (X g) (combDec v)).Holds (C.wC T S y (X g)) ∧
        ¬C.witOf y (X g) (C.wC T S y (X g)))) ?_).trans ?_
    · intro u v g h
      have key := combBad_h22_update C K hC T S N hK hy c hc u v h.1 g
      exact key.1 h.2
    refine (prEvent_three_or_le _ _).trans (add_le_add ?_ ?_)
    · refine prEvent_three_le_of_first _ fun v g => prEvent_uniformSample_le ?_
      exact (prU_qs_bad_le _ _).trans_eq (by rw [hn'])
    · refine prEvent_three_le_of_second (fun v g =>
        (C.sysOf y (X g) (combDec v)).Holds (C.wC T S y (X g)) ∧
          ¬C.witOf y (X g) (C.wC T S y (X g))) fun g => prEvent_uniformSample_le ?_
      have := hεc y (X g) (C.wC T S y (X g))
      rwa [prU_map_equiv (combEquiv M)] at this

end Keys

/-! ## The assembled bound -/

/-- The per-query charge of each domain for a combined relation: `ε_KOS`,
`ε_QS(n') + ε_c + n·2⁻⁴⁴⁸`, `N·2⁻¹²⁸`, and `0` elsewhere. -/
noncomputable def combEps (st : Statement) (S : Finset Blocks) (n' : ℕ) (εc : ℝ≥0∞) (n N : ℕ) :
    Kind → ℝ≥0∞
  | .h21 => epsKOS #S (Chain.kosL st)
  | .h22 => ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc + (n : ℝ≥0∞) / 2 ^ 448
  | .h23 => (N : ℝ≥0∞) / 2 ^ 128
  | _ => 0

omit [VoleMole.Verifier.HasPrg] in
lemma combEps_eq_zero (st : Statement) (S : Finset Blocks) (n' : ℕ) (εc : ℝ≥0∞) (n N : ℕ) :
    ∀ k ∉ chainKinds, combEps st S n' εc n N k = 0 := by
  intro k hk
  cases k <;> simp_all [chainKinds, combEps]

set_option exponentiation.threshold 500 in
-- `Finset.univ : Finset (Bytes 56)` (the combination cells) needs a deeper recursion to elaborate.
set_option maxRecDepth 4000 in
/-- **The per-chain terms over all queries, combined relations.** An adversary `oa` with at most
`n` queries in total and `q k` to each domain, against the lazy random oracle. If, outside the
binding failure and the dead-leaf failure, the event implies a bad query (`combBad`: KOS at
`H₂¹`, QS or combination at `H₂²` with `l` read from the table, few accepted at `H₂³`) for every
complete answer table, then
`Pr[event] ≤ q₁·ε_KOS + q₂·(ε_QS(n') + ε_c + n·2⁻⁴⁴⁸) + Q·N·2⁻¹²⁸ + ε_bind + ε_dead`. -/
theorem prEvent_le_comb_terms {α : Type} {T : CrtTables} (hT : liftInvOk T = true)
    {st : Statement} {M : ℕ} (C : CombData st M) (hC : C.Committed) (S : Finset Blocks)
    {n' : ℕ} (hn' : ∀ y g l, (C.sysOf y g l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ y g w, prU (Fin M → GF128) (fun l => (C.sysOf y g l).Holds w ∧ ¬C.witOf y g w) ≤ εc)
    (N : ℕ) (oa : OracleComp spec α) (n : ℕ) (hn : IsTotalQueryBound oa n) (q : Kind → ℕ)
    (hq : IsKindQueryBound oa q) (event bindFail deadFail : α → Prop) {εb εd : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[bindFail r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[deadFail r] ≤ εd)
    (htrace : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) oa;
      event r → ¬bindFail r → ¬deadFail r → ∃ e ∈ tableQueryLog oa g, combBad C T S N e.1 g) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤
      q .h21 * epsKOS #S (Chain.kosL st) +
        q .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc + (n : ℝ≥0∞) / 2 ^ 448) +
        q .h23 * ((N : ℝ≥0∞) / 2 ^ 128) + εb + εd := by
  let mx := (simulateQ randomOracle oa).run' ∅
  let K : Finset Dom := possibleQueryKeys oa ∪ Finset.univ.image (combKey M C.dst)
  have hK : ∀ u, combKey M C.dst u ∈ K := fun u =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  have hS : AllQueriesSatisfy oa (· ∈ K) :=
    (allQueriesSatisfy_possibleQueryKeys oa).mono fun d h => Finset.mem_union_left _ h
  let : SampleableType ((d : K) → Ans d.val) := SampleableType.piOfFintype _
  have hgood : Pr{let r ← mx}[event r ∧ ¬bindFail r ∧ ¬deadFail r] ≤
      q .h21 * epsKOS #S (Chain.kosL st) +
        q .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc + (n : ℝ≥0∞) / 2 ^ 448) +
        q .h23 * ((N : ℝ≥0∞) / 2 ^ 128) := by
    refine (prEvent_randomOracle_le_of_fresh_bad_queries oa K hS
      (fun t => combEps st S n' εc n N t.1) _
      (worstCaseCostBound_of_kindQueryBound oa chainKinds _ (combEps_eq_zero st S n' εc n N) q hq)
      n hn _ (combBad C T S N) ?_ fun g h => htrace g h.1 h.2.1 h.2.2).trans_eq ?_
    · rintro c ⟨⟨k, x⟩, hx⟩ hc hcard
      cases k
      case h22 => exact prEvent_combBad_h22_le C K hC T S N hn' hεc hK hx c hc hcard
      case h21 | h23 =>
        refine prEvent_completeTable_cell_le c _ hc
          (fun t G => combBad C T S N t.val (extendTable K G)) _ fun G => ?_
        simp only [extendTable_update, combBad, reduceCtorEq, ite_false]
        exact prEvent_chainBad_update_le hT C.toChainData (C.toChainData_committed hC) S
          (n := 0) (fun _ _ => rfl) N _ _
      all_goals
        refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun G h => ?_) zero_le
        simp [combBad, chainBad] at h
    · simp [chainKinds, combEps, add_assoc]
  calc Pr{let r ← mx}[event r]
      ≤ Pr{let r ← mx}[(event r ∧ ¬bindFail r ∧ ¬deadFail r) ∨ (bindFail r ∨ deadFail r)] :=
        prEvent_mono mx _ _ fun r h => by tauto
    _ ≤ Pr{let r ← mx}[event r ∧ ¬bindFail r ∧ ¬deadFail r] +
          (Pr{let r ← mx}[bindFail r] + Pr{let r ← mx}[deadFail r]) :=
        (prEvent_or_le mx _ _).trans (add_le_add le_rfl (prEvent_or_le mx _ _))
    _ ≤ _ := by
        rw [← add_assoc]
        exact add_le_add (add_le_add hgood hbind) hdead

/-! ## The deterministic step at one chain -/

/-- **A chain of a combined relation whose `H₂¹` and `H₂²` queries are not bad satisfies the
extraction theorem's conclusion** (`chain_good_of_not_bad` with `hcomb`): the chain's `l` is the
combination read from the table at `chal2 ‖ dst`. -/
theorem comb_good_of_not_bad {T : CrtTables} (hT : liftInvOk T = true) {st : Statement} {M : ℕ}
    (C : CombData st M) (S : Finset Blocks) (N : ℕ) {x y : ByteArray} {g : Table} {ch : Chain}
    (hpre : Chain.SamePrefix st (C.preOf x g) (C.midOf y g))
    (hc1 : (C.midOf y g).chal1 = (g (.h21, x) : Bytes 136).ba)
    (hmid : Chain.SameMid st (C.midOf y g) ch) (hc2 : ch.chal2 = (g (.h22, y) : Bytes 56).ba)
    (P : Finset Blocks → Prop) (Good : Prop)
    (hdet : ∀ A : Finset Blocks, (∀ Δ ∈ A, ch.OnChain st T Δ) → (A : Set Blocks) ⊆ S →
      Seed.KOSGood ch.kosCh (S : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
        ¬(C.sysOf y g (combDec (g (combKey M C.dst (g (.h22, y)))))).Holds
          (wStar uStar (ch.dc st)) →
        Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
          ⟨W128.word ch.chal2 48, 0⟩
          (valVec (C.sysOf y g (combDec (g (combKey M C.dst (g (.h22, y))))))
            (wStar uStar (ch.dc st))) ≠ 0) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
        (C.sysOf y g (combDec (g (combKey M C.dst (g (.h22, y)))))).Holds
          (wStar uStar (ch.dc st)) →
        C.witOf y g (wStar uStar (ch.dc st))) →
      P A → Good)
    (h1 : ¬combBad C T S N (.h21, x) g) (h2 : ¬combBad C T S N (.h22, y) g)
    (hP : P (onSet st T ch S)) : Good := by
  simp only [combBad, reduceCtorEq, ite_false, chainBad, not_not] at h1
  simp only [combBad, ite_true, CombData.qsComb, not_or, not_and, not_not] at h2
  have hkM : Seed.KOSGood (C.midOf y g).kosCh (S : Set Blocks) (lift T)
      ((C.midOf y g).kosQ st T) ((C.midOf y g).kosD st T) := by
    rw [hpre.kosQ_eq, hpre.kosD_eq, Chain.kosCh, hc1]
    exact h1
  have hk : Seed.KOSGood ch.kosCh (S : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T) := by
    rw [hmid.kosCh_eq, hmid.1.kosQ_eq, hmid.1.kosD_eq]; exact hkM
  have hA : ∀ Δ ∈ onSet st T ch S, ch.OnChain st T Δ := fun Δ h => (mem_onSet.1 h).2
  have hAS : onSet st T ch S ⊆ S := fun Δ h => (mem_onSet.1 h).1
  have hAV : onSet st T ch S ⊆ (C.midOf y g).AV st T S := fun Δ h => by
    rw [← hmid.AV_eq]; exact Chain.mem_AV_of_onChain st T _ (hA Δ h) (hAS h)
  refine hdet _ hA (Finset.coe_subset.2 hAS) hk (fun h2' uStar hs hnot => ?_)
    (fun h2' uStar hs hH => ?_) hP
  · rw [Chain.slope_eq_uCanon hT hkM hAV h2' (hmid.isSlope_iff.1 hs), hmid.dc_eq] at hnot ⊢
    rw [hc2]
    exact h2.1 hnot
  · rw [Chain.slope_eq_uCanon hT hkM hAV h2' (hmid.isSlope_iff.1 hs), hmid.dc_eq] at hH ⊢
    exact h2.2 hH

/-! ## Moussaka redemption and Ratatouille spend -/

/-- The data of a combined relation whose system (at a free `l`) and relation do not depend on
the chain. -/
def CombData.ofSys {st : Statement} {M : ℕ} (preOf midOf : ByteArray → Table → Chain)
    (sys : (Fin M → GF128) → System GF128) (wit : (ℕ → GF128) → Prop)
    (accOf : ByteArray → Table → Bytes 16 → Prop) (dst : ByteArray) : CombData st M :=
  ⟨preOf, midOf, fun _ _ => sys, fun _ _ => wit, accOf, dst⟩

omit [VoleMole.Verifier.HasPrg] in
lemma CombData.ofSys_committed {st : Statement} {M : ℕ} (preOf midOf : ByteArray → Table → Chain)
    (sys : (Fin M → GF128) → System GF128) (wit : (ℕ → GF128) → Prop)
    (accOf : ByteArray → Table → Bytes 16 → Prop) (dst : ByteArray)
    (hpre : ∀ x (g : Table) u, preOf x (Function.update g (.h21, x) u) = preOf x g)
    (hacc : ∀ z (g : Table) u, accOf z (Function.update g (.h23, z) u) = accOf z g)
    (hmid : ∀ y (g : Table) u, midOf y (Function.update g (.h22, y) u) = midOf y g)
    (hmidComb : ∀ y (g : Table) x v, midOf y (Function.update g (.comb M, x) v) = midOf y g) :
    (CombData.ofSys (st := st) preOf midOf sys wit accOf dst).Committed :=
  ⟨hpre, hacc, hmid, hmidComb, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ => rfl⟩

set_option exponentiation.threshold 500 in
/-- **Moussaka redemption over all random-oracle queries** (at most 64 anchors):
`Pr[event] ≤ q₁·2⁻¹⁵⁰ + q₂·(ε_QS(4409) + 2⁻¹²⁸ + n·2⁻⁴⁴⁸) + Q·9·2⁻¹²⁸ + ε_bind + ε_dead`. -/
theorem moussakaRedeem_prEvent_le {α : Type} (anchors : List UovPk) (hn64 : anchors.length ≤ 64)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hC : (CombData.ofSys (st := moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      preOf midOf (moussakaRedeemSysL anchors nf ctxIss ctxRed)
      (moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed)) accOf (toBA (VoleMole.Spec.makeDst "mous" 0 'l' '0'))).Committed)
    (oa : OracleComp spec α) (n : ℕ) (hn : IsTotalQueryBound oa n) (q : Kind → ℕ)
    (hq : IsKindQueryBound oa q) (event bindFail deadFail : α → Prop) {εb εd : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[bindFail r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[deadFail r] ≤ εd)
    (htrace : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) oa;
      event r → ¬bindFail r → ¬deadFail r → ∃ e ∈ tableQueryLog oa g,
        combBad (CombData.ofSys (st := moussakaRedeem anchors nf ctxIss ctxRed challengeDigest
          labelRows) preOf midOf (moussakaRedeemSysL anchors nf ctxIss ctxRed)
          (moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
            (fnOf ctxRed)) accOf (toBA (VoleMole.Spec.makeDst "mous" 0 'l' '0')))
          CrtGen.tables chal3Blocks 9 e.1 g) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤
      q .h21 * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        q .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) + (2 ^ 128 : ℝ≥0∞)⁻¹ +
          (n : ℝ≥0∞) / 2 ^ 448) +
        q .h23 * ((9 : ℝ≥0∞) / 2 ^ 128) + εb + εd := by
  refine (prEvent_le_comb_terms liftInvOk_tables _ hC chal3Blocks
    (fun _ _ _ => Moussaka.redeemSystem_length _ _ _ _ _ _ _)
    (fun _ _ w => prU_comb_bad_le _ _ w fun hW =>
      moussaka_redeem_comb_bad_gf128 _ (by simpa using hn64) _ _ _ w hW)
    9 oa n hn q hq event bindFail deadFail hbind hdead htrace).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ (by norm_num [moussakaRedeem]) (by norm_num [moussakaRedeem])
  · norm_num

set_option exponentiation.threshold 500 in
/-- **Ratatouille spend over all random-oracle queries** (`d < 2⁶⁴`):
`Pr[event] ≤ q₁·2⁻¹⁵⁰ + q₂·(ε_QS(12282) + 2⁻¹²⁸ + n·2⁻⁴⁴⁸) + Q·9·2⁻¹²⁸ + ε_bind + ε_dead`. -/
theorem ratatouilleSpend_prEvent_le {α : Type} (pk : UovPk) (nf : ByteArray) (d : ℕ)
    (hd : d < 2 ^ 64) (cNext ctxIss : ByteArray) (labelRows : Bool)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hC : (CombData.ofSys (st := ratatouilleSpend pk nf d cNext ctxIss labelRows)
      preOf midOf (ratatouilleSpendSysL pk nf d cNext ctxIss)
      (ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss)) accOf
      (toBA (VoleMole.Spec.makeDst "rata" 0 'l' '0'))).Committed)
    (oa : OracleComp spec α) (n : ℕ) (hn : IsTotalQueryBound oa n) (q : Kind → ℕ)
    (hq : IsKindQueryBound oa q) (event bindFail deadFail : α → Prop) {εb εd : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[bindFail r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[deadFail r] ≤ εd)
    (htrace : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) oa;
      event r → ¬bindFail r → ¬deadFail r → ∃ e ∈ tableQueryLog oa g,
        combBad (CombData.ofSys (st := ratatouilleSpend pk nf d cNext ctxIss labelRows) preOf
          midOf (ratatouilleSpendSysL pk nf d cNext ctxIss)
          (ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss)) accOf
          (toBA (VoleMole.Spec.makeDst "rata" 0 'l' '0'))) CrtGen.tables chal3Blocks 9 e.1 g) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤
      q .h21 * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        q .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) + (2 ^ 128 : ℝ≥0∞)⁻¹ +
          (n : ℝ≥0∞) / 2 ^ 448) +
        q .h23 * ((9 : ℝ≥0∞) / 2 ^ 128) + εb + εd := by
  refine (prEvent_le_comb_terms liftInvOk_tables _ hC chal3Blocks
    (fun _ _ _ => Ratatouille.spendSystem_length _ _ _ _ _ _ _ _)
    (fun _ _ w => prU_comb_bad_le _ _ w fun hW =>
      ratatouille_spend_comb_bad_gf128 _ _ hd _ _ w hW)
    9 oa n hn q hq event bindFail deadFail hbind hdead htrace).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ (by norm_num [ratatouilleSpend]) (by norm_num [ratatouilleSpend])
  · norm_num

-- Elaborating the combination cell `g (combKey Moussaka.M …)` needs a deeper recursion.
set_option maxRecDepth 4000 in
/-- **Moussaka redemption at one chain of the random-oracle game**: outside L2 and `hclaim1`, a
chain whose `H₂¹` and `H₂²` queries are not bad (with `l` read from the table at
`chal2 ‖ MOUSSAKA_REDEEM_COMBINE_DST`) yields a redemption witness or has at most 9 accepted
admissible `chal3`. -/
theorem moussakaRedeem_good_of_not_bad (anchors : List UovPk)
    (nf ctxIss ctxRed challengeDigest : ByteArray) (labelRows : Bool)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    {x y : ByteArray} {g : Table} {ch : Chain}
    (hpre : Chain.SamePrefix (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      (preOf x g) (midOf y g))
    (hc1 : (midOf y g).chal1 = (g (.h21, x) : Bytes 136).ba)
    (hmid : Chain.SameMid (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      (midOf y g) ch)
    (hc2 : ch.chal2 = (g (.h22, y) : Bytes 56).ba)
    (hvals : ∀ w, ch.vals w = (moussakaRedeemSysL anchors nf ctxIss ctxRed
      (combDec (g (combKey Moussaka.M (toBA (VoleMole.Spec.makeDst "mous" 0 'l' '0'))
        (g (.h22, y)))))).values w)
    (known : Finset (Fin BAVC.tau)) (acc : Bytes 16 → Prop) [DecidablePred acc]
    (h1 : ¬combBad (CombData.ofSys
        (st := moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) preOf midOf
        (moussakaRedeemSysL anchors nf ctxIss ctxRed)
        (moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
          (fnOf ctxRed)) accOf (toBA (VoleMole.Spec.makeDst "mous" 0 'l' '0')))
      CrtGen.tables chal3Blocks 9 (.h21, x) g)
    (h2 : ¬combBad (CombData.ofSys
        (st := moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) preOf midOf
        (moussakaRedeemSysL anchors nf ctxIss ctxRed)
        (moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
          (fnOf ctxRed)) accOf (toBA (VoleMole.Spec.makeDst "mous" 0 'l' '0')))
      CrtGen.tables chal3Blocks 9 (.h22, y) g)
    (hhyp : ChainHyps (onSet (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      CrtGen.tables ch chal3Blocks) known acc) :
    (∃ i ∈ known, moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
        (fnOf ctxRed) (candidate (F := GF128)
          (ch.u (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows))
          (ch.dc (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)) i)) ∨
      #{x ∈ admissible | acc x} ≤ 9 :=
  comb_good_of_not_bad liftInvOk_tables _ chal3Blocks 9 hpre hc1 hmid hc2
    (fun A => ChainHyps A known acc) _
    (fun _A hA hAS hkos hQS hcomb hP => moussakaRedeem_extract_chain anchors nf ctxIss ctxRed
      challengeDigest labelRows ch _ hvals hA hAS hkos hP.1 hQS hcomb admissible deltaBlocks
      deltaBlocks_injOn _ hP.2) h1 h2 hhyp

set_option maxRecDepth 8000 in
/-- **Ratatouille spend at one chain of the random-oracle game** (as
`moussakaRedeem_good_of_not_bad`, `l` at `chal2 ‖ RATATOUILLE_SPEND_COMBINE_DST`). -/
theorem ratatouilleSpend_good_of_not_bad (pk : UovPk) (nf : ByteArray) (d : ℕ)
    (cNext ctxIss : ByteArray) (labelRows : Bool) (preOf midOf : ByteArray → Table → Chain)
    (accOf : ByteArray → Table → Bytes 16 → Prop) {x y : ByteArray} {g : Table} {ch : Chain}
    (hpre : Chain.SamePrefix (ratatouilleSpend pk nf d cNext ctxIss labelRows) (preOf x g)
      (midOf y g))
    (hc1 : (midOf y g).chal1 = (g (.h21, x) : Bytes 136).ba)
    (hmid : Chain.SameMid (ratatouilleSpend pk nf d cNext ctxIss labelRows) (midOf y g) ch)
    (hc2 : ch.chal2 = (g (.h22, y) : Bytes 56).ba)
    (hvals : ∀ w, ch.vals w = (ratatouilleSpendSysL pk nf d cNext ctxIss
      (combDec (g (combKey Ratatouille.uovM (toBA (VoleMole.Spec.makeDst "rata" 0 'l' '0'))
        (g (.h22, y)))))).values w)
    (known : Finset (Fin BAVC.tau)) (acc : Bytes 16 → Prop) [DecidablePred acc]
    (h1 : ¬combBad (CombData.ofSys (st := ratatouilleSpend pk nf d cNext ctxIss labelRows) preOf
        midOf (ratatouilleSpendSysL pk nf d cNext ctxIss)
        (ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss)) accOf
        (toBA (VoleMole.Spec.makeDst "rata" 0 'l' '0'))) CrtGen.tables chal3Blocks 9 (.h21, x) g)
    (h2 : ¬combBad (CombData.ofSys (st := ratatouilleSpend pk nf d cNext ctxIss labelRows) preOf
        midOf (ratatouilleSpendSysL pk nf d cNext ctxIss)
        (ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss)) accOf
        (toBA (VoleMole.Spec.makeDst "rata" 0 'l' '0'))) CrtGen.tables chal3Blocks 9 (.h22, y) g)
    (hhyp : ChainHyps (onSet (ratatouilleSpend pk nf d cNext ctxIss labelRows) CrtGen.tables ch
      chal3Blocks) known acc) :
    (∃ i ∈ known, ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctxIss)
        (candidate (F := GF128) (ch.u (ratatouilleSpend pk nf d cNext ctxIss labelRows))
          (ch.dc (ratatouilleSpend pk nf d cNext ctxIss labelRows)) i)) ∨
      #{x ∈ admissible | acc x} ≤ 9 :=
  comb_good_of_not_bad liftInvOk_tables _ chal3Blocks 9 hpre hc1 hmid hc2
    (fun A => ChainHyps A known acc) _
    (fun _A hA hAS hkos hQS hcomb hP => ratatouilleSpend_extract_chain pk nf d cNext ctxIss
      labelRows ch _ hvals hA hAS hkos hP.1 hQS hcomb admissible deltaBlocks deltaBlocks_injOn _
      hP.2) h1 h2 hhyp

/-! ## PomFRIT -/

/-- PomFRIT's combined-relation data: the system and the relation at the chain's `chal1` (the
target `h(c₁)`), and the combination DST `"pomf" 0 'l' '0'`. -/
def pomfritData (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop) :
    CombData (pomfritRedeem pk sig msg labelRows) 45 where
  preOf := preOf
  midOf := midOf
  sysOf y g l := pomfritRedeemSysL pk sig msg labelRows (midOf y g).chal1 l
  witOf y g w := pomfritWit GF256.ofBits 119 45 pk.map
    (fun k => ⟨fnOf (pomfritTarget (pomfritParams labelRows) pk.digest (midOf y g).chal1 sig msg)
      k.val⟩) w
  accOf := accOf
  dst := toBA (VoleMole.Spec.makeDst "pomf" 0 'l' '0')

omit [VoleMole.Verifier.HasPrg] in
lemma pomfritData_committed (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hpre : ∀ x (g : Table) u, preOf x (Function.update g (.h21, x) u) = preOf x g)
    (hacc : ∀ z (g : Table) u, accOf z (Function.update g (.h23, z) u) = accOf z g)
    (hmid : ∀ y (g : Table) u, midOf y (Function.update g (.h22, y) u) = midOf y g)
    (hmidComb : ∀ y (g : Table) x v, midOf y (Function.update g (.comb 45, x) v) = midOf y g) :
    (pomfritData pk sig msg labelRows preOf midOf accOf).Committed where
  pre := hpre
  acc := hacc
  mid := hmid
  midComb := hmidComb
  sys y g u := by simp only [pomfritData, hmid]
  sysComb y g x v := by simp only [pomfritData, hmidComb]
  wit y g u := by simp only [pomfritData, hmid]
  witComb y g x v := by simp only [pomfritData, hmidComb]

set_option exponentiation.threshold 500 in
/-- **PomFRIT redemption over all random-oracle queries.** For chain data committed as in
`CombData.Committed`, an adversary with at most `n` queries, `q k` to each domain:
`Pr[event] ≤ q₁·2⁻¹⁵⁰ + q₂·(ε_QS(1313) + 2⁻¹²⁸ + n·2⁻⁴⁴⁸) + Q·2·2⁻¹²⁸ + ε_bind + ε_dead`, if
outside the binding and dead-leaf failures the event implies a bad query (`htrace`). -/
theorem pomfritRedeem_prEvent_le {α : Type} (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hC : (pomfritData pk sig msg labelRows preOf midOf accOf).Committed)
    (oa : OracleComp spec α) (n : ℕ) (hn : IsTotalQueryBound oa n) (q : Kind → ℕ)
    (hq : IsKindQueryBound oa q) (event bindFail deadFail : α → Prop) {εb εd : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[bindFail r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[deadFail r] ≤ εd)
    (htrace : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) oa;
      event r → ¬bindFail r → ¬deadFail r → ∃ e ∈ tableQueryLog oa g,
        combBad (pomfritData pk sig msg labelRows preOf midOf accOf) CrtGen.tables chal3Blocks 2
          e.1 g) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤
      q .h21 * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        q .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 1313) + (2 ^ 128 : ℝ≥0∞)⁻¹ +
          (n : ℝ≥0∞) / 2 ^ 448) +
        q .h23 * ((2 : ℝ≥0∞) / 2 ^ 128) + εb + εd := by
  refine (prEvent_le_comb_terms liftInvOk_tables _ hC chal3Blocks
    (fun _ _ _ => PomFRIT.pomfritRedeemSystem_length _ _ _ _ _ _ _)
    (fun _ _ w => prU_comb_bad_le _ _ w fun hW => pomfrit_comb_bad_gf128 _ _ _ _ w hW)
    2 oa n hn q hq event bindFail deadFail hbind hdead htrace).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ (by norm_num [pomfritRedeem, pomfritParams])
      (by norm_num [pomfritRedeem, pomfritParams])
  · norm_num

/-- **PomFRIT redemption at one chain of the random-oracle game**: outside L2 and `hclaim1`, a
chain whose `H₂¹` and `H₂²` queries are not bad yields a witness for the target at its `chal1`, or
has at most 2 accepted admissible `chal3`. -/
theorem pomfritRedeem_good_of_not_bad (pk : UovPk) (sig msg : ByteArray) (labelRows : Bool)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    {x y : ByteArray} {g : Table} {ch : Chain}
    (hpre : Chain.SamePrefix (pomfritRedeem pk sig msg labelRows) (preOf x g) (midOf y g))
    (hc1 : (midOf y g).chal1 = (g (.h21, x) : Bytes 136).ba)
    (hmid : Chain.SameMid (pomfritRedeem pk sig msg labelRows) (midOf y g) ch)
    (hc2 : ch.chal2 = (g (.h22, y) : Bytes 56).ba)
    (hvals : ∀ w, ch.vals w = (pomfritRedeemSysL pk sig msg labelRows (midOf y g).chal1
      (combDec (g (combKey 45 (toBA (VoleMole.Spec.makeDst "pomf" 0 'l' '0'))
        (g (.h22, y)))))).values w)
    (known : Finset (Fin BAVC.tau)) (acc : Bytes 16 → Prop) [DecidablePred acc]
    (h1 : ¬combBad (pomfritData pk sig msg labelRows preOf midOf accOf) CrtGen.tables
      chal3Blocks 2 (.h21, x) g)
    (h2 : ¬combBad (pomfritData pk sig msg labelRows preOf midOf accOf) CrtGen.tables
      chal3Blocks 2 (.h22, y) g)
    (hhyp : ChainHyps (onSet (pomfritRedeem pk sig msg labelRows) CrtGen.tables ch chal3Blocks)
      known acc) :
    (∃ i ∈ known, pomfritWit GF256.ofBits 119 45 pk.map
        (fun k => ⟨fnOf (pomfritTarget (pomfritParams labelRows) pk.digest (midOf y g).chal1
          sig msg) k.val⟩)
        (candidate (F := GF128) (ch.u (pomfritRedeem pk sig msg labelRows))
          (ch.dc (pomfritRedeem pk sig msg labelRows)) i)) ∨
      #{x ∈ admissible | acc x} ≤ 2 :=
  comb_good_of_not_bad liftInvOk_tables (pomfritData pk sig msg labelRows preOf midOf accOf)
    chal3Blocks 2 hpre hc1 hmid hc2 (fun A => ChainHyps A known acc) _
    (fun _A hA hAS hkos hQS hcomb hP => pomfritRedeem_extract_chain pk sig msg labelRows ch _ _
      hvals hA hAS hkos hP.1 hQS hcomb admissible deltaBlocks deltaBlocks_injOn _ hP.2) h1 h2 hhyp

end VoleMole.ROM
