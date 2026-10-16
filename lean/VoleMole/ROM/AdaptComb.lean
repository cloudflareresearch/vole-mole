import VoleMole.ROM.AdaptFull

/-!
# Adaptively chosen statements: the combined relations (Moussaka redemption, Ratatouille spend)

As `ROM/AdaptChain.lean` for the combined relations (`ROM/Comb.lean`): the `H₂²` charge reads the
combination cell `H_comb(chal2 ‖ dst)`, which must be outside the cells the chain data at `y` read.
With the statement chosen at the end, the chain data of a statement `s` must read the *adaptive*
game's log (not that of the fixed game at `s`, whose extractor and verifier queries differ), so
that "outside the log before `y`" is one condition for the data and for the statement committed at
`y` (`stmtAt`):

* `preOfA`, `midOfA`, `accOfA`, `preCellsA`: `ROM/CipherChain.lean`'s chain data at `stF s`, read
  off the adaptive game's log `gLogA`; committed (`*_committed_A`, `midOfA_comb`), and at the
  statement `P` chose they are the fixed game's (`preOfA_eq`, …: per table the two logs agree).
* `combDataA`: the combined data of each statement; `combBadA`: the bad event of the statement
  committed at the query.
* `prEvent_combBadA_h22_le`: `ROM/Comb.lean`'s two-cell bound with the statement committed at `y`
  (it reads neither `H₂²(y)` nor a combination cell outside the log before `y`).
* `combBad_trace_ic`: the fixed-statement deterministic step at the joint game.
* `prEvent_accept_le_adaptive_comb_E`: the adaptive union bound per cipher table;
  `prEvent_accept_le_adaptive_comb`: in the joint experiment.
* `moussakaRedeem_accept_le_adaptive`, `ratatouilleSpend_accept_le_adaptive`: the `_full` bounds
  plus `stmtBindEps q`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## The chain data against the adaptive game's log -/

section DataA

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement)
  (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable)

/-- The adaptive game's hash log. -/
def gLogA (g : Table) : QueryLog spec := tableQueryLog (gameA T stF P E) g

/-- `preOf` at the statement `st`, against the adaptive game's log. -/
def preOfA (st : Statement) (x : ByteArray) (g : Table) : Chain :=
  preCore st E (logBefore (.h21, x) (gLogA T stF P E g))
    (logBefore (.inl (.h21, x)) (jOf g P E)) x g

/-- `midOf` at the statement `st`, against the adaptive game's log. -/
def midOfA (st : Statement) (y : ByteArray) (g : Table) : Chain :=
  midCore st E (logBefore (.h22, y) (gLogA T stF P E g))
    (logBefore (.inl (.h22, y)) (jOf g P E)) y g

/-- `accOf` at the statement `st`, against the adaptive game's log. -/
def accOfA (st : Statement) (z : ByteArray) (g : Table) (b : Prob.Bytes 16) : Prop :=
  let tc := tailCore st E (logBefore (.h23, z) (gLogA T stF P E g))
    (logBefore (.inl (.h23, z)) (jOf g P E)) z g
  deltaBlocks b ∈ @hideSet (icPrg E.cipher) st T tc.1 tc.2

/-- The cells of the adaptive game's log before `y`. -/
def preCellsA (y : ByteArray) (g : Table) : List Dom :=
  (logBefore (.h22, y) (gLogA T stF P E g)).map Sigma.fst

lemma gLogA_eq (g : Table) : gLogA T stF P E g = gLog T (stF (sA g P E)) P E g :=
  tableQueryLog_gameA T stF P E g

lemma preOfA_eq (g : Table) (x : ByteArray) :
    preOfA T stF P E (stF (sA g P E)) x g = preOf T (stF (sA g P E)) P E x g := by
  simp only [preOfA, preOf, gLogA_eq]

lemma midOfA_eq (g : Table) (y : ByteArray) :
    midOfA T stF P E (stF (sA g P E)) y g = midOf T (stF (sA g P E)) P E y g := by
  simp only [midOfA, midOf, gLogA_eq]

lemma accOfA_eq (g : Table) (z : ByteArray) :
    accOfA T stF P E (stF (sA g P E)) z g = accOf T (stF (sA g P E)) P E z g := by
  funext b
  simp only [accOfA, accOf, gLogA_eq]

lemma preCellsA_eq (g : Table) (y : ByteArray) :
    preCellsA T stF P E y g = preCells T (stF (sA g P E)) P E y g := by
  simp only [preCellsA, preCells, gLogA_eq]

lemma logBefore_gLogA_update (g : Table) (t : Dom) (u : Ans t) :
    logBefore t (gLogA T stF P E (Function.update g t u)) = logBefore t (gLogA T stF P E g) :=
  logBefore_tableQueryLog_update _ g t u

theorem preOfA_committed (st : Statement) (x : ByteArray) (g : Table) (u : Ans (.h21, x)) :
    preOfA T stF P E st x (Function.update g (.h21, x) u) = preOfA T stF P E st x g := by
  simp only [preOfA, logBefore_gLogA_update, logBefore_jOf_update]
  exact preCore_update st E _ _ _ g _ u (midKind_of_chalKind (Or.inl rfl))

theorem midOfA_committed (st : Statement) (y : ByteArray) (g : Table) (u : Ans (.h22, y)) :
    midOfA T stF P E st y (Function.update g (.h22, y) u) = midOfA T stF P E st y g := by
  simp only [midOfA, logBefore_gLogA_update, logBefore_jOf_update]
  exact midCore_update st E _ _ _ g _ u (midKind_of_chalKind (Or.inr (Or.inl rfl)))

theorem accOfA_committed (st : Statement) (z : ByteArray) (g : Table) (u : Ans (.h23, z)) :
    accOfA T stF P E st z (Function.update g (.h23, z) u) = accOfA T stF P E st z g := by
  funext b
  simp only [accOfA, logBefore_gLogA_update, logBefore_jOf_update]
  rw [tailCore_update st E _ _ _ g _ u (Or.inr (Or.inr rfl))]

/-- **The data at `y` do not read the combination cells outside the adaptive log before `y`.** -/
theorem midOfA_comb (st : Statement) (M : ℕ) (y : ByteArray) (g : Table) (x : ByteArray)
    (v : Ans (.comb M, x)) (hx : ((.comb M, x) : Dom) ∉ preCellsA T stF P E y g) :
    midOfA T stF P E st y (Function.update g (.comb M, x) v) = midOfA T stF P E st y g := by
  unfold midOfA
  have h1 : logBefore (.h22, y) (gLogA T stF P E (Function.update g (.comb M, x) v)) =
      logBefore (.h22, y) (gLogA T stF P E g) :=
    logBefore_tableQueryLog_congr_of_not_mem _ g _ (fun t ht => Function.update_of_ne ht _ _) hx
  have hx' : ((.comb M, x) : Dom) ∉
      (logBefore (.h22, y) (gLog T (stF (sA g P E)) P E g)).map Sigma.fst := by
    rw [← gLogA_eq]; exact hx
  have h2 : logBefore (.inl (.h22, y)) (jOf (Function.update g (.comb M, x) v) P E) =
      logBefore (.inl (.h22, y)) (jOf g P E) :=
    logBefore_tableQueryLog_congr_of_not_mem P (join g E) _
      (fun t ht => join_update_inl_of_ne g E _ v ht) (not_mem_jPre T _ P E g hx')
  rw [h1, h2]
  exact midCore_update st E _ _ _ g _ v (midKind_comb M)

lemma preCellsA_mid (y : ByteArray) (g : Table) (u : Ans (.h22, y)) :
    preCellsA T stF P E y (Function.update g (.h22, y) u) = preCellsA T stF P E y g := by
  unfold preCellsA; rw [logBefore_gLogA_update]

lemma preCellsA_comb (M : ℕ) (y : ByteArray) (g : Table) (x : ByteArray) (v : Ans (.comb M, x))
    (h : ((.comb M, x) : Dom) ∈ preCellsA T stF P E y g) :
    ((.comb M, x) : Dom) ∈ preCellsA T stF P E y (Function.update g (.comb M, x) v) :=
  mem_logBefore_tableQueryLog_update _ g v h

/-- **The combined data of the statement `s`**, against the adaptive game's log. -/
def combDataA {M : ℕ} (sysL : ι → (Fin M → GF128) → System GF128)
    (witL : ι → (ℕ → GF128) → Prop) (dst : ByteArray) (s : ι) : CombData (stF s) M :=
  CombData.ofSys (preOfA T stF P E (stF s)) (midOfA T stF P E (stF s)) (sysL s) (witL s)
    (accOfA T stF P E (stF s))
    dst (preCellsA T stF P E)

theorem combDataA_committed {M : ℕ} (sysL : ι → (Fin M → GF128) → System GF128)
    (witL : ι → (ℕ → GF128) → Prop) (dst : ByteArray) (s : ι) :
    (combDataA T stF P E sysL witL dst s).Committed :=
  CombData.ofSys_committed _ _ _ _ _ _ _ (preOfA_committed T stF P E (stF s))
    (accOfA_committed T stF P E (stF s)) (midOfA_committed T stF P E (stF s))
    (fun y g x v hx => midOfA_comb T stF P E (stF s) M y g x v hx) (preCellsA_mid T stF P E)
    (fun y g x v h => preCellsA_comb T stF P E M y g x v h)

end DataA

/-! ## Congruence of the bad events in the chain data -/

/-- `chainBad` at a table reads the data at that table only. -/
theorem chainBad_congr {st : Statement} (C C' : ChainData st) (T : CrtTables) (S : Finset Blocks)
    (N : ℕ) (g : Table) (hpre : ∀ x, C.preOf x g = C'.preOf x g)
    (hmid : ∀ y, C.midOf y g = C'.midOf y g) (hcs : ∀ y, C.csOf y g = C'.csOf y g)
    (hacc : ∀ z, C.accOf z g = C'.accOf z g) [HasPrg] (t : Dom) :
    chainBad C T S N t g ↔ chainBad C' T S N t g := by
  obtain ⟨k, x⟩ := t
  cases k <;> simp only [chainBad]
  · rw [hpre x]
  · simp only [ChainData.wC]; rw [hmid x, hcs x]
  · rw [hacc x]

/-- **`combBad` at a table reads the data at that table only.** -/
theorem combBad_congr {st : Statement} {M : ℕ} (C C' : CombData st M) (T : CrtTables)
    (S : Finset Blocks) (N : ℕ) (g : Table) (hpre : ∀ x, C.preOf x g = C'.preOf x g)
    (hmid : ∀ y, C.midOf y g = C'.midOf y g) (hsys : ∀ y, C.sysOf y g = C'.sysOf y g)
    (hwit : ∀ y, C.witOf y g = C'.witOf y g) (hacc : ∀ z, C.accOf z g = C'.accOf z g)
    (hdst : C.dst = C'.dst) (hP : ∀ y, C.pre y g = C'.pre y g) [HasPrg] (t : Dom) :
    combBad C T S N t g ↔ combBad C' T S N t g := by
  obtain ⟨k, x⟩ := t
  by_cases hk : k = .h22
  · subst hk
    obtain ⟨p1, m1, s1, w1, a1, d1, r1⟩ := C
    obtain ⟨p2, m2, s2, w2, a2, d2, r2⟩ := C'
    simp only at hpre hmid hsys hwit hacc hdst hP
    subst hdst
    simp only [combBad, CombData.qsComb, CombData.wC, ite_true]
    rw [hmid x, hsys x, hwit x, hP x]
  · simp only [combBad, hk, ite_false]
    exact chainBad_congr C.toChainData C'.toChainData T S N g hpre hmid (fun _ => rfl) hacc (k, x)

/-! ## The total query count of the adaptive game -/

theorem isTotalQueryBound_extractIC {β : Type} (st : Statement) (E : CTable)
    (r : (ByteArray × β) × QueryLog specIC) : IsTotalQueryBound (extractIC st E r) 2 := by
  unfold extractIC mu1Q
  split <;>
  · refine isTotalQueryBound_hashQ_bind_iff.2 ⟨by norm_num, fun u => ?_⟩
    exact isTotalQueryBound_hashQ_bind_iff.2 ⟨by norm_num, fun _ => trivial⟩

/-- **The adaptive game's total hash queries**: `P`'s, the extractor's two, the verifier's 337. -/
theorem isTotalQueryBound_gameA {ι β : Type} (T : CrtTables) (stF : ι → Statement)
    {P : OracleComp specIC (ByteArray × (ι × β))} (E : CTable) {n : ℕ}
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) :
    IsTotalQueryBound (gameA T stF P E) (n + 2 + verifierTotal) :=
  isTotalQueryBound_bind (isTotalQueryBound_bind (isTotalQueryBound_runE E hn) fun r =>
    isTotalQueryBound_extractIC _ E r) fun r =>
      (isQueryBound_map_iff _ _ _ _ _).2 (@isTotalQueryBound_verifyQ (icPrg E.cipher) T _ r.1)

/-! ## The bad events at the committed statement -/

section CombA

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
  (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable) {M : ℕ}
  (sysL : ι → (Fin M → GF128) → System GF128) (witL : ι → (ℕ → GF128) → Prop) (dst : ByteArray)

/-- **A bad query of a combined relation at the statement committed there.** -/
def combBadA (N : ℕ) (t : Dom) (g : Table) : Prop :=
  ∃ s, stmtAt dec (gLogA T stF P E g) t = some s ∧
    @combBad (icPrg E.cipher) (stF s) M (combDataA T stF P E sysL witL dst s) T chal3Blocks N t g

lemma stmtAt_congr {L L' : QueryLog spec} {t : Dom} (h : logBefore t L = logBefore t L') :
    stmtAt dec L t = stmtAt dec L' t := by
  unfold stmtAt; rw [h]

/-- **The per-query bound at `H₂¹` and `H₂³`** (`chainBad` of the committed statement). -/
theorem prEvent_combBadA_cell_le (hT : liftInvOk T = true) (st₀ : Statement)
    (hparams : ∀ s, (stF s).params = st₀.params) (N : ℕ) (t : Dom) (ht : t.1 ≠ .h22)
    (g : Table) :
    Pr{let u ← $ᵗ (Ans t)}[combBadA T stF dec P E sysL witL dst N t (Function.update g t u)] ≤
      chainEps st₀ chal3Blocks 0 N t.1 := by
  classical
  let _ : HasPrg := icPrg E.cipher
  have h : ∀ u, combBadA T stF dec P E sysL witL dst N t (Function.update g t u) ↔
      ∃ s, stmtAt dec (gLogA T stF P E g) t = some s ∧
        chainBad (combDataA T stF P E sysL witL dst s).toChainData T chal3Blocks N t
          (Function.update g t u) := fun u => by
    unfold combBadA gLogA
    rw [stmtAt_update]
    simp only [combBad, ht, ite_false]
  simp_rw [h]
  rcases hσ : stmtAt dec (gLogA T stF P E g) t with _ | s
  · simp only [reduceCtorEq, false_and, exists_false]
    rw [prEvent_false]
    exact bot_le
  · have h' : ∀ u, (∃ s', some s = some s' ∧
        chainBad (combDataA T stF P E sysL witL dst s').toChainData T chal3Blocks N t
          (Function.update g t u)) ↔
        chainBad (combDataA T stF P E sysL witL dst s).toChainData T chal3Blocks N t
          (Function.update g t u) :=
      fun u => ⟨fun ⟨s', hs', hb⟩ => (Option.some.inj hs') ▸ hb, fun hb => ⟨s, rfl, hb⟩⟩
    simp_rw [h']
    refine (prEvent_chainBad_update_le hT _ (CombData.toChainData_committed _
      (combDataA_committed T stF P E sysL witL dst s)) chal3Blocks (n := 0) (fun _ _ => rfl) N t
      g).trans_eq ?_
    rw [chainEps_congr (hparams s)]

lemma extend_two_updates (K : Finset Dom) (c : (ofFn fun d : K => Ans d.val).QueryCache)
    {y : ByteArray} (hy : ((.h22, y) : Dom) ∈ K) (hc : c ⟨_, hy⟩ = none)
    (hK : ∀ u, combKey M dst u ∈ K) (u : Ans (.h22, y)) (v : Ans (combKey M dst u))
    (hv : c ⟨_, hK u⟩ = none) (g : (d : K) → Ans d.val) :
    extendTable K (completeTable c (Function.update (Function.update g ⟨_, hK u⟩ v) ⟨_, hy⟩ u)) =
      Function.update (Function.update (extendTable K (completeTable c g)) (combKey M dst u) v)
        (.h22, y) u := by
  rw [← completeTable_update_of_none c _ hc, ← completeTable_update_of_none c _ hv,
    extendTable_update, extendTable_update]

/-- The statement committed at `y` after setting `H₂²(y)` and a fresh combination cell. -/
lemma stmtAt_two_updates (N : ℕ) (X : Table) {y : ByteArray} (u : Ans (.h22, y))
    (v : Ans (combKey M dst u)) {s : ι}
    (hσ : stmtAt dec (gLogA T stF P E (Function.update (Function.update X (combKey M dst u) v)
      (.h22, y) u)) (.h22, y) = some s)
    (hb : @combBad (icPrg E.cipher) (stF s) M (combDataA T stF P E sysL witL dst s) T chal3Blocks N
      (.h22, y) (Function.update (Function.update X (combKey M dst u) v) (.h22, y) u)) :
    stmtAt dec (gLogA T stF P E X) (.h22, y) = some s := by
  let _ : HasPrg := icPrg E.cipher
  simp only [combBad, ite_true] at hb
  obtain ⟨-, hfresh⟩ := hb
  rw [Function.update_self] at hfresh
  have hfresh' : combKey M dst u ∉ preCellsA T stF P E y
      (Function.update X (combKey M dst u) v) := by
    intro hm
    refine hfresh ?_
    show combKey M dst u ∈ preCellsA T stF P E y _
    rw [preCellsA_mid]
    exact hm
  have hnot : combKey M dst u ∉ preCellsA T stF P E y X := fun hm =>
    hfresh' (preCellsA_comb T stF P E M y X _ v hm)
  unfold gLogA at hσ ⊢
  rw [stmtAt_update] at hσ
  rw [stmtAt_congr dec (logBefore_tableQueryLog_congr_of_not_mem _ X _
    (fun t' ht' => Function.update_of_ne ht' _ _) hnot)] at hσ
  exact hσ

set_option exponentiation.threshold 500 in
/-- **The `H₂²` bound at the committed statement** (`prEvent_combBad_h22_le`): at a fresh `H₂²`
query `y`, with fewer than `n` cached cells, `≤ ε_QS(n') + ε_c + n·2⁻⁴⁴⁸`. The statement
committed at `y` reads the log before `y` only, so neither the `H₂²` answer nor a combination cell
outside that log. -/
theorem prEvent_combBadA_h22_le (N : ℕ) {n' : ℕ} (hn' : ∀ s l, (sysL s l).length = n')
    {εc : ℝ≥0∞} (hεc : ∀ s w, prU (Fin M → GF128) (fun l => (sysL s l).Holds w ∧ ¬witL s w) ≤ εc)
    (K : Finset Dom) [SampleableType ((d : K) → Ans d.val)] (hK : ∀ u, combKey M dst u ∈ K)
    {y : ByteArray} (hy : ((.h22, y) : Dom) ∈ K) (c : (ofFn fun d : K => Ans d.val).QueryCache)
    (hc : c ⟨_, hy⟩ = none) {n : ℕ} (hcard : (cachedKeys c).card < n) :
    Pr{let g ← $ᵗ ((d : K) → Ans d.val)}[
      combBadA T stF dec P E sysL witL dst N (.h22, y) (extendTable K (completeTable c g))] ≤
      ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc + (n : ℝ≥0∞) / 2 ^ 448 := by
  classical
  let _ : HasPrg := icPrg E.cipher
  let t : K := ⟨_, hy⟩
  let p : Ans t.val → K := fun u => ⟨combKey M dst u, hK u⟩
  have hp : Function.Injective p := fun u u' h =>
    combKey_injective M dst (congrArg Subtype.val h)
  refine (prEvent_completeTable_le_two_cells c t p
    (fun G => combBadA T stF dec P E sysL witL dst N (.h22, y) (extendTable K G))).trans ?_
  rw [add_comm (ENNReal.ofReal _ + εc)]
  refine add_le_add ?_ ?_
  · refine (prEvent_isSome_le c p hp).trans ?_
    have hcardU : Fintype.card (Ans t.val) = 2 ^ 448 := card_bytes 56
    rw [hcardU, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.div_le_div_right (by exact_mod_cast hcard.le) _
  · let X : ((d : K) → Ans d.val) → Table := fun g => extendTable K (completeTable c g)
    let σ : ((d : K) → Ans d.val) → Option ι := fun g =>
      stmtAt dec (gLogA T stF P E (X g)) (.h22, y)
    let CA := combDataA T stF P E sysL witL dst
    change Pr{let u ← $ᵗ (Prob.Bytes 56); let v ← $ᵗ (Prob.Bytes (16 * M)); let g ← $ᵗ ((d : K) → Ans d.val)}[
          c (p u) = none ∧ combBadA T stF dec P E sysL witL dst N (.h22, y)
          (extendTable K (completeTable c (Function.update (Function.update g (p u) v) t u)))] ≤ _
    refine (prEvent_three_mono (Q := fun u v g =>
      (∃ s, σ g = some s ∧ (¬((CA s).sysOf y (X g) (combDec v)).Holds
          ((CA s).wC T chal3Blocks y (X g)) ∧
        Seed.zkHash ((CA s).sysOf y (X g) (combDec v)).length (gfOfBytes u.ba 0)
          (gfOfBytes u.ba 16) (gfOfBytes u.ba 32) ⟨W128.word u.ba 48, 0⟩
          (valVec ((CA s).sysOf y (X g) (combDec v)) ((CA s).wC T chal3Blocks y (X g))) = 0)) ∨
      (∃ s, σ g = some s ∧ (((CA s).sysOf y (X g) (combDec v)).Holds
          ((CA s).wC T chal3Blocks y (X g)) ∧
        ¬(CA s).witOf y (X g) ((CA s).wC T chal3Blocks y (X g))))) ?_).trans ?_
    · intro u v g h
      obtain ⟨hcu, s, hσ, hb⟩ := h
      have hq := combBad_h22_update (CA s) K (combDataA_committed T stF P E sysL witL dst s) T
        chal3Blocks N hK hy c hc u v hcu g hb
      have hσ' : σ g = some s := by
        have hX' : extendTable K (completeTable c (Function.update (Function.update g (p u) v) t u)) =
            Function.update (Function.update (X g) (combKey M dst u) v) (.h22, y) u :=
          extend_two_updates dst K c hy hc hK u v hcu g
        rw [hX'] at hσ hb
        exact stmtAt_two_updates T stF dec P E sysL witL dst N (X g) u v hσ hb
      rcases hq with hq | hq
      · exact Or.inl ⟨s, hσ', hq⟩
      · exact Or.inr ⟨s, hσ', hq⟩
    refine (prEvent_three_or_le _ _).trans (add_le_add ?_ ?_)
    · refine prEvent_three_le_of_first _ fun v g => ?_
      rcases hσ : σ g with _ | s
      · simp only [reduceCtorEq, false_and, exists_false]
        rw [prEvent_false]
        exact bot_le
      · simp only [Option.some.injEq, exists_eq_left']
        refine prEvent_uniformSample_le ?_
        exact (prU_qs_bad_le _ _).trans_eq (by rw [show ((CA s).sysOf y (X g) (combDec v)).length
          = n' from hn' s _])
    · refine prEvent_three_le_of_second (fun v g => ∃ s, σ g = some s ∧
        (((CA s).sysOf y (X g) (combDec v)).Holds ((CA s).wC T chal3Blocks y (X g)) ∧
          ¬(CA s).witOf y (X g) ((CA s).wC T chal3Blocks y (X g)))) fun g => ?_
      rcases hσ : σ g with _ | s
      · simp only [reduceCtorEq, false_and, exists_false]
        rw [prEvent_false]
        exact bot_le
      · simp only [Option.some.injEq, exists_eq_left']
        refine prEvent_uniformSample_le ?_
        have := hεc s ((CA s).wC T chal3Blocks y (X g))
        rwa [prU_map_equiv (combEquiv M)] at this

end CombA

/-! ## The deterministic step at the joint game, combined relations -/

/-- **The per-chain deterministic theorem of a combined relation** with systems `sysL l` at the
combination `l` and relation `witL` (`prEvent_accept_le_comb_terms`' `hdet`, for data whose system
does not depend on the chain). -/
def CombDet [HasPrg] {M : ℕ} (T : CrtTables) (st : Statement)
    (sysL : (Fin M → GF128) → System GF128) (witL : (ℕ → GF128) → Prop) (N : ℕ)
    (Wit : ByteArray → (ℕ → GF128) → Prop) : Prop :=
  ∀ (ch : Chain) (known : Finset (Fin BAVC.tau)) (acc : Prob.Bytes 16 → Prop)
    (l : Fin M → GF128), (∀ w, ch.vals w = (sysL l).values w) →
    ∀ A : Finset Blocks, (∀ Δ ∈ A, ch.OnChain st T Δ) → (A : Set Blocks) ⊆ chal3Blocks →
    Seed.KOSGood ch.kosCh (chal3Blocks : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T) →
    (2 ≤ A.card → ∀ uStar,
      (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
      ¬(sysL l).Holds (wStar uStar (ch.dc st)) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩ (valVec (sysL l) (wStar uStar (ch.dc st))) ≠ 0) →
    (2 ≤ A.card → ∀ uStar,
      (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
      (sysL l).Holds (wStar uStar (ch.dc st)) → witL (wStar uStar (ch.dc st))) →
    ChainHyps A known acc →
    (∃ i ∈ known, Wit ch.chal1 (candidate (F := GF128) (ch.u st) (ch.dc st) i)) ∨
      (open Classical in #{x ∈ admissible | acc x} ≤ N)

section TraceComb

variable {β : Type} {T : CrtTables}

set_option maxRecDepth 4000 in
/-- **The deterministic step at the joint game, combined relations** (`prEvent_accept_le_comb_terms`'
`htrace`, with the data, hits and failure events of `ROM/CipherChain.lean`, `ROM/CipherFull.lean`). -/
theorem combBad_trace_ic (hT : liftInvOk T = true) (st : Statement) {M : ℕ}
    (sysL : (Fin M → GF128) → System GF128) (witL : (ℕ → GF128) → Prop) (dst : ByteArray)
    (hcomb : st.comb = some (M, dst)) (N : ℕ) (Wit : ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ c1 (v : Prob.Bytes (16 * M)) w, st.values c1 v.ba w = (sysL (combDec v)).values w)
    (P : OracleComp specIC (ByteArray × β)) (E : CTable)
    (hdet : @CombDet (icPrg E.cipher) M T st sysL witL N Wit)
    (cf : Out (β × QueryLog specIC) → Prop)
    (hcf' : ∀ g, ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)) →
      KeysPre st E (jOf g P E) (gLog T st P E g) g) (g : Table)
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.accept = true)
    (hnex : ¬@Extracted (icPrg E.cipher) _ st Wit (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hnc : ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hnb : ¬@bindFail (icPrg E.cipher) _ st (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hnd : ¬DeadOpenOut st E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hh : NoHit (gameIC T st P E) (chainHit T st P E) g) :
    letI := icPrg E.cipher
    ∃ leaves, BAVC.reconstruct (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
        (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves ∧
      (verify (Hashes.ofTable g) T st (πOf g P E)).accept = true ∧
      let C := CombData.ofSys (st := st) (preOf T st P E) (midOf T st P E) sysL witL
        (accOf T st P E) dst (preCells T st P E)
      let ch := runChain (Hashes.ofTable g) T st (πOf g P E) leaves
        (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2.keys
      combBad C T chal3Blocks N (.h21, runX (Hashes.ofTable g) st (πOf g P E) leaves) g ∨
        combBad C T chal3Blocks N (.h22, runY (Hashes.ofTable g) st ch) g ∨
        combBad C T chal3Blocks N (.h23, runZ st ch) g := by
  classical
  let _ : HasPrg := icPrg E.cipher
  set C := CombData.ofSys (st := st) (preOf T st P E) (midOf T st P E) sysL witL
    (accOf T st P E) dst (preCells T st P E)
  have hs := sameChainHyp_ic_of T st P E cf hcf' g
  have hl := deadHiddenHyp_ic_of T st P E cf hcf' g
  have hcf := combFreshHyp_ic_of T st P E hcomb C rfl rfl cf g
  change let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))
    r.2.2.accept = true → ¬cf r → NoHit (game T st (proverIC st E P)) (chainHit T st P E) g →
    ∀ leaves, BAVC.reconstruct r.2.2.iv (Proof.opening ⟨st.params, r.1⟩)
      (Proof.delta ⟨st.params, r.1⟩) = some leaves →
    let ch := runChain (Hashes.ofTable g) T st r.1 leaves r.2.1.keys
    SameChain st T C.preOf C.midOf C.accOf (deadOf T st P E g) g ch
        (runX (Hashes.ofTable g) st r.1 leaves) (runY (Hashes.ofTable g) st ch) (runZ st ch) ∧
      ∀ i ∉ r.2.1.known, (deadOf T st P E g i).Nonempty at hs
  change let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))
    r.2.2.accept = true → ¬cf r → ¬DeadOpenOut st E r →
    NoHit (game T st (proverIC st E P)) (chainHit T st P E) g →
    ∀ i : Fin BAVC.tau, ∀ j ∈ deadOf T st P E g i,
      BAVC.deltaIndex (Proof.delta ⟨st.params, r.1⟩) i = j at hl
  change let r := evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))
    r.2.2.accept = true → ¬cf r → NoHit (game T st (proverIC st E P)) (chainHit T st P E) g →
    ∀ leaves, BAVC.reconstruct r.2.2.iv (Proof.opening ⟨st.params, r.1⟩)
      (Proof.delta ⟨st.params, r.1⟩) = some leaves →
    let y := runY (Hashes.ofTable g) st (runChain (Hashes.ofTable g) T st r.1 leaves r.2.1.keys)
    combKey M C.dst (g (.h22, y)) ∉ C.pre y g at hcf
  change (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))).2.2.accept = true
    at hacc
  change ¬Extracted st Wit (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P)))
    at hnex
  change ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))) at hnc
  change ¬bindFail st (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P))) at hnb
  change ¬DeadOpenOut st E (evalWithAnswerFn (QueryImpl.ofFn g) (game T st (proverIC st E P)))
    at hnd
  have hπ : (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).1 = πOf g P E :=
    proverIC_fst g st E P
  simp only [evalWithAnswerFn_game, hπ] at hs hl hacc hnex hnc hnb hnd
  rw [evalWithAnswerFn_game, hπ] at hcf
  set π := πOf g P E
  set e := (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2
  obtain ⟨-, leaves, hr, -⟩ := (accept_iff _ T st π).1 hacc
  obtain ⟨hiv, hc1⟩ := verify_iv_chal1 _ T st π hacc hr
  have hr' : BAVC.reconstruct (verify (Hashes.ofTable g) T st π).iv (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩) = some leaves := by rw [hiv]; exact hr
  have hbinds : Binds st (π, e, verify (Hashes.ofTable g) T st π) := by
    by_contra hb; exact hnb ⟨hacc, hb⟩
  have huc := outChain_u_dc (Hashes.ofTable g) T st (π, e, verify (Hashes.ofTable g) T st π) leaves
    hiv
  obtain ⟨hsc, hL2c⟩ := hs hacc hnc hh leaves hr'
  have hbad := combBad_of_accept hT C N Wit hcomb (fun _ _ v w => hvals _ v w)
    (fun _ _ ch known acc l _ hv A hA hAS hkos hQS hcb hP =>
      hdet ch known acc l hv A hA hAS hkos hQS hcb hP) hacc hr
    (fun i hi j hj hji => hbinds leaves hr' i hi j hj hji) hsc hL2c (hl hacc hnc hnd hh)
    (hcf hacc hnc hh leaves hr')
    (by
      rintro ⟨i, hi, hw⟩
      refine hnex ⟨i, hi, ?_⟩
      simp only [huc.1, huc.2, hc1]
      exact hw)
  exact ⟨leaves, hr, hacc, hbad⟩

end TraceComb

/-! ## The adaptive union bound, combined relations -/

section UnionComb

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
  (P : OracleComp specIC (ByteArray × (ι × β))) (E : CTable) {M : ℕ}
  (sysL : ι → (Fin M → GF128) → System GF128) (witL : ι → (ℕ → GF128) → Prop) (dst : ByteArray)

set_option maxRecDepth 4000 in
/-- At the statement `P` chose, the fixed game's combined data and the adaptive ones have the same
bad events. -/
theorem combBad_fixed_to_A (N : ℕ) (g : Table) (t : Dom) :
    @combBad (icPrg E.cipher) (stF (sA g P E)) M (CombData.ofSys (st := stF (sA g P E))
      (preOf T (stF (sA g P E)) P E) (midOf T (stF (sA g P E)) P E) (sysL (sA g P E))
      (witL (sA g P E)) (accOf T (stF (sA g P E)) P E) dst (preCells T (stF (sA g P E)) P E)) T
      chal3Blocks N t g →
    @combBad (icPrg E.cipher) (stF (sA g P E)) M (combDataA T stF P E sysL witL dst (sA g P E)) T
      chal3Blocks N t g := by
  let _ : HasPrg := icPrg E.cipher
  refine (combBad_congr _ (combDataA T stF P E sysL witL dst (sA g P E)) T chal3Blocks N g
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ t).1
  · intro x
    change preOf T (stF (sA g P E)) P E x g = preOfA T stF P E (stF (sA g P E)) x g
    exact (preOfA_eq T stF P E g x).symm
  · intro y
    change midOf T (stF (sA g P E)) P E y g = midOfA T stF P E (stF (sA g P E)) y g
    exact (midOfA_eq T stF P E g y).symm
  · intro y
    change sysL (sA g P E) = sysL (sA g P E)
    rfl
  · intro y
    change witL (sA g P E) = witL (sA g P E)
    rfl
  · intro z
    change accOf T (stF (sA g P E)) P E z g = accOfA T stF P E (stF (sA g P E)) z g
    exact (accOfA_eq T stF P E g z).symm
  · change dst = dst
    rfl
  · intro y
    change preCells T (stF (sA g P E)) P E y g = preCellsA T stF P E y g
    exact (preCellsA_eq T stF P E g y).symm

set_option exponentiation.threshold 500 in
-- `Finset.univ : Finset (Bytes 56)` (the combination cells) needs a deeper recursion to elaborate.
set_option maxRecDepth 4000 in
/-- **The adaptive union bound for the combined relations, per cipher table** (as
`prEvent_accept_le_adaptive_E`, with `ROM/Comb.lean`'s `H₂²` charge `ε_QS(n') + ε_c + n·2⁻⁴⁴⁸`,
`n` the game's total hash queries). -/
theorem prEvent_accept_le_adaptive_comb_E (hT : liftInvOk T = true) (st₀ : Statement)
    (hparams : ∀ s, (stF s).params = st₀.params) (hdel : ∀ s, (stF s).delayed = false)
    (hcomb : ∀ s, (stF s).comb = some (M, dst)) (hdec : ∀ s, dec (muIn (stF s)) = some s)
    {n' : ℕ} (hn' : ∀ s l, (sysL s l).length = n') {εc : ℝ≥0∞}
    (hεc : ∀ s w, prU (Fin M → GF128) (fun l => (sysL s l).Holds w ∧ ¬witL s w) ≤ εc)
    (N : ℕ) (Wit : ι → ByteArray → (ℕ → GF128) → Prop)
    (hvals : ∀ s c1 (v : Prob.Bytes (16 * M)) w,
      (stF s).values c1 v.ba w = (sysL s (combDec v)).values w)
    (hdet : ∀ s, @CombDet (icPrg E.cipher) M T (stF s) (sysL s) (witL s) N (Wit s))
    (cf : Out ((ι × β) × QueryLog specIC) → Prop)
    (hcf : ∀ s g, ¬cf (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T (stF s) P E)) →
      KeysPre (stF s) E (jOf g P E) (gLog T (stF s) P E g) g)
    (n : ℕ) (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    let n'' := q + extractorQueries + verifierQueries
    Pr{let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r)) (Wit (stOut r)) r] ≤
      n'' .h21 * epsKOS #chal3Blocks (Chain.kosL st₀) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (M, dst)) n'')) + n'' .mu * stmtEps n'' .mu +
        Pr{let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[bindFailA stF E r] +
        Pr{let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[deadOpenA stF E r] +
        Pr{let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[cf r] := by
  classical
  intro n''
  let _ : HasPrg := icPrg E.cipher
  set oa := gameA T stF P E
  set mx := (simulateQ randomOracle oa).run' ∅
  set ntot := n + 2 + verifierTotal
  let cb : Option (ℕ × ByteArray) := some (M, dst)
  let ev : Out ((ι × β) × QueryLog specIC) → Prop := fun r =>
    r.2.2.accept = true ∧ ¬Extracted (stF (stOut r)) (Wit (stOut r)) r
  let bad : Dom → Table → Prop := fun t g =>
    combBadA T stF dec P E sysL witL dst N t g ∨ chainHitL cb (tableQueryLog oa) t g ∨
      stmtHit (tableQueryLog oa) t g
  let combE : Kind → ℝ≥0∞ := fun k => if k = .h22 then
    ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc + (ntot : ℝ≥0∞) / 2 ^ 448
    else chainEps st₀ chal3Blocks 0 N k
  let ε : Kind → ℝ≥0∞ := fun k => combE k + (hitEps n'' (combCount cb n'') k + stmtEps n'' k)
  have hKε : ∀ k ∉ adaptKinds, ε k = 0 := by
    intro k hk
    cases k <;> simp_all [adaptKinds, ε, combE, chainEps, hitEps, stmtEps]
  let K : Finset Dom := possibleQueryKeys oa ∪ Finset.univ.image (combKey M dst)
  have hK : ∀ u, combKey M dst u ∈ K := fun u =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  have hS : AllQueriesSatisfy oa (· ∈ K) :=
    (allQueriesSatisfy_possibleQueryKeys oa).mono fun d h => Finset.mem_union_left _ h
  let : SampleableType ((d : K) → Ans d.val) := SampleableType.piOfFintype _
  have hq'' := isKindQueryBound_gameA T stF P E hq
  have htrace : ∀ g : Table, (fun r => ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧
      ¬cf r) (evalWithAnswerFn (QueryImpl.ofFn g) oa) →
      ∃ e ∈ tableQueryLog oa g, bad e.1 g := by
    intro g h
    simp only [ev, bindFailA, deadOpenA, oa, evalWithAnswerFn_gameA, stOut_gameIC] at h
    obtain ⟨⟨hacc, hnex⟩, hnb, hnd, hnp⟩ := h
    set s := sA g P E
    set st := stF s
    have hlog : tableQueryLog oa g = gLog T st P E g := tableQueryLog_gameA T stF P E g
    by_cases hh : NoHit (gameIC T st P E) (chainHit T st P E) g
    swap
    · simp only [NoHit, not_forall, not_not] at hh
      obtain ⟨e, he, hhit⟩ := hh
      refine ⟨e, hlog ▸ he, Or.inr (Or.inl ?_)⟩
      unfold chainHitL
      rw [hlog, show cb = st.comb from (hcomb s).symm]
      exact hhit
    by_cases hs : NoStmtHit T st P E g
    swap
    · simp only [NoStmtHit, not_forall, not_not] at hs
      obtain ⟨e, he, hhit⟩ := hs
      refine ⟨e, hlog ▸ he, Or.inr (Or.inr ?_)⟩
      unfold stmtHit
      rw [hlog]
      exact hhit
    obtain ⟨leaves, hr, hacc', hbad⟩ := combBad_trace_ic hT st (sysL s) (witL s) dst (hcomb s) N
      (Wit s) (hvals s) P E (hdet s) cf (hcf s) g hacc hnex hnp hnb hnd hh
    set keys := (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2.keys
    obtain ⟨h1, h2, h3⟩ := stmtAt_ident dec T st P E g (hdel s) (hdec s) hh hs keys hacc' hr
    have hr0 : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, πOf g P E⟩
        (st.mu1 (Hashes.ofTable g))) (Proof.opening ⟨st.params, πOf g P E⟩)
        (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves := hr
    obtain ⟨hxL, hyL, hzL⟩ := inLog_verifyQ g T st (πOf g P E) hacc' hr0 keys
    have hconv := combBad_fixed_to_A T stF P E sysL witL dst N g
    have hmk : ∀ t, InLog (verifyQ T st (πOf g P E)) g t →
        stmtAt dec (gLog T st P E g) t = some s →
        combBad (CombData.ofSys (st := st) (preOf T st P E) (midOf T st P E)
          (sysL s) (witL s) (accOf T st P E) dst (preCells T st P E)) T chal3Blocks N t g →
        ∃ e ∈ tableQueryLog oa g, bad e.1 g := by
      intro t ht hst hb
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 (inLog_gLog T st P E g ht)
      refine ⟨e, hlog ▸ he, Or.inl ⟨s, ?_, hconv _ hb⟩⟩
      show stmtAt dec (tableQueryLog oa g) e.1 = some s
      rw [hlog]
      exact hst
    rcases hbad with hb | hb | hb
    · exact hmk _ hxL h1 hb
    · exact hmk _ hyL h2 hb
    · exact hmk _ hzL h3 hb
  have hgood := prEvent_randomOracle_le_of_fresh_bad_queries oa K hS (fun t => ε t.1) _
    (worstCaseCostBound_of_kindQueryBound oa adaptKinds ε hKε n'' hq'') ntot
    (isTotalQueryBound_gameA T stF E hn)
    (fun r => ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬cf r) bad ?_ htrace
  · have hsum : ∑ k ∈ adaptKinds, (n'' k : ℝ≥0∞) * ε k =
        n'' .h21 * epsKOS #chal3Blocks (Chain.kosL st₀) +
          n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
            ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
          n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
          hitSum n'' (hitEps n'' (combCount (some (M, dst)) n'')) + n'' .mu * stmtEps n'' .mu := by
      simp only [adaptKinds, ε, combE]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [chainEps, hitEps, stmtEps, hitSum, reduceCtorEq, ite_true, ite_false, zero_add,
        add_zero, mul_add, ntot]
      ring
    calc Pr{let r ← mx}[ev r]
        ≤ Pr{let r ← mx}[(ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬cf r) ∨
            (bindFailA stF E r ∨ (deadOpenA stF E r ∨ cf r))] :=
          prEvent_mono mx _ _ fun r h => by tauto
      _ ≤ Pr{let r ← mx}[ev r ∧ ¬bindFailA stF E r ∧ ¬deadOpenA stF E r ∧ ¬cf r] +
            (Pr{let r ← mx}[bindFailA stF E r] +
              (Pr{let r ← mx}[deadOpenA stF E r] + Pr{let r ← mx}[cf r])) :=
          (prEvent_or_le mx _ _).trans (add_le_add le_rfl ((prEvent_or_le mx _ _).trans
            (add_le_add le_rfl (prEvent_or_le mx _ _))))
      _ ≤ _ := by
          rw [← hsum]
          refine (add_le_add hgood le_rfl).trans_eq ?_
          ring
  · rintro c ⟨⟨k, x⟩, hx⟩ hc hcard
    refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ((prEvent_or_le _ _ _).trans
      (add_le_add ?_ ?_)))
    · by_cases hk : k = .h22
      · subst hk
        show _ ≤ combE .h22
        simp only [combE, ite_true]
        exact prEvent_combBadA_h22_le T stF dec P E sysL witL dst N hn' hεc K hK hx c hc hcard
      · refine prEvent_completeTable_cell_le c _ hc
          (fun t G => combBadA T stF dec P E sysL witL dst N t.val (extendTable K G)) _
          fun G => ?_
        simp only [extendTable_update]
        show _ ≤ combE k
        rw [show combE k = chainEps st₀ chal3Blocks 0 N k from by simp only [combE, hk, ite_false]]
        exact prEvent_combBadA_cell_le T stF dec P E sysL witL dst hT st₀ hparams N (k, x) hk _
    · refine prEvent_completeTable_cell_le c _ hc
        (fun t G => chainHitL cb (tableQueryLog oa) t.val (extendTable K G)) _ fun G => ?_
      simp only [extendTable_update]
      exact prEvent_chainHitL_le cb oa n'' hq'' _ _
    · refine prEvent_completeTable_cell_le c _ hc
        (fun t G => stmtHit (tableQueryLog oa) t.val (extendTable K G)) _ fun G => ?_
      simp only [extendTable_update]
      exact prEvent_stmtHit_le oa n'' hq'' _ _

end UnionComb

/-! ## The joint experiment, combined relations -/

section JointComb

variable {ι β : Type} (T : CrtTables) (stF : ι → Statement) (dec : ByteArray → Option ι)
  (P : OracleComp specIC (ByteArray × (ι × β))) {M : ℕ}
  (sysL : ι → (Fin M → GF128) → System GF128) (witL : ι → (ℕ → GF128) → Prop) (dst : ByteArray)

/-- **The adaptive bound for the combined relations in the joint experiment**
(`prEvent_accept_le_adaptive_comb_E` averaged over the cipher table, the failure events bounded
adaptively). -/
theorem prEvent_accept_le_adaptive_comb (hT : liftInvOk T = true) (st₀ : Statement)
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
    (hq : IsKindQueryBoundIC P q) :
    let n'' := q + extractorQueries + verifierQueries
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA T stF P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stF (stOut r)) (Wit (stOut r)) r] ≤
      n'' .h21 * epsKOS #chal3Blocks (Chain.kosL st₀) +
        n'' .h22 * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n') + εc +
          ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        n'' .h23 * ((N : ℝ≥0∞) / 2 ^ 128) +
        hitSum n'' (hitEps n'' (combCount (some (M, dst)) n'')) + n'' .mu * stmtEps n'' .mu +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
  intro n''
  have hE := fun E => prEvent_accept_le_adaptive_comb_E T stF dec P E sysL witL dst hT st₀
    hparams hdel hcomb hdec hn' hεc N Wit hvals (hdet E) (fun r => PostOut E r)
    (fun s g h => keysPre_of_not_postOut T (stF s) P E g h) n hn q hq
  have hdo := prEvent_joint_deadOpen_le_A T stF P st₀.params hparams q hq
  refine (prEvent_avg_le_add3 _ _ (fun E r => bindFailA stF E r) (fun E r => deadOpenA stF E r)
    (fun E r => PostOut E r) _ hE).trans ?_
  gcongr
  · exact (prEvent_joint_bindFail_le_A T stF P qE hqE).trans (add_le_add le_rfl hdo)
  · exact prEvent_joint_postOut_le_A T stF P qE hqE q hq

end JointComb

/-! ## Moussaka redemption and Ratatouille spend -/

section Rel

variable {ι β : Type}

set_option exponentiation.threshold 500 in
set_option maxRecDepth 4000 in
/-- **Moussaka redemption with an adaptively chosen instance**, in the random-oracle and
ideal-cipher model, every term explicit: the prover outputs a proof and an index `s` of the
instance `(anchors, nf, ctx_iss, ctx_red, challenge_digest)` it proves (at most 64 anchors), from
a family with injective instance encodings (`Spec.Moussaka.redeemEncode_inj`: the encoding
determines the anchors' digests, so the family must determine the anchors from their digests,
e.g. fixed anchors); the extractor runs at that instance. The verifier accepts and the
extractor's candidate is not a redemption witness for the chosen instance with probability

    ≤ (the bound of `moussakaRedeem_accept_le_full`) + (q₀+3)·(q₂₁+q₀+4)·2⁻²⁵⁶. -/
theorem moussakaRedeem_accept_le_adaptive (anc : ι → List UovPk)
    (hn64 : ∀ s, (anc s).length ≤ 64) (nf ctxIss ctxRed cd : ι → ByteArray) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows).instEnc
        ByteArray.empty)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (moussakaRedeem (anc (stOut r)) (nf (stOut r)) (ctxIss (stOut r)) (ctxRed (stOut r))
            (cd (stOut r)) labelRows)
          (fun _ => moussakaRedeemWit GF256.ofBits ((anc (stOut r)).map UovPk.map)
            (fnOf (nf (stOut r))) (fnOf (ctxIss (stOut r))) (fnOf (ctxRed (stOut r)))) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q Moussaka.M + stmtBindEps q := by
  classical
  set stF : ι → Statement := fun s =>
    moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) labelRows
  set st₀ := moussakaRedeem [] ByteArray.empty ByteArray.empty ByteArray.empty ByteArray.empty
    labelRows
  have hmu := muIn_injective (stF := stF) (dst := st₀.dst) (fun _ => rfl) hinj
  have h := prEvent_accept_le_adaptive_comb CrtGen.tables stF (decOf fun s => muIn (stF s)) P
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
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb q Moussaka.M rfl, stmtEps_game]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, moussakaRedeem]) (by norm_num [st₀, moussakaRedeem])
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4409) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n : ℝ≥0∞) + 2 + (verifierTotal : ℝ≥0∞)) / 2 ^ 448) +
          ((q .h23 : ℝ≥0∞) + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q Moussaka.M +
          stmtBindEps q +
          (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
          (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
          ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
        gcongr
    _ = _ := by push_cast; ring

set_option exponentiation.threshold 500 in
set_option maxRecDepth 8000 in
/-- **Ratatouille spend with an adaptively chosen instance** `(pk, nf, d, c_next, ctx_iss)`
(`d < 2⁶⁴`), as `moussakaRedeem_accept_le_adaptive` (the encoding `dig(pk) ‖ nf ‖ le64(d) ‖ c_next
‖ ctx_iss` injective on the family, which then determines `pk` from its digest, e.g. a fixed key):

    ≤ (the bound of `ratatouilleSpend_accept_le_full`) + (q₀+3)·(q₂₁+q₀+4)·2⁻²⁵⁶. -/
theorem ratatouilleSpend_accept_le_adaptive (pk : ι → UovPk) (nf : ι → ByteArray) (d : ι → ℕ)
    (hd : ∀ s, d s < 2 ^ 64) (cNext ctxIss : ι → ByteArray) (labelRows : Bool)
    (hinj : Function.Injective fun s =>
      (ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows).instEnc
        ByteArray.empty)
    (P : OracleComp specIC (ByteArray × (ι × β))) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (n : ℕ)
    (hn : IsQueryBoundP P (fun t => t.isLeft = true) n) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameA CrtGen.tables
      (fun s => ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _
          (ratatouilleSpend (pk (stOut r)) (nf (stOut r)) (d (stOut r)) (cNext (stOut r))
            (ctxIss (stOut r)) labelRows)
          (fun _ => ratatouilleSpendWit GF256.ofBits (pk (stOut r)).map (fnOf (nf (stOut r)))
            (d (stOut r)) (fnOf (cNext (stOut r))) (fnOf (ctxIss (stOut r)))) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
          (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
        (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        chainHitEpsComb q Ratatouille.uovM + stmtBindEps q := by
  classical
  set stF : ι → Statement := fun s =>
    ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) labelRows
  set st₀ := ratatouilleSpend ⟨ByteArray.empty, ByteArray.empty⟩ ByteArray.empty 0 ByteArray.empty
    ByteArray.empty labelRows
  have hmu := muIn_injective (stF := stF) (dst := st₀.dst) (fun _ => rfl) hinj
  have h := prEvent_accept_le_adaptive_comb CrtGen.tables stF (decOf fun s => muIn (stF s)) P
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
  rw [hitSum_add_extractorQueries, hitSum_hitEps_comb q Ratatouille.uovM rfl, stmtEps_game]
  have hkos : epsKOS #chal3Blocks (Chain.kosL st₀) ≤ (2 ^ 150 : ℝ≥0∞)⁻¹ :=
    epsKOS_chal3Blocks_le _ (by norm_num [st₀, ratatouilleSpend])
      (by norm_num [st₀, ratatouilleSpend])
  simp only [Pi.add_apply, extractorQueries, verifierQueries, reduceCtorEq, or_self, ite_false,
    add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  calc _ ≤ ((q .h21 : ℝ≥0∞) + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
          ((q .h22 : ℝ≥0∞) + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
            (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n : ℝ≥0∞) + 2 + (verifierTotal : ℝ≥0∞)) / 2 ^ 448) +
          ((q .h23 : ℝ≥0∞) + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) + chainHitEpsComb q Ratatouille.uovM +
          stmtBindEps q +
          (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
          (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
          ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
        gcongr
    _ = _ := by push_cast; ring

end Rel

end VoleMole.ROM.IC
