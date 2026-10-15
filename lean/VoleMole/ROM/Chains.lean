import VoleMole.ROM.UnionBound
import VoleMole.Prob.ChainRelations

/-!
# The per-chain terms over all random-oracle queries (plan M5)

The M2/M3 single-challenge bounds, applied to every `H₂¹`, `H₂²` and `H₂³` query of an adversary
against the lazy random oracle, and summed by the union bound of `ROM/UnionBound.lean`:

  `Pr[event] ≤ q₁·ε_KOS + q₂·ε_QS(n) + Q·N·2⁻¹²⁸ + ε_bind + ε_dead`

for an adversary making at most `q₁`, `q₂`, `Q` queries to `H₂¹`, `H₂²`, `H₂³`.

## What a query commits to

Each bad predicate reads the chain data the query commits to, as a function of the query input
and the answer table, with the hypothesis that it does not read the query's own answer:
* `preOf x g` at an `H₂¹` query `x`: the chain prefix (leaf keys, `c_i`, `c_mult`, `iv_pre`),
  through which `chal1 = g(H₂¹, x)` is checked (`Chain.kosQ`, `Chain.kosD`). It may read other
  cells (`H₁`, `H₄`, …): the leaf keys are not in `x` but determined by the commitments in it
  (binding, L1);
* `midOf y g` at an `H₂²` query `y`: the chain data up to `chal2` (`chal1`, `ũ`, `d`, `h_V`),
  hence the canonical witness `w* = uCanon + d` (L4 §5), and `csOf y g` the system checked;
* `accOf z g` at an `H₂³` query `z`: the set of `chal3` values a proof completing `z` would be
  accepted with.

## The bad predicates (`chainBad`) and their bounds (`prEvent_chainBad_update_le`)

* `H₂¹`: `chal1` is not KOS-good for the committed responses (L3): `≤ ε_KOS(|S|, L)`;
* `H₂²`: the system fails at `w*` and `zkHash = 0` (L4, `hQS` at the canonical slope):
  `≤ ε_QS(n)`;
* `H₂³`: at most `N` admissible `chal3` are accepted, and the answer is one of them:
  `≤ N·2⁻¹²⁸`.

The system `csOf y g` must not read the `H₂²` answer at `y`. This covers the issue relations; for
the combined relations the system reads `l = H(chal2 ‖ dst)`, a different cell chosen by the
answer, and the bound needs the freshness of `chal2 ‖ dst` (L0 §2.2): `ROM/Comb.lean`.

## The assembled bound (`prEvent_le_chain_terms`)

The event is split into "binding fails" (`ε_bind`, L1/C1–C3), "a dead-leaf tree is not fixed"
(`ε_dead`, L2), both named hypotheses about the game, and the rest, which must imply a bad query
for every complete answer table (`htrace`). `moussakaIssue_prEvent_le`,
`ratatouilleIssue_prEvent_le`: the numbers, `q₁·2⁻¹⁵⁰ + q₂·ε_QS(n) + Q·9·2⁻¹²⁸ + ε_bind + ε_dead`.

## The deterministic step (`chain_good_of_not_bad`, `*_good_of_not_bad`)

What `htrace` needs per chain: if a chain's `H₂¹` and `H₂²` queries are not bad, `*_extract_chain`
gives extraction or at most `N` accepted admissible `chal3` (`chain_prob`'s case analysis, per
table), and in the second case an accepted `H₂³` answer is a bad query (`chainBad_h23_of_accept`).
What is left of `htrace` is the identification of the accepted proof's chain in the log, with its
committed data, L2 and `hclaim1` ("same chain", binding: L1, M6). `ROM/Accept.lean` proves `htrace`
for the executable verifier run against the oracle, from exactly these (`SameChain`, binding, L2).
-/

open Finset ENNReal

namespace VoleMole.ROM

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.EndToEnd OracleComp OracleSpec

/-- The data a chain's random-oracle queries commit to (module doc). -/
structure ChainData (st : Statement) where
  /-- The chain prefix committed at an `H₂¹` query. -/
  preOf : ByteArray → Table → Chain
  /-- The chain data up to `chal2` committed at an `H₂²` query. -/
  midOf : ByteArray → Table → Chain
  /-- The system checked at an `H₂²` query. -/
  csOf : ByteArray → Table → System GF128
  /-- The accepted `chal3` values at an `H₂³` query. -/
  accOf : ByteArray → Table → Bytes 16 → Prop

namespace ChainData

variable {st : Statement} (C : ChainData st)

/-- The data at each query does not read the query's own answer. -/
structure Committed : Prop where
  pre : ∀ x (g : Table) u, C.preOf x (Function.update g (.h21, x) u) = C.preOf x g
  mid : ∀ y (g : Table) u, C.midOf y (Function.update g (.h22, y) u) = C.midOf y g
  cs : ∀ y (g : Table) u, C.csOf y (Function.update g (.h22, y) u) = C.csOf y g
  acc : ∀ z (g : Table) u, C.accOf z (Function.update g (.h23, z) u) = C.accOf z g

/-- The canonical witness `w* = uCanon + d` of the chain data at an `H₂²` query. -/
noncomputable def wC (T : CrtTables) (S : Finset Blocks) (y : ByteArray) (g : Table) :
    ℕ → GF128 :=
  wStar ((C.midOf y g).uCanon st T S) ((C.midOf y g).dc st)

end ChainData

/-- **The bad queries** (module doc): KOS-bad `chal1`, `zkHash = 0` for a failing canonical
witness, `chal3` landing in a set of at most `N` accepted values. -/
def chainBad {st : Statement} (C : ChainData st) (T : CrtTables) (S : Finset Blocks) (N : ℕ) :
    Dom → Table → Prop
  | (.h21, x), g => ¬Seed.KOSGood (chOf gfId mem_shortKeys (g (.h21, x)).ba) (S : Set Blocks)
      (lift T) ((C.preOf x g).kosQ st T) ((C.preOf x g).kosD st T)
  | (.h22, y), g => ¬(C.csOf y g).Holds (C.wC T S y g) ∧
      Seed.zkHash (C.csOf y g).length (gfOfBytes (g (.h22, y)).ba 0)
        (gfOfBytes (g (.h22, y)).ba 16) (gfOfBytes (g (.h22, y)).ba 32)
        ⟨W128.word (g (.h22, y)).ba 48, 0⟩ (valVec (C.csOf y g) (C.wC T S y g)) = 0
  | (.h23, z), g => (open Classical in #{x ∈ admissible | C.accOf z g x} ≤ N) ∧
      g (.h23, z) ∈ admissible ∧ C.accOf z g (g (.h23, z))
  | _, _ => False

/-- The per-query bound of each domain: `ε_KOS`, `ε_QS(n)`, `N·2⁻¹²⁸`, and `0` elsewhere. -/
noncomputable def chainEps (st : Statement) (S : Finset Blocks) (n N : ℕ) : Kind → ℝ≥0∞
  | .h21 => epsKOS #S (Chain.kosL st)
  | .h22 => ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n)
  | .h23 => (N : ℝ≥0∞) / 2 ^ 128
  | _ => 0

/-- The domains with a nonzero charge. -/
def chainKinds : Finset Kind := {.h21, .h22, .h23}

lemma chainEps_eq_zero (st : Statement) (S : Finset Blocks) (n N : ℕ) :
    ∀ k ∉ chainKinds, chainEps st S n N k = 0 := by
  intro k hk
  cases k <;> simp_all [chainKinds, chainEps]

lemma prEvent_false_le {α : Type} [SampleableType α] [Fintype α] (ε : ℝ≥0∞) :
    Pr{let _x ← $ᵗ α}[False] ≤ ε :=
  (prEvent_uniformSample_eq_prU (fun _ : α => False)).trans_le (prU_false.trans_le zero_le)

/-- **Each bad predicate has its single-challenge bound** when only its own cell is resampled,
for every background table: L3 (`prU_kos_bad_le`) at `H₂¹`, L4 at the canonical slope
(`prU_qs_bad_le`) at `H₂²`, the final step (`prU_accept_le`) at `H₂³`. -/
theorem prEvent_chainBad_update_le {T : CrtTables} (hT : liftInvOk T = true) {st : Statement}
    (C : ChainData st) (hC : C.Committed) (S : Finset Blocks) {n : ℕ}
    (hn : ∀ y g, (C.csOf y g).length = n) (N : ℕ) (t : Dom) (g : Table) :
    Pr{let u ← $ᵗ (Ans t)}[chainBad C T S N t (Function.update g t u)] ≤
      chainEps st S n N t.1 := by
  classical
  obtain ⟨k, x⟩ := t
  cases k
  case h21 =>
    have h : ∀ u : Ans (.h21, x), chainBad C T S N (.h21, x) (Function.update g (.h21, x) u) ↔
        ¬Seed.KOSGood (chOf gfId mem_shortKeys (u : Bytes 136).ba) (S : Set Blocks) (lift T)
          ((C.preOf x g).kosQ st T) ((C.preOf x g).kosD st T) := fun u => by
      simp only [chainBad]
      rw [Function.update_self, hC.pre]
    simp_rw [h]
    exact prEvent_uniformSample_le (α := Bytes 136) (prU_kos_bad_le hT S _ _)
  case h22 =>
    have h : ∀ u : Ans (.h22, x), chainBad C T S N (.h22, x) (Function.update g (.h22, x) u) ↔
        ¬(C.csOf x g).Holds (C.wC T S x g) ∧
          Seed.zkHash (C.csOf x g).length (gfOfBytes (u : Bytes 56).ba 0)
            (gfOfBytes (u : Bytes 56).ba 16) (gfOfBytes (u : Bytes 56).ba 32)
            ⟨W128.word (u : Bytes 56).ba 48, 0⟩ (valVec (C.csOf x g) (C.wC T S x g)) = 0 :=
      fun u => by
        simp only [chainBad, ChainData.wC]
        rw [Function.update_self, hC.mid, hC.cs]
    simp_rw [h]
    refine prEvent_uniformSample_le (α := Bytes 56)
      ((prU_qs_bad_le (C.csOf x g) _).trans_eq ?_)
    rw [hn]; rfl
  case h23 =>
    have h : ∀ u : Ans (.h23, x), chainBad C T S N (.h23, x) (Function.update g (.h23, x) u) ↔
        #{x' ∈ admissible | C.accOf x g x'} ≤ N ∧ (u : Bytes 16) ∈ admissible ∧ C.accOf x g u :=
        fun u => by
      simp only [chainBad]
      rw [Function.update_self, hC.acc]
    simp_rw [h]
    by_cases hN : #{x' ∈ admissible | C.accOf x g x'} ≤ N
    · refine prEvent_uniformSample_le (α := Bytes 16) (le_trans (prU_mono fun u h => h.2) ?_)
      exact prU_accept_le _ hN
    · simp only [hN, false_and]
      exact prEvent_false_le _
  all_goals
    simp only [chainBad]
    exact prEvent_false_le _

/-- **The per-chain terms over all queries.** An adversary `oa` with at most `q k` queries to each
domain, against the lazy random oracle. If, outside the binding failure `bindFail` and the
dead-leaf failure `deadFail`, the event implies a bad `H₂¹`, `H₂²` or `H₂³` query for every
complete answer table (`htrace`), then
`Pr[event] ≤ q₁·ε_KOS(|S|, L) + q₂·ε_QS(n) + Q·N·2⁻¹²⁸ + ε_bind + ε_dead`. -/
theorem prEvent_le_chain_terms {α : Type} {T : CrtTables} (hT : liftInvOk T = true)
    {st : Statement} (C : ChainData st) (hC : C.Committed) (S : Finset Blocks) {n : ℕ}
    (hn : ∀ y g, (C.csOf y g).length = n) (N : ℕ) (oa : OracleComp spec α) (q : Kind → ℕ)
    (hq : IsKindQueryBound oa q) (event bindFail deadFail : α → Prop) {εb εd : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[bindFail r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[deadFail r] ≤ εd)
    (htrace : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) oa;
      event r → ¬bindFail r → ¬deadFail r → ∃ e ∈ tableQueryLog oa g, chainBad C T S N e.1 g) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤
      q .h21 * epsKOS #S (Chain.kosL st) +
        q .h22 * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) +
        q .h23 * ((N : ℝ≥0∞) / 2 ^ 128) + εb + εd := by
  let mx := (simulateQ randomOracle oa).run' ∅
  have hgood : Pr{let r ← mx}[event r ∧ ¬bindFail r ∧ ¬deadFail r] ≤
      q .h21 * epsKOS #S (Chain.kosL st) +
        q .h22 * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) n) +
        q .h23 * ((N : ℝ≥0∞) / 2 ^ 128) := by
    refine (prEvent_exists_bad_query_le oa q hq _ (chainBad C T S N) chainKinds
      (chainEps st S n N) (chainEps_eq_zero st S n N)
      (prEvent_chainBad_update_le hT C hC S hn N)
      fun g h => htrace g h.1 h.2.1 h.2.2).trans_eq ?_
    simp [chainKinds, chainEps, add_assoc]
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

/-- **A chain whose `H₂¹` and `H₂²` queries are not bad satisfies the extraction theorem's
conclusion.** For a chain `ch` with the prefix committed at its `H₂¹` query `x`, the data up to
`chal2` committed at its `H₂²` query `y` (`chal1 = g(H₂¹, x)`, `chal2 = g(H₂², y)`), and a
deterministic theorem `hdet` of the shape of the issue relations' `*_extract_chain`: not KOS-bad
gives `hkos`, and not QS-bad at the canonical witness gives `hQS` for every slope on
`A ⊆ A_V` (`forall_slope_of_uCanon`). This is `chain_prob`'s case analysis, per table. -/
theorem chain_good_of_not_bad {T : CrtTables} (hT : liftInvOk T = true) {st : Statement}
    (C : ChainData st) (S : Finset Blocks) (N : ℕ) {x y : ByteArray} {g : Table} {ch : Chain}
    (hpre : Chain.SamePrefix st (C.preOf x g) (C.midOf y g))
    (hc1 : (C.midOf y g).chal1 = (g (.h21, x) : Bytes 136).ba)
    (hmid : Chain.SameMid st (C.midOf y g) ch) (hc2 : ch.chal2 = (g (.h22, y) : Bytes 56).ba)
    (P : Finset Blocks → Prop) (Good : Prop)
    (hdet : ∀ A : Finset Blocks, (∀ Δ ∈ A, ch.OnChain st T Δ) → (A : Set Blocks) ⊆ S →
      Seed.KOSGood ch.kosCh (S : Set Blocks) (lift T) (ch.kosQ st T) (ch.kosD st T) →
      (2 ≤ A.card → ∀ uStar,
        (∀ j, ∃ v, ∀ Δ ∈ A, ch.Qw st T j Δ = v + uStar j * lift T Δ) →
        ¬(C.csOf y g).Holds (wStar uStar (ch.dc st)) →
        Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
          ⟨W128.word ch.chal2 48, 0⟩ (valVec (C.csOf y g) (wStar uStar (ch.dc st))) ≠ 0) →
      P A → Good)
    (h1 : ¬chainBad C T S N (.h21, x) g) (h2 : ¬chainBad C T S N (.h22, y) g)
    (hP : P (onSet st T ch S)) : Good := by
  simp only [chainBad, not_not, not_and] at h1 h2
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
  refine hdet _ hA (Finset.coe_subset.2 hAS) hk (fun h2' uStar hs hnot => ?_) hP
  rw [Chain.slope_eq_uCanon hT hkM hAV h2' (hmid.isSlope_iff.1 hs), hmid.dc_eq] at hnot ⊢
  rw [hc2]
  exact h2 hnot

/-- **Moussaka issuance at one chain of the random-oracle game**: outside L2 and `hclaim1`
(`ChainHyps`), a chain whose `H₂¹` and `H₂²` queries are not bad yields a witness or has at most 9
accepted admissible `chal3`. -/
theorem moussakaIssue_good_of_not_bad (t ctxIss : ByteArray) (labelRows : Bool)
    (C : ChainData (moussakaIssue t ctxIss labelRows)) (N : ℕ) {x y : ByteArray} {g : Table}
    {ch : Chain}
    (hpre : Chain.SamePrefix (moussakaIssue t ctxIss labelRows) (C.preOf x g) (C.midOf y g))
    (hc1 : (C.midOf y g).chal1 = (g (.h21, x) : Bytes 136).ba)
    (hmid : Chain.SameMid (moussakaIssue t ctxIss labelRows) (C.midOf y g) ch)
    (hc2 : ch.chal2 = (g (.h22, y) : Bytes 56).ba) (hcs : C.csOf y g = moussakaIssueSys t ctxIss)
    (hvals : ∀ w, ch.vals w = (moussakaIssueSys t ctxIss).values w)
    (known : Finset (Fin BAVC.tau)) (acc : Bytes 16 → Prop) [DecidablePred acc]
    (h1 : ¬chainBad C CrtGen.tables chal3Blocks N (.h21, x) g)
    (h2 : ¬chainBad C CrtGen.tables chal3Blocks N (.h22, y) g)
    (hhyp : ChainHyps (onSet (moussakaIssue t ctxIss labelRows) CrtGen.tables ch chal3Blocks)
      known acc) :
    (∃ i ∈ known, moussakaIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)
        (candidate (F := GF128) (ch.u (moussakaIssue t ctxIss labelRows))
          (ch.dc (moussakaIssue t ctxIss labelRows)) i)) ∨
      #{x ∈ admissible | acc x} ≤ 9 :=
  chain_good_of_not_bad liftInvOk_tables C chal3Blocks N hpre hc1 hmid hc2
    (fun A => ChainHyps A known acc) _
    (fun A hA hAS hkos hQS hP => moussakaIssue_extract_chain t ctxIss labelRows ch hvals hA hAS
      hkos hP.1 (by rwa [hcs] at hQS) admissible deltaBlocks deltaBlocks_injOn _ hP.2) h1 h2 hhyp

/-- **Ratatouille issuance at one chain of the random-oracle game** (as
`moussakaIssue_good_of_not_bad`). -/
theorem ratatouilleIssue_good_of_not_bad (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray)
    (labelRows : Bool) (C : ChainData (ratatouilleIssue c tInit ctxIss labelRows)) (N : ℕ)
    {x y : ByteArray} {g : Table} {ch : Chain}
    (hpre : Chain.SamePrefix (ratatouilleIssue c tInit ctxIss labelRows) (C.preOf x g)
      (C.midOf y g))
    (hc1 : (C.midOf y g).chal1 = (g (.h21, x) : Bytes 136).ba)
    (hmid : Chain.SameMid (ratatouilleIssue c tInit ctxIss labelRows) (C.midOf y g) ch)
    (hc2 : ch.chal2 = (g (.h22, y) : Bytes 56).ba)
    (hcs : C.csOf y g = ratatouilleIssueSys c tInit ctxIss)
    (hvals : ∀ w, ch.vals w = (ratatouilleIssueSys c tInit ctxIss).values w)
    (known : Finset (Fin BAVC.tau)) (acc : Bytes 16 → Prop) [DecidablePred acc]
    (h1 : ¬chainBad C CrtGen.tables chal3Blocks N (.h21, x) g)
    (h2 : ¬chainBad C CrtGen.tables chal3Blocks N (.h22, y) g)
    (hhyp : ChainHyps (onSet (ratatouilleIssue c tInit ctxIss labelRows) CrtGen.tables ch
      chal3Blocks) known acc) :
    (∃ i ∈ known, ratatouilleIssueWit (fnOf c) tInit (fnOf ctxIss)
        (candidate (F := GF128) (ch.u (ratatouilleIssue c tInit ctxIss labelRows))
          (ch.dc (ratatouilleIssue c tInit ctxIss labelRows)) i)) ∨
      #{x ∈ admissible | acc x} ≤ 9 :=
  chain_good_of_not_bad liftInvOk_tables C chal3Blocks N hpre hc1 hmid hc2
    (fun A => ChainHyps A known acc) _
    (fun A hA hAS hkos hQS hP => ratatouilleIssue_extract_chain c tInit ctxIss labelRows ch hvals
      hA hAS hkos hP.1 (by rwa [hcs] at hQS) admissible deltaBlocks deltaBlocks_injOn _ hP.2)
    h1 h2 hhyp

-- Elaborating `g (.h23, z) ∈ admissible` against `chainBad`'s match needs a deeper recursion.
set_option maxRecDepth 4000 in
/-- **The `H₂³` query of a chain with few accepted values is bad when it is accepted**: the
remaining case of the trace (`*_good_of_not_bad`'s second disjunct). -/
theorem chainBad_h23_of_accept {st : Statement} (C : ChainData st) (T : CrtTables)
    (S : Finset Blocks) (N : ℕ) {z : ByteArray} {g : Table}
    (hN : open Classical in #{x ∈ admissible | C.accOf z g x} ≤ N)
    (hadm : g.chal3 z ∈ admissible) (hacc : C.accOf z g (g.chal3 z)) :
    chainBad C T S N (.h23, z) g :=
  (⟨hN, hadm, hacc⟩ : (open Classical in #{x ∈ admissible | C.accOf z g x} ≤ N) ∧
    g.chal3 z ∈ admissible ∧ C.accOf z g (g.chal3 z))

/-! ## The issue relations, numerically -/

/-- The chain data of a relation with a fixed system `cs`. -/
def ChainData.ofSys {st : Statement} (preOf midOf : ByteArray → Table → Chain)
    (cs : System GF128) (accOf : ByteArray → Table → Bytes 16 → Prop) : ChainData st :=
  ⟨preOf, midOf, fun _ _ => cs, accOf⟩

lemma ChainData.ofSys_committed {st : Statement} (preOf midOf : ByteArray → Table → Chain)
    (cs : System GF128) (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hpre : ∀ x (g : Table) u, preOf x (Function.update g (.h21, x) u) = preOf x g)
    (hmid : ∀ y (g : Table) u, midOf y (Function.update g (.h22, y) u) = midOf y g)
    (hacc : ∀ z (g : Table) u, accOf z (Function.update g (.h23, z) u) = accOf z g) :
    (ChainData.ofSys (st := st) preOf midOf cs accOf).Committed :=
  ⟨hpre, hmid, fun _ _ _ => rfl, hacc⟩

/-- **Moussaka issuance over all random-oracle queries**:
`Pr[event] ≤ q₁·2⁻¹⁵⁰ + q₂·ε_QS(4008) + Q·9·2⁻¹²⁸ + ε_bind + ε_dead`. -/
theorem moussakaIssue_prEvent_le {α : Type} (t ctxIss : ByteArray) (labelRows : Bool)
    (preOf midOf : ByteArray → Table → Chain) (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hC : (ChainData.ofSys (st := moussakaIssue t ctxIss labelRows) preOf midOf
      (moussakaIssueSys t ctxIss) accOf).Committed)
    (oa : OracleComp spec α) (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (event bindFail deadFail : α → Prop) {εb εd : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[bindFail r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[deadFail r] ≤ εd)
    (htrace : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) oa;
      event r → ¬bindFail r → ¬deadFail r → ∃ e ∈ tableQueryLog oa g,
        chainBad (ChainData.ofSys (st := moussakaIssue t ctxIss labelRows) preOf midOf
          (moussakaIssueSys t ctxIss) accOf) CrtGen.tables chal3Blocks 9 e.1 g) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤
      q .h21 * (2 ^ 150 : ℝ≥0∞)⁻¹ + q .h22 * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        q .h23 * ((9 : ℝ≥0∞) / 2 ^ 128) + εb + εd := by
  refine (prEvent_le_chain_terms liftInvOk_tables _ hC chal3Blocks
    (fun _ _ => Moussaka.issueSystem_length _ _) 9 oa q hq event bindFail deadFail hbind hdead
    htrace).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ (by norm_num [moussakaIssue]) (by norm_num [moussakaIssue])
  · norm_num

/-- **Ratatouille issuance over all random-oracle queries**:
`Pr[event] ≤ q₁·2⁻¹⁵⁰ + q₂·ε_QS(3776) + Q·9·2⁻¹²⁸ + ε_bind + ε_dead`. -/
theorem ratatouilleIssue_prEvent_le {α : Type} (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray)
    (labelRows : Bool) (preOf midOf : ByteArray → Table → Chain)
    (accOf : ByteArray → Table → Bytes 16 → Prop)
    (hC : (ChainData.ofSys (st := ratatouilleIssue c tInit ctxIss labelRows) preOf midOf
      (ratatouilleIssueSys c tInit ctxIss) accOf).Committed)
    (oa : OracleComp spec α) (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (event bindFail deadFail : α → Prop) {εb εd : ℝ≥0∞}
    (hbind : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[bindFail r] ≤ εb)
    (hdead : Pr{let r ← (simulateQ randomOracle oa).run' ∅}[deadFail r] ≤ εd)
    (htrace : ∀ g : Table, let r := evalWithAnswerFn (QueryImpl.ofFn g) oa;
      event r → ¬bindFail r → ¬deadFail r → ∃ e ∈ tableQueryLog oa g,
        chainBad (ChainData.ofSys (st := ratatouilleIssue c tInit ctxIss labelRows) preOf midOf
          (ratatouilleIssueSys c tInit ctxIss) accOf) CrtGen.tables chal3Blocks 9 e.1 g) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] ≤
      q .h21 * (2 ^ 150 : ℝ≥0∞)⁻¹ + q .h22 * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
        q .h23 * ((9 : ℝ≥0∞) / 2 ^ 128) + εb + εd := by
  refine (prEvent_le_chain_terms liftInvOk_tables _ hC chal3Blocks
    (fun _ _ => Ratatouille.issueSystem_length _ _ _) 9 oa q hq event bindFail deadFail hbind
    hdead htrace).trans ?_
  gcongr
  · exact epsKOS_chal3Blocks_le _ (by norm_num [ratatouilleIssue]) (by norm_num [ratatouilleIssue])
  · norm_num

end VoleMole.ROM
