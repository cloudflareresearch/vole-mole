import VoleMole.ROM.UnionBound

/-!
# Domain separation: one random oracle with disjoint input domains is the per-domain oracles

`ROM/Basic.lean` answers every hash by an oracle indexed by `Dom = Kind × ByteArray`: a separate
random function per L0 domain. SHAKE128 is one function of its input; the domains are told apart
by the input alone (the final byte, and the lengths of the three `H₁` shapes; L0 §2.1,
`Protocols/DomainSeparation.lean`). This file proves that the two models agree.

* `spec₁ κ`: **one random oracle on byte strings**, answering an input `x` with `(κ x).outLen`
  bytes, where `κ : ByteArray → Kind` reads off the domain of an input (any function: L0's rule is
  one).
* `route κ oa`: a computation against the per-domain oracles, run against the single oracle: the
  query `(k, x)` asks `x` (the answer is resized to `k.outLen` bytes; for `κ x = k` the sizes agree).
* `prEvent_route_eq`: **if every query `(k, x)` of `oa` is in its domain (`κ x = k`), the lazy
  single oracle and the lazy per-domain oracles give every event the same probability.** Proof:
  restrict both to finite key sets (VCVio's `restrictQueries`), pass to eager complete tables
  (`evalDist_simulateQ_randomOracle_run'_eq_completeTable`), and identify the two uniform tables by
  the bijection `(k, x) ↦ x` on the queried keys (injective because `k = κ x`).

So the per-domain model of `ROM/` is the single-SHAKE model, for every adversary whose queries
respect the domain rule `κ`; what remains a modelling step is SHAKE128 itself as a random oracle
(and the variable output length, here fixed per domain).
-/

open ENNReal OracleComp OracleSpec

namespace VoleMole.ROM

open VoleMole.Prob VoleMole.Verifier

/-- `n` bytes resized to `m` (truncated, or padded with zeros); the identity for `m = n`. -/
def Bytes.resize {n : ℕ} (m : ℕ) (u : Bytes n) : Bytes m :=
  fun i => if h : i.val < n then u ⟨i, h⟩ else 0

lemma Bytes.resize_resize {n m : ℕ} (u : Bytes n) (h : m = n) :
    Bytes.resize n (Bytes.resize m u) = u := by
  subst h
  funext i
  simp [Bytes.resize]

/-- **The single random oracle**: input `x` answered with `(κ x).outLen` bytes. -/
abbrev spec₁ (κ : ByteArray → Kind) : OracleSpec ByteArray :=
  OracleSpec.ofFn fun x => Bytes (κ x).outLen

/-- A per-domain query `(k, x)` asked of the single oracle at `x`. -/
def routeImpl (κ : ByteArray → Kind) : QueryImpl spec (OracleComp (spec₁ κ)) :=
  fun d => Bytes.resize d.1.outLen <$>
    (liftM ((spec₁ κ).query d.2) : OracleComp (spec₁ κ) (Bytes (κ d.2).outLen))

/-- A computation against the per-domain oracles, run against the single oracle. -/
def route {α : Type} (κ : ByteArray → Kind) (oa : OracleComp spec α) : OracleComp (spec₁ κ) α :=
  simulateQ (routeImpl κ) oa

variable {α : Type} (κ : ByteArray → Kind)

/-- Against a complete table `G` of the single oracle, the routed computation runs against the
per-domain table `(k, x) ↦ G x` (resized). -/
theorem evalWithAnswerFn_route (oa : OracleComp spec α) (G : (x : ByteArray) → Bytes (κ x).outLen) :
    evalWithAnswerFn (QueryImpl.ofFn G) (route κ oa) =
      evalWithAnswerFn (QueryImpl.ofFn fun d : Dom => Bytes.resize d.1.outLen (G d.2)) oa := by
  rw [route, evalWithAnswerFn_simulateQ]
  rfl

/-- The routed computation queries the second components of the original queries. -/
theorem allQueriesSatisfy_route {oa : OracleComp spec α} {P : Dom → Prop}
    (h : AllQueriesSatisfy oa P) : AllQueriesSatisfy (route κ oa) fun x => ∃ d, P d ∧ d.2 = x := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
    rw [route, simulateQ_bind, simulateQ_spec_query]
    simp only [routeImpl, bind_map_left]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨⟨t, ht, rfl⟩, fun u => ih _ (hk _)⟩

/-- The second component, from a set of keys to their inputs. -/
def sndOn {S : Finset Dom} (d : S) : S.image Prod.snd := ⟨d.1.2, Finset.mem_image_of_mem _ d.2⟩

section Eager

variable {κ} {S : Finset Dom} (hS : ∀ d ∈ S, κ d.2 = d.1)
include hS

lemma sndOn_bijective : Function.Bijective (sndOn (S := S)) := by
  refine ⟨fun d d' h => ?_, fun x => ?_⟩
  · have h2 : d.1.2 = d'.1.2 := congrArg Subtype.val h
    have h1 : d.1.1 = d'.1.1 := by rw [← hS _ d.2, ← hS _ d'.2, h2]
    exact Subtype.ext (Prod.ext h1 h2)
  · obtain ⟨d, hd, hx⟩ := Finset.mem_image.1 x.2
    exact ⟨⟨d, hd⟩, Subtype.ext hx⟩

/-- **The two uniform tables are the same**: a table of the single oracle on the inputs of `S`,
read as a per-domain table on `S` (each cell resized, sizes agreeing on `S`). -/
noncomputable def tableEquiv :
    ((x : S.image Prod.snd) → Bytes (κ x.1).outLen) ≃ ((d : S) → Ans d.1) where
  toFun G d := Bytes.resize d.1.1.outLen (G (sndOn d))
  invFun H x := Bytes.resize (κ x.1).outLen (H ((Equiv.ofBijective _ (sndOn_bijective hS)).symm x))
  left_inv G := by
    funext x
    set d := (Equiv.ofBijective _ (sndOn_bijective hS)).symm x
    have hx : sndOn d = x := (Equiv.ofBijective _ (sndOn_bijective hS)).apply_symm_apply x
    have hk : d.1.1.outLen = (κ x.1).outLen := by
      rw [← hS _ d.2]; exact congrArg (fun y : S.image Prod.snd => (κ y.1).outLen) hx
    show Bytes.resize _ (Bytes.resize _ (G (sndOn d))) = G x
    rw [show Bytes.resize (κ x.1).outLen (Bytes.resize d.1.1.outLen (G (sndOn d))) =
        Bytes.resize (κ x.1).outLen (Bytes.resize d.1.1.outLen (G x)) from
      congrArg (fun y => Bytes.resize (κ x.1).outLen (Bytes.resize d.1.1.outLen (G y))) hx]
    exact Bytes.resize_resize _ hk
  right_inv H := by
    funext d
    have hd : (Equiv.ofBijective _ (sndOn_bijective hS)).symm (sndOn d) = d :=
      (Equiv.ofBijective _ (sndOn_bijective hS)).symm_apply_apply d
    show Bytes.resize _ (Bytes.resize _ (H _)) = H d
    rw [show Bytes.resize d.1.1.outLen (Bytes.resize (κ (sndOn d).1).outLen
        (H ((Equiv.ofBijective _ (sndOn_bijective hS)).symm (sndOn d)))) =
        Bytes.resize d.1.1.outLen (Bytes.resize (κ (sndOn d).1).outLen (H d)) from
      congrArg (fun y => Bytes.resize d.1.1.outLen (Bytes.resize (κ (sndOn d).1).outLen
        (H y))) hd]
    exact Bytes.resize_resize _ (congrArg Kind.outLen (hS _ d.2))

end Eager

lemma allQueriesSatisfy_and {ι : Type} {sp : OracleSpec ι} {oa : OracleComp sp α}
    {P Q : ι → Prop} (hP : AllQueriesSatisfy oa P) (hQ : AllQueriesSatisfy oa Q) :
    AllQueriesSatisfy oa fun t => P t ∧ Q t := by
  induction oa using OracleComp.inductionOn with
  | pure _ => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    obtain ⟨hp, hk⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hP
    obtain ⟨hq, hk'⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hQ
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨⟨hp, hq⟩, fun u => ih u (hk u) (hk' u)⟩

/-- **Domain separation ⇒ independent oracles.** If every query `(k, x)` of `oa` lies in its
domain (`κ x = k`), then running `oa` against one lazy random oracle on byte strings (`route`)
and against the lazy per-domain oracles of `ROM/Basic.lean` gives every event the same
probability. -/
theorem prEvent_route_eq (oa : OracleComp spec α) (hκ : AllQueriesSatisfy oa fun d => κ d.2 = d.1)
    (event : α → Prop) :
    Pr{let r ← (simulateQ randomOracle (route κ oa)).run' ∅}[event r] =
      Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] := by
  classical
  let S : Finset Dom := (possibleQueryKeys oa).filter fun d => κ d.2 = d.1
  have hSκ : ∀ d ∈ S, κ d.2 = d.1 := fun d hd => (Finset.mem_filter.1 hd).2
  have hS : AllQueriesSatisfy oa (· ∈ S) :=
    (allQueriesSatisfy_and (allQueriesSatisfy_possibleQueryKeys oa) hκ).mono fun d hd =>
      Finset.mem_filter.2 hd
  let S₁ := S.image Prod.snd
  have hS₁ : AllQueriesSatisfy (route κ oa) (· ∈ S₁) :=
    (allQueriesSatisfy_route κ hS).mono fun x ⟨d, hd, hx⟩ => hx ▸ Finset.mem_image_of_mem _ hd
  let : SampleableType ((d : S) → Ans d.1) := SampleableType.piOfFintype _
  let : SampleableType ((x : S₁) → Bytes (κ x.1).outLen) := SampleableType.piOfFintype _
  let : MeasurableSpace α := ⊤
  have e1 : (simulateQ randomOracle (restrictQueries S oa hS)).run' ∅ =
      (simulateQ randomOracle oa).run' ∅ := randomOracle_restrictQueries S oa hS ∅
  have e2 : (simulateQ randomOracle (restrictQueries S₁ (route κ oa) hS₁)).run' ∅ =
      (simulateQ randomOracle (route κ oa)).run' ∅ := randomOracle_restrictQueries S₁ _ hS₁ ∅
  rw [← e1, ← e2]
  have h1 := evalDist_simulateQ_randomOracle_run'_eq_completeTable (restrictQueries S oa hS) ∅
  have h2 := evalDist_simulateQ_randomOracle_run'_eq_completeTable
    (restrictQueries S₁ (route κ oa) hS₁) ∅
  simp only [completeTable_empty] at h1 h2
  rw [(EvalDistEq.of_evalDist_eq h1).prEvent_eq event,
    (EvalDistEq.of_evalDist_eq h2).prEvent_eq event]
  simp only [prEvent_norm]
  rw [prEvent_uniformSample_eq_prU, prEvent_uniformSample_eq_prU, prU_map_equiv (tableEquiv hSκ)]
  congr 1
  funext G₁
  simp only [Function.comp]
  congr 1
  let R₁ : ByteArray → Type := fun x => Bytes (κ x).outLen
  have hG₁ : (fun d : S₁ => extendTable (R := R₁) S₁ G₁ d.val) = G₁ :=
    funext (extendTable_subtype (R := R₁) S₁ G₁)
  have ha := evalWithAnswerFn_restrictQueries S₁ (route κ oa) hS₁ (extendTable (R := R₁) S₁ G₁)
  rw [hG₁] at ha
  rw [ha, evalWithAnswerFn_route, ← evalWithAnswerFn_restrictQueries S oa hS]
  congr 2
  funext d
  show Bytes.resize _ (extendTable (R := R₁) S₁ G₁ d.1.2) = Bytes.resize _ (G₁ (sndOn d))
  rw [← extendTable_subtype (R := R₁) S₁ G₁ (sndOn d)]
  rfl

/-! ## Every single-oracle adversary is a per-domain adversary -/

lemma Bytes.resize_self {n : ℕ} (u : Bytes n) : Bytes.resize n u = u := by
  funext i; simp [Bytes.resize]

/-- A computation against the single oracle, as a computation against the per-domain oracles:
the query `x` asks `(κ x, x)`. -/
def unroute (oa : OracleComp (spec₁ κ) α) : OracleComp spec α :=
  simulateQ (fun x => (liftM (spec.query (κ x, x)) : OracleComp spec (Bytes (κ x).outLen))) oa

lemma unroute_query_bind (x : ByteArray) (k : Bytes (κ x).outLen → OracleComp (spec₁ κ) α) :
    unroute κ (liftM ((spec₁ κ).query x) >>= k) =
      liftM (spec.query (κ x, x)) >>= fun u => unroute κ (k u) := by
  rw [unroute, simulateQ_bind, simulateQ_spec_query]
  rfl

/-- Routing undoes `unroute`. -/
theorem route_unroute (oa : OracleComp (spec₁ κ) α) : route κ (unroute κ oa) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind x k ih =>
    rw [unroute_query_bind, route, simulateQ_bind, simulateQ_spec_query]
    simp only [routeImpl, bind_map_left, Bytes.resize_self]
    exact congrArg _ (funext fun u => ih u)

/-- `unroute`'s queries are in their domains. -/
theorem allQueriesSatisfy_unroute (oa : OracleComp (spec₁ κ) α) :
    AllQueriesSatisfy (unroute κ oa) fun d => κ d.2 = d.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind x k ih =>
    rw [unroute_query_bind]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨rfl, fun u => ih u⟩

/-- **Domain separation, for any single-oracle adversary**: against the lazy single oracle, `oa`
has the event probabilities of `unroute κ oa` against the lazy per-domain oracles. -/
theorem prEvent_unroute_eq (oa : OracleComp (spec₁ κ) α) (event : α → Prop) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[event r] =
      Pr{let r ← (simulateQ randomOracle (unroute κ oa)).run' ∅}[event r] := by
  rw [← prEvent_route_eq κ (unroute κ oa) (allQueriesSatisfy_unroute κ oa), route_unroute]

/-- `oa` asks at most `q k` inputs of domain `k` (`κ x = k`), on every path. -/
def IsDomainQueryBound (oa : OracleComp (spec₁ κ) α) (q : Kind → ℕ) : Prop :=
  IsQueryBound oa q (fun x b => 0 < b (κ x)) (fun x b => Function.update b (κ x) (b (κ x) - 1))

/-- Per-domain counts of a single-oracle adversary are the per-kind counts of `unroute`. -/
theorem isKindQueryBound_unroute {oa : OracleComp (spec₁ κ) α} {q : Kind → ℕ}
    (h : IsDomainQueryBound κ oa q) : IsKindQueryBound (unroute κ oa) q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind x k ih =>
    obtain ⟨h0, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).mp h
    rw [unroute_query_bind]
    exact isKindQueryBound_query_bind_iff.2 ⟨h0, fun u => ih u (hk u)⟩

/-- Total counts transfer to `unroute`. -/
theorem isTotalQueryBound_unroute {oa : OracleComp (spec₁ κ) α} {n : ℕ}
    (h : IsTotalQueryBound oa n) : IsTotalQueryBound (unroute κ oa) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind x k ih =>
    obtain ⟨h0, hk⟩ := isTotalQueryBound_query_bind_iff.mp h
    rw [unroute_query_bind]
    exact isTotalQueryBound_query_bind_iff.2 ⟨h0, fun u => ih u (hk u)⟩

end VoleMole.ROM
