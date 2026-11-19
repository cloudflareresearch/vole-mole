import VoleMole.Assumptions.UnboundLinks
import VoleMole.Privacy.Hybrid

/-!
# Unbound Moussaka: nullifier determinism and single use per context (Corollary U2)

`lean/docs/security/moussaka-unbound.md` §5.1. Items 1 and 2 of Corollary U2 hold "on the good
event of Theorem U1": in the OMUF-U game of `ROM/MoussakaUnboundOMUF.lean`, with the reductions'
view `extAll` (the game and the straight-line extraction of every proof), off the events that
Theorem U1 charges (an accepted proof not extracted, a collision of `Com ∪ UCom`, a forgery).

* **`U2`** (an event of the view): for every accepted unbound redemption `(S, nf, ctx_iss,
  ctx_red)`,
  1. *determinism*: its proof is extracted, and every extracted input `(nf_key, ctx_iss', r)` is the
     input extracted from an accepted **unbound** issuance query `(t, ctx_iss)`: `UCom(input) = t`,
     `ctx_iss' = ctx_iss`, and `nf = Derive(nf_key, ctx_red)`. So the nullifier is a function of a
     signed `t` and `ctx_red`;
  2. *single use per context*: two accepted redemptions in one `ctx_red` whose extracted inputs
     commit to the same `t` have the same record key `(ctx_iss, ctx_red, nf)`. A Moderator that
     records the key and rejects repeats (across every Anchor Set) accepts at most one redemption
     per signed `t` and `ctx_red`.
* `notU2_imp` (per table): off `U2`, an accepted proof is not extracted, or `B₁` finds a
  collision, or `B₂` a forgery; the core of `win_imp`, without the counting step.
* **`corU2_le`**, **`corU2_le_sim`**, **`corU2_le_num_sim`**, **`corU2_le_num_ompr_sim`**:
  `Pr[¬U2]` has the bounds of Theorem U1 (`omufU_le`, `omufU_le_sim`, `omufU_le_num_sim`,
  `omufU_le_num_ompr_sim`), term for term.

Item 3 (honest uniqueness): **`honest_nf_distinct`**: `U` honest keys give pairwise distinct
nullifiers in a context `c` except with probability `≤ U²·2⁻¹⁹³ + Adv^prf_U`, `Adv^prf_U` the
PRF advantage (`prfUAdv`, a hypothesis on Keccak-p[800]) of the explicit collision test. The
paper's seed-collision term `U²·2⁻²⁵⁷` is not needed when the keys are uniform (the spec's model
of the seed expansion, as in `Privacy/MoussakaUnbound.lean`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC.OMUFU

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ROM
  VoleMole.ROM.IC VoleMole.ROM.IC.OMUF

attribute [local irreducible] Spec.Moussaka.com Spec.MoussakaUnbound.ucom
  Spec.MoussakaUnbound.derive

variable {K qR : ℕ}

/-! ## The event -/

section Event

variable (lr : Bool) (pk : Fin K → UovPk)

/-- **Corollary U2, items 1 and 2, as an event of the reductions' view.** -/
def U2 (E : CTable) (v : View K) : Prop :=
  (∀ (j : ℕ) (rq : RedQ K), v.1.2[j]? = some (rq, true) →
    ∃ r, v.2.2.2[j]? = some r ∧ (OpUR E lr pk r).Nonempty ∧
      ∀ y ∈ OpUR E lr pk r, y ∈ SUI lr E v ∧
        (∃ (i : ℕ) (q : IssQ K), v.1.1[i]? = some (.inr q, true) ∧ ucomO y = toL q.t ∧
          y.2.1 = toL q.ctx) ∧
        y.2.1 = toL rq.ci ∧ Spec.MoussakaUnbound.derive y.1 (toL rq.cr) = toL rq.nf) ∧
  (∀ (j j' : ℕ) (rq rq' : RedQ K) (r r' : OutR K) (y y' : UOpening),
    v.1.2[j]? = some (rq, true) → v.1.2[j']? = some (rq', true) →
    v.2.2.2[j]? = some r → v.2.2.2[j']? = some r' → y ∈ OpUR E lr pk r → y' ∈ OpUR E lr pk r' →
    ucomO y = ucomO y' → toL rq.cr = toL rq'.cr →
    toL rq.ci = toL rq'.ci ∧ toL rq.nf = toL rq'.nf)

end Event

/-! ## The per-table core -/

section Core

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ) (A : Adversary K qR)

/-- **The per-table core of Corollary U2**: off `U2`, some accepted proof (of one of the three
families) is not extracted, or `B₁` finds a collision of `Com ∪ UCom`, or `B₂` a forgery. -/
theorem notU2_imp (g : Table) (E : CTable)
    (hn : ¬U2 lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E))) :
    (∃ j ∈ Finset.range qI, BadBI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E))) ∨
    (∃ j ∈ Finset.range qI, BadUI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E))) ∨
    (∃ j ∈ Finset.range qR, BadUR E lr pk (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E))) ∨
    Coll lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E)) ∨
    Forge lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (extAll lr pk sk qI A E)) := by
  classical
  obtain ⟨hlI, -, hlR, -⟩ := game_eval g E lr pk sk A qI
  rw [extAll_eval] at hn ⊢
  set o := evalWithAnswerFn (QueryImpl.ofFn (join g E)) (game lr pk sk qI A) with ho
  set ob := (List.range qI).map (fun j =>
    evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E))
    with hob
  set ou := (List.range qI).map (fun j =>
    evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E))
    with hou
  set orr := (List.range qR).map (fun j =>
    evalWithAnswerFn (QueryImpl.ofFn g) (gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E))
    with horr
  by_contra hno
  simp only [BadBI, BadUI, BadUR, not_or, not_exists, not_and, Finset.mem_range, not_not] at hno
  obtain ⟨hB, hU, hR, hC, hF⟩ := hno
  -- no collision: extracted inputs are determined by their commitment
  have hinj : ∀ x ∈ SX lr pk E (o, ob, ou, orr), ∀ x' ∈ SX lr pk E (o, ob, ou, orr),
      comX x = comX x' → x = x' := fun x hx x' hx' he => by
    by_contra hne
    exact hC ⟨x, hx, x', hx', hne, he⟩
  -- the redemption outputs of the view
  have horr_get : ∀ j r, orr[j]? = some r → j < qR ∧
      r = evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E) := fun j r h => by
    simp only [horr, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨hj, ha⟩ := List.getElem?_eq_some_iff.1 ha
    rw [List.getElem_range] at ha
    rw [List.length_range] at hj
    exact ⟨hj, by rw [ha]⟩
  -- every extracted redemption input is an extracted unbound issuance input
  have hsui : ∀ y ∈ SUR lr pk E (o, ob, ou, orr), y ∈ SUI lr E (o, ob, ou, orr) ∧
      ∃ (i : ℕ) (q : IssQ K), o.1[i]? = some (.inr q, true) ∧ ucomO y = toL q.t ∧
        y.2.1 = toL q.ctx := fun y hy => by
    have hyx : (Sum.inr y : XOp) ∈ SX lr pk E (o, ob, ou, orr) :=
      Or.inr ⟨y, Or.inr hy, rfl⟩
    have hsig : ucomO y ∈ sigT o := by
      by_contra hs
      exact hF ⟨y, hy, hs⟩
    rcases mem_sigT hsig with hu | hb
    · obtain ⟨⟨t, c⟩, hq, ht⟩ := List.mem_map.1 hu
      simp only [uissL, List.mem_map, List.mem_filter, Bool.and_eq_true] at hq
      obtain ⟨⟨p, b⟩, ⟨hp, hpb, hpr⟩, hpe⟩ := hq
      rcases p with p | p
      · simp at hpr
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
      have hil : i < qI := by rw [← hlI]; exact (List.getElem?_eq_some_iff.1 hi).1
      have hi' : o.1[i]? = some (.inr p, true) := by rw [hi]; simpa using hpb
      obtain ⟨hacc, hst⟩ := accepted_UI g E lr pk sk qI A hi'
      obtain ⟨y', hy', hyc, hyt⟩ := opUI_of_ext E lr (hU i hil hacc)
      have hy'S : y' ∈ SUI lr E (o, ob, ou, orr) := ⟨i, p, _, hi', by simp [ou, hil], hy'⟩
      simp only [Prod.mk.injEq] at hpe
      have hct : ucomO y' = ucomO y := by
        rw [hyc, hst, ← ht, ← hpe.1]; rfl
      have hyy : (Sum.inr y' : XOp) = Sum.inr y :=
        hinj _ (Or.inr ⟨y', Or.inl hy'S, rfl⟩) _ hyx (by simp only [comX, Sum.elim_inr]; exact hct)
      cases hyy
      refine ⟨hy'S, i, p, hi', ?_, ?_⟩
      · rw [hyc, hst]
      · rw [hyt, hst]
    · exfalso
      simp only [bissL, List.mem_map, List.mem_filter, Bool.and_eq_true] at hb
      obtain ⟨⟨p, b⟩, ⟨hp, hpb, hpl⟩, hpe⟩ := hb
      rcases p with p | p
      swap
      · simp at hpl
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
      have hil : i < qI := by rw [← hlI]; exact (List.getElem?_eq_some_iff.1 hi).1
      have hi' : o.1[i]? = some (.inl p, true) := by rw [hi]; simpa using hpb
      obtain ⟨hacc, hst⟩ := accepted_BI g E lr pk sk qI A hi'
      obtain ⟨x, hx, hxc, -⟩ := opBI_of_ext E lr (hB i hil hacc)
      have hxS : (Sum.inl x : XOp) ∈ SX lr pk E (o, ob, ou, orr) :=
        Or.inl ⟨x, ⟨i, p, _, hi', by simp [ob, hil], hx⟩, rfl⟩
      have := hinj _ hxS _ hyx (by
        simp only [comX, Sum.elim_inl, Sum.elim_inr]
        rw [hxc, hst, ← hpe]; rfl)
      cases this
  refine hn ⟨fun j rq hj => ?_, fun j j' rq rq' r r' y y' hj hj' hr hr' hy hy' hc hcr => ?_⟩
  · have hjl : j < qR := by rw [← hlR]; exact (List.getElem?_eq_some_iff.1 hj).1
    obtain ⟨hacc, hst⟩ := accepted_UR g E lr pk sk qI A hj
    refine ⟨evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E), by simp [orr, hjl], ?_,
      fun y hy => ?_⟩
    · obtain ⟨y, hy, -⟩ := opUR_of_ext E lr pk (hR j hjl hacc)
      exact ⟨y, hy⟩
    · have hyS : y ∈ SUR lr pk E (o, ob, ou, orr) := ⟨j, rq, _, hj, by simp [orr, hjl], hy⟩
      obtain ⟨h1, h2⟩ := hsui y hyS
      refine ⟨h1, h2, ?_, ?_⟩
      · rw [hy.2.1, hst]
      · have := hy.2.2.1
        rw [hst] at this
        exact this
  · obtain ⟨-, rfl⟩ := horr_get j r hr
    obtain ⟨-, rfl⟩ := horr_get j' r' hr'
    obtain ⟨-, hst⟩ := accepted_UR g E lr pk sk qI A hj
    obtain ⟨-, hst'⟩ := accepted_UR g E lr pk sk qI A hj'
    have hyS : (Sum.inr y : XOp) ∈ SX lr pk E (o, ob, ou, orr) :=
      Or.inr ⟨y, Or.inr ⟨j, rq, _, hj, hr, hy⟩, rfl⟩
    have hyS' : (Sum.inr y' : XOp) ∈ SX lr pk E (o, ob, ou, orr) :=
      Or.inr ⟨y', Or.inr ⟨j', rq', _, hj', hr', hy'⟩, rfl⟩
    have hyy := hinj _ hyS _ hyS' (by simp only [comX, Sum.elim_inr]; exact hc)
    cases hyy
    have e1 := hy.2.1
    have e2 := hy'.2.1
    have n1 := hy.2.2.1
    have n2 := hy'.2.2.1
    rw [hst] at e1 n1
    rw [hst'] at e2 n2
    refine ⟨e1.symm.trans e2, n1.symm.trans ?_⟩
    simp only at hcr n1 n2 ⊢
    rw [hcr]
    exact n2

end Core

/-! ## The bounds of Theorem U1 -/

section Bounds

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ) (A : Adversary K qR)

/-- **Corollary U2 (items 1 and 2), the reduction**: `Pr[¬U2]` is at most the terms of `omufU_le`. -/
theorem corU2_le :
    Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        ¬U2 lr pk E v] ≤
      ∑ j ∈ Finset.range qI, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E)).run' ∅}[BadBI E lr r] +
      ∑ j ∈ Finset.range qI, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E)).run' ∅}[BadUI E lr r] +
      ∑ j ∈ Finset.range qR, Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
        (gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E)).run' ∅}[BadUR E lr pk r] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Forge lr pk E v] :=
  prEvent_bind_le_sum5_of_table ($ᵗ CTable) (fun E => extAll lr pk sk qI A E)
    (fun E v => ¬U2 lr pk E v) (Finset.range qI) (Finset.range qI) (Finset.range qR)
    _ _ _ _ _ _ _ _ _ fun E g hn => notU2_imp lr pk sk qI A g E hn

/-- **Corollary U2, with simultaneous extraction events** (`omufU_le_sim`'s terms). -/
theorem corU2_le_sim :
    Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        ¬U2 lr pk E v] ≤
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        SimBI lr E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        SimU lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Forge lr pk E v] := by
  have h := prEvent_bind_le_sum4_of_table ($ᵗ CTable) (fun E => extAll lr pk sk qI A E)
    (fun E v => ¬U2 lr pk E v) {0} {0} (fun _ E => extAll lr pk sk qI A E)
    (fun E v => SimBI lr E v) (fun _ E => extAll lr pk sk qI A E) (fun E v => SimU lr pk E v)
    (fun E => extAll lr pk sk qI A E) (fun E v => Coll lr pk E v) (fun E v => Forge lr pk E v)
    fun E g hn => by
      rcases notU2_imp lr pk sk qI A g E hn with ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | hC | hF
      · refine Or.inl ⟨0, Finset.mem_singleton_self 0, ?_⟩
        rw [extAll_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inl ?_⟩)
        rw [extAll_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inr ?_⟩)
        rw [extAll_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · exact Or.inr (Or.inr (Or.inl hC))
      · exact Or.inr (Or.inr (Or.inr hF))
  simpa only [Finset.sum_singleton] using h

variable {lr pk sk qI A} {q : Kind → ℕ} {qE n : ℕ}

/-- **Corollary U2 (items 1 and 2) with simultaneous extraction**: for an adversary within its
budget and honest Anchors with distinct 32-byte key digests,

    Pr[¬U2] ≤ εI^sim(q', q'_E, qI) + εU^sim(q', q'_E, n', qI, qR) + AdvBind(B₁) + AdvCTUF(B₂),

the bound of `omufU_le_num_sim`. -/
theorem corU2_le_num_sim (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest) :
    Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        ¬U2 lr pk E v] ≤
      epsIsim (gameK q qI qR) (gameE lr qE qI qR) qI +
      epsUsim (gameK q qI qR) (gameE lr qE qI qR) (gameH n qI qR) qI qR +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Coll lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle (extAll lr pk sk qI A E)).run' ∅}[
        Forge lr pk E v] :=
  (corU2_le_sim lr pk sk qI A).trans (add_le_add (add_le_add (add_le_add
    (prEvent_simBI_le hA) (prEvent_simU_le hA hdig hdinj)) le_rfl) le_rfl)

end Bounds

end VoleMole.ROM.IC.OMUFU

namespace VoleMole.Assumptions.UOV.Links

open VoleMole.ROM VoleMole.ROM.IC VoleMole.Prob VoleMole.Verifier VoleMole.ZK.Sim
open VoleMole.ROM.IC.OMUF VoleMole.ROM.IC.OMUFU CTUFOpen

variable {K qR : ℕ}

section Unbound

variable (lr : Bool) (pk : Fin K → UovPk) (sk : Fin K → Spec.Signer) (qI : ℕ)
  (A : OMUFU.Adversary K qR)

/-- **Per table, Corollary U2 with CT-UF^open**: off `U2`, an accepted proof is not extracted, or
`B₁` finds a collision, or `B₂` wins CT-UF^open over `Com ∪ UCom`. -/
theorem notU2_imp_open (g : Table) (E : CTable)
    (hn : ¬U2 lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (OMUFU.extAll lr pk sk qI A E))) :
    (∃ j ∈ Finset.range qI, BadBI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E))) ∨
    (∃ j ∈ Finset.range qI, BadUI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E))) ∨
    (∃ j ∈ Finset.range qR, BadUR E lr pk (evalWithAnswerFn (QueryImpl.ofFn g)
        (gameA CrtGen.tables (stUR lr pk) (PUR lr pk sk qI A j) E))) ∨
    OMUFU.Coll lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (OMUFU.extAll lr pk sk qI A E)) ∨
    CTOpenWin (verK pk) comX WFX
      (ctufOutU lr pk E (evalWithAnswerFn (QueryImpl.ofFn g) (OMUFU.extAll lr pk sk qI A E))) := by
  by_cases hB : ∃ j ∈ Finset.range qI, BadBI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stI lr) (PBI lr pk sk qI A j) E))
  · exact Or.inl hB
  by_cases hU : ∃ j ∈ Finset.range qI, BadUI E lr (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameA CrtGen.tables (stUI lr) (PUI lr pk sk qI A j) E))
  · exact Or.inr (Or.inl hU)
  push Not at hB hU
  rcases OMUFU.notU2_imp lr pk sk qI A g E hn with h | h | h | h | h
  · exact absurd h (by push Not; exact hB)
  · exact absurd h (by push Not; exact hU)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (ctOpenWin_of_forgeU lr pk sk qI A g E hB hU h))))

/-- **Corollary U2 with `B₂`'s standalone CT-UF^open advantage, simultaneous extraction events.** -/
theorem corU2_le_open_sim :
    Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[¬U2 lr pk E v] ≤
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[SimBI lr E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[SimU lr pk E v] +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[OMUFU.Coll lr pk E v] +
      advCTUFOpenAt (verK pk) comX WFX (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk)
        (ctufForgerU lr pk qI A) := by
  rw [advCTUFOpenAt_ctufForgerU]
  have h := prEvent_bind_le_sum4_of_table ($ᵗ CTable) (fun E => OMUFU.extAll lr pk sk qI A E)
    (fun E v => ¬U2 lr pk E v) {0} {0} (fun _ E => OMUFU.extAll lr pk sk qI A E)
    (fun E v => SimBI lr E v) (fun _ E => OMUFU.extAll lr pk sk qI A E) (fun E v => SimU lr pk E v)
    (fun E => OMUFU.extAll lr pk sk qI A E) (fun E v => OMUFU.Coll lr pk E v)
    (fun E v => CTOpenWin (verK pk) comX WFX (ctufOutU lr pk E v)) fun E g hn => by
      rcases notU2_imp_open lr pk sk qI A g E hn with
        ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | ⟨j, hj, hb⟩ | hC | hF
      · refine Or.inl ⟨0, Finset.mem_singleton_self 0, ?_⟩
        rw [OMUFU.extAll_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inl ?_⟩)
        rw [OMUFU.extAll_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · refine Or.inr (Or.inl ⟨0, Finset.mem_singleton_self 0, Or.inr ?_⟩)
        rw [OMUFU.extAll_eval]
        exact ⟨_, List.mem_map_of_mem (List.mem_range.2 (Finset.mem_range.1 hj)), hb⟩
      · exact Or.inr (Or.inr (Or.inl hC))
      · exact Or.inr (Or.inr (Or.inr hF))
  simpa only [Finset.sum_singleton] using h

variable {lr pk sk qI A} {q : Kind → ℕ} {qE n : ℕ}
  {DR : Type} [DecidableEq DR] {AR : DR → Type} [∀ d, SampleableType (AR d)]
  {Xc T S PK SK : Type} [DecidableEq Xc] [DecidableEq T] [Inhabited T] [SampleableType T]

/-- **Corollary U2 (items 1 and 2) down to OMPR with simultaneous extraction**: under the
modelling hypothesis `hmodel` of `omufU_le_num_ompr_sim`,

    Pr[¬U2] ≤ εI^sim + εU^sim + AdvBind(B₁)
              + Σ_j (Adv^{ompr}_{key j}(B_j; q_f + 2q_S + 1, q_S) + (q_f + 2q_S + 1)·failPr_{key j}). -/
theorem corU2_le_num_ompr_sim (tr : Trapdoor PK SK T S) (ks : Fin K → PK × SK) (qf qS : ℕ)
    (hA : A.Budget q qE n) (hdig : ∀ k, (pk k).digest.size = 32)
    (hdinj : Function.Injective fun k => (pk k).digest)
    (F : ProbComp (OracleComp (specCI AR K Xc T S) (CTOut K S Xc)))
    (hF : ∀ f ∈ support F, CIBudget qf qS f)
    (hmodel : advCTUFOpenAt (verK pk) comX WFX
        (signers (fun (sk : Spec.Signer) => sk.derivePreimage) sk) (ctufForgerU lr pk qI A) ≤
      advCTUFIdealAt (fun k => tr.IsPre (ks k).1) (signers tr.D fun k => (ks k).2) F) :
    Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[¬U2 lr pk E v] ≤
      epsIsim (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) qI +
      epsUsim (OMUFU.gameK q qI qR) (OMUFU.gameE lr qE qI qR) (OMUFU.gameH n qI qR) qI qR +
      Pr{let E ← $ᵗ CTable; let v ← (simulateQ randomOracle
        (OMUFU.extAll lr pk sk qI A E)).run' ∅}[OMUFU.Coll lr pk E v] +
      ∑ j : Fin K, (advOMPR (tr.atKey (ks j)) (qf + 2 * qS + 1) qS
          (ompRed qS fun _ => guessF j (signers tr.D fun k => (ks k).2) <$> F) +
        ((qf + 2 * qS + 1 : ℕ) : ℝ≥0∞) * preFailPr (tr.atKey (ks j))) :=
  (corU2_le_open_sim lr pk sk qI A).trans (add_le_add (add_le_add (add_le_add
    (prEvent_simBI_le hA) (prEvent_simU_le hA hdig hdinj)) le_rfl)
    (hmodel.trans (advCTUFIdealAt_le_ompr tr qf qS ks F hF)))

end Unbound

end VoleMole.Assumptions.UOV.Links

/-! ## Item 3: honest uniqueness -/

namespace VoleMole.MoussakaUnbound.CorU2

open Finset VoleMole.Privacy VoleMole.Spec VoleMole.Spec.MoussakaUnbound
open VoleMole.Spec.Moussaka (ctxBytes nfBytes)

attribute [local irreducible] derive

variable (U : ℕ)

/-- The real `U`-key PRF experiment: the table `(i, c) ↦ Derive(k_i, c)`. -/
def prfUReal (k : Fin U → Coins nfKeyBytes) : Fin U → Coins ctxBytes → Bytes :=
  fun i c => derive (List.ofFn (k i)) (List.ofFn c)

/-- The ideal experiment: a uniform table. -/
def prfUIdeal (F : Fin U × Coins ctxBytes → Coins nfBytes) : Fin U → Coins ctxBytes → Bytes :=
  fun i c => List.ofFn (F (i, c))

/-- **The `U`-key PRF advantage** of `D` (`Adv^prf_U`, `security/moussaka-unbound.md` §3.2,
without the commitments). -/
noncomputable def prfUAdv (D : (Fin U → Coins ctxBytes → Bytes) → Prop) : ℝ :=
  |pr (Fin U → Coins nfKeyBytes) (fun k => D (prfUReal U k)) -
    pr (Fin U × Coins ctxBytes → Coins nfBytes) (fun F => D (prfUIdeal U F))|

/-- **The collision test** in a context `c`: two tokens with one nullifier. -/
def collD (c : Coins ctxBytes) (O : Fin U → Coins ctxBytes → Bytes) : Prop :=
  ∃ i j, i ≠ j ∧ O i c = O j c

theorem card_coins_nf : Fintype.card (Coins nfBytes) = 2 ^ 192 := by
  rw [Fintype.card_fun, Fintype.card_fin, Prob.card_uint8]; norm_num

/-- Two distinct entries of a uniform table are equal with probability `2⁻¹⁹²`. -/
theorem pr_tab_eq_le {i j : Fin U} (hij : i ≠ j) (c : Coins ctxBytes) :
    pr (Fin U × Coins ctxBytes → Coins nfBytes) (fun F => F (i, c) = F (j, c)) ≤ 1 / 2 ^ 192 := by
  let pts : Bool → Fin U × Coins ctxBytes := fun b => cond b (i, c) (j, c)
  have hinj : Function.Injective pts := by
    intro a b h
    cases a <;> cases b <;> simp only [pts, Bool.cond_true, Bool.cond_false, Prod.mk.injEq] at h <;>
      first | rfl | exact absurd h.1 hij | exact absurd h.1.symm hij
  have h1 := close_restrict (R := Coins nfBytes) hinj (fun u => u true = u false)
  have e : pr (Fin U × Coins ctxBytes → Coins nfBytes) (fun F => F (i, c) = F (j, c)) =
      pr (Bool → Coins nfBytes) (fun u => u true = u false) :=
    sub_eq_zero.1 (abs_nonpos_iff.1 h1)
  rw [e, ← pr_equiv (Equiv.boolArrowEquivProd (Coins nfBytes)).symm]
  have h2 := pr_mem_indep_le (α := Coins nfBytes) (β := Coins nfBytes) id Function.injective_id
    (fun v => {v}) (q := 1) (fun _ => by simp)
  rw [card_coins_nf] at h2
  refine le_of_eq_of_le (pr_congr fun p => ?_) (h2.trans (by norm_num))
  simp [Equiv.boolArrowEquivProd, eq_comm]

/-- At most `U²/2` ordered pairs `i < j`. -/
theorem card_lt_pairs : 2 * (#{p : Fin U × Fin U | p.1 < p.2} : ℝ) ≤ (U : ℝ) ^ 2 := by
  have h1 : #{p : Fin U × Fin U | p.1 < p.2} = #{p : Fin U × Fin U | p.2 < p.1} :=
    Finset.card_equiv (Equiv.prodComm _ _) (by simp)
  have h2 : #{p : Fin U × Fin U | p.1 < p.2} + #{p : Fin U × Fin U | p.2 < p.1} ≤ U * U := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun p _ h h' => lt_asymm h h')]
    exact (Finset.card_le_univ _).trans (by simp)
  have : 2 * #{p : Fin U × Fin U | p.1 < p.2} ≤ U * U := by omega
  have h3 : (2 * #{p : Fin U × Fin U | p.1 < p.2} : ℝ) ≤ ((U * U : ℕ) : ℝ) := by exact_mod_cast this
  rw [sq]; push_cast at h3; exact h3

/-- **Corollary U2, item 3 (honest uniqueness)**: `U` honest uniform keys give pairwise distinct
nullifiers in a context `c`, except with probability at most `U²·2⁻¹⁹³ + Adv^prf_U(collD c)`. -/
theorem honest_nf_distinct (c : Coins ctxBytes) :
    pr (Fin U → Coins nfKeyBytes) (fun k => ∃ i j, i ≠ j ∧
        derive (List.ofFn (k i)) (List.ofFn c) = derive (List.ofFn (k j)) (List.ofFn c)) ≤
      (U : ℝ) ^ 2 / 2 ^ 193 + prfUAdv U (collD U c) := by
  classical
  have hreal : pr (Fin U → Coins nfKeyBytes) (fun k => ∃ i j, i ≠ j ∧
      derive (List.ofFn (k i)) (List.ofFn c) = derive (List.ofFn (k j)) (List.ofFn c)) =
      pr (Fin U → Coins nfKeyBytes) (fun k => collD U c (prfUReal U k)) := rfl
  have hadv : pr (Fin U → Coins nfKeyBytes) (fun k => collD U c (prfUReal U k)) -
      pr (Fin U × Coins ctxBytes → Coins nfBytes) (fun F => collD U c (prfUIdeal U F)) ≤
      prfUAdv U (collD U c) := le_abs_self _
  have hid : pr (Fin U × Coins ctxBytes → Coins nfBytes) (fun F => collD U c (prfUIdeal U F)) ≤
      (U : ℝ) ^ 2 / 2 ^ 193 := by
    have hmono : ∀ F : Fin U × Coins ctxBytes → Coins nfBytes, collD U c (prfUIdeal U F) →
        ∃ p : Fin U × Fin U, p.1 < p.2 ∧ F (p.1, c) = F (p.2, c) := by
      rintro F ⟨i, j, hij, he⟩
      have he' : F (i, c) = F (j, c) := List.ofFn_injective he
      rcases lt_or_gt_of_ne hij with h | h
      · exact ⟨(i, j), h, he'⟩
      · exact ⟨(j, i), h, he'.symm⟩
    refine (pr_mono hmono).trans ((pr_exists_le_sum _).trans ?_)
    · calc ∑ p : Fin U × Fin U, pr (Fin U × Coins ctxBytes → Coins nfBytes)
            (fun F => p.1 < p.2 ∧ F (p.1, c) = F (p.2, c))
          ≤ ∑ p : Fin U × Fin U, (if p.1 < p.2 then (1 : ℝ) / 2 ^ 192 else 0) := by
            refine Finset.sum_le_sum fun p _ => ?_
            split_ifs with hp
            · exact (pr_mono fun F hF => hF.2).trans (pr_tab_eq_le U (ne_of_lt hp) c)
            · refine (pr_mono (Q := fun _ => False) fun F hF => hp hF.1).trans ?_
              rw [pr_const]; simp
        _ = (#{p : Fin U × Fin U | p.1 < p.2} : ℝ) * (1 / 2 ^ 192) := by
            rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        _ ≤ (U : ℝ) ^ 2 / 2 ^ 193 := by
            have := card_lt_pairs U
            rw [show (2 : ℝ) ^ 193 = 2 * 2 ^ 192 by norm_num]
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
  rw [hreal]
  linarith

end VoleMole.MoussakaUnbound.CorU2
