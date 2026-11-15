import VoleMole.ZK.MainSharedN
import VoleMole.ZK.HopsMainICLin

/-!
# The joint hop on `main` for `n` proofs, linear in `n` (`lean/docs/zk.md` §4.2)

`main_sharedAll_leN` (`ZK/MainSharedN.lean`) replaces `n` `main`-layout proofs on all-shared
tables by simulated ones at the cost `(2ⁿ − 1)·(εS + Δ23N) + (2ⁿ − 1)·Pr_sim[bstarN]`: each hop
costs `εS + Δ23N` and the bad event `bstarN` in the next hybrid, and that bad event is moved to the
all-simulated hybrid across the later hops, which may double it each time (`chain_le`).

Here the one-proof theorem is used in its identical-until-bad form (`slot_zk_main_iub`,
`ZK/HopsMainICLin.lean`): for an event `Φ` of the view that **contains `bstarN`**, the hop costs
`εS + Δ23N` and no bad term (`hopN_iub`), because the prediction of the replaced proof on its
simulated side implies `bstarN` (`ctx_bad`). Applying it to `F ∨ bstarN` and to `bstarN` alone,
whose read sets are those of `F` and of `bstarN` together (`rdN_or`), gives

    |Pr[all real; F] − Pr[all simulated; F]|
        ≤ 2n·(εS(2q₃ + n, 2q_E + 2n·4607) + Δ23N(d, n)) + Pr[all simulated; bstarN]
                                                                     (main_sharedAll_leLin)

`Pr[F] = Pr[F ∨ b] − Pr[b ∧ ¬F]`: the first moves by `n·ε` across the `n` hops, the second lies in
`[0, Pr[b]]` on both sides and `Pr[b]` moves by `n·ε`. The budgets `2q₃`, `2q_E` count the reads of
`F` and of `bstarN` (`R5`'s own reads) separately.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC
open VoleMole.Privacy.MainChain

attribute [local instance] decEqW128
attribute [local irreducible] simulate realRO progRO realKeys5 realKeysE progKeys5 progKeysE

/-! ## Read sets of a disjunction -/

section Rd

variable {S : Type} {n : ℕ} {p₀ : Params}

/-- **A larger budget.** -/
theorem rdN_mono {X : Sort*} {f : NView S n p₀ → X} {R5 : NView S n p₀ → Finset (Bytes 37)}
    {q3 qE q3' qE' : ℕ} (h : RdN f R5 q3 qE) (h3 : q3 ≤ q3') (hE : qE ≤ qE') :
    RdN f R5 q3' qE' := by
  obtain ⟨h5, ⟨QE, hQEc, hQE⟩, ⟨Q3, hQ3c, hQ3⟩⟩ := h
  exact ⟨h5, ⟨QE, fun v => (hQEc v).trans hE, hQE⟩, ⟨Q3, fun v => (hQ3c v).trans h3, hQ3⟩⟩

/-- **The read sets of a disjunction** are the unions. -/
theorem rdN_or {P Q : NView S n p₀ → Prop} {R5 : NView S n p₀ → Finset (Bytes 37)}
    {q3 qE q3' qE' : ℕ} (hP : RdN P R5 q3 qE) (hQ : RdN Q R5 q3' qE') :
    RdN (fun v => P v ∨ Q v) R5 (q3 + q3') (qE + qE') := by
  classical
  obtain ⟨hP5, ⟨PE, hPEc, hPE⟩, ⟨P3, hP3c, hP3⟩⟩ := hP
  obtain ⟨hQ5, ⟨QE, hQEc, hQE⟩, ⟨Q3, hQ3c, hQ3⟩⟩ := hQ
  refine ⟨fun v G5 h => ?_, ⟨fun v => PE v ∪ QE v, fun v => (card_union_le _ _).trans
    (add_le_add (hPEc v) (hQEc v)), fun v E h => ?_⟩, ⟨fun v => P3 v ∪ Q3 v,
    fun v => (card_union_le _ _).trans (add_le_add (hP3c v) (hQ3c v)), fun v T' h => ?_⟩⟩
  · show (P _ ∨ Q _) = (P v ∨ Q v)
    rw [hP5 v G5 h, hQ5 v G5 h]
  · show (P _ ∨ Q _) = (P v ∨ Q v)
    rw [hPE v E fun k hk => h k (mem_union_left _ hk),
      hQE v E fun k hk => h k (mem_union_right _ hk)]
  · show (P _ ∨ Q _) = (P v ∨ Q v)
    rw [hP3 v T' fun k hk => h k (mem_union_left _ hk),
      hQ3 v T' fun k hk => h k (mem_union_right _ hk)]

end Rd

/-! ## One proof in a context, identical until bad -/

section Tools

variable (Hb : Hashes) {V : Type}

set_option maxRecDepth 8000 in
/-- **`ctx_hopN`, identical until bad**: if the event holds on the simulated side wherever the
prediction does (`hB`), replacing the proof costs `εS` only. -/
theorem ctx_hopN_iub {p : Params} (hm : MainP p) (hp : SmallParams p) (hHb : HashesWF Hb) (y : SW)
    (hy : ValidZK CrtGen.tables p y) (getU : V → USh) (withU : V → USh → V)
    (get3 : V → Tab3) (set3 : V → Tab3 → V) (Ψ : V → Prop) (R5 : V → Finset (Bytes 37))
    (C : Out → VP p → USh → V)
    (T5 : Out → VP p → USh → Finset (Bytes 37)) (TE : Out → VP p → USh → Finset Blk)
    (T3 : Finset (Bytes 16)) {tE : ℕ}
    (hCu : ∀ o V u, getU (C o V u) = u)
    (hC5 : ∀ o V u (G5 : Tab5F), (∀ k ∈ T5 o V u, u.1 k = G5 k) →
      C o V (G5, u.2) = withU (C o V u) (G5, u.2))
    (hCE : ∀ o V u (E : Cipher), (∀ k ∈ TE o V u, u.2 k = E k) →
      C o V (u.1, E) = withU (C o V u) (u.1, E))
    (hTE : ∀ o V u, (TE o V u).card ≤ tE)
    (hC3 : ∀ o (G3 G3' : Tab3) (G2 : Tab2G p) u, (∀ k ∈ T3, G3 k = G3' k) →
      C o (G3', G2) u = set3 (C o (G3, G2) u) G3')
    (hg3 : ∀ o (G3 : Tab3) (G2 : Tab2G p) u, get3 (C o (G3, G2) u) = G3)
    {q3 qE : ℕ}
    (hΨ5 : ∀ v (G5 : Tab5F), (∀ k ∈ R5 v, (getU v).1 k = G5 k) →
      Ψ (withU v (G5, (getU v).2)) = Ψ v)
    (hΨE : ∃ Q : V → Finset Blk, (∀ v, (Q v).card ≤ qE) ∧
      ∀ v (E : Cipher), (∀ k ∈ Q v, (getU v).2 k = E k) → Ψ (withU v ((getU v).1, E)) = Ψ v)
    (hΨ3 : ∃ Q : V → Finset (Bytes 16), (∀ v, (Q v).card ≤ q3) ∧
      ∀ v (G3 : Tab3), (∀ k ∈ Q v, get3 v k = G3 k) → Ψ (set3 v G3) = Ψ v)
    (hB : ∀ z : USh × KS p, mainPredIC Hb (withP y.1 p) hm
        (fun o G3 G2 G5 E => R5 (C o (G3, G2) (G5, E)) ∪ T5 o (G3, G2) (G5, E)) (wPre y.2)
        ((z.2.1.2, (z.2.2.1, z.2.2.2, z.1.1)), z.1.2) →
      Ψ (C (simulate p z.2.1.2) (z.2.2.1, (progRO p Hb (withP y.1 p) z.2.1.2
        (shOf z.2.2.2 z.1)).1) z.1)) :
    |pr (USh × KS p) (fun z => Ψ (C (realRO p Hb (withP y.1 p) y.2 z.2.1.1 z.2.2.1
          (shOf z.2.2.2 z.1)) z.2.2 z.1)) -
      pr (USh × KS p) (fun z => Ψ (C (simulate p z.2.1.2)
          (z.2.2.1, (progRO p Hb (withP y.1 p) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1))| ≤
      εS (q3 + T3.card) (qE + tE) := by
  classical
  obtain ⟨cs, hzk⟩ := hy
  obtain ⟨QE, hQEc, hQE⟩ := hΨE
  obtain ⟨Q3, hQ3c, hQ3⟩ := hΨ3
  refine slot_zk_main_iub Hb (withP y.1 p) y.2 hm hzk hHb hp
    (fun o G3 G2 G5 E => Ψ (C o (G3, G2) (G5, E)))
    (fun o G3 G2 G5 E => Q3 (C o (G3, G2) (G5, E)) ∪ T3) ?_
    (q3 := q3 + T3.card) (fun _ _ _ _ _ => (card_union_le _ _).trans (add_le_add (hQ3c _) le_rfl))
    (fun o G3 G2 G5 E => R5 (C o (G3, G2) (G5, E)) ∪ T5 o (G3, G2) (G5, E)) ?_
    (fun o G3 G2 G5 E => QE (C o (G3, G2) (G5, E)) ∪ TE o (G3, G2) (G5, E)) ?_ ?_ hB
  · intro o G3 G3' G2 G5 E h
    show Ψ (C o (G3, G2) (G5, E)) ↔ Ψ (C o (G3', G2) (G5, E))
    rw [hC3 o G3 G3' G2 (G5, E) fun k hk => h k (mem_union_right _ hk),
      hQ3 _ G3' (by rw [hg3]; exact fun k hk => h k (mem_union_left _ hk))]
  · intro o G3 G2 G5 G5' E h
    have e := hC5 o (G3, G2) (G5, E) G5' fun k hk => h k (mem_union_right _ hk)
    have hu := hCu o (G3, G2) (G5, E)
    have := hΨ5 (C o (G3, G2) (G5, E)) G5' (by
      rw [hu]; exact fun k hk => h k (mem_union_left _ hk))
    rw [hu] at this
    show Ψ (C o (G3, G2) (G5, E)) ↔ Ψ (C o (G3, G2) (G5', E))
    rw [e, this]
  · intro o G3 G2 G5 E E' h
    have e := hCE o (G3, G2) (G5, E) E' fun k hk => h k (mem_union_right _ hk)
    have hu := hCu o (G3, G2) (G5, E)
    have := hQE (C o (G3, G2) (G5, E)) E' (by
      rw [hu]; exact fun k hk => h k (mem_union_left _ hk))
    rw [hu] at this
    show Ψ (C o (G3, G2) (G5, E)) ↔ Ψ (C o (G3, G2) (G5, E'))
    rw [e, this]
  · intro o G3 G2 G5 E
    exact (card_union_le _ _).trans (add_le_add (hQEc _) (hTE _ _ _))

end Tools

/-! ## The hop, identical until bad -/

section HopMain

variable (Hb : Hashes) (p₀ : Params) {n : ℕ} (ns : Fin n → ℕ) {S : Type} (G : NGame S n)

set_option maxRecDepth 8000 in
/-- **Hop `j` on one fiber, identical until bad**: for an event `Φ` that contains `bstarN`, the
cost is `εS + Δ23N`, without the bad event. -/
theorem hop_fiber_iub (hHb : HashesWF Hb) (hv : NValid G p₀ ns) (j : ℕ) (hj : j < n)
    (x : NTape p₀ ns S) (y : SW) (hy : yJ Hb p₀ ns G j hj x = some y)
    (Φ : NView S n p₀ → Prop) (R5 : NView S n p₀ → Finset (Bytes 37)) {q3 qE : ℕ}
    (hΦ : RdN Φ R5 q3 qE) (hb : ∀ v, bstarN Hb G (fun i => pw p₀ (ns i)) R5 v → Φ v) :
    |pr (USh × KS (pw p₀ (ns ⟨j, hj⟩))) (fun b =>
        Φ (hybVN Hb p₀ ns G j (setJ Hb p₀ ns G j hj x b))) -
      pr (USh × KS (pw p₀ (ns ⟨j, hj⟩))) (fun b =>
        Φ (hybVN Hb p₀ ns G (j + 1) (setJ Hb p₀ ns G j hj x b)))| ≤
      εS (q3 + n) (qE + n * 4607) + Δ23N p₀.qsDegree n := by
  classical
  set pj := pw p₀ (ns ⟨j, hj⟩) with hpj
  set P := preJ Hb p₀ ns G j hj x with hP
  set C := ctxV Hb p₀ ns G j hj x with hC
  have hyv : ValidZK CrtGen.tables pj y := hv.v ⟨j, hj⟩ x.1 _ y hy
  have eR : ∀ b : USh × KS pj, Φ (hybVN Hb p₀ ns G j (setJ Hb p₀ ns G j hj x b)) ↔
      Φ (C (realRO pj Hb (withP y.1 pj) y.2 b.2.1.1 b.2.2.1
        (shOf (p := pj) (LJ Hb p₀ ns G j x b.1 b.2.2.2) b.1)) b.2.2 b.1) := by
    rintro ⟨u, ⟨ρ, c⟩, G3, G2⟩
    rw [hyb_real_eq Hb p₀ ns G j hj x y hy u ρ c G3 G2]
  have eS : ∀ b : USh × KS pj, hybVN Hb p₀ ns G (j + 1) (setJ Hb p₀ ns G j hj x b) =
      C (simulate pj b.2.1.2) (b.2.2.1, (progRO pj Hb (withP y.1 pj) b.2.1.2
        (shOf b.2.2.2 b.1)).1) b.1 := by
    rintro ⟨u, ⟨ρ, c⟩, G3, G2⟩
    exact hyb_sim_eq Hb p₀ ns G j hj x y hy u ρ c G3 G2
  -- the programming-collision term
  set Tl := (univ.filter fun i : Fin n => i.val < j).image (fun i => simTail (x.2.1 i).2)
    with hTl
  have hTl_card : Tl.card ≤ n := card_image_le.trans ((card_filter_le _ _).trans (by simp))
  have hδ : |pr (USh × KS pj) (fun b => Φ (C (realRO pj Hb (withP y.1 pj) y.2 b.2.1.1 b.2.2.1
        (shOf (p := pj) (LJ Hb p₀ ns G j x b.1 b.2.2.2) b.1)) b.2.2 b.1)) -
      pr (USh × KS pj) (fun b => Φ (C (realRO pj Hb (withP y.1 pj) y.2 b.2.1.1 b.2.2.1
        (shOf b.2.2.2 b.1)) b.2.2 b.1))| ≤ Δ23N p₀.qsDegree n := by
    refine (abs_pr_sub_le_of_agree _ _ _ fun b hb => ?_).trans
      (pr_collide_slotN Hb (hv.m _) (hv.sm _) hHb y hyv
        (fun u H => LJ Hb p₀ ns G j x u H) Tl hTl_card fun u H k hk =>
          preRun_tl Hb p₀ ns G hHb j hj.le x.1 x.2.1 x.2.2.1 u x.2.2.2.2 H k hk)
    have e : realRO pj Hb (withP y.1 pj) y.2 b.2.1.1 b.2.2.1
        (shOf (p := pj) (LJ Hb p₀ ns G j x b.1 b.2.2.2) b.1) =
        realRO pj Hb (withP y.1 pj) y.2 b.2.1.1 b.2.2.1 (shOf b.2.2.2 b.1) := not_not.1 hb
    rw [e]
  -- the context hop, identical until bad
  have key := ctx_hopN_iub Hb (hv.m _) (hv.sm _) hHb y hyv NView.u NView.withU
    (fun v => v.T P) (fun v g => v.withT (Function.update v.T P g)) Φ R5 C
    (fun o V u => trace5 p₀ G x.1 (ctxF Hb p₀ ns j x.2.1 (TJ Hb p₀ ns G j hj x V.1) u o) V.2)
    (fun o V u => traceE p₀ G x.1 (ctxF Hb p₀ ns j x.2.1 (TJ Hb p₀ ns G j hj x V.1) u o) V.2)
    (univ.image fun i : Fin n => (x.2.1 i).1) (tE := n * 4607) (fun _ _ _ => rfl)
    (fun o V u G5 h => viewN_withU p₀ G x.1 _ _ V.2 u (G5, u.2) _
      (runN_congr p₀ G x.1 _ _ V.2 fun i => ctxF_u5 Hb p₀ ns j x.2.1 _ u o i _ _ G5
        fun k hk => h k (mem_biUnion.2 ⟨i, mem_univ _, hk⟩)))
    (fun o V u E h => viewN_withU p₀ G x.1 _ _ V.2 u (u.1, E) _
      (runN_congr p₀ G x.1 _ _ V.2 fun i => ctxF_uE Hb p₀ ns hHb j x.2.1 _ u o i _ _ E
        fun k hk => h k (mem_biUnion.2 ⟨i, mem_univ _, hk⟩)))
    (fun o V u => by
      refine card_biUnion_le.trans ?_
      calc ∑ i : Fin n, _ ≤ ∑ _i : Fin n, 4607 := sum_le_sum fun i _ =>
            card_ctxF_kE Hb p₀ ns j _ _ u o i _ _
        _ = n * 4607 := by simp)
    (fun o G3 G3' G2 u h => by
      have e := viewN_withT p₀ G x.1 _ _ G2 u (TJ Hb p₀ ns G j hj x G3)
        (TJ Hb p₀ ns G j hj x G3')
        (runN_congr p₀ G x.1 _ _ G2 fun i => ctxF_T Hb p₀ ns j x.2.1 P x.2.2.1 G3 G3' u o i _ _
          (h _ (mem_image_of_mem _ (mem_univ i))))
      refine e.trans ?_
      show _ = NView.withT _ (Function.update (TJ Hb p₀ ns G j hj x G3) P G3')
      unfold TJ
      rw [← hP, Function.update_idem]
      rfl)
    (fun o G3 G2 u => by
      show TJ Hb p₀ ns G j hj x G3 P = G3
      unfold TJ
      rw [← hP, Function.update_self])
    hΦ.h5 hΦ.hE (by
      obtain ⟨Q, hQc, hQ⟩ := hΦ.hT
      refine ⟨fun v => colPts (Q v) (some P), fun v => (card_colPts _ _).trans (hQc v),
        fun v G3 h => hQ v _ fun k hk => ?_⟩
      by_cases hk1 : k.1 = P
      · obtain ⟨k1, k2⟩ := k
        simp only at hk1
        subst hk1
        rw [Function.update_self]
        exact h k2 (mem_colPts hk rfl)
      · rw [Function.update_of_ne hk1])
    (fun z hz => by
      refine hb _ ?_
      have eP := progRO_fst Hb (withP y.1 pj) z.2.1.2 (shOf z.2.2.2 z.1)
      rw [eP]
      unfold mainPredIC mainPred2 at hz
      exact ctx_bad Hb p₀ ns G hHb hv j hj x y hy R5 z.2.1.2 _ z.1 hz)
  have hcard : εS (q3 + (univ.image fun i : Fin n => (x.2.1 i).1).card) (qE + n * 4607) ≤
      εS (q3 + n) (qE + n * 4607) :=
    εS_mono (by have := (card_image_le (s := (univ : Finset (Fin n)))
      (f := fun i : Fin n => (x.2.1 i).1)); simp at this; omega) le_rfl
  have hR : pr (USh × KS pj) (fun b => Φ (hybVN Hb p₀ ns G j (setJ Hb p₀ ns G j hj x b))) =
      pr (USh × KS pj) (fun b => Φ (C (realRO pj Hb (withP y.1 pj) y.2 b.2.1.1 b.2.2.1
        (shOf (p := pj) (LJ Hb p₀ ns G j x b.1 b.2.2.2) b.1)) b.2.2 b.1)) := pr_congr eR
  have hS : pr (USh × KS pj) (fun b => Φ (hybVN Hb p₀ ns G (j + 1)
        (setJ Hb p₀ ns G j hj x b))) =
      pr (USh × KS pj) (fun b => Φ (C (simulate pj b.2.1.2) (b.2.2.1,
        (progRO pj Hb (withP y.1 pj) b.2.1.2 (shOf b.2.2.2 b.1)).1) b.1)) :=
    pr_congr fun b => by rw [eS b]
  rw [hR, hS]
  have := abs_sub_le (pr (USh × KS pj) (fun b => Φ (C (realRO pj Hb (withP y.1 pj) y.2 b.2.1.1
      b.2.2.1 (shOf (p := pj) (LJ Hb p₀ ns G j x b.1 b.2.2.2) b.1)) b.2.2 b.1)))
    (pr (USh × KS pj) (fun b => Φ (C (realRO pj Hb (withP y.1 pj) y.2 b.2.1.1 b.2.2.1
      (shOf b.2.2.2 b.1)) b.2.2 b.1)))
    (pr (USh × KS pj) (fun b => Φ (C (simulate pj b.2.1.2) (b.2.2.1,
      (progRO pj Hb (withP y.1 pj) b.2.1.2 (shOf b.2.2.2 b.1)).1) b.1)))
  linarith

end HopMain

/-! ## The hops and the result -/

section Chain

variable (Hb : Hashes) (p₀ : Params) {n : ℕ} (ns : Fin n → ℕ) {S : Type} [Fintype S]
  [Nonempty S] (G : NGame S n)

/-- **Hop `j`, identical until bad**: for an event `Φ` that contains `bstarN`, replacing slot `j`
by the simulator costs `εS(q₃ + n, q_E + n·4607) + Δ23N`. -/
theorem hopN_iub (hHb : HashesWF Hb) (hv : NValid G p₀ ns) (j : ℕ) (hj : j < n)
    (Φ : NView S n p₀ → Prop) (R5 : NView S n p₀ → Finset (Bytes 37)) {q3 qE : ℕ}
    (hΦ : RdN Φ R5 q3 qE) (hb : ∀ v, bstarN Hb G (fun i => pw p₀ (ns i)) R5 v → Φ v) :
    |hybN Hb p₀ ns G j Φ - hybN Hb p₀ ns G (j + 1) Φ| ≤
      εS (q3 + n) (qE + n * 4607) + Δ23N p₀.qsDegree n := by
  rw [hybN_lens Hb p₀ ns G j hj j Φ, hybN_lens Hb p₀ ns G j hj (j + 1) Φ]
  refine abs_pr_prod_sub_le _ _ fun x => ?_
  rcases hy : yJ Hb p₀ ns G j hj x with _ | y
  · have e : ∀ b, hybVN Hb p₀ ns G j (setJ Hb p₀ ns G j hj x b) =
        hybVN Hb p₀ ns G (j + 1) (setJ Hb p₀ ns G j hj x b) := hyb_none Hb p₀ ns G j hj x hy
    simp only [e, sub_self, abs_zero]
    have := εS_nonneg (q3 + n) (qE + n * 4607)
    have := Δ23N_nonneg p₀.qsDegree n
    linarith
  · exact hop_fiber_iub Hb p₀ ns G hHb hv j hj x y hy Φ R5 hΦ hb

/-- **A linear chain**: `n` hops of cost `ε` each. -/
theorem lin_chain_le (ε : ℝ) : ∀ (n : ℕ) (h : ℕ → ℝ), (∀ j < n, |h j - h (j + 1)| ≤ ε) →
    |h 0 - h n| ≤ n * ε
  | 0, h, _ => by simp
  | n + 1, h, hF => by
    have ih := lin_chain_le ε n h fun j hj => hF j (by omega)
    have := hF n (by omega)
    have := abs_sub_le (h 0) (h n) (h (n + 1))
    push_cast
    linarith

variable {Hb p₀ ns G}

/-- **The joint zero-knowledge hop on `main` for `n` proofs, linear in `n`**: all tables shared
(one `H₃`, one `H₂³` table, one `H₅` table, one cipher). For an event `F` of the view with
consistent reads (`H₅` at `R5`, the cipher at `q_E` keys, `H₃` at `q₃` points),

    |Pr[all real; F] − Pr[all simulated; F]|
        ≤ 2n·(εS(2q₃ + n, 2q_E + 2n·4607) + Δ23N(d, n)) + Pr[all simulated; bstarN].

Compared with `main_sharedAll_leN`, the factor `2ⁿ − 1` on `εS + Δ23N` becomes `2n` and the
factor on the bad event becomes `1`. -/
theorem main_sharedAll_leLin (hHb : HashesWF Hb) (hv : NValid G p₀ ns) (F : NView S n p₀ → Prop)
    (R5 : NView S n p₀ → Finset (Bytes 37)) {q3 qE : ℕ} (hF : RdN F R5 q3 qE)
    (hR : RdN R5 R5 q3 qE) :
    |hybN Hb p₀ ns G 0 F - hybN Hb p₀ ns G n F| ≤
      2 * n * (εS (2 * q3 + n) (2 * qE + 2 * n * 4607) + Δ23N p₀.qsDegree n) +
        hybN Hb p₀ ns G n (bstarN Hb G (fun i => pw p₀ (ns i)) R5) := by
  set b := bstarN Hb G (fun i => pw p₀ (ns i)) R5 with hbdef
  set ε := εS (2 * q3 + n) (2 * qE + 2 * n * 4607) + Δ23N p₀.qsDegree n with hε
  have hB := rd_bstarN Hb G (fun i => pw p₀ (ns i)) hR
  have hFB : RdN (fun v => F v ∨ b v) R5 (2 * q3) (2 * qE + n * 4607) := by
    have := rdN_or hF hB
    refine rdN_mono this (by omega) (by omega)
  have hB' : RdN b R5 (2 * q3) (2 * qE + n * 4607) := rdN_mono hB (by omega) (by omega)
  have e2 : 2 * qE + n * 4607 + n * 4607 = 2 * qE + 2 * n * 4607 := by ring
  have hop : ∀ Φ : NView S n p₀ → Prop, RdN Φ R5 (2 * q3) (2 * qE + n * 4607) →
      (∀ v, b v → Φ v) → |hybN Hb p₀ ns G 0 Φ - hybN Hb p₀ ns G n Φ| ≤ n * ε := by
    intro Φ hΦ hbΦ
    refine lin_chain_le ε n (fun j => hybN Hb p₀ ns G j Φ) fun j hj => ?_
    have := hopN_iub Hb p₀ ns G hHb hv j hj Φ R5 hΦ hbΦ
    rw [e2] at this
    exact this
  have h1 := abs_sub_le_iff.1 (hop _ hFB fun v hv => Or.inr hv)
  have h2 := abs_sub_le_iff.1 (hop _ hB' fun v hv => hv)
  -- `Pr[F] ≤ Pr[F ∨ b] ≤ Pr[F] + Pr[b]` in every hybrid
  have m : ∀ j, hybN Hb p₀ ns G j F ≤ hybN Hb p₀ ns G j (fun v => F v ∨ b v) := fun j =>
    pr_mono fun x hx => Or.inl hx
  have o : ∀ j, hybN Hb p₀ ns G j (fun v => F v ∨ b v) ≤
      hybN Hb p₀ ns G j F + hybN Hb p₀ ns G j b := fun j =>
    pr_or_le (fun x => F (hybVN Hb p₀ ns G j x)) (fun x => b (hybVN Hb p₀ ns G j x))
  have m0 := m 0
  have mn := m n
  have o0 := o 0
  have on := o n
  have hε0 : 0 ≤ ε := add_nonneg (εS_nonneg _ _) (Δ23N_nonneg _ _)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [abs_sub_le_iff]
  constructor <;> nlinarith

end Chain

end VoleMole.ZK.Sim
