import VoleMole.Privacy.SharedH3PomFRIT
import VoleMole.Privacy.PomFRITRAGame
import VoleMole.ZK.SharedH3RA

/-!
# PomFRIT blindness with one shared `H₃` and an Issuer whose interaction reads the tables

`Privacy/SharedH3PomFRIT.lean` for the game of `Privacy/PomFRITRAGame.lean`: the Issuer's key,
messages and responses read the tables (no `H₂³`), and with one shared `H₃` they read `H₃` through
the rows, at any prefix (the sessions' prefixes included, before the sessions' instances are
fixed). The Issuer of the shared model reads no slot slice (`IBudget 0 i₅ i_E`, `GBudget 0 q₅ q_E`;
then `A.at sl s` does not depend on `sl`, `AdversaryRA.at_free`).

The hops are those of `PomFRITRAGame.lean` with `ZK.Sim.zk2_sharedA` in place of `zk2_adaptive`:
session `0`'s continuation (the Issuer's responses, and session `1`'s real step 1 for its request)
reads the rows, the replaced session's column among them. The collision term is bounded pointwise
as in `deltaRA_le` (`deltaSh_le`: `≤ noHitProb + 2⁻¹²⁸`, the same bound). A session's prefix is a
function of its coins, so the column is fixed before the Issuer reads anything: no `ρ`-collision
term appears beyond the rows read (`qE`, `i_E`), and no prefix-collision term.

**`blindnessRASh_numG`**: for every Issuer that reads the tables only,

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q_E + 4i_E + 23035, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT

attribute [local irreducible] commitRefresher UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-! ## An Issuer that reads no slice -/

/-- A reader that reads no slice key does not depend on the slice. -/
lemma sReads_free {X : Type*} {p : Params} {f : Tb (RowH R) p → X} {a2 a5 aE : ℕ}
    (h : SReads p f 0 a2 a5 aE) (g g' : Tab3) (s : ShG (RowH R) p) : f (g', s) = f (g, s) := by
  obtain ⟨Q, hQ, hc⟩ := h
  have h0 : (Q (g, s)).1 = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 (hc _).1)
  refine (hQ (g, s) (g', s) ⟨fun k hk => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩).2
  rw [h0] at hk
  exact absurd hk (Finset.notMem_empty _)

namespace AdversaryRA

variable {A : AdversaryRA (RowH R)} {i5 iE q5 qE : ℕ}

lemma at_eq_of {sl sl' : SlP} {s : ShP (RowH R)} (hk : A.keyOf sl s = A.keyOf sl' s)
    (hr : ∀ t₀ t₁, A.respOf t₀ t₁ sl s = A.respOf t₀ t₁ sl' s) : A.at sl s = A.at sl' s := by
  simp only [keyOf, Prod.mk.injEq] at hk
  obtain ⟨hpk, hm0, hm1⟩ := hk
  unfold AdversaryRA.at
  congr 1
  · funext b
    cases b
    · exact hm0
    · exact hm1
  · funext t₀ t₁ i
    have := hr t₀ t₁
    simp only [respOf, Prod.mk.injEq] at this
    cases i
    · exact this.1
    · exact this.2

/-- **The Issuer that reads no slice is the same at every pair of slices.** -/
lemma at_free (hI : A.IBudget 0 i5 iE) (sl sl' : SlP) (s : ShP (RowH R)) : A.at sl s = A.at sl' s := by
  obtain ⟨g₀, g₁⟩ := sl
  obtain ⟨g₀', g₁'⟩ := sl'
  have e1 : A.at (g₀, g₁) s = A.at (g₀', g₁) s :=
    at_eq_of (sReads_free (hI.k0 g₁) g₀' g₀ s) fun t₀ t₁ => sReads_free (hI.r0 t₀ t₁ g₁) g₀' g₀ s
  have e2 : A.at (g₀', g₁) s = A.at (g₀', g₁') s :=
    at_eq_of (sReads_free (hI.k1 g₀') g₁' g₁ s) fun t₀ t₁ => sReads_free (hI.r1 t₀ t₁ g₀') g₁' g₁ s
  exact e1.trans e2

/-- **The guess that reads no slice.** -/
lemma sliceFree (hA : A.GBudget 0 q5 qE) (sl : SlP) (s : ShP (RowH R)) : (A.at sl s).SliceFree := by
  intro t₀ t₁ y sl₁ sl₂ s'
  obtain ⟨a, b⟩ := sl₁
  obtain ⟨c, d⟩ := sl₂
  have e1 := rd3_zero (hA.h30 t₀ t₁ y b s') a c
  have e2 := rd3_zero (hA.h31 t₀ t₁ y c s') b d
  exact Iff.of_eq (e1.symm.trans e2.symm)

end AdversaryRA

/-! ## The game -/

section Game

variable (Hb : Hashes) (A : AdversaryRA (RowH R))

/-- **The real game with one shared `H₃` and an Issuer that reads the tables.** -/
noncomputable def realGameRASh (b : Bool) (z : (XR × XR) × ShP (RowH R)) : Prop :=
  realGameSh Hb (A.at (z.1.1.2, z.1.2.2) z.2) b z

variable {Hb A} {i5 iE q5 qE : ℕ}

lemma realGameRASh_iff (hA : A.GBudget 0 q5 qE) (hI : A.IBudget 0 i5 iE) (b : Bool)
    (z : (XR × XR) × ShP (RowH R)) : realGameRASh Hb A b z ↔ realGameRA Hb A b (τR Hb z) := by
  unfold realGameRASh realGameRA
  rw [realGameSh_iff (AdversaryRA.sliceFree hA _ _)]
  show realGameRO Hb (A.at (z.1.1.2, z.1.2.2) z.2) b (τR Hb z) ↔
    realGameRO Hb (A.at ((τR Hb z).1.1.2, (τR Hb z).1.2.2) z.2) b (τR Hb z)
  rw [AdversaryRA.at_free hI (z.1.1.2, z.1.2.2) ((τR Hb z).1.1.2, (τR Hb z).1.2.2)]

end Game

/-! ## Hop 0 -/

section Hop0

variable {Hb : Hashes} {A : AdversaryRA (RowH R)} {q5 qE i5 iE : ℕ}

/-- Session `0`'s continuation, session `1` real on the shared `H₃`. -/
noncomputable def K0sA (Hb : Hashes) (A : AdversaryRA (RowH R)) (ref₀ : Coins refresherBytes)
    (r₀ : Coins uovM) (x₁ : XR) (s : ShP (RowH R)) : Cont2 :=
  K0 Hb A ref₀ r₀ (x₁.1, h3At s (keyP Hb x₁.1.2)) default s

/-- The reduction for session `0`, session `1` real on the shared `H₃`. -/
noncomputable def D0sA (Hb : Hashes) (A : AdversaryRA (RowH R)) (ref₀ : Coins refresherBytes)
    (r₀ : Coins uovM) (x₁ : XR) (o : Out2) (g : Tab3) (s : ShP (RowH R)) : Prop :=
  D0A Hb A ref₀ r₀ (x₁.1, h3At s (keyP Hb x₁.1.2)) o g s

lemma K0_free (hI : A.IBudget 0 i5 iE) (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR)
    (g g' : Tab3) (s : ShP (RowH R)) : K0 Hb A ref₀ r₀ x₁ g s = K0 Hb A ref₀ r₀ x₁ g' s := by
  unfold K0
  rw [AdversaryRA.at_free hI (g, x₁.2) (g', x₁.2)]

lemma K0_g3 (hI : A.IBudget 0 i5 iE) (ref₀ : Coins refresherBytes) (r₀ : Coins uovM)
    (x : Coins proveSeedBytes × Coins refresherBytes × Coins uovM) (g : Tab3) {G G' : Tab3}
    (s : ShP (RowH R)) (h : G x.1 = G' x.1) : K0 Hb A ref₀ r₀ (x, G) g s = K0 Hb A ref₀ r₀ (x, G') g s := by
  unfold K0
  rw [AdversaryRA.at_free hI (g, G) (g, G')]
  simp only [tR]
  rw [s1R_g3 x s h]

lemma D0A_free (hA : A.GBudget 0 q5 qE) (hI : A.IBudget 0 i5 iE) (ref₀ : Coins refresherBytes)
    (r₀ : Coins uovM) (x₁ : XR) (o : Out2) (g g' : Tab3) (s : ShP (RowH R)) :
    D0A Hb A ref₀ r₀ x₁ o g s ↔ D0A Hb A ref₀ r₀ x₁ o g' s := by
  unfold D0A
  rw [AdversaryRA.at_free hI (g, x₁.2) (g', x₁.2)]
  exact AdversaryRA.sliceFree hA _ _ _ _ _ _ _ _

lemma D0A_g3 (hA : A.GBudget 0 q5 qE) (hI : A.IBudget 0 i5 iE) (ref₀ : Coins refresherBytes)
    (r₀ : Coins uovM) (x : Coins proveSeedBytes × Coins refresherBytes × Coins uovM) (o : Out2)
    (g : Tab3) {G G' : Tab3} (s : ShP (RowH R)) (h : G x.1 = G' x.1) :
    D0A Hb A ref₀ r₀ (x, G) o g s = D0A Hb A ref₀ r₀ (x, G') o g s := by
  unfold D0A D0
  rw [AdversaryRA.at_free hI (g, G) (g, G')]
  apply propext
  rw [oR_g3 (Hb := Hb) _ _ x _ s h]
  exact AdversaryRA.sliceFree hA _ _ _ _ _ _ _ _

theorem hop0RASh [ZKRow R] [ZK2ARow R] (hHb : HashesWF Hb) (hA : A.GBudget 0 q5 qE)
    (hI : A.IBudget 0 i5 iE) :
    |pr ((XR × XR) × ShP (RowH R)) (fun z => G0RA Hb A (τR Hb z)) -
        pr ((XS × XR) × ShP (RowH R)) (fun z => G1RA Hb A (τ1 Hb z))| ≤
      ZKRow.εz R pP ((iE + 4607 + (iE + (qE + 4607)) + 1) + (iE + 4607 + iE + 1))
        ((i5 + 624 + (i5 + (q5 + 624))) + (i5 + 624 + i5))
        ((iE + 4607 + (iE + (qE + 4607)) + 1) + (iE + 4607 + iE + 1)) := by
  rw [← pr_equiv (eqR0 (R := RowH R)), ← pr_equiv (eqS0 (R := RowH R))]
  refine abs_pr_prod_sub_le _ _ fun ζ => ?_
  obtain ⟨⟨ref₀, r₀⟩, x₁⟩ := ζ
  have hK5 : ∀ o1, Rd5 (fun s => K0sA Hb A ref₀ r₀ x₁ s o1) (i5 + 624 + i5) := fun o1 =>
    rd5_h3At (f := fun G s => K0 Hb A ref₀ r₀ (x₁.1, G) default s o1)
      (fun G => (hyp2RA_R hHb hI ref₀ r₀ (x₁.1, G)).h5 o1 default) (keyP Hb x₁.1.2)
  have hKE : ∀ o1, RdE (fun s => K0sA Hb A ref₀ r₀ x₁ s o1) (iE + 4607 + iE + 1) := fun o1 =>
    rdE_h3At (f := fun G s => K0 Hb A ref₀ r₀ (x₁.1, G) default s o1) x₁.1.1
      (fun G G' s h => by rw [K0_g3 hI ref₀ r₀ x₁.1 default s h])
      (fun G => (hyp2RA_R hHb hI ref₀ r₀ (x₁.1, G)).hE o1 default) (keyP Hb x₁.1.2)
  have hD : Budget pP 0 (i5 + 624 + (i5 + (q5 + 624))) (iE + 4607 + (iE + (qE + 4607)) + 1)
      (D0sA Hb A ref₀ r₀ x₁) :=
    ⟨fun o s => ⟨fun _ => ∅, fun _ => by simp, fun g g' _ =>
        propext (D0A_free hA hI ref₀ r₀ _ o g' g s)⟩,
      fun o g => rd5_h3At (f := fun G s => D0A Hb A ref₀ r₀ (x₁.1, G) o g s)
        (fun G => (budget_D0A hHb hA hI ref₀ r₀ (x₁.1, G)).h5 o g) (keyP Hb x₁.1.2),
      fun o g => rdE_h3At (f := fun G s => D0A Hb A ref₀ r₀ (x₁.1, G) o g s) x₁.1.1
        (fun G G' s h => D0A_g3 hA hI ref₀ r₀ x₁.1 o g s h)
        (fun G => (budget_D0A hHb hA hI ref₀ r₀ (x₁.1, G)).hE o g) (keyP Hb x₁.1.2)⟩
  have key := zk2_sharedA Hb (stOf ref₀) (toBA (List.ofFn r₀)) uovM (keyP Hb (ref₀, r₀))
    (K0sA Hb A ref₀ r₀ x₁)
    (fun s => (hyp2RA_R hHb hI ref₀ r₀ (x₁.1, h3At s (keyP Hb x₁.1.2))).hyp default s)
    (by rw [size_toBA, List.length_ofFn])
    (fun s G2 => K0_h23 hI ref₀ r₀ (x₁.1, h3At s (keyP Hb x₁.1.2)) default s G2) hK5 hKE hHb
    (smallParams_of_le (p := pP) (by decide) (by decide)) (D0sA Hb A ref₀ r₀ x₁) hD
  refine le_of_eq_of_le (congrArg abs (congrArg₂ (· - ·) ?_ ?_)) key
  · refine pr_congr fun a => ?_
    have e := realRO2_cont Hb (stOf ref₀) (toBA (List.ofFn r₀)) a.1.1 (h3At a.2 (keyP Hb (ref₀, r₀))) a.2
      (K := K0 Hb A ref₀ r₀ (x₁.1, h3At a.2 (keyP Hb x₁.1.2)) (h3At a.2 (keyP Hb (ref₀, r₀))))
      (K' := K0sA Hb A ref₀ r₀ x₁) (K0_free hI ref₀ r₀ _ _ _ a.2)
    refine (G0RA_iff_D0A ref₀ r₀ (x₁.1, h3At a.2 (keyP Hb x₁.1.2))
      ((a.1.1, h3At a.2 (keyP Hb (ref₀, r₀))), a.2)).trans ?_
    refine (Iff.of_eq (congrArg (fun o => D0A Hb A ref₀ r₀ (x₁.1, h3At a.2 (keyP Hb x₁.1.2)) o
      (h3At a.2 (keyP Hb (ref₀, r₀))) a.2) e)).trans ?_
    exact D0A_free hA hI ref₀ r₀ _ _ _ _ _
  · refine pr_congr fun a => ?_
    have e1 := simRO2_cont Hb (stOf ref₀) uovM a.1.1 a.2
      (K := K0 Hb A ref₀ r₀ (x₁.1, h3At a.2 (keyP Hb x₁.1.2)) a.1.2) (K' := K0sA Hb A ref₀ r₀ x₁)
      (K0_free hI ref₀ r₀ _ _ _ a.2)
    have e2 := progRO2_cont Hb (stOf ref₀) uovM a.1.1 a.2
      (K := K0 Hb A ref₀ r₀ (x₁.1, h3At a.2 (keyP Hb x₁.1.2)) a.1.2) (K' := K0sA Hb A ref₀ r₀ x₁)
      (K0_free hI ref₀ r₀ _ _ _ a.2)
    have e3 : h3At (progRO2 Hb (stOf ref₀) uovM (K0sA Hb A ref₀ r₀ x₁) a.1.1 a.2) (keyP Hb x₁.1.2) =
        h3At a.2 (keyP Hb x₁.1.2) := h3At_progRO2 _ _ _ _ _ _ _
    refine (G1RA_iff_D0A hI ref₀ r₀ (x₁.1, h3At a.2 (keyP Hb x₁.1.2)) a).trans ?_
    refine (Iff.of_eq (congrArg₂ (fun o v => D0A Hb A ref₀ r₀ (x₁.1, h3At a.2 (keyP Hb x₁.1.2)) o
      a.1.2 v) e1 e2)).trans ?_
    exact Iff.of_eq (congrArg (fun G => D0A Hb A ref₀ r₀ (x₁.1, G)
      (simRO2 Hb (stOf ref₀) uovM (K0sA Hb A ref₀ r₀ x₁) a.1.1 a.2) a.1.2
      (progRO2 Hb (stOf ref₀) uovM (K0sA Hb A ref₀ r₀ x₁) a.1.1 a.2)) e3.symm)

end Hop0

/-! ## Hop 1 -/

section Hop1

variable {Hb : Hashes} {A : AdversaryRA (RowH R)} {q5 qE i5 iE : ℕ}

/-- Session `1`'s continuation, session `0` simulated. -/
noncomputable def K1sA (Hb : Hashes) (A : AdversaryRA (RowH R)) (ref₁ : Coins refresherBytes)
    (r₁ : Coins uovM) (y₀ : XS) (s : ShP (RowH R)) : Cont2 :=
  K1 Hb A ref₁ r₁ y₀ default s

lemma K1_free (hI : A.IBudget 0 i5 iE) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (y₀ : XS)
    (g g' : Tab3) (s : ShP (RowH R)) : K1 Hb A ref₁ r₁ y₀ g s = K1 Hb A ref₁ r₁ y₀ g' s := by
  unfold K1
  rw [AdversaryRA.at_free hI (y₀.2, g) (y₀.2, g')]

lemma D1A_free (hA : A.GBudget 0 q5 qE) (hI : A.IBudget 0 i5 iE) (ref₁ : Coins refresherBytes)
    (r₁ : Coins uovM) (y₀ : XS) (o : Out2) (g g' : Tab3) (s : ShP (RowH R)) :
    D1A Hb A ref₁ r₁ y₀ o g s ↔ D1A Hb A ref₁ r₁ y₀ o g' s := by
  unfold D1A
  rw [AdversaryRA.at_free hI (y₀.2, g) (y₀.2, g')]
  exact AdversaryRA.sliceFree hA _ _ _ _ _ _ _ _

/-- **The collision term with one shared `H₃`**: `≤ noHitProb + 2⁻¹²⁸`, as `deltaRA_le`. -/
theorem deltaSh_le (hHb : HashesWF Hb) (A : AdversaryRA (RowH R)) :
    pr ((XS × XR) × ShP (RowH R)) (fun z =>
      badRO Hb (A.at ((τ1 Hb z).1.1.2, (τ1 Hb z).1.2.2) z.2) (τ1 Hb z)) ≤
      noHitProb + 1 / 2 ^ 128 := by
  refine (pr_mono (Q := fun z => firstHit z.1.1.1.1.1.1.2.1 = none ∨
      preTail (blk (preLen pP) (pre1 (A.at ((τ1 Hb z).1.1.2, (τ1 Hb z).1.2.2) z.2) Hb (τ1 Hb z))) =
        ba z.1.1.1.1.1.2.2.2.2.2)
    fun z hz => ?_).trans ?_
  · obtain ⟨⟨y₀, x₁⟩, s⟩ := z
    exact deltaRO_event' _ hHb y₀ (x₁.1, h3At s (keyP Hb x₁.1.2)) s hz
  refine pr_le_of_snd fun s => pr_le_of_snd fun x₁ => pr_le_of_snd fun g₀ =>
    pr_le_of_snd fun rr => pr_le_of_snd fun fb => ?_
  have h := pr_simCoins_tail_le (p := pP)
    (fun c => preTail (blk (preLen pP) (pre1 (A.at (g₀, h3At s (keyP Hb x₁.1.2)) s) Hb
      (((((c, fb), rr), g₀), (x₁.1, h3At s (keyP Hb x₁.1.2))), s))))
    fun c a => by simp only [pre1, tS, s1S, s1C_tail]
  rw [tail_pP] at h
  exact h

theorem hop1RASh [ZKRow R] [ZK2ARow R] (hHb : HashesWF Hb) (hA : A.GBudget 0 q5 qE)
    (hI : A.IBudget 0 i5 iE) :
    |pr ((XS × XR) × ShP (RowH R)) (fun z => G1RA Hb A (τ1 Hb z)) -
        pr ((XS × XS) × ShP (RowH R)) (G2RA Hb A)| ≤
      ZKRow.εz R pP ((iE + 4607 + (iE + (qE + 13821))) + (iE + 4607 + iE))
        ((i5 + (i5 + (q5 + 312))) + (i5 + i5))
        ((iE + 4607 + (iE + (qE + 13821))) + (iE + 4607 + iE)) + (noHitProb + 1 / 2 ^ 128) := by
  have hδ : |pr ((XS × XR) × ShP (RowH R)) (fun z => G1RA Hb A (τ1 Hb z)) -
      pr ((XS × XR) × ShP (RowH R)) (fun z => G1'RA Hb A (τ1 Hb z))| ≤ noHitProb + 1 / 2 ^ 128 :=
    (abs_pr_sub_le_of_agree _ _ _ fun z hz => G1_iff_G1'_of Hb _ (τ1 Hb z) hz).trans
      (deltaSh_le hHb A)
  suffices h : |pr ((XS × XR) × ShP (RowH R)) (fun z => G1'RA Hb A (τ1 Hb z)) -
      pr ((XS × XS) × ShP (RowH R)) (G2RA Hb A)| ≤
      ZKRow.εz R pP ((iE + 4607 + (iE + (qE + 13821))) + (iE + 4607 + iE))
        ((i5 + (i5 + (q5 + 312))) + (i5 + i5))
        ((iE + 4607 + (iE + (qE + 13821))) + (iE + 4607 + iE)) by
    have := abs_sub_le (pr ((XS × XR) × ShP (RowH R)) (fun z => G1RA Hb A (τ1 Hb z)))
      (pr ((XS × XR) × ShP (RowH R)) (fun z => G1'RA Hb A (τ1 Hb z)))
      (pr ((XS × XS) × ShP (RowH R)) (G2RA Hb A))
    linarith
  rw [← pr_equiv (eqR1 (R := RowH R)), ← pr_equiv (eqS1 (R := RowH R))]
  refine abs_pr_prod_sub_le _ _ fun ζ => ?_
  obtain ⟨y₀, ref₁, r₁⟩ := ζ
  have hK := hyp2RA_S (Hb := Hb) hI ref₁ r₁ y₀
  have hD : Budget pP 0 (i5 + (i5 + (q5 + 312))) (iE + 4607 + (iE + (qE + 13821)))
      (D1A Hb A ref₁ r₁ y₀) :=
    ⟨fun o s => ⟨fun _ => ∅, fun _ => by simp, fun g g' _ =>
      propext (D1A_free hA hI ref₁ r₁ y₀ o g' g s)⟩, (budget_D1A hA hI ref₁ r₁ y₀).h5,
      (budget_D1A hA hI ref₁ r₁ y₀).hE⟩
  have key := zk2_sharedA Hb (stOf ref₁) (toBA (List.ofFn r₁)) uovM (keyP Hb (ref₁, r₁))
    (K1sA Hb A ref₁ r₁ y₀) (fun s => hK.hyp default s) hK.size (fun s G2 => hK.h2 default s G2)
    (fun o1 => hK.h5 o1 default) (fun o1 => hK.hE o1 default) hHb
    (smallParams_of_le (p := pP) (by decide) (by decide)) (D1A Hb A ref₁ r₁ y₀) hD
  refine le_of_eq_of_le (congrArg abs (congrArg₂ (· - ·) ?_ ?_)) key
  · refine pr_congr fun a => ?_
    have e := realRO2_cont Hb (stOf ref₁) (toBA (List.ofFn r₁)) a.1.1 (h3At a.2 (keyP Hb (ref₁, r₁))) a.2
      (K := K1 Hb A ref₁ r₁ y₀ (h3At a.2 (keyP Hb (ref₁, r₁)))) (K' := K1sA Hb A ref₁ r₁ y₀)
      (K1_free hI ref₁ r₁ y₀ _ _ a.2)
    refine (G1'RA_iff_D1A y₀ ref₁ r₁ ((a.1.1, h3At a.2 (keyP Hb (ref₁, r₁))), a.2)).trans ?_
    refine (Iff.of_eq (congrArg (fun o => D1A Hb A ref₁ r₁ y₀ o
      (h3At a.2 (keyP Hb (ref₁, r₁))) a.2) e)).trans ?_
    exact D1A_free hA hI ref₁ r₁ y₀ _ _ _ _
  · refine pr_congr fun a => ?_
    have e1 := simRO2_cont Hb (stOf ref₁) uovM a.1.1 a.2
      (K := K1 Hb A ref₁ r₁ y₀ a.1.2) (K' := K1sA Hb A ref₁ r₁ y₀) (K1_free hI ref₁ r₁ y₀ _ _ a.2)
    have e2 := progRO2_cont Hb (stOf ref₁) uovM a.1.1 a.2
      (K := K1 Hb A ref₁ r₁ y₀ a.1.2) (K' := K1sA Hb A ref₁ r₁ y₀) (K1_free hI ref₁ r₁ y₀ _ _ a.2)
    refine (G2RA_iff_D1A hI y₀ ref₁ r₁ a).trans ?_
    exact Iff.of_eq (congrArg₂ (fun o v => D1A Hb A ref₁ r₁ y₀ o a.1.2 v) e1 e2)

end Hop1

/-! ## Blindness -/

section Blind

variable {Hb : Hashes} [ZKRow R] [ZK2ARow R]

theorem blindnessRASh (hHb : HashesWF Hb) (A : AdversaryRA (RowH R)) {q5 qE i5 iE : ℕ}
    (hA : A.GBudget 0 q5 qE) (hI : A.IBudget 0 i5 iE) :
    |pr ((XR × XR) × ShP (RowH R)) (realGameRASh Hb A false) -
        pr ((XR × XR) × ShP (RowH R)) (realGameRASh Hb A true)| ≤
      2 * (ZKRow.εz R pP ((iE + 4607 + (iE + (qE + 4607)) + 1) + (iE + 4607 + iE + 1))
          ((i5 + 624 + (i5 + (q5 + 624))) + (i5 + 624 + i5))
          ((iE + 4607 + (iE + (qE + 4607)) + 1) + (iE + 4607 + iE + 1)) +
        ZKRow.εz R pP ((iE + 4607 + (iE + (qE + 13821))) + (iE + 4607 + iE))
          ((i5 + (i5 + (q5 + 312))) + (i5 + i5))
          ((iE + 4607 + (iE + (qE + 13821))) + (iE + 4607 + iE))) +
        2 * (noHitProb + 1 / 2 ^ 128) := by
  have g0 : ∀ {B : AdversaryRA (RowH R)}, B.GBudget 0 q5 qE → B.IBudget 0 i5 iE →
      pr ((XR × XR) × ShP (RowH R)) (realGameRASh Hb B false) =
        pr ((XR × XR) × ShP (RowH R)) (fun z => G0RA Hb B (τR Hb z)) := fun hB hBI =>
    pr_congr fun z => (realGameRASh_iff hB hBI false z).trans (realGameRA_iff Hb _ _)
  have h1 : pr ((XR × XR) × ShP (RowH R)) (realGameRASh Hb A true) =
      pr ((XR × XR) × ShP (RowH R)) (realGameRASh Hb A.swap false) := by
    rw [← pr_equiv swapXR (realGameRASh Hb A.swap false)]
    refine pr_congr fun z => ?_
    rw [realGameRASh_iff hA hI, realGameRA_true, realGameRASh_iff hA.swap hI.swap]
    exact Iff.rfl
  have c0 := (abs_sub_le _ _ _).trans (add_le_add (hop0RASh hHb hA hI) (hop1RASh hHb hA hI))
  have c1 := (abs_sub_le _ _ _).trans (add_le_add (hop0RASh hHb hA.swap hI.swap)
    (hop1RASh hHb hA.swap hI.swap))
  have hs := G2RA_swap Hb A
  rw [h1, g0 hA hI, g0 hA.swap hI.swap]
  rw [hs] at c0
  have := abs_sub_le (pr ((XR × XR) × ShP (RowH R)) (fun z => G0RA Hb A (τR Hb z)))
    (pr ((XS × XS) × ShP (RowH R)) (G2RA Hb A.swap))
    (pr ((XR × XR) × ShP (RowH R)) (fun z => G0RA Hb A.swap (τR Hb z)))
  rw [abs_sub_comm (pr ((XS × XS) × ShP (RowH R)) (G2RA Hb A.swap))] at this
  linarith

/-- **PomFRIT blindness with one shared `H₃` and an Issuer that reads the tables, every term
explicit, for every type of cipher rows** (`ZKRow R`, `ZK2ARow R`; SHAKE as the base record):

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q_E + 4i_E + 23035, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸. -/
theorem blindnessRASh_numG (A : AdversaryRA (RowH R)) {q5 qE i5 iE : ℕ}
    (hA : A.GBudget 0 q5 qE) (hI : A.IBudget 0 i5 iE) :
    |pr ((XR × XR) × ShP (RowH R)) (realGameRASh Hashes.shake A false) -
        pr ((XR × XR) × ShP (RowH R)) (realGameRASh Hashes.shake A true)| ≤
      4 * ZKRow.εz R pP (qE + 4 * iE + 23035) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 := by
  have h := blindnessRASh hashesWF_shake A hA hI
  have e1 := ZKRow.εz_mono (R := R) pP
    (q3 := (iE + 4607 + (iE + (qE + 4607)) + 1) + (iE + 4607 + iE + 1)) (q3' := qE + 4 * iE + 23035)
    (q5 := (i5 + 624 + (i5 + (q5 + 624))) + (i5 + 624 + i5)) (q5' := q5 + 4 * i5 + 1872)
    (qE := (iE + 4607 + (iE + (qE + 4607)) + 1) + (iE + 4607 + iE + 1)) (qE' := qE + 4 * iE + 23035)
    (by omega) (by omega) (by omega)
  have e2 := ZKRow.εz_mono (R := R) pP
    (q3 := (iE + 4607 + (iE + (qE + 13821))) + (iE + 4607 + iE)) (q3' := qE + 4 * iE + 23035)
    (q5 := (i5 + (i5 + (q5 + 312))) + (i5 + i5)) (q5' := q5 + 4 * i5 + 1872)
    (qE := (iE + 4607 + (iE + (qE + 13821))) + (iE + 4607 + iE)) (qE' := qE + 4 * iE + 23035)
    (by omega) (by omega) (by omega)
  refine h.trans ?_
  have : (2 : ℝ) / 2 ^ 128 = 2 * (1 / 2 ^ 128) := by ring
  linarith

/-- **PomFRIT blindness with one shared `H₃` and a table-reading Issuer, function rows.** -/
theorem blindnessRASh_num (A : AdversaryRA (RowH (Blk → Blk))) {q5 qE i5 iE : ℕ}
    (hA : A.GBudget 0 q5 qE) (hI : A.IBudget 0 i5 iE) :
    |pr ((XR × XR) × ShP (RowH (Blk → Blk))) (realGameRASh Hashes.shake A false) -
        pr ((XR × XR) × ShP (RowH (Blk → Blk))) (realGameRASh Hashes.shake A true)| ≤
      4 * εRO (qE + 4 * iE + 23035) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 :=
  blindnessRASh_numG A hA hI

/-- **PomFRIT blindness with one shared `H₃` and a table-reading Issuer, AES as uniformly random
permutations.** -/
theorem blindnessRASh_num_perm (A : AdversaryRA (RowH (Equiv.Perm Blk))) {q5 qE i5 iE : ℕ}
    (hA : A.GBudget 0 q5 qE) (hI : A.IBudget 0 i5 iE) :
    |pr ((XR × XR) × ShP (RowH (Equiv.Perm Blk))) (realGameRASh Hashes.shake A false) -
        pr ((XR × XR) × ShP (RowH (Equiv.Perm Blk))) (realGameRASh Hashes.shake A true)| ≤
      4 * εROPm pP (qE + 4 * iE + 23035) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 :=
  blindnessRASh_numG A hA hI

end Blind

end VoleMole.Privacy.PomFRIT
