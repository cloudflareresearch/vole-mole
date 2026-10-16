import VoleMole.Privacy.PomFRITRA

/-!
# PomFRIT blindness with a table-reading Issuer: the game, the hops and the bound

The game and the hybrids of `Privacy/PomFRITRA.lean`'s model: `realGameRA`, the hops
`hop0RA`/`hop1RA` (`ZK.Sim.zk2_adaptive`), the collision term `deltaRA` (`deltaRA_le`), the
exchange of the roles `G2RA_swap`, and **`blindnessRA_lean_num`**.

**Cipher rows.** Everything here is stated for every type of cipher rows `R` (the shared
tables `ZK.Sim.ShG R p`, `ZK/ReadsRO.lean`) with `ZKRow R`, `ZK2ARow R`; `blindnessRA_lean_numG` is the generic
Lean-prover bound and `blindnessRA_lean_num` its instance at function rows (`Blk → Blk`, the PRF
view); `Privacy/PermRA.lean` instantiates it at permutation rows (AES as uniformly random
permutations, the adversary reading whole rows: forward and inverse queries).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT

-- `Com` and the UOV map evaluate Keccak and the public map; nothing below needs to unfold them.
attribute [local irreducible] commitRefresher UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-! ## The game and the hybrids, at the Issuer at the tables -/

section Game

variable (Hb : Hashes) (A : AdversaryRA R)

/-- **The real game with an Issuer whose interaction reads the tables**: `realGameRO` (the spec's
protocol with the Lean prover on the tables) for the Issuer at the game's slices and tables. -/
noncomputable def realGameRA (b : Bool) (z : (XR × XR) × ShP R) : Prop :=
  realGameRO Hb (A.at (z.1.1.2, z.1.2.2) z.2) b z

/-- `G0` at the Issuer at the tables. -/
noncomputable def G0RA (z : (XR × XR) × ShP R) : Prop := G0 Hb (A.at (z.1.1.2, z.1.2.2) z.2) z

/-- `G1` at the Issuer at the (original) tables. -/
noncomputable def G1RA (z : (XS × XR) × ShP R) : Prop := G1 Hb (A.at (z.1.1.2, z.1.2.2) z.2) z

/-- `G1'` at the Issuer at the tables. -/
noncomputable def G1'RA (z : (XS × XR) × ShP R) : Prop := G1' Hb (A.at (z.1.1.2, z.1.2.2) z.2) z

/-- `G2` at the Issuer at the (original) tables. -/
noncomputable def G2RA (z : (XS × XS) × ShP R) : Prop := G2 Hb (A.at (z.1.1.2, z.1.2.2) z.2) z

/-- The event of `deltaRO` for a fixed Issuer: session `1`, run for real, reads `H₂³` differently on
the tables session `0`'s simulator programmed. -/
def badRO (A' : AdversaryRO R) (z : (XS × XR) × ShP R) : Prop :=
  oR Hb A' (A'.msg true) true z.1.2 (tS Hb A' (A'.msg false) z.1.1)
      (pS Hb A' (A'.msg false) false z.1.1 (tR Hb A' (A'.msg true) z.1.2) z.2) ≠
    oR Hb A' (A'.msg true) true z.1.2 (tS Hb A' (A'.msg false) z.1.1) z.2

/-- **The programming collision term** at the Issuer at the tables. -/
noncomputable def deltaRA : ℝ :=
  pr ((XS × XR) × ShP R) (fun z => badRO Hb (A.at (z.1.1.2, z.1.2.2) z.2) z)

lemma realGameRA_iff (z : (XR × XR) × ShP R) : realGameRA Hb A false z ↔ G0RA Hb A z :=
  realGameRO_iff Hb _ z

lemma realGameRA_true (z : (XR × XR) × ShP R) :
    realGameRA Hb A true z ↔ realGameRA Hb A.swap false (swapXR z) :=
  realGameRO_true Hb _ z

/-- **`G1` and `G1'` agree for a fixed Issuer unless session `1` reads a programmed point**
(the body of `G1_G1'`). -/
lemma G1_iff_G1'_of (A' : AdversaryRO R) (z : (XS × XR) × ShP R) (hz : ¬ badRO Hb A' z) :
    G1 Hb A' z ↔ G1' Hb A' z := by
  obtain ⟨⟨y₀, x₁⟩, s⟩ := z
  have hz' := not_not.1 hz
  dsimp only at hz'
  set v := pS Hb A' (A'.msg false) false y₀ (tR Hb A' (A'.msg true) x₁) s with hv
  set o := oR Hb A' (A'.msg true) true x₁ (tS Hb A' (A'.msg false) y₀) s with ho
  have ho1 : (o.1, o.2.1) = s1R Hb x₁ s := oR_s1 Hb A' _ _ _ _ _
  have hvs : v.2.2 = s.2.2 := rfl
  have h1 : oS Hb A' (A'.msg false) false y₀ (tR Hb A' (A'.msg true) x₁) s =
      oS Hb A' (A'.msg false) false y₀
        (fun _ => tOf A' (A'.msg true) x₁.1.2.1 x₁.1.2.2 (o.1, o.2.1)) s :=
    oS_cont Hb A' _ _ _ s (by rw [ho1]; rfl)
  have h2 : v = pS Hb A' (A'.msg false) false y₀
      (fun _ => tOf A' (A'.msg true) x₁.1.2.1 x₁.1.2.2 (o.1, o.2.1)) s :=
    pS_cont Hb A' _ _ _ s (by rw [ho1]; rfl)
  have h3 : oR Hb A' (A'.msg true) true x₁ (fun _ => tOf A' (A'.msg false) y₀.1.2.1 y₀.1.2.2
      ((oS Hb A' (A'.msg false) false y₀ (tR Hb A' (A'.msg true) x₁) s).1,
       (oS Hb A' (A'.msg false) false y₀ (tR Hb A' (A'.msg true) x₁) s).2.1)) v = o := by
    have hc : tOf A' (A'.msg false) y₀.1.2.1 y₀.1.2.2
        ((oS Hb A' (A'.msg false) false y₀ (tR Hb A' (A'.msg true) x₁) s).1,
         (oS Hb A' (A'.msg false) false y₀ (tR Hb A' (A'.msg true) x₁) s).2.1) =
        tS Hb A' (A'.msg false) y₀ v := by
      rw [oS_s1, tS, s1S_eq Hb y₀ s v hvs]
    rw [oR_cont Hb A' (A'.msg true) true x₁ v (t₁ := fun _ => tOf A' (A'.msg false) y₀.1.2.1 y₀.1.2.2
      ((oS Hb A' (A'.msg false) false y₀ (tR Hb A' (A'.msg true) x₁) s).1,
       (oS Hb A' (A'.msg false) false y₀ (tR Hb A' (A'.msg true) x₁) s).2.1))
      (t₂ := tS Hb A' (A'.msg false) y₀) hc, ← hz']
  show G1 Hb A' ((y₀, x₁), s) ↔ G1' Hb A' ((y₀, x₁), s)
  unfold G1 G1' D1
  dsimp only
  rw [← hv, h3, h1, ← h2]

/-- **`G1` and the reduction's real side agree unless session `1` reads a programmed point.** -/
theorem G1RA_G1'RA : |pr ((XS × XR) × ShP R) (G1RA Hb A) - pr ((XS × XR) × ShP R) (G1'RA Hb A)| ≤
    deltaRA Hb A :=
  abs_pr_sub_le_of_agree _ _ _ fun z hz => G1_iff_G1'_of Hb _ z hz

end Game

/-! ## The hops -/

section Hops

variable {Hb : Hashes} {A : AdversaryRA R} {q3 q5 qE i3 i5 iE : ℕ}

/-- The real two-phase prover reads its continuation at its tables only. -/
lemma realRO2_at (st : Statement) (r : ByteArray) (K : ShG R st.params → Cont2) (ρ : Bytes 16)
    (G3 : Tab3) (s : ShG R st.params) :
    realRO2 Hb st r K ρ G3 s = realRO2 Hb st r (fun _ => K s) ρ G3 s := rfl

lemma simRO2_at (st : Statement) (n : ℕ) (K : ShG R st.params → Cont2) (c : SimCoins2 st.params)
    (s : ShG R st.params) : simRO2 Hb st n K c s = simRO2 Hb st n (fun _ => K s) c s := rfl

lemma progRO2_at (st : Statement) (n : ℕ) (K : ShG R st.params → Cont2) (c : SimCoins2 st.params)
    (s : ShG R st.params) : progRO2 Hb st n K c s = progRO2 Hb st n (fun _ => K s) c s := rfl

lemma G0RA_iff_D0A (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR)
    (a : (Bytes 16 × Tab3) × ShP R) :
    G0RA Hb A ((((a.1.1, ref₀, r₀), a.1.2), x₁), a.2) ↔
      D0A Hb A ref₀ r₀ x₁ (realRO2 Hb (stOf ref₀) (toBA (List.ofFn r₀)) (K0 Hb A ref₀ r₀ x₁ a.1.2)
        a.1.1 a.1.2 a.2) a.1.2 a.2 := by
  have h := G0_iff_D0 Hb (A.at (a.1.2, x₁.2) a.2) ref₀ r₀ x₁ a
  rw [realRO2_at (Hb := Hb) (st := stOf ref₀) (r := toBA (List.ofFn r₀)) (ρ := a.1.1) (G3 := a.1.2)
    (s := a.2)] at h
  unfold D0A G0RA
  rw [realRO2_at (Hb := Hb) (st := stOf ref₀) (r := toBA (List.ofFn r₀)) (K := K0 Hb A ref₀ r₀ x₁ a.1.2)
    (ρ := a.1.1) (G3 := a.1.2) (s := a.2)]
  exact h

lemma G1RA_iff_D0A (hI : A.IBudget i3 i5 iE) (ref₀ : Coins refresherBytes) (r₀ : Coins uovM)
    (x₁ : XR) (a : (SimCoins2 pP × Tab3) × ShP R) :
    G1RA Hb A ((((a.1.1, ref₀, r₀), a.1.2), x₁), a.2) ↔
      D0A Hb A ref₀ r₀ x₁ (simRO2 Hb (stOf ref₀) uovM (K0 Hb A ref₀ r₀ x₁ a.1.2) a.1.1 a.2) a.1.2
        (progRO2 Hb (stOf ref₀) uovM (K0 Hb A ref₀ r₀ x₁ a.1.2) a.1.1 a.2) := by
  have h := G1_iff_D0 Hb (A.at (a.1.2, x₁.2) a.2) ref₀ r₀ x₁ a
  rw [simRO2_at (Hb := Hb) (st := stOf ref₀) (n := uovM) (c := a.1.1) (s := a.2),
    progRO2_at (Hb := Hb) (st := stOf ref₀) (n := uovM) (c := a.1.1) (s := a.2)] at h
  have e : A.at (a.1.2, x₁.2) (progRO2 Hb (stOf ref₀) uovM (K0 Hb A ref₀ r₀ x₁ a.1.2) a.1.1 a.2) =
      A.at (a.1.2, x₁.2) a.2 :=
    hI.at_h23 (a.1.2, x₁.2) a.2 (progRO2 Hb (stOf ref₀) uovM (K0 Hb A ref₀ r₀ x₁ a.1.2) a.1.1 a.2).1
  unfold D0A G1RA
  rw [e, simRO2_at (Hb := Hb) (st := stOf ref₀) (n := uovM) (K := K0 Hb A ref₀ r₀ x₁ a.1.2)
      (c := a.1.1) (s := a.2),
    progRO2_at (Hb := Hb) (st := stOf ref₀) (n := uovM) (K := K0 Hb A ref₀ r₀ x₁ a.1.2)
      (c := a.1.1) (s := a.2)]
  exact h

lemma G1'RA_iff_D1A (y₀ : XS) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM)
    (a : (Bytes 16 × Tab3) × ShP R) :
    G1'RA Hb A ((y₀, ((a.1.1, ref₁, r₁), a.1.2)), a.2) ↔
      D1A Hb A ref₁ r₁ y₀ (realRO2 Hb (stOf ref₁) (toBA (List.ofFn r₁)) (K1 Hb A ref₁ r₁ y₀ a.1.2)
        a.1.1 a.1.2 a.2) a.1.2 a.2 := by
  have h := G1'_iff_D1 Hb (A.at (y₀.2, a.1.2) a.2) y₀ ref₁ r₁ a
  rw [realRO2_at (Hb := Hb) (st := stOf ref₁) (r := toBA (List.ofFn r₁)) (ρ := a.1.1) (G3 := a.1.2)
    (s := a.2)] at h
  unfold D1A G1'RA
  rw [realRO2_at (Hb := Hb) (st := stOf ref₁) (r := toBA (List.ofFn r₁)) (K := K1 Hb A ref₁ r₁ y₀ a.1.2)
    (ρ := a.1.1) (G3 := a.1.2) (s := a.2)]
  exact h

lemma G2RA_iff_D1A (hI : A.IBudget i3 i5 iE) (y₀ : XS) (ref₁ : Coins refresherBytes)
    (r₁ : Coins uovM) (a : (SimCoins2 pP × Tab3) × ShP R) :
    G2RA Hb A ((y₀, ((a.1.1, ref₁, r₁), a.1.2)), a.2) ↔
      D1A Hb A ref₁ r₁ y₀ (simRO2 Hb (stOf ref₁) uovM (K1 Hb A ref₁ r₁ y₀ a.1.2) a.1.1 a.2) a.1.2
        (progRO2 Hb (stOf ref₁) uovM (K1 Hb A ref₁ r₁ y₀ a.1.2) a.1.1 a.2) := by
  have h := G2_iff_D1 Hb (A.at (y₀.2, a.1.2) a.2) y₀ ref₁ r₁ a
  rw [simRO2_at (Hb := Hb) (st := stOf ref₁) (n := uovM) (c := a.1.1) (s := a.2),
    progRO2_at (Hb := Hb) (st := stOf ref₁) (n := uovM) (c := a.1.1) (s := a.2)] at h
  have e : A.at (y₀.2, a.1.2) (progRO2 Hb (stOf ref₁) uovM (K1 Hb A ref₁ r₁ y₀ a.1.2) a.1.1 a.2) =
      A.at (y₀.2, a.1.2) a.2 :=
    hI.at_h23 (y₀.2, a.1.2) a.2 (progRO2 Hb (stOf ref₁) uovM (K1 Hb A ref₁ r₁ y₀ a.1.2) a.1.1 a.2).1
  unfold D1A G2RA
  rw [e, simRO2_at (Hb := Hb) (st := stOf ref₁) (n := uovM) (K := K1 Hb A ref₁ r₁ y₀ a.1.2)
      (c := a.1.1) (s := a.2),
    progRO2_at (Hb := Hb) (st := stOf ref₁) (n := uovM) (K := K1 Hb A ref₁ r₁ y₀ a.1.2)
      (c := a.1.1) (s := a.2)]
  exact h

/-- **Hop 0** (`G0 → G1`): session `0` simulated, by `zk2_adaptive` for its two-phase run, its
continuation (the Issuer's response) reading the tables after its step 1. -/
theorem hop0RA [ZKRow R] [ZK2ARow R] (hHb : HashesWF Hb) (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i5 iE) :
    |pr ((XR × XR) × ShP R) (G0RA Hb A) - pr ((XS × XR) × ShP R) (G1RA Hb A)| ≤
      ZKRow.εz R pP ((i3 + (i3 + q3)) + (i3 + i3)) ((i5 + 624 + (i5 + (q5 + 624))) + (i5 + 624 + i5))
        ((iE + 4607 + (iE + (qE + 4607))) + (iE + 4607 + iE)) := by
  have e1 : pr ((XR × XR) × ShP R) (G0RA Hb A) =
      pr (((Coins refresherBytes × Coins uovM) × XR) × ((Bytes 16 × Tab3) × ShP R)) (fun c =>
        G0RA Hb A ((((c.2.1.1, c.1.1.1, c.1.1.2), c.2.1.2), c.1.2), c.2.2)) :=
    (pr_equiv eqR0 (G0RA Hb A)).symm
  have e2 : pr ((XS × XR) × ShP R) (G1RA Hb A) =
      pr (((Coins refresherBytes × Coins uovM) × XR) × ((SimCoins2 pP × Tab3) × ShP R)) (fun c =>
        G1RA Hb A ((((c.2.1.1, c.1.1.1, c.1.1.2), c.2.1.2), c.1.2), c.2.2)) :=
    (pr_equiv eqS0 (G1RA Hb A)).symm
  rw [e1, e2]
  refine abs_pr_prod_sub_le _ _ fun ζ => ?_
  obtain ⟨⟨ref₀, r₀⟩, x₁⟩ := ζ
  have key := ZK2ARow.zk2A Hb (stOf ref₀) (toBA (List.ofFn r₀)) uovM (K0 Hb A ref₀ r₀ x₁)
    (hyp2RA_R hHb hI ref₀ r₀ x₁) hHb (smallParams_of_le (p := pP) (by decide) (by decide))
    (D0A Hb A ref₀ r₀ x₁) (budget_D0A hHb hA hI ref₀ r₀ x₁)
  have key' : |pr ((Bytes 16 × Tab3) × ShP R) (fun a => D0A Hb A ref₀ r₀ x₁
      (realRO2 Hb (stOf ref₀) (toBA (List.ofFn r₀)) (K0 Hb A ref₀ r₀ x₁ a.1.2) a.1.1 a.1.2 a.2)
      a.1.2 a.2) -
    pr ((SimCoins2 pP × Tab3) × ShP R) (fun a => D0A Hb A ref₀ r₀ x₁
      (simRO2 Hb (stOf ref₀) uovM (K0 Hb A ref₀ r₀ x₁ a.1.2) a.1.1 a.2) a.1.2
      (progRO2 Hb (stOf ref₀) uovM (K0 Hb A ref₀ r₀ x₁ a.1.2) a.1.1 a.2))| ≤
      ZKRow.εz R pP ((i3 + (i3 + q3)) + (i3 + i3)) ((i5 + 624 + (i5 + (q5 + 624))) + (i5 + 624 + i5))
        ((iE + 4607 + (iE + (qE + 4607))) + (iE + 4607 + iE)) := key
  refine le_of_eq_of_le (congrArg abs (congrArg₂ (· - ·) ?_ ?_)) key'
  · exact pr_congr fun a => G0RA_iff_D0A ref₀ r₀ x₁ a
  · exact pr_congr fun a => G1RA_iff_D0A hI ref₀ r₀ x₁ a

/-- **Hop 1** (`G1 → G2`): session `1` simulated, by `zk2_adaptive`, plus the collision term. -/
theorem hop1RA [ZKRow R] [ZK2ARow R] (hHb : HashesWF Hb) (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i5 iE) :
    |pr ((XS × XR) × ShP R) (G1RA Hb A) - pr ((XS × XS) × ShP R) (G2RA Hb A)| ≤
      ZKRow.εz R pP ((i3 + (i3 + q3)) + (i3 + i3)) ((i5 + (i5 + (q5 + 312))) + (i5 + i5))
        ((iE + 4607 + (iE + (qE + 13821))) + (iE + 4607 + iE)) + deltaRA Hb A := by
  have hδ := G1RA_G1'RA Hb A
  suffices h : |pr ((XS × XR) × ShP R) (G1'RA Hb A) - pr ((XS × XS) × ShP R) (G2RA Hb A)| ≤
      ZKRow.εz R pP ((i3 + (i3 + q3)) + (i3 + i3)) ((i5 + (i5 + (q5 + 312))) + (i5 + i5))
        ((iE + 4607 + (iE + (qE + 13821))) + (iE + 4607 + iE)) by
    have := abs_sub_le (pr ((XS × XR) × ShP R) (G1RA Hb A)) (pr ((XS × XR) × ShP R) (G1'RA Hb A))
      (pr ((XS × XS) × ShP R) (G2RA Hb A))
    linarith
  have e1 : pr ((XS × XR) × ShP R) (G1'RA Hb A) =
      pr ((XS × (Coins refresherBytes × Coins uovM)) × ((Bytes 16 × Tab3) × ShP R)) (fun c =>
        G1'RA Hb A ((c.1.1, ((c.2.1.1, c.1.2.1, c.1.2.2), c.2.1.2)), c.2.2)) :=
    (pr_equiv eqR1 (G1'RA Hb A)).symm
  have e2 : pr ((XS × XS) × ShP R) (G2RA Hb A) =
      pr ((XS × (Coins refresherBytes × Coins uovM)) × ((SimCoins2 pP × Tab3) × ShP R)) (fun c =>
        G2RA Hb A ((c.1.1, ((c.2.1.1, c.1.2.1, c.1.2.2), c.2.1.2)), c.2.2)) :=
    (pr_equiv eqS1 (G2RA Hb A)).symm
  rw [e1, e2]
  refine abs_pr_prod_sub_le _ _ fun ζ => ?_
  obtain ⟨y₀, ref₁, r₁⟩ := ζ
  have key := ZK2ARow.zk2A Hb (stOf ref₁) (toBA (List.ofFn r₁)) uovM (K1 Hb A ref₁ r₁ y₀)
    (hyp2RA_S hI ref₁ r₁ y₀) hHb (smallParams_of_le (p := pP) (by decide) (by decide))
    (D1A Hb A ref₁ r₁ y₀) (budget_D1A hA hI ref₁ r₁ y₀)
  have key' : |pr ((Bytes 16 × Tab3) × ShP R) (fun a => D1A Hb A ref₁ r₁ y₀
      (realRO2 Hb (stOf ref₁) (toBA (List.ofFn r₁)) (K1 Hb A ref₁ r₁ y₀ a.1.2) a.1.1 a.1.2 a.2)
      a.1.2 a.2) -
    pr ((SimCoins2 pP × Tab3) × ShP R) (fun a => D1A Hb A ref₁ r₁ y₀
      (simRO2 Hb (stOf ref₁) uovM (K1 Hb A ref₁ r₁ y₀ a.1.2) a.1.1 a.2) a.1.2
      (progRO2 Hb (stOf ref₁) uovM (K1 Hb A ref₁ r₁ y₀ a.1.2) a.1.1 a.2))| ≤
      ZKRow.εz R pP ((i3 + (i3 + q3)) + (i3 + i3)) ((i5 + (i5 + (q5 + 312))) + (i5 + i5))
        ((iE + 4607 + (iE + (qE + 13821))) + (iE + 4607 + iE)) := key
  refine le_of_eq_of_le (congrArg abs (congrArg₂ (· - ·) ?_ ?_)) key'
  · exact pr_congr fun a => G1'RA_iff_D1A y₀ ref₁ r₁ a
  · exact pr_congr fun a => G2RA_iff_D1A hI y₀ ref₁ r₁ a

end Hops

/-! ## `G2` for the Issuer and for the Issuer with the roles exchanged -/

section Swap

variable (Hb : Hashes) (A : AdversaryRA R)

/-- The re-parametrization of `G2`'s tape at the Issuer at the tables. -/
noncomputable def swapRA (A : AdversaryRA R) (z : (XS × XS) × ShP R) : (XS × XS) × ShP R :=
  swapS Hb (A.at (z.1.1.2, z.1.2.2) z.2) z

lemma swapRA_swapRA (A : AdversaryRA R) (z : (XS × XS) × ShP R) :
    swapRA Hb A.swap (swapRA Hb A z) = z := by
  have e : swapS Hb (A.swap.at ((swapRA Hb A z).1.1.2, (swapRA Hb A z).1.2.2) (swapRA Hb A z).2) =
      swapS Hb (A.at (z.1.1.2, z.1.2.2) z.2) := swapS_congr Hb rfl rfl
  unfold swapRA at e ⊢
  rw [e]
  exact swapS_involutive Hb _ z

lemma swapRA_swapRA' (A : AdversaryRA R) (z : (XS × XS) × ShP R) :
    swapRA Hb A (swapRA Hb A.swap z) = z := by
  have e : swapS Hb (A.at ((swapRA Hb A.swap z).1.1.2, (swapRA Hb A.swap z).1.2.2)
      (swapRA Hb A.swap z).2) = swapS Hb (A.swap.at (z.1.1.2, z.1.2.2) z.2) :=
    swapS_congr Hb rfl rfl
  unfold swapRA at e ⊢
  rw [e]
  exact swapS_involutive Hb _ z

/-- **`G2` is the same for the Issuer and for the Issuer with the roles exchanged.** -/
theorem G2RA_swap : pr ((XS × XS) × ShP R) (G2RA Hb A) = pr ((XS × XS) × ShP R) (G2RA Hb A.swap) := by
  let e : (XS × XS) × ShP R ≃ (XS × XS) × ShP R :=
    { toFun := swapRA Hb A
      invFun := swapRA Hb A.swap
      left_inv := swapRA_swapRA Hb A
      right_inv := swapRA_swapRA' Hb A }
  rw [← pr_equiv e (G2RA Hb A.swap)]
  refine pr_congr fun z => ?_
  show G2 Hb (A.at (z.1.1.2, z.1.2.2) z.2) z ↔
    G2 Hb (A.at (z.1.1.2, z.1.2.2) z.2).swap (swapS Hb (A.at (z.1.1.2, z.1.2.2) z.2) z)
  rw [G2_iff_G2c, G2_iff_G2c]
  exact (G2c_swap Hb _ z).symm

end Swap

/-! ## Blindness -/

section Blind

variable {Hb : Hashes}

/-- **The collision term**: `δ ≤ noHitProb + 2⁻¹²⁸` (`deltaRO_event'` at the Issuer at the
tables; session `1`'s prefix is computed from the Issuer at the tables and session `0`'s request,
neither of which reads session `0`'s `ã`). -/
theorem deltaRA_le (hHb : HashesWF Hb) (A : AdversaryRA R) :
    deltaRA Hb A ≤ noHitProb + 1 / 2 ^ 128 := by
  unfold deltaRA
  refine (pr_mono (Q := fun z => firstHit z.1.1.1.1.1.1.2.1 = none ∨
      preTail (blk (preLen pP) (pre1 (A.at (z.1.1.2, z.1.2.2) z.2) Hb z)) =
        ba z.1.1.1.1.1.2.2.2.2.2)
    fun z hz => ?_).trans ?_
  · obtain ⟨⟨y₀, x₁⟩, s⟩ := z
    exact deltaRO_event' _ hHb y₀ x₁ s hz
  refine pr_le_of_snd fun s => pr_le_of_snd fun x₁ => pr_le_of_snd fun g₀ =>
    pr_le_of_snd fun rr => pr_le_of_snd fun fb => ?_
  have h := pr_simCoins_tail_le (p := pP)
    (fun c => preTail (blk (preLen pP) (pre1 (A.at (g₀, x₁.2) s) Hb (((((c, fb), rr), g₀), x₁), s))))
    fun c a => by simp only [pre1, tS, s1S, s1C_tail]
  rw [tail_pP] at h
  exact h

/-- **The chain of world `false`**: `G0 → G1 → G2`. -/
theorem chain_falseRA [ZKRow R] [ZK2ARow R] (hHb : HashesWF Hb) {A : AdversaryRA R} {q3 q5 qE i3 i5 iE : ℕ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i5 iE) :
    |pr ((XR × XR) × ShP R) (G0RA Hb A) - pr ((XS × XS) × ShP R) (G2RA Hb A)| ≤
      ZKRow.εz R pP (q3 + 4 * i3) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) +
        (ZKRow.εz R pP (q3 + 4 * i3) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) + deltaRA Hb A) := by
  have h0 := hop0RA hHb hA hI
  have h1 := hop1RA hHb hA hI
  have m0 := ZKRow.εz_mono (R := R) pP (q3 := (i3 + (i3 + q3)) + (i3 + i3)) (q3' := q3 + 4 * i3)
    (q5 := (i5 + 624 + (i5 + (q5 + 624))) + (i5 + 624 + i5)) (q5' := q5 + 4 * i5 + 1872)
    (qE := (iE + 4607 + (iE + (qE + 4607))) + (iE + 4607 + iE)) (qE' := qE + 4 * iE + 23035)
    (by omega) (by omega) (by omega)
  have m1 := ZKRow.εz_mono (R := R) pP (q3 := (i3 + (i3 + q3)) + (i3 + i3)) (q3' := q3 + 4 * i3)
    (q5 := (i5 + (i5 + (q5 + 312))) + (i5 + i5)) (q5' := q5 + 4 * i5 + 1872)
    (qE := (iE + 4607 + (iE + (qE + 13821))) + (iE + 4607 + iE)) (qE' := qE + 4 * iE + 23035)
    (by omega) (by omega) (by omega)
  have := abs_sub_le (pr ((XR × XR) × ShP R) (G0RA Hb A)) (pr ((XS × XR) × ShP R) (G1RA Hb A))
    (pr ((XS × XS) × ShP R) (G2RA Hb A))
  linarith

/-- **PomFRIT blindness with an Issuer whose key, messages and responses read the tables**
(ROM and ideal cipher, label rows, the Lean prover on the shared tables; `hash_to_target`,
`XOF_seed` and the refresher commitment SHAKE): for every Issuer whose interaction reads at most
`(i₃, i₅, i_E)` keys per stage (no `H₂³`) and whose guess has budget `(q₃, q₅, q_E)`, the two
worlds differ by at most the four zero-knowledge errors and the two collision terms. -/
theorem blindnessRA [ZKRow R] [ZK2ARow R] (hHb : HashesWF Hb) (A : AdversaryRA R) {q3 q5 qE i3 i5 iE : ℕ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i5 iE) :
    |pr ((XR × XR) × ShP R) (realGameRA Hb A false) - pr ((XR × XR) × ShP R) (realGameRA Hb A true)| ≤
      4 * ZKRow.εz R pP (q3 + 4 * i3) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) + deltaRA Hb A +
        deltaRA Hb A.swap := by
  have h0 : pr ((XR × XR) × ShP R) (realGameRA Hb A false) = pr ((XR × XR) × ShP R) (G0RA Hb A) :=
    pr_congr (realGameRA_iff Hb A)
  have h1 : pr ((XR × XR) × ShP R) (realGameRA Hb A true) = pr ((XR × XR) × ShP R) (G0RA Hb A.swap) :=
    (pr_congr (realGameRA_true Hb A)).trans ((pr_equiv swapXR (realGameRA Hb A.swap false)).trans
      (pr_congr (realGameRA_iff Hb A.swap)))
  have c0 := chain_falseRA hHb hA hI
  have c1 := chain_falseRA hHb hA.swap hI.swap
  have hs := G2RA_swap Hb A
  rw [h0, h1]
  rw [hs] at c0
  have := abs_sub_le (pr ((XR × XR) × ShP R) (G0RA Hb A)) (pr ((XS × XS) × ShP R) (G2RA Hb A.swap))
    (pr ((XR × XR) × ShP R) (G0RA Hb A.swap))
  rw [abs_sub_comm (pr ((XS × XS) × ShP R) (G2RA Hb A.swap))] at this
  linarith

/-- **PomFRIT blindness with a table-reading Issuer, every term explicit, for every type of cipher
rows** (`ZKRow R`, `ZK2ARow R`; SHAKE as the base record):

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q₃ + 4i₃, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸. -/
theorem blindnessRA_lean_numG [ZKRow R] [ZK2ARow R] (A : AdversaryRA R) {q3 q5 qE i3 i5 iE : ℕ} (hA : A.GBudget q3 q5 qE)
    (hI : A.IBudget i3 i5 iE) :
    |pr ((XR × XR) × ShP R) (realGameRA Hashes.shake A false) -
        pr ((XR × XR) × ShP R) (realGameRA Hashes.shake A true)| ≤
      4 * ZKRow.εz R pP (q3 + 4 * i3) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 := by
  have h := blindnessRA hashesWF_shake A hA hI
  have d0 := deltaRA_le hashesWF_shake A
  have d1 := deltaRA_le hashesWF_shake A.swap
  have : (2 : ℝ) / 2 ^ 128 = 1 / 2 ^ 128 + 1 / 2 ^ 128 := by ring
  linarith

/-- **PomFRIT blindness with a table-reading Issuer, every term explicit** (SHAKE as the base
record; function rows):

    |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q₃ + 4i₃, q₅ + 4i₅ + 1872, q_E + 4i_E + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸. -/
theorem blindnessRA_lean_num (A : AdversaryRA (Blk → Blk)) {q3 q5 qE i3 i5 iE : ℕ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudget i3 i5 iE) :
    |pr ((XR × XR) × ShP (Blk → Blk)) (realGameRA Hashes.shake A false) -
        pr ((XR × XR) × ShP (Blk → Blk)) (realGameRA Hashes.shake A true)| ≤
      4 * εRO (q3 + 4 * i3) (q5 + 4 * i5 + 1872) (qE + 4 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 :=
  blindnessRA_lean_numG A hA hI

end Blind

end VoleMole.Privacy.PomFRIT
