import VoleMole.Privacy.PomFRITDelta
import VoleMole.ZK.SharedH3Two
import VoleMole.ZK.TwoPhasePerm

/-!
# PomFRIT blindness with one shared `H₃`

`Privacy/PomFRITRO.lean` gives each of the two sessions its own independent `H₃` slice. In the
scheme both sessions hash with one `H₃`, and a session's slice is `H₃` at its prefix: the witness
prefix `r` (PomFRIT's `WITNESS_PREFIX_BYTES = uov::M`, `pomfrit/redeem.hpp:103`) and the delayed
`μ₁` of the refresher commitment (`keyP`). Here the game is stated with one shared `H₃`
(`ZK/SharedH3.lean`: the shared tables carry `H₃`'s columns in their rows) and each session reads
its slice at its prefix (`realGameSh`). The Issuer of the shared model has the tables only: its
guess does not read the (unused) slot slices (`AdversaryRO.SliceFree`).

**No prefix-collision term.** The two sessions' prefixes coincide when their `r` and refresher
commitments do (`2⁻³⁶⁰`-type on paper). Nothing here needs them to differ. In hop 0 (session `0`
simulated) session `1` runs for real inside session `0`'s continuation (session `0`'s instance is
chosen after the Issuer saw both requests): with equal prefixes the continuation reads session
`0`'s own slice (at session `1`'s `ρ`). The slice-model proof uses two-phase zero knowledge for a
continuation that does not read the proof's slice (`ZK2Row`); here the adaptive version
(`ZK2ARow`, `zk2_adaptive`, whose continuation may read the slice) is used, through
`ZK.Sim.zk2_shared`, and the read costs one row in the error. Hop 1 (session `1` simulated) has a
continuation that reads only the simulated session `0`.

**The bound** (`blindnessSh_numG`, `blindnessSh_num`, `blindnessSh_num_perm`): for every Issuer with
budget `(q₃, q₅, q_E)` (the rows, cipher and `H₃` together, at `q_E` keys) whose guess ignores the
slot slices,

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q_E + 18428, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸,

`blindnessRO_lean_num`'s bound with `q₃` replaced by `q_E + 18428` (each row read is also a read
of the replaced session's slice).
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT

attribute [local irreducible] commitRefresher UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-! ## The model -/

section Model

variable (Hb : Hashes)

/-- **The prefix of a session** (its refresher and `r`): `r ‖ μ₁`, `μ₁` the delayed instance hash
of the step-1 statement. -/
noncomputable def keyP (c : Coins refresherBytes × Coins uovM) : Pre :=
  preKey ((toBA (List.ofFn c.2)).extract 0 (st1 (stOf c.1)).params.witnessBytes ++
    (st1 (stOf c.1)).mu1 Hb)

/-- The sessions' slices replaced by the shared `H₃` at their prefixes. -/
noncomputable def τR (z : (XR × XR) × ShP (RowH R)) : (XR × XR) × ShP (RowH R) :=
  (((z.1.1.1, h3At z.2 (keyP Hb z.1.1.1.2)), (z.1.2.1, h3At z.2 (keyP Hb z.1.2.1.2))), z.2)

/-- Session `1`'s slice replaced by the shared `H₃` at its prefix. -/
noncomputable def τ1 (z : (XS × XR) × ShP (RowH R)) : (XS × XR) × ShP (RowH R) :=
  ((z.1.1, (z.1.2.1, h3At z.2 (keyP Hb z.1.2.1.2))), z.2)

/-- **An Issuer of the shared model**: its guess does not read the slot slices (it has the
tables, `H₃` included, and nothing else). -/
def AdversaryRO.SliceFree (A : AdversaryRO R) : Prop :=
  ∀ t₀ t₁ y sl sl' s, A.guess t₀ t₁ y sl s ↔ A.guess t₀ t₁ y sl' s

lemma AdversaryRO.SliceFree.swap {A : AdversaryRO R} (h : A.SliceFree) : A.swap.SliceFree :=
  fun t₀ t₁ y sl sl' s => h t₁ t₀ y (sl.2, sl.1) (sl'.2, sl'.1) s

/-- **The real game with one shared `H₃`**: the spec's protocol, both sessions with the Lean prover
on the shared tables, each session's `H₃` slice the shared `H₃` at its prefix. -/
noncomputable def realGameSh (A : AdversaryRO (RowH R)) (b : Bool) (z : (XR × XR) × ShP (RowH R)) :
    Prop :=
  viewS A b (realSession Layout.labelRows (leanProverRO Hb (h3At z.2 (keyP Hb z.1.1.1.2)) z.2) A.pk
      (A.msg b) z.1.1.1)
    (realSession Layout.labelRows (leanProverRO Hb (h3At z.2 (keyP Hb z.1.2.1.2)) z.2) A.pk
      (A.msg !b) z.1.2.1)
    (z.1.1.2, z.1.2.2) z.2

variable {Hb}

lemma realGameSh_iff {A : AdversaryRO (RowH R)} (hF : A.SliceFree) (b : Bool)
    (z : (XR × XR) × ShP (RowH R)) : realGameSh Hb A b z ↔ realGameRO Hb A b (τR Hb z) :=
  hF _ _ _ _ _ _

end Model

/-! ## The two-phase runs read their continuation only at the tables they run on -/

section Cont

variable {R' : Type} [CipherRow R'] (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ)

lemma realRO2_cont {K K' : ShG R' st.params → Cont2} (ρ : Bytes 16) (G3 : Tab3) (s : ShG R' st.params)
    (h : K s = K' s) : realRO2 Hb st r K ρ G3 s = realRO2 Hb st r K' ρ G3 s := by
  unfold realRO2
  rw [h]

lemma simRO2_cont {K K' : ShG R' st.params → Cont2} (c : SimCoins2 st.params) (s : ShG R' st.params)
    (h : K s = K' s) : simRO2 Hb st n K c s = simRO2 Hb st n K' c s := by
  unfold simRO2
  rw [h]

lemma progRO2_cont {K K' : ShG R' st.params → Cont2} (c : SimCoins2 st.params) (s : ShG R' st.params)
    (h : K s = K' s) : progRO2 Hb st n K c s = progRO2 Hb st n K' c s := by
  unfold progRO2
  rw [simRO2_cont Hb st n c s h, h]

end Cont

section SetK

variable (Hb : Hashes) (A : AdversaryRO (RowH R))

lemma tS_setK (msg : Bytes) (y : XS) (s : ShP (RowH R)) (k : Pre) (g : Tab3) :
    tS Hb A msg y (setK s k g) = tS Hb A msg y s := by
  simp only [tS, s1S, s1C]
  rw [rowFn_setK]

lemma tR_setK (msg : Bytes) (x : XR) (s : ShP (RowH R)) (k : Pre) (g : Tab3) :
    tR Hb A msg x (setK s k g) = tR Hb A msg x s := by
  simp only [tR, s1R, setK_fst, setK_snd_fst]
  rw [rowFn_setK]

lemma oR_setK (msg : Bytes) (i : Bool) (x : XR) (t' : ShP (RowH R) → Bytes) (s : ShP (RowH R))
    (k : Pre) (g : Tab3) :
    oR Hb A msg i x t' (setK s k g) = oR Hb A msg i x (fun s' => t' (setK s' k g)) s :=
  realRO2_setK Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2))
    (fun s => kOf A msg x.1.2.1 x.1.2.2 i (t' s)) x.1.1 x.2 s k g

lemma pS_setK (msg : Bytes) (i : Bool) (y : XS) (t' : ShP (RowH R) → Bytes) (s : ShP (RowH R))
    (k : Pre) (g : Tab3) :
    pS Hb A msg i y t' (setK s k g) = setK (pS Hb A msg i y (fun s' => t' (setK s' k g)) s) k g :=
  progRO2_setK Hb (stOf y.1.2.1) uovM (fun s => kOf A msg y.1.2.1 y.1.2.2 i (t' s)) y.1.1 s k g

end SetK

/-! ## Hop 0: session `0` simulated -/

section Hop0

variable {Hb : Hashes} {A : AdversaryRO (RowH R)}

/-- `D0` with session `1`'s slice the shared `H₃` at its prefix. -/
noncomputable def D0s (Hb : Hashes) (A : AdversaryRO (RowH R)) (ref₀ : Coins refresherBytes)
    (r₀ : Coins uovM) (x₁ : XR) (o : Out2) (g : Tab3) (s : ShP (RowH R)) : Prop :=
  D0 Hb A ref₀ r₀ (x₁.1, h3At s (keyP Hb x₁.1.2)) o g s

/-- The continuation of session `0` with session `1` real on the shared `H₃`. -/
noncomputable def K0s (Hb : Hashes) (A : AdversaryRO (RowH R)) (ref₀ : Coins refresherBytes)
    (r₀ : Coins uovM) (x₁ : XR) (s : ShP (RowH R)) : Cont2 :=
  kOf A (A.msg false) ref₀ r₀ false (tR Hb A (A.msg true) (x₁.1, h3At s (keyP Hb x₁.1.2)) s)

lemma s1R_g3 (x : Coins proveSeedBytes × Coins refresherBytes × Coins uovM) {G G' : Tab3}
    (s : ShP (RowH R)) (h : G x.1 = G' x.1) : s1R Hb (x, G) s = s1R Hb (x, G') s := by
  unfold s1R
  rw [step1_g3_congr' (Hb := Hb) (st := stOf x.2.1) (r := toBA (List.ofFn x.2.2)) x.1 s h]

lemma oR_g3 (msg : Bytes) (i : Bool) (x : Coins proveSeedBytes × Coins refresherBytes × Coins uovM)
    {G G' : Tab3} (t' : ShP (RowH R) → Bytes) (s : ShP (RowH R)) (h : G x.1 = G' x.1) :
    oR Hb A msg i (x, G) t' s = oR Hb A msg i (x, G') t' s :=
  realRO2_g3_congr' (Hb := Hb) (st := stOf x.2.1) (r := toBA (List.ofFn x.2.2))
    (fun s => kOf A msg x.2.1 x.2.2 i (t' s)) x.1 s h

lemma K0s_h5 (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR) :
    Rd5 (K0s Hb A ref₀ r₀ x₁) 624 :=
  rd5_h3At (fun G => (s1R_rd5 Hb (x₁.1, G)).map fun o =>
    kOf A (A.msg false) ref₀ r₀ false (tOf A (A.msg true) x₁.1.2.1 x₁.1.2.2 o)) (keyP Hb x₁.1.2)

lemma K0s_hE (hHb : HashesWF Hb) (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR) :
    RdE (K0s Hb A ref₀ r₀ x₁) (4607 + 1) :=
  rdE_h3At x₁.1.1 (fun G G' s h => by
      show kOf A (A.msg false) ref₀ r₀ false (tOf A (A.msg true) x₁.1.2.1 x₁.1.2.2 (s1R Hb (x₁.1, G) s)) =
        kOf A (A.msg false) ref₀ r₀ false (tOf A (A.msg true) x₁.1.2.1 x₁.1.2.2 (s1R Hb (x₁.1, G') s))
      rw [s1R_g3 x₁.1 s h])
    (fun G => (s1R_rdE Hb hHb (x₁.1, G)).map fun o =>
      kOf A (A.msg false) ref₀ r₀ false (tOf A (A.msg true) x₁.1.2.1 x₁.1.2.2 o)) (keyP Hb x₁.1.2)

lemma D0s_free (hF : A.SliceFree) (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR)
    (o : Out2) (g g' : Tab3) (s : ShP (RowH R)) : D0s Hb A ref₀ r₀ x₁ o g s ↔ D0s Hb A ref₀ r₀ x₁ o g' s :=
  hF _ _ _ _ _ _

/-- `D0s`'s budget: `D0`'s, session `1`'s slice read through one row. -/
theorem budget_D0s (hHb : HashesWF Hb) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) (hF : A.SliceFree)
    (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR) :
    Budget pP 0 (q5 + 624) (qE + 4607 + 1) (D0s Hb A ref₀ r₀ x₁) where
  h3 o s := ⟨fun _ => ∅, fun _ => by simp, fun g g' _ =>
    propext (D0s_free hF ref₀ r₀ x₁ o g' g s)⟩
  h5 o g := rd5_h3At (f := fun G s => D0 Hb A ref₀ r₀ (x₁.1, G) o g s)
    (fun G => (budget_D0 hHb hA ref₀ r₀ (x₁.1, G)).h5 o g) (keyP Hb x₁.1.2)
  hE o g := rdE_h3At (f := fun G s => D0 Hb A ref₀ r₀ (x₁.1, G) o g s) x₁.1.1
    (fun G G' s h => by
      have e := oR_g3 (Hb := Hb) (A := A) (A.msg true) true x₁.1
        (fun _ => tOf A (A.msg false) ref₀ r₀ (o.1, o.2.1)) s h
      apply propext
      show view2 A false _ _ o _ (g, G) s ↔ view2 A false _ _ o _ (g, G') s
      rw [e]
      exact hF _ _ _ _ _ _)
    (fun G => (budget_D0 hHb hA ref₀ r₀ (x₁.1, G)).hE o g) (keyP Hb x₁.1.2)

/-- **Hop 0 with one shared `H₃`** (`G0 → G1`, both on the shared `H₃`): `ZK.Sim.zk2_shared` for
session `0`, whose continuation runs session `1` for real on the shared `H₃` (reading session
`0`'s own column when the prefixes coincide). -/
theorem hop0Sh [ZKRow R] [ZK2ARow R] (hHb : HashesWF Hb) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE)
    (hF : A.SliceFree) :
    |pr ((XR × XR) × ShP (RowH R)) (fun z => G0 Hb A (τR Hb z)) -
        pr ((XS × XR) × ShP (RowH R)) (fun z => G1 Hb A (τ1 Hb z))| ≤
      ZKRow.εz R pP ((qE + 4607 + 1) + (4607 + 1)) ((q5 + 624) + 624) ((qE + 4607 + 1) + (4607 + 1)) := by
  rw [← pr_equiv (eqR0 (R := RowH R)), ← pr_equiv (eqS0 (R := RowH R))]
  refine abs_pr_prod_sub_le _ _ fun ζ => ?_
  obtain ⟨⟨ref₀, r₀⟩, x₁⟩ := ζ
  have key := zk2_shared Hb (stOf ref₀) (toBA (List.ofFn r₀)) uovM (keyP Hb (ref₀, r₀))
    (K0s Hb A ref₀ r₀ x₁) (fun _ => hyp2_kOf A (A.msg false) ref₀ r₀ false _)
    (by rw [size_toBA, List.length_ofFn])
    (fun s G2 => (hyp2RO_R Hb A hHb (A.msg false) (A.msg true) ref₀ r₀ false
      (x₁.1, h3At s (keyP Hb x₁.1.2))).h2 s G2)
    (K0s_h5 ref₀ r₀ x₁) (K0s_hE hHb ref₀ r₀ x₁) hHb
    (smallParams_of_le (p := pP) (by decide) (by decide)) (D0s Hb A ref₀ r₀ x₁)
    (budget_D0s hHb hA hF ref₀ r₀ x₁)
  refine le_of_eq_of_le (congrArg abs (congrArg₂ (· - ·) ?_ ?_)) key
  · refine pr_congr fun a => ?_
    have e := realRO2_cont Hb (stOf ref₀) (toBA (List.ofFn r₀)) a.1.1 (h3At a.2 (keyP Hb (ref₀, r₀))) a.2
      (K := fun s => kOf A (A.msg false) ref₀ r₀ false
        (tR Hb A (A.msg true) (x₁.1, h3At a.2 (keyP Hb x₁.1.2)) s)) (K' := K0s Hb A ref₀ r₀ x₁) rfl
    refine (G0_iff_D0 Hb A ref₀ r₀ (x₁.1, h3At a.2 (keyP Hb x₁.1.2))
      ((a.1.1, h3At a.2 (keyP Hb (ref₀, r₀))), a.2)).trans ?_
    refine (Iff.of_eq (congrArg (fun o => D0 Hb A ref₀ r₀ (x₁.1, h3At a.2 (keyP Hb x₁.1.2)) o
      (h3At a.2 (keyP Hb (ref₀, r₀))) a.2) e)).trans ?_
    exact D0s_free hF ref₀ r₀ x₁ _ _ _ _
  · refine pr_congr fun a => ?_
    have e1 := simRO2_cont Hb (stOf ref₀) uovM a.1.1 a.2
      (K := fun s => kOf A (A.msg false) ref₀ r₀ false
        (tR Hb A (A.msg true) (x₁.1, h3At a.2 (keyP Hb x₁.1.2)) s)) (K' := K0s Hb A ref₀ r₀ x₁) rfl
    have e2 := progRO2_cont Hb (stOf ref₀) uovM a.1.1 a.2
      (K := fun s => kOf A (A.msg false) ref₀ r₀ false
        (tR Hb A (A.msg true) (x₁.1, h3At a.2 (keyP Hb x₁.1.2)) s)) (K' := K0s Hb A ref₀ r₀ x₁) rfl
    have e3 : h3At (progRO2 Hb (stOf ref₀) uovM (K0s Hb A ref₀ r₀ x₁) a.1.1 a.2) (keyP Hb x₁.1.2) =
        h3At a.2 (keyP Hb x₁.1.2) := h3At_progRO2 _ _ _ _ _ _ _
    refine (G1_iff_D0 Hb A ref₀ r₀ (x₁.1, h3At a.2 (keyP Hb x₁.1.2)) a).trans ?_
    refine (Iff.of_eq (congrArg₂ (fun o v => D0 Hb A ref₀ r₀ (x₁.1, h3At a.2 (keyP Hb x₁.1.2)) o
      a.1.2 v) e1 e2)).trans ?_
    exact Iff.of_eq (congrArg (fun G => D0 Hb A ref₀ r₀ (x₁.1, G)
      (simRO2 Hb (stOf ref₀) uovM (K0s Hb A ref₀ r₀ x₁) a.1.1 a.2) a.1.2
      (progRO2 Hb (stOf ref₀) uovM (K0s Hb A ref₀ r₀ x₁) a.1.1 a.2)) e3.symm)

end Hop0

/-! ## Hop 1: session `1` simulated -/

section Hop1

variable {Hb : Hashes} {A : AdversaryRO (RowH R)}

/-- **`G1` and the reduction's real side agree unless session `1` reads a programmed point**
(pointwise; `G1_G1'`'s argument). -/
theorem G1_iff_G1' (z : (XS × XR) × ShP (RowH R))
    (hz : oR Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1)
        (pS Hb A (A.msg false) false z.1.1 (tR Hb A (A.msg true) z.1.2) z.2) =
      oR Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1) z.2) :
    G1 Hb A z ↔ G1' Hb A z := by
  obtain ⟨⟨y₀, x₁⟩, s⟩ := z
  dsimp only at hz
  set v := pS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s with hv
  set o := oR Hb A (A.msg true) true x₁ (tS Hb A (A.msg false) y₀) s with ho
  have ho1 : (o.1, o.2.1) = s1R Hb x₁ s := oR_s1 Hb A _ _ _ _ _
  have hvs : v.2.2 = s.2.2 := rfl
  have h1 : oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s =
      oS Hb A (A.msg false) false y₀ (fun _ => tOf A (A.msg true) x₁.1.2.1 x₁.1.2.2 (o.1, o.2.1)) s :=
    oS_cont Hb A _ _ _ s (by rw [ho1]; rfl)
  have h2 : v = pS Hb A (A.msg false) false y₀
      (fun _ => tOf A (A.msg true) x₁.1.2.1 x₁.1.2.2 (o.1, o.2.1)) s :=
    pS_cont Hb A _ _ _ s (by rw [ho1]; rfl)
  have h3 : oR Hb A (A.msg true) true x₁ (fun _ => tOf A (A.msg false) y₀.1.2.1 y₀.1.2.2
      ((oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s).1,
       (oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s).2.1)) v = o := by
    have hc : tOf A (A.msg false) y₀.1.2.1 y₀.1.2.2
        ((oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s).1,
         (oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s).2.1) =
        tS Hb A (A.msg false) y₀ v := by
      rw [oS_s1, tS, s1S_eq Hb y₀ s v hvs]
    rw [oR_cont Hb A (A.msg true) true x₁ v (t₁ := fun _ => tOf A (A.msg false) y₀.1.2.1 y₀.1.2.2
      ((oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s).1,
       (oS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s).2.1))
      (t₂ := tS Hb A (A.msg false) y₀) hc, ← hz]
  show G1 Hb A ((y₀, x₁), s) ↔ G1' Hb A ((y₀, x₁), s)
  unfold G1 G1' D1
  dsimp only
  rw [← hv, h3, h1, ← h2]

/-- **The collision term with one shared `H₃` is the slice model's** (`ZK.Sim.pr_h3At_slice`). -/
theorem deltaRO_sh :
    pr ((XS × XR) × ShP (RowH R)) (fun z =>
      oR Hb A (A.msg true) true (τ1 Hb z).1.2 (tS Hb A (A.msg false) (τ1 Hb z).1.1)
          (pS Hb A (A.msg false) false (τ1 Hb z).1.1 (tR Hb A (A.msg true) (τ1 Hb z).1.2) z.2) ≠
        oR Hb A (A.msg true) true (τ1 Hb z).1.2 (tS Hb A (A.msg false) (τ1 Hb z).1.1) z.2) =
      deltaRO Hb A := by
  unfold deltaRO
  rw [← pr_equiv (eqR1 (R := RowH R)), ← pr_equiv (eqR1 (R := RowH R))]
  exact pr_h3At_slice (R := R) (Γ := XS × (Coins refresherBytes × Coins uovM)) (ρT := Bytes 16)
    (p := pP) (fun γ => keyP Hb γ.2)
    (fun γ ρ G s => oR Hb A (A.msg true) true ((ρ, γ.2), G) (tS Hb A (A.msg false) γ.1)
        (pS Hb A (A.msg false) false γ.1 (tR Hb A (A.msg true) ((ρ, γ.2), G)) s) ≠
      oR Hb A (A.msg true) true ((ρ, γ.2), G) (tS Hb A (A.msg false) γ.1) s)
    fun γ ρ G s k g => by
      simp only [pS_setK, oR_setK, tS_setK, tR_setK]

lemma D1_free (hF : A.SliceFree) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (y₀ : XS)
    (o : Out2) (g g' : Tab3) (s : ShP (RowH R)) : D1 Hb A ref₁ r₁ y₀ o g s ↔ D1 Hb A ref₁ r₁ y₀ o g' s :=
  hF _ _ _ _ _ _

/-- **Hop 1 with one shared `H₃`** (`G1 → G2`): `ZK.Sim.zk2_shared` for session `1`, plus the
collision term. -/
theorem hop1Sh [ZKRow R] [ZK2ARow R] (hHb : HashesWF Hb) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE)
    (hF : A.SliceFree) :
    |pr ((XS × XR) × ShP (RowH R)) (fun z => G1 Hb A (τ1 Hb z)) -
        pr ((XS × XS) × ShP (RowH R)) (G2 Hb A)| ≤
      ZKRow.εz R pP ((qE + 13821) + 4607) ((q5 + 312) + 0) ((qE + 13821) + 4607) + deltaRO Hb A := by
  have hδ : |pr ((XS × XR) × ShP (RowH R)) (fun z => G1 Hb A (τ1 Hb z)) -
      pr ((XS × XR) × ShP (RowH R)) (fun z => G1' Hb A (τ1 Hb z))| ≤ deltaRO Hb A := by
    rw [← deltaRO_sh]
    exact abs_pr_sub_le_of_agree _ _ _ fun z hz => G1_iff_G1' (τ1 Hb z) (not_not.1 hz)
  suffices h : |pr ((XS × XR) × ShP (RowH R)) (fun z => G1' Hb A (τ1 Hb z)) -
      pr ((XS × XS) × ShP (RowH R)) (G2 Hb A)| ≤
      ZKRow.εz R pP ((qE + 13821) + 4607) ((q5 + 312) + 0) ((qE + 13821) + 4607) by
    have := abs_sub_le (pr ((XS × XR) × ShP (RowH R)) (fun z => G1 Hb A (τ1 Hb z)))
      (pr ((XS × XR) × ShP (RowH R)) (fun z => G1' Hb A (τ1 Hb z)))
      (pr ((XS × XS) × ShP (RowH R)) (G2 Hb A))
    linarith
  rw [← pr_equiv (eqR1 (R := RowH R)), ← pr_equiv (eqS1 (R := RowH R))]
  refine abs_pr_prod_sub_le _ _ fun ζ => ?_
  obtain ⟨y₀, ref₁, r₁⟩ := ζ
  have hK := hyp2RO_S (R := RowH R) Hb A (A.msg true) (A.msg false) ref₁ r₁ true y₀
  have key := zk2_shared Hb (stOf ref₁) (toBA (List.ofFn r₁)) uovM (keyP Hb (ref₁, r₁))
    (fun s => kOf A (A.msg true) ref₁ r₁ true (tS Hb A (A.msg false) y₀ s)) hK.hyp hK.size hK.h2
    hK.h5 hK.hE hHb (smallParams_of_le (p := pP) (by decide) (by decide)) (D1 Hb A ref₁ r₁ y₀)
    (budget_D1 hA ref₁ r₁ y₀)
  refine le_of_eq_of_le (congrArg abs (congrArg₂ (· - ·) ?_ ?_)) key
  · refine pr_congr fun a => ?_
    show D1 Hb A ref₁ r₁ y₀ (realRO2 Hb (stOf ref₁) (toBA (List.ofFn r₁))
      (fun s => kOf A (A.msg true) ref₁ r₁ true (tS Hb A (A.msg false) y₀ s)) a.1.1
      (h3At a.2 (keyP Hb (ref₁, r₁))) a.2) (h3At a.2 (keyP Hb (ref₁, r₁))) a.2 ↔ _
    exact D1_free hF ref₁ r₁ y₀ _ _ _ _
  · exact pr_congr fun a => G2_iff_D1 Hb A y₀ ref₁ r₁ a

end Hop1

/-! ## Blindness -/

section Blind

variable {Hb : Hashes} [ZKRow R] [ZK2ARow R]

/-- **PomFRIT blindness with one shared `H₃`, for any base record**: the two worlds differ by at
most the four zero-knowledge errors and the two worlds' collision terms. -/
theorem blindnessSh (hHb : HashesWF Hb) (A : AdversaryRO (RowH R)) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (hF : A.SliceFree) :
    |pr ((XR × XR) × ShP (RowH R)) (realGameSh Hb A false) -
        pr ((XR × XR) × ShP (RowH R)) (realGameSh Hb A true)| ≤
      2 * (ZKRow.εz R pP ((qE + 4607 + 1) + (4607 + 1)) ((q5 + 624) + 624)
          ((qE + 4607 + 1) + (4607 + 1)) +
        ZKRow.εz R pP ((qE + 13821) + 4607) ((q5 + 312) + 0) ((qE + 13821) + 4607)) +
        deltaRO Hb A + deltaRO Hb A.swap := by
  have g0 : ∀ {B : AdversaryRO (RowH R)}, B.SliceFree →
      pr ((XR × XR) × ShP (RowH R)) (realGameSh Hb B false) =
        pr ((XR × XR) × ShP (RowH R)) (fun z => G0 Hb B (τR Hb z)) := fun hB =>
    pr_congr fun z => (realGameSh_iff hB false z).trans (realGameRO_iff Hb _ _)
  have h1 : pr ((XR × XR) × ShP (RowH R)) (realGameSh Hb A true) =
      pr ((XR × XR) × ShP (RowH R)) (realGameSh Hb A.swap false) := by
    rw [← pr_equiv swapXR (realGameSh Hb A.swap false)]
    refine pr_congr fun z => ?_
    rw [realGameSh_iff hF, realGameRO_true, realGameSh_iff hF.swap]
    exact Iff.rfl
  have c0 := (abs_sub_le _ _ _).trans (add_le_add (hop0Sh hHb hA hF) (hop1Sh hHb hA hF))
  have c1 := (abs_sub_le _ _ _).trans (add_le_add (hop0Sh hHb hA.swap hF.swap)
    (hop1Sh hHb hA.swap hF.swap))
  have hs := G2_swap Hb A
  rw [h1, g0 hF, g0 hF.swap]
  rw [hs] at c0
  have := abs_sub_le (pr ((XR × XR) × ShP (RowH R)) (fun z => G0 Hb A (τR Hb z)))
    (pr ((XS × XS) × ShP (RowH R)) (G2 Hb A.swap))
    (pr ((XR × XR) × ShP (RowH R)) (fun z => G0 Hb A.swap (τR Hb z)))
  rw [abs_sub_comm (pr ((XS × XS) × ShP (RowH R)) (G2 Hb A.swap))] at this
  linarith

/-- **PomFRIT blindness with one shared `H₃`, every term explicit, for every type of cipher rows**
(`ZKRow R`, `ZK2ARow R`; SHAKE for the other hashes): for every Issuer with budget
`(q₃, q₅, q_E)` whose guess does not read the slot slices,

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q_E + 18428, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸,

with no term for sessions whose prefixes coincide. -/
theorem blindnessSh_numG (A : AdversaryRO (RowH R)) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE)
    (hF : A.SliceFree) :
    |pr ((XR × XR) × ShP (RowH R)) (realGameSh Hashes.shake A false) -
        pr ((XR × XR) × ShP (RowH R)) (realGameSh Hashes.shake A true)| ≤
      4 * ZKRow.εz R pP (qE + 18428) (q5 + 1248) (qE + 18428) + 2 * noHitProb + 2 / 2 ^ 128 := by
  have h := blindnessSh hashesWF_shake A hA hF
  have e1 : ZKRow.εz R pP ((qE + 4607 + 1) + (4607 + 1)) ((q5 + 624) + 624)
      ((qE + 4607 + 1) + (4607 + 1)) ≤ ZKRow.εz R pP (qE + 18428) (q5 + 1248) (qE + 18428) :=
    ZKRow.εz_mono pP (by omega) (by omega) (by omega)
  have e2 : ZKRow.εz R pP ((qE + 13821) + 4607) ((q5 + 312) + 0) ((qE + 13821) + 4607) ≤
      ZKRow.εz R pP (qE + 18428) (q5 + 1248) (qE + 18428) :=
    ZKRow.εz_mono pP (by omega) (by omega) (by omega)
  have d0 := deltaRO_le (R := RowH R) A hashesWF_shake
  have d1 := deltaRO_le (R := RowH R) A.swap hashesWF_shake
  refine h.trans ?_
  linarith

/-- **PomFRIT blindness with one shared `H₃`, function rows**:

    |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q_E + 18428, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸. -/
theorem blindnessSh_num (A : AdversaryRO (RowH (Blk → Blk))) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (hF : A.SliceFree) :
    |pr ((XR × XR) × ShP (RowH (Blk → Blk))) (realGameSh Hashes.shake A false) -
        pr ((XR × XR) × ShP (RowH (Blk → Blk))) (realGameSh Hashes.shake A true)| ≤
      4 * εRO (qE + 18428) (q5 + 1248) (qE + 18428) + 2 * noHitProb + 2 / 2 ^ 128 :=
  blindnessSh_numG A hA hF

/-- **PomFRIT blindness with one shared `H₃`, AES as uniformly random permutations**:

    |Pr[W₀] − Pr[W₁]| ≤ 4·εROPm(pP; q_E + 18428, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸. -/
theorem blindnessSh_num_perm (A : AdversaryRO (RowH (Equiv.Perm Blk))) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (hF : A.SliceFree) :
    |pr ((XR × XR) × ShP (RowH (Equiv.Perm Blk))) (realGameSh Hashes.shake A false) -
        pr ((XR × XR) × ShP (RowH (Equiv.Perm Blk))) (realGameSh Hashes.shake A true)| ≤
      4 * εROPm pP (qE + 18428) (q5 + 1248) (qE + 18428) + 2 * noHitProb + 2 / 2 ^ 128 :=
  blindnessSh_numG A hA hF

end Blind

end VoleMole.Privacy.PomFRIT
