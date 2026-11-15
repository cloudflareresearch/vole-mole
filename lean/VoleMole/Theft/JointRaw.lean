import VoleMole.Theft.JointZK
import VoleMole.ZK.ChainExp

/-!
# The joint step with the hop's charge taken where the one-proof theorem takes it

`real_sim_leN_jointZK` (`Theft/JointZK.lean`) asks, for hop `i`, for an error `ε + E[Y]` with the
expectation in **hybrid `i`**: slot `i`'s real proof made on the tables the earlier simulations
programmed (`viewN`). The one-proof theorem with expected charges (`ZK.Sim.zk_ro_exp`) gives the
expectation in **its** real world: the proof made on the unprogrammed tables `s`, the
distinguisher (`distN`) reading the programmed ones. The two differ only when the proof reads the
tables differently with and without the programming, which is the collision event `deltaN i`
that the hop already pays. So the hop with the charge in the zero-knowledge theorem's world costs
`(1 + B)·Pr[deltaN i]` instead of `Pr[deltaN i]`, `B` a bound on the charge:

* **`contView`**: the view of the rest of the game after slot `i` (`contN`'s arguments), and
  `viewN_update` (hybrid `i`'s view with slot `i` set);
* **`exU_slot_real`**: an expectation over a slot that does not read the simulator coins;
* **`hyb_hop_expRaw`**: one hop, the charge in the zero-knowledge theorem's real world;
* **`real_sim_leN_jointRaw`**: the joint bound

      |Pr_real[Ev] − Pr_sim[Ev]| ≤ (Σ_i (ε_i + (1 + B)·Pr[deltaN i]) + J) / (1 − N·B),

  with `J` bounding `Σ_i E_sim[Y_i]` (the fully simulated game).
-/

open Finset

namespace VoleMole.Theft

open VoleMole.Privacy

section Many

variable {Ω O ρ C G S : Type*}
  (P : Ω → List O → ρ → G → S → O) (Sm : Ω → List O → C → O) (pg : Ω → List O → C → S → S)
  {N : ℕ} [Nonempty ρ] [Nonempty C] [Nonempty G]

/-- **The view of the rest of the game after slot `i`**, given that slot's output `o`, its private
table `g` and the tables `u` the game runs on: what `contN` reads. -/
noncomputable def contView (i : Fin N) (ω : Ω) (τ : Fin N → Slot ρ C G) (o : O) (g : G) (u : S) :
    Ω × List O × (Fin N → G) × S :=
  (ω, realFrom P ω (tapeR τ) u ((simPre Sm pg ω (tapeC τ) i).1 ++ [o]) (i.val + 1)
      (N - (i.val + 1)), Function.update (tapeG τ) i g, u)

/-- `contN` is an event of `contView`. -/
lemma contN_view (Ev : Ω → List O → (Fin N → G) → S → Prop) (i : Fin N) (ω : Ω)
    (τ : Fin N → Slot ρ C G) (o : O) (g : G) (u : S) :
    contN P Sm pg Ev i ω τ o g u ↔ Ev (contView P Sm pg i ω τ o g u).1
      (contView P Sm pg i ω τ o g u).2.1 (contView P Sm pg i ω τ o g u).2.2.1
      (contView P Sm pg i ω τ o g u).2.2.2 := Iff.rfl

/-- **Hybrid `i`'s view with slot `i` set to `t`**: the real proof of slot `i` on the programmed
tables, then the rest. -/
theorem viewN_update (i : Fin N) (ω : Ω) (τ : Fin N → Slot ρ C G) (t : Slot ρ C G) (s : S) :
    viewN P Sm pg i ((ω, Function.update τ i t), s) =
      contView P Sm pg i ω τ
        (P ω (simPre Sm pg ω (tapeC τ) i).1 t.1.1 t.2 ((simPre Sm pg ω (tapeC τ) i).2 s)) t.2
        ((simPre Sm pg ω (tapeC τ) i).2 s) := by
  have hN : N - i.val = (N - (i.val + 1)) + 1 := by have := i.isLt; omega
  simp only [viewN, contView]
  rw [simPre_update, hN, realFrom, tapeR_update_self, tapeG_update,
    realFrom_congr P _ _ (i.val + 1) fun k hk => tapeR_update_ne τ i t (by omega)]

omit [Nonempty ρ] [Nonempty G] in
/-- **An expectation over a slot that does not read the simulator coins.** -/
lemma exU_slot_real [Fintype ρ] [Fintype C] [Fintype G] [Fintype S] (f : ρ → G → S → ℝ) :
    exU (Slot ρ C G × S) (fun a => f a.1.1.1 a.1.2 a.2) =
      exU ((ρ × G) × S) (fun a => f a.1.1 a.1.2 a.2) := by
  let e : C × ((ρ × G) × S) ≃ Slot ρ C G × S :=
    { toFun := fun y => (((y.2.1.1, y.1), y.2.1.2), y.2.2)
      invFun := fun a => (a.1.1.2, ((a.1.1.1, a.1.2), a.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : exU (Slot ρ C G × S) (fun a => f a.1.1.1 a.1.2 a.2) =
      exU (C × ((ρ × G) × S)) (fun y => f y.2.1.1 y.2.1.2 y.2.2) :=
    (ZK.IC.exP_equiv e (fun a : Slot ρ C G × S => f a.1.1.1 a.1.2 a.2)).symm
  rw [h1]
  show ZK.IC.exP _ _ = ZK.IC.exP _ _
  rw [ZK.IC.exP_prod]
  dsimp only
  exact ZK.IC.exP_const (α := C) _

variable [Fintype Ω] [Nonempty Ω] [Fintype ρ] [Fintype C] [Fintype G] [Fintype S] [Nonempty S]

/-- **One hop, with the charge in the zero-knowledge theorem's real world.** If for every rest of
the tape the real proof of slot `i` (on the unprogrammed tables `s`) and its simulation are
`ε + E[Y]`-close through the hop's distinguisher, `E[Y]` the expectation over the proof's coins and
the tables of `Y` read on the rest of the game after the real proof made on `s`, with `Y ∈ [0, B]`,
then hybrids `i` and `i + 1` are `ε + (1 + B)·Pr[deltaN i] + E_i[Y]`-close. -/
theorem hyb_hop_expRaw (Ev : Ω → List O → (Fin N → G) → S → Prop) (i : Fin N) {ε B : ℝ}
    (Y : Ω × List O × (Fin N → G) × S → ℝ) (hY0 : ∀ v, 0 ≤ Y v) (hYB : ∀ v, Y v ≤ B)
    (h : ∀ ω τ, |pr ((ρ × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) a.1.2 a.2) -
        pr ((C × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (Sm ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1) a.1.2
          (pg ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.2))| ≤
        ε + exU ((ρ × G) × S) (fun a => Y (contView P Sm pg i ω τ
          (P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) a.1.2
          ((simPre Sm pg ω (tapeC τ) i).2 a.2)))) :
    |pr _ (hyb P Sm pg N i Ev) - pr _ (hyb P Sm pg N (i.val + 1) Ev)| ≤
      ε + (1 + B) * pr _ (deltaN P Sm pg i) + exU _ (fun z => Y (viewN (C := C) P Sm pg i z)) := by
  classical
  set Γ := Ω × (Fin N → Slot ρ C G)
  -- the raw and the hybrid charge, and the bad event, per rest of the tape
  let L : Γ → S → S := fun γ => (simPre Sm pg γ.1 (tapeC γ.2) i).2
  let hs : Γ → List O := fun γ => (simPre Sm pg γ.1 (tapeC γ.2) i).1
  let raw : Γ → (ρ × G) × S → ℝ := fun γ a =>
    Y (contView P Sm pg i γ.1 γ.2 (P γ.1 (hs γ) a.1.1 a.1.2 a.2) a.1.2 (L γ a.2))
  let hy : Γ → (ρ × G) × S → ℝ := fun γ a =>
    Y (contView P Sm pg i γ.1 γ.2 (P γ.1 (hs γ) a.1.1 a.1.2 (L γ a.2)) a.1.2 (L γ a.2))
  let bad : Γ → (ρ × G) × S → ℝ := fun γ a =>
    if P γ.1 (hs γ) a.1.1 a.1.2 (L γ a.2) ≠ P γ.1 (hs γ) a.1.1 a.1.2 a.2 then 1 else 0
  have hpt : ∀ γ a, raw γ a ≤ hy γ a + B * bad γ a := by
    intro γ a
    simp only [bad]
    split_ifs with hb
    · rw [mul_one]
      exact (hYB _).trans (le_add_of_nonneg_left (hY0 _))
    · rw [mul_zero, add_zero]
      simp only [raw, hy, not_not.1 hb]
      exact le_rfl
  have hB : 0 ≤ B := (hY0 (Classical.arbitrary _)).trans (hYB _)
  -- the hybrid charge averaged is hybrid `i`'s expectation
  have ehy : exU Γ (fun γ => exU ((ρ × G) × S) (hy γ)) =
      exU _ (fun z => Y (viewN (C := C) P Sm pg i z)) := by
    rw [← exU_slot i (fun z => Y (viewN (C := C) P Sm pg i z))]
    refine congrArg (exU Γ) (funext fun γ => ?_)
    have e1 := exU_slot_real (C := C) (fun r g s => Y (contView P Sm pg i γ.1 γ.2
      (P γ.1 (hs γ) r g (L γ s)) g (L γ s)))
    rw [← e1]
    refine congrArg (exU _) (funext fun a => ?_)
    rw [viewN_update]
  -- the bad event averaged is `Pr[deltaN i]`
  have ebad : exU Γ (fun γ => exU ((ρ × G) × S) (bad γ)) = pr _ (deltaN P Sm pg i) := by
    rw [pr_eq_exU, ← exU_slot i]
    refine congrArg (exU Γ) (funext fun γ => ?_)
    have e1 := exU_slot_real (C := C) (fun r g s =>
      if P γ.1 (hs γ) r g (L γ s) ≠ P γ.1 (hs γ) r g s then (1 : ℝ) else 0)
    rw [← e1]
    refine congrArg (exU _) (funext fun a => ?_)
    simp only [deltaN, simPre_update, tapeR_update_self, hs, L]
  have hraw : exU Γ (fun γ => exU ((ρ × G) × S) (raw γ)) ≤
      exU _ (fun z => Y (viewN (C := C) P Sm pg i z)) + B * pr _ (deltaN P Sm pg i) := by
    rw [← ehy, ← ebad]
    show ZK.IC.exP _ _ ≤ ZK.IC.exP _ _ + B * ZK.IC.exP _ _
    rw [← ZK.IC.exP_mul_left, ← ZK.IC.exP_add]
    refine ZK.IC.exP_mono fun γ => ?_
    show ZK.IC.exP _ _ ≤ ZK.IC.exP _ _ + B * ZK.IC.exP _ _
    rw [← ZK.IC.exP_mul_left, ← ZK.IC.exP_add]
    exact ZK.IC.exP_mono fun a => hpt γ a
  have h1 := hyb_hop_avg P Sm pg Ev i (fun ω τ => ε + exU ((ρ × G) × S) (raw (ω, τ)))
    (fun ω τ => h ω τ)
  have e2 : exU Γ (fun γ => ε + exU ((ρ × G) × S) (raw (γ.1, γ.2))) =
      ε + exU Γ (fun γ => exU ((ρ × G) × S) (raw γ)) := exU_const_add ε _
  rw [e2] at h1
  have hd0 : 0 ≤ pr _ (deltaN P Sm pg i) := pr_nonneg _
  nlinarith

/-- **The joint bound with the hops' charges in the zero-knowledge theorem's world**: if every
hop's real proof (on the unprogrammed tables) and its simulation are `ε i + E[Y i]`-close through
the hop's distinguisher (`hyb_hop_expRaw`), for every event and every rest of the tape, with
`Y i ∈ [0, B]`, and the charges sum to at most `J` in the simulated game, then for every event

    |Pr_real[Ev] − Pr_sim[Ev]| ≤ (Σ_i (ε i + (1 + B)·Pr[deltaN i]) + J) / (1 − N·B). -/
theorem real_sim_leN_jointRaw (ε : ℕ → ℝ) (Y : ℕ → Ω × List O × (Fin N → G) × S → ℝ) {B J : ℝ}
    (hY0 : ∀ i v, 0 ≤ Y i v) (hYB : ∀ i < N, ∀ v, Y i v ≤ B)
    (h : ∀ (i : Fin N) (Ev : Ω → List O → (Fin N → G) → S → Prop) ω τ,
      |pr ((ρ × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) a.1.2 a.2) -
        pr ((C × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (Sm ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1) a.1.2
          (pg ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.2))| ≤
        ε i + exU ((ρ × G) × S) (fun a => Y i (contView P Sm pg i ω τ
          (P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) a.1.2
          ((simPre Sm pg ω (tapeC τ) i).2 a.2))))
    (hJ : ∑ i ∈ range N, exU _ (fun z => Y i (viewN (C := C) P Sm pg N z)) ≤ J)
    (hNB : N * B < 1) (Ev : Ω → List O → (Fin N → G) → S → Prop) :
    |pr _ (realGN (C := C) P Ev) - pr _ (simGN (ρ := ρ) Sm pg Ev)| ≤
      (∑ i : Fin N, (ε i + (1 + B) * pr _ (deltaN P Sm pg i)) + J) / (1 - N * B) := by
  let c : ℕ → ℝ := fun i =>
    if hi : i < N then ε i + (1 + B) * pr _ (deltaN P Sm pg ⟨i, hi⟩) else 0
  have hc : ∑ i : Fin N, (ε i + (1 + B) * pr _ (deltaN P Sm pg i)) = ∑ i ∈ range N, c i := by
    rw [← Fin.sum_univ_eq_sum_range c N]
    exact Finset.sum_congr rfl fun i _ => by simp only [c, i.isLt, ↓reduceDIte]
  rw [hc]
  refine real_sim_leN_joint P Sm pg c Y hY0 hYB (fun i hi Ev' => ?_) hJ hNB Ev
  have := hyb_hop_expRaw P Sm pg Ev' ⟨i, hi⟩ (Y i) (hY0 i) (hYB i hi) (h ⟨i, hi⟩ Ev')
  simp only [c, hi, ↓reduceDIte]
  linarith

end Many

end VoleMole.Theft
