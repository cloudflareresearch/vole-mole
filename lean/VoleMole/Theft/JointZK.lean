import VoleMole.Theft.Many

/-!
# A many-proof zero-knowledge step that charges the adversary's budget once

`Theft/Many.lean` replaces the `N` honest proofs one at a time (`hyb_hop`, `real_sim_leN`). Hop
`i` uses the one-proof zero-knowledge theorem as a black box: its distinguisher (the rest of the
game, adversary included) has the adversary's whole budget, so every hop pays the budget terms
`(q₃ + q₅ + 221·q_E)·2⁻¹²⁸` again and the bound is `N` times them. No bound on the hops one at a
time can do better: one proof's zero-knowledge error is at least of order `q_E·2⁻¹²⁸` (guess a
hidden node's key, expand it at the proof's CTR inputs and compare with the opened seeds), and
each hop's distinguisher may spend all its queries on that hop's proof.

What can do better is to charge each hop only the reads that concern its proof, **in
expectation** over the hybrid. If hop `i` costs `c i + E_i[Y i]`, with `Y i ≥ 0` a function of the
hybrid's view (for the cipher, the weighted number of the distinguisher's reads at the points of
proof `i`: keys of any value, inputs on the CTR blocks of proof `i`'s `iv`), the expectations are
taken in different hybrids, but the hybrids are close, and the error closes on itself:

    S := Σ_i (c i + E_i[Y i]) ≤ Σ_i c i + Σ_i E_N[Y i] + N·B·S,

with `B` a bound on every `Y i` (`exU_sub_le`: `|E_i f − E_N f| ≤ B·TV(i, N) ≤ B·S`). Hence, if
`Σ_i E_N[Y i] ≤ J` (in one world, the fully simulated one, every read is charged to the proofs it
concerns, so `J` is the adversary's budget term **once**, times the largest number of proofs that
share a read) and `N·B < 1`:

    |Pr_real − Pr_sim| ≤ (Σ_i c i + J) / (1 − N·B).

At the theft games' numbers (`N ≤ 2³¹`, `B ≈ 223·2⁻⁶³`, so `N·B ≈ 2⁻²⁴`) the denominator costs a
factor `1 + 2⁻²³`.

* **`exU`**, **`exU_sub_le`**: expectations under a uniform tape; bounded functions through two
  maps that are `δ`-close on every event.
* **`joint_le`**: the self-bounding composition for worlds `t 0, …, t N` on one tape.
* **`viewN`**, **`real_sim_leN_joint`**: the same for the hybrids of `Theft/Many.lean`.
* **`hyb_hop_avg`**, **`exU_slot`**, **`hyb_hop_exp`**, **`real_sim_leN_jointZK`**: the hop's
  hypothesis per rest of the tape (as in `hyb_hop`), with an error `ε + E[Y i]`, the expectation
  over the hop's slot and tables of `Y i` read on hybrid `i`'s view.

**What is not proved.** The hypothesis of `real_sim_leN_jointZK`, one-proof zero knowledge with an
error linear in the **expected** number of the distinguisher's reads **at the proof's points**,
is not the zero-knowledge theorem of `ZK/` (`ZKRow.zk`, `zk_ro`): that one charges every read of
a hidden node's **row** (key-level, `IC.puncture`), counted by a **worst-case** budget (`RdE`).
At key level the joint charge cannot help: an adversary's read at a random key hits a hidden
key of one of the `N` proofs with probability `221·N·2⁻¹²⁸`, so the key-level bad event has
probability `≈ 221·N·q_E·2⁻¹²⁸`, the bound of `Theft/Many.lean`. See
`lean/docs/security/ratatouille.md` §5.
-/

open Finset

namespace VoleMole.Theft

open VoleMole.Privacy

/-! ## Expectations under a uniform tape -/

section Exp

variable {Z V : Type*} [Fintype Z]

/-- **The expectation of `f` under the uniform distribution on `Z`.** -/
noncomputable def exU (Z : Type*) [Fintype Z] (f : Z → ℝ) : ℝ :=
  (∑ z, f z) / Fintype.card Z

lemma exU_nonneg {f : Z → ℝ} (hf : ∀ z, 0 ≤ f z) : 0 ≤ exU Z f :=
  div_nonneg (Finset.sum_nonneg fun z _ => hf z) (Nat.cast_nonneg _)

lemma exU_le {f : Z → ℝ} {B : ℝ} (hB : 0 ≤ B) (hf : ∀ z, f z ≤ B) : exU Z f ≤ B := by
  unfold exU
  rcases Nat.eq_zero_or_pos (Fintype.card Z) with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]; exact hB
  · have hc : (0 : ℝ) < Fintype.card Z := by exact_mod_cast hpos
    rw [div_le_iff₀ hc]
    calc ∑ z, f z ≤ ∑ _z : Z, B := Finset.sum_le_sum fun z _ => hf z
      _ = B * Fintype.card Z := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- A probability is the expectation of the indicator. -/
lemma pr_eq_exU (P : Z → Prop) [DecidablePred P] :
    pr Z P = exU Z (fun z => if P z then 1 else 0) := by
  rw [pr_def, exU, Finset.sum_boole]

/-- A sum through a map is a sum over its values, weighted by the fibres. -/
lemma sum_comp_fibre [DecidableEq V] (t : Z → V) (W : Finset V) (hW : ∀ z, t z ∈ W)
    (g : V → ℝ) :
    ∑ z, g (t z) = ∑ v ∈ W, (#{z | t z = v} : ℝ) * g v := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := W) (g := t) (fun z _ => hW z)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g v) fun z hz => by rw [(Finset.mem_filter.1 hz).2],
    Finset.sum_const, nsmul_eq_mul]

/-- **Bounded functions through close maps.** If every event has probability at most `δ` more
through `ta` than through `tb`, a function with values in `[0, B]` has expectation at most `B·δ`
more. -/
theorem exU_sub_le [Nonempty Z] (ta tb : Z → V) (f : V → ℝ) {B δ : ℝ} (hf0 : ∀ v, 0 ≤ f v)
    (hfB : ∀ v, f v ≤ B)
    (hδ : ∀ F : V → Prop, pr Z (fun z => F (ta z)) - pr Z (fun z => F (tb z)) ≤ δ) :
    exU Z (fun z => f (ta z)) - exU Z (fun z => f (tb z)) ≤ B * δ := by
  classical
  have hc : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  let W : Finset V := univ.image ta ∪ univ.image tb
  have hWa : ∀ z, ta z ∈ W := fun z => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (mem_univ z))
  have hWb : ∀ z, tb z ∈ W := fun z => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (mem_univ z))
  let na : V → ℝ := fun v => (#{z | ta z = v} : ℝ)
  let nb : V → ℝ := fun v => (#{z | tb z = v} : ℝ)
  let pos : V → Prop := fun v => nb v < na v
  have hpos := hδ pos
  rw [pr_eq_exU, pr_eq_exU] at hpos
  unfold exU at hpos ⊢
  rw [← sub_div, div_le_iff₀ hc] at hpos ⊢
  beta_reduce at hpos ⊢
  rw [sum_comp_fibre ta W hWa (fun v => if pos v then (1 : ℝ) else 0),
    sum_comp_fibre tb W hWb (fun v => if pos v then (1 : ℝ) else 0)] at hpos
  rw [sum_comp_fibre ta W hWa f, sum_comp_fibre tb W hWb f]
  rw [← Finset.sum_sub_distrib] at hpos ⊢
  have hB : 0 ≤ B := (hf0 (ta (Classical.arbitrary Z))).trans (hfB _)
  have hterm : ∀ v ∈ W, na v * f v - nb v * f v ≤
      B * (na v * (if pos v then 1 else 0) - nb v * (if pos v then 1 else 0)) := by
    intro v _
    by_cases hv : pos v
    · simp only [hv, ↓reduceIte, mul_one]
      have : (na v - nb v) * f v ≤ (na v - nb v) * B :=
        mul_le_mul_of_nonneg_left (hfB v) (by simp only [pos] at hv; linarith)
      linarith
    · simp only [hv, ↓reduceIte, mul_zero, sub_zero]
      have hle : na v ≤ nb v := not_lt.1 hv
      have : (na v - nb v) * f v ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (hf0 v)
      linarith
  calc ∑ v ∈ W, (na v * f v - nb v * f v)
      ≤ ∑ v ∈ W, B * (na v * (if pos v then 1 else 0) - nb v * (if pos v then 1 else 0)) :=
        Finset.sum_le_sum hterm
    _ = B * ∑ v ∈ W, (na v * (if pos v then 1 else 0) - nb v * (if pos v then 1 else 0)) := by
        rw [Finset.mul_sum]
    _ ≤ B * (δ * Fintype.card Z) := mul_le_mul_of_nonneg_left hpos hB
    _ = B * δ * Fintype.card Z := by ring

end Exp

/-! ## The self-bounding composition -/

section Joint

variable {Z V : Type*} [Fintype Z] [Nonempty Z]

/-- **The joint hybrid.** Worlds `t 0, …, t N` on one uniform tape; hop `i` costs `c i` plus the
expectation, in world `i`, of a function `Y i ∈ [0, B]` of the world's value, for every event. If
in the last world the expectations sum to at most `J` and `N·B < 1`:

    |Pr_0[F] − Pr_N[F]| ≤ (Σ_i c i + J) / (1 − N·B). -/
theorem joint_le {N : ℕ} (t : ℕ → Z → V) (c : ℕ → ℝ) (Y : ℕ → V → ℝ) {B J : ℝ}
    (hY0 : ∀ i v, 0 ≤ Y i v) (hYB : ∀ i < N, ∀ v, Y i v ≤ B)
    (hop : ∀ i < N, ∀ F : V → Prop,
      |pr Z (fun z => F (t i z)) - pr Z (fun z => F (t (i + 1) z))| ≤
        c i + exU Z (fun z => Y i (t i z)))
    (hJ : ∑ i ∈ range N, exU Z (fun z => Y i (t N z)) ≤ J) (hNB : N * B < 1) (F : V → Prop) :
    |pr Z (fun z => F (t 0 z)) - pr Z (fun z => F (t N z))| ≤
      (∑ i ∈ range N, c i + J) / (1 - N * B) := by
  set D : ℕ → ℝ := fun i => c i + exU Z (fun z => Y i (t i z)) with hDdef
  set S := ∑ i ∈ range N, D i with hSdef
  have hD0 : ∀ i < N, 0 ≤ D i := fun i hi => (abs_nonneg _).trans (hop i hi fun _ => True)
  -- the distance from world `N − k` to world `N`
  have tele : ∀ k ≤ N, ∀ F : V → Prop,
      |pr Z (fun z => F (t (N - k) z)) - pr Z (fun z => F (t N z))| ≤
        ∑ j ∈ Ico (N - k) N, D j := by
    intro k
    induction k with
    | zero => intro _ F; simp
    | succ k ih =>
      intro hk F
      have hi : N - (k + 1) < N := by omega
      have e : N - (k + 1) + 1 = N - k := by omega
      have h1 := hop (N - (k + 1)) hi F
      rw [e] at h1
      have h2 := ih (by omega) F
      have h3 := abs_sub_le (pr Z (fun z => F (t (N - (k + 1)) z)))
        (pr Z (fun z => F (t (N - k) z))) (pr Z (fun z => F (t N z)))
      rw [Finset.sum_eq_sum_Ico_succ_bot hi, e]
      linarith
  have TV : ∀ i ≤ N, ∀ F : V → Prop,
      |pr Z (fun z => F (t i z)) - pr Z (fun z => F (t N z))| ≤ S := by
    intro i hi F
    have h := tele (N - i) (by omega) F
    rw [show N - (N - i) = i by omega] at h
    refine h.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j hj _ => hD0 j ?_)
    · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
    · simpa using hj
  have hE : ∀ i < N, exU Z (fun z => Y i (t i z)) ≤ exU Z (fun z => Y i (t N z)) + B * S := by
    intro i hi
    have := exU_sub_le (t i) (t N) (Y i) (hY0 i) (hYB i hi)
      fun F => (le_abs_self _).trans (TV i hi.le F)
    linarith
  have hS : S ≤ ∑ i ∈ range N, c i + J + N * B * S := by
    have h1 : S = ∑ i ∈ range N, c i + ∑ i ∈ range N, exU Z (fun z => Y i (t i z)) := by
      rw [hSdef, hDdef, Finset.sum_add_distrib]
    have h2 : ∑ i ∈ range N, exU Z (fun z => Y i (t i z)) ≤
        ∑ i ∈ range N, (exU Z (fun z => Y i (t N z)) + B * S) :=
      Finset.sum_le_sum fun i hi => hE i (Finset.mem_range.1 hi)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    rw [h1]
    nlinarith
  have hden : 0 < 1 - N * B := by linarith
  have hS' : S ≤ (∑ i ∈ range N, c i + J) / (1 - N * B) := by
    rw [le_div_iff₀ hden]; nlinarith
  have h0 := TV 0 (Nat.zero_le _) F
  exact h0.trans hS'

end Joint

/-! ## The hybrids of `Theft/Many.lean` -/

section Many

variable {Ω O ρ C G S : Type*}
  (P : Ω → List O → ρ → G → S → O) (Sm : Ω → List O → C → O) (pg : Ω → List O → C → S → S)
  {N : ℕ} [Nonempty ρ] [Nonempty C] [Nonempty G]

/-- **The view of hybrid `i`**: what its event reads (`hyb`). -/
noncomputable def viewN (i : ℕ) (z : (Ω × (Fin N → Slot ρ C G)) × S) :
    Ω × List O × (Fin N → G) × S :=
  (z.1.1, realFrom P z.1.1 (tapeR z.1.2) ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2 z.2)
      (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 i (N - i),
    tapeG z.1.2, (simPre Sm pg z.1.1 (tapeC z.1.2) i).2 z.2)

/-- Hybrid `i`'s event is read on its view. -/
lemma hyb_viewN (i : ℕ) (Ev : Ω → List O → (Fin N → G) → S → Prop)
    (z : (Ω × (Fin N → Slot ρ C G)) × S) :
    hyb P Sm pg N i Ev z ↔ Ev (viewN (C := C) P Sm pg i z).1 (viewN (C := C) P Sm pg i z).2.1
      (viewN (C := C) P Sm pg i z).2.2.1 (viewN (C := C) P Sm pg i z).2.2.2 := Iff.rfl

variable [Fintype Ω] [Nonempty Ω] [Fintype ρ] [Fintype C] [Fintype G] [Fintype S] [Nonempty S]

/-- **The joint bound on the hybrids of `Theft/Many.lean`**: if hop `i` costs `c i` plus the
expectation in hybrid `i` of `Y i ∈ [0, B]` read on its view, for every event, then for every
event `Ev`

    |Pr_real[Ev] − Pr_sim[Ev]| ≤ (Σ_i c i + J) / (1 − N·B),

`J` bounding `Σ_i E_sim[Y i]` (the fully simulated game). -/
theorem real_sim_leN_joint (c : ℕ → ℝ) (Y : ℕ → Ω × List O × (Fin N → G) × S → ℝ) {B J : ℝ}
    (hY0 : ∀ i v, 0 ≤ Y i v) (hYB : ∀ i < N, ∀ v, Y i v ≤ B)
    (hop : ∀ i < N, ∀ Ev : Ω → List O → (Fin N → G) → S → Prop,
      |pr _ (hyb P Sm pg N i Ev) - pr _ (hyb P Sm pg N (i + 1) Ev)| ≤
        c i + exU _ (fun z => Y i (viewN (C := C) P Sm pg i z)))
    (hJ : ∑ i ∈ range N, exU _ (fun z => Y i (viewN (C := C) P Sm pg N z)) ≤ J)
    (hNB : N * B < 1) (Ev : Ω → List O → (Fin N → G) → S → Prop) :
    |pr _ (realGN (C := C) P Ev) - pr _ (simGN (ρ := ρ) Sm pg Ev)| ≤
      (∑ i ∈ range N, c i + J) / (1 - N * B) := by
  rw [← hyb_zero P Sm pg Ev, ← hyb_last P Sm pg Ev]
  have h := joint_le (Z := (Ω × (Fin N → Slot ρ C G)) × S) (t := fun i z => viewN P Sm pg i z)
    c Y hY0 hYB (fun i hi F => hop i hi fun ω l g s => F (ω, l, g, s)) hJ hNB
    (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2)
  exact h

omit [Nonempty S] in
/-- **One hop, with an error that depends on the rest of the tape**: `hyb_hop` with `η ω τ` in
place of a constant, averaged. -/
theorem hyb_hop_avg (Ev : Ω → List O → (Fin N → G) → S → Prop) (i : Fin N)
    (η : Ω → (Fin N → Slot ρ C G) → ℝ)
    (h : ∀ ω τ, |pr ((ρ × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) a.1.2 a.2) -
        pr ((C × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (Sm ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1) a.1.2
          (pg ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.2))| ≤ η ω τ) :
    |pr _ (hyb P Sm pg N i Ev) - pr _ (hyb P Sm pg N (i.val + 1) Ev)| ≤
      exU (Ω × (Fin N → Slot ρ C G)) (fun γ => η γ.1 γ.2) + pr _ (deltaN P Sm pg i) := by
  let A : (Ω × (Fin N → Slot ρ C G)) × (Slot ρ C G × S) → Prop := fun z =>
    contN P Sm pg Ev i z.1.1 z.1.2
      (P z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 z.2.1.1.1 z.2.1.2
        ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2 z.2.2)) z.2.1.2
      ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2 z.2.2)
  let A' : (Ω × (Fin N → Slot ρ C G)) × (Slot ρ C G × S) → Prop := fun z =>
    contN P Sm pg Ev i z.1.1 z.1.2
      (P z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 z.2.1.1.1 z.2.1.2 z.2.2) z.2.1.2
      ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2 z.2.2)
  let B : (Ω × (Fin N → Slot ρ C G)) × (Slot ρ C G × S) → Prop := fun z =>
    contN P Sm pg Ev i z.1.1 z.1.2 (Sm z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 z.2.1.1.2)
      z.2.1.2 ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2
        (pg z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 z.2.1.1.2 z.2.2))
  let bad : (Ω × (Fin N → Slot ρ C G)) × (Slot ρ C G × S) → Prop := fun z =>
    P z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 z.2.1.1.1 z.2.1.2
        ((simPre Sm pg z.1.1 (tapeC z.1.2) i).2 z.2.2) ≠
      P z.1.1 (simPre Sm pg z.1.1 (tapeC z.1.2) i).1 z.2.1.1.1 z.2.1.2 z.2.2
  have eA : pr _ (hyb P Sm pg N i Ev) = pr _ A := by
    rw [← pr_slot i (hyb P Sm pg N i Ev)]
    exact pr_congr fun z => hyb_update_real P Sm pg Ev i z.1.1 z.1.2 z.2.1 z.2.2
  have eB : pr _ (hyb P Sm pg N (i.val + 1) Ev) = pr _ B := by
    rw [← pr_slot i (hyb P Sm pg N (i.val + 1) Ev)]
    exact pr_congr fun z => hyb_update_sim P Sm pg Ev i z.1.1 z.1.2 z.2.1 z.2.2
  have ebad : pr _ (deltaN P Sm pg i) = pr _ bad := by
    rw [← pr_slot i (deltaN P Sm pg i)]
    refine pr_congr fun z => ?_
    simp only [deltaN, bad, simPre_update, tapeR_update_self]
  have h1 : |pr _ A - pr _ A'| ≤ pr _ bad :=
    abs_pr_sub_le_of_agree A A' bad fun z hz => by
      simp only [A, A', bad] at hz ⊢
      rw [not_not.1 hz]
  have h2 : |pr _ A' - pr _ B| ≤ exU (Ω × (Fin N → Slot ρ C G)) (fun γ => η γ.1 γ.2) := by
    have hα : (0 : ℝ) < Fintype.card (Ω × (Fin N → Slot ρ C G)) := by
      exact_mod_cast Fintype.card_pos
    rw [pr_prod, pr_prod, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hα, exU]
    gcongr
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun γ _ => ?_)
    have e1 := pr_slot_real (C := C) (fun r g s => contN P Sm pg Ev i γ.1 γ.2
      (P γ.1 (simPre Sm pg γ.1 (tapeC γ.2) i).1 r g s) g ((simPre Sm pg γ.1 (tapeC γ.2) i).2 s))
    have e2 := pr_slot_sim (ρ := ρ) (fun c g s => contN P Sm pg Ev i γ.1 γ.2
      (Sm γ.1 (simPre Sm pg γ.1 (tapeC γ.2) i).1 c) g
      ((simPre Sm pg γ.1 (tapeC γ.2) i).2 (pg γ.1 (simPre Sm pg γ.1 (tapeC γ.2) i).1 c s)))
    simp only [A', B]
    rw [e1, e2]
    exact h γ.1 γ.2
  rw [eA, eB, ebad]
  have := abs_sub_le (pr _ A) (pr _ A') (pr _ B)
  linarith

/-- **Averaging over a resampled slot**: the expectation over the rest of the tape of the
expectation over slot `i` and the tables is the expectation over the whole tape. -/
lemma exU_slot (i : Fin N) (f : (Ω × (Fin N → Slot ρ C G)) × S → ℝ) :
    exU (Ω × (Fin N → Slot ρ C G))
        (fun γ => exU (Slot ρ C G × S) (fun a => f ((γ.1, Function.update γ.2 i a.1), a.2))) =
      exU ((Ω × (Fin N → Slot ρ C G)) × S) f := by
  let e : (Ω × (Fin N → Slot ρ C G)) × (Slot ρ C G × S) ≃
      Slot ρ C G × ((Ω × (Fin N → Slot ρ C G)) × S) :=
    { toFun := fun z => (z.1.2 i, ((z.1.1, Function.update z.1.2 i z.2.1), z.2.2))
      invFun := fun y => ((y.2.1.1, Function.update y.2.1.2 i y.1), (y.2.1.2 i, y.2.2))
      left_inv := fun z => by simp
      right_inv := fun y => by simp }
  have hsum : ∑ γ : Ω × (Fin N → Slot ρ C G), ∑ a : Slot ρ C G × S,
      f ((γ.1, Function.update γ.2 i a.1), a.2) = Fintype.card (Slot ρ C G) * ∑ w, f w := by
    rw [← Fintype.sum_prod_type', ← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (g := fun _ => ∑ w, f w) fun s _ =>
      Finset.sum_congr rfl fun w _ => by simp [e]]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [exU]
  rw [← Finset.sum_div, hsum, Fintype.card_prod (Slot ρ C G) S,
    Fintype.card_prod (Ω × (Fin N → Slot ρ C G)) S, Nat.cast_mul, Nat.cast_mul]
  have h1 : (0 : ℝ) < Fintype.card (Slot ρ C G) := by exact_mod_cast Fintype.card_pos
  have h2 : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have h3 : (0 : ℝ) < Fintype.card (Ω × (Fin N → Slot ρ C G)) := by
    exact_mod_cast Fintype.card_pos
  field_simp

omit [Nonempty S] in
lemma exU_const_add {Z : Type*} [Fintype Z] [Nonempty Z] (ε : ℝ) (g : Z → ℝ) :
    exU Z (fun z => ε + g z) = ε + exU Z g := by
  have hc : (Fintype.card Z : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [exU]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_div,
    mul_div_cancel_left₀ _ hc]

/-- **One hop, with an error linear in an expected charge**: if slot `i`'s real proof and its
simulation are `ε + E[Y]`-close through the hop's distinguisher, for every rest of the tape, with
`E[Y]` the expectation over slot `i` and the tables of `Y` read on hybrid `i`'s view, then
hybrids `i` and `i + 1` are `ε + Pr[deltaN i] + E_i[Y]`-close. -/
theorem hyb_hop_exp (Ev : Ω → List O → (Fin N → G) → S → Prop) (i : Fin N) {ε : ℝ}
    (Y : Ω × List O × (Fin N → G) × S → ℝ)
    (h : ∀ ω τ, |pr ((ρ × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) a.1.2 a.2) -
        pr ((C × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (Sm ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1) a.1.2
          (pg ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.2))| ≤
        ε + exU (Slot ρ C G × S)
          (fun a => Y (viewN P Sm pg i ((ω, Function.update τ i a.1), a.2)))) :
    |pr _ (hyb P Sm pg N i Ev) - pr _ (hyb P Sm pg N (i.val + 1) Ev)| ≤
      ε + pr _ (deltaN P Sm pg i) + exU _ (fun z => Y (viewN (C := C) P Sm pg i z)) := by
  have h1 := hyb_hop_avg P Sm pg Ev i _ h
  rw [exU_const_add, exU_slot i (fun z => Y (viewN P Sm pg i z))] at h1
  linarith

/-- **The joint many-proof bound from per-proof zero knowledge with expected charges**: if every
hop's real proof and simulation are `ε i + E[Y i]`-close through the hop's distinguisher, for every
event and every rest of the tape (`hyb_hop_exp`), with `Y i ∈ [0, B]` read on hybrid `i`'s view,
and the charges sum to at most `J` in the simulated game, then for every event `Ev`

    |Pr_real[Ev] − Pr_sim[Ev]| ≤ (Σ_i (ε i + Pr[deltaN i]) + J) / (1 − N·B).

Against `real_sim_leN`'s `Σ_i (ε_i + Pr[deltaN i])`, the budget terms are in `J`, once. -/
theorem real_sim_leN_jointZK (ε : ℕ → ℝ) (Y : ℕ → Ω × List O × (Fin N → G) × S → ℝ) {B J : ℝ}
    (hY0 : ∀ i v, 0 ≤ Y i v) (hYB : ∀ i < N, ∀ v, Y i v ≤ B)
    (h : ∀ (i : Fin N) (Ev : Ω → List O → (Fin N → G) → S → Prop) ω τ,
      |pr ((ρ × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) a.1.2 a.2) -
        pr ((C × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (Sm ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1) a.1.2
          (pg ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.2))| ≤
        ε i + exU (Slot ρ C G × S)
          (fun a => Y i (viewN P Sm pg i ((ω, Function.update τ i a.1), a.2))))
    (hJ : ∑ i ∈ range N, exU _ (fun z => Y i (viewN (C := C) P Sm pg N z)) ≤ J)
    (hNB : N * B < 1) (Ev : Ω → List O → (Fin N → G) → S → Prop) :
    |pr _ (realGN (C := C) P Ev) - pr _ (simGN (ρ := ρ) Sm pg Ev)| ≤
      (∑ i : Fin N, (ε i + pr _ (deltaN P Sm pg i)) + J) / (1 - N * B) := by
  let c : ℕ → ℝ := fun i => if hi : i < N then ε i + pr _ (deltaN P Sm pg ⟨i, hi⟩) else 0
  have hc : ∑ i : Fin N, (ε i + pr _ (deltaN P Sm pg i)) = ∑ i ∈ range N, c i := by
    rw [← Fin.sum_univ_eq_sum_range c N]
    exact Finset.sum_congr rfl fun i _ => by simp only [c, i.isLt, ↓reduceDIte]
  rw [hc]
  refine real_sim_leN_joint P Sm pg c Y hY0 hYB (fun i hi Ev' => ?_) hJ hNB Ev
  have := hyb_hop_exp P Sm pg Ev' ⟨i, hi⟩ (Y i) (h ⟨i, hi⟩ Ev')
  simp only [c, hi, ↓reduceDIte]
  exact this

end Many

end VoleMole.Theft
