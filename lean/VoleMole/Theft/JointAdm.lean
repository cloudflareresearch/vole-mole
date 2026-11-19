import VoleMole.Theft.JointRaw

/-!
# The joint step for a class of events

`joint_le` and `real_sim_leN_jointRaw` move each hop's expected charge from hybrid `i` to the
simulated game through the hybrids' distance on **every** event (`exU_sub_le`). A hop bound for
every event is a hop bound for distinguishers that read the whole tables, which the one-proof
theorem with point charges (`ZKExp`) does not give: it needs a consistent point reader. Here the
hops are asked only for a class `Adm` of events (those read by the game's reader), as in
`ZK.IC.chain3_le`: the charges are weighted sums `Σ_k w k · n i k` of bounded natural-valued
functions of the view whose level sets are in the class, and expectations are compared level set
by level set (layer cakes):

* `exU_sum`, `exU_nat_sub_le`: linearity, and `E_a[n] ≤ E_b[n] + M·δ` for close level sets;
* **`joint_le_adm`**: the self-bounding composition for a class of events;
* **`real_sim_leN_jointAdm`**: for the hybrids of `Theft/Many.lean`, with the hop's charge in the
  zero-knowledge theorem's real world (`hyb_hop_expRaw`): for every event in the class,

      |Pr_real[Ev] − Pr_sim[Ev]| ≤ (Σ_i (ε i + (1 + B)·Pr[deltaN i]) + J) / (1 − N·B),

  `B = Σ_k w k · M k`, `J` bounding `Σ_i Σ_k w k · E_sim[n i k]`.
-/

open Finset

namespace VoleMole.Theft

open VoleMole.Privacy

section Lin

variable {Z : Type*} [Fintype Z] {K : Type*}

/-- **Linearity of the expectation over a finite sum.** -/
lemma exU_sum (s : Finset K) (f : K → Z → ℝ) :
    exU Z (fun z => ∑ k ∈ s, f k z) = ∑ k ∈ s, exU Z (f k) := by
  simp only [exU]
  rw [Finset.sum_comm, Finset.sum_div]

lemma exU_mul_left (c : ℝ) (f : Z → ℝ) : exU Z (fun z => c * f z) = c * exU Z f := by
  simp only [exU]
  rw [← Finset.mul_sum, mul_div_assoc]

/-- **A natural-valued function below `M` under close worlds**: `M` times the distance on its
level sets. -/
lemma exU_nat_sub_le {V : Type*} (ta tb : Z → V) (n : V → ℕ) {M : ℕ} (hn : ∀ v, n v ≤ M) {δ : ℝ}
    (h : ∀ l < M, |pr Z (fun z => l < n (ta z)) - pr Z (fun z => l < n (tb z))| ≤ δ) :
    exU Z (fun z => (n (ta z) : ℝ)) ≤ exU Z (fun z => (n (tb z) : ℝ)) + M * δ := by
  have ea : exU Z (fun z => (n (ta z) : ℝ)) = ∑ l ∈ range M, pr Z (fun z => l < n (ta z)) :=
    ZK.IC.exP_eq_sum_pr (fun z => n (ta z)) fun z => hn _
  have eb : exU Z (fun z => (n (tb z) : ℝ)) = ∑ l ∈ range M, pr Z (fun z => l < n (tb z)) :=
    ZK.IC.exP_eq_sum_pr (fun z => n (tb z)) fun z => hn _
  rw [ea, eb]
  have : ∑ l ∈ range M, pr Z (fun z => l < n (ta z)) - ∑ l ∈ range M, pr Z (fun z => l < n (tb z))
      ≤ M * δ := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ l ∈ range M, (pr Z (fun z => l < n (ta z)) - pr Z (fun z => l < n (tb z)))
        ≤ ∑ _l ∈ range M, δ := Finset.sum_le_sum fun l hl =>
          (le_abs_self _).trans (h l (Finset.mem_range.1 hl))
      _ = M * δ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

end Lin

section JointAdm

variable {Z V K : Type*} [Fintype Z] [Fintype K]

/-- **The joint hybrid for a class of events.** Worlds `t 0, …, t N` on one uniform tape; hop `i`
costs `c i + Σ_k w k · E_i[n i k]` for every event of the class `Adm`, with `n i k ≤ M k` and the
level sets of every `n i k` in `Adm`. If the charges sum to at most `J` in the last world and
`N·B < 1`, `B = Σ_k w k · M k`, then for every event of the class

    |Pr_0[F] − Pr_N[F]| ≤ (Σ_i c i + J) / (1 − N·B). -/
theorem joint_le_adm {N : ℕ} (t : ℕ → Z → V) (Adm : (V → Prop) → Prop) (c : ℕ → ℝ) (w : K → ℝ)
    (hw : ∀ k, 0 ≤ w k) (n : ℕ → K → V → ℕ) (M : K → ℕ) (hn : ∀ i < N, ∀ k v, n i k v ≤ M k)
    (hlev : ∀ i < N, ∀ k (l : ℕ), Adm (fun v => l < n i k v))
    (hop : ∀ i < N, ∀ F, Adm F →
      |pr Z (fun z => F (t i z)) - pr Z (fun z => F (t (i + 1) z))| ≤
        c i + ∑ k, w k * exU Z (fun z => (n i k (t i z) : ℝ)))
    {J : ℝ} (hJ : ∑ i ∈ range N, ∑ k, w k * exU Z (fun z => (n i k (t N z) : ℝ)) ≤ J)
    (hNB : N * ∑ k, w k * M k < 1) (F : V → Prop) (hF : Adm F) :
    |pr Z (fun z => F (t 0 z)) - pr Z (fun z => F (t N z))| ≤
      (∑ i ∈ range N, c i + J) / (1 - N * ∑ k, w k * M k) := by
  set B := ∑ k, w k * (M k : ℝ) with hBdef
  set D : ℕ → ℝ := fun i => c i + ∑ k, w k * exU Z (fun z => (n i k (t i z) : ℝ)) with hDdef
  set S := ∑ i ∈ range N, D i with hSdef
  have hD0 : ∀ i < N, 0 ≤ D i := fun i hi => (abs_nonneg _).trans (hop i hi F hF)
  have tele : ∀ k ≤ N, ∀ G : V → Prop, Adm G →
      |pr Z (fun z => G (t (N - k) z)) - pr Z (fun z => G (t N z))| ≤
        ∑ j ∈ Ico (N - k) N, D j := by
    intro k
    induction k with
    | zero => intro _ G _; simp
    | succ k ih =>
      intro hk G hG
      have hi : N - (k + 1) < N := by omega
      have e : N - (k + 1) + 1 = N - k := by omega
      have h1 := hop (N - (k + 1)) hi G hG
      rw [e] at h1
      have h2 := ih (by omega) G hG
      have h3 := abs_sub_le (pr Z (fun z => G (t (N - (k + 1)) z)))
        (pr Z (fun z => G (t (N - k) z))) (pr Z (fun z => G (t N z)))
      rw [Finset.sum_eq_sum_Ico_succ_bot hi, e]
      linarith
  have TV : ∀ i ≤ N, ∀ G : V → Prop, Adm G →
      |pr Z (fun z => G (t i z)) - pr Z (fun z => G (t N z))| ≤ S := by
    intro i hi G hG
    have h := tele (N - i) (by omega) G hG
    rw [show N - (N - i) = i by omega] at h
    refine h.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j hj _ => hD0 j ?_)
    · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
    · simpa using hj
  have hE : ∀ i < N, ∑ k, w k * exU Z (fun z => (n i k (t i z) : ℝ)) ≤
      ∑ k, w k * exU Z (fun z => (n i k (t N z) : ℝ)) + B * S := by
    intro i hi
    have hk : ∀ k, w k * exU Z (fun z => (n i k (t i z) : ℝ)) ≤
        w k * exU Z (fun z => (n i k (t N z) : ℝ)) + w k * M k * S := by
      intro k
      have := exU_nat_sub_le (t i) (t N) (n i k) (hn i hi k)
        fun l _ => TV i hi.le (fun v => l < n i k v) (hlev i hi k l)
      have := mul_le_mul_of_nonneg_left this (hw k)
      linarith
    calc ∑ k, w k * exU Z (fun z => (n i k (t i z) : ℝ))
        ≤ ∑ k, (w k * exU Z (fun z => (n i k (t N z) : ℝ)) + w k * M k * S) :=
          Finset.sum_le_sum fun k _ => hk k
      _ = ∑ k, w k * exU Z (fun z => (n i k (t N z) : ℝ)) + B * S := by
          rw [Finset.sum_add_distrib, hBdef, Finset.sum_mul]
  have hS : S ≤ ∑ i ∈ range N, c i + J + N * B * S := by
    have h1 : S = ∑ i ∈ range N, c i +
        ∑ i ∈ range N, ∑ k, w k * exU Z (fun z => (n i k (t i z) : ℝ)) := by
      rw [hSdef, hDdef, Finset.sum_add_distrib]
    have h2 : ∑ i ∈ range N, ∑ k, w k * exU Z (fun z => (n i k (t i z) : ℝ)) ≤
        ∑ i ∈ range N, (∑ k, w k * exU Z (fun z => (n i k (t N z) : ℝ)) + B * S) :=
      Finset.sum_le_sum fun i hi => hE i (Finset.mem_range.1 hi)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    rw [h1]
    nlinarith
  have hden : 0 < 1 - N * B := by linarith
  have hS' : S ≤ (∑ i ∈ range N, c i + J) / (1 - N * B) := by
    rw [le_div_iff₀ hden]; nlinarith
  exact (TV 0 (Nat.zero_le _) F hF).trans hS'

end JointAdm

section Many

variable {Ω O ρ C G S K : Type*}
  (P : Ω → List O → ρ → G → S → O) (Sm : Ω → List O → C → O) (pg : Ω → List O → C → S → S)
  {N : ℕ} [Nonempty ρ] [Nonempty C] [Nonempty G]
  [Fintype Ω] [Nonempty Ω] [Fintype ρ] [Fintype C] [Fintype G] [Fintype S] [Nonempty S]
  [Fintype K]

/-- **The joint bound for a class of events, with the hops' charges in the zero-knowledge
theorem's world.** `Adm` is a class of events of the game's view; every hop for an event of the
class is `ε i + E_raw[Σ_k w k · n i k]`-close (`hyb_hop_expRaw`'s hypothesis), with `n i k ≤ M k`
natural-valued and its level sets in the class; the charges sum to at most `J` in the simulated
game. Then for every event `Ev` of the class

    |Pr_real[Ev] − Pr_sim[Ev]| ≤ (Σ_i (ε i + (1 + B)·Pr[deltaN i]) + J) / (1 − N·B),

`B = Σ_k w k · M k`. -/
theorem real_sim_leN_jointAdm (Adm : (Ω × List O × (Fin N → G) × S → Prop) → Prop) (ε : ℕ → ℝ)
    (w : K → ℝ) (hw : ∀ k, 0 ≤ w k) (n : ℕ → K → Ω × List O × (Fin N → G) × S → ℕ) (M : K → ℕ)
    (hn : ∀ i < N, ∀ k v, n i k v ≤ M k) (hlev : ∀ i < N, ∀ k (l : ℕ), Adm (fun v => l < n i k v))
    (h : ∀ (i : Fin N) (Ev : Ω → List O → (Fin N → G) → S → Prop),
      Adm (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) → ∀ ω τ,
      |pr ((ρ × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) a.1.2 a.2) -
        pr ((C × G) × S) (fun a => distN P Sm pg Ev i ω τ
          (Sm ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1) a.1.2
          (pg ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.2))| ≤
        ε i + exU ((ρ × G) × S) (fun a => ∑ k, w k * (n i k (contView P Sm pg i ω τ
          (P ω (simPre Sm pg ω (tapeC τ) i).1 a.1.1 a.1.2 a.2) a.1.2
          ((simPre Sm pg ω (tapeC τ) i).2 a.2)) : ℝ)))
    {J : ℝ} (hJ : ∑ i ∈ range N, ∑ k, w k *
      exU _ (fun z => (n i k (viewN (C := C) P Sm pg N z) : ℝ)) ≤ J)
    (hNB : N * ∑ k, w k * M k < 1) (Ev : Ω → List O → (Fin N → G) → S → Prop)
    (hEv : Adm (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2)) :
    |pr _ (realGN (C := C) P Ev) - pr _ (simGN (ρ := ρ) Sm pg Ev)| ≤
      (∑ i : Fin N, (ε i + (1 + ∑ k, w k * M k) * pr _ (deltaN P Sm pg i)) + J) /
        (1 - N * ∑ k, w k * M k) := by
  set B := ∑ k, w k * (M k : ℝ)
  let c : ℕ → ℝ := fun i => if hi : i < N then ε i + (1 + B) * pr _ (deltaN P Sm pg ⟨i, hi⟩) else 0
  have hc : ∑ i : Fin N, (ε i + (1 + B) * pr _ (deltaN P Sm pg i)) = ∑ i ∈ range N, c i := by
    rw [← Fin.sum_univ_eq_sum_range c N]
    exact Finset.sum_congr rfl fun i _ => by simp only [c, i.isLt, ↓reduceDIte]
  rw [hc, ← hyb_zero P Sm pg Ev, ← hyb_last P Sm pg Ev]
  refine joint_le_adm (Z := (Ω × (Fin N → Slot ρ C G)) × S) (fun i z => viewN P Sm pg i z) Adm c w
    hw n M hn hlev (fun i hi F hF => ?_) hJ hNB (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv
  -- one hop for an event of the class
  let Y : Ω × List O × (Fin N → G) × S → ℝ := fun v => ∑ k, w k * (n i k v : ℝ)
  have hY0 : ∀ v, 0 ≤ Y v := fun v => Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (Nat.cast_nonneg _)
  have hYB : ∀ v, Y v ≤ B := fun v => Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast hn i hi k v) (hw k)
  have hop := hyb_hop_expRaw P Sm pg (fun ω l g s => F (ω, l, g, s)) ⟨i, hi⟩ Y hY0 hYB
    (h ⟨i, hi⟩ (fun ω l g s => F (ω, l, g, s)) hF)
  have eY : exU _ (fun z => Y (viewN (C := C) P Sm pg i z)) =
      ∑ k, w k * exU _ (fun z => (n i k (viewN (C := C) P Sm pg i z) : ℝ)) := by
    simp only [Y]
    rw [exU_sum]
    exact Finset.sum_congr rfl fun k _ => exU_mul_left _ _
  rw [eY] at hop
  simp only [c, hi, ↓reduceDIte]
  exact hop

end Many

end VoleMole.Theft
