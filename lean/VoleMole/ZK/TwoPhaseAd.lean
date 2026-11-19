import VoleMole.ZK.TwoPhaseReadsRO
import VoleMole.ZK.CollideRO2

/-!
# Two-phase zero knowledge with a continuation that reads the tables after step 1

`zk2_rom_ic_h23` (`ZK/TwoPhaseIC.lean`) lets the continuation `K G5 E` (the rest of the game up to
the proof's instance) read `H₅` and the cipher, at key sets fixed **before** step 1 (the whole
function `o₁ ↦ K G5 E o₁` is determined by the tables on them). In PomFRIT with an Issuer that reads
the tables, the continuation is the Issuer's response to the request computed **from step 1's
output** `o₁`, so its reads depend on `o₁`; it also reads the session's own `H₃` slice. Here:

* **The continuation** `K G3 G5 E : Cont2` reads, at each step-1 output `o₁`, the proof's `H₃`
  slice at `q_k3` keys, `H₅` at `q_k5` keys and the cipher at `q_kE` keys (`QK3 o₁ …`, `QK5 o₁ …`,
  `QKE o₁ …`; each with the other tables fixed), and does **not** read `H₂³`.
* **The hybrids** are those of `ZK/TwoPhaseRO.lean`/`ZK/TwoPhaseIC.lean`. Every hop but H1, H4 and
  H6 holds for every value of the tables, hence for a continuation depending on them (`zk2_progA`,
  `zk2_keysA`, `zk2_tapeA`, `zk2_simA`). H1 (`zk2_h1A`): `A v G3` reads the slice at the
  distinguisher's and the continuation's keys at `out1 v`, so `≤ (q₃ + q_k3)·2⁻¹²⁸`. H6
  (`zk2_h6A`) and H4 (`joint3_h4_2A`) add the continuation's keys **at the output's step 1** to the
  distinguisher's (the hops' query sets may depend on the output). The output depends on the
  continuation only at its step-1 output (`proveIdeal2_kcongr`, `hyb2'_kcongr`,
  `simRun2_kcongr'`, `outPre2_kcongr'`), which is the same on two tables agreeing on the keys read.
* **`zk2_rom_ic_h23A_num`**: `q₃ + q_k3`, `q₅ + q_k5`, `q_E + q_kE` in `εRO`. In the form of the
  games (`zk2_adaptive`, `Hyp2RA`): the continuation `K : Tab3 → Sh p → Cont2` reads the slice and
  the shared tables, not `H₂³`, error `εRO (q₃ + q_k3) (q₅ + q_k5) (q_E + q_kE)`.

`Hyp2RA` is stated for any type of cipher rows; **`ZK2ARow R`** is the class of row types with
`zk2_adaptive` (instances `ZK2ARow.fn`, and `ZK2ARow.perm` in `ZK/TwoPhasePerm.lean`).

A continuation that reads `H₂³` is not covered. The simulator programs `H₂³` at the block of the
prefix it recomputes for the continuation's instance, and at the zero-prefix block when the
continuation stops (`simTab2` at `outPre2 = ∅`): a continuation whose decision to stop depends on
`H₂³` there distinguishes, so the simulator would have to program nothing in that case. And a
continuation that read the block later programmed would need the programming hop (`zk2_progA`,
exact by `pr_program_eq` because the programmed points do not depend on `H₂³`) to pay a collision
term, bounded by a second application of the theorem (as `pr_preBlk_mem` for the single-phase
prover), with the tail `ã` of the real prefix hidden from a reader that has seen step 1.
PomFRIT's blindness game does not need that theorem: `Privacy/PomFRITRAH.lean` takes the Issuer's
`H₂³` reads out of the game by lazy sampling before the hybrids and bounds the remaining collision
with this file's theorem (`ZK/CollideAd2.lean`, `pr_tail2A`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

/-! ## The runs read the continuation only at their step-1 output -/

section KCongr

variable [HasPrg] (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray)

/-- The ideal two-phase run's step-1 output does not depend on the continuation. -/
lemma proveIdeal2_o1 (k k' : Cont2) (t : IdealTape2 st.params) :
    ((proveIdeal2 Hs T st r k t).1, (proveIdeal2 Hs T st r k t).2.1) =
      ((proveIdeal2 Hs T st r k' t).1, (proveIdeal2 Hs T st r k' t).2.1) := by
  unfold proveIdeal2
  rcases firstHit t.1.1.2.1 with _ | ⟨ctr, d⟩ <;> rfl

/-- **The ideal two-phase run reads its continuation only at its step-1 output.** -/
lemma proveIdeal2_kcongr {k k' : Cont2} (t : IdealTape2 st.params)
    (h : k ((proveIdeal2 Hs T st r k t).1, (proveIdeal2 Hs T st r k t).2.1) =
      k' ((proveIdeal2 Hs T st r k t).1, (proveIdeal2 Hs T st r k t).2.1)) :
    proveIdeal2 Hs T st r k t = proveIdeal2 Hs T st r k' t := by
  unfold proveIdeal2 at h ⊢
  rcases hf : firstHit t.1.1.2.1 with _ | ⟨ctr, d⟩
  · simp only [hf] at h ⊢
    rw [h]
  · simp only [hf] at h ⊢
    rw [h]

/-- The simulated two-phase run's step-1 output does not depend on the continuation. -/
lemma simRun2_o1 (n : ℕ) (k k' : Cont2) (c : SimCoins2 st.params) :
    ((simRun2 Hs st n k c).1, (simRun2 Hs st n k c).2.1) =
      ((simRun2 Hs st n k' c).1, (simRun2 Hs st n k' c).2.1) := by
  unfold simRun2
  rcases firstHit c.1.1.2.1 with _ | ⟨ctr, d⟩ <;> rfl

/-- **The simulated two-phase run reads its continuation only at its step-1 output.** -/
lemma simRun2_kcongr' (n : ℕ) {k k' : Cont2} (c : SimCoins2 st.params)
    (h : k ((simRun2 Hs st n k c).1, (simRun2 Hs st n k c).2.1) =
      k' ((simRun2 Hs st n k c).1, (simRun2 Hs st n k c).2.1)) :
    simRun2 Hs st n k c = simRun2 Hs st n k' c := by
  unfold simRun2 at h ⊢
  rcases hf : firstHit c.1.1.2.1 with _ | ⟨ctr, d⟩
  · simp only [hf] at h ⊢
    rw [h]
  · simp only [hf] at h ⊢
    rw [h]

/-- **The recomputed prefix reads the continuation only at the output's step 1.** -/
lemma outPre2_kcongr' {k k' : Cont2} (G5 : Tab5F) (o : Out2) (h : k (o.1, o.2.1) = k' (o.1, o.2.1)) :
    outPre2 Hs T st k G5 o = outPre2 Hs T st k' G5 o := by
  unfold outPre2
  rw [h]

/-- The two-phase grinding prefix reads the continuation only at step 1's output. -/
lemma pre2_kcongr {k k' : Cont2} (x : Bytes 16 × Bytes 16)
    (h : k (out1 Hs T st r x) = k' (out1 Hs T st r x)) :
    pre2 Hs T st r k x = pre2 Hs T st r k' x := by
  show realPre Hs (withInst st ((k (out1 Hs T st r x)).getD (default, .empty)).1)
      (pendAt Hs T (st1 st) r x) (r ++ ((k (out1 Hs T st r x)).getD (default, .empty)).2) =
    realPre Hs (withInst st ((k' (out1 Hs T st r x)).getD (default, .empty)).1)
      (pendAt Hs T (st1 st) r x) (r ++ ((k' (out1 Hs T st r x)).getD (default, .empty)).2)
  rw [h]

lemma preP_kcongr {k k' : Cont2} (x : Bytes 16 × Bytes 16)
    (h : k (out1 Hs T st r x) = k' (out1 Hs T st r x)) :
    preP Hs T st r k x = preP Hs T st r k' x := by
  unfold preP
  rw [h, pre2_kcongr Hs T st r x h]

/-- **Hybrid H2 reads the continuation only at step 1's output.** -/
lemma hyb2'_kcongr {k k' : Cont2} (hHs : HashesWF Hs) (hk : Hyp2 st r k) (hk' : Hyp2 st r k')
    (x : Bytes 16 × Bytes 16) (g : Grind)
    (h : k (out1 Hs CrtGen.tables st r x) = k' (out1 Hs CrtGen.tables st r x)) :
    hyb2' Hs CrtGen.tables st r k (x.1, x.2, g) = hyb2' Hs CrtGen.tables st r k' (x.1, x.2, g) := by
  have hp := pre2_kcongr Hs CrtGen.tables st r x h
  have hr : recAt2 Hs CrtGen.tables st r k x g = recAt2 Hs CrtGen.tables st r k' x g := by
    simp only [recAt2, hp]
  rw [hyb2'_eq Hs st r k hHs hk x g, hyb2'_eq Hs st r k' hHs hk' x g]
  simp only [hr, h]

/-- **The hybrid after H4 reads the continuation only at its step-1 output.** -/
lemma hyb3'_kcongr {k k' : Cont2} (b : (Bytes 16 × Grind) × Fallback st.params)
    (hid : Hidden st.params)
    (h : k ((hyb3' Hs T st r k b hid).1, (hyb3' Hs T st r k b hid).2.1) =
      k' ((hyb3' Hs T st r k b hid).1, (hyb3' Hs T st r k b hid).2.1)) :
    hyb3' Hs T st r k b hid = hyb3' Hs T st r k' b hid := by
  unfold hyb3' at h ⊢
  exact proveIdeal2_kcongr Hs T st r _ h

end KCongr

/-! ## The hybrids before H4, the continuation reading the `H₃` slice -/

section Pre

variable [HasPrg] (Hb : Hashes) (st : Statement) (r : ByteArray) (kf : Tab3 → Tab5F → Cont2)

/-- **H1 with a continuation that reads the slice** (two phases): `rho` and the `H₃` table against
a uniform seed and `iv_pre`, for a distinguisher that reads the slice at `q₃` keys and a
continuation that reads it at `q_k3` keys at step 1's output: `≤ (q₃ + q_k3)·2⁻¹²⁸`. -/
theorem zk2_h1A (hHb : HashesWF Hb) (hh : ∀ G3 G5, Hyp2 st r (kf G3 G5))
    (QK3 : ByteArray × ByteArray → Tab3 → Tab5F → Finset (Bytes 16))
    (hQK3 : ∀ o1 G3 G3' G5, (∀ k ∈ QK3 o1 G3 G5, G3 k = G3' k) → kf G3' G5 o1 = kf G3 G5 o1)
    {qk3 : ℕ} (hqk3 : ∀ o1 G3 G5, (QK3 o1 G3 G5).card ≤ qk3)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q3 : Out2 → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (realRun2 (recH Hb (st1 st) r c.2.1 c.1.2 c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2)
          (ba c.1.1)) c.2.1 c.1.2 c.2.2) -
      pr (((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (hyb2' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2)
          (c.1.1.1, c.1.1.2, c.1.2 ∘ key2 st.params
            (preP (rec5 Hb c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2) c.1.1)))
          c.2.1 c.1.2 c.2.2)| ≤ (q3 + qk3) / 2 ^ 128 := by
  let E0 : (Tab2G st.params × Tab5F) × (Bytes 16 × Tab3) ≃
      (Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F) :=
    { toFun := fun c => ((c.2.1, c.1.1), (c.2.2, c.1.2))
      invFun := fun c => ((c.1.2, c.2.2), (c.1.1, c.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E1 : (Tab2G st.params × Tab5F) × (Tab3 × (Bytes 16 × Bytes 16)) ≃
      ((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5F) :=
    { toFun := fun c => ((c.2.2, c.1.1), (c.2.1, c.1.2))
      invFun := fun c => ((c.1.2, c.2.2), (c.2.1, c.1.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E0, ← pr_equiv E1]
  refine abs_pr_prod_sub_le _ _ fun a => ?_
  obtain ⟨G2, G5⟩ := a
  have hB0 : HashesWF (recB Hb (st1 st) r (fun _ => 0) G5) :=
    recH_wf (st := st1 st) (w := r) hHb _ _ G5
  let R : Bytes 16 × Bytes 16 → Tab3 → Out2 := fun x G3 =>
    hyb2' (recB Hb (st1 st) r (fun _ => 0) G5) CrtGen.tables st r (kf G3 G5)
      (x.1, x.2, G2 ∘ key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r (kf G3 G5) x))
  have hR : ∀ (G3' : Tab3) (k : Cont2), hyb2' (recB Hb (st1 st) r G3' G5) CrtGen.tables st r k =
      hyb2' (recB Hb (st1 st) r (fun _ => 0) G5) CrtGen.tables st r k := fun G3' k =>
    hyb2'_agreeOff unread_h3 (recH_agreeOff_h3 (st := st1 st) (w := r) G3' (fun _ => 0)
      (fun _ => 0) G5) CrtGen.tables st r k
  have hout : out1 (recB Hb (st1 st) r (fun _ => 0) G5) CrtGen.tables st r =
      out1 (rec5 Hb G5) CrtGen.tables st r := out1_recB _ _
  let A : Bytes 16 × Bytes 16 → Tab3 → Prop := fun v G3 => D (R v G3) G3 G2 G5
  let Q : Bytes 16 × Bytes 16 → Tab3 → Finset (Bytes 16) := fun v G3 =>
    Q3 (R v G3) G3 G2 G5 ∪ QK3 (out1 (rec5 Hb G5) CrtGen.tables st r v) G3 G5
  have hQ : ∀ v G G', (∀ k ∈ Q v G, G k = G' k) → (A v G ↔ A v G') := by
    intro v G G' hG
    have hk : kf G' G5 (out1 (rec5 Hb G5) CrtGen.tables st r v) =
        kf G G5 (out1 (rec5 Hb G5) CrtGen.tables st r v) :=
      hQK3 _ G G' G5 fun k hk => hG k (Finset.mem_union_right _ hk)
    have hRv : R v G' = R v G := by
      show hyb2' (recB Hb (st1 st) r (fun _ => 0) G5) CrtGen.tables st r (kf G' G5)
          (v.1, v.2, G2 ∘ key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r (kf G' G5) v)) =
        hyb2' (recB Hb (st1 st) r (fun _ => 0) G5) CrtGen.tables st r (kf G G5)
          (v.1, v.2, G2 ∘ key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r (kf G G5) v))
      rw [preP_kcongr (rec5 Hb G5) CrtGen.tables st r v hk]
      exact hyb2'_kcongr _ st r hB0 (hh G' G5) (hh G G5) v _ (by rw [hout]; exact hk)
    show D (R v G) G G2 G5 ↔ D (R v G') G' G2 G5
    rw [hRv]
    exact hQ3 (R v G) G G' G2 G5 fun k hk => hG k (Finset.mem_union_left _ hk)
  have h := h3_rom_query ((st1 st).mu1 Hb) r Hb A Q hQ (q := q3 + qk3)
    (fun v G3 => (card_union_le _ _).trans (add_le_add (hq3 _ G3 G2 G5) (hqk3 _ G3 G5)))
  have e1 : pr (Bytes 16 × Tab3) (fun b =>
      D (realRun2 (recH Hb (st1 st) r b.2 G2 G5) CrtGen.tables st r (kf b.2 G5) (ba b.1)) b.2 G2 G5) =
      pr (Bytes 16 × (Bytes 16 → Bytes 32)) (fun p =>
        A (h3Seed (Hb.withTable .h3 (seedInput ((st1 st).mu1 Hb) r) p.2) ((st1 st).mu1 Hb) r
          (ba p.1)) p.2) := by
    refine pr_congr fun b => ?_
    simp only [A, R, real_form Hb st r (kf b.2 G5) hHb (hh b.2 G5), h3Seed_withTable, hR]
  have e2 : pr (Bytes 16 × ((Bytes 16 → Bytes 32) × Bytes 32)) (fun p =>
      A (splitSeed p.2.2) p.2.1) =
      pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b => D (hyb2' (recB Hb (st1 st) r b.1 G5)
        CrtGen.tables st r (kf b.1 G5) (b.2.1, b.2.2,
          G2 ∘ key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r (kf b.1 G5) b.2))) b.1 G2 G5) := by
    rw [pr_prod_snd (α := Bytes 16)
      (fun q : (Bytes 16 → Bytes 32) × Bytes 32 => A (splitSeed q.2) q.1),
      ← pr_equiv (Equiv.prodCongr (Equiv.refl Tab3) splitEquiv)]
    refine pr_congr fun b => ?_
    simp only [A, R, hR]
    rfl
  have e1' : pr (Bytes 16 × Tab3) (fun b =>
      D (realRun2 (recH Hb (st1 st) r b.2 G2 G5) CrtGen.tables st r (kf b.2 G5) (ba b.1)) b.2 G2 G5) =
      pr (Bytes 16 × Tab3) (fun b =>
        D (realRun2 (recH Hb (st1 st) r (E0 ((G2, G5), b)).2.1 (E0 ((G2, G5), b)).1.2
          (E0 ((G2, G5), b)).2.2) CrtGen.tables st r (kf (E0 ((G2, G5), b)).2.1 (E0 ((G2, G5), b)).2.2)
            (ba (E0 ((G2, G5), b)).1.1))
          (E0 ((G2, G5), b)).2.1 (E0 ((G2, G5), b)).1.2 (E0 ((G2, G5), b)).2.2) := rfl
  have e2' : pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b => D (hyb2' (recB Hb (st1 st) r b.1 G5)
        CrtGen.tables st r (kf b.1 G5) (b.2.1, b.2.2,
          G2 ∘ key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r (kf b.1 G5) b.2))) b.1 G2 G5) =
      pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b =>
        D (hyb2' (recB Hb (st1 st) r (E1 ((G2, G5), b)).2.1 (E1 ((G2, G5), b)).2.2)
          CrtGen.tables st r (kf (E1 ((G2, G5), b)).2.1 (E1 ((G2, G5), b)).2.2)
            ((E1 ((G2, G5), b)).1.1.1, (E1 ((G2, G5), b)).1.1.2,
            (E1 ((G2, G5), b)).1.2 ∘ key2 st.params (preP (rec5 Hb (E1 ((G2, G5), b)).2.2)
              CrtGen.tables st r (kf (E1 ((G2, G5), b)).2.1 (E1 ((G2, G5), b)).2.2)
                (E1 ((G2, G5), b)).1.1)))
          (E1 ((G2, G5), b)).2.1 (E1 ((G2, G5), b)).1.2 (E1 ((G2, G5), b)).2.2) := rfl
  rw [← e1', ← e2', e1, ← e2]
  exact h.trans (le_of_eq (by push_cast; ring))

/-- **Grinding with `H₂³` visible: programming is perfect** (exact, two phases, a continuation
depending on the slice and `H₅`). -/
theorem zk2_progA (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop) :
    |pr (((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (hyb2' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2)
          (c.1.1.1, c.1.1.2, c.1.2 ∘ key2 st.params
            (preP (rec5 Hb c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2) c.1.1)))
          c.2.1 c.1.2 c.2.2) -
      pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (fun c =>
        D (hyb2' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2)
            (c.1.1.1, c.1.1.2, c.1.2.2))
          c.2.1 (programAt (key2 st.params
            (preP (rec5 Hb c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2) c.1.1)) c.1.2.2 c.1.2.1)
          c.2.2)| ≤ 0 := by
  refine abs_pr_prod_sub_le' _ _ fun v => ?_
  obtain ⟨G3, G5⟩ := v
  rw [abs_nonpos_iff, sub_eq_zero]
  exact pr_program_eq (C := Bytes 16 × Bytes 16) (R := Bytes 16)
    (x := fun c => key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r (kf G3 G5) c))
    (fun c => key2_injective _ _)
    (fun c (u : Grind) (G2 : Tab2G st.params) =>
      D (hyb2' (recB Hb (st1 st) r G3 G5) CrtGen.tables st r (kf G3 G5) (c.1, c.2, u)) G3 G2 G5)

/-- **The programmed points, recomputed from the output, and a uniform fallback block**
(`≤ Pr[GrindBad]`, `zk2_keys` with a continuation depending on the slice and `H₅`). -/
theorem zk2_keysA (hHb : HashesWF Hb) (hh : ∀ G3 G5, Hyp2 st r (kf G3 G5))
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop) :
    |pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (fun c =>
        D (hyb2' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2)
            (c.1.1.1, c.1.1.2, c.1.2.2))
          c.2.1 (programAt (key2 st.params
            (preP (rec5 Hb c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2) c.1.1)) c.1.2.2 c.1.2.1)
          c.2.2) -
      pr ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
          (Tab3 × Tab5F)) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.1 c.2.2) D (hyb3' (recB Hb (st1 st) r c.2.1 c.2.2)
          CrtGen.tables st r (kf c.2.1 c.2.2) ((c.1.1.1.2, c.1.1.2.2), c.1.2)
          (hiddenOut st.params (ivOfPre Hb (st1 st) c.1.1.1.2) (ba (deltaOf c.1.1.2.2)) c.1.1.1.1))
          c.1.1.2.2 (c.2.1, c.1.1.2.1, c.2.2))| ≤
      pr Grind (GrindBad CrtGen.tables) := by
  let L : ((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F) → Prop := fun c =>
    D (hyb2' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2)
        (c.1.1.1, c.1.1.2, c.1.2.2))
      c.2.1 (programAt (key2 st.params
        (preP (rec5 Hb c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2) c.1.1)) c.1.2.2 c.1.2.1) c.2.2
  let EF : (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) ×
      Fallback st.params ≃ (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) ×
        Fallback st.params) × (Tab3 × Tab5F) :=
    { toFun := fun c => ((c.1.1, c.2), c.1.2)
      invFun := fun c => ((c.1.1, c.2), c.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e0 : pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) L =
      pr ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
        (Tab3 × Tab5F)) (fun c => L (c.1.1, c.2)) := by
    rw [← pr_equiv EF, ← pr_prod_fst (β := Fallback st.params) L]
    rfl
  rw [show (fun c : ((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F) =>
      D (hyb2' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2)
          (c.1.1.1, c.1.1.2, c.1.2.2))
        c.2.1 (programAt (key2 st.params
          (preP (rec5 Hb c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2) c.1.1)) c.1.2.2 c.1.2.1)
        c.2.2) = L from rfl, e0]
  refine (abs_pr_sub_le_of_agree _ _ (fun c => GrindBad CrtGen.tables c.1.1.2.2)
    fun c hc => ?_).trans (le_of_eq ?_)
  · obtain ⟨⟨⟨x, G2, g⟩, fb⟩, G3, G5⟩ := c
    dsimp only at hc ⊢
    have hBwf : HashesWF (recB Hb (st1 st) r G3 G5) := recH_wf (st := st1 st) (w := r) hHb G3 _ G5
    have hiv : ivOfPre (recB Hb (st1 st) r G3 G5) (st1 st) = ivOfPre Hb (st1 st) :=
      recH_ivOfPre (st := st1 st) (w := r) G3 (fun _ => 0) G5
    obtain ⟨⟨ctr, δ⟩, hf⟩ := Option.ne_none_iff_exists'.1 (not_or.1 hc).1
    have e1 : hyb3' (recB Hb (st1 st) r G3 G5) CrtGen.tables st r (kf G3 G5) ((x.2, g), fb)
        (hiddenOut st.params (ivOfPre Hb (st1 st) x.2) (ba (deltaOf g)) x.1) =
        hyb2' (recB Hb (st1 st) r G3 G5) CrtGen.tables st r (kf G3 G5) (x.1, x.2, g) := by
      rw [← hiv, hyb3'_hiddenOut st r (kf G3 G5) _ hBwf (hh G3 G5).hlab x g fb]
      exact proveIdeal2_fb _ _ st r (kf G3 G5) (t := tapeAt (recB Hb (st1 st) r G3 G5)
        CrtGen.tables st.params (pendAt (recB Hb (st1 st) r G3 G5) CrtGen.tables (st1 st) r x) g)
        hf _ _
    have hout : out1 (recB Hb (st1 st) r G3 G5) CrtGen.tables st r =
        out1 (rec5 Hb G5) CrtGen.tables st r := out1_recB _ _
    have e2 : outPre2 Hb CrtGen.tables st (kf G3 G5) G5
        (hyb2' (recB Hb (st1 st) r G3 G5) CrtGen.tables st r (kf G3 G5) (x.1, x.2, g)) =
        preP (rec5 Hb G5) CrtGen.tables st r (kf G3 G5) x := by
      rcases hk1 : kf G3 G5 (out1 (rec5 Hb G5) CrtGen.tables st r x) with _ | ⟨y, sfx⟩
      · rw [hyb2'_none _ st r (kf G3 G5) hBwf (hh G3 G5) x g (by rw [hout]; exact hk1)]
        simp only [outPre2, preP, hk1, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      · obtain ⟨proof, hok, hv⟩ := hyb2'_vPre _ st r (kf G3 G5) hBwf (hh G3 G5) x g hc
          (y := y) (sfx := sfx) (by rw [hout]; exact hk1)
        rw [hok]
        have hv' : vPre (rec5 Hb G5) CrtGen.tables (withInst st y) proof =
            pre2 (rec5 Hb G5) CrtGen.tables st r (kf G3 G5) x := by
          rw [← recH_eq_rec5 (fun H => vPre H CrtGen.tables (withInst st y))
              (fun _ _ _ hu h => vPre_agreeOff hu h _ _) Hb (st1 st) r G3 (fun _ => 0) G5,
            ← recH_eq_rec5 (fun H => pre2 H CrtGen.tables st r (kf G3 G5))
              (fun _ _ _ hu h => pre2_agreeOff hu h _ _ _ _) Hb (st1 st) r G3 (fun _ => 0) G5]
          exact hv
        simp only [outPre2, hout, hk1, preP, Option.isSome_some, ↓reduceIte]
        exact hv'
    simp only [L, Dp2, simTab2, e1, e2]
  · rw [pr_prod_fst (β := Tab3 × Tab5F)
      (fun a : ((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params =>
        GrindBad CrtGen.tables a.1.2.2),
      pr_prod_fst (β := Fallback st.params)
        (fun a : (Bytes 16 × Bytes 16) × (Tab2G st.params × Grind) => GrindBad CrtGen.tables a.2.2),
      pr_prod_snd (α := Bytes 16 × Bytes 16)
        (fun a : Tab2G st.params × Grind => GrindBad CrtGen.tables a.2),
      pr_prod_snd (α := Tab2G st.params) (GrindBad CrtGen.tables)]

/-- **The two-phase hybrids before H4, the continuation reading the slice** (`zk2_pre_h4`). -/
theorem zk2_pre_h4A (hHb : HashesWF Hb) (hh : ∀ G3 G5, Hyp2 st r (kf G3 G5))
    (QK3 : ByteArray × ByteArray → Tab3 → Tab5F → Finset (Bytes 16))
    (hQK3 : ∀ o1 G3 G3' G5, (∀ k ∈ QK3 o1 G3 G5, G3 k = G3' k) → kf G3' G5 o1 = kf G3 G5 o1)
    {qk3 : ℕ} (hqk3 : ∀ o1 G3 G5, (QK3 o1 G3 G5).card ≤ qk3)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q3 : Out2 → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (realRun2 (recH Hb (st1 st) r c.2.1 c.1.2 c.2.2) CrtGen.tables st r (kf c.2.1 c.2.2)
          (ba c.1.1)) c.2.1 c.1.2 c.2.2) -
      pr ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
          (Tab3 × Tab5F)) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.1 c.2.2) D (hyb3' (recB Hb (st1 st) r c.2.1 c.2.2)
          CrtGen.tables st r (kf c.2.1 c.2.2) ((c.1.1.1.2, c.1.1.2.2), c.1.2)
          (hiddenOut st.params (ivOfPre Hb (st1 st) c.1.1.1.2) (ba (deltaOf c.1.1.2.2)) c.1.1.1.1))
          c.1.1.2.2 (c.2.1, c.1.1.2.1, c.2.2))| ≤
      (q3 + qk3) / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) := by
  have h1 := zk2_h1A Hb st r kf hHb hh QK3 hQK3 hqk3 D Q3 hQ3 hq3
  have h2 := zk2_progA Hb st r kf D
  have h3 := zk2_keysA Hb st r kf hHb hh D
  have := abs_sub_le _ _ _ |>.trans (add_le_add h1 ((abs_sub_le _ _ _).trans (add_le_add h2 h3)))
  exact this.trans (le_of_eq (by ring))

end Pre

/-! ## The hybrids after H4, the continuation reading `H₅` at step 1's output -/

section Post

variable [HasPrg] (Hb : Hashes) (st : Statement) (r : ByteArray) (kf : Tab3 → Tab5F → Cont2)

/-- **The deterministic steps with the tables** (`zk2_tape`, exact). -/
theorem zk2_tapeA (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop) :
    |pr ((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params)
        (fun c => Dp2 Hb CrtGen.tables st (kf c.2.1 c.2.2.2) D (hyb3' (recB Hb (st1 st) r c.2.1 c.2.2.2)
          CrtGen.tables st r (kf c.2.1 c.2.2.2) c.1.2 (hiddenIdeal (ba (deltaOf c.1.2.1.2)) c.1.1))
          c.1.2.1.2 c.2) -
      pr (IdealTape2 st.params × Vis2 st.params) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.1 c.2.2.2) D (proveIdeal2 (recB Hb (st1 st) r c.2.1 c.2.2.2)
          CrtGen.tables st r (kf c.2.1 c.2.2.2)
            (fillSib (recB Hb (st1 st) r c.2.1 c.2.2.2) CrtGen.tables (st1 st) c.1.1, c.1.2))
          c.1.1.1.2.1 c.2)| ≤ 0 := by
  refine abs_pr_prod_sub_le' _ _ fun v => ?_
  rw [abs_nonpos_iff, sub_eq_zero]
  let R := recB Hb (st1 st) r v.1 v.2.2
  let F : Out2 → Grind → Prop := fun o g => Dp2 Hb CrtGen.tables st (kf v.1 v.2.2) D o g v
  have e1 : pr (Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) (fun y =>
      F (hyb3' R CrtGen.tables st r (kf v.1 v.2.2) y.2 (hiddenIdeal (ba (deltaOf y.2.1.2)) y.1))
        y.2.1.2) =
      pr (Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params))
        (fun y => F (hyb3' R CrtGen.tables st r (kf v.1 v.2.2) y.2 y.1) y.2.1.2) :=
    pr_congr fun y => by rw [hyb3'_zeroTail]
  have e2 : pr (IdealTape2 st.params) (fun t =>
      F (proveIdeal2 R CrtGen.tables st r (kf v.1 v.2.2) (fillSib R CrtGen.tables (st1 st) t.1, t.2))
        t.1.1.2.1) =
      pr (Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params))
        (fun y => F (hyb3' R CrtGen.tables st r (kf v.1 v.2.2) y.2 y.1) y.2.1.2) := by
    rw [← pr_equiv (tapeEquiv2 st.params), ← pr_prod_fst (β := Sib)
      (fun y : Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params) =>
        F (hyb3' R CrtGen.tables st r (kf v.1 v.2.2) y.2 y.1) y.2.1.2)]
    refine pr_congr fun x => ?_
    rw [show (tapeEquiv2 st.params x).1 = tapeOfHidden x.1.2.1.1 x.1.2.1.2 x.1.1 x.2 from rfl,
      show (tapeEquiv2 st.params x).2 = x.1.2.2 from rfl, hyb3',
      fillSib_tapeOfHidden R CrtGen.tables (st1 st) _ _ _ x.2 fun _ => fun _ => 0]
    rfl
  exact e1.trans e2.symm

/-- **The ideal two-phase run on a uniform tape is the simulator** (`zk2_sim`, exact). -/
theorem zk2_simA (hh : ∀ G3 G5, Hyp2 st r (kf G3 G5))
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop) :
    |pr (IdealTape2 st.params × Vis2 st.params) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.1 c.2.2.2) D (proveIdeal2 (recB Hb (st1 st) r c.2.1 c.2.2.2)
          CrtGen.tables st r (kf c.2.1 c.2.2.2) c.1) c.1.1.1.2.1 c.2) -
      pr (SimCoins2 st.params × Vis2 st.params) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.1 c.2.2.2) D (simRun2 Hb st r.size (kf c.2.1 c.2.2.2) c.1)
          c.1.1.1.2.1 c.2)| ≤ 0 :=
  abs_pr_prod_sub_le' _ _ fun v => by
    have hB : simRun2 (recB Hb (st1 st) r v.1 v.2.2) st r.size (kf v.1 v.2.2) =
        simRun2 Hb st r.size (kf v.1 v.2.2) := by
      have a1 := Hb.agreeOff_withTable .h3
        (seedInput ((st1 st).mu1 Hb) (r.extract 0 (st1 st).params.witnessBytes)) v.1
      have a2 := (Hb.withTable .h3 (seedInput ((st1 st).mu1 Hb)
        (r.extract 0 (st1 st).params.witnessBytes)) v.1).agreeOff_withTable .h23
          (enc2 (st1 st).params) (fun _ => 0)
      have a3 := ((Hb.withTable .h3 (seedInput ((st1 st).mu1 Hb)
        (r.extract 0 (st1 st).params.witnessBytes)) v.1).withTable .h23
          (enc2 (st1 st).params) (fun _ => 0)).agreeOff_withTable .h5 enc5 v.2.2
      exact ((simRun2_agreeOff a1 (by decide) (by decide) (by decide) (by decide) (by decide) st
        r.size (kf v.1 v.2.2)).trans ((simRun2_agreeOff a2 (by decide) (by decide) (by decide)
          (by decide) (by decide) st r.size (kf v.1 v.2.2)).trans (simRun2_agreeOff a3 (by decide)
            (by decide) (by decide) (by decide) (by decide) st r.size (kf v.1 v.2.2)))).symm
    have := proveIdeal2_close_shared st r (kf v.1 v.2.2) (recB Hb (st1 st) r v.1 v.2.2)
      (hh v.1 v.2.2) (fun os => Dp2 Hb CrtGen.tables st (kf v.1 v.2.2) D os.1 os.2 v)
    dsimp only at this ⊢
    rw [← hB]
    exact this

/-- **H6 with the tables, the continuation reading `H₅` at step 1's output** (`zk2_h6`): the
continuation's keys at the output's step 1 are added to the distinguisher's. -/
theorem zk2_h6A (hHb : HashesWF Hb) (hh : ∀ G3 G5, Hyp2 st r (kf G3 G5))
    (QK5 : ByteArray × ByteArray → Tab3 → Tab5F → Finset (Bytes 37))
    (hQK5 : ∀ o1 G3 G5 G5', (∀ key ∈ QK5 o1 G3 G5, G5 key = G5' key) → kf G3 G5' o1 = kf G3 G5 o1)
    {qk5 : ℕ} (hqk5 : ∀ o1 G3 G5, (QK5 o1 G3 G5).card ≤ qk5)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q5 : Out2 → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5, (Q5 o G3 G2 G5).card ≤ q5) :
    |pr (IdealTape2 st.params × Vis2 st.params) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.1 c.2.2.2) D (proveIdeal2 (recB Hb (st1 st) r c.2.1 c.2.2.2)
          CrtGen.tables st r (kf c.2.1 c.2.2.2)
            (fillSib (recB Hb (st1 st) r c.2.1 c.2.2.2) CrtGen.tables (st1 st) c.1.1, c.1.2))
          c.1.1.1.2.1 c.2) -
      pr (IdealTape2 st.params × Vis2 st.params) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.1 c.2.2.2) D (proveIdeal2 (recB Hb (st1 st) r c.2.1 c.2.2.2)
          CrtGen.tables st r (kf c.2.1 c.2.2.2) c.1) c.1.1.1.2.1 c.2)| ≤
      (q5 + qk5 + 1) / 2 ^ 128 := by
  have hlab := (hh (fun _ => 0) fun _ => 0).hlab
  let E6 : (Tab3 × Tab2G st.params) × (Fallback st.params × (IdealTape st.params × Tab5F)) ≃
      IdealTape2 st.params × Vis2 st.params :=
    { toFun := fun c => ((c.2.2.1, c.2.1), (c.1.1, (c.1.2, c.2.2.2)))
      invFun := fun c => ((c.2.1, c.2.2.1), (c.1.2, (c.1.1, c.2.2.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E6, ← pr_equiv E6]
  refine abs_pr_prod_sub_le _ _ fun a => abs_pr_prod_sub_le _ _ fun fb => ?_
  obtain ⟨G3, G2⟩ := a
  set base := (Hb.withTable .h3 (seedInput ((st1 st).mu1 Hb)
    (r.extract 0 (st1 st).params.witnessBytes)) G3).withTable .h23 (enc2 (st1 st).params)
      (fun _ => 0) with hbase
  have a1 := Hb.agreeOff_withTable .h3 (seedInput ((st1 st).mu1 Hb)
    (r.extract 0 (st1 st).params.witnessBytes)) G3
  have a2 := (Hb.withTable .h3 (seedInput ((st1 st).mu1 Hb)
    (r.extract 0 (st1 st).params.witnessBytes)) G3).agreeOff_withTable .h23
      (enc2 (st1 st).params) (fun _ => 0)
  have hbwf : HashesWF base := (hHb.withTable .h3 _ G3).withTable .h23 _ _
  let sk : Shared × PadsU st.params → Fin 312 → Bytes 37 := fun c e =>
    blk 37 (sibInput base CrtGen.tables (st1 st) c.1 (withSib c.2 fun _ => fun _ => 0) e)
  have hsk : ∀ c e, enc5 (sk c e) =
      sibInput base CrtGen.tables (st1 st) c.1 (withSib c.2 fun _ => fun _ => 0) e :=
    fun c e => ba_blk_of_size (sibInput_size base CrtGen.tables (st1 st) hbwf _ _ e)
  have hkey : ∀ c e, keyOf enc5 (sk c e) = sk c e :=
    fun c e => keyOf_eq (fun a b h => ba_injective h) _
  have hv5 : ∀ (G : Tab5F) (st' : Statement), (st' = st1 st ∨ ∃ y, st' = withInst st y) →
      vIn5 (rec5 Hb G) CrtGen.tables st' = vIn5 base CrtGen.tables st' := by
    intro G st' _
    have a0 := Hb.agreeOff_withTable .h5 enc5 G
    refine vIn5_congr CrtGen.tables st' ?_ ?_
    · exact (a0.mu1 (by decide) (by decide) st').symm.trans
        ((a1.mu1 (by decide) (by decide) st').trans (a2.mu1 (by decide) (by decide) st'))
    · exact (a0 .h4 (by decide)).symm.trans ((a1 .h4 (by decide)).trans (a2 .h4 (by decide)))
  let QD : Out2 → Shared → Tab5F → Finset (Bytes 37) := fun o s G5 =>
    Q5 o G3 (simTab2 Hb CrtGen.tables st (kf G3 G5) G5 o s.2.1 G2) G5 ∪ QK5 (o.1, o.2.1) G3 G5
  have hA : ∀ (t : IdealTape st.params) (G G' : Tab5F), (∀ key ∈ proverKeysG base CrtGen.tables
      (st1 st) enc5 t ∪ QD (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G)
        (t, fb)) t.1 G, G key = G' key) →
      (Dp2 Hb CrtGen.tables st (kf G3 G) D (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables
          st r (kf G3 G) (t, fb)) t.1.2.1 (G3, G2, G) ↔
        Dp2 Hb CrtGen.tables st (kf G3 G') D (proveIdeal2 (base.withTable .h5 enc5 G')
          CrtGen.tables st r (kf G3 G') (t, fb)) t.1.2.1 (G3, G2, G')) := by
    rintro ⟨s0, t0⟩ G G' hG
    have hp := proveIdeal2_table_congrG base st r (kf G3 G) enc5 hlab ((s0, t0), fb) G G'
      fun key hk => hG key (Finset.mem_union_left _ hk)
    have hK : kf G3 G' ((proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G)
          ((s0, t0), fb)).1,
        (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G) ((s0, t0), fb)).2.1) =
        kf G3 G ((proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G)
          ((s0, t0), fb)).1,
        (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G) ((s0, t0), fb)).2.1) :=
      hQK5 _ G3 G G' fun key hk => hG key (Finset.mem_union_right _ (Finset.mem_union_right _ hk))
    have ho' : proveIdeal2 (base.withTable .h5 enc5 G') CrtGen.tables st r (kf G3 G') ((s0, t0), fb)
        = proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G) ((s0, t0), fb) := by
      have e1 : proveIdeal2 (base.withTable .h5 enc5 G') CrtGen.tables st r (kf G3 G') ((s0, t0), fb)
          = proveIdeal2 (base.withTable .h5 enc5 G') CrtGen.tables st r (kf G3 G) ((s0, t0), fb) := by
        refine proveIdeal2_kcongr _ _ _ _ _ ?_
        have e2 := proveIdeal2_o1 (base.withTable .h5 enc5 G') CrtGen.tables st r (kf G3 G')
          (kf G3 G) ((s0, t0), fb)
        rw [e2, ← hp]
        exact hK
      rw [e1, ← hp]
    have hpre : outPre2 Hb CrtGen.tables st (kf G3 G) G
        (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G) ((s0, t0), fb)) =
        outPre2 Hb CrtGen.tables st (kf G3 G) G'
          (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G) ((s0, t0), fb)) := by
      unfold outPre2
      rcases hb : (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G)
        ((s0, t0), fb)).2.2 with _ | e | b
      · rfl
      · rfl
      rcases hk1 : kf G3 G ((proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G)
          ((s0, t0), fb)).1,
        (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G)
          ((s0, t0), fb)).2.1) with _ | ⟨y, sfx⟩
      · rfl
      dsimp only
      have hag : (rec5 Hb G).AgreeOff .h5 (rec5 Hb G') :=
        Hashes.AgreeOff.withTable_same (k := .h5) (Hs := Hb) (Hs' := Hb) (fun _ _ => rfl) enc5
          enc5 G G'
      refine vPre_h5_congr hag CrtGen.tables (withInst st y) b fun x hx => ?_
      rw [hv5 G (withInst st y) (Or.inr ⟨y, rfl⟩)] at hx
      have hx' : x ∈ actInputs base CrtGen.tables (st1 st) s0 t0 :=
        vIn5_proveIdeal2 base st r (kf G3 G) (base.withTable .h5 enc5 G) (hh G3 G) s0 t0 fb hb hk1
          x hx
      simp only [rec5, Hashes.withTable, ↓reduceIte]
      split
      · rename_i hy
        have hk : hy.choose ∈ proverKeysG base CrtGen.tables (st1 st) enc5 (s0, t0) := by
          rw [mem_proverKeysG, hy.choose_spec]; exact hx'
        exact congrArg ba (hG _ (Finset.mem_union_left _ hk))
      · rfl
    have hX : simTab2 Hb CrtGen.tables st (kf G3 G') G'
        (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G) ((s0, t0), fb))
          s0.2.1 G2 =
        simTab2 Hb CrtGen.tables st (kf G3 G) G
          (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G) ((s0, t0), fb))
            s0.2.1 G2 := by
      unfold simTab2
      rw [outPre2_kcongr' Hb CrtGen.tables st G' _ hK, ← hpre]
    show D (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G) ((s0, t0), fb)) G3
        (simTab2 Hb CrtGen.tables st (kf G3 G) G
          (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G3 G) ((s0, t0), fb))
            s0.2.1 G2) G ↔
      D (proveIdeal2 (base.withTable .h5 enc5 G') CrtGen.tables st r (kf G3 G') ((s0, t0), fb)) G3
        (simTab2 Hb CrtGen.tables st (kf G3 G') G'
          (proveIdeal2 (base.withTable .h5 enc5 G') CrtGen.tables st r (kf G3 G') ((s0, t0), fb))
            s0.2.1 G2) G'
    rw [ho', hX]
    exact hQ5 _ G3 _ G G' fun key hk =>
      hG key (Finset.mem_union_right _ (Finset.mem_union_left _ hk))
  have hc : ((q5 + qk5 : ℕ) + 1 : ℝ) / 2 ^ 128 = (q5 + qk5 + 1) / 2 ^ 128 := by push_cast; ring
  rw [← hc]
  exact lab2_hyp base st r enc5 sk (kf G3) (hh G3) hsk hkey fb
    (fun o (s : Shared) G5 => Dp2 Hb CrtGen.tables st (kf G3 G5) D o s.2.1 (G3, G2, G5)) QD hA
    (fun o s G => (card_union_le _ _).trans (add_le_add (hq5 _ _ _ _) (hqk5 _ _ _)))

/-- **The two-phase hybrids after H4** (`zk2_post_h4`), the continuation reading `H₅` at step 1's
output. -/
theorem zk2_post_h4A (hHb : HashesWF Hb) (hh : ∀ G3 G5, Hyp2 st r (kf G3 G5))
    (QK5 : ByteArray × ByteArray → Tab3 → Tab5F → Finset (Bytes 37))
    (hQK5 : ∀ o1 G3 G5 G5', (∀ key ∈ QK5 o1 G3 G5, G5 key = G5' key) → kf G3 G5' o1 = kf G3 G5 o1)
    {qk5 : ℕ} (hqk5 : ∀ o1 G3 G5, (QK5 o1 G3 G5).card ≤ qk5)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q5 : Out2 → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5, (Q5 o G3 G2 G5).card ≤ q5) :
    |pr ((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params)
        (fun c => Dp2 Hb CrtGen.tables st (kf c.2.1 c.2.2.2) D (hyb3' (recB Hb (st1 st) r c.2.1 c.2.2.2)
          CrtGen.tables st r (kf c.2.1 c.2.2.2) c.1.2 (hiddenIdeal (ba (deltaOf c.1.2.1.2)) c.1.1))
          c.1.2.1.2 c.2) -
      pr (SimCoins2 st.params × Vis2 st.params) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.1 c.2.2.2) D (simRun2 Hb st r.size (kf c.2.1 c.2.2.2) c.1)
          c.1.1.1.2.1 c.2)| ≤
      (q5 + qk5 + 1) / 2 ^ 128 := by
  have h5 := zk2_tapeA Hb st r kf D
  have h6 := zk2_h6A Hb st r kf hHb hh QK5 hQK5 hqk5 D Q5 hQ5 hq5
  have h7 := zk2_simA Hb st r kf hh D
  have := abs_sub_le _ _ _ |>.trans (add_le_add h5 ((abs_sub_le _ _ _).trans (add_le_add h6 h7)))
  exact this.trans (le_of_eq (by ring))

end Post

/-! ## H4 in the ideal-cipher model, the continuation reading the cipher at step 1's output -/

section IC

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (K : Tab3 → Tab5F → Cipher → Cont2)

/-- The step-1 output of the hybrid after H4 does not depend on the continuation. -/
lemma hyb3'_o1 [HasPrg] (Hs : Hashes) (T : CrtTables) (k k' : Cont2)
    (b : (Bytes 16 × Grind) × Fallback st.params) (hid : Hidden st.params) :
    ((hyb3' Hs T st r k b hid).1, (hyb3' Hs T st r k b hid).2.1) =
      ((hyb3' Hs T st r k' b hid).1, (hyb3' Hs T st r k' b hid).2.1) := by
  unfold hyb3'
  exact proveIdeal2_o1 Hs T st r k k' _

/-- **The distinguisher's view after the programmed points are recomputed** (two phases), as a
function of the hidden part `o` and the cipher table `E`; the continuation `K G3 G5 E`. -/
noncomputable def viewIC2A (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (E : Cipher) : Prop :=
  @Dp2 (icPrg E) Hb CrtGen.tables st (K v.1 v.2.2 E) (fun o G3 G2 G5 => D o G3 G2 G5 E)
    (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E) ((a, g), fb) o)
    g v

/-- **The keys the two-phase view reads**: the distinguisher's, the honest recomputation's and
the continuation's at the output's step 1. -/
noncomputable def viewKeys2A (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (QKE : ByteArray × ByteArray → Tab3 → Tab5F → Cipher → Finset Blk)
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (E : Cipher) : Finset Blk :=
  QE (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E) ((a, g), fb) o)
      v.1 (@simTab2 (icPrg E) Hb CrtGen.tables st (K v.1 v.2.2 E) v.2.2
        (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
          ((a, g), fb) o) g v.2.1) v.2.2 E ∪
    hRd E (recB Hb (st1 st) r v.1 v.2.2) (st1 st) (a, g, o.1, o.2.1) (deltaOf g) ∪
    QKE ((@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
          ((a, g), fb) o).1,
        (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
          ((a, g), fb) o).2.1) v.1 v.2.2 E

variable {Hb st r K}

/-- **The two-phase view reads the cipher only at `viewKeys2A`.** -/
theorem viewIC2A_congr (hh : ∀ G3 G5 E, Hyp2 st r (K G3 G5 E))
    (QKE : ByteArray × ByteArray → Tab3 → Tab5F → Cipher → Finset Blk)
    (hQKE : ∀ o1 G3 G5 E E', (∀ key ∈ QKE o1 G3 G5 E, E key = E' key) →
      K G3 G5 E' o1 = K G3 G5 E o1)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (E E' : Cipher) (hE : ∀ key ∈ viewKeys2A Hb st r K QE QKE a g fb v o E, E key = E' key) :
    viewIC2A Hb st r K D a g fb v o E ↔ viewIC2A Hb st r K D a g fb v o E' := by
  have hrd : ∀ key ∈ hRd E (recB Hb (st1 st) r v.1 v.2.2) (st1 st) (a, g, o.1, o.2.1) (deltaOf g),
      E key = E' key :=
    fun key hk => hE key (Finset.mem_union_left _ (Finset.mem_union_right _ hk))
  have hout : @hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
      ((a, g), fb) o =
      @hyb3' (icPrg E') (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
        ((a, g), fb) o :=
    hyb3'_ic_congr _ CrtGen.tables st r (K v.1 v.2.2 E) ((a, g), fb) o hrd
  have hK3 : ∀ key ∈ QKE ((@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
        (K v.1 v.2.2 E) ((a, g), fb) o).1,
      (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
        ((a, g), fb) o).2.1) v.1 v.2.2 E, E key = E' key :=
    fun key hk => hE key (Finset.mem_union_right _ hk)
  have hK := hQKE _ v.1 v.2.2 E E' hK3
  have hout' : @hyb3' (icPrg E') (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E')
      ((a, g), fb) o =
      @hyb3' (icPrg E') (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
        ((a, g), fb) o := by
    refine @hyb3'_kcongr (icPrg E') (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r _ _
      ((a, g), fb) o ?_
    have e := @hyb3'_o1 st r (icPrg E') (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables
      (K v.1 v.2.2 E') (K v.1 v.2.2 E) ((a, g), fb) o
    rw [e, ← hout]
    exact hK
  have htab : @simTab2 (icPrg E) Hb CrtGen.tables st (K v.1 v.2.2 E) v.2.2
      (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
        ((a, g), fb) o) g v.2.1 =
      @simTab2 (icPrg E') Hb CrtGen.tables st (K v.1 v.2.2 E') v.2.2
        (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
          ((a, g), fb) o) g v.2.1 := by
    have e0 : @simTab2 (icPrg E') Hb CrtGen.tables st (K v.1 v.2.2 E') v.2.2
        (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
          ((a, g), fb) o) g v.2.1 =
        @simTab2 (icPrg E') Hb CrtGen.tables st (K v.1 v.2.2 E) v.2.2
          (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
            ((a, g), fb) o) g v.2.1 := by
      unfold simTab2
      rw [@outPre2_kcongr' (icPrg E') Hb CrtGen.tables st _ _ v.2.2 _ hK]
    rw [e0]
    unfold simTab2 outPre2
    rcases ho : (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
      (K v.1 v.2.2 E) ((a, g), fb) o).2.2 with _ | e | proof
    · rfl
    · rfl
    rcases hk1 : K v.1 v.2.2 E ((@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
      (K v.1 v.2.2 E) ((a, g), fb) o).1,
      (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
        ((a, g), fb) o).2.1) with _ | ⟨y, sfx⟩
    · rfl
    obtain ⟨hO, hD, hI⟩ := @hyb3'_ok_fields (icPrg E) st r (K v.1 v.2.2 E)
      (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables (hh v.1 v.2.2 E) ((a, g), fb) o proof ho
    have hv : @vPre (icPrg E) (rec5 Hb v.2.2) CrtGen.tables (withInst st y) proof =
        @vPre (icPrg E') (rec5 Hb v.2.2) CrtGen.tables (withInst st y) proof := by
      refine vPre_ic_congr (rec5 Hb v.2.2) CrtGen.tables (withInst st y) proof fun key hk =>
        hrd key ?_
      rw [ivOf, hO, hD, hI, rec5_h4, rec5_mu1] at hk
      rw [hRd, recB, recH_hash_ne (by decide) (by decide) (by decide), recH_mu1]
      exact hk
    simp only [hv]
  have hD3 : ∀ key ∈ QE (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
      (K v.1 v.2.2 E) ((a, g), fb) o) v.1 (@simTab2 (icPrg E) Hb CrtGen.tables st (K v.1 v.2.2 E)
        v.2.2 (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
          ((a, g), fb) o) g v.2.1) v.2.2 E, E key = E' key :=
    fun key hk => hE key (Finset.mem_union_left _ (Finset.mem_union_left _ hk))
  show D (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
        ((a, g), fb) o) v.1
      (@simTab2 (icPrg E) Hb CrtGen.tables st (K v.1 v.2.2 E) v.2.2
        (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
          ((a, g), fb) o) g v.2.1) v.2.2 E ↔
    D (@hyb3' (icPrg E') (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E')
        ((a, g), fb) o) v.1
      (@simTab2 (icPrg E') Hb CrtGen.tables st (K v.1 v.2.2 E') v.2.2
        (@hyb3' (icPrg E') (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E')
          ((a, g), fb) o) g v.2.1) v.2.2 E'
  rw [hout', ← hout, ← htab]
  exact hQE _ _ _ _ _ _ hD3

theorem viewKeys2A_card
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE)
    (QKE : ByteArray × ByteArray → Tab3 → Tab5F → Cipher → Finset Blk) {qkE : ℕ}
    (hqkE : ∀ o1 G3 G5 E, (QKE o1 G3 G5 E).card ≤ qkE)
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (E : Cipher) :
    (viewKeys2A Hb st r K QE QKE a g fb v o E).card ≤ (qE + qkE) + 4607 := by
  unfold viewKeys2A
  refine (card_union_le _ _).trans ?_
  have h1 := card_union_le (QE (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
      (K v.1 v.2.2 E) ((a, g), fb) o) v.1 (@simTab2 (icPrg E) Hb CrtGen.tables st (K v.1 v.2.2 E)
        v.2.2 (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
          ((a, g), fb) o) g v.2.1) v.2.2 E)
    (hRd E (recB Hb (st1 st) r v.1 v.2.2) (st1 st) (a, g, o.1, o.2.1) (deltaOf g))
  have h3 := hqE (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
      (K v.1 v.2.2 E) ((a, g), fb) o) v.1 (@simTab2 (icPrg E) Hb CrtGen.tables st (K v.1 v.2.2 E)
        v.2.2 (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 E)
          ((a, g), fb) o) g v.2.1) v.2.2 E
  have h4 : (hRd E (recB Hb (st1 st) r v.1 v.2.2) (st1 st) (a, g, o.1, o.2.1) (deltaOf g)).card ≤
      4607 := rdKeys_card _ _ _ _
  have h5 := hqkE ((@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
      (K v.1 v.2.2 E) ((a, g), fb) o).1, (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2)
        CrtGen.tables st r (K v.1 v.2.2 E) ((a, g), fb) o).2.1) v.1 v.2.2 E
  omega

variable (Hb st r K)

/-- **H4 in the ideal-cipher model, two phases, the continuation reading the cipher at step 1's
output** (`joint3_h4_2`). -/
theorem joint3_h4_2A (hp : SmallParams st.params) (hh : ∀ G3 G5 E, Hyp2 st r (K G3 G5 E))
    (QKE : ByteArray × ByteArray → Tab3 → Tab5F → Cipher → Finset Blk)
    (hQKE : ∀ o1 G3 G5 E E', (∀ key ∈ QKE o1 G3 G5 E, E key = E' key) →
      K G3 G5 E' o1 = K G3 G5 E o1)
    {qkE : ℕ} (hqkE : ∀ o1 G3 G5 E, (QKE o1 G3 G5 E).card ≤ qkE)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) :
    |pr (((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
          (Tab3 × Tab5F)) × Cipher)
        (fun c => @Dp2 (icPrg c.2) Hb CrtGen.tables st (K c.1.2.1 c.1.2.2 c.2)
          (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
          (@hyb3' (icPrg c.2) (recB Hb (st1 st) r c.1.2.1 c.1.2.2) CrtGen.tables st r
            (K c.1.2.1 c.1.2.2 c.2) ((c.1.1.1.1.2, c.1.1.1.2.2), c.1.1.2)
            (@hiddenOut (icPrg c.2) st.params (ivOfPre Hb (st1 st) c.1.1.1.1.2)
              (ba (deltaOf c.1.1.1.2.2)) c.1.1.1.1.1))
          c.1.1.1.2.2 (c.1.2.1, c.1.1.1.2.1, c.1.2.2)) -
      pr (((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params) ×
          Cipher) (fun c =>
        @Dp2 (icPrg c.2) Hb CrtGen.tables st (K c.1.2.1 c.1.2.2.2 c.2)
          (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
          (@hyb3' (icPrg c.2) (recB Hb (st1 st) r c.1.2.1 c.1.2.2.2) CrtGen.tables st r
            (K c.1.2.1 c.1.2.2.2 c.2) c.1.1.2 (hiddenIdeal (ba (deltaOf c.1.1.2.1.2)) c.1.1.1))
          c.1.1.2.1.2 c.1.2)| ≤
      221 * (4607 + ((qE + qkE : ℕ) + 4607)) / 2 ^ 128 := by
  let E2 : (((Bytes 16 × Grind) × Fallback st.params) × Vis2 st.params) × (Blk × Cipher) ≃
      ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
        (Tab3 × Tab5F)) × Cipher :=
    { toFun := fun c => (((((c.2.1, c.1.1.1.1), (c.1.2.2.1, c.1.1.1.2)), c.1.1.2),
        (c.1.2.1, c.1.2.2.2)), c.2.2)
      invFun := fun c => ((((c.1.1.1.1.2, c.1.1.1.2.2), c.1.1.2), (c.1.2.1, c.1.1.1.2.1, c.1.2.2)),
        (c.1.1.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : (((Bytes 16 × Grind) × Fallback st.params) × Vis2 st.params) ×
      (Hidden st.params × Cipher) ≃
      ((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params) × Cipher :=
    { toFun := fun c => (((c.2.1, c.1.1), c.1.2), c.2.2)
      invFun := fun c => ((c.1.1.2, c.1.2), (c.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E2, ← pr_equiv E3]
  refine abs_pr_prod_sub_le _ _ fun x => ?_
  obtain ⟨⟨⟨a, g⟩, fb⟩, v⟩ := x
  have h := hide_rom_query st.params (ivOfPre Hb (st1 st) a) (ba (deltaOf g)) hp
    (viewIC2A Hb st r K D a g fb v) (viewKeys2A Hb st r K QE QKE a g fb v)
    (fun o E E' hk => viewIC2A_congr hh QKE hQKE D QE hQE a g fb v o E E' hk)
    (viewKeys2A_card QE hqE QKE hqkE a g fb v)
  unfold IC.realPr IC.idealPr at h
  have e : pr (Blk × Cipher) (fun p => viewIC2A Hb st r K D a g fb v
        (hiddenOutE p.2 st.params (ivOfPre Hb (st1 st) a) (ba (deltaOf g)) p.1) p.2) =
      pr (Blk × Cipher) (fun p => viewIC2A Hb st r K D a g fb v
        (@hiddenOut (icPrg p.2) st.params (ivOfPre Hb (st1 st) a) (ba (deltaOf g)) p.1) p.2) :=
    pr_congr fun p => by rw [hiddenOut_ic]
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end IC

/-! ## The end-to-end statement -/

section Main

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (K : Tab3 → Tab5F → Cipher → Cont2)

/-- **Two-phase zero knowledge in the ROM and ideal-cipher model, with a continuation that reads
the tables after step 1** (`zk2_rom_ic_h23` with the continuation `K G3 G5 E` reading the proof's
`H₃` slice, `H₅` and the cipher at `q_k3`, `q_k5`, `q_kE` keys at each step-1 output). The bound is
`zk2_rom_ic_h23`'s with the continuation's reads added to the distinguisher's:

    (q₃ + q_k3)·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + (q_E + q_kE) + 4607)·2⁻¹²⁸
      + ((q₅ + q_k5) + 1)·2⁻¹²⁸. -/
theorem zk2_rom_ic_h23A (hh : ∀ G3 G5 E, Hyp2 st r (K G3 G5 E)) (hHb : HashesWF Hb)
    (hp : SmallParams st.params)
    (QK3 : ByteArray × ByteArray → Tab3 → Tab5F → Cipher → Finset (Bytes 16))
    (hQK3 : ∀ o1 G3 G3' G5 E, (∀ k ∈ QK3 o1 G3 G5 E, G3 k = G3' k) →
      K G3' G5 E o1 = K G3 G5 E o1)
    {qk3 : ℕ} (hqk3 : ∀ o1 G3 G5 E, (QK3 o1 G3 G5 E).card ≤ qk3)
    (QK5 : ByteArray × ByteArray → Tab3 → Tab5F → Cipher → Finset (Bytes 37))
    (hQK5 : ∀ o1 G3 G5 G5' E, (∀ key ∈ QK5 o1 G3 G5 E, G5 key = G5' key) →
      K G3 G5' E o1 = K G3 G5 E o1)
    {qk5 : ℕ} (hqk5 : ∀ o1 G3 G5 E, (QK5 o1 G3 G5 E).card ≤ qk5)
    (QKE : ByteArray × ByteArray → Tab3 → Tab5F → Cipher → Finset Blk)
    (hQKE : ∀ o1 G3 G5 E E', (∀ key ∈ QKE o1 G3 G5 E, E key = E' key) →
      K G3 G5 E' o1 = K G3 G5 E o1)
    {qkE : ℕ} (hqkE : ∀ o1 G3 G5 E, (QKE o1 G3 G5 E).card ≤ qkE)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (Q3 : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 E, (∀ k ∈ Q3 o G3 G2 G5 E, G3 k = G3' k) →
      (D o G3 G2 G5 E ↔ D o G3' G2 G5 E))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 E, (Q3 o G3 G2 G5 E).card ≤ q3)
    (Q5 : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' E, (∀ k ∈ Q5 o G3 G2 G5 E, G5 k = G5' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5' E))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 E, (Q5 o G3 G2 G5 E).card ≤ q5)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@realRun2 (icPrg c.2) (recH Hb (st1 st) r c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st r
          (K c.1.2.1 c.1.2.2 c.2) (ba c.1.1.1)) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins2 st.params × Vis2 st.params) × Cipher) (fun c =>
        D (@simRun2 (icPrg c.2) Hb st r.size (K c.1.2.1 c.1.2.2.2 c.2) c.1.1) c.1.2.1
          (@simTab2 (icPrg c.2) Hb CrtGen.tables st (K c.1.2.1 c.1.2.2.2 c.2) c.1.2.2.2
            (@simRun2 (icPrg c.2) Hb st r.size (K c.1.2.1 c.1.2.2.2 c.2) c.1.1) c.1.1.1.1.2.1
              c.1.2.2.1)
          c.1.2.2.2 c.2)| ≤
      (q3 + qk3) / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) +
        221 * (4607 + ((qE + qkE : ℕ) + 4607)) / 2 ^ 128 + ((q5 + qk5 : ℕ) + 1) / 2 ^ 128 := by
  have hA := abs_pr_avgE
    (fun (c : (Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (E : Cipher) =>
      D (@realRun2 (icPrg E) (recH Hb (st1 st) r c.2.1 c.1.2 c.2.2) CrtGen.tables st r
        (K c.2.1 c.2.2 E) (ba c.1.1)) c.2.1 c.1.2 c.2.2 E)
    (fun (c : (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
        (Tab3 × Tab5F)) (E : Cipher) =>
      @Dp2 (icPrg E) Hb CrtGen.tables st (K c.2.1 c.2.2 E) (fun o G3 G2 G5 => D o G3 G2 G5 E)
        (@hyb3' (icPrg E) (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (K c.2.1 c.2.2 E)
          ((c.1.1.1.2, c.1.1.2.2), c.1.2)
          (@hiddenOut (icPrg E) st.params (ivOfPre Hb (st1 st) c.1.1.1.2) (ba (deltaOf c.1.1.2.2))
            c.1.1.1.1))
        c.1.1.2.2 (c.2.1, c.1.1.2.1, c.2.2))
    (fun E => @zk2_pre_h4A (icPrg E) Hb st r (fun G3 G5 => K G3 G5 E) hHb (fun G3 G5 => hh G3 G5 E)
      (fun o1 G3 G5 => QK3 o1 G3 G5 E) (fun o1 G3 G3' G5 => hQK3 o1 G3 G3' G5 E) qk3
      (fun o1 G3 G5 => hqk3 o1 G3 G5 E)
      (fun o G3 G2 G5 => D o G3 G2 G5 E)
      (fun o G3 G2 G5 => Q3 o G3 G2 G5 E) (fun o G3 G3' G2 G5 => hQ3 o G3 G3' G2 G5 E) q3
      (fun o G3 G2 G5 => hq3 o G3 G2 G5 E))
  have hB := joint3_h4_2A Hb st r K hp hh QKE hQKE hqkE D QE hQE hqE
  have hC := abs_pr_avgE
    (fun (c : (Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params)
        (E : Cipher) =>
      @Dp2 (icPrg E) Hb CrtGen.tables st (K c.2.1 c.2.2.2 E) (fun o G3 G2 G5 => D o G3 G2 G5 E)
        (@hyb3' (icPrg E) (recB Hb (st1 st) r c.2.1 c.2.2.2) CrtGen.tables st r (K c.2.1 c.2.2.2 E)
          c.1.2 (hiddenIdeal (ba (deltaOf c.1.2.1.2)) c.1.1)) c.1.2.1.2 c.2)
    (fun (c : SimCoins2 st.params × Vis2 st.params) (E : Cipher) =>
      D (@simRun2 (icPrg E) Hb st r.size (K c.2.1 c.2.2.2 E) c.1) c.2.1
        (@simTab2 (icPrg E) Hb CrtGen.tables st (K c.2.1 c.2.2.2 E) c.2.2.2
          (@simRun2 (icPrg E) Hb st r.size (K c.2.1 c.2.2.2 E) c.1) c.1.1.1.2.1 c.2.2.1) c.2.2.2 E)
    (fun E => @zk2_post_h4A (icPrg E) Hb st r (fun G3 G5 => K G3 G5 E) hHb
      (fun G3 G5 => hh G3 G5 E)
      (fun o1 G3 G5 => QK5 o1 G3 G5 E) (fun o1 G3 G5 G5' => hQK5 o1 G3 G5 G5' E) qk5
      (fun o1 G3 G5 => hqk5 o1 G3 G5 E)
      (fun o G3 G2 G5 => D o G3 G2 G5 E)
      (fun o G3 G2 G5 => Q5 o G3 G2 G5 E) (fun o G3 G2 G5 G5' => hQ5 o G3 G2 G5 G5' E) q5
      (fun o G3 G2 G5 => hq5 o G3 G2 G5 E))
  refine (abs_sub_le _ _ _).trans ((add_le_add hA ((abs_sub_le _ _ _).trans
    (add_le_add hB hC))).trans (le_of_eq (by push_cast; ring)))

/-- **`zk2_rom_ic_h23A` with `Pr[GrindBad] ≤ 2⁻¹¹³`**: the error is
`εRO (q₃ + q_k3) (q₅ + q_k5) (q_E + q_kE)`. -/
theorem zk2_rom_ic_h23A_num (hh : ∀ G3 G5 E, Hyp2 st r (K G3 G5 E)) (hHb : HashesWF Hb)
    (hp : SmallParams st.params)
    (QK3 : ByteArray × ByteArray → Tab3 → Tab5F → Cipher → Finset (Bytes 16))
    (hQK3 : ∀ o1 G3 G3' G5 E, (∀ k ∈ QK3 o1 G3 G5 E, G3 k = G3' k) →
      K G3' G5 E o1 = K G3 G5 E o1)
    {qk3 : ℕ} (hqk3 : ∀ o1 G3 G5 E, (QK3 o1 G3 G5 E).card ≤ qk3)
    (QK5 : ByteArray × ByteArray → Tab3 → Tab5F → Cipher → Finset (Bytes 37))
    (hQK5 : ∀ o1 G3 G5 G5' E, (∀ key ∈ QK5 o1 G3 G5 E, G5 key = G5' key) →
      K G3 G5' E o1 = K G3 G5 E o1)
    {qk5 : ℕ} (hqk5 : ∀ o1 G3 G5 E, (QK5 o1 G3 G5 E).card ≤ qk5)
    (QKE : ByteArray × ByteArray → Tab3 → Tab5F → Cipher → Finset Blk)
    (hQKE : ∀ o1 G3 G5 E E', (∀ key ∈ QKE o1 G3 G5 E, E key = E' key) →
      K G3 G5 E' o1 = K G3 G5 E o1)
    {qkE : ℕ} (hqkE : ∀ o1 G3 G5 E, (QKE o1 G3 G5 E).card ≤ qkE)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (Q3 : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 E, (∀ k ∈ Q3 o G3 G2 G5 E, G3 k = G3' k) →
      (D o G3 G2 G5 E ↔ D o G3' G2 G5 E))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 E, (Q3 o G3 G2 G5 E).card ≤ q3)
    (Q5 : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' E, (∀ k ∈ Q5 o G3 G2 G5 E, G5 k = G5' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5' E))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 E, (Q5 o G3 G2 G5 E).card ≤ q5)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@realRun2 (icPrg c.2) (recH Hb (st1 st) r c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st r
          (K c.1.2.1 c.1.2.2 c.2) (ba c.1.1.1)) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins2 st.params × Vis2 st.params) × Cipher) (fun c =>
        D (@simRun2 (icPrg c.2) Hb st r.size (K c.1.2.1 c.1.2.2.2 c.2) c.1.1) c.1.2.1
          (@simTab2 (icPrg c.2) Hb CrtGen.tables st (K c.1.2.1 c.1.2.2.2 c.2) c.1.2.2.2
            (@simRun2 (icPrg c.2) Hb st r.size (K c.1.2.1 c.1.2.2.2 c.2) c.1.1) c.1.1.1.1.2.1
              c.1.2.2.1)
          c.1.2.2.2 c.2)| ≤
      εRO (q3 + qk3) (q5 + qk5) (qE + qkE) := by
  refine (zk2_rom_ic_h23A Hb st r K hh hHb hp QK3 hQK3 hqk3 QK5 hQK5 hqk5 QKE hQKE hqkE D Q3 hQ3
    hq3 Q5 hQ5 hq5 QE hQE hqE).trans ?_
  have := grindBad_le_113
  unfold εRO
  push_cast
  linarith

end Main

/-! ## In the form of the games -/

/-- **The hypotheses on a two-phase instance whose continuation reads the tables after step 1**:
`K g s` is the continuation on the proof's `H₃` slice `g` and the shared tables `s`. For every
value, the deterministic hypotheses hold; `|r| = n`; `K` does not read `H₂³`; at each step-1
output `o₁`, `K · · o₁` reads the slice at `qk3` keys, `H₅` at `qk5` and the cipher at `qkE` keys
(each with the other tables fixed). -/
structure Hyp2RA {R : Type} (st : Statement) (r : ByteArray) (n : ℕ) (K : Tab3 → ShG R st.params → Cont2)
    (qk3 qk5 qkE : ℕ) : Prop where
  hyp : ∀ g s, Hyp2 st r (K g s)
  size : r.size = n
  h2 : ∀ g (s : ShG R st.params) (G2 : Tab2G st.params), K g (G2, s.2) = K g s
  h3 : ∀ o1 (s : ShG R st.params), Rd3 (fun g => K g s o1) qk3
  h5 : ∀ o1 g, Rd5 (fun s => K g s o1) qk5
  hE : ∀ o1 g, RdE (fun s => K g s o1) qkE

lemma Hyp2RA.mono {R : Type} {st : Statement} {r : ByteArray} {n : ℕ}
    {K : Tab3 → ShG R st.params → Cont2}
    {qk3 qk5 qkE qk3' qk5' qkE' : ℕ} (h : Hyp2RA st r n K qk3 qk5 qkE) (h3 : qk3 ≤ qk3')
    (h5 : qk5 ≤ qk5') (hE : qkE ≤ qkE') : Hyp2RA st r n K qk3' qk5' qkE' :=
  ⟨h.hyp, h.size, h.h2, fun o1 s => (h.h3 o1 s).mono h3, fun o1 g => (h.h5 o1 g).mono h5,
    fun o1 g => (h.hE o1 g).mono hE⟩

section ZKA

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ) (K : Tab3 → Sh st.params → Cont2)

/-- **`zk2_adaptive`: two-phase zero knowledge with a continuation that reads the tables after
step 1** (ROM and ideal cipher, the tables visible). The real two-phase prover `realRO2` and the
simulator with its programming `simRO2`, `progRO2`, the continuation at the proof's slice and the
(unprogrammed) shared tables, are `εRO (q₃ + qk3) (q₅ + qk5) (q_E + qkE)`-close against a
distinguisher with budget `(q₃, q₅, q_E)` (`H₂³` free). -/
theorem zk2_adaptive {qk3 qk5 qkE : ℕ} (hh : Hyp2RA st r n K qk3 qk5 qkE) (hHb : HashesWF Hb)
    (hp : SmallParams st.params) {q3 q5 qE : ℕ} (D : Out2 → Tab3 → Sh st.params → Prop)
    (hD : Budget st.params q3 q5 qE D) :
    |pr ((Bytes 16 × Tab3) × Sh st.params) (fun a =>
        D (realRO2 Hb st r (K a.1.2) a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((SimCoins2 st.params × Tab3) × Sh st.params) (fun a =>
        D (simRO2 Hb st n (K a.1.2) a.1.1 a.2) a.1.2 (progRO2 Hb st n (K a.1.2) a.1.1 a.2))| ≤
      εRO (q3 + qk3) (q5 + qk5) (qE + qkE) := by
  choose Q3 hQ3c hQ3 using hD.h3
  choose Q5 hQ5c hQ5 using hD.h5
  choose QE hQEc hQE using hD.hE
  obtain ⟨K', hKf⟩ : ∃ K' : Tab3 → Tab5F → Cipher → Cont2, K = fun g s => K' g s.2.1 s.2.2 :=
    ⟨fun g G5 E => K g (fun _ => 0, G5, E), funext fun g => funext fun s => (hh.h2 g s fun _ => 0).symm⟩
  subst hKf
  choose QK3 hQK3c hQK3 using hh.h3
  choose QK5 hQK5c hQK5 using hh.h5
  choose QKE hQKEc hQKE using hh.hE
  have hr : r.size = n := hh.size
  subst hr
  have key := zk2_rom_ic_h23A_num Hb st r K' (fun G3 G5 E => hh.hyp G3 (fun _ => 0, G5, E)) hHb hp
    (fun o1 G3 G5 E => QK3 o1 (fun _ => 0, G5, E) G3)
    (fun o1 G3 G3' G5 E hk => hQK3 o1 (fun _ => 0, G5, E) G3 G3' hk)
    (fun o1 G3 G5 E => hQK3c o1 _ G3)
    (fun o1 G3 G5 E => QK5 o1 G3 (fun _ => 0, G5, E))
    (fun o1 G3 G5 G5' E hk => hQK5 o1 G3 (fun _ => 0, G5, E) G5' hk)
    (fun o1 G3 G5 E => hQK5c o1 G3 _)
    (fun o1 G3 G5 E => QKE o1 G3 (fun _ => 0, G5, E))
    (fun o1 G3 G5 E E' hk => hQKE o1 G3 (fun _ => 0, G5, E) E' hk)
    (fun o1 G3 G5 E => hQKEc o1 G3 _)
    (fun o G3 G2 G5 E => D o G3 (G2, G5, E))
    (fun o G3 G2 G5 E => Q3 o (G2, G5, E) G3)
    (fun o G3 G3' G2 G5 E hk => Iff.of_eq (hQ3 o (G2, G5, E) G3 G3' hk).symm)
    (fun o G3 G2 G5 E => hQ3c o (G2, G5, E) G3)
    (fun o G3 G2 G5 E => Q5 o G3 (G2, G5, E))
    (fun o G3 G2 G5 G5' E hk => Iff.of_eq (hQ5 o G3 (G2, G5, E) G5' hk).symm)
    (fun o G3 G2 G5 E => hQ5c o G3 (G2, G5, E))
    (fun o G3 G2 G5 E => QE o G3 (G2, G5, E))
    (fun o G3 G2 G5 E E' hk => Iff.of_eq (hQE o G3 (G2, G5, E) E' hk).symm)
    (fun o G3 G2 G5 E => hQEc o G3 (G2, G5, E))
  let e1 : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher ≃
      (Bytes 16 × Tab3) × Sh st.params :=
    { toFun := fun c => ((c.1.1.1, c.1.2.1), (c.1.1.2, c.1.2.2, c.2))
      invFun := fun c => (((c.1.1, c.2.1), (c.1.2, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (SimCoins2 st.params × Vis2 st.params) × Cipher ≃
      (SimCoins2 st.params × Tab3) × Sh st.params :=
    { toFun := fun c => ((c.1.1, c.1.2.1), (c.1.2.2.1, c.1.2.2.2, c.2))
      invFun := fun c => ((c.1.1, (c.1.2, c.2.1, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e1, ← pr_equiv e2]
  exact key

end ZKA

/-! ## For a type of cipher rows -/

/-- **Two-phase zero knowledge with a continuation that reads the tables after step 1, for a type
of cipher rows**: `zk2_adaptive` for the shared tables `ShG R p`, error `ZKRow.εz` at the
distinguisher's budget plus the continuation's reads. Function rows: `zk2_adaptive`
(`ZK2ARow.fn`); permutation rows: `ZK/TwoPhasePerm.lean`. -/
class ZK2ARow (R : Type) [Fintype R] [CipherRow R] [ZKRow R] where
  /-- `zk2_adaptive` with this row type. -/
  zk2A : ∀ (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ)
    (K : Tab3 → ShG R st.params → Cont2) {qk3 qk5 qkE : ℕ}, Hyp2RA st r n K qk3 qk5 qkE →
    HashesWF Hb → SmallParams st.params → ∀ {q3 q5 qE : ℕ}
    (D : Out2 → Tab3 → ShG R st.params → Prop), Budget st.params q3 q5 qE D →
    |pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        D (realRO2 Hb st r (K a.1.2) a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((SimCoins2 st.params × Tab3) × ShG R st.params) (fun a =>
        D (simRO2 Hb st n (K a.1.2) a.1.1 a.2) a.1.2 (progRO2 Hb st n (K a.1.2) a.1.1 a.2))| ≤
      ZKRow.εz R st.params (q3 + qk3) (q5 + qk5) (qE + qkE)

/-- **Function rows**: `zk2_adaptive`. -/
instance ZK2ARow.fn : ZK2ARow (Blk → Blk) where
  zk2A Hb st r n K _ _ _ hh hHb hp _ _ _ D hD := zk2_adaptive Hb st r n K hh hHb hp D hD

end VoleMole.ZK.Sim
