import VoleMole.ZK.MainSharedN
import VoleMole.ZK.MainSharedSim

/-!
# The bad event of the `n`-proof joint hop on simulated proofs (`lean/docs/zk.md` §4.2)

`main_sharedAll_leN` (`ZK/MainSharedN.lean`) leaves `Pr[bstarN]` in the hybrid with all `n` proofs
simulated. This file is `bstar_sim` and its probability terms (`ZK/MainSharedSim.lean`) for `n`
slots:

* **`bstarN_sim`**: on simulated proofs `bstarN` is a failed simulation, a prediction of some
  slot's witness prefix from the public key set `SpN` (the event's `H₅` read set and the `n` proofs'
  active gate inputs; `candO`), or a sibling gate input of an earlier proof that is a sibling gate
  input of a later one.
* **`pr_bstarN_sim_le`**:

      Pr[all simulated; bstarN] ≤ n·noHitProb + Σᵢ Pr[candOᵢ] + n²·313·2⁻¹²⁸.

  A failed simulation is `noHitProb` per slot (`pr_errC_le`); a collision of two simulated proofs'
  sibling inputs is `313·2⁻¹²⁸` per pair (`pr_sib_hit_le`: the later proof's field `d` is uniform
  and independent of the earlier proof and of the later proof's statement). The prediction terms
  are the (PU) terms of the game.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

attribute [local instance] decEqW128
attribute [local irreducible] simulate realRO progRO realKeys5 realKeysE progKeys5 progKeysE

section Sim

variable (Hb : Hashes) (p₀ : Params) {n : ℕ} (ns : Fin n → ℕ) {S : Type} (G : NGame S n)

/-- **The outputs of the all-simulated hybrid**: slot `i` outputs its simulation iff it has a
statement. -/
lemma os_simN (x : NTape p₀ ns S) (i : Fin n) :
    (hybVN Hb p₀ ns G n x).os i =
      (yN G i (hybVN Hb p₀ ns G n x)).map fun _ => simulate (pw p₀ (ns i)) (x.2.1 i).2 := by
  unfold hybVN
  rw [os_viewN, yN_viewN]
  unfold sfN
  have e : modeF Hb p₀ ns n x.2.1 x.2.2.1 x.2.2.2.1 i
      (stN G x.1 (modeF Hb p₀ ns n x.2.1 x.2.2.1 x.2.2.2.1) x.2.2.2.2 i) =
      simF Hb p₀ ns i (x.2.1 i).2 x.2.2.2.1
        (stN G x.1 (modeF Hb p₀ ns n x.2.1 x.2.2.1 x.2.2.2.1) x.2.2.2.2 i) := by
    simp only [modeF, i.2, ↓reduceIte]
  rw [e]
  rfl

/-- **The public key set of the all-simulated hybrid**: the event's `H₅` read set and the `n`
proofs' active gate inputs. -/
noncomputable def SpN (R5 : NView S n p₀ → Finset (Bytes 37)) (x : NTape p₀ ns S) :
    Finset (Bytes 37) :=
  R5 (hybVN Hb p₀ ns G n x) ∪ univ.biUnion fun i : Fin n =>
    (actO Hb (pw p₀ (ns i)) (qOf (yN G i (hybVN Hb p₀ ns G n x))) x.2.2.2.1.2
      (x.2.1 i).2).toFinset.image (blk 37)

/-- Slot `i`'s witness prefix is a candidate of the public key set, on its simulated proof. -/
def candN (R5 : NView S n p₀ → Finset (Bytes 37)) (i : Fin n) (x : NTape p₀ ns S) : Prop :=
  candO Hb (qOf (yN G i (hybVN Hb p₀ ns G n x))) x.2.2.2.1.2 (x.2.1 i).2 (SpN Hb p₀ ns G R5 x)

/-- A sibling gate input of slot `i`'s simulated proof is one of slot `m`'s. -/
def collN (i m : Fin n) (x : NTape p₀ ns S) : Prop :=
  ∃ z ∈ sibO Hb (pw p₀ (ns i)) (qOf (yN G i (hybVN Hb p₀ ns G n x))) x.2.2.2.1.2 (x.2.1 i).2,
    z ∈ sibO Hb (pw p₀ (ns m)) (qOf (yN G m (hybVN Hb p₀ ns G n x))) x.2.2.2.1.2 (x.2.1 m).2

set_option maxRecDepth 8000 in
/-- **`bstarN` on simulated proofs**: a failed simulation, a prediction from the public key set,
or a collision of an earlier proof's sibling input with a later proof's. -/
theorem bstarN_sim (hHb : HashesWF Hb) (R5 : NView S n p₀ → Finset (Bytes 37))
    (x : NTape p₀ ns S) (h : bstarN Hb G (fun i => pw p₀ (ns i)) R5 (hybVN Hb p₀ ns G n x)) :
    (∃ i, errC (pw p₀ (ns i)) (x.2.1 i).2) ∨ (∃ i, candN Hb p₀ ns G R5 i x) ∨
      ∃ m i : Fin n, i < m ∧ collN Hb p₀ ns G i m x := by
  classical
  set v := hybVN Hb p₀ ns G n x with hv
  have hos := os_simN Hb p₀ ns G x
  have hu : v.u = x.2.2.2.1 := rfl
  have hR : R5 v ⊆ SpN Hb p₀ ns G R5 x := subset_union_left
  have hA : ∀ i : Fin n, (actO Hb (pw p₀ (ns i)) (qOf (yN G i v)) x.2.2.2.1.2
      (x.2.1 i).2).toFinset.image (blk 37) ⊆ SpN Hb p₀ ns G R5 x := fun i k hk =>
    mem_union_right _ (mem_biUnion.2 ⟨i, mem_univ _, hk⟩)
  rcases h with ⟨i, he⟩ | ⟨j, hz | ⟨k, hk, hhit⟩⟩
  · rw [hos] at he
    exact Or.inl ⟨i, slotErr_simO _ _ he⟩
  · rw [hos, slotZero_simO] at hz
    exact Or.inr (Or.inl ⟨j, candO_of_zero Hb hz⟩)
  · rw [hos, hu, slotHit_simO] at hhit
    rcases mem_union.1 hk with hk | hk
    · exact Or.inr (Or.inl ⟨j, candO_of_key Hb ⟨k, hR hk, hhit⟩⟩)
    · obtain ⟨m, hm, hkm⟩ := mem_biUnion.1 hk
      have hmj : m ≠ j := (mem_filter.1 hm).2
      rw [hos, hu, slotKeys_simO] at hkm
      rcases mem_union.1 hkm with ha | hs
      · exact Or.inr (Or.inl ⟨j, candO_of_key Hb ⟨k, hA m ha, hhit⟩⟩)
      · obtain ⟨z, hz, rfl⟩ := mem_image.1 hs
        rw [List.mem_toFinset] at hz
        have hz' : enc5 (blk 37 z) = z := ba_blk_of_size (sibO_size Hb hHb _ _ _ hz)
        rw [hz'] at hhit
        rcases lt_or_gt_of_ne hmj with hlt | hlt
        · exact Or.inr (Or.inr ⟨j, m, hlt, z, hz, hhit⟩)
        · exact Or.inr (Or.inr ⟨m, j, hlt, z, hhit, hz⟩)

/-! ## Resampling one slot's coins -/

/-- The tape with slot `m`'s coins replaced. -/
def setC (m : Fin n) (x : NTape p₀ ns S) (k : Bytes 16 × SimCoins (pw p₀ (ns m))) :
    NTape p₀ ns S :=
  (x.1, Function.update x.2.1 m k, x.2.2)

theorem pr_setC [Fintype S] (m : Fin n) (Φ : NTape p₀ ns S → Prop) :
    pr (NTape p₀ ns S × (Bytes 16 × SimCoins (pw p₀ (ns m)))) (fun z => Φ (setC p₀ ns m z.1 z.2)) =
      pr (NTape p₀ ns S) Φ :=
  pr_lens (fun x => x.2.1 m) (setC p₀ ns m) (fun x k => by simp [setC])
    (fun x => by simp [setC]) (fun x k k' => by simp [setC]) Φ

/-- **The statements of the all-simulated hybrid up to slot `m` do not depend on slot `m`'s
coins.** -/
lemma yN_setC (m : Fin n) (x : NTape p₀ ns S) (k : Bytes 16 × SimCoins (pw p₀ (ns m)))
    (i : Fin n) (hi : i ≤ m) :
    yN G i (hybVN Hb p₀ ns G n (setC p₀ ns m x k)) = yN G i (hybVN Hb p₀ ns G n x) := by
  unfold hybVN
  rw [yN_viewN, yN_viewN]
  unfold stN setC
  congr 1
  exact preRun_fst_eq Hb p₀ ns G n n i i.2.le i.2.le i.2.le x.1 _ _ _ _ _ _ _ _ fun l hl => by
    show (x.2.1 l).2 = (Function.update x.2.1 m k l).2
    rw [Function.update_of_ne (fun h => by rw [h] at hl; exact absurd hl (not_lt.2 hi))]

/-- A bound on a slot's coins `Bytes 16 × SimCoins p` from a bound with the field `d`
separated. -/
theorem pr_K_d_le {p : Params} (P : Bytes 16 × SimCoins p → Prop) {ε : ℝ}
    (h : ∀ (ρ : Bytes 16) (sh : Shared) (c₁ : Bytes (16 * p.correctionBytes))
      (c₂ : Bytes (p.nMask * p.nMultBytes)) (c₃ : Bytes 64) (c₅ : Bytes (16 * (p.qsDegree - 1))),
      pr (Bytes p.witnessBytes) (fun d => P (ρ, (sh, (c₁, c₂, c₃, d, c₅)))) ≤ ε) :
    pr (Bytes 16 × SimCoins p) P ≤ ε := by
  rw [← pr_prod_fst (β := VP p) P]
  exact pr_KS_d_le (fun k : KS p => P k.1) fun ρ sh c₁ c₂ c₃ c₅ _ => h ρ sh c₁ c₂ c₃ c₅

variable [Fintype S] [Nonempty S]

/-- **A simulation fails with probability `noHitProb`**, in every slot. -/
theorem pr_errN_le (i : Fin n) :
    pr (NTape p₀ ns S) (fun x => errC (pw p₀ (ns i)) (x.2.1 i).2) ≤ noHitProb := by
  rw [← pr_setC p₀ ns i]
  refine pr_le_of_fst fun x => ?_
  have e : ∀ k : Bytes 16 × SimCoins (pw p₀ (ns i)),
      errC (pw p₀ (ns i)) ((setC p₀ ns i x k).2.1 i).2 ↔ errC (pw p₀ (ns i)) k.2 := fun k => by
    simp [setC]
  rw [pr_congr e, ← pr_prod_fst (β := VP (pw p₀ (ns i)))
    (fun k : Bytes 16 × SimCoins (pw p₀ (ns i)) => errC (pw p₀ (ns i)) k.2)]
  exact pr_errC_le

/-- **Two simulated proofs' sibling inputs collide with probability `≤ 313·2⁻¹²⁸`**: the later
proof's field `d` is uniform and independent of the earlier proof and of the statements. -/
theorem pr_collN_le (hv : NValid G p₀ ns) (i m : Fin n) (him : i < m) :
    pr (NTape p₀ ns S) (collN Hb p₀ ns G i m) ≤ ((312 : ℕ) + 1) / 2 ^ 128 := by
  rw [← pr_setC p₀ ns m]
  refine pr_le_of_fst fun x => ?_
  have hci : ∀ k, ((setC p₀ ns m x k).2.1 i).2 = (x.2.1 i).2 := fun k => by
    simp only [setC]
    rw [Function.update_of_ne (ne_of_lt him)]
  have hcm : ∀ k, ((setC p₀ ns m x k).2.1 m).2 = k.2 := fun k => by
    simp only [setC, Function.update_self]
  set qi := qOf (yN G i (hybVN Hb p₀ ns G n x)) with hqi
  set qm := qOf (yN G m (hybVN Hb p₀ ns G n x)) with hqm
  have e : ∀ k, collN Hb p₀ ns G i m (setC p₀ ns m x k) ↔
      ∃ z ∈ sibO Hb (pw p₀ (ns i)) qi x.2.2.2.1.2 (x.2.1 i).2,
        z ∈ sibO Hb (pw p₀ (ns m)) qm x.2.2.2.1.2 k.2 := fun k => by
    unfold collN
    rw [yN_setC Hb p₀ ns G m x k i him.le, yN_setC Hb p₀ ns G m x k m le_rfl, hci, hcm]
    rfl
  rw [pr_congr e]
  rcases hq : qm with _ | ⟨st, r⟩
  · refine le_of_eq_of_le (pr_congr (Q := fun _ => False) fun k => by simp [sibO]) ?_
    rw [pr_false]; positivity
  · refine pr_K_d_le _ fun ρ sh c₁ c₂ c₃ c₅ => ?_
    exact pr_sib_hit_le Hb (hv.m m) st x.2.2.2.1.2 sh c₁ c₂ c₃ c₅ r _
      (sibO_length_le Hb _ _ _)

/-- **The bad event with all `n` proofs simulated**: failed simulations, the predictions, and
the collisions of sibling inputs. -/
theorem pr_bstarN_sim_le (hHb : HashesWF Hb) (hv : NValid G p₀ ns)
    (R5 : NView S n p₀ → Finset (Bytes 37)) :
    hybN Hb p₀ ns G n (bstarN Hb G (fun i => pw p₀ (ns i)) R5) ≤
      n * noHitProb + ∑ i, pr (NTape p₀ ns S) (candN Hb p₀ ns G R5 i) +
        n * n * (((312 : ℕ) + 1) / 2 ^ 128) := by
  classical
  have h1 : hybN Hb p₀ ns G n (bstarN Hb G (fun i => pw p₀ (ns i)) R5) ≤
      pr (NTape p₀ ns S) (fun x => (∃ i, errC (pw p₀ (ns i)) (x.2.1 i).2) ∨
        (∃ i, candN Hb p₀ ns G R5 i x) ∨
        ∃ m i : Fin n, if i < m then collN Hb p₀ ns G i m x else False) :=
    pr_mono fun x hx => by
      rcases bstarN_sim Hb p₀ ns G hHb R5 x hx with h | h | ⟨m, i, him, hc⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨m, i, by simp only [him, ↓reduceIte]; exact hc⟩)
  have hA : pr (NTape p₀ ns S) (fun x => ∃ i, errC (pw p₀ (ns i)) (x.2.1 i).2) ≤
      n * noHitProb := by
    refine (pr_exists_le_sum _).trans ?_
    calc ∑ i : Fin n, pr (NTape p₀ ns S) (fun x => errC (pw p₀ (ns i)) (x.2.1 i).2)
        ≤ ∑ _i : Fin n, noHitProb := sum_le_sum fun i _ => pr_errN_le p₀ ns i
      _ = n * noHitProb := by simp
  have hB : pr (NTape p₀ ns S) (fun x => ∃ i, candN Hb p₀ ns G R5 i x) ≤
      ∑ i, pr (NTape p₀ ns S) (candN Hb p₀ ns G R5 i) := pr_exists_le_sum _
  have hC : pr (NTape p₀ ns S) (fun x => ∃ m i : Fin n,
      if i < m then collN Hb p₀ ns G i m x else False) ≤
      n * n * (((312 : ℕ) + 1) / 2 ^ 128) := by
    refine (pr_exists_le_sum _).trans ?_
    calc ∑ m : Fin n, pr (NTape p₀ ns S) (fun x => ∃ i : Fin n,
          if i < m then collN Hb p₀ ns G i m x else False)
        ≤ ∑ _m : Fin n, ∑ _i : Fin n, (((312 : ℕ) + 1) / 2 ^ 128 : ℝ) :=
          sum_le_sum fun m _ => (pr_exists_le_sum _).trans (sum_le_sum fun i _ => by
            by_cases him : i < m
            · simp only [him, ↓reduceIte]
              exact pr_collN_le Hb p₀ ns G hv i m him
            · simp only [him, ↓reduceIte]
              rw [pr_false]; positivity)
      _ = n * n * (((312 : ℕ) + 1) / 2 ^ 128) := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h2 := pr_or_le (α := NTape p₀ ns S) (fun x => ∃ i, errC (pw p₀ (ns i)) (x.2.1 i).2)
    (fun x => (∃ i, candN Hb p₀ ns G R5 i x) ∨
      ∃ m i : Fin n, if i < m then collN Hb p₀ ns G i m x else False)
  have h3 := pr_or_le (α := NTape p₀ ns S) (fun x => ∃ i, candN Hb p₀ ns G R5 i x)
    (fun x => ∃ m i : Fin n, if i < m then collN Hb p₀ ns G i m x else False)
  linarith

end Sim

end VoleMole.ZK.Sim
