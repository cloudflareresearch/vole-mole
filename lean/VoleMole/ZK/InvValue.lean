import VoleMole.ZK.InvPoint
import VoleMole.ZK.IdealCipherPtPerm

/-!
# The counterexample of `ZK/InvPoint.lean` under the value charge

`inv_point_charge_fails` shows that a point charge (keys read at the proof's points) does not
bound a distinguisher that inverse-queries a revealed value `y` under `q` keys: the advantage is
about `q/n`, the point charge about `q/n` too, so the point-level bound is about `q/n²`.

The permutation-row hop (`IC.puncturePtPm_real`, `ZK/IdealCipherPtPerm.lean`) charges a read also
when its **value** is a value of the secret rows at their points (`IC.vkeys`, `IC.valsP`). Here:

* `qInv_vkeys`: every inverse query at a charged value is charged, so `qInv`'s charge is `q`
  (all of `S`), not about `q/n`;
* `inv_vcharge_eq`: in the counterexample's real experiment, `E_real[chV] = q` exactly;
* `inv_vbound`: `IC.puncturePtPm_real` applies to the counterexample (its hypotheses hold) and
  gives `|real − replaced| ≤ (1 + q + 3)/(n − q)`, which is consistent with the advantage
  `≥ (q/n)·(1 − q/n)` of `inv_adv_ge` (the replaced experiment there has a permutation row at the
  root, here a function row; the real experiment is the same).
-/

open Finset

namespace VoleMole.ZK.IC

open VoleMole.Privacy

section InvValue

variable {K : Type} [Fintype K] [DecidableEq K] [Nonempty K]

omit [Fintype K] [Nonempty K] in
/-- **An inverse query at a charged value is charged**: the charge of `qInv` at a value `y ∈ V` is
all of `S`. -/
theorem qInv_vkeys (P : K → Prop) [DecidablePred P] (S : Finset K) {y : K} {V : Finset K}
    (hy : y ∈ V) (π : K → Equiv.Perm K) : vkeys P V (qInv S y π) π = S := by
  ext k
  simp only [vkeys, qInv, mem_image, mem_filter]
  constructor
  · rintro ⟨kz, ⟨⟨k', hk', rfl⟩, -⟩, rfl⟩
    exact hk'
  · intro hk
    refine ⟨(k, (π k).symm y), ⟨⟨k, hk, rfl⟩, Or.inr ?_⟩, rfl⟩
    simp only [Equiv.apply_symm_apply]
    exact hy

/-- The inputs charged in the counterexample: `z₀` and the tree's inputs. -/
def pInv (x : ℕ → K) (z0 : K) (z : K) : Prop := z = z0 ∨ ∃ m, x m = z

noncomputable instance (x : ℕ → K) (z0 : K) : DecidablePred (pInv x z0) := Classical.decPred _

/-- The root's points: `z₀` and its children's inputs. -/
def pnInv (x : ℕ → K) (z0 : K) (m : ℕ) : Finset K := {z0, x (2 * m + 1), x (2 * m + 2)}

/-- **The value charge of `qInv` is `q`**: in the counterexample's real experiment (one secret
node, the root, read at `z₀`), every inverse query at the revealed value is charged, so the
expected charge is `|S|`. -/
theorem inv_vcharge_eq (x : ℕ → K) (S : Finset K) (z0 : K) :
    exP (Coins K K 1 × (K → Equiv.Perm K)) (fun p =>
      ((vkeys (pInv x z0) (valsP 1 (fun n => n = 0) (pnInv x z0) (rowAt x 1 ∅ (cf p.2) p.1.2 p.1.1))
        (qInv S (phiInv z0 (rowAt x 1 ∅ (cf p.2) p.1.2 p.1.1)) p.2) p.2).card : ℝ)) = S.card := by
  have h : ∀ p : Coins K K 1 × (K → Equiv.Perm K),
      ((vkeys (pInv x z0) (valsP 1 (fun n => n = 0) (pnInv x z0) (rowAt x 1 ∅ (cf p.2) p.1.2 p.1.1))
        (qInv S (phiInv z0 (rowAt x 1 ∅ (cf p.2) p.1.2 p.1.1)) p.2) p.2).card : ℝ) = S.card := by
    intro p
    rw [qInv_vkeys _ S _ p.2]
    simp only [valsP, phiInv, mem_biUnion, mem_filter, mem_range, mem_image]
    exact ⟨0, ⟨by norm_num, rfl⟩, z0, by simp [pnInv], rfl⟩
  simp only [h]
  exact exP_const _

omit [Fintype K] [Nonempty K] in
lemma pnInv_card (x : ℕ → K) (z0 : K) (m : ℕ) : ((pnInv x z0 m).card.choose 2) ≤ 3 := by
  have h : (pnInv x z0 m).card ≤ 3 := by
    unfold pnInv
    exact (card_insert_le _ _).trans (by
      have := card_insert_le (x (2 * m + 1)) ({x (2 * m + 2)} : Finset K)
      simp only [card_singleton] at this
      omega)
  have hm : ((pnInv x z0 m).card.choose 2) ≤ Nat.choose 3 2 := Nat.choose_le_choose 2 h
  simpa using hm

/-- **The permutation-row hop applies to the counterexample**, with the value charge `= q`
(`inv_vcharge_eq`): the real experiment and the one with a uniform function row at the root are
`(1 + q + 3)/(|K| − q)`-close, for `q = |S| < |K|`. -/
theorem inv_vbound (x : ℕ → K) (S : Finset K) (z0 : K) (hS : (S.card : ℝ) < Fintype.card K) :
    |pr (Coins K K 1 × (K → Equiv.Perm K)) (fun p =>
        aInv S z0 (phiInv z0 (rowAt x 1 ∅ (cf p.2) p.1.2 p.1.1)) p.2) -
      pr (Coins K K 1 × (K → Equiv.Perm K)) (fun p =>
        aInv S z0 (phiInv z0 (rowAt x 1 ((range 1).filter fun n => n = 0) (cf p.2) p.1.2 p.1.1))
          p.2)| ≤ (1 + S.card + 3) / (Fintype.card K - S.card) := by
  have hsec : ((range 1).filter fun n => n = 0) = {0} := by decide
  have h := puncturePtPm_real (x := x) (N := 1) (P := pInv x z0) (fun n => n = 0) (pnInv x z0)
    (fun n hn _ h0 => absurd (by omega : n = 0) h0) (fun n hn _ h0 => absurd (by omega : n = 0) h0)
    (fun m => Or.inr ⟨m, rfl⟩)
    (fun m z hz => by
      simp only [pnInv, mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inr ⟨_, rfl⟩)
    (fun c hc => by
      simp only [pnInv, mem_insert, mem_singleton]
      rcases Nat.even_or_odd c with ⟨r, hr⟩ | ⟨r, hr⟩
      · right; right; congr 1; omega
      · right; left; congr 1; omega)
    (phiInv z0) (fun n hn _ h0 => absurd (by omega : n = 0) h0)
    (fun ρ ρ' hs _ => hs 0 (by norm_num) rfl z0 (by simp [pnInv]))
    (fun o G => aInv S z0 o G) (fun o G => qInv S o G)
    (fun o G G' h => (qInv_cons S z0 o G G' h).1) (fun o G G' h => (qInv_cons S z0 o G G' h).2)
    (qm := S.card) (fun o V G => card_image_le.trans ((card_filter_le _ _).trans card_image_le))
    (by rw [hsec, card_singleton]; simpa using hS)
  rw [inv_vcharge_eq x S z0, hsec, card_singleton, sum_singleton] at h
  refine h.trans ?_
  have hc := pnInv_card x z0 0
  have hden : (0 : ℝ) < Fintype.card K - S.card := by linarith
  simp only [Nat.cast_one, one_mul]
  refine div_le_div_of_nonneg_right ?_ hden.le
  have : (((pnInv x z0 0).card.choose 2 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hc
  linarith

end InvValue

end VoleMole.ZK.IC
