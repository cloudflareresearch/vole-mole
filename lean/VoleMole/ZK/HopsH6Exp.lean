import VoleMole.ZK.HopsH6
import VoleMole.ZK.HopsROMExp

/-!
# Hop H6 with an expected charge at the proof's `H₅` inputs

`pr_bad_le` (`ZK/HopsH6.lean`) bounds the bad event of hop H6 (a sibling `H₅` input read by the
prover or by the distinguisher) by `(q + 1)·2⁻¹²⁸`, `q` a worst-case bound on the distinguisher's
`H₅` keys. Only some keys count: a key is a guess of `u_pre` (`guessOf` non-empty) only if its
input is a gate input `iv ‖ e ‖ label ‖ 5` of this proof, with this proof's `iv` (`guessOf`). And
`u_pre` (through `Θ`) is uniform and independent of the proof's fields, so the bound holds with the
**expected** number of such keys:

    pr_bad_exp:  Pr_t[bad] ≤ (1 + E_f[#keys of D that are gate inputs of the proof]) / 2¹²⁸,

the expectation over the proof's fields `f` uniform (`SimFields`: the simulated proof's
distribution, `upush_fieldsOf`), for a fixed table and shared tape. Keys of other proofs (other
`iv`s) cost nothing.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

variable [VoleMole.Verifier.HasPrg]

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
open VoleMole.ZK.IC

attribute [local instance] decEqW128

section Query

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128)
  (QD : Except String ByteArray → (SKey st.params → Bytes 4) → Finset (SKey st.params))

/-- **The H6 charge of a proof**: the distinguisher's `H₅` keys whose input is one of the proof's
gate inputs, for some label offset (exactly the keys that guess something). -/
noncomputable def chg5 (G : SKey st.params → Bytes 4) (s : Shared) (f : SimFields st.params) : ℕ :=
  haveI := Classical.decPred fun k : SKey st.params => (guessOf Hs T st s f k).Nonempty
  ((QD (outOf st s f) G).filter fun k => (guessOf Hs T st s f k).Nonempty).card

lemma card_guesses_le_chg5 (G : SKey st.params → Bytes 4) (s : Shared) (f : SimFields st.params) :
    (guesses Hs T st QD G s f).card ≤ 1 + chg5 Hs T st QD G s f := by
  classical
  unfold guesses chg5
  refine (Finset.card_insert_le _ _).trans ?_
  rw [Nat.add_comm 1]
  refine Nat.add_le_add_right ?_ 1
  refine Finset.card_biUnion_le.trans ?_
  rw [Finset.card_filter]
  convert Finset.sum_le_sum (s := QD (outOf st s f) G) fun k _ =>
    (show (guessOf Hs T st s f k).card ≤ if (guessOf Hs T st s f k).Nonempty then 1 else 0 by
      split_ifs with hk
      · exact card_guessOf_le Hs T st s f k
      · rw [Finset.not_nonempty_iff_eq_empty.1 hk, Finset.card_empty])

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024 in
/-- **H6's bad event with the expected number of the proof's `H₅` keys read**: for a fixed shared
tape and table,

    Pr[a sibling input is read] ≤ (1 + E_f[chg5]) / 2¹²⁸,

`chg5` the distinguisher's keys at the proof's gate inputs, `f` the proof's fields, uniform. -/
theorem pr_bad_exp (hlr : st.params.labelRows = true) (h : ZKHyp T st w cs)
    (G : SKey st.params → Bytes 4) (s : Shared) :
    pr (Pads st.params) (fun t => ∃ e, sibKey Hs T st (s, dropSib t) e ∈
      proverKeys Hs T st (s, t) ∪ QD (proveIdeal (H5 Hs T st G) T st w (s, t)) G) ≤
      (1 + exP (SimFields st.params) (fun f => (chg5 Hs T st QD G s f : ℝ))) / 2 ^ 128 := by
  obtain ⟨h1, -, hlb, h2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  let F := fieldsOf (H5 Hs T st G) T st w cs s (hitOf s).1 (hitOf s).2
  let S := guesses Hs T st QD G s
  have e1 : pr (Pads st.params) (fun t => ∃ e, sibKey Hs T st (s, dropSib t) e ∈
      proverKeys Hs T st (s, t) ∪ QD (proveIdeal (H5 Hs T st G) T st w (s, t)) G) ≤
      pr (Pads st.params) (fun t => thetaW st.params (F t).2 ∈ S (F t).1) :=
    pr_mono fun t ht => by
      have hm := bad_mem_guesses Hs T st w cs QD hlab h G s t ht
      rw [uPre_eq_thetaW hlr] at hm
      rw [fieldsOf_theta]
      exact hm
  have e2 : pr (Pads st.params) (fun t => thetaW st.params (F t).2 ∈ S (F t).1) =
      pr (SimFields st.params × Bytes (labelBytes st.params))
        (fun y => thetaW st.params y.2 ∈ S y.1) := by
    have := (upush_fieldsOf (H5 Hs T st G) T st w cs s (hitOf s).1 (hitOf s).2 h.hT h.hnm)
      (fun y => thetaW st.params y.2 ∈ S y.1)
    rw [abs_nonpos_iff, sub_eq_zero] at this
    exact this
  have e3 : pr (SimFields st.params × Bytes (labelBytes st.params))
      (fun y => thetaW st.params y.2 ∈ S y.1) ≤
      exP (SimFields st.params) (fun f => ((S f).card : ℝ)) /
        Fintype.card (Bytes (labelBytes st.params)) := by
    rw [← pr_equiv (Equiv.prodComm (Bytes (labelBytes st.params)) (SimFields st.params))]
    exact pr_mem_indep_exp (thetaW st.params) (thetaW_injective hlr) S
  have hc : ((2 ^ (8 * labelBytes st.params) : ℕ) : ℝ) = 2 ^ 128 := by rw [hlb]; norm_num
  rw [Prob.card_bytes, hc] at e3
  refine (e1.trans (e2.le.trans e3)).trans (div_le_div_of_nonneg_right ?_ (by positivity))
  rw [← exP_const_add]
  exact exP_mono fun f => by exact_mod_cast card_guesses_le_chg5 Hs T st QD G s f

end Query

end VoleMole.ZK.Sim
