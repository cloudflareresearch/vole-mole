import VoleMole.ZK.CollideRO
import VoleMole.ZK.TwoPhaseReadsRO

/-!
# Programming collisions for the two-phase prover

The two-phase analogues of `ZK/CollideRO.lean`, for PomFRIT's collision term:

* `realRun2_h23_congr`: the real two-phase run reads `H₂³` only at the grinding points of the
  prefix `pre2` of the instance its continuation picks, and not at all if the continuation stops
  (`real_form`, `hyb2'_none`); `realRun2_out1`: its step-1 output is `out1` (no `H₂³`).
* `preTail_outPre2`: the prefix the two-phase simulator programs, when its grinding succeeded and
  its continuation continues, ends with the simulator's uniform `ã` (`vPre_simAssemble`).
* `pr_simCoins_tail_le`: a uniform simulator tape's `ã` hits a value computed from the rest of the
  tape with probability `≤ 2^(−8·16(d−1))`, its grinding fails with probability `noHitProb`.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

section TwoPhase

variable [HasPrg] {Hb : Hashes} {st : Statement} {r : ByteArray} {k : Cont2}

lemma out1_recB (G3 : Tab3) (G5 : Tab5F) :
    out1 (recB Hb (st1 st) r G3 G5) CrtGen.tables st r = out1 (rec5 Hb G5) CrtGen.tables st r :=
  recH_eq_rec5 (fun H => out1 H CrtGen.tables st r)
    (fun _ _ _ hu h => out1_agreeOff CrtGen.tables st r hu h) Hb (st1 st) r G3 _ G5

/-- **The real two-phase run's step-1 output** is `out1` at the seed and `iv_pre` of its slice. -/
theorem realRun2_out1 (hHb : HashesWF Hb) (hh : Hyp2 st r k) (G3 : Tab3) (G2 : Tab2G st.params)
    (G5 : Tab5F) (ρ : Bytes 16) :
    ((realRun2 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k (ba ρ)).1,
      (realRun2 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k (ba ρ)).2.1) =
      out1 (rec5 Hb G5) CrtGen.tables st r (splitSeed (G3 ρ)) := by
  have hBwf : HashesWF (recB Hb (st1 st) r G3 G5) :=
    recH_wf (st := st1 st) (w := r) hHb G3 _ G5
  rw [real_form Hb st r k hHb hh G3 G2 G5 ρ, hyb2'_eq _ st r k hBwf hh, out1_recB]

/-- **The real two-phase run reads `H₂³` only at its instance's grinding points**, and not at all
if its continuation stops. -/
theorem realRun2_h23_congr (hHb : HashesWF Hb) (hh : Hyp2 st r k) (G3 : Tab3)
    (G2 G2' : Tab2G st.params) (G5 : Tab5F) (ρ : Bytes 16)
    (hG : (k (out1 (rec5 Hb G5) CrtGen.tables st r (splitSeed (G3 ρ)))).isSome →
      ∀ c, G2' (key2 st.params (pre2 (rec5 Hb G5) CrtGen.tables st r k (splitSeed (G3 ρ))) c) =
        G2 (key2 st.params (pre2 (rec5 Hb G5) CrtGen.tables st r k (splitSeed (G3 ρ))) c)) :
    realRun2 (recH Hb (st1 st) r G3 G2' G5) CrtGen.tables st r k (ba ρ) =
      realRun2 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k (ba ρ) := by
  have hBwf : HashesWF (recB Hb (st1 st) r G3 G5) :=
    recH_wf (st := st1 st) (w := r) hHb G3 _ G5
  rw [real_form Hb st r k hHb hh G3 G2' G5 ρ, real_form Hb st r k hHb hh G3 G2 G5 ρ]
  by_cases hc : (k (out1 (rec5 Hb G5) CrtGen.tables st r (splitSeed (G3 ρ)))).isSome
  · have e : G2' ∘ key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r k (splitSeed (G3 ρ))) =
        G2 ∘ key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r k (splitSeed (G3 ρ))) := by
      funext c
      simp only [Function.comp_apply, preP, hc, ↓reduceIte]
      exact hG hc c
    rw [e]
  · have hk : k (out1 (recB Hb (st1 st) r G3 G5) CrtGen.tables st r (splitSeed (G3 ρ))) = none := by
      rw [out1_recB]; exact Option.not_isSome_iff_eq_none.1 hc
    rw [hyb2'_none _ st r k hBwf hh _ _ hk, hyb2'_none _ st r k hBwf hh _ _ hk]

/-- **The prefix the two-phase simulator programs, when its grinding succeeded and its
continuation continues, ends with its uniform `ã`.** -/
theorem preTail_outPre2 (hHb : HashesWF Hb) (T : CrtTables) (n : ℕ) (G5 : Tab5F)
    (c : SimCoins2 st.params) {ctr : ℕ} {δ : Bytes 16} (hf : firstHit c.1.1.2.1 = some (ctr, δ))
    (hk : (k (simPhase1 Hb (st1 st) n c.1.1 ctr δ c.1.2)).isSome) :
    preTail (blk (preLen st.params) (outPre2 Hb T st k G5 (simRun2 Hb st n k c))) =
      ba c.1.2.2.2.2.2 := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hk
  have e : simRun2 Hb st n k c = ((simPhase1 Hb (st1 st) n c.1.1 ctr δ c.1.2).1,
      (simPhase1 Hb (st1 st) n c.1.1 ctr δ c.1.2).2,
      some (.ok (simAssemble st.params c.1.1 ctr δ c.1.2))) := by
    simp only [simRun2, hf, hy, Option.map_some]
  obtain ⟨X, hX, hv⟩ := vPre_simAssemble (rec5 Hb G5) (hHb.withTable .h5 enc5 G5) T
    (withInst st y.1) c.1.1 ctr δ c.1.2 hf
  rw [e]
  simp only [outPre2, hy, hv]
  exact preTail_blk hX (size_ba _)

end TwoPhase

/-! ## A simulator tape's `ã` against the rest of the tape -/

section Coins

variable {p : Params}

/-- **A uniform simulator tape**: its grinding fails, or its `ã` equals a value computed from the
rest of the tape (`F`, which does not read `ã`), with probability
`≤ noHitProb + 2^(−8·16(d−1))`. -/
theorem pr_simCoins_tail_le (F : SimCoins p → ByteArray)
    (hF : ∀ c (a : Bytes (16 * (p.qsDegree - 1))),
      F (c.1, (c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, a)) = F c) :
    pr (SimCoins p) (fun c => firstHit c.1.2.1 = none ∨ F c = ba c.2.2.2.2.2) ≤
      noHitProb + 1 / 2 ^ (8 * (16 * (p.qsDegree - 1))) := by
  refine (pr_or_le _ _).trans (add_le_add (le_of_eq ?_) ?_)
  · have e1 := pr_prod_fst (β := SimFields p) (fun s : Shared => firstHit s.2.1 = none)
    have e2 := pr_prod_snd (α := Bytes 16)
      (fun x : Grind × (Fin BAVC.tau → Bytes 32) × (Fin 105 → Bytes 16) => firstHit x.1 = none)
    have e3 := pr_prod_fst (β := (Fin BAVC.tau → Bytes 32) × (Fin 105 → Bytes 16))
      (fun g : Grind => firstHit g = none)
    exact e1.trans (e2.trans e3)
  · refine pr_le_of_fst fun sh => pr_le_of_fst fun f1 => pr_le_of_fst fun f2 =>
      pr_le_of_fst fun f3 => pr_le_of_fst fun f4 => ?_
    have h := pr_ba_mem_le (n := 16 * (p.qsDegree - 1))
      {F (sh, (f1, f2, f3, f4, fun _ => 0))}
    rw [Finset.card_singleton, Nat.cast_one] at h
    refine le_trans (le_of_eq (pr_congr fun a => ?_)) h
    rw [Finset.mem_singleton, ← hF (sh, (f1, f2, f3, f4, fun _ => 0)) a, eq_comm]

end Coins

end VoleMole.ZK.Sim
