import VoleMole.ZK.TwoPhaseAd
import VoleMole.ZK.CollideRO2

/-!
# A table-reading continuation's `H₂³` reads against the real two-phase prover's grinding block

`ZK/TwoPhaseAd.lean`'s continuation does not read `H₂³`. An environment that does (PomFRIT's
Issuer, `Privacy/PomFRITRAH.lean`) reads it at a set `Q` of grinding points that depends on step 1's
output and the other tables. The real prover reads `H₂³` at the grinding points of its own prefix
`pre = chal2 ‖ qs_check ‖ ã`, whose tail `ã` is pseudorandom. This file bounds the probability that
`Q` meets that block, by a second application of two-phase zero knowledge (`ZK2ARow.zk2A`), as
`pr_preBlk_mem` does for one phase:

* `realRun2_outPre2` (no probability): unless the grinding outcome at the real prefix is bad
  (`GrindBad`), a continuing real run outputs a proof from which the simulator's recomputation
  (`outPre2`) recovers the real prefix (`real_form`, `hyb2'_vPre`).
* `outPre2_rd5`, `outPre2_rdE`: the recomputation reads `H₅` at `312` and the cipher at `4607`
  keys, so the event "`Q` meets the recomputed block" (`tailEv2`) is a distinguisher with a budget
  (`budget_tailEv2`).
* `pr_simCoins_tail_mem`: for the simulated proof the recomputed block's tail is the simulator's
  uniform `ã`, and `Q` is computed from step 1, which does not read it (`simRun2_o1_tail`).
* **`pr_tail2A`**: for a continuation `K` with `Hyp2RA` (reads `(k₃, k₅, k_E)`, no `H₂³`) and a
  query set `Qf` (at most `m` keys, read off step 1's output, the slice and `H₅`/cipher at
  `(a₃, a₅, a_E)` keys, not off `H₂³`),

      Pr[K continues ∧ Qf meets the real prefix's block]
        ≤ 2⁻¹¹³ + εz(k₃ + a₃ + k₃, k₅ + a₅ + 312 + k₅, k_E + a_E + 4607 + k_E)
          + m·2^(−8·16(d−1)).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## The real run's recomputed prefix -/

section Real

variable [HasPrg] {Hb : Hashes} {st : Statement} {r : ByteArray} {k : Cont2}

/-- **The recomputation recovers a continuing real run's prefix** (no probability): unless the
grinding answers at the real prefix are bad, the run outputs a proof and `outPre2` of the output is
the real prefix `pre2`. -/
theorem realRun2_outPre2 (hHb : HashesWF Hb) (hh : Hyp2 st r k) (G3 : Tab3) (G2 : Tab2G st.params)
    (G5 : Tab5F) (ρ : Bytes 16)
    (hk : (k (out1 (rec5 Hb G5) CrtGen.tables st r (splitSeed (G3 ρ)))).isSome)
    (hg : ¬ GrindBad CrtGen.tables
      (G2 ∘ key2 st.params (pre2 (rec5 Hb G5) CrtGen.tables st r k (splitSeed (G3 ρ))))) :
    (∃ b, (realRun2 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k (ba ρ)).2.2 =
        some (.ok b)) ∧
      outPre2 Hb CrtGen.tables st k G5
          (realRun2 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k (ba ρ)) =
        pre2 (rec5 Hb G5) CrtGen.tables st r k (splitSeed (G3 ρ)) := by
  have hBwf : HashesWF (recB Hb (st1 st) r G3 G5) := recH_wf (st := st1 st) (w := r) hHb G3 _ G5
  obtain ⟨⟨y, sfx⟩, hk1⟩ := Option.isSome_iff_exists.1 hk
  have hout := out1_recB (Hb := Hb) (st := st) (r := r) G3 G5
  have hpre : pre2 (recB Hb (st1 st) r G3 G5) CrtGen.tables st r k =
      pre2 (rec5 Hb G5) CrtGen.tables st r k :=
    recH_eq_rec5 (fun H => pre2 H CrtGen.tables st r k)
      (fun _ _ _ hu h => pre2_agreeOff hu h _ _ _ _) Hb (st1 st) r G3 (fun _ => 0) G5
  have hvP : vPre (recB Hb (st1 st) r G3 G5) CrtGen.tables (withInst st y) =
      vPre (rec5 Hb G5) CrtGen.tables (withInst st y) :=
    recH_eq_rec5 (fun H => vPre H CrtGen.tables (withInst st y))
      (fun _ _ _ hu h => vPre_agreeOff hu h _ _) Hb (st1 st) r G3 (fun _ => 0) G5
  have hpP : preP (rec5 Hb G5) CrtGen.tables st r k (splitSeed (G3 ρ)) =
      pre2 (rec5 Hb G5) CrtGen.tables st r k (splitSeed (G3 ρ)) := by
    simp only [preP, hk, ↓reduceIte]
  have e := real_form Hb st r k hHb hh G3 G2 G5 ρ
  rw [hpP] at e
  obtain ⟨proof, hok, hv⟩ := hyb2'_vPre _ st r k hBwf hh (splitSeed (G3 ρ)) _ hg (y := y)
    (sfx := sfx) (by rw [hout]; exact hk1)
  rw [e, hok]
  refine ⟨⟨proof, rfl⟩, ?_⟩
  rw [hvP, hpre] at hv
  simp only [outPre2, hout, hk1]
  exact hv

end Real

/-! ## The recomputation's reads -/

section Reads

variable {R : Type} [CipherRow R]

/-- **The recomputed prefix reads `H₅` at `312` keys** (two phases, a fixed continuation). -/
theorem outPre2_rd5 (Hb : Hashes) (st : Statement) (k : Cont2) (o : Out2) :
    Rd5 (fun s : ShG R st.params => @outPre2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st k s.2.1 o)
      312 := by
  classical
  refine ⟨fun s => progKeys52 Hb st k o s, fun s => ?_, fun s G5 h => ?_⟩
  · unfold progKeys52
    dsimp only
    split
    · exact card_image_le.trans ((List.toFinset_card_le _).trans
        (@vIn5_length_le (icPrg (rowFn s.2.2)) _ _ _ _))
    · simp
  · unfold progKeys52 at h
    dsimp only at h
    unfold outPre2
    split
    · rename_i b y hb hy
      rw [hb, hy] at h
      have hmu : (withInst st y.1).mu1 (rec5 Hb G5) = (withInst st y.1).mu1 (rec5 Hb s.2.1) := by
        rw [rec5_mu1, rec5_mu1]
      have h4 : (rec5 Hb G5).hash .h4 = (rec5 Hb s.2.1).hash .h4 := by rw [rec5_h4, rec5_h4]
      have hA : (rec5 Hb G5).AgreeOff .h5 (rec5 Hb s.2.1) := by
        intro k' hk; rw [rec5_agree_ne hk, rec5_agree_ne hk]
      refine @vPre_h5_congr (icPrg (rowFn s.2.2)) _ _ hA _ _ _ fun x hx => ?_
      rw [@vIn5_congr (icPrg (rowFn s.2.2)) _ (withInst st y.1) _ _ hmu h4] at hx
      exact withTable_h5_congr _ fun _ => (h _ (mem_image.2 ⟨x, List.mem_toFinset.2 hx, rfl⟩)).symm
    · rfl

/-- **The recomputed prefix reads the cipher at `4607` keys** (two phases, a fixed
continuation). -/
theorem outPre2_rdE (Hb : Hashes) (st : Statement) (k : Cont2) (o : Out2) :
    RdE (fun s : ShG R st.params => @outPre2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st k s.2.1 o)
      4607 := by
  classical
  refine ⟨fun s => progKeysE2 Hb st k o s, fun s => ?_, fun s E h => ?_⟩
  · unfold progKeysE2
    dsimp only
    split
    · exact rdKeys_card _ _ _ _
    · simp
  · unfold progKeysE2 at h
    dsimp only at h
    unfold outPre2
    split
    · rename_i b y hb hy
      rw [hb, hy] at h
      exact (vPre_ic_congr (rec5 Hb s.2.1) CrtGen.tables (withInst st y.1) b
        fun k hk => rowFn_congr (h k hk)).symm
    · rfl

/-- **The event**: the continuation's value `y` continues, the output is a proof, and the block of
the prefix recomputed from it is among the first components of `Q`. -/
def tailEvK (Hb : Hashes) (st : Statement) (y : Option (Inst2 × ByteArray))
    (Q : Finset (K2 st.params)) (o : Out2) (s : ShG R st.params) : Prop :=
  y.isSome ∧ (∃ b, o.2.2 = some (.ok b)) ∧
    ∃ κ ∈ Q, κ.1 = blk (preLen st.params)
      (@outPre2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st (fun _ => y) s.2.1 o)

/-- **The distinguisher**: `tailEvK` at the continuation's value and the query set at the output's
step 1. -/
def tailEv2 (Hb : Hashes) (st : Statement) (K : Tab3 → ShG R st.params → Cont2)
    (Qf : ByteArray × ByteArray → Tab3 → ShG R st.params → Finset (K2 st.params))
    (o : Out2) (g : Tab3) (s : ShG R st.params) : Prop :=
  tailEvK Hb st (K g s (o.1, o.2.1)) (Qf (o.1, o.2.1) g s) o s

lemma tailEvK_rd5 (Hb : Hashes) (st : Statement) (y : Option (Inst2 × ByteArray))
    (Q : Finset (K2 st.params)) (o : Out2) :
    Rd5 (fun s : ShG R st.params => tailEvK Hb st y Q o s) 312 :=
  (outPre2_rd5 (R := R) Hb st (fun _ => y) o).map fun P =>
    y.isSome ∧ (∃ b, o.2.2 = some (.ok b)) ∧ ∃ κ ∈ Q, κ.1 = blk (preLen st.params) P

lemma tailEvK_rdE (Hb : Hashes) (st : Statement) (y : Option (Inst2 × ByteArray))
    (Q : Finset (K2 st.params)) (o : Out2) :
    RdE (fun s : ShG R st.params => tailEvK Hb st y Q o s) 4607 :=
  (outPre2_rdE (R := R) Hb st (fun _ => y) o).map fun P =>
    y.isSome ∧ (∃ b, o.2.2 = some (.ok b)) ∧ ∃ κ ∈ Q, κ.1 = blk (preLen st.params) P

/-- **The budget of the event**: the continuation's and the query set's reads, and the
recomputation's (`312` `H₅` keys, `4607` cipher keys). -/
theorem budget_tailEv2 (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ)
    (K : Tab3 → ShG R st.params → Cont2) {k3 k5 kE : ℕ} (hh : Hyp2RA st r n K k3 k5 kE)
    (Qf : ByteArray × ByteArray → Tab3 → ShG R st.params → Finset (K2 st.params)) {a3 a5 aE : ℕ}
    (hQ3 : ∀ o1 s, Rd3 (fun g => Qf o1 g s) a3) (hQ5 : ∀ o1 g, Rd5 (fun s => Qf o1 g s) a5)
    (hQE : ∀ o1 g, RdE (fun s => Qf o1 g s) aE) :
    Budget st.params (k3 + a3) (k5 + a5 + 312) (kE + aE + 4607) (tailEv2 Hb st K Qf) where
  h3 o s := by
    have hm := (hh.h3 (o.1, o.2.1) s).bind (f := fun y g => (y, Qf (o.1, o.2.1) g s))
      fun y => (hQ3 (o.1, o.2.1) s).map fun Q => (y, Q)
    exact hm.map fun yQ => tailEvK Hb st yQ.1 yQ.2 o s
  h5 o g := by
    have hm := (hh.h5 (o.1, o.2.1) g).bind (f := fun y s => (y, Qf (o.1, o.2.1) g s))
      fun y => (hQ5 (o.1, o.2.1) g).map fun Q => (y, Q)
    exact hm.bind (f := fun yQ s => tailEvK Hb st yQ.1 yQ.2 o s) fun yQ =>
      tailEvK_rd5 Hb st yQ.1 yQ.2 o
  hE o g := by
    have hm := (hh.hE (o.1, o.2.1) g).bind (f := fun y s => (y, Qf (o.1, o.2.1) g s))
      fun y => (hQE (o.1, o.2.1) g).map fun Q => (y, Q)
    exact hm.bind (f := fun yQ s => tailEvK Hb st yQ.1 yQ.2 o s) fun yQ =>
      tailEvK_rdE Hb st yQ.1 yQ.2 o

/-- **The event does not read `H₂³`.** -/
lemma tailEv2_h23 {Hb : Hashes} {st : Statement} {r : ByteArray} {n : ℕ}
    {K : Tab3 → ShG R st.params → Cont2} {k3 k5 kE : ℕ} (hh : Hyp2RA st r n K k3 k5 kE)
    {Qf : ByteArray × ByteArray → Tab3 → ShG R st.params → Finset (K2 st.params)}
    (hQ2 : ∀ o1 g (s : ShG R st.params) (G2 : Tab2G st.params), Qf o1 g (G2, s.2) = Qf o1 g s)
    (o : Out2) (g : Tab3) (s s' : ShG R st.params) (hs : s'.2 = s.2) :
    tailEv2 Hb st K Qf o g s' ↔ tailEv2 Hb st K Qf o g s := by
  obtain ⟨G2, rest⟩ := s'
  dsimp only at hs
  subst hs
  unfold tailEv2
  rw [hh.h2, hQ2]
  rfl

end Reads

/-! ## The simulated side -/

section Sim

variable {p : Params}

/-- **A uniform simulator tape's `ã` lies in a set computed from the rest of the tape** (at most
`m` values) with probability `≤ m·2^(−8·16(d−1))`. -/
theorem pr_simCoins_tail_mem (F : SimCoins p → Finset ByteArray)
    (hF : ∀ c (a : Bytes (16 * (p.qsDegree - 1))),
      F (c.1, (c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, a)) = F c)
    {m : ℕ} (hm : ∀ c, (F c).card ≤ m) :
    pr (SimCoins p) (fun c => ba c.2.2.2.2.2 ∈ F c) ≤
      m / 2 ^ (8 * (16 * (p.qsDegree - 1))) := by
  refine pr_le_of_fst fun sh => pr_le_of_fst fun f1 => pr_le_of_fst fun f2 =>
    pr_le_of_fst fun f3 => pr_le_of_fst fun f4 => ?_
  have h := pr_ba_mem_le (n := 16 * (p.qsDegree - 1)) (F (sh, (f1, f2, f3, f4, fun _ => 0)))
  refine le_trans (le_of_eq (pr_congr fun a => ?_)) (h.trans ?_)
  · rw [← hF (sh, (f1, f2, f3, f4, fun _ => 0)) a]
  · have : ((F (sh, (f1, f2, f3, f4, fun _ => 0))).card : ℝ) ≤ m := by exact_mod_cast hm _
    gcongr

variable [HasPrg]

/-- A simulated two-phase run's step-1 output does not read the simulator's `ã`. -/
lemma simRun2_o1_tail (Hb : Hashes) (st : Statement) (n : ℕ) (k : Cont2) (c : SimCoins st.params)
    (fb : Fallback st.params) (a : Bytes (16 * (st.params.qsDegree - 1))) :
    ((simRun2 Hb st n k ((c.1, (c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, a)), fb)).1,
      (simRun2 Hb st n k ((c.1, (c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, a)), fb)).2.1) =
      ((simRun2 Hb st n k (c, fb)).1, (simRun2 Hb st n k (c, fb)).2.1) := by
  unfold simRun2
  dsimp only
  rcases firstHit c.1.2.1 with _ | ⟨ctr, d⟩
  · rfl
  · simp only [simPhase1]

end Sim

/-! ## The bound -/

section Main

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-- The real run's step-1 output on the tables. -/
noncomputable def o1R2 (Hb : Hashes) (st : Statement) (r : ByteArray)
    (a : (Bytes 16 × Tab3) × ShG R st.params) : ByteArray × ByteArray :=
  @out1 (icPrg (rowFn a.2.2.2)) (rec5 Hb a.2.2.1) CrtGen.tables st r (splitSeed (a.1.2 a.1.1))

/-- The real run's grinding prefix on the tables (continuation `K` at the slice and the tables). -/
noncomputable def preR2 (Hb : Hashes) (st : Statement) (r : ByteArray)
    (K : Tab3 → ShG R st.params → Cont2) (a : (Bytes 16 × Tab3) × ShG R st.params) : ByteArray :=
  @pre2 (icPrg (rowFn a.2.2.2)) (rec5 Hb a.2.2.1) CrtGen.tables st r (K a.1.2 a.2)
    (splitSeed (a.1.2 a.1.1))

/-- The event on the simulated output, at fixed tables and coins. -/
def simEv2 (Hb : Hashes) (st : Statement) (n : ℕ) (K : Tab3 → ShG R st.params → Cont2)
    (Qf : ByteArray × ByteArray → Tab3 → ShG R st.params → Finset (K2 st.params))
    (s : ShG R st.params) (g : Tab3) (cf : SimCoins2 st.params) : Prop :=
  tailEvK Hb st (K g s ((@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) cf).1,
      (@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) cf).2.1))
    (Qf ((@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) cf).1,
      (@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) cf).2.1) g s)
    (@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) cf) s

/-- **The simulated side, at fixed tables**: the block recomputed from a simulated proof has the
simulator's uniform `ã` as its tail, and the query set, read off the simulated step 1, does not
depend on it. -/
theorem pr_simEv2 (Hb : Hashes) (st : Statement) (n : ℕ) (K : Tab3 → ShG R st.params → Cont2)
    (hHb : HashesWF Hb)
    (Qf : ByteArray × ByteArray → Tab3 → ShG R st.params → Finset (K2 st.params))
    {m : ℕ} (hm : ∀ o1 g s, (Qf o1 g s).card ≤ m) (s : ShG R st.params) (g : Tab3)
    (fb : Fallback st.params) :
    pr (SimCoins st.params) (fun c => simEv2 Hb st n K Qf s g (c, fb)) ≤
      m / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) := by
  classical
  let F : SimCoins st.params → Finset ByteArray := fun c =>
    (Qf ((@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) (c, fb)).1,
      (@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) (c, fb)).2.1) g s).image fun κ => preTail κ.1
  have hF : ∀ c (a : Bytes (16 * (st.params.qsDegree - 1))),
      F (c.1, (c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, a)) = F c := fun c a => by
    simp only [F, @simRun2_o1_tail (icPrg (rowFn s.2.2)) Hb st n (K g s) c fb a]
  have hFm : ∀ c, (F c).card ≤ m := fun c => card_image_le.trans (hm _ _ _)
  refine le_trans (pr_mono fun c hc => ?_) (pr_simCoins_tail_mem F hF hFm)
  unfold simEv2 tailEvK at hc
  obtain ⟨hk1, ⟨b, hb'⟩, κ, hκ', hblk'⟩ := hc
  have e2 : @outPre2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st
      (fun _ => K g s ((@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) (c, fb)).1,
        (@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) (c, fb)).2.1)) s.2.1
      (@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) (c, fb)) =
      @outPre2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st (K g s) s.2.1
        (@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) (c, fb)) :=
    @outPre2_kcongr' (icPrg (rowFn s.2.2)) Hb CrtGen.tables st _ _ s.2.1 _ (by rfl)
  rw [e2] at hblk'
  rcases hf : firstHit c.1.2.1 with _ | ⟨ctr, δ⟩
  · exfalso
    have e : (@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) (c, fb)).2.2 =
        ((K g s) (ba fb.1, ba fb.2)).map fun _ => .error "grinding failed" := by
      simp only [simRun2, hf]
    rw [e] at hb'
    rcases hK0 : (K g s) (ba fb.1, ba fb.2) with _ | y
    · rw [hK0] at hb'; cases hb'
    · rw [hK0] at hb'; cases hb'
  · have ho : ((@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) (c, fb)).1,
        (@simRun2 (icPrg (rowFn s.2.2)) Hb st n (K g s) (c, fb)).2.1) =
        @simPhase1 (icPrg (rowFn s.2.2)) Hb (st1 st) n c.1 ctr δ c.2 := by
      simp only [simRun2, hf]
    have hk' : (K g s (@simPhase1 (icPrg (rowFn s.2.2)) Hb (st1 st) n c.1 ctr δ c.2)).isSome := by
      rw [← ho]; exact hk1
    have ht := @preTail_outPre2 (icPrg (rowFn s.2.2)) Hb st (K g s) hHb CrtGen.tables n s.2.1
      (c, fb) ctr δ hf hk'
    refine mem_image.2 ⟨κ, hκ', ?_⟩
    show preTail κ.1 = _
    rw [hblk']
    exact ht

/-- **The simulated side**: `pr_simEv2` averaged over the tables. -/
theorem pr_tailEv2_sim (Hb : Hashes) (st : Statement) {r : ByteArray} (n : ℕ)
    (K : Tab3 → ShG R st.params → Cont2) {k3 k5 kE : ℕ} (hh : Hyp2RA st r n K k3 k5 kE)
    (hHb : HashesWF Hb)
    (Qf : ByteArray × ByteArray → Tab3 → ShG R st.params → Finset (K2 st.params))
    (hQ2 : ∀ o1 g (s : ShG R st.params) (G2 : Tab2G st.params), Qf o1 g (G2, s.2) = Qf o1 g s)
    {m : ℕ} (hm : ∀ o1 g s, (Qf o1 g s).card ≤ m) :
    pr ((SimCoins2 st.params × Tab3) × ShG R st.params) (fun a =>
      tailEv2 Hb st K Qf (simRO2 Hb st n (K a.1.2) a.1.1 a.2) a.1.2
        (progRO2 Hb st n (K a.1.2) a.1.1 a.2)) ≤
      m / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) := by
  have e : ∀ a : (SimCoins2 st.params × Tab3) × ShG R st.params,
      tailEv2 Hb st K Qf (simRO2 Hb st n (K a.1.2) a.1.1 a.2) a.1.2
        (progRO2 Hb st n (K a.1.2) a.1.1 a.2) ↔ simEv2 Hb st n K Qf a.2 a.1.2 a.1.1 := fun a => by
    refine (tailEv2_h23 (Hb := Hb) hh hQ2 (simRO2 Hb st n (K a.1.2) a.1.1 a.2) a.1.2 a.2
      (progRO2 Hb st n (K a.1.2) a.1.1 a.2) rfl).trans ?_
    unfold simRO2 simEv2 tailEv2
    exact Iff.rfl
  rw [pr_congr e]
  refine pr_le_of_snd fun s => pr_le_of_snd fun g => pr_le_of_snd fun fb => ?_
  exact pr_simEv2 Hb st n K hHb Qf hm s g fb

/-- **A table-reading continuation's `H₂³` reads meet the real two-phase prover's grinding
block** with probability `≤ 2⁻¹¹³ + εz(k₃ + a₃ + k₃, k₅ + a₅ + 312 + k₅, k_E + a_E + 4607 + k_E)
+ m·2^(−8·16(d−1))`: unless the grinding outcome is bad, the block is the one recomputed from the
proof (`realRun2_outPre2`); by two-phase zero knowledge (`ZK2ARow.zk2A`, the distinguisher
`tailEv2`) the recomputed block meets the reads with the simulated proof's probability, and the
simulated block's tail is uniform and independent of the reads (`pr_simCoins_tail_mem`). -/
theorem pr_tail2A [ZKRow R] [ZK2ARow R] (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ)
    (K : Tab3 → ShG R st.params → Cont2) {k3 k5 kE : ℕ} (hh : Hyp2RA st r n K k3 k5 kE)
    (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (Qf : ByteArray × ByteArray → Tab3 → ShG R st.params → Finset (K2 st.params))
    (hQ2 : ∀ o1 g (s : ShG R st.params) (G2 : Tab2G st.params), Qf o1 g (G2, s.2) = Qf o1 g s)
    {m : ℕ} (hm : ∀ o1 g s, (Qf o1 g s).card ≤ m) {a3 a5 aE : ℕ}
    (hQ3 : ∀ o1 s, Rd3 (fun g => Qf o1 g s) a3) (hQ5 : ∀ o1 g, Rd5 (fun s => Qf o1 g s) a5)
    (hQE : ∀ o1 g, RdE (fun s => Qf o1 g s) aE) :
    pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        (K a.1.2 a.2 (o1R2 Hb st r a)).isSome ∧
          ∃ κ ∈ Qf (o1R2 Hb st r a) a.1.2 a.2, κ.1 = blk (preLen st.params) (preR2 Hb st r K a)) ≤
      1 / 2 ^ 113 + ZKRow.εz R st.params (k3 + a3 + k3) (k5 + a5 + 312 + k5) (kE + aE + 4607 + kE) +
        m / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) := by
  classical
  let D := tailEv2 (R := R) Hb st K Qf
  have hD := budget_tailEv2 Hb st r n K hh Qf hQ3 hQ5 hQE
  -- The event is a bad grinding outcome or the event on the real output.
  have hsplit : ∀ a : (Bytes 16 × Tab3) × ShG R st.params,
      ((K a.1.2 a.2 (o1R2 Hb st r a)).isSome ∧
        ∃ κ ∈ Qf (o1R2 Hb st r a) a.1.2 a.2, κ.1 = blk (preLen st.params) (preR2 Hb st r K a)) →
      GrindBad CrtGen.tables (a.2.1 ∘ key2 st.params (preR2 Hb st r K a)) ∨
        D (realRO2 Hb st r (K a.1.2) a.1.1 a.1.2 a.2) a.1.2 a.2 := by
    rintro ⟨⟨ρ, g⟩, s⟩ ⟨hk, κ, hκ, hblk⟩
    by_cases hg : GrindBad CrtGen.tables (s.1 ∘ key2 st.params (preR2 Hb st r K ((ρ, g), s)))
    · exact Or.inl hg
    · right
      have hh' := hh.hyp g s
      obtain ⟨hok, hpre⟩ := @realRun2_outPre2 (icPrg (rowFn s.2.2)) Hb st r (K g s) hHb hh' g s.1
        s.2.1 ρ hk hg
      have ho1 := @realRun2_out1 (icPrg (rowFn s.2.2)) Hb st r (K g s) hHb hh' g s.1 s.2.1 ρ
      show tailEvK Hb st (K g s ((realRO2 Hb st r (K g) ρ g s).1, (realRO2 Hb st r (K g) ρ g s).2.1))
        (Qf ((realRO2 Hb st r (K g) ρ g s).1, (realRO2 Hb st r (K g) ρ g s).2.1) g s)
        (realRO2 Hb st r (K g) ρ g s) s
      have e1 : ((realRO2 Hb st r (K g) ρ g s).1, (realRO2 Hb st r (K g) ρ g s).2.1) =
          o1R2 Hb st r ((ρ, g), s) := ho1
      rw [e1]
      refine ⟨hk, hok, κ, hκ, ?_⟩
      have e2 : @outPre2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st
          (fun _ => K g s (o1R2 Hb st r ((ρ, g), s))) s.2.1 (realRO2 Hb st r (K g) ρ g s) =
          @outPre2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables st (K g s) s.2.1
            (realRO2 Hb st r (K g) ρ g s) :=
        @outPre2_kcongr' (icPrg (rowFn s.2.2)) Hb CrtGen.tables st _ _ s.2.1 _ (by rw [e1])
      rw [e2]
      exact hblk.trans (congrArg _ hpre.symm)
  -- The grinding answers at the real prefix are uniform.
  have hgrind : pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
      GrindBad CrtGen.tables (a.2.1 ∘ key2 st.params (preR2 Hb st r K a))) ≤ 1 / 2 ^ 113 := by
    refine pr_le_of_fst fun x => pr_le_of_snd fun rr => ?_
    have e : ∀ G2 : Tab2G st.params, preR2 Hb st r K (x, (G2, rr)) =
        preR2 Hb st r K (x, (fun _ => 0, rr)) := fun G2 => by
      unfold preR2
      rw [show K x.2 (G2, rr) = K x.2 (fun _ => 0, rr) from hh.h2 x.2 (fun _ => 0, rr) G2]
    have h := close_restrict (R := Bytes 16) (key2_injective st.params
      (preR2 Hb st r K (x, (fun _ => 0, rr)))) (GrindBad CrtGen.tables)
    rw [abs_nonpos_iff, sub_eq_zero] at h
    refine le_trans (le_of_eq ?_) ((le_of_eq h).trans grindBad_le_113)
    exact pr_congr fun G2 => by rw [e G2]
  -- Zero knowledge for the event.
  have hz := ZK2ARow.zk2A Hb st r n K hh hHb hp D hD
  -- The simulated side.
  have hsim : pr ((SimCoins2 st.params × Tab3) × ShG R st.params) (fun a =>
      D (simRO2 Hb st n (K a.1.2) a.1.1 a.2) a.1.2 (progRO2 Hb st n (K a.1.2) a.1.1 a.2)) ≤
      m / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) := by
    exact pr_tailEv2_sim Hb st n K hh hHb Qf hQ2 hm
  have hreal : pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
      D (realRO2 Hb st r (K a.1.2) a.1.1 a.1.2 a.2) a.1.2 a.2) ≤
      ZKRow.εz R st.params (k3 + a3 + k3) (k5 + a5 + 312 + k5) (kE + aE + 4607 + kE) +
        m / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) := by
    have := (abs_sub_le_iff.1 hz).1
    linarith
  refine (pr_mono hsplit).trans ((pr_or_le _ _).trans ?_)
  linarith

end Main

end VoleMole.ZK.Sim
