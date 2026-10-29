import VoleMole.Privacy.PomFRITRO
import VoleMole.ZK.CollideRO2

/-!
# PomFRIT in the random-oracle model: the programming-collision term, bounded

`blindnessRO_lean` (`Privacy/PomFRITRO.lean`) carries `δ(A)` (`deltaRO`): the probability that
session `1`, run for real, reads `H₂³` differently on the tables session `0`'s simulator
programmed. Here `δ(A) ≤ noHitProb + 2⁻¹²⁸` (`deltaRO_le`):

* session `1`'s run reads `H₂³` only at the grinding points of the prefix `pre2` of the instance
  its continuation picks, and not at all if it stops (`realRun2_h23_congr`); session `0`'s
  simulator programs the keys of one prefix block, that of the prefix it recomputes;
* if session `1` continues, both responses passed the Clients' checks (`bothOK`, symmetric in the
  two sessions), so session `0`'s continuation continues too, and if its grinding succeeded, the
  programmed prefix ends with its uniform `ã₀` (`16` bytes: PomFRIT's `d = 2`, `preLen = 88`;
  `preTail_outPre2`);
* session `1`'s prefix is computed from its coins, the tables and session `0`'s *request*, which
  does not read `ã₀` (`simRun2_s1_tail`): a collision has probability `≤ 2⁻¹²⁸`; session `0`'s
  grinding fails with probability `noHitProb` (`pr_simCoins_tail_le`).

**`blindnessRO_lean_num`**: `|Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428)
+ 2·noHitProb + 2·2⁻¹²⁸`.

**Cipher rows.** Everything here is stated for every type of cipher rows `R` (the shared
tables `ZK.Sim.ShG R p`, `ZK/ReadsRO.lean`) with `ZKRow R`, `ZK2Row R`; `blindnessRO_lean_numG` is the generic
Lean-prover bound and `blindnessRO_lean_num` its instance at function rows (`Blk → Blk`, the PRF
view); `Privacy/PermRO.lean` instantiates it at permutation rows (AES as uniformly random
permutations, the adversary reading whole rows: forward and inverse queries).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT

-- `Com` and the UOV map evaluate Keccak and the public map; nothing below needs to unfold them.
attribute [local irreducible] commitRefresher UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R] {Hb : Hashes} (A : AdversaryRO R)

lemma tail_pP : (8 * (16 * (pP.qsDegree - 1)) : ℕ) = 128 := rfl

/-- **A simulated session's request does not read its `ã`.** -/
lemma s1C_tail (ref : Coins refresherBytes) (c : SimCoins pP) (fb : Fallback pP)
    (a : Sim.Bytes (16 * (pP.qsDegree - 1))) (s : ShP R) :
    s1C Hb ref ((c.1, (c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2.1, a)), fb) s = s1C Hb ref (c, fb) s := by
  unfold s1C simRun2
  dsimp only
  rcases firstHit c.1.2.1 with _ | ⟨ctr, d⟩
  · rfl
  · simp only [simPhase1]

/-- The prefix session `1`'s real run grinds at, in `deltaRO`'s tape. -/
noncomputable def pre1 (Hb : Hashes) (z : (XS × XR) × ShP R) : ByteArray :=
  @pre2 (icPrg (rowFn z.2.2.2)) (rec5 Hb z.2.2.1) CrtGen.tables (stOf z.1.2.1.2.1)
    (toBA (List.ofFn z.1.2.1.2.2))
    (kOf A (A.msg true) z.1.2.1.2.1 z.1.2.1.2.2 true (tS Hb A (A.msg false) z.1.1 z.2))
    (splitSeed (z.1.2.2 z.1.2.1.1))

/-- The prefix block session `0`'s simulator programs, in `deltaRO`'s tape. -/
noncomputable def pre0 (Hb : Hashes) (y₀ : XS) (x₁ : XR) (s : ShP R) : ByteArray :=
  @outPre2 (icPrg (rowFn s.2.2)) Hb CrtGen.tables (stOf y₀.1.2.1)
    (kOf A (A.msg false) y₀.1.2.1 y₀.1.2.2 false (tR Hb A (A.msg true) x₁ s)) s.2.1
    (@simRun2 (icPrg (rowFn s.2.2)) Hb (stOf y₀.1.2.1) uovM
      (kOf A (A.msg false) y₀.1.2.1 y₀.1.2.2 false (tR Hb A (A.msg true) x₁ s)) y₀.1.1)

lemma pS_pre0 (y₀ : XS) (x₁ : XR) (s : ShP R) :
    pS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s =
      (programAt (key2 pP (pre0 A Hb y₀ x₁ s)) y₀.1.1.1.1.2.1 s.1, s.2) := by
  rw [pS_eq]; rfl

/-- Session `1`'s real run, with its continuation's other request fixed. -/
lemma oR_run (y₀ : XS) (x₁ : XR) (s v : ShP R) (hv : v.2 = s.2) :
    oR Hb A (A.msg true) true x₁ (tS Hb A (A.msg false) y₀) v =
      @realRun2 (icPrg (rowFn s.2.2)) (recH Hb (st1 (stOf x₁.1.2.1)) (toBA (List.ofFn x₁.1.2.2)) x₁.2 v.1
        s.2.1) CrtGen.tables (stOf x₁.1.2.1) (toBA (List.ofFn x₁.1.2.2))
        (kOf A (A.msg true) x₁.1.2.1 x₁.1.2.2 true (tS Hb A (A.msg false) y₀ s)) (ba x₁.1.1) := by
  obtain ⟨G2, r⟩ := v
  dsimp only at hv
  subst hv
  rw [oR_cont Hb A _ _ x₁ (G2, s.2) (t₂ := fun _ => tS Hb A (A.msg false) y₀ s)
    (by rw [tS, tS, s1S_eq Hb y₀ s (G2, s.2) rfl])]
  rfl

/-- **A collision of `deltaRO`**: session `0`'s grinding failed, or session `1`'s prefix ends
with session `0`'s `ã₀`. -/
theorem deltaRO_event' (hHb : HashesWF Hb) (y₀ : XS) (x₁ : XR) (s : ShP R)
    (hz : oR Hb A (A.msg true) true x₁ (tS Hb A (A.msg false) y₀)
        (pS Hb A (A.msg false) false y₀ (tR Hb A (A.msg true) x₁) s) ≠
      oR Hb A (A.msg true) true x₁ (tS Hb A (A.msg false) y₀) s) :
    firstHit y₀.1.1.1.1.2.1 = none ∨
      preTail (blk (preLen pP) (pre1 A Hb ((y₀, x₁), s))) = ba y₀.1.1.1.2.2.2.2.2 := by
  have hh := hyp2_kOf A (A.msg true) x₁.1.2.1 x₁.1.2.2 true (tS Hb A (A.msg false) y₀ s)
  rw [oR_run A y₀ x₁ s _ (by rw [pS_pre0]), oR_run A y₀ x₁ s s rfl, pS_pre0] at hz
  -- Session 1 continues, and reads a programmed point.
  have hcol : (kOf A (A.msg true) x₁.1.2.1 x₁.1.2.2 true (tS Hb A (A.msg false) y₀ s)
      (@out1 (icPrg (rowFn s.2.2)) (rec5 Hb s.2.1) CrtGen.tables (stOf x₁.1.2.1)
        (toBA (List.ofFn x₁.1.2.2)) (splitSeed (x₁.2 x₁.1.1)))).isSome ∧
      ∃ c, programAt (key2 pP (pre0 A Hb y₀ x₁ s)) y₀.1.1.1.1.2.1 s.1
          (key2 pP (pre1 A Hb ((y₀, x₁), s)) c) ≠ s.1 (key2 pP (pre1 A Hb ((y₀, x₁), s)) c) := by
    by_contra hn
    refine hz (@realRun2_h23_congr (icPrg (rowFn s.2.2)) Hb (stOf x₁.1.2.1) (toBA (List.ofFn x₁.1.2.2))
      _ hHb hh x₁.2 s.1 _ s.2.1 x₁.1.1 fun hk c => ?_)
    by_contra hc
    exact hn ⟨hk, c, hc⟩
  obtain ⟨hk1, c, hc⟩ := hcol
  -- The programmed block is session 1's.
  have hblk : blk (preLen pP) (pre1 A Hb ((y₀, x₁), s)) = blk (preLen pP) (pre0 A Hb y₀ x₁ s) := by
    by_contra hne
    exact hc (programAt_apply_of_ne _ _ fun i hi => hne (congrArg Prod.fst hi).symm)
  rcases hf : firstHit y₀.1.1.1.1.2.1 with _ | ⟨ctr, δ⟩
  · exact Or.inl rfl
  · right
    -- Session 0 continues too: `bothOK` is symmetric.
    have hs1 : s1R Hb x₁ s = @out1 (icPrg (rowFn s.2.2)) (rec5 Hb s.2.1) CrtGen.tables (stOf x₁.1.2.1)
        (toBA (List.ofFn x₁.1.2.2)) (splitSeed (x₁.2 x₁.1.1)) :=
      (oR_s1 Hb A (A.msg true) true x₁ (fun _ => tS Hb A (A.msg false) y₀ s) s).symm.trans
        (@realRun2_out1 (icPrg (rowFn s.2.2)) Hb (stOf x₁.1.2.1) (toBA (List.ofFn x₁.1.2.2)) _ hHb hh x₁.2
          s.1 s.2.1 x₁.1.1)
    have hs0 : s1S Hb y₀ s = @simPhase1 (icPrg (rowFn s.2.2)) Hb (st1 (stOf y₀.1.2.1)) uovM y₀.1.1.1.1 ctr
        δ y₀.1.1.1.2 := by
      simp only [s1S, s1C, simRun2, hf]
    have hk0 : (kOf A (A.msg false) y₀.1.2.1 y₀.1.2.2 false (tR Hb A (A.msg true) x₁ s)
        (@simPhase1 (icPrg (rowFn s.2.2)) Hb (st1 (stOf y₀.1.2.1)) uovM y₀.1.1.1.1 ctr δ
          y₀.1.1.1.2)).isSome := by
      rw [kOf_isSome] at hk1 ⊢
      simp only [Bool.cond_true, Bool.cond_false] at hk1 ⊢
      rw [tR, hs1, ← hs0]
      exact hk1
    have ht := @preTail_outPre2 (icPrg (rowFn s.2.2)) Hb (stOf y₀.1.2.1) _ hHb CrtGen.tables uovM
      s.2.1 y₀.1.1 ctr δ hf hk0
    rw [hblk]
    exact ht

theorem deltaRO_event (hHb : HashesWF Hb) (z : (XS × XR) × ShP R)
    (hz : oR Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1)
        (pS Hb A (A.msg false) false z.1.1 (tR Hb A (A.msg true) z.1.2) z.2) ≠
      oR Hb A (A.msg true) true z.1.2 (tS Hb A (A.msg false) z.1.1) z.2) :
    firstHit z.1.1.1.1.1.1.2.1 = none ∨
      preTail (blk (preLen pP) (pre1 A Hb z)) = ba z.1.1.1.1.1.2.2.2.2.2 := by
  obtain ⟨⟨y₀, x₁⟩, s⟩ := z
  exact deltaRO_event' A hHb y₀ x₁ s hz

/-- **The programming collision term of PomFRIT**: `δ(A) ≤ noHitProb + 2⁻¹²⁸`. -/
theorem deltaRO_le (hHb : HashesWF Hb) : deltaRO Hb A ≤ noHitProb + 1 / 2 ^ 128 := by
  unfold deltaRO
  refine (pr_mono (Q := fun z => firstHit z.1.1.1.1.1.1.2.1 = none ∨
      preTail (blk (preLen pP) (pre1 A Hb z)) = ba z.1.1.1.1.1.2.2.2.2.2)
    fun z hz => ?_).trans ?_
  · exact deltaRO_event A hHb z hz
  refine pr_le_of_snd fun s => pr_le_of_snd fun x₁ => pr_le_of_snd fun g₀ =>
    pr_le_of_snd fun rr => pr_le_of_snd fun fb => ?_
  have h := pr_simCoins_tail_le (p := pP)
    (fun c => preTail (blk (preLen pP) (pre1 A Hb (((((c, fb), rr), g₀), x₁), s)))) fun c a => by
      simp only [pre1, tS, s1S, s1C_tail]
  rw [tail_pP] at h
  exact h

/-- **PomFRIT blindness with every term explicit, for every type of cipher rows** (`ZKRow R`,
`ZK2Row R`): `blindnessRO_leanG` with the collision terms bounded,

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q₃, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸. -/
theorem blindnessRO_lean_numG [ZKRow R] [ZK2Row R] (A : AdversaryRO R) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr ((XR × XR) × ShP R) (realGameRO Hashes.shake A false) -
        pr ((XR × XR) × ShP R) (realGameRO Hashes.shake A true)| ≤
      4 * ZKRow.εz R pP q3 (q5 + 1248) (qE + 18428) + 2 * noHitProb + 2 / 2 ^ 128 := by
  refine (blindnessRO_leanG A hA).trans (le_trans (add_le_add (add_le_add le_rfl
    (deltaRO_le A hashesWF_shake)) (deltaRO_le A.swap hashesWF_shake)) (le_of_eq ?_))
  ring

/-- **PomFRIT blindness in the random-oracle and ideal-cipher model, with every term explicit**:
`blindnessRO_lean` with the collision terms bounded,

    |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q₃, q₅ + 1248, q_E + 18428) + 2·noHitProb + 2·2⁻¹²⁸.

(`blindnessRO_lean_numG` at function rows.) -/
theorem blindnessRO_lean_num (A : AdversaryRO (Blk → Blk)) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr ((XR × XR) × ShP (Blk → Blk)) (realGameRO Hashes.shake A false) -
        pr ((XR × XR) × ShP (Blk → Blk)) (realGameRO Hashes.shake A true)| ≤
      4 * εRO q3 (q5 + 1248) (qE + 18428) + 2 * noHitProb + 2 / 2 ^ 128 :=
  blindnessRO_lean_numG A hA

end VoleMole.Privacy.PomFRIT
