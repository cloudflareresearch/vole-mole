import VoleMole.ZK.MainSharedSim

/-!
# Programming collisions on `main` (`lean/docs/zk.md` §4.2)

`pr_collide_zk` (`ZK/CollideRO.lean`) bounds the probability that a real proof, run on an `H₂³`
table that earlier simulations programmed, differs from the proof on the original table. It
applies zero knowledge a second time (`ZKRow.zk`, the label-row theorem). Here is the same bound
on `main` (`MainP`: no label rows), with `zk_rom_ic_h23_main_num` in place of the label-row
theorem.

The second application's distinguisher (`TailIn`: the tail of the grinding prefix recomputed from
the output is in a fixed set `T`) reads `H₅` only at the verifier's gate inputs of the output
(`progKeys5`, at most `312`) and the cipher at the reconstruction's nodes (`progKeysE`). On `main`
the one-proof theorem adds the (PU) term `Pr[mainPredIC]` of that read set on the simulated proof.
That term is **statistical**: on a simulated proof the read set is its own active gate inputs,
which do not depend on the simulator's uniform field `d` (`progKeys5_congr_f`), and neither do
the candidate offsets they name (`guessSetG_congr_f`); the witness prefix is a candidate iff the
offset `d[0..16) ⊕ w[0..16)` is one of at most `313` values, so (`pr_mainPredIC_act_le`)

    Pr[mainPredIC] ≤ 313·2⁻¹²⁸

whatever the witness. **`pr_collide_main`**: for a real proof on `main` and a programming `L` of
`H₂³` at prefix blocks whose tails lie in a fixed set `T`,

    Pr[ realRO(L s) ≠ realRO(s) ] ≤ 2⁻¹¹³ + εS(0, 4607) + 313·2⁻¹²⁸
                                     + noHitProb + |T|·2^(−8·16(d−1)).

Against the label-row bound (`2⁻¹¹³ + εRO(0, 312, 4607) + noHitProb + |T|·2^(−8·16(d−1))`, whose
`εRO` contains `(312 + 1)·2⁻¹²⁸`) the bound is the same.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

attribute [local instance] decEqW128

/-! ## The recomputation's reads, with the key sets explicit -/

section Reads

variable {R : Type} [CipherRow R] {p : Params}

/-- **The recomputed prefix reads `H₅` only at `progKeys5`** (`outPre_rd5` with the keys
explicit). -/
theorem outPre_congr5 (Hb : Hashes) (st : Statement) (o : Except String ByteArray) (s : ShG R p)
    (G5 : Tab5F) (h : ∀ k ∈ progKeys5 Hb st o s, s.2.1 k = G5 k) :
    @outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st G5 o =
      @outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1 o := by
  classical
  unfold progKeys5 at h
  unfold outPre
  cases o with
  | error e => rfl
  | ok b =>
    dsimp only at h ⊢
    have hmu : st.mu1 (rec5 Hb G5) = st.mu1 (rec5 Hb s.2.1) := by rw [rec5_mu1, rec5_mu1]
    have h4 : (rec5 Hb G5).hash .h4 = (rec5 Hb s.2.1).hash .h4 := by rw [rec5_h4, rec5_h4]
    have hA : (rec5 Hb G5).AgreeOff .h5 (rec5 Hb s.2.1) := by
      intro k hk; rw [rec5_agree_ne hk, rec5_agree_ne hk]
    refine @vPre_h5_congr (icPrg (rowFn s.2.2)) _ _ hA _ _ _ fun x hx => ?_
    rw [@vIn5_congr (icPrg (rowFn s.2.2)) _ st _ _ hmu h4] at hx
    exact withTable_h5_congr _ fun _ => (h _ (mem_image.2 ⟨x, List.mem_toFinset.2 hx, rfl⟩)).symm

/-- **The recomputed prefix reads the cipher only at `progKeysE`** (`outPre_rdE` with the keys
explicit). -/
theorem outPre_congrE (Hb : Hashes) (st : Statement) (o : Except String ByteArray) (s : ShG R p)
    (E : Blk → R) (h : ∀ k ∈ progKeysE Hb st o s, s.2.2 k = E k) :
    @outPre (icPrg (rowFn E)) Hb CrtGen.tables st s.2.1 o =
      @outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1 o := by
  unfold progKeysE at h
  unfold outPre
  cases o with
  | error e => rfl
  | ok b => exact (vPre_ic_congr _ _ _ _ fun k hk => rowFn_congr (h k hk)).symm

lemma card_progKeys5 (Hb : Hashes) (st : Statement) (o : Except String ByteArray) (s : ShG R p) :
    (progKeys5 Hb st o s).card ≤ 312 := by
  unfold progKeys5
  split
  · exact card_image_le.trans ((List.toFinset_card_le _).trans
      (@vIn5_length_le (icPrg (rowFn s.2.2)) _ _ _ _))
  · simp

lemma card_progKeysE' (Hb : Hashes) (st : Statement) (o : Except String ByteArray) (s : ShG R p) :
    (progKeysE Hb st o s).card ≤ 4607 := by
  unfold progKeysE
  split
  · exact rdKeys_card _ _ _ _
  · simp

end Reads

/-! ## The second application's (PU) term is statistical -/

section Act

variable (Hb : Hashes) (st : Statement)

/-- **The active gate inputs of a simulated proof do not depend on its field `d`**: the read set
of the recomputation depends on the simulator's fields only through the corrections. -/
lemma progKeys5_congr_f {c c' : SimCoins st.params} (hs : c.1 = c'.1) (hf : c.2.1 = c'.2.1)
    {G2 : Tab2G st.params} (G2' : Tab2G st.params) {u : USh} :
    progKeys5 Hb st (simulate st.params c) ((G2, u) : Sh st.params) =
      progKeys5 Hb st (simulate st.params c') ((G2', u) : Sh st.params) := by
  obtain ⟨s, f⟩ := c
  obtain ⟨s', f'⟩ := c'
  dsimp only at hs hf
  subst hs
  rcases h : firstHit s.2.1 with _ | ⟨ctr, δ⟩
  · have e : ∀ g : SimFields st.params, simulate st.params (s, g) = .error "grinding failed" :=
      fun g => by unfold simulate; rw [h]
    rw [e, e]
    rfl
  · have e : ∀ g : SimFields st.params,
        simulate st.params (s, g) = .ok (simAssemble st.params s ctr δ g) := fun g => by
      unfold simulate; rw [h]; rfl
    rw [e, e]
    unfold progKeys5
    dsimp only
    have k : ∀ g : SimFields st.params,
        @vIn5 (icPrg (rowFn u.2)) (rec5 Hb u.1) CrtGen.tables st (simAssemble st.params s ctr δ g) =
          Prover.gateInputsOff st.params CrtGen.tables (@pubOf (icPrg (rowFn u.2)) Hb st s δ).iv
            (@qcolsOf (icPrg (rowFn u.2)) st (@pubOf (icPrg (rowFn u.2)) Hb st s δ) δ (ba g.1))
            W128.zero := fun g => by
      rw [@vIn5_eq_vInOff (icPrg (rowFn u.2)),
        @vInOff_congr (icPrg (rowFn u.2)) (rec5 Hb u.1) CrtGen.tables st Hb (rec5_mu1 _)
          (rec5_h4 _)]
      exact @vInOff_simAssemble (icPrg (rowFn u.2)) Hb CrtGen.tables st s ctr δ g h _
    rw [k, k, hf]

/-- The candidate offsets named by a key set depend on the simulator's fields only through the
corrections. -/
lemma guessSetG_congr_f [HasPrg] (S : Finset (Bytes 37)) (s : Shared) {f f' : SimFields st.params}
    (hf : f.1 = f'.1) :
    guessSetG Hb CrtGen.tables st enc5 S s f = guessSetG Hb CrtGen.tables st enc5 S s f' := by
  unfold guessSetG guessOfG qcolsF
  rw [hf]

/-- The `H₅` reads of the second application: the recomputation's. -/
noncomputable def actQ5 (o : Except String ByteArray) (_ : Tab3) (G2 : Tab2G st.params) (G5 : Tab5F)
    (E : Cipher) : Finset (Bytes 37) :=
  progKeys5 Hb st o ((G2, G5, E) : Sh st.params)

/-- **The (PU) term of a distinguisher that reads `H₅` at the recomputation's keys is
`≤ 313·2⁻¹²⁸`**, for every witness prefix `r`: the candidate set does not depend on the
simulator's field `d`, and the candidate condition is `d[0..16) ⊕ r` in a set of at most `313`
offsets. -/
theorem pr_mainPredIC_act_le (hm : MainP st.params) (r : Bytes 16) :
    pr ((SimCoins st.params × Vis2 st.params) × Cipher)
      (mainPredIC Hb st hm (actQ5 Hb st) r) ≤ ((312 : ℕ) + 1) / 2 ^ 128 := by
  let Ω := ((Shared × (Bytes (16 * st.params.correctionBytes) ×
    Bytes (st.params.nMask * st.params.nMultBytes) × Bytes 64 × Bytes (16 * (st.params.qsDegree - 1)))) ×
      Vis2 st.params) × Cipher
  let fOf : Bytes st.params.witnessBytes → Ω → SimFields st.params := fun d ω =>
    (ω.1.1.2.1, ω.1.1.2.2.1, ω.1.1.2.2.2.1, d, ω.1.1.2.2.2.2)
  let e : Bytes st.params.witnessBytes × Ω ≃ (SimCoins st.params × Vis2 st.params) × Cipher :=
    { toFun := fun z => (((z.2.1.1.1, fOf z.1 z.2), z.2.1.2), z.2.2)
      invFun := fun c => (c.1.1.2.2.2.2.1, ((c.1.1.1, (c.1.1.2.1, c.1.1.2.2.1, c.1.1.2.2.2.1,
        c.1.1.2.2.2.2.2)), c.1.2), c.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let d0 : Bytes st.params.witnessBytes := fun _ => 0
  let G : Ω → Finset W128 := fun ω =>
    letI : HasPrg := icPrg ω.2
    guessSetG Hb CrtGen.tables st enc5
      (progKeys5 Hb st (simulate st.params (ω.1.1.1, fOf d0 ω))
        ((ω.1.2.2.1, ω.1.2.2.2, ω.2) : Sh st.params)) ω.1.1.1 (fOf d0 ω)
  have hG : ∀ ω, (G ω).card ≤ 312 + 1 := fun ω => by
    let _ : HasPrg := icPrg ω.2
    exact (card_guessSetG_le Hb CrtGen.tables st enc5 _ _ _).trans
      (Nat.succ_le_succ (card_progKeys5 Hb st _ _))
  rw [← pr_equiv e]
  refine le_of_eq_of_le (pr_congr fun z => ?_) (pr_thetaMain_le hm.hw (fun _ : Ω => r) G hG)
  unfold mainPredIC mainPred2
  rw [@mem_candidatesG (icPrg z.2.2)]
  unfold actQ5
  beta_reduce
  rw [progKeys5_congr_f Hb st (c := (e z).1.1) (c' := (z.2.1.1.1, fOf d0 z.2)) rfl rfl
    z.2.1.2.2.1,
    @guessSetG_congr_f Hb st (icPrg z.2.2) _ _ (e z).1.1.2 (fOf d0 z.2) rfl]
  rfl

end Act

/-! ## The collision bound on `main` -/

section Collide

variable {Hb : Hashes} {st : Statement} {w : ByteArray} {cs : ByteArray → ByteArray → System GF128}

/-- **The programming-collision bound on `main`** (`pr_collide_zk` with `zk_rom_ic_h23_main_num`):
a programming `L` of `H₂³` at prefix blocks whose tails lie in a fixed set `T` changes the real
proof with probability at most

    2⁻¹¹³ + εS(0, 4607) + 313·2⁻¹²⁸ + noHitProb + |T|·2^(−8·16(d−1)). -/
theorem pr_collide_main (hm : MainP st.params) (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hp : SmallParams st.params) {L : Sh st.params → Sh st.params}
    {B : Sh st.params → Finset (Bytes (preLen st.params))} (hL : ProgAt L B)
    (T : Finset ByteArray) (hT : ∀ s, ∀ b ∈ B s, preTail b ∈ T) :
    pr ((Bytes 16 × Tab3) × Sh st.params) (fun a =>
        realRO st.params Hb st w a.1.1 a.1.2 (L a.2) ≠ realRO st.params Hb st w a.1.1 a.1.2 a.2) ≤
      1 / 2 ^ 113 + εS 0 4607 + ((312 : ℕ) + 1) / 2 ^ 128 +
        (noHitProb + T.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1)))) := by
  have hlab := hm.hlab
  -- The distinguisher: the recomputed prefix's tail is in `T`.
  let D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop :=
    fun o _ G2 G5 E => TailIn Hb st T o ((G2, G5, E) : Sh st.params)
  have hsplit : ∀ a : (Bytes 16 × Tab3) × Sh st.params,
      realRO st.params Hb st w a.1.1 a.1.2 (L a.2) ≠ realRO st.params Hb st w a.1.1 a.1.2 a.2 →
      GrindBad CrtGen.tables (a.2.1 ∘ key2 st.params (preRO Hb st w a.1.1 a.1.2 a.2)) ∨
        D (realRO st.params Hb st w a.1.1 a.1.2 a.2) a.1.2 a.2.1 a.2.2.1 a.2.2.2 := by
    intro a h
    by_cases hg : GrindBad CrtGen.tables (a.2.1 ∘ key2 st.params (preRO Hb st w a.1.1 a.1.2 a.2))
    · exact Or.inl hg
    · right
      have hmem : blk (preLen st.params) (preRO Hb st w a.1.1 a.1.2 a.2) ∈ B a.2 := by
        by_contra hn
        exact h (realRO_progAt hzk hHb hlab hL a.1.1 a.1.2 a.2 hn)
      obtain ⟨proof, hok, hv⟩ := realRO_vPre hzk hHb hlab a.1.1 a.1.2 a.2 hg
      show preTail (blk (preLen st.params) (@outPre (icPrg (rowFn a.2.2.2)) Hb CrtGen.tables st
        a.2.2.1 (realRO st.params Hb st w a.1.1 a.1.2 a.2))) ∈ T
      rw [hok, hv]
      exact hT _ _ hmem
  have hz := zk_rom_ic_h23_main_num Hb st w hm hzk hHb hp D (fun _ _ _ _ _ => ∅)
    (fun _ _ _ _ _ _ _ => Iff.rfl) (q3 := 0) (fun _ _ _ _ _ => le_rfl) (actQ5 Hb st)
    (fun o G3 G2 G5 G5' E h => by
      show TailIn Hb st T o ((G2, G5, E) : Sh st.params) ↔ TailIn Hb st T o ((G2, G5', E) : Sh st.params)
      unfold TailIn
      rw [outPre_congr5 Hb st o ((G2, G5, E) : Sh st.params) G5' h])
    (fun o _ G2 G5 E => progKeysE Hb st o ((G2, G5, E) : Sh st.params))
    (fun o G3 G2 G5 E E' h => by
      show TailIn Hb st T o ((G2, G5, E) : Sh st.params) ↔ TailIn Hb st T o ((G2, G5, E') : Sh st.params)
      unfold TailIn
      rw [outPre_congrE Hb st o ((G2, G5, E) : Sh st.params) E' h])
    (qE := 4607) (fun o _ G2 G5 E => card_progKeysE' Hb st o _)
  -- the real side, on the tape of `pr_collide_main`
  let e : (Bytes 16 × Tab3) × Sh st.params ≃
      ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher :=
    { toFun := fun a => (((a.1.1, a.2.1), (a.1.2, a.2.2.1)), a.2.2.2)
      invFun := fun c => ((c.1.1.1, c.1.2.1), (c.1.1.2, c.1.2.2, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hreal : pr ((Bytes 16 × Tab3) × Sh st.params) (fun a =>
      D (realRO st.params Hb st w a.1.1 a.1.2 a.2) a.1.2 a.2.1 a.2.2.1 a.2.2.2) =
      pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@Prover.prove (icPrg c.2) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 c.1.2.2 c.2) := by
    rw [← pr_equiv e]
    rfl
  have hsim : pr ((SimCoins st.params × Vis2 st.params) × Cipher) (fun c =>
      D (simulate st.params c.1.1) c.1.2.1
        (@simTab (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
          c.1.2.2.1) c.1.2.2.2 c.2) ≤
      noHitProb + T.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) := by
    have e1 : ∀ c : (SimCoins st.params × Vis2 st.params) × Cipher,
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
            c.1.2.2.1) c.1.2.2.2 c.2 ↔ simTail c.1.1 ∈ T := fun c => by
      show preTail (blk (preLen st.params) (@outPre (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2
        (simulate st.params c.1.1))) ∈ T ↔ _
      rw [@preTail_outPre st.params (icPrg c.2) Hb hHb CrtGen.tables st rfl c.1.2.2.2 c.1.1]
    rw [pr_congr e1]
    have f1 := pr_prod_fst (β := Cipher) (fun c : SimCoins st.params × Vis2 st.params => simTail c.1 ∈ T)
    have f2 := pr_prod_fst (β := Vis2 st.params) (fun c : SimCoins st.params => simTail c ∈ T)
    exact (f1.trans f2).le.trans (pr_simTail_mem T)
  have hP := pr_mainPredIC_act_le Hb st hm (wPre w)
  have hR : pr ((Bytes 16 × Tab3) × Sh st.params) (fun a =>
      D (realRO st.params Hb st w a.1.1 a.1.2 a.2) a.1.2 a.2.1 a.2.2.1 a.2.2.2) ≤
      εS 0 4607 + ((312 : ℕ) + 1) / 2 ^ 128 +
        (noHitProb + T.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1)))) := by
    rw [hreal]
    have := (abs_sub_le_iff.1 hz).1
    unfold εS
    simp only [Nat.cast_zero, zero_div, zero_add, Nat.cast_ofNat] at this ⊢
    linarith
  refine (pr_mono hsplit).trans ((pr_or_le _ _).trans ?_)
  have := pr_grindBad_preRO (R := Blk → Blk) (Hb := Hb) (st := st) (w := w)
  linarith

end Collide

end VoleMole.ZK.Sim
