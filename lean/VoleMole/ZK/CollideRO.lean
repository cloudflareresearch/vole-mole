import VoleMole.ZK.ReadsRO

/-!
# Programming collisions: when a real proof reads `H₂³` where a simulator programmed it

The hybrids of the privacy games (`Privacy.hop_ro`) carry an explicit collision term: the
probability that a real proof, run on the tables earlier simulations programmed, differs from the
proof on the original tables. Here are the facts that bound it (`lean/docs/zk.md` §10.2).

* **What the real prover reads of `H₂³`** (`prove_recH_eq`): the executable prover with the record
  `recH` is the run of hybrid H2 at the seed and `iv_pre` from its `H₃` slice and the `H₂³` table's
  answers at the grinding points `pre ‖ ctr ‖ 11` of its own prefix `pre` (`preR`, computed without
  `H₂³`). So a programming that leaves the keys with prefix block `blk pre` alone leaves the proof
  alone (`realRO_progAt`). And unless the grinding outcome is bad (`GrindBad`), the proof is
  produced and the verifier recomputes `pre` from it (`realRO_vPre`, from `hyb3_vPre`).
* **What a simulator programs** (`progRO_progAt`): the keys of one prefix block, the block of the
  prefix recomputed from its proof. **The simulated opening reconstructs** (`reconstruct_openingOf`:
  the opening `openingOf` has the right size, its seeds fit, the padding is zero), so the
  recomputed prefix is `chal2 ‖ qs_check ‖ ã` with `|chal2 ‖ qs_check| = 72` (`vPre_simAssemble`);
  its last `16·(d − 1)` bytes (`preTail`) are the simulator's uniform `ã`, or a fixed block if the
  simulation produced no proof (`simTail`, `preTail_progRO`).
* **The collision bound with a second application of zero knowledge** (`pr_collide_zk`): for a
  real proof whose statement may depend on the earlier simulations, and a programming `L` whose
  programmed prefix blocks have their tails in a fixed set `T`,

      Pr[ realRO(L s) ≠ realRO(s) ] ≤ 2⁻¹¹³ + εRO(0, 312, 4607) + noHitProb + |T|·2^(−8·16(d−1)).

  A collision needs the real prefix's tail in `T`; unless the grinding outcome is bad (`≤ 2⁻¹¹³`,
  the answers at the real prefix are uniform: the prefix does not read `H₂³`) that tail is the one
  the verifier recomputes from the proof, a distinguisher of the proof and the tables reading `H₅`
  and the cipher at `312`, `4607` keys; by zero knowledge (`zk_ro`) its probability is that for the
  simulated proof up to `εRO(0, 312, 4607)`, and the simulated proof's tail is its own uniform `ã`.

Everything is stated for any type of cipher rows (`ShG R p`); `pr_collide_zk` for a row type with
`ZKRow R`, with `ZKRow.εz R p 0 312 4607` (`εRO(0, 312, 4607)` for function rows,
`εROPm p 0 312 4607` for permutation rows) in place of `εRO(0, 312, 4607)`.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## Probability bookkeeping -/

section PrLemmas

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A bound for every first coordinate is a bound. -/
lemma pr_le_of_fst [Nonempty α] {P : α × β → Prop} {ε : ℝ}
    (h : ∀ a, pr β (fun b => P (a, b)) ≤ ε) : pr (α × β) P ≤ ε := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, div_le_iff₀ hα]
  calc ∑ a, pr β (fun b => P (a, b)) ≤ ∑ _a : α, ε := Finset.sum_le_sum fun a _ => h a
    _ = ε * Fintype.card α := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- A bound for every second coordinate is a bound. -/
lemma pr_le_of_snd [Nonempty β] {P : α × β → Prop} {ε : ℝ}
    (h : ∀ b, pr α (fun a => P (a, b)) ≤ ε) : pr (α × β) P ≤ ε := by
  rw [← pr_equiv (Equiv.prodComm β α)]
  exact pr_le_of_fst fun b => h b

/-- **A uniform byte string is in a fixed set `T` with probability `≤ |T| / 2^(8n)`.** -/
lemma pr_ba_mem_le {n : ℕ} (T : Finset ByteArray) :
    pr (Bytes n) (fun a => ba a ∈ T) ≤ T.card / 2 ^ (8 * n) := by
  have h := pr_mem_le (ba (n := n)) ba_injective T
  rw [show Fintype.card (Bytes n) = 2 ^ (8 * n) from VoleMole.Prob.card_bytes n] at h
  exact_mod_cast h

end PrLemmas

/-! ## The simulated opening reconstructs -/

section Opening

variable [HasPrg]

lemma openingOf_body_size (delta : ByteArray) (coms : Fin BAVC.tau → Bytes 32)
    (seeds : Fin 105 → Bytes 16) (h : openCount delta ≤ 105) :
    ((List.range (openCount delta)).foldl
      (fun acc k => acc ++ if h : k < 105 then ba (seeds ⟨k, h⟩) else ByteArray.empty)
      ((List.range BAVC.tau).foldl
        (fun acc i => acc ++ if h : i < BAVC.tau then ba (coms ⟨i, h⟩) else ByteArray.empty)
        ByteArray.empty)).size = BAVC.tau * BAVC.hashLen + 16 * openCount delta := by
  have h1 := size_foldl_range (fun i => if h : i < BAVC.tau then ba (coms ⟨i, h⟩)
    else ByteArray.empty) 32 BAVC.tau (fun i hi => by simp [hi]) ByteArray.empty
  have h2 := size_foldl_range (fun k => if h : k < 105 then ba (seeds ⟨k, h⟩)
    else ByteArray.empty) 16 (openCount delta) (fun k hk => by simp [show k < 105 by omega])
  rw [h2, h1, ByteArray.size_empty]
  have e2 : BAVC.tau = 17 := rfl
  have e3 : BAVC.hashLen = 32 := rfl
  rw [e2, e3]

/-- **The simulator's opening is well formed** for an accepted `Δ` (at most `T_OPEN` seeds): the
right size, the seeds fit, the padding is zero. -/
theorem badOpening_openingOf (delta : ByteArray) (coms : Fin BAVC.tau → Bytes 32)
    (seeds : Fin 105 → Bytes 16) (h : openCount delta ≤ 105) :
    badOpening (openingOf delta coms seeds) delta = false := by
  have hs := openingOf_size delta coms seeds h
  have hb := openingOf_body_size delta coms seeds h
  have hn := openNodes_size delta
  have ho : BAVC.openSize = BAVC.tau * BAVC.hashLen + 105 * 16 := rfl
  unfold badOpening
  simp only [hs, bne_self_eq_false, Bool.false_or, hn, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    not_lt, List.any_eq_false, List.mem_range, bne_iff_ne, ne_eq, not_not]
  refine ⟨by omega, fun k hk => ?_⟩
  unfold openingOf
  dsimp only
  rw [get!_append, hb]
  split_ifs with h'
  · omega
  · exact get!_zeros _ _

theorem reconstruct_openingOf (iv delta : ByteArray) (coms : Fin BAVC.tau → Bytes 32)
    (seeds : Fin 105 → Bytes 16) (h : openCount delta ≤ 105) :
    (BAVC.reconstruct iv (openingOf delta coms seeds) delta).isSome := by
  rw [reconstruct_eq, badOpening_openingOf delta coms seeds h]
  rfl

/-- **The prefix recomputed from a simulated proof**: `chal2 ‖ qs_check` (`72` bytes) and the
simulator's uniform `ã`. -/
theorem vPre_simAssemble (Hs : Hashes) (hHs : HashesWF Hs) (T : CrtTables) (st : Statement)
    (s : Shared) (ctr : ℕ) (δ : Bytes 16) (f : SimFields st.params)
    (hf : firstHit s.2.1 = some (ctr, δ)) :
    ∃ X : ByteArray, X.size = 72 ∧
      vPre Hs T st (simAssemble st.params s ctr δ f) = X ++ ba f.2.2.2.2 := by
  have hacc := firstHit_accepts hf
  have hoc : openCount (ba δ) ≤ 105 := by
    unfold accepts at hacc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc; exact hacc.2
  set pf : Proof := { params := st.params, bytes := simAssemble st.params s ctr δ f } with hpf
  have pfO : pf.opening = openingOf (ba δ) s.2.2.1 s.2.2.2 :=
    (fields_assemble st.params _).2.2.2.2.2.1.trans (fit_of_size (openingOf_size _ _ _ hoc))
  have pfD : pf.delta = ba δ := (fields_assemble st.params _).2.2.2.2.2.2.1.trans
    (fit_of_size (size_ba _))
  have pfQ : pf.qsProof = ba f.2.2.2.2 := (fields_assemble st.params _).2.2.2.2.1.trans
    (fit_of_size (by rw [size_ba, Nat.mul_comm]))
  obtain ⟨leaves, hl⟩ := Option.isSome_iff_exists.1
    (reconstruct_openingOf (ivOf Hs pf (st.mu1 Hs)) (ba δ) s.2.2.1 s.2.2.2 hoc)
  show ∃ X : ByteArray, X.size = 72 ∧ vPreP Hs T st pf = X ++ ba f.2.2.2.2
  unfold vPreP
  rw [pfO, pfD, hl]
  dsimp only
  rw [vPreOf, pfQ]
  refine ⟨_, ?_, rfl⟩
  rw [ByteArray.size_append, gfToBytes_size', chal2, hHs]
  rfl

end Opening

/-! ## The tail of a prefix block -/

section Tail

variable {p : Params}

lemma preLen_eq (p : Params) : preLen p = 72 + 16 * (p.qsDegree - 1) := by
  unfold preLen; omega

/-- **The last `16·(d − 1)` bytes of a grinding-prefix block**: the field `ã` of
`chal2 ‖ qs_check ‖ ã`. -/
def preTail (b : Bytes (preLen p)) : ByteArray := (ba b).extract 72 (preLen p)

lemma extract_append_size (X Y : ByteArray) : (X ++ Y).extract X.size (X.size + Y.size) = Y := by
  apply byteArray_ext_get!
  · rw [ByteArray.size_extract, ByteArray.size_append]; omega
  intro k hk
  rw [ByteArray.size_extract, ByteArray.size_append] at hk
  rw [get!_extract _ (by omega) (by rw [ByteArray.size_append]), get!_append]
  simp only [show ¬ (X.size + k < X.size) by omega, ↓reduceIte, Nat.add_sub_cancel_left]

/-- `preTail` of a prefix `X ‖ Y` with `|X| = 72` is `Y`. -/
lemma preTail_blk {X Y : ByteArray} (hX : X.size = 72) (hY : Y.size = 16 * (p.qsDegree - 1)) :
    preTail (blk (preLen p) (X ++ Y)) = Y := by
  have hs : (X ++ Y).size = preLen p := by rw [ByteArray.size_append, hX, hY, preLen_eq]
  rw [preTail, ba_blk_of_size hs, preLen_eq, ← hX, ← hY]
  exact extract_append_size X Y

/-- **The tail of the prefix block a simulation programs**: its uniform `ã`, or the empty
prefix's tail if it produced no proof. -/
def simTail (c : SimCoins p) : ByteArray :=
  match firstHit c.1.2.1 with
  | none => preTail (p := p) (blk (preLen p) ByteArray.empty)
  | some _ => ba c.2.2.2.2.2

variable [HasPrg]

/-- **The tail of the prefix recomputed from a simulated proof is the simulation's tail.** -/
theorem preTail_outPre {Hb : Hashes} (hHb : HashesWF Hb) (T : CrtTables) {st : Statement}
    (hp : st.params = p) (G5 : Tab5F) (c : SimCoins p) :
    preTail (blk (preLen p) (outPre Hb T st G5 (simulate p c))) = simTail c := by
  subst hp
  unfold simTail
  rcases hf : firstHit c.1.2.1 with _ | ⟨ctr, δ⟩
  · simp only [simulate, hf, outPre]
  · have e : simulate st.params c = .ok (simAssemble st.params c.1 ctr δ c.2) := by
      simp only [simulate, hf, simAssemble]
    obtain ⟨X, hX, hv⟩ := vPre_simAssemble (rec5 Hb G5) (hHb.withTable .h5 enc5 G5) T st c.1
      ctr δ c.2 hf
    simp only [e, outPre, hv]
    exact preTail_blk hX (size_ba _)

end Tail

/-! ## Programmings at prefix blocks -/

section ProgAt

variable {R : Type} [CipherRow R] {p : Params}

/-- **A programming of `H₂³` at the prefix blocks `B s`**: it changes only the `H₂³` table, and
there only the keys whose prefix block is in `B s`. -/
def ProgAt (L : ShG R p → ShG R p) (B : ShG R p → Finset (Bytes (preLen p))) : Prop :=
  (∀ s, (L s).2 = s.2) ∧ ∀ s (k : K2 p), k.1 ∉ B s → (L s).1 k = s.1 k

lemma ProgAt.id : ProgAt (fun s : ShG R p => s) (fun _ => ∅) :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

lemma ProgAt.comp {L L' : ShG R p → ShG R p} {B B' : ShG R p → Finset (Bytes (preLen p))}
    (h : ProgAt L B) (h' : ProgAt L' B') :
    ProgAt (fun s => L (L' s)) (fun s => B (L' s) ∪ B' s) := by
  refine ⟨fun s => (h.1 _).trans (h'.1 s), fun s k hk => ?_⟩
  rw [Finset.mem_union, not_or] at hk
  exact (h.2 _ k hk.1).trans (h'.2 s k hk.2)

lemma ProgAt.ite {L : ShG R p → ShG R p} {B : ShG R p → Finset (Bytes (preLen p))} (c : Prop)
    [Decidable c] (h : ProgAt L B) :
    ProgAt (fun s => if c then L s else s) (fun s => if c then B s else ∅) := by
  by_cases hc : c
  · simpa only [hc, ↓reduceIte] using h
  · simpa only [hc, ↓reduceIte] using (ProgAt.id (p := p))

lemma ProgAt.ite_else {L : ShG R p → ShG R p} {B : ShG R p → Finset (Bytes (preLen p))} (c : Prop)
    [Decidable c] (h : ProgAt L B) :
    ProgAt (fun s => if c then s else L s) (fun s => if c then ∅ else B s) := by
  by_cases hc : c
  · simpa only [hc, ↓reduceIte] using (ProgAt.id (p := p))
  · simpa only [hc, ↓reduceIte] using h

lemma ProgAt.mono {L : ShG R p → ShG R p} {B B' : ShG R p → Finset (Bytes (preLen p))} (h : ProgAt L B)
    (hB : ∀ s, B s ⊆ B' s) : ProgAt L B' :=
  ⟨h.1, fun s k hk => h.2 s k fun h' => hk (hB s h')⟩

lemma ProgAt.congr {L L' : ShG R p → ShG R p} {B : ShG R p → Finset (Bytes (preLen p))} (h : ProgAt L B)
    (e : ∀ s, L' s = L s) : ProgAt L' B :=
  ⟨fun s => by rw [e]; exact h.1 s, fun s k hk => by rw [e]; exact h.2 s k hk⟩

/-- The prefix block a simulation programs, on the tables `s`. -/
noncomputable def simBlk (Hb : Hashes) (st : Statement) (c : SimCoins p) (s : ShG R p) :
    Bytes (preLen p) :=
  blk (preLen p) (@outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1 (simulate p c))

/-- **The simulator programs one prefix block**, the one of the prefix it recomputes. -/
theorem progRO_progAt (Hb : Hashes) (st : Statement) (c : SimCoins p) :
    ProgAt (progRO (R := R) p Hb st c) (fun s => {simBlk Hb st c s}) := by
  refine ⟨fun _ => rfl, fun s k hk => ?_⟩
  refine programAt_apply_of_ne _ _ fun i hi => hk ?_
  rw [← hi, Finset.mem_singleton]
  rfl

/-- **The tail of the block a simulation programs** is its `simTail`. -/
theorem preTail_simBlk {Hb : Hashes} (hHb : HashesWF Hb) {st : Statement} (hp : st.params = p)
    (c : SimCoins p) (s : ShG R p) : preTail (simBlk Hb st c s) = simTail c :=
  @preTail_outPre p (icPrg (rowFn s.2.2)) Hb hHb CrtGen.tables st hp s.2.1 c

end ProgAt

/-! ## What the real prover reads of `H₂³` -/

section Real

variable {R : Type} [CipherRow R]

/-- **The executable prover with the record `recH`** is the run of hybrid H2 at the seed and
`iv_pre` of its `H₃` slice and the `H₂³` table's answers at its own grinding prefix. -/
theorem prove_recH_eq [HasPrg] {Hb : Hashes} {st : Statement} {w : ByteArray}
    {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (ρ : Bytes 16) (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5F) :
    Prover.prove (recH Hb st w G3 G2 G5) CrtGen.tables st w (ba ρ) =
      hyb3 (recB Hb st w G3 G5) CrtGen.tables st w ((splitSeed (G3 ρ)).2,
        G2 ∘ key2 st.params (preR Hb CrtGen.tables st w G5 (splitSeed (G3 ρ))))
        (hiddenOut st.params (ivOfPre Hb st (splitSeed (G3 ρ)).2)
          (ba (deltaOf (G2 ∘ key2 st.params (preR Hb CrtGen.tables st w G5 (splitSeed (G3 ρ))))))
          (splitSeed (G3 ρ)).1) := by
  have hR : RunHyp (recH Hb st w G3 G2 G5) CrtGen.tables st w cs :=
    ⟨hzk, recH_wf hHb _ _ _, bavcComplete, fun rho => crtComplete _ _ _ _ rho _ hlab, hlab⟩
  rw [← proveP_prove _ CrtGen.tables st w hR ρ, prePrefix_recH, proveP, recH_h3Seed]
  exact runP_recH Hb CrtGen.tables st w hHb hzk.q G3 G2 G5 _

/-- **The real prover's grinding prefix** on the shared tables (it reads neither `H₃` beyond the
seed nor `H₂³`). -/
noncomputable def preRO (Hb : Hashes) (st : Statement) (w : ByteArray) (ρ : Bytes 16) (G3 : Tab3)
    (s : ShG R st.params) : ByteArray :=
  @preR (icPrg (rowFn s.2.2)) Hb CrtGen.tables st w s.2.1 (splitSeed (G3 ρ))

variable {Hb : Hashes} {st : Statement} {w : ByteArray} {cs : ByteArray → ByteArray → System GF128}

lemma realRO_eq (ρ : Bytes 16) (G3 : Tab3) (s : ShG R st.params) :
    realRO st.params Hb st w ρ G3 s =
      @Prover.prove (icPrg (rowFn s.2.2)) (recH Hb st w G3 s.1 s.2.1) CrtGen.tables st w (ba ρ)
        st.params.witnessBytes := rfl

/-- **A programming that leaves the real prover's prefix block alone leaves its proof alone.** -/
theorem realRO_progAt (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) {L : ShG R st.params → ShG R st.params}
    {B : ShG R st.params → Finset (Bytes (preLen st.params))} (hL : ProgAt L B) (ρ : Bytes 16)
    (G3 : Tab3) (s : ShG R st.params) (hn : blk (preLen st.params) (preRO Hb st w ρ G3 s) ∉ B s) :
    realRO st.params Hb st w ρ G3 (L s) = realRO st.params Hb st w ρ G3 s := by
  have h2 : L s = ((L s).1, s.2) := Prod.ext rfl (hL.1 s)
  rw [realRO_eq, realRO_eq, h2]
  dsimp only
  rw [@prove_recH_eq (icPrg (rowFn s.2.2)) Hb st w cs hzk hHb hlab, @prove_recH_eq (icPrg (rowFn s.2.2)) Hb st w cs
    hzk hHb hlab]
  have e : (L s).1 ∘ key2 st.params (@preR (icPrg (rowFn s.2.2)) Hb CrtGen.tables st w s.2.1
      (splitSeed (G3 ρ))) = s.1 ∘ key2 st.params (@preR (icPrg (rowFn s.2.2)) Hb CrtGen.tables st w s.2.1
      (splitSeed (G3 ρ))) :=
    funext fun c => hL.2 s _ hn
  rw [e]

/-- **Completeness of the recomputation on real proofs**: unless the grinding outcome at the
prover's prefix is bad, the real prover produces a proof, and the prefix recomputed from it is the
prover's. -/
theorem realRO_vPre (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) (ρ : Bytes 16) (G3 : Tab3)
    (s : ShG R st.params)
    (hg : ¬ GrindBad CrtGen.tables (s.1 ∘ key2 st.params (preRO Hb st w ρ G3 s))) :
    ∃ proof, realRO st.params Hb st w ρ G3 s = .ok proof ∧
      @outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1 (.ok proof) = preRO Hb st w ρ G3 s := by
  rw [realRO_eq, @prove_recH_eq (icPrg (rowFn s.2.2)) Hb st w cs hzk hHb hlab]
  have hwf : HashesWF (recB Hb st w G3 s.2.1) := recH_wf hHb G3 _ s.2.1
  obtain ⟨proof, hok, hv⟩ := @hyb3_vPre (icPrg (rowFn s.2.2)) _ st w hwf cs hzk hlab (splitSeed (G3 ρ)) _ hg
  have hiv : ivOfPre (recB Hb st w G3 s.2.1) st = ivOfPre Hb st :=
    @recH_ivOfPre (icPrg (rowFn s.2.2)) Hb st w G3 (fun _ => 0) s.2.1
  have hvp : @vPre (icPrg (rowFn s.2.2)) (recB Hb st w G3 s.2.1) CrtGen.tables st =
      @vPre (icPrg (rowFn s.2.2)) (rec5 Hb s.2.1) CrtGen.tables st :=
    @vPre_recH (icPrg (rowFn s.2.2)) Hb CrtGen.tables st w G3 (fun _ => 0) s.2.1
  have hpp : @prePrefix (icPrg (rowFn s.2.2)) (recB Hb st w G3 s.2.1) CrtGen.tables st w =
      @preR (icPrg (rowFn s.2.2)) Hb CrtGen.tables st w s.2.1 :=
    @prePrefix_recH (icPrg (rowFn s.2.2)) Hb CrtGen.tables st w G3 (fun _ => 0) s.2.1
  rw [hiv] at hok
  rw [hvp, hpp] at hv
  exact ⟨proof, hok, hv⟩

end Real

/-! ## The recomputation's reads, and the simulated tail -/

section Reads

variable {R : Type} [CipherRow R] {p : Params}

/-- **The recomputed prefix reads `H₅` at `312` keys** (the verifier's gate inputs). -/
theorem outPre_rd5 (Hb : Hashes) (st : Statement) (o : Except String ByteArray) :
    Rd5 (fun s : ShG R p => @outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1 o) 312 := by
  classical
  refine ⟨progKeys5 Hb st o, fun s => ?_, fun s G5 h => ?_⟩
  · unfold progKeys5
    split
    · exact card_image_le.trans ((List.toFinset_card_le _).trans
        (@vIn5_length_le (icPrg (rowFn s.2.2)) _ _ _ _))
    · simp
  · unfold progKeys5 at h
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

/-- **The recomputed prefix reads the cipher at `4607` keys** (the reconstruction's nodes). -/
theorem outPre_rdE (Hb : Hashes) (st : Statement) (o : Except String ByteArray) :
    RdE (fun s : ShG R p => @outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1 o) 4607 := by
  classical
  refine ⟨progKeysE Hb st o, fun s => ?_, fun s E h => ?_⟩
  · unfold progKeysE
    split
    · exact rdKeys_card _ _ _ _
    · simp
  · unfold progKeysE at h
    unfold outPre
    cases o with
    | error e => rfl
    | ok b => exact (vPre_ic_congr _ _ _ _ fun k hk => rowFn_congr (h k hk)).symm

/-- **A simulation's tail is in a fixed set** with probability `≤ noHitProb + |T|·2^(−8·16(d−1))`
(no proof, or the uniform `ã` in `T`). -/
theorem pr_simTail_mem (T : Finset ByteArray) :
    pr (SimCoins p) (fun c => simTail c ∈ T) ≤
      noHitProb + T.card / 2 ^ (8 * (16 * (p.qsDegree - 1))) := by
  refine (pr_mono (Q := fun c : SimCoins p => firstHit c.1.2.1 = none ∨ ba c.2.2.2.2.2 ∈ T)
    fun c hc => ?_).trans ((pr_or_le _ _).trans (add_le_add (le_of_eq ?_) ?_))
  · unfold simTail at hc
    rcases hf : firstHit c.1.2.1 with _ | ⟨ctr, δ⟩
    · exact Or.inl rfl
    · rw [hf] at hc; exact Or.inr hc
  · have e1 := pr_prod_fst (β := SimFields p) (fun s : Shared => firstHit s.2.1 = none)
    have e2 := pr_prod_snd (α := Bytes 16)
      (fun x : Grind × (Fin BAVC.tau → Bytes 32) × (Fin 105 → Bytes 16) => firstHit x.1 = none)
    have e3 := pr_prod_fst (β := (Fin BAVC.tau → Bytes 32) × (Fin 105 → Bytes 16))
      (fun g : Grind => firstHit g = none)
    exact e1.trans (e2.trans e3)
  · have e1 := pr_prod_snd (α := Shared) (fun f : SimFields p => ba f.2.2.2.2 ∈ T)
    have e2 := pr_prod_snd (α := Bytes (16 * p.correctionBytes))
      (fun f : Bytes (p.nMask * p.nMultBytes) × Bytes 64 × Bytes p.witnessBytes ×
        Bytes (16 * (p.qsDegree - 1)) => ba f.2.2.2 ∈ T)
    have e3 := pr_prod_snd (α := Bytes (p.nMask * p.nMultBytes))
      (fun f : Bytes 64 × Bytes p.witnessBytes × Bytes (16 * (p.qsDegree - 1)) => ba f.2.2 ∈ T)
    have e4 := pr_prod_snd (α := Bytes 64)
      (fun f : Bytes p.witnessBytes × Bytes (16 * (p.qsDegree - 1)) => ba f.2 ∈ T)
    have e5 := pr_prod_snd (α := Bytes p.witnessBytes)
      (fun f : Bytes (16 * (p.qsDegree - 1)) => ba f ∈ T)
    exact (e1.trans (e2.trans (e3.trans (e4.trans e5)))).le.trans (pr_ba_mem_le T)

end Reads

/-! ## The collision bound, with a second application of zero knowledge -/

section Collide

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]
variable {Hb : Hashes} {st : Statement} {w : ByteArray} {cs : ByteArray → ByteArray → System GF128}

/-- The grinding answers at the real prover's prefix are uniform: the prefix does not read
`H₂³`. -/
theorem pr_grindBad_preRO :
    pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
      GrindBad CrtGen.tables (a.2.1 ∘ key2 st.params (preRO Hb st w a.1.1 a.1.2 a.2))) ≤
      1 / 2 ^ 113 := by
  refine pr_le_of_fst fun x => pr_le_of_snd fun r => ?_
  have h := close_restrict (R := Bytes 16)
    (key2_injective st.params (@preR (icPrg (rowFn r.2)) Hb CrtGen.tables st w r.1 (splitSeed (x.2 x.1))))
    (GrindBad CrtGen.tables)
  rw [abs_nonpos_iff, sub_eq_zero] at h
  exact (le_of_eq h).trans grindBad_le_113

/-- **A collision puts the real prefix's tail among the programmed tails.** -/
theorem realRO_ne_tail (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    {L : ShG R st.params → ShG R st.params} {B : ShG R st.params → Finset (Bytes (preLen st.params))}
    (hL : ProgAt L B) {T : ShG R st.params → Finset ByteArray}
    (hT : ∀ s, ∀ b ∈ B s, preTail b ∈ T s) (ρ : Bytes 16) (G3 : Tab3) (s : ShG R st.params)
    (h : realRO st.params Hb st w ρ G3 (L s) ≠ realRO st.params Hb st w ρ G3 s) :
    preTail (blk (preLen st.params) (preRO Hb st w ρ G3 s)) ∈ T s := by
  by_contra hn
  exact h (realRO_progAt hzk hHb hlab hL ρ G3 s fun hb => hn (hT s _ hb))

/-- **A simulation's tail hits a fixed value** with probability `≤ noHitProb + 2^(−8·16(d−1))`. -/
theorem pr_simTail_eq_le {p : Params} (t : ByteArray) :
    pr (SimCoins p) (fun c => t = simTail c) ≤
      noHitProb + 1 / 2 ^ (8 * (16 * (p.qsDegree - 1))) := by
  have h := pr_simTail_mem (p := p) {t}
  rw [Finset.card_singleton, Nat.cast_one] at h
  refine le_trans (le_of_eq (pr_congr fun c => ?_)) h
  rw [Finset.mem_singleton, eq_comm]

lemma pr_false {α : Type*} [Fintype α] : pr α (fun _ => False) = 0 := by
  classical
  rw [pr_def]; simp

/-- The distinguisher of the second application of zero knowledge: the tail of the prefix
recomputed from the output is in `T`. -/
def TailIn {p : Params} (Hb : Hashes) (st : Statement) (T : Finset ByteArray)
    (o : Except String ByteArray) (s : ShG R p) : Prop :=
  preTail (blk (preLen p) (@outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1 o)) ∈ T

/-- **The programming-collision bound for a real proof** whose statement may depend on the
earlier simulations: a programming `L` at prefix blocks whose tails lie in a fixed set `T` changes
the real proof with probability at most

    2⁻¹¹³ + εRO(0, 312, 4607) + noHitProb + |T|·2^(−8·16(d−1)). -/
theorem pr_collide_zk [ZKRow R] (hlr : st.params.labelRows = true) (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hp : SmallParams st.params) {L : ShG R st.params → ShG R st.params}
    {B : ShG R st.params → Finset (Bytes (preLen st.params))} (hL : ProgAt L B)
    (T : Finset ByteArray) (hT : ∀ s, ∀ b ∈ B s, preTail b ∈ T) :
    pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        realRO st.params Hb st w a.1.1 a.1.2 (L a.2) ≠ realRO st.params Hb st w a.1.1 a.1.2 a.2) ≤
      1 / 2 ^ 113 + ZKRow.εz R st.params 0 312 4607 +
        (noHitProb + T.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1)))) := by
  obtain ⟨hl1, -, -, hl2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  -- The distinguisher: the recomputed prefix's tail is in `T`.
  let D : Except String ByteArray → Tab3 → ShG R st.params → Prop := fun o _ s => TailIn Hb st T o s
  have hD : Budget st.params 0 312 4607 D :=
    ⟨fun o s => Rd3.const (TailIn Hb st T o s),
      fun o _ => (outPre_rd5 Hb st o).map fun P => preTail (blk (preLen st.params) P) ∈ T,
      fun o _ => (outPre_rdE Hb st o).map fun P => preTail (blk (preLen st.params) P) ∈ T⟩
  have hsplit : ∀ a : (Bytes 16 × Tab3) × ShG R st.params,
      realRO st.params Hb st w a.1.1 a.1.2 (L a.2) ≠ realRO st.params Hb st w a.1.1 a.1.2 a.2 →
      GrindBad CrtGen.tables (a.2.1 ∘ key2 st.params (preRO Hb st w a.1.1 a.1.2 a.2)) ∨
        D (realRO st.params Hb st w a.1.1 a.1.2 a.2) a.1.2 a.2 := by
    intro a h
    by_cases hg : GrindBad CrtGen.tables (a.2.1 ∘ key2 st.params (preRO Hb st w a.1.1 a.1.2 a.2))
    · exact Or.inl hg
    · right
      have hmem : blk (preLen st.params) (preRO Hb st w a.1.1 a.1.2 a.2) ∈ B a.2 := by
        by_contra hn
        exact h (realRO_progAt hzk hHb hlab hL a.1.1 a.1.2 a.2 hn)
      obtain ⟨proof, hok, hv⟩ := realRO_vPre hzk hHb hlab a.1.1 a.1.2 a.2 hg
      show preTail (blk (preLen st.params) (@outPre (icPrg (rowFn a.2.2.2)) Hb CrtGen.tables st a.2.2.1
        (realRO st.params Hb st w a.1.1 a.1.2 a.2))) ∈ T
      rw [hok, hv]
      exact hT _ _ hmem
  have hz := ZKRow.zk Hb st w hlr hzk hHb hp D hD
  have hsim : pr ((SimCoins st.params × Tab3) × ShG R st.params) (fun a =>
      D (simulate st.params a.1.1) a.1.2 (progRO st.params Hb st a.1.1 a.2)) ≤
      noHitProb + T.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) := by
    have e : ∀ a : (SimCoins st.params × Tab3) × ShG R st.params,
        D (simulate st.params a.1.1) a.1.2 (progRO st.params Hb st a.1.1 a.2) ↔
          simTail a.1.1 ∈ T := fun a => by
      show preTail (blk (preLen st.params) (@outPre (icPrg (rowFn a.2.2.2)) Hb CrtGen.tables st a.2.2.1
        (simulate st.params a.1.1))) ∈ T ↔ _
      rw [@preTail_outPre st.params (icPrg (rowFn a.2.2.2)) Hb hHb CrtGen.tables st rfl a.2.2.1 a.1.1]
    rw [pr_congr e]
    have e1 := pr_prod_fst (β := ShG R st.params) (fun c : SimCoins st.params × Tab3 => simTail c.1 ∈ T)
    have e2 := pr_prod_fst (β := Tab3) (fun c : SimCoins st.params => simTail c ∈ T)
    exact (e1.trans e2).le.trans (pr_simTail_mem T)
  have hreal : pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
      D (realRO st.params Hb st w a.1.1 a.1.2 a.2) a.1.2 a.2) ≤
      ZKRow.εz R st.params 0 312 4607 + (noHitProb + T.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1)))) := by
    have := (abs_sub_le_iff.1 hz).1
    linarith
  refine (pr_mono hsplit).trans ((pr_or_le _ _).trans ?_)
  have := pr_grindBad_preRO (R := R) (Hb := Hb) (st := st) (w := w)
  linarith

end Collide

end VoleMole.ZK.Sim
