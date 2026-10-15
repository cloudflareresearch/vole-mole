import VoleMole.ZK.BavcLemmas
import VoleMole.ZK.IdealFields

/-!
# Reading a real run off its tape: helper facts

For `ZK/TapeOf.lean` (`prove = proveIdeal ∘ tapeOf`):

* `findFirst_map`, `findFirst_congr`; `firstHit_tapeOf`: the first accepted `H₂³` answer of the
  tape is the real grinding outcome (`Prover.grindStep`, with `openSeeds_size`: the opening fits iff
  `openCount Δ ≤ 105`);
* `openingOf_eq`: the tape's commitments and seeds reassemble the real opening (`BAVC.openAt`);
* `usBytes_tapeOf`: the tape's pads reassemble the small VOLEs' inputs;
* `wordAt_testBit`, `gateInputsOff_congr`: the gate inputs read the label rows only.
-/

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith

/-! ## `findFirst` -/

lemma findFirst_map {α β : Type} (f : ℕ → Option α) (φ : α → β) :
    ∀ (n c : ℕ), (Prover.findFirst f n c).map φ = Prover.findFirst (fun k => (f k).map φ) n c
  | 0, _ => rfl
  | n + 1, c => by
    simp only [Prover.findFirst]
    cases f c <;> simp [findFirst_map f φ n (c + 1)]

lemma findFirst_congr {α : Type} {f g : ℕ → Option α} :
    ∀ (n c : ℕ), (∀ k, c ≤ k → k < c + n → f k = g k) →
      Prover.findFirst f n c = Prover.findFirst g n c
  | 0, _, _ => rfl
  | n + 1, c, h => by
    simp only [Prover.findFirst]
    rw [h c le_rfl (by omega)]
    cases g c
    · exact findFirst_congr n (c + 1) fun k h1 h2 => h k (by omega) (by omega)
    · rfl

/-! ## Grinding -/

lemma openAt_isSome (t : Array ByteArray) (coms delta : ByteArray) :
    (BAVC.openAt t coms delta).isSome = decide (openCount delta ≤ 105) := by
  simp only [BAVC.openAt, openSeeds_size]
  split_ifs with h <;> simp <;> omega

/-- **The tape's first accepted answer is the real grinding outcome.** -/
theorem firstHit_grind (Hs : Hashes) (hHs : HashesWF Hs) (s : Prover.Pending) (pre : ByteArray) :
    (firstHit fun c : Fin nGrind =>
        blk 16 (Hs.hash .h23 ((AES.pushLE32 pre c.val.toUInt32).push 11))).map
      (fun x => (x.1, ba x.2)) =
      (Prover.findFirst (Prover.grindStep Hs s pre) (2 ^ 32) 0).map fun x => (x.1, x.2.1) := by
  rw [firstHit, findFirst_map, findFirst_map]
  refine findFirst_congr _ _ fun k _ hk => ?_
  have hk' : k < nGrind := by simpa [nGrind] using hk
  have hd : ∀ x, ba (blk 16 (Hs.hash .h23 x)) = Hs.hash .h23 x := fun x =>
    ba_blk_of_size (n := 16) (hHs .h23 x)
  simp only [hk', dite_true, Prover.grindStep, hd, accepts]
  have hsz : (Hs.hash .h23 ((AES.pushLE32 pre k.toUInt32).push 11)).size = 16 := hHs _ _
  generalize Hs.hash .h23 ((AES.pushLE32 pre k.toUInt32).push 11) = d at hsz ⊢
  have ho := openAt_isSome s.tree s.leaves.coms d
  by_cases h15 : d.get! 15 = 0
  · cases hopen : BAVC.openAt s.tree s.leaves.coms d with
    | none =>
      rw [hopen] at ho
      have : ¬ openCount d ≤ 105 := by simpa using ho
      simp [h15, this]
    | some o =>
      rw [hopen] at ho
      have : openCount d ≤ 105 := by simpa using ho
      simp [h15, this, ba_blk_of_size hsz]
  · simp [h15]

/-! ## The opening -/

lemma list_foldl_append_idx : ∀ (l : List ByteArray) (acc : ByteArray),
    l.foldl (· ++ ·) acc = (List.range l.length).foldl (fun acc k => acc ++ l.getD k .empty) acc := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro acc; rfl
  | append_singleton l x ih =>
    intro acc
    rw [List.foldl_append, ih, List.length_append, List.length_singleton, List.range_succ,
      List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    congr 1
    · refine List.foldl_ext _ _ _ fun acc k hk => ?_
      rw [List.getD_append _ _ _ _ (List.mem_range.1 hk)]
    · rw [List.getD_append_right _ _ _ _ le_rfl]; simp

lemma array_foldl_append (a : Array ByteArray) (acc : ByteArray) :
    a.foldl (· ++ ·) acc = (List.range a.size).foldl (fun acc k => acc ++ a[k]!) acc := by
  rw [← Array.foldl_toList, list_foldl_append_idx, Array.length_toList]
  refine List.foldl_ext _ _ _ fun acc k _ => ?_
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?]
  rfl

lemma size_foldl_hidden (f : ℕ → ByteArray) (hf : ∀ i, (f i).size = 32) (n : ℕ) :
    ((List.range n).foldl (fun acc i => acc ++ f i) ByteArray.empty).size = 32 * n := by
  rw [size_foldl_append']; simp [hf, List.sum_replicate, mul_comm]

lemma leafOffset_succ (i : ℕ) : BAVC.leafOffset (i + 1) = BAVC.leafOffset i + 2 ^ BAVC.kOf i := by
  simp [BAVC.leafOffset, List.range_succ, List.foldl_append]

lemma leafOffset_mono {i j : ℕ} (h : i ≤ j) : BAVC.leafOffset i ≤ BAVC.leafOffset j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [leafOffset_succ]; exact le_trans ih (Nat.le_add_right _ _)

/-- The hidden leaf of tree `i` is a leaf. -/
lemma hidden_leaf_lt (delta : ByteArray) {i : ℕ} (hi : i < BAVC.tau) :
    BAVC.leafOffset i + BAVC.deltaIndex delta i < BAVC.numLeaves := by
  have h1 := hiddenIndex_lt (BAVC.deltaBit delta) i
  have h2 := leafOffset_mono (show i + 1 ≤ BAVC.tau by omega)
  rw [leafOffset_succ, leafOffset_tau] at h2
  simp only [BAVC.deltaIndex]
  omega

/-- **The tape's commitments and seeds reassemble an opening** (`BAVC.openAt`), for leaf
commitments of `32 L` bytes and tree nodes of 16 bytes. -/
theorem openingOf_eq (t : Array ByteArray) (coms delta : ByteArray) (hd : delta.size = 16)
    (hcs : coms.size = BAVC.hashLen * BAVC.numLeaves)
    (htree : ∀ k < BAVC.numNodes, (t[k]!).size = 16) {o : ByteArray}
    (ho : BAVC.openAt t coms delta = some o) :
    openingOf (ba (blk 16 delta)) (comsOf coms delta) (seedsOf t delta) = o := by
  rw [ba_blk_of_size hd]
  unfold BAVC.openAt at ho
  simp only at ho
  split_ifs at ho with hbig
  simp only [Option.some.injEq] at ho
  subst ho
  have hn : openCount delta = (BAVC.openSeeds t delta).size := (openSeeds_size t delta).symm
  -- The hidden commitments.
  have hhid : (List.range BAVC.tau).foldl (fun acc i => acc ++ if h : i < BAVC.tau then
      ba (comsOf coms delta ⟨i, h⟩) else ByteArray.empty) ByteArray.empty =
      (List.range BAVC.tau).foldl (fun acc i =>
        acc ++ coms.extract (BAVC.hashLen * (BAVC.leafOffset i + BAVC.deltaIndex delta i))
          (BAVC.hashLen * (BAVC.leafOffset i + BAVC.deltaIndex delta i) + BAVC.hashLen))
        ByteArray.empty := by
    refine List.foldl_ext _ _ _ fun acc i hi => ?_
    have hi := List.mem_range.1 hi
    have hl := hidden_leaf_lt delta hi
    simp only [hi, dite_true, comsOf]
    rw [ba_blk_of_size]
    have h1 : BAVC.hashLen * (BAVC.leafOffset i + BAVC.deltaIndex delta i) + BAVC.hashLen ≤
        coms.size := by
      rw [hcs, ← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ hl
    rw [ByteArray.size_extract, Nat.min_eq_left h1, Nat.add_sub_cancel_left]
    rfl
  -- The seeds.
  have hseeds : ∀ acc, (List.range (openCount delta)).foldl (fun acc k => acc ++ if h : k < 105 then
      ba (seedsOf t delta ⟨k, h⟩) else ByteArray.empty) acc =
      (List.range (BAVC.openSeeds t delta).size).foldl
        (fun acc k => acc ++ (BAVC.openSeeds t delta)[k]!) acc := by
    intro acc
    rw [hn]
    refine List.foldl_ext _ _ _ fun acc k hk => ?_
    have hk := List.mem_range.1 hk
    have hk' : k < 105 := by omega
    have hsz : ((BAVC.openSeeds t delta)[k]!).size = 16 := by
      have hpos := openPos_lt delta
      have hk2 : k < (openPos delta).size := by rw [openSeeds_eq] at hk; simpa using hk
      rw [getElem!_pos (BAVC.openSeeds t delta) k hk]
      simp only [openSeeds_eq, Array.getElem_map]
      exact htree _ (hpos _ (Array.getElem_mem hk2))
    simp only [hk', dite_true, seedsOf]
    rw [show (BAVC.openSeeds t delta).getD k ByteArray.empty = (BAVC.openSeeds t delta)[k]! from by
      rw [Array.getElem!_eq_getD]; rfl, ba_blk_of_size hsz]
  simp only [openingOf]
  rw [hhid, hseeds, array_foldl_append]
  rfl

/-! ## Words and blocks -/

lemma wordsOf_bytesOfWords (W : Array UInt64) : wordsOf (bytesOfWords W) = W := by
  apply Array.ext
  · simp [wordsOf, bytesOfWords_size]
  intro k h1 h2
  have hk : k < W.size := h2
  simp only [wordsOf, Array.getElem_map, Array.getElem_range]
  rw [word_bytesOfWords W hk, getElem!_pos W k hk]

lemma fit_eq_extract {b : ByteArray} {n : ℕ} (h : n ≤ b.size) : Prover.fit b n = b.extract 0 n := by
  apply byteArray_ext_get!
  · rw [fit_size, ByteArray.size_extract]; omega
  intro k hk
  rw [fit_size] at hk
  rw [get!_extract0 _ hk h, Prover.fit, get!_extract0 _ hk (by
    rw [ByteArray.size_append, zeros_size]; omega), get!_append, ite_eq_left (by omega)]

lemma ba_blk_extract {b : ByteArray} {a c n : ℕ} (hc : c ≤ b.size) (hn : c - a = n) :
    ba (blk n (b.extract a c)) = b.extract a c :=
  ba_blk_of_size (by rw [ByteArray.size_extract]; omega)

/-- **The pads of a column reassemble it.** -/
lemma usBytes_reassemble (p : Params) (X : ℕ → ByteArray) (hX : ∀ i, (X i).size = p.colBytes)
    (hi8 : Bytes p.nMask) (sib : Fin 312 → Bytes 4) {i : ℕ} (hi : i < BAVC.tau) :
    usBytes p (blk p.witnessBytes (X 0),
      blk (labelBytes p) ((X 0).extract p.witnessBytes p.correctionBytes),
      fun j => blk p.correctionBytes (X (j.val + 1)),
      fun j => blk p.nMask ((X j.val).extract p.correctionBytes (p.correctionBytes + p.nMask)),
      fun j => blk (restBytes p) ((X j.val).extract (p.correctionBytes + p.nMask) p.colBytes),
      hi8, sib) i = X i := by
  have h1 := cb_add_nMask_le p
  have h2 := wb_le_cb p
  have hl := labelBytes_add p
  have hcorr : ∀ j, ba (blk p.correctionBytes (X j)) = (X j).extract 0 p.correctionBytes := fun j => by
    rw [ba_blk, fit_eq_extract (by rw [hX]; omega)]
  have hmask : ∀ j, ba (blk p.nMask ((X j).extract p.correctionBytes (p.correctionBytes + p.nMask))) =
      (X j).extract p.correctionBytes (p.correctionBytes + p.nMask) := fun j =>
    ba_blk_extract (by rw [hX]; omega) (by omega)
  have hrest : ∀ j, ba (blk (restBytes p) ((X j).extract (p.correctionBytes + p.nMask) p.colBytes)) =
      (X j).extract (p.correctionBytes + p.nMask) p.colBytes := fun j =>
    ba_blk_extract (by rw [hX]) (by simp only [restBytes]; omega)
  have htail : ∀ j, (X j).extract p.correctionBytes (p.correctionBytes + p.nMask) ++
      (X j).extract (p.correctionBytes + p.nMask) p.colBytes = (X j).extract p.correctionBytes
        p.colBytes := fun j => by
    rw [ByteArray.extract_append_extract, Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]
  have hall : ∀ j, (X j).extract 0 p.correctionBytes ++ (X j).extract p.correctionBytes p.colBytes =
      X j := fun j => by
    rw [ByteArray.extract_append_extract, Nat.min_eq_left (by omega), Nat.max_eq_right (by omega),
      ← hX j, ByteArray.extract_zero_size]
  unfold usBytes
  simp only [hi, dite_true, hmask, hrest, htail]
  by_cases h0 : i = 0
  · subst h0
    simp only [↓reduceIte]
    rw [ba_blk, fit_eq_extract (by rw [hX]; omega),
      ba_blk_extract (by rw [hX]; omega) (by simp only [labelBytes]),
      ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
      Nat.max_eq_right h2, hall]
  · have hi' : i - 1 < BAVC.tau - 1 := by omega
    simp only [h0, ↓reduceIte, hi', dite_true, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0),
      hcorr, hall]

/-! ## The gate inputs read the label rows only -/

lemma uint64_testBit_lt (x : UInt64) {k : ℕ} (hk : 64 ≤ k) : x.toNat.testBit k = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by norm_num) hk))

lemma wbit_getD (w : Array UInt64) (r : ℕ) : wbit w r = (w.getD (r / 64) 0).toNat.testBit (r % 64) := by
  rw [wbit_eq, Array.getElem!_eq_getD]; rfl

/-- Bit `k < 64` of `wordAt w o` is bit `o + k` of `w`. -/
lemma wordAt_testBit (w : Array UInt64) (o : ℕ) {k : ℕ} (hk : k < 64) :
    (wordAt w o).toNat.testBit k = wbit w (o + k) := by
  rw [wbit_getD]
  unfold wordAt
  by_cases hs : o % 64 = 0
  · simp only [hs, beq_self_eq_true, ↓reduceIte]
    rw [show (o + k) / 64 = o / 64 by omega, show (o + k) % 64 = k by omega]
  · have hs' : (o % 64 == 0) = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, ↓reduceIte, UInt64.toNat_or, Nat.testBit_or,
      UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, Nat.testBit_shiftRight]
    have e1 : (o % 64).toUInt64.toNat % 64 = o % 64 := by
      simp [Nat.toUInt64]
    have e2 : (64 - o % 64).toUInt64.toNat % 64 = 64 - o % 64 := by
      simp [Nat.toUInt64]; omega
    rw [e1, e2, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    by_cases hlt : o % 64 + k < 64
    · rw [show (o + k) / 64 = o / 64 by omega, show (o + k) % 64 = o % 64 + k by omega]
      simp [show ¬ (64 - o % 64 ≤ k) by omega]
    · rw [show (o + k) / 64 = o / 64 + 1 by omega,
        show (o + k) % 64 = k - (64 - o % 64) by omega,
        uint64_testBit_lt _ (show 64 ≤ o % 64 + k by omega)]
      simp [hk, show 64 - o % 64 ≤ k by omega]

/-- `wordAt` reads 64 bits. -/
lemma wordAt_congr {a b : Array UInt64} {o : ℕ} (h : ∀ k < 64, wbit a (o + k) = wbit b (o + k)) :
    wordAt a o = wordAt b o := by
  apply UInt64.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 64
  · rw [wordAt_testBit _ _ hk, wordAt_testBit _ _ hk, h k hk]
  · rw [uint64_testBit_lt _ (by omega), uint64_testBit_lt _ (by omega)]

/-- **The gate inputs read the 128 label rows only.** -/
lemma gateInputsOff_congr (p : Params) (T : CrtTables) (iv : ByteArray)
    {cols cols' : Array (Array UInt64)} (off : W128)
    (h : ∀ c < 120, ∀ k < 128, wbit cols[c]! (p.labelRowOffset + k) =
      wbit cols'[c]! (p.labelRowOffset + k)) :
    Prover.gateInputsOff p T iv cols off = Prover.gateInputsOff p T iv cols' off := by
  have htops : ((Array.range 120).map fun c =>
      (⟨wordAt cols[c]! p.labelRowOffset, wordAt cols[c]! (p.labelRowOffset + 64)⟩ : W128)) =
      (Array.range 120).map fun c =>
      (⟨wordAt cols'[c]! p.labelRowOffset, wordAt cols'[c]! (p.labelRowOffset + 64)⟩ : W128) := by
    refine Array.map_congr_left fun c hc => ?_
    have hc := Array.mem_range.1 hc
    have e1 : wordAt cols[c]! p.labelRowOffset = wordAt cols'[c]! p.labelRowOffset :=
      wordAt_congr fun k hk => h c hc k (by omega)
    have e2 : wordAt cols[c]! (p.labelRowOffset + 64) = wordAt cols'[c]! (p.labelRowOffset + 64) :=
      wordAt_congr fun k hk => by rw [Nat.add_assoc]; exact h c hc (64 + k) (by omega)
    rw [e1, e2]
  simp only [Prover.gateInputsOff, htops]

end VoleMole.ZK.Sim
