import VoleMole.Theft.JointGame
import VoleMole.ZK.IvOverlapK

/-!
# The hop's charge as a function of the game's view

`real_sim_leN_game` (`Theft/JointGame.lean`) asks for a bound of the hop's charge (`chPt` of the
reads of `hopRd`, at the proof's `iv`) by a function of the rest of the game's view. The hop's
reads are those of the earlier programmings, the later real proofs and the game reader. A real
proof (a programming) whose reads are **confined** to its own `iv` (`Conf`: its `H₅` keys are gate
inputs of its `iv`, its cipher points CTR blocks of its `iv`) is charged to proof `i` only if its
`iv` can meet proof `i`'s: equal middle bytes for the cipher (`ovE`), equal `iv`s for `H₅`
(`ov5`; a gate input begins with its `iv`, `gate5_iv_eq`). Both are read off the outputs in the
view (`ivAt`). So:

* `cEof_union`, `c5of_union`: charges of unions;
* `Conf.cE`, `Conf.c5`: a confined reader is charged `a_E·ovE`, `a₅·ov5`;
* `realFromRd_cE`, `progsRd_cE` (and `_c5`, `_q3`): the later real proofs and the earlier
  programmings, by induction, at the `iv`s of the view's outputs;
* **`hopRd_cE`**, **`hopRd_c5`**, **`hopRd_q3`**: the hop's charges are at most the game reader's
  plus `Σ_{j ≠ i} a·ov(iv_i, iv_j)`.
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.ZK.IC VoleMole.Verifier VoleMole.Verifier.Bridge

/-! ## A gate input begins with its `iv` -/

section Gate

/-- **The first 16 bytes of a gate input are its `iv`.** -/
lemma gate5_get! {p : Params} {T : CrtTables} {a : ByteArray} {k : Bytes 37} (h : Gate5 p T a k)
    (ha : a.size = 16) : ∀ j < 16, (ba k).get! j = a.get! j := by
  obtain ⟨cols, off, e, he⟩ := h
  intro j hj
  unfold enc5 at he
  rw [he]
  unfold Prover.gateInputsOff
  simp only []
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hm : e.val < p.nMult
  · rw [List.getElem?_range hm]
    simp only [Option.map_some, Option.getD_some]
    have h1 : j < 16 + 4 + (((W128.rowMul (fun c => wbit T.g[c]! e) 120
        ((Array.range 120).map fun c => (⟨wordAt cols[c]! p.labelRowOffset,
          wordAt cols[c]! (p.labelRowOffset + 64)⟩ : W128))).xor off).toBytes).size := by omega
    rw [get!_push, ByteArray.size_append, size_pushLE32, ha]
    simp only [h1, ↓reduceIte]
    rw [get!_append, size_pushLE32, ha]
    simp only [show j < 16 + 4 by omega, ↓reduceIte]
    rw [get!_pushLE32, ha]
    simp only [hj, ↓reduceIte]
  · exfalso
    unfold Prover.gateInputsOff at he
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (by simp only [List.length_range]; omega)] at he
    have := congrArg ByteArray.size he
    simp at this

/-- **Two 16-byte `iv`s with a common gate input are equal.** -/
lemma gate5_iv_eq {p p' : Params} {T T' : CrtTables} {a b : ByteArray} {k : Bytes 37}
    (h : Gate5 p T a k) (h' : Gate5 p' T' b k) (ha : a.size = 16) (hb : b.size = 16) : a = b :=
  byteArray_ext_get! (ha.trans hb.symm) fun j hj => by
    rw [ha] at hj
    rw [← gate5_get! h ha j hj, gate5_get! h' hb j hj]

end Gate

/-! ## Overlaps and charges of unions -/

section Ov

/-- **Can reads confined to `iv'` be charged at `iv` (cipher)?** Not if both are 16-byte `iv`s with
different middle bytes. -/
noncomputable def ovE (iv iv' : Option ByteArray) : ℕ :=
  match iv, iv' with
  | some a, some b => if a.size = 16 ∧ b.size = 16 ∧ midB (blk 16 a) ≠ midB (blk 16 b) then 0 else 1
  | _, _ => 1

/-- **Can reads confined to `iv'` be charged at `iv` (`H₅`)?** Not if both are different 16-byte
`iv`s. -/
noncomputable def ov5 (iv iv' : Option ByteArray) : ℕ :=
  match iv, iv' with
  | some a, some b => if a.size = 16 ∧ b.size = 16 ∧ a ≠ b then 0 else 1
  | _, _ => 1

lemma ovE_le_one (iv iv' : Option ByteArray) : ovE iv iv' ≤ 1 := by
  unfold ovE; split <;> (try split_ifs) <;> omega

lemma ov5_le_one (iv iv' : Option ByteArray) : ov5 iv iv' ≤ 1 := by
  unfold ov5; split <;> (try split_ifs) <;> omega

lemma cEof_union (iv : Option ByteArray) (A B : Finset (Blk × Blk)) :
    cEof iv (A ∪ B) ≤ cEof iv A + cEof iv B := by
  classical
  unfold cEof
  rcases iv with _ | v
  · simp only [image_union]; exact card_union_le _ _
  · simp only [qkeys, filter_union, image_union]; exact card_union_le _ _

lemma c5of_union (p : Params) (T : CrtTables) (iv : Option ByteArray) (A B : Finset (Bytes 37)) :
    c5of p T iv (A ∪ B) ≤ c5of p T iv A + c5of p T iv B := by
  classical
  unfold c5of
  rcases iv with _ | v
  · exact card_union_le _ _
  · simp only [filter_union]; exact card_union_le _ _

lemma cEof_le_keys (iv : Option ByteArray) (A : Finset (Blk × Blk)) :
    cEof iv A ≤ (A.image Prod.fst).card := by
  rcases iv with _ | v
  · exact le_rfl
  · exact cEof_le_some v A

lemma c5of_le_card (p : Params) (T : CrtTables) (iv : Option ByteArray) (A : Finset (Bytes 37)) :
    c5of p T iv A ≤ A.card := by
  rcases iv with _ | v
  · exact le_rfl
  · exact c5of_le_some p T v A

end Ov

/-! ## Readers confined to an `iv` -/

section Conf

variable {p : Params} {Y : Type*}

/-- **A table reader confined to an `iv`**: it reads no slice, at most `a₅` `H₅` keys, all gate
inputs of the `iv`, and cipher points of at most `a_E` keys, all at CTR blocks of the `iv` (when
there is one). -/
structure Conf {F : Tab3 → Sh p → Y} (R : TRd F) (iv : Sh p → Option ByteArray) (a5 aE : ℕ) :
    Prop where
  h3 : ∀ g s, R.Q3 g s = ∅
  h5 : ∀ g s, (R.Q5 g s).card ≤ a5
  hE : ∀ g s, ((R.QE g s).image Prod.fst).card ≤ aE
  in5 : ∀ g s v, iv s = some v → ∀ k ∈ R.Q5 g s, Gate5 p CrtGen.tables v k
  inE : ∀ g s v, iv s = some v → ∀ kz ∈ R.QE g s, InY v kz.2

/-- **A confined reader's cipher charge** at `iv₀` is at most `a_E·ovE(iv₀, iv)`. -/
lemma Conf.cE {F : Tab3 → Sh p → Y} {R : TRd F} {iv : Sh p → Option ByteArray} {a5 aE : ℕ}
    (hc : Conf R iv a5 aE) (iv0 : Option ByteArray) (g : Tab3) (s : Sh p) :
    cEof iv0 (R.QE g s) ≤ aE * ovE iv0 (iv s) := by
  classical
  have hk : cEof iv0 (R.QE g s) ≤ aE := (cEof_le_keys _ _).trans (hc.hE g s)
  rcases iv0 with _ | a
  · simpa [ovE] using hk
  rcases hiv : iv s with _ | b
  · simpa [ovE] using hk
  by_cases hab : a.size = 16 ∧ b.size = 16 ∧ midB (blk 16 a) ≠ midB (blk 16 b)
  · obtain ⟨ha, hb, hm⟩ := hab
    have h0 : cEof (some a) (R.QE g s) = 0 := by
      unfold cEof qkeys
      rw [card_eq_zero, image_eq_empty, filter_eq_empty_iff]
      intro kz hkz hza
      have hzb := hc.inE g s b hiv kz hkz
      rw [← ba_blk_of_size ha] at hza
      rw [← ba_blk_of_size hb] at hzb
      exact hm ((midB_of_inY_self hza).symm.trans (midB_of_inY_self hzb))
    rw [h0]; exact Nat.zero_le _
  · simp only [ovE, hab, ↓reduceIte, mul_one]; exact hk

/-- **A confined reader's `H₅` charge** at `iv₀` is at most `a₅·ov5(iv₀, iv)`. -/
lemma Conf.c5 {F : Tab3 → Sh p → Y} {R : TRd F} {iv : Sh p → Option ByteArray} {a5 aE : ℕ}
    (hc : Conf R iv a5 aE) (iv0 : Option ByteArray) (g : Tab3) (s : Sh p) :
    c5of p CrtGen.tables iv0 (R.Q5 g s) ≤ a5 * ov5 iv0 (iv s) := by
  classical
  have hk : c5of p CrtGen.tables iv0 (R.Q5 g s) ≤ a5 := (c5of_le_card _ _ _ _).trans (hc.h5 g s)
  rcases iv0 with _ | a
  · simpa [ov5] using hk
  rcases hiv : iv s with _ | b
  · simpa [ov5] using hk
  by_cases hab : a.size = 16 ∧ b.size = 16 ∧ a ≠ b
  · obtain ⟨ha, hb, hne⟩ := hab
    have h0 : c5of p CrtGen.tables (some a) (R.Q5 g s) = 0 := by
      unfold c5of
      rw [card_eq_zero, filter_eq_empty_iff]
      intro k hk hka
      exact hne (gate5_iv_eq hka (hc.in5 g s b hiv k hk) ha hb)
    rw [h0]; exact Nat.zero_le _
  · simp only [ov5, hab, ↓reduceIte, mul_one]; exact hk

end Conf

/-! ## The `iv`s of the view's outputs -/

section Hist

variable {X I O Ω : Type*} (ivO : X → I → O → Option ByteArray) (xOf : Ω → List O → I)

/-- **The `iv` of entry `j` of a history**: the decoder `ivO` at the entry's instance. -/
noncomputable def ivAt (x : X) (ω : Ω) (l : List O) (j : ℕ) : Option ByteArray :=
  match l[j]? with
  | some o => ivO x (xOf ω (l.take j)) o
  | none => none

lemma ivAt_append (x : X) (ω : Ω) (h r : List O) {j : ℕ} (hj : j < h.length) :
    ivAt ivO xOf x ω (h ++ r) j = ivAt ivO xOf x ω h j := by
  unfold ivAt
  rw [List.getElem?_append_left hj, List.take_append_of_le_length hj.le]

lemma ivAt_last (x : X) (ω : Ω) (h : List O) (o : O) (r : List O) :
    ivAt ivO xOf x ω (h ++ [o] ++ r) h.length = ivO x (xOf ω h) o := by
  unfold ivAt
  rw [List.append_assoc, List.getElem?_append_right le_rfl, Nat.sub_self,
    List.take_left' rfl]
  rfl

end Hist

/-- **The real suffix extends the history.** -/
lemma realFrom_prefix {Ω O ρ G S : Type*} (P : Ω → List O → ρ → G → S → O) (ω : Ω)
    (rs : ℕ → ρ × G) (u : S) :
    ∀ m (h : List O) j, ∃ r, realFrom P ω rs u h j m = h ++ r
  | 0, h, _ => ⟨[], by simp [realFrom]⟩
  | m + 1, h, j => by
    obtain ⟨r, hr⟩ := realFrom_prefix P ω rs u m (h ++ [P ω h (rs j).1 (rs j).2 u]) (j + 1)
    exact ⟨[P ω h (rs j).1 (rs j).2 u] ++ r, by simp only [realFrom, hr, List.append_assoc]⟩

lemma simPre_succ_fst {Ω O C S : Type*} (Sm : Ω → List O → C → O) (pg : Ω → List O → C → S → S)
    (ω : Ω) (cs : ℕ → C) (j : ℕ) :
    (simPre Sm pg ω cs (j + 1)).1 = (simPre Sm pg ω cs j).1 ++ [Sm ω (simPre Sm pg ω cs j).1 (cs j)] :=
  rfl

/-! ## The charges of the later real proofs and of the earlier programmings -/

section GameCharge

variable {p : Params} {X : Type} {I W C O Ω : Type*}
  {prove : X → I → W → Bytes 16 → Tab3 → Sh p → O} {sim : I → C → O}
  {prog : X → I → C → Sh p → Sh p} {xOf : Ω → List O → I} {wOf : Ω → List O → W}
  (ivO : X → I → O → Option ByteArray)

/-- **The later real proofs' cipher charge**: at most the reader's after them plus `s_E·ovE` per
proof, at the `iv` of its output in the history. -/
theorem realFromRd_cE
    (RP : ∀ x xI w r g', TRd (fun (_ : Tab3) (s : Sh p) => prove x xI w r g' s)) {s5 sE : ℕ}
    (hRP : ∀ x xI w r g', Conf (RP x xI w r g') (fun s => ivO x xI (prove x xI w r g' s)) s5 sE)
    (x : X) (ω : Ω) (rs : ℕ → Bytes 16 × Tab3) {Φ : List O → Tab3 → Sh p → Prop}
    (RΦ : ∀ l, TRd (Φ l)) (iv0 : Option ByteArray) :
    ∀ m (h : List O) j g s,
      cEof iv0 ((realFromRd (xOf := xOf) prove wOf RP x ω rs RΦ m h j).QE g s) ≤
        cEof iv0 ((RΦ (realFrom (gP prove xOf wOf) ω rs (atX s x) h j m)).QE g s) +
          ∑ t ∈ range m, sE * ovE iv0 (ivAt ivO xOf x ω
            (realFrom (gP prove xOf wOf) ω rs (atX s x) h j m) (h.length + t))
  | 0, h, j, g, s => by simp [realFromRd, realFrom]
  | m + 1, h, j, g, s => by
    set o := prove x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2 s
    have e : (realFromRd (xOf := xOf) prove wOf RP x ω rs RΦ (m + 1) h j).QE g s =
        (RP x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2).QE g s ∪
          (realFromRd (xOf := xOf) prove wOf RP x ω rs RΦ m (h ++ [o]) (j + 1)).QE g s := rfl
    have eL : realFrom (gP prove xOf wOf) ω rs (atX s x) h j (m + 1) =
        realFrom (gP prove xOf wOf) ω rs (atX s x) (h ++ [o]) (j + 1) m := rfl
    have ih := realFromRd_cE RP hRP x ω rs RΦ iv0 m (h ++ [o]) (j + 1) g s
    have h1 : cEof iv0 ((RP x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2).QE g s) ≤
        sE * ovE iv0 (ivO x (xOf ω h) o) := (hRP x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2).cE iv0 g s
    obtain ⟨r, hr⟩ := realFrom_prefix (gP prove xOf wOf) ω rs (atX s x) m (h ++ [o]) (j + 1)
    have hlast : ivAt ivO xOf x ω (realFrom (gP prove xOf wOf) ω rs (atX s x) (h ++ [o]) (j + 1) m)
        h.length = ivO x (xOf ω h) o := by rw [hr]; exact ivAt_last ivO xOf x ω h o r
    rw [e, eL, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [hlast]
    simp only [List.length_append, List.length_singleton] at ih
    have hs : ∀ t ∈ range m, h.length + 1 + t = h.length + (t + 1) := fun t _ => by omega
    rw [Finset.sum_congr rfl fun t ht => by rw [hs t ht]] at ih
    have := cEof_union iv0 ((RP x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2).QE g s)
      ((realFromRd (xOf := xOf) prove wOf RP x ω rs RΦ m (h ++ [o]) (j + 1)).QE g s)
    omega

/-- **The later real proofs' `H₅` charge.** -/
theorem realFromRd_c5
    (RP : ∀ x xI w r g', TRd (fun (_ : Tab3) (s : Sh p) => prove x xI w r g' s)) {s5 sE : ℕ}
    (hRP : ∀ x xI w r g', Conf (RP x xI w r g') (fun s => ivO x xI (prove x xI w r g' s)) s5 sE)
    (x : X) (ω : Ω) (rs : ℕ → Bytes 16 × Tab3) {Φ : List O → Tab3 → Sh p → Prop}
    (RΦ : ∀ l, TRd (Φ l)) (iv0 : Option ByteArray) :
    ∀ m (h : List O) j g s,
      c5of p CrtGen.tables iv0 ((realFromRd (xOf := xOf) prove wOf RP x ω rs RΦ m h j).Q5 g s) ≤
        c5of p CrtGen.tables iv0 ((RΦ (realFrom (gP prove xOf wOf) ω rs (atX s x) h j m)).Q5 g s) +
          ∑ t ∈ range m, s5 * ov5 iv0 (ivAt ivO xOf x ω
            (realFrom (gP prove xOf wOf) ω rs (atX s x) h j m) (h.length + t))
  | 0, h, j, g, s => by simp [realFromRd, realFrom]
  | m + 1, h, j, g, s => by
    set o := prove x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2 s
    have e : (realFromRd (xOf := xOf) prove wOf RP x ω rs RΦ (m + 1) h j).Q5 g s =
        (RP x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2).Q5 g s ∪
          (realFromRd (xOf := xOf) prove wOf RP x ω rs RΦ m (h ++ [o]) (j + 1)).Q5 g s := rfl
    have eL : realFrom (gP prove xOf wOf) ω rs (atX s x) h j (m + 1) =
        realFrom (gP prove xOf wOf) ω rs (atX s x) (h ++ [o]) (j + 1) m := rfl
    have ih := realFromRd_c5 RP hRP x ω rs RΦ iv0 m (h ++ [o]) (j + 1) g s
    have h1 : c5of p CrtGen.tables iv0 ((RP x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2).Q5 g s) ≤
        s5 * ov5 iv0 (ivO x (xOf ω h) o) := (hRP x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2).c5 iv0 g s
    obtain ⟨r, hr⟩ := realFrom_prefix (gP prove xOf wOf) ω rs (atX s x) m (h ++ [o]) (j + 1)
    have hlast : ivAt ivO xOf x ω (realFrom (gP prove xOf wOf) ω rs (atX s x) (h ++ [o]) (j + 1) m)
        h.length = ivO x (xOf ω h) o := by rw [hr]; exact ivAt_last ivO xOf x ω h o r
    rw [e, eL, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    rw [hlast]
    simp only [List.length_append, List.length_singleton] at ih
    have hs : ∀ t ∈ range m, h.length + 1 + t = h.length + (t + 1) := fun t _ => by omega
    rw [Finset.sum_congr rfl fun t ht => by rw [hs t ht]] at ih
    have := c5of_union p CrtGen.tables iv0 ((RP x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2).Q5 g s)
      ((realFromRd (xOf := xOf) prove wOf RP x ω rs RΦ m (h ++ [o]) (j + 1)).Q5 g s)
    omega

/-- **The later real proofs read no slice**: the `H₃` keys are the reader's after them. -/
theorem realFromRd_q3
    (RP : ∀ x xI w r g', TRd (fun (_ : Tab3) (s : Sh p) => prove x xI w r g' s)) {s5 sE : ℕ}
    (hRP : ∀ x xI w r g', Conf (RP x xI w r g') (fun s => ivO x xI (prove x xI w r g' s)) s5 sE)
    (x : X) (ω : Ω) (rs : ℕ → Bytes 16 × Tab3) {Φ : List O → Tab3 → Sh p → Prop}
    (RΦ : ∀ l, TRd (Φ l)) :
    ∀ m (h : List O) j g s,
      (realFromRd (xOf := xOf) prove wOf RP x ω rs RΦ m h j).Q3 g s =
        (RΦ (realFrom (gP prove xOf wOf) ω rs (atX s x) h j m)).Q3 g s
  | 0, h, j, g, s => rfl
  | m + 1, h, j, g, s => by
    have e : (realFromRd (xOf := xOf) prove wOf RP x ω rs RΦ (m + 1) h j).Q3 g s =
        (RP x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2).Q3 g s ∪
          (realFromRd (xOf := xOf) prove wOf RP x ω rs RΦ m
            (h ++ [prove x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2 s]) (j + 1)).Q3 g s := rfl
    rw [e, (hRP x (xOf ω h) (wOf ω h) (rs j).1 (rs j).2).h3, Finset.empty_union,
      realFromRd_q3 RP hRP x ω rs RΦ m _ (j + 1) g s]
    rfl


/-- **The earlier programmings' cipher charge**: `m_E·ovE` per simulation, at the `iv` of its
output in the history. -/
theorem progsRd_cE (hkeep : ∀ x xI c s, (prog x xI c s).2 = s.2)
    (Rpg : ∀ x xI c, TRd (fun (_ : Tab3) s => (prog x xI c s).1)) {m5 mE : ℕ}
    (hRpg : ∀ x xI c, Conf (Rpg x xI c) (fun _ => ivO x xI (sim xI c)) m5 mE)
    (x : X) (ω : Ω) (cs : ℕ → C) (iv0 : Option ByteArray) :
    ∀ j g s, cEof iv0 ((progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω cs j).QE g s) ≤
      ∑ k ∈ range j, mE * ovE iv0 (ivAt ivO xOf x ω (simPre (gS sim xOf) (gPg prog xOf) ω cs j).1 k)
  | 0, g, s => by
    show cEof iv0 (∅ : Finset (Blk × Blk)) ≤ _
    rcases iv0 with _ | v <;> simp [cEof, qkeys]
  | j + 1, g, s => by
    set h := (simPre (gS sim xOf) (gPg prog xOf) ω cs j).1
    have e : (progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω cs (j + 1)).QE g s =
        (Rpg x (xOf ω h) (cs j)).QE g s ∪
          (progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω cs j).QE g (prog x (xOf ω h) (cs j) s) :=
      rfl
    have ih := progsRd_cE hkeep Rpg hRpg x ω cs iv0 j g (prog x (xOf ω h) (cs j) s)
    change _ ≤ ∑ k ∈ range j, mE * ovE iv0 (ivAt ivO xOf x ω h k) at ih
    have h1 : cEof iv0 ((Rpg x (xOf ω h) (cs j)).QE g s) ≤
        mE * ovE iv0 (ivO x (xOf ω h) (sim (xOf ω h) (cs j))) := (hRpg _ _ _).cE iv0 g s
    have hl : (simPre (gS sim xOf) (gPg prog xOf) ω cs (j + 1)).1 = h ++ [sim (xOf ω h) (cs j)] :=
      simPre_succ_fst _ _ ω cs j
    have hlen : h.length = j := simPre_length _ _ ω cs j
    have hlast : ivAt ivO xOf x ω (h ++ [sim (xOf ω h) (cs j)]) j =
        ivO x (xOf ω h) (sim (xOf ω h) (cs j)) := by
      have := ivAt_last ivO xOf x ω h (sim (xOf ω h) (cs j)) []
      rwa [List.append_nil, hlen] at this
    have hpre : ∀ k ∈ range j, ivAt ivO xOf x ω (h ++ [sim (xOf ω h) (cs j)]) k =
        ivAt ivO xOf x ω h k := fun k hk =>
      ivAt_append ivO xOf x ω h _ (by rw [hlen]; exact Finset.mem_range.1 hk)
    rw [e, hl, Finset.sum_range_succ, hlast, Finset.sum_congr rfl fun k hk => by rw [hpre k hk]]
    have := cEof_union iv0 ((Rpg x (xOf ω h) (cs j)).QE g s)
      ((progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω cs j).QE g (prog x (xOf ω h) (cs j) s))
    omega

/-- **The earlier programmings' `H₅` charge.** -/
theorem progsRd_c5 (hkeep : ∀ x xI c s, (prog x xI c s).2 = s.2)
    (Rpg : ∀ x xI c, TRd (fun (_ : Tab3) s => (prog x xI c s).1)) {m5 mE : ℕ}
    (hRpg : ∀ x xI c, Conf (Rpg x xI c) (fun _ => ivO x xI (sim xI c)) m5 mE)
    (x : X) (ω : Ω) (cs : ℕ → C) (iv0 : Option ByteArray) :
    ∀ j g s, c5of p CrtGen.tables iv0
        ((progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω cs j).Q5 g s) ≤
      ∑ k ∈ range j, m5 * ov5 iv0 (ivAt ivO xOf x ω (simPre (gS sim xOf) (gPg prog xOf) ω cs j).1 k)
  | 0, g, s => by
    show c5of p CrtGen.tables iv0 (∅ : Finset (Bytes 37)) ≤ _
    rcases iv0 with _ | v <;> simp [c5of]
  | j + 1, g, s => by
    set h := (simPre (gS sim xOf) (gPg prog xOf) ω cs j).1
    have e : (progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω cs (j + 1)).Q5 g s =
        (Rpg x (xOf ω h) (cs j)).Q5 g s ∪
          (progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω cs j).Q5 g (prog x (xOf ω h) (cs j) s) :=
      rfl
    have ih := progsRd_c5 hkeep Rpg hRpg x ω cs iv0 j g (prog x (xOf ω h) (cs j) s)
    change _ ≤ ∑ k ∈ range j, m5 * ov5 iv0 (ivAt ivO xOf x ω h k) at ih
    have h1 : c5of p CrtGen.tables iv0 ((Rpg x (xOf ω h) (cs j)).Q5 g s) ≤
        m5 * ov5 iv0 (ivO x (xOf ω h) (sim (xOf ω h) (cs j))) := (hRpg _ _ _).c5 iv0 g s
    have hl : (simPre (gS sim xOf) (gPg prog xOf) ω cs (j + 1)).1 = h ++ [sim (xOf ω h) (cs j)] :=
      simPre_succ_fst _ _ ω cs j
    have hlen : h.length = j := simPre_length _ _ ω cs j
    have hlast : ivAt ivO xOf x ω (h ++ [sim (xOf ω h) (cs j)]) j =
        ivO x (xOf ω h) (sim (xOf ω h) (cs j)) := by
      have := ivAt_last ivO xOf x ω h (sim (xOf ω h) (cs j)) []
      rwa [List.append_nil, hlen] at this
    have hpre : ∀ k ∈ range j, ivAt ivO xOf x ω (h ++ [sim (xOf ω h) (cs j)]) k =
        ivAt ivO xOf x ω h k := fun k hk =>
      ivAt_append ivO xOf x ω h _ (by rw [hlen]; exact Finset.mem_range.1 hk)
    rw [e, hl, Finset.sum_range_succ, hlast, Finset.sum_congr rfl fun k hk => by rw [hpre k hk]]
    have := c5of_union p CrtGen.tables iv0 ((Rpg x (xOf ω h) (cs j)).Q5 g s)
      ((progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω cs j).Q5 g (prog x (xOf ω h) (cs j) s))
    omega

/-- **The earlier programmings read no slice.** -/
theorem progsRd_q3 (hkeep : ∀ x xI c s, (prog x xI c s).2 = s.2)
    (Rpg : ∀ x xI c, TRd (fun (_ : Tab3) s => (prog x xI c s).1)) {m5 mE : ℕ}
    (hRpg : ∀ x xI c, Conf (Rpg x xI c) (fun _ => ivO x xI (sim xI c)) m5 mE)
    (x : X) (ω : Ω) (cs : ℕ → C) :
    ∀ j g s, (progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω cs j).Q3 g s = ∅
  | 0, g, s => rfl
  | j + 1, g, s => by
    have e : (progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω cs (j + 1)).Q3 g s =
        (Rpg x (xOf ω (simPre (gS sim xOf) (gPg prog xOf) ω cs j).1) (cs j)).Q3 g s ∪
          (progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω cs j).Q3 g
            (prog x (xOf ω (simPre (gS sim xOf) (gPg prog xOf) ω cs j).1) (cs j) s) := rfl
    rw [e, (hRpg _ _ _).h3, progsRd_q3 hkeep Rpg hRpg x ω cs j, Finset.union_empty]


/-- **Sums over the slots before and after `i`** are within the sum over the slots other than
`i`. -/
lemma sum_around_le {N i : ℕ} (hi : i < N) (f : ℕ → ℕ) (a b : ℕ) :
    ∑ k ∈ range i, a * f k + ∑ t ∈ range (N - (i + 1)), b * f (i + 1 + t) ≤
      ∑ j ∈ (range N).erase i, max a b * f j := by
  classical
  have hdisj : Disjoint (range i) ((range (N - (i + 1))).map (addLeftEmbedding (i + 1))) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    obtain ⟨t, -, rfl⟩ := Finset.mem_map.1 hk'
    simp only [Finset.mem_range, addLeftEmbedding_apply] at hk
    omega
  have hsub : range i ∪ (range (N - (i + 1))).map (addLeftEmbedding (i + 1)) ⊆ (range N).erase i := by
    intro k hk
    rcases Finset.mem_union.1 hk with hk | hk
    · simp only [Finset.mem_range] at hk
      exact Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 (by omega)⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_map.1 hk
      simp only [Finset.mem_range] at ht
      simp only [addLeftEmbedding_apply]
      exact Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 (by omega)⟩
  calc ∑ k ∈ range i, a * f k + ∑ t ∈ range (N - (i + 1)), b * f (i + 1 + t)
      ≤ ∑ k ∈ range i, max a b * f k + ∑ t ∈ range (N - (i + 1)), max a b * f (i + 1 + t) :=
        add_le_add (Finset.sum_le_sum fun k _ => Nat.mul_le_mul_right _ (le_max_left _ _))
          (Finset.sum_le_sum fun k _ => Nat.mul_le_mul_right _ (le_max_right _ _))
    _ = ∑ j ∈ range i ∪ (range (N - (i + 1))).map (addLeftEmbedding (i + 1)), max a b * f j := by
        rw [Finset.sum_union hdisj, Finset.sum_map]
        rfl
    _ ≤ ∑ j ∈ (range N).erase i, max a b * f j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _

end GameCharge

/-! ## The hop's charges -/

section HopCharge

variable {p : Params} {X : Type} {I W C O Ω : Type*} [Nonempty C]
  {prove : X → I → W → Bytes 16 → Tab3 → Sh p → O} {sim : I → C → O}
  {prog : X → I → C → Sh p → Sh p} {xOf : Ω → List O → I} {wOf : Ω → List O → W}
  (ivO : X → I → O → Option ByteArray) {N : ℕ}

/-- **The cipher charge of slot `i` in a view**: the game reader's keys at CTR blocks of the
slot's `iv`, plus `a_E` per other slot whose `iv` may share them. -/
noncomputable def nE (R : GRd Ω O p X N) (aE : ℕ) (i : ℕ)
    (v : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X) : ℕ :=
  cEof (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 i) (R.QE v.1 v.2.1 v.2.2.1 v.2.2.2) +
    ∑ j ∈ (range N).erase i,
      aE * ovE (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 i) (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 j)

/-- **The `H₅` charge of slot `i` in a view.** -/
noncomputable def n5 (R : GRd Ω O p X N) (a5 : ℕ) (i : ℕ)
    (v : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X) : ℕ :=
  c5of p CrtGen.tables (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 i) (R.Q5 v.1 v.2.1 v.2.2.1 v.2.2.2) +
    ∑ j ∈ (range N).erase i,
      a5 * ov5 (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 i) (ivAt ivO xOf v.2.2.2.2.2 v.1 v.2.1 j)

/-- **The `H₃` charge of slot `i` in a view**: the game reader's keys of slice `i`. -/
def n3 (R : GRd Ω O p X N) (i : ℕ) (v : Ω × List O × (Fin N → Tab3) × ShX (Blk → Blk) p X) : ℕ :=
  if h : i < N then (R.Q3 v.1 v.2.1 v.2.2.1 v.2.2.2 ⟨i, h⟩).card else 0

variable (prove wOf) in
/-- **The hop's charges are the view's**: for the `iv` of slot `i`'s output, the hop reader's
`H₃` keys are the game reader's keys of slice `i`, and its cipher and `H₅` charges are at most
`nE`, `n5` of the rest of the game's view. -/
theorem hopRd_charges (hkeep : ∀ x xI c s, (prog x xI c s).2 = s.2)
    (Rpg : ∀ x xI c, TRd (fun (_ : Tab3) s => (prog x xI c s).1)) {m5 mE : ℕ}
    (hRpg : ∀ x xI c, Conf (Rpg x xI c) (fun _ => ivO x xI (sim xI c)) m5 mE)
    (RP : ∀ x xI w r g', TRd (fun (_ : Tab3) (s : Sh p) => prove x xI w r g' s)) {s5 sE : ℕ}
    (hRP : ∀ x xI w r g', Conf (RP x xI w r g') (fun s => ivO x xI (prove x xI w r g' s)) s5 sE)
    (R : GRd Ω O p X N) (hc : R.Cons)
    (Ev : Ω → List O → (Fin N → Tab3) → ShX (Blk → Blk) p X → Prop)
    (hEv : R.Reads (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2)) (i : Fin N) (ω : Ω)
    (τ : Fin N → Slot (Bytes 16) C Tab3) (x : X) (o : O) (g : Tab3) (s : Sh p) :
    let rd := hopRd (sim := sim) (xOf := xOf) prove wOf hkeep Rpg RP R hc Ev hEv i ω τ x o
    let v := contView (gP prove xOf wOf) (gS sim xOf) (gPg prog xOf) i ω τ o g
      ((simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).2 (atX s x))
    let iv0 := ivO x (xOf ω (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1) o
    (rd.Q3 g s).card = n3 R i v ∧
      cEof iv0 (rd.QE g s) ≤ nE ivO (xOf := xOf) R (max mE sE) i v ∧
      c5of p CrtGen.tables iv0 (rd.Q5 g s) ≤ n5 ivO (xOf := xOf) R (max m5 s5) i v := by
  intro rd v iv0
  set h0 := (simPre (gS sim xOf) (gPg prog xOf) ω (tapeC τ) i).1 with hh0
  set u := progsAt sim prog xOf x ω (tapeC τ) i s
  set L := realFrom (gP prove xOf wOf) ω (tapeR τ) (atX u x) (h0 ++ [o]) (i.val + 1)
    (N - (i.val + 1)) with hL
  have hlen : h0.length = i.val := simPre_length _ _ ω _ i.val
  have hv : v = (ω, L, Function.update (tapeG τ) i g, atX u x) := by
    simp only [v, contView, simPre_atX]
    rfl
  obtain ⟨r, hr⟩ := realFrom_prefix (gP prove xOf wOf) ω (tapeR τ) (atX u x) (N - (i.val + 1))
    (h0 ++ [o]) (i.val + 1)
  have hiv : ivAt ivO xOf x ω L i.val = iv0 := by
    rw [hL, hr, ← hlen]; exact ivAt_last ivO xOf x ω h0 o r
  have hpre : ∀ k < i.val, ivAt ivO xOf x ω h0 k = ivAt ivO xOf x ω L k := fun k hk => by
    rw [hL, hr, List.append_assoc]
    exact (ivAt_append ivO xOf x ω h0 _ (by rw [hlen]; exact hk)).symm
  -- the reads of the hop reader: the programmings', then the real proofs' and the game reader's
  have eQ3 : rd.Q3 g s = (progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω (tapeC τ) i).Q3 g s ∪
      (realFromRd (xOf := xOf) prove wOf RP x ω (tapeR τ)
        (Φ := fun l g s => Ev ω l (Function.update (tapeG τ) i g) (atX s x))
        (fun l => R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω l (tapeG τ) i x)
        (N - (i.val + 1)) (h0 ++ [o]) (i.val + 1)).Q3 g u := rfl
  have eQE : rd.QE g s = (progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω (tapeC τ) i).QE g s ∪
      (realFromRd (xOf := xOf) prove wOf RP x ω (tapeR τ)
        (Φ := fun l g s => Ev ω l (Function.update (tapeG τ) i g) (atX s x))
        (fun l => R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω l (tapeG τ) i x)
        (N - (i.val + 1)) (h0 ++ [o]) (i.val + 1)).QE g u := rfl
  have eQ5 : rd.Q5 g s = (progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω (tapeC τ) i).Q5 g s ∪
      (realFromRd (xOf := xOf) prove wOf RP x ω (tapeR τ)
        (Φ := fun l g s => Ev ω l (Function.update (tapeG τ) i g) (atX s x))
        (fun l => R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω l (tapeG τ) i x)
        (N - (i.val + 1)) (h0 ++ [o]) (i.val + 1)).Q5 g u := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [eQ3, progsRd_q3 (xOf := xOf) ivO hkeep Rpg hRpg x ω (tapeC τ) i g s, Finset.empty_union,
      realFromRd_q3 (xOf := xOf) (wOf := wOf) ivO RP hRP x ω (tapeR τ) _ _ _ _ g u, hv]
    simp only [n3, i.isLt, ↓reduceDIte]
    rfl
  · rw [eQE]
    have h1 : cEof iv0 ((progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω (tapeC τ) i).QE g s) ≤
        ∑ k ∈ range i.val, mE * ovE iv0 (ivAt ivO xOf x ω L k) := by
      have := progsRd_cE (xOf := xOf) ivO hkeep Rpg hRpg x ω (tapeC τ) iv0 i g s
      rw [Finset.sum_congr rfl fun k hk => by rw [hpre k (Finset.mem_range.1 hk)]] at this
      exact this
    have h2 : cEof iv0 ((realFromRd (xOf := xOf) prove wOf RP x ω (tapeR τ)
        (Φ := fun l g s => Ev ω l (Function.update (tapeG τ) i g) (atX s x))
        (fun l => R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω l (tapeG τ) i x)
        (N - (i.val + 1)) (h0 ++ [o]) (i.val + 1)).QE g u) ≤
        cEof iv0 ((R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω L (tapeG τ) i x).QE g u) +
          ∑ t ∈ range (N - (i.val + 1)), sE * ovE iv0 (ivAt ivO xOf x ω L (i.val + 1 + t)) := by
      have := realFromRd_cE (xOf := xOf) (wOf := wOf) ivO RP hRP x ω (tapeR τ)
        (Φ := fun l g s => Ev ω l (Function.update (tapeG τ) i g) (atX s x))
        (fun l => R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω l (tapeG τ) i x) iv0
        (N - (i.val + 1)) (h0 ++ [o]) (i.val + 1) g u
      have e2 : ∀ t, (h0 ++ [o]).length + t = i.val + 1 + t := fun t => by
        simp only [List.length_append, List.length_singleton, hlen]
      simp only [e2] at this
      exact this
    have h3 := sum_around_le i.isLt (fun j => ovE iv0 (ivAt ivO xOf x ω L j)) mE sE
    have h4 := cEof_union iv0
      ((progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω (tapeC τ) i).QE g s)
      ((realFromRd (xOf := xOf) prove wOf RP x ω (tapeR τ)
        (Φ := fun l g s => Ev ω l (Function.update (tapeG τ) i g) (atX s x))
        (fun l => R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω l (tapeG τ) i x)
        (N - (i.val + 1)) (h0 ++ [o]) (i.val + 1)).QE g u)
    have h5 : nE ivO (xOf := xOf) R (max mE sE) i v =
        cEof iv0 ((R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω L (tapeG τ) i x).QE g u) +
          ∑ j ∈ (range N).erase i.val, max mE sE * ovE iv0 (ivAt ivO xOf x ω L j) := by
      rw [hv]
      simp only [nE, atX, hiv]
      rfl
    rw [h5]
    omega
  · rw [eQ5]
    have h1 : c5of p CrtGen.tables iv0 ((progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω (tapeC τ) i).Q5 g s) ≤
        ∑ k ∈ range i.val, m5 * ov5 iv0 (ivAt ivO xOf x ω L k) := by
      have := progsRd_c5 (xOf := xOf) ivO hkeep Rpg hRpg x ω (tapeC τ) iv0 i g s
      rw [Finset.sum_congr rfl fun k hk => by rw [hpre k (Finset.mem_range.1 hk)]] at this
      exact this
    have h2 : c5of p CrtGen.tables iv0 ((realFromRd (xOf := xOf) prove wOf RP x ω (tapeR τ)
        (Φ := fun l g s => Ev ω l (Function.update (tapeG τ) i g) (atX s x))
        (fun l => R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω l (tapeG τ) i x)
        (N - (i.val + 1)) (h0 ++ [o]) (i.val + 1)).Q5 g u) ≤
        c5of p CrtGen.tables iv0 ((R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω L (tapeG τ) i x).Q5 g u) +
          ∑ t ∈ range (N - (i.val + 1)), s5 * ov5 iv0 (ivAt ivO xOf x ω L (i.val + 1 + t)) := by
      have := realFromRd_c5 (xOf := xOf) (wOf := wOf) ivO RP hRP x ω (tapeR τ)
        (Φ := fun l g s => Ev ω l (Function.update (tapeG τ) i g) (atX s x))
        (fun l => R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω l (tapeG τ) i x) iv0
        (N - (i.val + 1)) (h0 ++ [o]) (i.val + 1) g u
      have e2 : ∀ t, (h0 ++ [o]).length + t = i.val + 1 + t := fun t => by
        simp only [List.length_append, List.length_singleton, hlen]
      simp only [e2] at this
      exact this
    have h3 := sum_around_le i.isLt (fun j => ov5 iv0 (ivAt ivO xOf x ω L j)) m5 s5
    have h4 := c5of_union p CrtGen.tables iv0
      ((progsRd (sim := sim) (xOf := xOf) hkeep Rpg x ω (tapeC τ) i).Q5 g s)
      ((realFromRd (xOf := xOf) prove wOf RP x ω (tapeR τ)
        (Φ := fun l g s => Ev ω l (Function.update (tapeG τ) i g) (atX s x))
        (fun l => R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω l (tapeG τ) i x)
        (N - (i.val + 1)) (h0 ++ [o]) (i.val + 1)).Q5 g u)
    have h5 : n5 ivO (xOf := xOf) R (max m5 s5) i v =
        c5of p CrtGen.tables iv0 ((R.atRd hc (fun v => Ev v.1 v.2.1 v.2.2.1 v.2.2.2) hEv ω L (tapeG τ) i x).Q5 g u) +
          ∑ j ∈ (range N).erase i.val, max m5 s5 * ov5 iv0 (ivAt ivO xOf x ω L j) := by
      rw [hv]
      simp only [n5, atX, hiv]
      rfl
    rw [h5]
    omega

end HopCharge


end VoleMole.Theft
