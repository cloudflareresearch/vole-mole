import VoleMole.Theft.JointRun
import VoleMole.Theft.PlainRataManyRom

/-!
# `ROM/`'s straight-line extractor at points

The theft games' event runs `ROM/`'s straight-line extractor `eRom` (`Theft/PlainRataRom.lean`,
the many-token `eRomN`). `eRom_congr` (`Theft/PlainRataReads.lean`) has it read the cipher in
**rows** (`romRows`: the query list's cells' rows, the reconstruction's rows, the zero key's
row; via `extract_congr_rows`). Every one of those reads is at a point: a cell of the query list,
or a CTR block of the forged proof's `iv` (the extraction looks up the logged keys at the leaf
positions `lp iv i c`, the reconstruction and the candidates' PRG expansions use the forged
`iv`). Here:

* `extractKey_congrP`, `knownOf_congrP`, `keysOf_congrP`: the extraction from a cipher log at the
  CTR blocks of `iv` of the logged keys and of the reconstruction's nodes;
* `uBit_congrP`: a candidate bit reads the PRG only at the CTR blocks of its `iv` of its keys;
* **`eRom_congrP`**: `eRom` reads the cipher only at `romPts`: the query list's cells, and the
  points of `romKeysP` (zero key, the cells' keys, the reconstruction's nodes) at the CTR blocks of
  the forged proof's `iv` (`romIv`); `romPts_congr`: tables that agree there have the same points.
  So a slot is charged for the extraction's points only if the forged proof's `iv` shares its
  middle bytes (`romPts_inY`).
-/

open Finset OracleComp OracleSpec

set_option synthInstance.maxSize 1024

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## The extraction at points -/

section Extract

variable {log : QueryLog cspec} {E E' : CTable} {iv : ByteArray}

/-- `lp iv i c` is a CTR block of `iv`. -/
lemma lp_inY (iv : ByteArray) (i c : ℕ) : InY iv (lp iv i c) := ⟨_, _, rfl⟩

/-- **The extraction reads the logged keys at the leaf positions of `iv` only.** -/
theorem extractKey_congrP (h : ∀ k ∈ logKeys log, PtsAgree E.cipher E'.cipher k iv) (i : ℕ)
    (a : ByteArray) : extractKey log E iv i a = extractKey log E' iv i a := by
  unfold extractKey
  refine congrArg _ (find?_congr_mem fun q hq => ?_)
  have hk := h _ (mem_logKeys hq)
  have e0 : E (q.1.1, lp iv i 0) = E' (q.1.1, lp iv i 0) := hk _ _
  have e1 : E (q.1.1, lp iv i 1) = E' (q.1.1, lp iv i 1) := hk _ _
  rw [e0, e1]

theorem knownOf_congrP (h : ∀ k ∈ logKeys log, PtsAgree E.cipher E'.cipher k iv)
    (opening : ByteArray) : knownOf log E iv opening = knownOf log E' iv opening := by
  unfold knownOf
  simp only [extractKey_congrP h]

/-- **The leaf keys at points**: the logged keys and the reconstruction's nodes at the CTR blocks
of `iv`. -/
theorem keysOf_congrP {opening delta : ByteArray}
    (h : ∀ k ∈ logKeys log ∪ rdKeys E.cipher iv opening delta, PtsAgree E.cipher E'.cipher k iv) :
    keysOf log E iv opening delta = keysOf log E' iv opening delta := by
  have hr := reconstruct_ic_congrP (E := E.cipher) (E' := E'.cipher) (iv := iv) (opening := opening)
    (delta := delta) fun k hk => h k (mem_union_right _ hk)
  have he := extractKey_congrP (log := log) (E := E) (E' := E') (iv := iv)
    fun k hk => h k (mem_union_left _ hk)
  unfold keysOf
  rw [← hr]
  simp only [he]

/-- **A candidate bit reads the PRG only at the CTR blocks of its `iv` of its keys.** -/
theorem uBit_congrP {E E' : Cipher} {p : Params} {iv : ByteArray} {corr : ℕ → ByteArray}
    {key : ℕ → ℕ → ByteArray} {i : Fin BAVC.tau} (r : ℕ)
    (h : ∀ j < 2 ^ BAVC.kOf i, (key i j).size = 16 → PtsAgree E E' (blk 16 (key i j)) iv) :
    @uBit (icPrg E) p iv corr key i r = @uBit (icPrg E') p iv corr key i r := by
  have hs : (∑ j ∈ range (2 ^ BAVC.kOf i),
      zb (wbit (@prgWords (icPrg E) p iv i (key i j)) r)) =
      ∑ j ∈ range (2 ^ BAVC.kOf i), zb (wbit (@prgWords (icPrg E') p iv i (key i j)) r) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.1 hj
    unfold prgWords
    rw [icPrg_congrP (h j hj)]
  unfold uBit smallVoleU
  rw [hs]

end Extract

/-! ## `eRom` at points -/

namespace Ratatouille

open VoleMole.Privacy.Ratatouille VoleMole.Spec.Ratatouille

section ERom

variable {G S : Type} {L M : ℕ}

/-- The forged proof's `iv` (with the extra table's `H₄`, `mu₁`). -/
noncomputable def romIv (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows) (x : XTab L M) :
    ByteArray :=
  ivOf (hbX x) ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩ ((Hit.Rata.fd A op).1.mu1 (hbX x))

/-- **The keys `eRom` reads at the forged `iv`**: the zero key, the query list's cells' keys, the
reconstruction's nodes. -/
noncomputable def romKeysP (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows)
    (qs : List DomIC) (E : Blk → Blk → Blk) (x : XTab L M) : Finset Blk :=
  insert zeroRow ((qs.filterMap decE).toFinset ∪
    rdKeys E (romIv A op x) (Proof.opening ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩)
      (Proof.delta ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩))

/-- **The points `eRom` reads**: the query list's cells, and `romKeysP` at the CTR blocks of the
forged `iv`. -/
noncomputable def romPts (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows)
    (qs : List DomIC) (E : Blk → Blk → Blk) (x : XTab L M) : Finset (Blk × Blk) :=
  (qs.filterMap decC).toFinset ∪ ptsOf (romKeysP A op qs E x) (romIv A op x)

lemma card_romKeysP_le (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows) (qs : List DomIC)
    (E : Blk → Blk → Blk) (x : XTab L M) :
    (romKeysP A op qs E x).card ≤ (qs.filterMap decE).toFinset.card + 4608 :=
  (card_insert_le _ _).trans (by
    have := (card_union_le _ _).trans (Nat.add_le_add_left (rdKeys_card E (romIv A op x)
      (Proof.opening ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩)
      (Proof.delta ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩))
      (qs.filterMap decE).toFinset.card)
    omega)

lemma decE_of_decC {d : DomIC} {kz : Blk × Blk} (h : decC d = some kz) : decE d = some kz.1 := by
  rcases d with d | c
  · simp [decC] at h
  · simp only [decC, Option.some.injEq] at h
    subst h; rfl

/-- **The cipher keys of `eRom`'s points**: the cells' keys and `romKeysP`. -/
lemma card_romPts_keys_le (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows) (qs : List DomIC)
    (E : Blk → Blk → Blk) (x : XTab L M) :
    ((romPts A op qs E x).image Prod.fst).card ≤ (qs.filterMap decE).toFinset.card + 4608 := by
  classical
  refine (card_le_card fun k hk => ?_).trans (card_romKeysP_le A op qs E x)
  obtain ⟨kz, hkz, rfl⟩ := mem_image.1 hk
  rcases mem_union.1 hkz with h | h
  · obtain ⟨d, hd, hdk⟩ := List.mem_filterMap.1 (List.mem_toFinset.1 h)
    exact mem_insert_of_mem (mem_union_left _ (mem_dec hd (decE_of_decC hdk)))
  · exact (mem_ptsOf.1 h).1

/-- **The extraction's points at the forged `iv` are CTR blocks of it.** -/
lemma romPts_inY (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows) (qs : List DomIC)
    (E : Blk → Blk → Blk) (x : XTab L M) {kz : Blk × Blk}
    (h : kz ∈ ptsOf (romKeysP A op qs E x) (romIv A op x)) : InY (romIv A op x) kz.2 :=
  (mem_ptsOf.1 h).2

set_option maxHeartbeats 1000000 in
/-- **`eRom` reads neither the slices nor `H₅`, and the cipher only at `romPts`.** -/
theorem eRom_congrP (A : Thief Sizes.labelRows G S)
    (p₁ : Option (IssueInstance × IssueProof Sizes.labelRows))
    (p₂ : Option (SpendInstance × SpendProof Sizes.labelRows)) (op : Op Sizes.labelRows)
    (qs : List DomIC) (g₁ g₂ g₁' g₂' : Tab3) (G5 G5' : Tab5F) {E E' : Blk → Blk → Blk}
    (x : XTab L M) (h : ∀ kz ∈ romPts A op qs E x, E kz.1 kz.2 = E' kz.1 kz.2) :
    eRom A p₁ p₂ op qs g₁' g₂' ((G5', E'), x) = eRom A p₁ p₂ op qs g₁ g₂ ((G5, E), x) := by
  rw [eRom_eq, eRom_eq]
  have hc : cLog (ctOf E') qs = cLog (ctOf E) qs :=
    (cLog_congr fun c hc => by
      show E c.1 c.2 = E' c.1 c.2
      exact h c (mem_union_left _ (mem_dec hc rfl))).symm
  rw [hc]
  have hP : ∀ k ∈ romKeysP A op qs E x, PtsAgree E E' k (romIv A op x) := fun k hk c t =>
    h (k, _) (mem_union_right _ (mem_ptsOf.2 ⟨hk, c, t, rfl⟩))
  unfold romKeysP at hP
  unfold romIv at hP
  generalize Hit.Rata.fd A op = f at hP ⊢
  generalize cLog (ctOf E) qs = log at hc ⊢
  have hsub : logKeys log ⊆ (qs.filterMap decE).toFinset := hc ▸ logKeys_cLog_subset _ _
  set iv := ivOf (hbX x) ⟨f.1.params, f.2⟩ (f.1.mu1 (hbX x))
  have hk : keysOf log (ctOf E) iv (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩) =
      keysOf log (ctOf E') iv (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩) :=
    keysOf_congrP (E := ctOf E) (E' := ctOf E') (iv := iv) fun k hk' => by
      rcases mem_union.1 hk' with hk' | hk'
      · exact hP k (mem_insert_of_mem (mem_union_left _ (hsub hk')))
      · exact hP k (mem_insert_of_mem (mem_union_right _ hk'))
  have hkn : knownOf log (ctOf E) iv (Proof.opening ⟨f.1.params, f.2⟩) =
      knownOf log (ctOf E') iv (Proof.opening ⟨f.1.params, f.2⟩) :=
    knownOf_congrP (E := ctOf E) (E' := ctOf E') (iv := iv)
      (fun k hk' => hP k (mem_insert_of_mem (mem_union_left _ (hsub hk')))) _
  have hr : rOut f.1 f.2 (hbX x) (ctOf E') log = rOut f.1 f.2 (hbX x) (ctOf E) log := by
    unfold rOut
    rw [← hk, ← hkn]
  rw [hr]
  have hu0 : ∀ (i : Fin BAVC.tau) (j : ℕ) (corr : ℕ → ByteArray),
      @uBit (icPrg (ctOf E').cipher) f.1.params iv corr (keysOf log (ctOf E) iv
        (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩)) i j =
      @uBit (icPrg (ctOf E).cipher) f.1.params iv corr (keysOf log (ctOf E) iv
        (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩)) i j := by
    intro i j corr
    refine (uBit_congrP (E := (ctOf E).cipher) (E' := (ctOf E').cipher) j fun j' _ _ => ?_).symm
    have hrow := keysOf_row log (ctOf E) iv (Proof.opening ⟨f.1.params, f.2⟩)
      (Proof.delta ⟨f.1.params, f.2⟩) i j'
    have hmem : blk 16 (keysOf log (ctOf E) iv (Proof.opening ⟨f.1.params, f.2⟩)
        (Proof.delta ⟨f.1.params, f.2⟩) i j') ∈ insert zeroRow ((qs.filterMap decE).toFinset ∪
          rdKeys E iv (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩)) := by
      rcases mem_insert.1 hrow with hz | hl
      · rw [hz]; exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_union_left _ (hsub hl))
    exact hP _ hmem
  have ek : (outChain (rOut f.1 f.2 (hbX x) (ctOf E) log)).keys = keysOf log (ctOf E) iv
      (Proof.opening ⟨f.1.params, f.2⟩) (Proof.delta ⟨f.1.params, f.2⟩) := rfl
  have ei : (outChain (rOut f.1 f.2 (hbX x) (ctOf E) log)).iv = iv := rfl
  have hcand : candOf (ctOf E') f.1 (rOut f.1 f.2 (hbX x) (ctOf E) log) =
      candOf (ctOf E) f.1 (rOut f.1 f.2 (hbX x) (ctOf E) log) := by
    funext i
    unfold candOf Chain.u
    simp only [ek, ei, hu0]
  rw [hcand]

/-- **Tables that agree at `eRom`'s points have the same points.** -/
theorem romPts_congr (A : Thief Sizes.labelRows G S) (op : Op Sizes.labelRows) (qs : List DomIC)
    {E E' : Blk → Blk → Blk} (x : XTab L M)
    (h : ∀ kz ∈ romPts A op qs E x, E kz.1 kz.2 = E' kz.1 kz.2) :
    romPts A op qs E' x = romPts A op qs E x := by
  have hA : RecAgreeP E E' (romIv A op x)
      (Proof.opening ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩)
      (Proof.delta ⟨(Hit.Rata.fd A op).1.params, (Hit.Rata.fd A op).2⟩) := fun k hk c t =>
    h (k, _) (mem_union_right _ (mem_ptsOf.2 ⟨mem_insert_of_mem (mem_union_right _ hk), c, t, rfl⟩))
  unfold romPts romKeysP
  rw [rdKeys_ic_congrP hA]

end ERom

end Ratatouille

end VoleMole.Theft
