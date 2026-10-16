import VoleMole.ZK.HopsH23

/-!
# Zero knowledge in the random-oracle and ideal-cipher model with `H₂³` visible (`lean/docs/zk.md` §10.1)

`zk_rom_ic` (`ZK/HopsJoint.lean`) computes the BAVC's hidden part with a uniform cipher table `E`,
but its distinguisher does not read `H₂³`; `zk_rom_h23` (`ZK/HopsH23.lean`) lets it read `H₂³` but
assumes BAVC hiding (`HideHyp`). Here both at once, for the executable prover and verifier with
the cipher a uniform table in the **whole** BAVC and VOLE expansion.

**The cipher-parametric code.** The executable BAVC, VOLE expansion, prover and verifier call the
CTR PRG through the class `HasPrg` (`Verifier/Prg.lean`; the executable instance is AES). With the
instance `icPrg E` (`ZK/HopsH4.lean`: the CTR PRG of the table `E` on 16-byte keys) they are the
prover and verifier of the ideal-cipher model; at `E = aesTable` they are the executable ones
(`icPrg_aes`; `prove_icPrg_aes`, `reconstruct_icPrg_aes`, `convertToVoleAt_icPrg_aes`,
`verify_icPrg_aes`, `vPre_icPrg_aes`). Every lemma of `zk_rom_h23`'s chain is stated for any
instance, so its completeness step (outside `GrindBad`, the verifier's recomputed grinding prefix
is the prover's: `hyb3_vPre`, from `vPre_proveCommit`, `bavcComplete`, `crtComplete`) holds for
every cipher: the VOLE correlation `q = v + Δ·u` only needs the prover and the verifier to use the
same PRG.

**The reads of the honest recomputation.** After H4 the hidden part is uniform, and the rest of the
view is computed from it and `E`: the prover's public part (the opened subtrees, `pubOf`, and the
key columns, `qcolsOf`) and the simulator's recomputation of the grinding prefix (`vPre` on the
proof, whose opening is the tape's, `hyb3_ok_fields`). Both read `E` only at the nodes that
`BAVC.reconstruct` rebuilds from the opening (`rdKeys`; `reconstruct_ic_congr`, by induction on the
derivation, node `n` being final from step `n` on, `derivN_stable`; `convertToVoleAt_ic_congr`: the
leaf keys off the hidden leaves are nodes, `leafKey_reconstruct`; `hyb3_ic_congr`, `vPre_ic_congr`),
at most `2L − 1 = 4607` keys (`rdKeys_card`). They are counted with the distinguisher's reads in
`hide_rom_query` (`viewKeys`, `viewIC_congr`, `joint3_h4`).

**The `H₅` table** is on every `37`-byte input (`HopsH23.Tab5F`): a table on the sibling inputs
(`HopsROM.sEnc`) would sit at positions computed with the cipher, so that the record, and with it
the view, would depend on `E` everywhere. H6 for this layout: `HopsH6.lab_romG`, `pr_bad_leG`,
`HopsH23.lab_rom_hyp_sG`.

**`zk_rom_ic_h23`.** For a statement with dedicated label rows, a witness satisfying the
deterministic hypotheses (`ZKHyp`), `HashesWF Hb` and `SmallParams`, the advantage is at most

    q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸

against a distinguisher that sees the proof, `H₃`, `H₂³`, `H₅` and `E`, and reads `H₃`, `H₅`, `E`
adaptively at `q₃`, `q₅`, `q_E` keys and `H₂³` freely. The hybrids: `zk_pre_h4` (H1, grinding and
programming, the programmed points recomputed: for every `E`), `joint3_h4` (H4, jointly over the
root seed and `E`), `zk_post_h4` (the tape, H6, the simulator: for every `E`).

`Pr[GrindBad] ≤ 2⁻¹¹⁰` for these tables (`ZK/GrindNum.lean`: `grindBad_le_110`, and
`zk_rom_ic_h23_num`, the bound above with `2⁻¹¹⁰` in its place).

**Not covered.** The second `4607` counts the honest recomputation's reads; they are all values
of tree nodes off the hidden paths, which `IC.hop`'s candidates already contain, so an argument
inside the hybrid would remove it. One proof; the cipher's rows are uniform functions (the PRF
view). With the rows uniform permutations (AES as a family of random permutations, the
distinguisher reading whole rows, so forward and inverse queries) the same chain is
`zk_rom_ic_h23_perm` (`ZK/HopsICPerm.lean`), the PRP/PRF switching term `switchEps` proved there
(`ZK/HopsH4Perm.lean`); the privacy games with permutation rows are `Privacy/PermRO.lean`,
`Privacy/PermRA.lean`. SHAKE as a random oracle and AES as an ideal cipher are the modelling
steps.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

/-! ## `BAVC.reconstruct`, unfolded -/

section Unfold

variable [HasPrg]

/-- The opened seeds placed at their nodes (the start of `BAVC.reconstruct`'s derivation). -/
def placedOf (opening delta : ByteArray) : Array (Option ByteArray) :=
  (List.range (BAVC.openNodes delta).size).foldl (fun known k =>
      known.set! (BAVC.openNodes delta)[k]! (some (opening.extract (BAVC.tau * BAVC.hashLen + 16 * k)
        (BAVC.tau * BAVC.hashLen + 16 * k + 16))))
    (Array.replicate BAVC.numNodes none)

/-- The derivation's first `N` steps from any start `A`. -/
def derivN (iv : ByteArray) (A : Array (Option ByteArray)) (N : ℕ) : Array (Option ByteArray) :=
  (List.range N).foldl (BAVC.deriveStep iv) A

/-- The top-down derivation after its first `N` steps. -/
def derivedN (iv opening delta : ByteArray) (N : ℕ) : Array (Option ByteArray) :=
  derivN iv (placedOf opening delta) N

/-- **The reconstructed tree**: the derivation's nodes, the unknown ones zero. -/
def recTree (iv opening delta : ByteArray) : Array ByteArray :=
  (derivedN iv opening delta (BAVC.numLeaves - 1)).map (·.getD BAVC.zeroBlock)

/-- `BAVC.reconstruct`'s test of a malformed opening. -/
def badOpening (opening delta : ByteArray) : Bool :=
  opening.size != BAVC.openSize ||
    decide (BAVC.tau * BAVC.hashLen + 16 * (BAVC.openNodes delta).size > BAVC.openSize) ||
    (List.range (BAVC.openSize - (BAVC.tau * BAVC.hashLen + 16 * (BAVC.openNodes delta).size))).any
      fun k => opening.get! (BAVC.tau * BAVC.hashLen + 16 * (BAVC.openNodes delta).size + k) != 0

theorem reconstruct_eq (iv opening delta : ByteArray) :
    BAVC.reconstruct iv opening delta = if badOpening opening delta then none else
      some (BAVC.leavesOf iv (recTree iv opening delta) (fun i => some (BAVC.deltaIndex delta i))
        (fun i => opening.extract (BAVC.hashLen * i) (BAVC.hashLen * i + BAVC.hashLen))) := rfl

lemma derivedN_eq (iv opening delta : ByteArray) (N : ℕ) :
    derivedN iv opening delta N = derivN iv (placedOf opening delta) N := rfl

lemma derivN_zero (iv : ByteArray) (A : Array (Option ByteArray)) : derivN iv A 0 = A := rfl

lemma derivN_succ (iv : ByteArray) (A : Array (Option ByteArray)) (N : ℕ) :
    derivN iv A (N + 1) = BAVC.deriveStep iv (derivN iv A N) N := by
  simp only [derivN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma derivedN_succ (iv opening delta : ByteArray) (N : ℕ) :
    derivedN iv opening delta (N + 1) = BAVC.deriveStep iv (derivedN iv opening delta N) N :=
  derivN_succ iv _ N

omit [HasPrg] in
lemma placedOf_size (opening delta : ByteArray) : (placedOf opening delta).size = BAVC.numNodes := by
  unfold placedOf
  generalize (List.range (BAVC.openNodes delta).size) = l
  suffices ∀ (A : Array (Option ByteArray)), (l.foldl (fun known k =>
      known.set! (BAVC.openNodes delta)[k]! (some (opening.extract (BAVC.tau * BAVC.hashLen + 16 * k)
        (BAVC.tau * BAVC.hashLen + 16 * k + 16)))) A).size = A.size by
    rw [this]; simp
  induction l with
  | nil => intro A; rfl
  | cons k l ih => intro A; rw [List.foldl_cons, ih, size_set!]

lemma deriveStep_size (iv : ByteArray) (A : Array (Option ByteArray)) (n : ℕ) :
    (BAVC.deriveStep iv A n).size = A.size := by
  unfold BAVC.deriveStep
  split
  · rw [size_set!, size_set!]
  · rfl

lemma derivN_size (iv : ByteArray) (A : Array (Option ByteArray)) (N : ℕ) :
    (derivN iv A N).size = A.size := by
  induction N with
  | zero => rfl
  | succ N ih => rw [derivN_succ, deriveStep_size]; exact ih

lemma derivedN_size (iv opening delta : ByteArray) (N : ℕ) :
    (derivedN iv opening delta N).size = BAVC.numNodes := by
  rw [derivedN_eq, derivN_size, placedOf_size]

/-- A derivation step changes only the two children of its node. -/
lemma deriveStep_get_ne (iv : ByteArray) (A : Array (Option ByteArray)) {m n : ℕ}
    (h1 : n ≠ 2 * m + 1) (h2 : n ≠ 2 * m + 2) : (BAVC.deriveStep iv A m)[n]! = A[n]! := by
  unfold BAVC.deriveStep
  split
  · rw [getElem!_set!, getElem!_set!]
    split_ifs with a b
    · exact absurd a.1.symm h2
    · exact absurd b.1.symm h1
    · rfl
  · rfl

/-- **Node `n` is final once step `n` is reached** (later steps set larger nodes). -/
lemma derivN_stable (iv : ByteArray) (A : Array (Option ByteArray)) (n : ℕ) :
    ∀ N, n ≤ N → (derivN iv A N)[n]! = (derivN iv A n)[n]! := by
  intro N
  induction N with
  | zero => intro h; rw [Nat.le_zero.1 h]
  | succ N ih =>
    intro h
    rcases Nat.lt_or_ge n (N + 1) with h' | h'
    · rw [derivN_succ, deriveStep_get_ne iv _ (by omega) (by omega), ih (by omega)]
    · rw [show n = N + 1 by omega]

lemma derivedN_stable (iv opening delta : ByteArray) (n : ℕ) :
    ∀ N, n ≤ N → (derivedN iv opening delta N)[n]! = (derivedN iv opening delta n)[n]! :=
  derivN_stable iv _ n

/-- The reconstructed tree at a node the derivation knows. -/
lemma recTree_get (iv opening delta : ByteArray) {n : ℕ} (hn : n < BAVC.numLeaves - 1)
    {x : ByteArray} (hx : (derivedN iv opening delta n)[n]! = some x) :
    (recTree iv opening delta)[n]! = x := by
  have hN : n < BAVC.numNodes := by
    have : BAVC.numLeaves - 1 < BAVC.numNodes := by decide
    omega
  rw [recTree, getElem!_map' _ _ (by rw [derivedN_size]; exact hN),
    derivedN_stable iv opening delta n _ hn.le, hx]
  rfl

/-! ### The nodes are blocks -/

/-- Every known node of a partial derivation is a 16-byte block. -/
def Blocks (A : Array (Option ByteArray)) : Prop :=
  ∀ (n : ℕ) (x : ByteArray), A[n]! = some x → x.size = 16

omit [HasPrg] in
lemma Blocks.set {A : Array (Option ByteArray)} (hA : Blocks A) (i : ℕ) {x : ByteArray}
    (hx : x.size = 16) : Blocks (A.set! i (some x)) := fun n y hy => by
  rw [getElem!_set!] at hy
  split_ifs at hy
  · cases hy; exact hx
  · exact hA n y hy

omit [HasPrg] in
lemma blocks_replicate (N : ℕ) : Blocks (Array.replicate N none) := fun n x hx => by
  rw [getElem!_def, Array.getElem?_replicate] at hx
  split_ifs at hx

omit [HasPrg] in
lemma badOpening_false {opening delta : ByteArray} (hb : badOpening opening delta = false) :
    opening.size = BAVC.openSize ∧
      BAVC.tau * BAVC.hashLen + 16 * (BAVC.openNodes delta).size ≤ BAVC.openSize := by
  simp only [badOpening, Bool.or_eq_false_iff, bne_eq_false_iff_eq, decide_eq_false_iff_not,
    not_lt] at hb
  exact ⟨hb.1.1, hb.1.2⟩

omit [HasPrg] in
lemma placed_blocks (opening delta : ByteArray) (M : ℕ)
    (hsz : opening.size = BAVC.openSize)
    (hend : BAVC.tau * BAVC.hashLen + 16 * (BAVC.openNodes delta).size ≤ BAVC.openSize) :
    ∀ N, N ≤ (BAVC.openNodes delta).size → Blocks ((List.range N).foldl (fun known k =>
      known.set! (BAVC.openNodes delta)[k]! (some (opening.extract (BAVC.tau * BAVC.hashLen + 16 * k)
        (BAVC.tau * BAVC.hashLen + 16 * k + 16)))) (Array.replicate M none)) := by
  intro N
  induction N with
  | zero => intro _; exact blocks_replicate M
  | succ N ih =>
    intro hN
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine (ih (by omega)).set _ ?_
    rw [ByteArray.size_extract, hsz]
    omega

omit [HasPrg] in
lemma placedOf_blocks {opening delta : ByteArray} (hb : badOpening opening delta = false) :
    Blocks (placedOf opening delta) := by
  obtain ⟨hsz, hend⟩ := badOpening_false hb
  exact placed_blocks opening delta _ hsz hend _ le_rfl

lemma deriveStep_blocks (iv : ByteArray) {A : Array (Option ByteArray)} (hA : Blocks A) (n : ℕ) :
    Blocks (BAVC.deriveStep iv A n) := by
  unfold BAVC.deriveStep
  split
  · exact (hA.set _ (block_size _ _ (by simp [children_size]))).set _
      (block_size _ _ (by simp [children_size]))
  · exact hA

lemma derivN_blocks (iv : ByteArray) {A : Array (Option ByteArray)} (hA : Blocks A) :
    ∀ N, Blocks (derivN iv A N) := by
  intro N
  induction N with
  | zero => exact hA
  | succ N ih => rw [derivN_succ]; exact deriveStep_blocks iv ih N

/-- **For a well-formed opening, the reconstructed tree's nodes are 16-byte blocks.** -/
lemma recTree_size {iv opening delta : ByteArray} (hb : badOpening opening delta = false) {n : ℕ}
    (hn : n < BAVC.numNodes) : ((recTree iv opening delta)[n]!).size = 16 := by
  have hB : ∀ N, Blocks (derivedN iv opening delta N) := derivN_blocks iv (placedOf_blocks hb)
  rw [recTree, getElem!_map' _ _ (by rw [derivedN_size]; exact hn)]
  rcases hx : (derivedN iv opening delta (BAVC.numLeaves - 1))[n]! with _ | x
  · rfl
  · exact hB _ n x hx

/-- **The verifier's leaf keys off the hidden leaves are the reconstructed tree's nodes.** -/
lemma leafKey_reconstruct {iv opening delta : ByteArray} {leaves : BAVC.Leaves}
    (h : BAVC.reconstruct iv opening delta = some leaves) {i j : ℕ} (hi : i < BAVC.tau)
    (hj : j < 2 ^ BAVC.kOf i) (hjd : j ≠ BAVC.deltaIndex delta i) :
    leafKey leaves i j = (recTree iv opening delta)[BAVC.treePos i j]! := by
  rw [reconstruct_eq] at h
  split_ifs at h with hb
  cases h
  rw [Bool.not_eq_true] at hb
  unfold leafKey
  rw [leavesOf_eq]
  have hne : (some (BAVC.deltaIndex delta i) == some j) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq]; exact Ne.symm hjd
  rw [extract_pieces _ 16 (fun i' hi' j' hj' => by
      split
      · rfl
      · exact recTree_size hb (treePos_lt hi' hj')) hi hj]
  simp only [hne, Bool.false_eq_true, ↓reduceIte]

end Unfold

/-! ## At `E = aesTable` the cipher-parametric code is the executable code -/

section Bridge

/-- **The prover with the ideal cipher of `aesTable` is the executable prover.** -/
theorem prove_icPrg_aes : @Prover.prove (icPrg aesTable) = @Prover.prove aesPrg := by
  rw [icPrg_aes]

/-- **The BAVC reconstruction with the ideal cipher of `aesTable` is the executable one.** -/
theorem reconstruct_icPrg_aes : @BAVC.reconstruct (icPrg aesTable) = @BAVC.reconstruct aesPrg := by
  rw [icPrg_aes]

/-- **The verifier's VOLE expansion with the ideal cipher of `aesTable` is the executable one.** -/
theorem convertToVoleAt_icPrg_aes :
    @convertToVoleAt (icPrg aesTable) = @convertToVoleAt aesPrg := by
  rw [icPrg_aes]

/-- **The executable verifier with the ideal cipher of `aesTable` is the executable verifier.** -/
theorem verify_icPrg_aes : @verify (icPrg aesTable) = @verify aesPrg := by
  rw [icPrg_aes]

/-- **The verifier's recomputed grinding prefix with the ideal cipher of `aesTable`** is the one of
the executable code. -/
theorem vPre_icPrg_aes : @vPre (icPrg aesTable) = @vPre aesPrg := by
  rw [icPrg_aes]

end Bridge

/-! ## The reads of the honest recomputation in the ideal-cipher model -/

section Reads

/-- The ideal-cipher PRGs of `E` and `E'` agree on a key at which the tables agree (and on every
key that is not 16 bytes, answered by AES). -/
lemma icPrg_congr {E E' : Cipher} {key : ByteArray}
    (h : key.size = 16 → E (blk 16 key) = E' (blk 16 key)) (iv : ByteArray) (t c : UInt32)
    (n : ℕ) : @HasPrg.prg (icPrg E) key iv t c n = @HasPrg.prg (icPrg E') key iv t c n := by
  show icPrgF E key iv t c n = icPrgF E' key iv t c n
  unfold icPrgF
  split_ifs with hk
  · rw [h hk]
  · rfl

/-- **The keys at which the BAVC reconstruction with the ideal cipher `E` reads the table**: the
reconstructed tree's nodes (the opened seeds and everything derived from them), at most
`2L − 1 = 4607` keys. -/
def rdKeys (E : Cipher) (iv opening delta : ByteArray) : Finset Blk :=
  (range BAVC.numNodes).image fun n => blk 16 ((@recTree (icPrg E) iv opening delta)[n]!)

theorem rdKeys_card (E : Cipher) (iv opening delta : ByteArray) :
    (rdKeys E iv opening delta).card ≤ 4607 :=
  card_image_le.trans (le_of_eq (by rw [card_range]; rfl))

lemma mem_rdKeys {E : Cipher} {iv opening delta : ByteArray} {n : ℕ} (hn : n < BAVC.numNodes) :
    blk 16 ((@recTree (icPrg E) iv opening delta)[n]!) ∈ rdKeys E iv opening delta :=
  Finset.mem_image.2 ⟨n, Finset.mem_range.2 hn, rfl⟩

variable {E E' : Cipher} {iv opening delta : ByteArray}

/-- **The derivation reads the table only at its nodes.** -/
theorem derivedN_ic_congr (h : ∀ k ∈ rdKeys E iv opening delta, E k = E' k) :
    ∀ N ≤ BAVC.numLeaves - 1,
      @derivedN (icPrg E) iv opening delta N = @derivedN (icPrg E') iv opening delta N := by
  have hLN : BAVC.numLeaves - 1 < BAVC.numNodes := by decide
  intro N
  induction N with
  | zero => intro _; exact (@derivN_zero (icPrg E) iv _).trans (@derivN_zero (icPrg E') iv _).symm
  | succ N ih =>
    intro hN
    rewrite [@derivedN_succ (icPrg E), @derivedN_succ (icPrg E'), ← ih (by omega)]
    rcases hA : (@derivedN (icPrg E) iv opening delta N)[N]! with _ | node
    · simp only [BAVC.deriveStep, hA]
    · have hmem : blk 16 node ∈ rdKeys E iv opening delta := by
        have := @mem_rdKeys E iv opening delta N (by omega)
        rwa [@recTree_get (icPrg E) iv opening delta N (by omega) node hA] at this
      have hc : @BAVC.children (icPrg E) iv node N = @BAVC.children (icPrg E') iv node N :=
        icPrg_congr (fun _ => h _ hmem) _ _ _ _
      simp only [BAVC.deriveStep, hA, hc]

theorem recTree_ic_congr (h : ∀ k ∈ rdKeys E iv opening delta, E k = E' k) :
    @recTree (icPrg E) iv opening delta = @recTree (icPrg E') iv opening delta := by
  unfold recTree
  rewrite [derivedN_ic_congr h _ le_rfl]
  rfl

/-- **The reconstruction reads the table only at `rdKeys`.** -/
theorem reconstruct_ic_congr (h : ∀ k ∈ rdKeys E iv opening delta, E k = E' k) :
    @BAVC.reconstruct (icPrg E) iv opening delta = @BAVC.reconstruct (icPrg E') iv opening delta := by
  have ht := recTree_ic_congr h
  rewrite [@reconstruct_eq (icPrg E), @reconstruct_eq (icPrg E'), ← ht]
  split_ifs with hb
  · rfl
  · rewrite [@leavesOf_eq (icPrg E), @leavesOf_eq (icPrg E')]
    simp only [Option.some.injEq, BAVC.Leaves.mk.injEq, true_and]
    apply congrArg (List.foldl (· ++ ·) ByteArray.empty)
    refine pieces_congr fun i hi j hj => ?_
    split_ifs
    · rfl
    · exact icPrg_congr (fun _ => h _ (mem_rdKeys (treePos_lt hi hj))) _ _ _ _

/-- **The verifier's leaf keys off the hidden leaves are among the reconstruction's reads.** -/
theorem leafKey_mem_rdKeys {i j : ℕ} (hi : i < BAVC.tau) (hj : j < 2 ^ BAVC.kOf i)
    (hjd : j ≠ BAVC.deltaIndex delta i)
    (hs : (leafKey ((@BAVC.reconstruct (icPrg E) iv opening delta).getD ⟨.empty, .empty⟩) i j).size
      = 16) :
    blk 16 (leafKey ((@BAVC.reconstruct (icPrg E) iv opening delta).getD ⟨.empty, .empty⟩) i j) ∈
      rdKeys E iv opening delta := by
  rcases hr : @BAVC.reconstruct (icPrg E) iv opening delta with _ | leaves
  · rw [hr] at hs
    simp [leafKey] at hs
  · rw [Option.getD_some, @leafKey_reconstruct (icPrg E) iv opening delta leaves hr i j hi hj hjd]
    exact mem_rdKeys (treePos_lt hi hj)

/-- **The VOLE expansion reads the table only at the leaf keys off the hidden leaves.** -/
theorem convertToVoleAt_ic_congr (p : Params) (dbit : ℕ → Bool) (corr : ℕ → ByteArray)
    (iv : ByteArray) (key : ℕ → ℕ → ByteArray)
    (h : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i, j ≠ BAVC.hiddenIndex dbit i →
      (key i j).size = 16 → E (blk 16 (key i j)) = E' (blk 16 (key i j))) :
    @convertToVoleAt (icPrg E) p dbit corr iv key = @convertToVoleAt (icPrg E') p dbit corr iv key := by
  have ht : ∀ i < BAVC.tau, @treeColumns (icPrg E) p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i) =
      @treeColumns (icPrg E') p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i) := by
    intro i hi
    have hp : @prgOuts (icPrg E) p iv i (BAVC.hiddenIndex dbit i) (key i) =
        @prgOuts (icPrg E') p iv i (BAVC.hiddenIndex dbit i) (key i) := by
      unfold prgOuts
      refine Array.map_congr_left fun j hj => ?_
      have hj := Array.mem_range.1 hj
      split_ifs with hjd
      · rfl
      · simp only [prgWords]
        rw [icPrg_congr (fun hs => h i hi j hj (by simpa using hjd) hs)]
    simp only [treeColumns, hp]
  have htr : ((Array.range BAVC.tau).map fun i =>
      @treeColumns (icPrg E) p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i)) =
      (Array.range BAVC.tau).map fun i =>
        @treeColumns (icPrg E') p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i) :=
    Array.map_congr_left fun i hi => ht i (Array.mem_range.1 hi)
  simp only [convertToVoleAt, htr]

end Reads

/-! ## The honest recomputation reads the cipher only at the opened tree -/

section Congr

/-- **The honest reads of a shared tape at `Δ`**: the keys at which the reconstruction of the
tape's opening reads the cipher table `E` (`rdKeys`; at most `4607`). -/
def hRd (E : Cipher) (Hs : Hashes) (st : Statement) (s : Shared) (δ : Bytes 16) : Finset Blk :=
  rdKeys E (Hs.hash .h4 ((ba s.1 ++ st.mu1 Hs).push 4)) (openingOf (ba δ) s.2.2.1 s.2.2.2) (ba δ)

variable {E E' : Cipher}

theorem pubOf_ic_congr (Hs : Hashes) (st : Statement) (s : Shared) (δ : Bytes 16)
    (h : ∀ k ∈ hRd E Hs st s δ, E k = E' k) :
    @pubOf (icPrg E) Hs st s δ = @pubOf (icPrg E') Hs st s δ := by
  simp only [pubOf]
  rewrite [reconstruct_ic_congr h]
  rfl

theorem qcolsOf_ic_congr (Hs : Hashes) (st : Statement) (s : Shared) (δ : Bytes 16)
    (h : ∀ k ∈ hRd E Hs st s δ, E k = E' k) (c : ByteArray) :
    @qcolsOf (icPrg E') st (@pubOf (icPrg E') Hs st s δ) δ c =
      @qcolsOf (icPrg E) st (@pubOf (icPrg E') Hs st s δ) δ c := by
  rw [← pubOf_ic_congr Hs st s δ h]
  unfold qcolsOf
  refine (convertToVoleAt_ic_congr _ _ _ _ _ fun i hi j hj hjd hs => h _ ?_).symm
  exact leafKey_mem_rdKeys hi hj hjd hs

/-- **The ideal-tape prover depends on the PRG only through the public part** (`pubOf`) and the
key columns (`qcolsOf`), after the grinding outcome. -/
theorem idealCore_inst_congr (i1 i2 : HasPrg) (Hs : Hashes) (T : CrtTables) (st : Statement)
    (w : ByteArray) (s : Shared) (ctr : ℕ) (δ : Bytes 16) (t : Pads st.params)
    (hP : @pubOf i1 Hs st s δ = @pubOf i2 Hs st s δ)
    (hQ : ∀ c, @qcolsOf i1 st (@pubOf i2 Hs st s δ) δ c = @qcolsOf i2 st (@pubOf i2 Hs st s δ) δ c) :
    @idealCore i1 Hs T st w s ctr δ t = @idealCore i2 Hs T st w s ctr δ t := by
  simp only [idealCore, idealTail, cmultIdeal, tCrt, tVRows, tVMask, tUt, tC1, hP, hQ]

theorem proveIdeal_inst_congr (i1 i2 : HasPrg) (Hs : Hashes) (T : CrtTables) (st : Statement)
    (w : ByteArray) (t : IdealTape st.params)
    (hP : @pubOf i1 Hs st t.1 (deltaOf t.1.2.1) = @pubOf i2 Hs st t.1 (deltaOf t.1.2.1))
    (hQ : ∀ c, @qcolsOf i1 st (@pubOf i2 Hs st t.1 (deltaOf t.1.2.1)) (deltaOf t.1.2.1) c =
      @qcolsOf i2 st (@pubOf i2 Hs st t.1 (deltaOf t.1.2.1)) (deltaOf t.1.2.1) c) :
    @proveIdeal i1 Hs T st w t = @proveIdeal i2 Hs T st w t := by
  unfold proveIdeal
  split_ifs
  · rfl
  · rcases hf : firstHit t.1.2.1 with _ | ⟨ctr, δ⟩
    · rfl
    · have hd : deltaOf t.1.2.1 = δ := by unfold deltaOf; rw [hf]; rfl
      rw [hd] at hP hQ
      exact idealCore_inst_congr i1 i2 Hs T st w t.1 ctr δ t.2 hP hQ

theorem sibOf_inst_congr (i1 i2 : HasPrg) (Hs : Hashes) (T : CrtTables) (st : Statement)
    (s : Shared) (t : Pads st.params)
    (hP : @pubOf i1 Hs st s (deltaOf s.2.1) = @pubOf i2 Hs st s (deltaOf s.2.1))
    (hQ : ∀ c, @qcolsOf i1 st (@pubOf i2 Hs st s (deltaOf s.2.1)) (deltaOf s.2.1) c =
      @qcolsOf i2 st (@pubOf i2 Hs st s (deltaOf s.2.1)) (deltaOf s.2.1) c) :
    @sibOf i1 Hs T st s t = @sibOf i2 Hs T st s t := by
  simp only [sibOf, hP, hQ]

/-- **The hybrid after H4 reads the cipher only at the honest reads of its tape.** -/
theorem hyb3_ic_congr (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
    (b : Bytes 16 × Grind) (o : Hidden st.params)
    (h : ∀ k ∈ hRd E Hs st (b.1, b.2, o.1, o.2.1) (deltaOf b.2), E k = E' k) :
    @hyb3 (icPrg E) Hs T st w b o = @hyb3 (icPrg E') Hs T st w b o := by
  have hP := pubOf_ic_congr Hs st (b.1, b.2, o.1, o.2.1) (deltaOf b.2) h
  have hQ := fun c => (qcolsOf_ic_congr Hs st (b.1, b.2, o.1, o.2.1) (deltaOf b.2) h c).symm
  unfold hyb3 fillSib tapeOfHidden
  dsimp only
  rewrite [sibOf_inst_congr (icPrg E) (icPrg E') Hs T st _ _ hP hQ]
  exact proveIdeal_inst_congr (icPrg E) (icPrg E') Hs T st w _ hP hQ

/-- **The verifier's recomputation reads the cipher only at the reconstruction's reads** of the
proof's opening. -/
theorem vPre_ic_congr (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (h : ∀ k ∈ rdKeys E (ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs)) (⟨st.params, proof⟩ : Proof).opening
      (⟨st.params, proof⟩ : Proof).delta, E k = E' k) :
    @vPre (icPrg E) Hs T st proof = @vPre (icPrg E') Hs T st proof := by
  set pf : Proof := ⟨st.params, proof⟩ with hpf
  have hr := reconstruct_ic_congr h
  show @vPreP (icPrg E) Hs T st pf = @vPreP (icPrg E') Hs T st pf
  unfold vPreP
  rcases hl : @BAVC.reconstruct (icPrg E) (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta with _ | leaves
  · rw [← hr, hl]
  · rw [← hr, hl]
    have hc : @convertToVole (icPrg E) pf (ivOf Hs pf (st.mu1 Hs)) leaves =
        @convertToVole (icPrg E') pf (ivOf Hs pf (st.mu1 Hs)) leaves := by
      unfold convertToVole
      refine convertToVoleAt_ic_congr _ _ _ _ _ fun i hi j hj hjd hs => h _ ?_
      have := @leafKey_mem_rdKeys E (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta i j hi hj hjd
      rw [hl, Option.getD_some] at this
      exact this hs
    simp only [vPreOf, hc]

end Congr

/-! ## The chain of `zk_rom_h23` around H4, for any PRG -/

section Generic

variable [HasPrg] (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- **The hybrids before H4** (H1, grinding and programming, the programmed points recomputed from
the proof), for any PRG: the executable prover with the record `recH`, against hybrid H3 with the
simulator's `H₂³` table (`Dp`). -/
theorem zk_pre_h4 {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (Prover.prove (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1))
          c.2.1 c.1.2 c.2.2) -
      pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (fun c =>
        Dp Hb CrtGen.tables st D (hyb3 (recB Hb st w c.2.1 c.2.2) CrtGen.tables st w
          (c.1.1.2, c.1.2.2)
          (hiddenOut st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2.2)) c.1.1.1))
          c.1.2.2 (c.2.1, c.1.2.1, c.2.2))| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) := by
  obtain ⟨hl1, -, -, hl2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  have e0 : pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
      D (Prover.prove (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1))
        c.2.1 c.1.2 c.2.2) =
      pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (proveP (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w
          (preR Hb CrtGen.tables st w c.2.2) c.1.1) c.2.1 c.1.2 c.2.2) := by
    refine pr_congr fun c => ?_
    have hR : RunHyp (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w cs :=
      ⟨hzk, recH_wf hHb _ _ _, bavcComplete, fun rho => crtComplete _ _ _ _ rho _ hlab, hlab⟩
    rw [← proveP_prove _ CrtGen.tables st w hR c.1.1, prePrefix_recH]
  rw [e0]
  have h1 := joint2_h1 Hb CrtGen.tables st w D Q3 hQ3 hq3
  have h2 := joint2_prog Hb CrtGen.tables st w hHb hzk.q D
  have h3 := joint2_keys Hb st w hHb hzk hlab D
  have := abs_sub_le _ _ _ |>.trans (add_le_add h1 ((abs_sub_le _ _ _).trans (add_le_add h2 h3)))
  exact this.trans (le_of_eq (by ring))

/-- **The hybrids after H4** (the tape, H6, the simulator), for any PRG: hybrid H4 (the ideal hidden
part) with the simulator's `H₂³` table against the simulator. -/
theorem zk_post_h4 {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5, (Q5 o G3 G2 G5).card ≤ q5) :
    |pr ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) (fun c =>
        Dp Hb CrtGen.tables st D (hyb3 (recB Hb st w c.2.1 c.2.2.2) CrtGen.tables st w
          c.1.2 (hiddenIdeal (ba (deltaOf c.1.2.2)) c.1.1)) c.1.2.2 c.2) -
      pr (SimCoins st.params × Vis2 st.params) (fun c =>
        D (simulate st.params c.1) c.2.1
          (simTab Hb CrtGen.tables st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1) c.2.2.2)| ≤
      (q5 + 1) / 2 ^ 128 := by
  have h5 := joint2_tape Hb CrtGen.tables st w D
  have h6 := joint2_h6 Hb CrtGen.tables st w hlr hzk hHb D Q5 hQ5 hq5
  have h7 := joint2_sim Hb CrtGen.tables st w hzk D
  have := abs_sub_le _ _ _ |>.trans (add_le_add h5 ((abs_sub_le _ _ _).trans (add_le_add h6 h7)))
  exact this.trans (le_of_eq (by ring))

/-- **An ideal-tape proof's public fields**: if the hybrid after H4 returns a proof, its opening,
`Δ` and `iv_pre` are the tape's. -/
theorem hyb3_ok_fields (Hs : Hashes) (T : CrtTables) {cs : ByteArray → ByteArray → System GF128}
    (h : ZKHyp T st w cs) (b : Bytes 16 × Grind) (o : Hidden st.params) {proof : ByteArray}
    (hok : hyb3 Hs T st w b o = .ok proof) :
    (⟨st.params, proof⟩ : Proof).opening = openingOf (ba (deltaOf b.2)) o.1 o.2.1 ∧
      (⟨st.params, proof⟩ : Proof).delta = ba (deltaOf b.2) ∧
      (⟨st.params, proof⟩ : Proof).ivPre = ba b.1 := by
  unfold hyb3 at hok
  set t := fillSib Hs T st (tapeOfHidden b.1 b.2 o fun _ => fun _ => 0) with ht
  have ht1 : t.1 = (b.1, b.2, o.1, o.2.1) := rfl
  rw [show t = (t.1, t.2) from rfl, proveIdeal_eq_outOf T st w cs Hs h t.1 t.2] at hok
  unfold outOf at hok
  rw [ht1] at hok
  rcases hf : firstHit b.2 with _ | ⟨ctr, δ⟩
  · simp only [hf] at hok
    cases hok
  · simp only [hf, Except.ok.injEq] at hok
    subst hok
    have hd : deltaOf b.2 = δ := by unfold deltaOf; rw [hf]; rfl
    have hacc := firstHit_accepts hf
    have hoc : openCount (ba δ) ≤ 105 := by
      unfold accepts at hacc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc; exact hacc.2
    rw [hd]
    refine ⟨?_, ?_, ?_⟩
    · exact (fields_assemble st.params _).2.2.2.2.2.1.trans (fit_of_size (openingOf_size _ _ _ hoc))
    · exact (fields_assemble st.params _).2.2.2.2.2.2.1.trans (fit_of_size (size_ba _))
    · exact (fields_assemble st.params _).2.2.2.2.2.2.2.1.trans (fit_of_size (size_ba _))

end Generic

/-! ## H4 in the ideal-cipher model, with the honest recomputation's reads -/

section IC

variable (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **The distinguisher's view after the programmed points are recomputed** (hybrid H3), as a
function of the hidden part `o` and the cipher table `E`: the proof of the hybrid with `E`, the
tables `v` (`H₃`, `H₂³`, `H₅`) with `H₂³` programmed by the simulator at the points it recomputes
with `E`, and `E` itself. -/
noncomputable def viewIC (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      Cipher → Prop) (a : Bytes 16) (g : Grind) (v : Vis2 st.params) (o : Hidden st.params)
    (E : Cipher) : Prop :=
  @Dp (icPrg E) Hb T st (fun o G3 G2 G5 => D o G3 G2 G5 E)
    (@hyb3 (icPrg E) (recB Hb st w v.1 v.2.2) T st w (a, g) o) g v

/-- **The keys the view reads**: the distinguisher's (`QE`, at the view's proof and tables) and the
honest recomputation's (`hRd`: the reconstruction of the tape's opening, in the prover's public
part and in the simulator's recomputation of the grinding prefix). -/
noncomputable def viewKeys (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      Cipher → Finset Blk) (a : Bytes 16) (g : Grind) (v : Vis2 st.params) (o : Hidden st.params)
    (E : Cipher) : Finset Blk :=
  QE (@hyb3 (icPrg E) (recB Hb st w v.1 v.2.2) T st w (a, g) o) v.1
      (@simTab (icPrg E) Hb T st v.2.2 (@hyb3 (icPrg E) (recB Hb st w v.1 v.2.2) T st w (a, g) o) g
        v.2.1) v.2.2 E ∪
    hRd E (recB Hb st w v.1 v.2.2) st (a, g, o.1, o.2.1) (deltaOf g)

variable {Hb T st w}

lemma rec5_h4 (G5 : Tab5F) : (rec5 Hb G5).hash .h4 = Hb.hash .h4 :=
  ((Hb.agreeOff_withTable .h5 enc5 G5) .h4 (by decide)).symm

lemma rec5_mu1 (G5 : Tab5F) : st.mu1 (rec5 Hb G5) = st.mu1 Hb :=
  ((Hb.agreeOff_withTable .h5 enc5 G5).mu1 (by decide) (by decide) st).symm

/-- **The view reads the cipher only at `viewKeys`.** -/
theorem viewIC_congr {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp T st w cs)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    (a : Bytes 16) (g : Grind) (v : Vis2 st.params) (o : Hidden st.params) (E E' : Cipher)
    (hE : ∀ k ∈ viewKeys Hb T st w QE a g v o E, E k = E' k) :
    viewIC Hb T st w D a g v o E ↔ viewIC Hb T st w D a g v o E' := by
  obtain ⟨G3, G2, G5⟩ := v
  set R := recB Hb st w G3 G5 with hR
  have hrd : ∀ k ∈ hRd E R st (a, g, o.1, o.2.1) (deltaOf g), E k = E' k :=
    fun k hk => hE k (Finset.mem_union_right _ hk)
  have hout : @hyb3 (icPrg E) R T st w (a, g) o = @hyb3 (icPrg E') R T st w (a, g) o :=
    hyb3_ic_congr R T st w (a, g) o hrd
  have htab : @simTab (icPrg E) Hb T st G5 (@hyb3 (icPrg E) R T st w (a, g) o) g G2 =
      @simTab (icPrg E') Hb T st G5 (@hyb3 (icPrg E) R T st w (a, g) o) g G2 := by
    unfold simTab outPre
    rcases ho : @hyb3 (icPrg E) R T st w (a, g) o with e | proof
    · rfl
    · obtain ⟨hO, hD, hI⟩ := @hyb3_ok_fields (icPrg E) st w R T cs hzk (a, g) o proof ho
      have hv : @vPre (icPrg E) (rec5 Hb G5) T st proof =
          @vPre (icPrg E') (rec5 Hb G5) T st proof := by
        refine vPre_ic_congr (rec5 Hb G5) T st proof fun k hk => hrd k ?_
        rw [ivOf, hO, hD, hI, rec5_h4, rec5_mu1] at hk
        rw [hRd, hR, recB, recH_hash_ne (by decide) (by decide) (by decide), recH_mu1]
        exact hk
      simp only [hv]
  show D (@hyb3 (icPrg E) R T st w (a, g) o) G3
      (@simTab (icPrg E) Hb T st G5 (@hyb3 (icPrg E) R T st w (a, g) o) g G2) G5 E ↔
    D (@hyb3 (icPrg E') R T st w (a, g) o) G3
      (@simTab (icPrg E') Hb T st G5 (@hyb3 (icPrg E') R T st w (a, g) o) g G2) G5 E'
  rw [← hout, ← htab]
  exact hQE _ _ _ _ _ _ fun k hk => hE k (Finset.mem_union_left _ hk)

theorem viewKeys_card
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) (a : Bytes 16) (g : Grind)
    (v : Vis2 st.params) (o : Hidden st.params) (E : Cipher) :
    (viewKeys Hb T st w QE a g v o E).card ≤ qE + 4607 :=
  (card_union_le _ _).trans (add_le_add (hqE _ _ _ _ _) (rdKeys_card _ _ _ _))

variable (Hb T st w)

/-- **H4 in the ideal-cipher model, with the cipher in the whole prover and verifier**: the hidden
part computed with `E` from a uniform root seed, against the ideal hidden part, with `E` uniform
and seen by the distinguisher, who reads it at `q_E` keys; the honest recomputation (the prover's
public part, the simulator's prefix) reads it at the reconstruction's `≤ 4607` keys, which count
as reads (`hide_rom_query`). -/
theorem joint3_h4 (hp : SmallParams st.params) {cs : ByteArray → ByteArray → System GF128}
    (hzk : ZKHyp T st w cs)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) :
    |pr ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) × Cipher)
        (fun c => @Dp (icPrg c.2) Hb T st (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
          (@hyb3 (icPrg c.2) (recB Hb st w c.1.2.1 c.1.2.2) T st w (c.1.1.1.2, c.1.1.2.2)
            (@hiddenOut (icPrg c.2) st.params (ivOfPre Hb st c.1.1.1.2) (ba (deltaOf c.1.1.2.2))
              c.1.1.1.1))
          c.1.1.2.2 (c.1.2.1, c.1.1.2.1, c.1.2.2)) -
      pr (((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) × Cipher) (fun c =>
        @Dp (icPrg c.2) Hb T st (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
          (@hyb3 (icPrg c.2) (recB Hb st w c.1.2.1 c.1.2.2.2) T st w c.1.1.2
            (hiddenIdeal (ba (deltaOf c.1.1.2.2)) c.1.1.1)) c.1.1.2.2 c.1.2)| ≤
      221 * (4607 + (qE + 4607)) / 2 ^ 128 := by
  let E2 : ((Bytes 16 × Grind) × Vis2 st.params) × (Blk × Cipher) ≃
      (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) × Cipher :=
    { toFun := fun c => ((((c.2.1, c.1.1.1), (c.1.2.2.1, c.1.1.2)), (c.1.2.1, c.1.2.2.2)), c.2.2)
      invFun := fun c => (((c.1.1.1.2, c.1.1.2.2), (c.1.2.1, c.1.1.2.1, c.1.2.2)), (c.1.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : ((Bytes 16 × Grind) × Vis2 st.params) × (Hidden st.params × Cipher) ≃
      ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) × Cipher :=
    { toFun := fun c => (((c.2.1, c.1.1), c.1.2), c.2.2)
      invFun := fun c => ((c.1.1.2, c.1.2), (c.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E2, ← pr_equiv E3]
  refine abs_pr_prod_sub_le _ _ fun x => ?_
  obtain ⟨⟨a, g⟩, v⟩ := x
  have h := hide_rom_query st.params (ivOfPre Hb st a) (ba (deltaOf g)) hp
    (viewIC Hb T st w D a g v) (viewKeys Hb T st w QE a g v)
    (fun o E E' hk => viewIC_congr hzk D QE hQE a g v o E E' hk)
    (viewKeys_card QE hqE a g v)
  unfold IC.realPr IC.idealPr at h
  have e : pr (Blk × Cipher) (fun p => viewIC Hb T st w D a g v
        (hiddenOutE p.2 st.params (ivOfPre Hb st a) (ba (deltaOf g)) p.1) p.2) =
      pr (Blk × Cipher) (fun p => viewIC Hb T st w D a g v
        (@hiddenOut (icPrg p.2) st.params (ivOfPre Hb st a) (ba (deltaOf g)) p.1) p.2) :=
    pr_congr fun p => by rw [hiddenOut_ic]
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end IC

/-! ## The end-to-end statement -/

section Main

variable (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- Averaging a hop over the cipher table. -/
lemma abs_pr_avgE {α α' : Type*} [Fintype α] [Fintype α'] {ε : ℝ} (P : α → Cipher → Prop)
    (Q : α' → Cipher → Prop) (h : ∀ E, |pr α (fun a => P a E) - pr α' (fun a => Q a E)| ≤ ε) :
    |pr (α × Cipher) (fun c => P c.1 c.2) - pr (α' × Cipher) (fun c => Q c.1 c.2)| ≤ ε :=
  abs_pr_prod_sub_le' (fun c => P c.1 c.2) (fun c => Q c.1 c.2) h

/-- **Zero knowledge in the random-oracle and ideal-cipher model with `H₂³` visible** (label-row
layout, faest-arch-opt's tables, one statement and witness).

The hash record is `recH Hb … G3 G2 G5`: the base record `Hb` with `H₃` a uniform table `G3` on
the seed inputs, `H₂³` a uniform table `G2` on every grinding point `pre ‖ ctr ‖ 11`, and `H₅` a
uniform table `G5` on every `37`-byte input. The cipher of the whole BAVC and VOLE expansion (the
prover's commitment, its public part, the verifier's reconstruction) is a uniform table `E`: the
real world is the **executable prover** `Prover.prove` run with the ideal-cipher PRG `icPrg E` in
place of AES (`icPrg_aes`: at `E = aesTable` it is the executable prover). The tables and `E` are
independent.

The simulator outputs `simulate` (from its coins only) and the `H₂³` table `simTab`: `G2`
programmed at the grinding points of the prefix it recomputes from its own proof with the
verifier's recomputation `vPre` run with `E` (and the `H₅` table).

A distinguisher `D` sees the output, the three tables and `E`, reads `H₃`, `H₅` and `E`
adaptively at `q₃`, `q₅` and `q_E` keys (`Q3`, `Q5`, `QE`: each condition says that `D` does not
depend on that table outside them, with the others fixed), and reads `H₂³` freely. Its advantage
is at most

    q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸

(H1; grinding and programming, exact; the programmed points recomputed from the proof, which
agree with the prover's unless no grinding answer is accepted or `Δ' = 0`, for every cipher;
H4 in the ideal-cipher model, where the honest recomputation of the opened part of the tree, by
the prover and by the simulator, reads `E` at the at most `4607` reconstructed nodes, counted as
reads (`rdKeys`); H6). -/
theorem zk_rom_ic_h23 {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 E, (∀ k ∈ Q3 o G3 G2 G5 E, G3 k = G3' k) →
      (D o G3 G2 G5 E ↔ D o G3' G2 G5 E))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 E, (Q3 o G3 G2 G5 E).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' E, (∀ k ∈ Q5 o G3 G2 G5 E, G5 k = G5' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5' E))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 E, (Q5 o G3 G2 G5 E).card ≤ q5)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@Prover.prove (icPrg c.2) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins st.params × Vis2 st.params) × Cipher) (fun c =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
            c.1.2.2.1) c.1.2.2.2 c.2)| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) + 221 * (4607 + (qE + 4607)) / 2 ^ 128 +
        (q5 + 1) / 2 ^ 128 := by
  have hA := abs_pr_avgE
    (fun (c : (Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (E : Cipher) =>
      D (@Prover.prove (icPrg E) (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1)
        st.params.witnessBytes) c.2.1 c.1.2 c.2.2 E)
    (fun (c : ((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (E : Cipher) =>
      @Dp (icPrg E) Hb CrtGen.tables st (fun o G3 G2 G5 => D o G3 G2 G5 E)
        (@hyb3 (icPrg E) (recB Hb st w c.2.1 c.2.2) CrtGen.tables st w (c.1.1.2, c.1.2.2)
          (@hiddenOut (icPrg E) st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2.2)) c.1.1.1))
        c.1.2.2 (c.2.1, c.1.2.1, c.2.2))
    (fun E => @zk_pre_h4 (icPrg E) Hb st w cs hlr hzk hHb (fun o G3 G2 G5 => D o G3 G2 G5 E)
      (fun o G3 G2 G5 => Q3 o G3 G2 G5 E) (fun o G3 G3' G2 G5 => hQ3 o G3 G3' G2 G5 E) q3
      (fun o G3 G2 G5 => hq3 o G3 G2 G5 E))
  have hB := joint3_h4 Hb CrtGen.tables st w hp hzk D QE hQE hqE
  have hC := abs_pr_avgE
    (fun (c : (Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) (E : Cipher) =>
      @Dp (icPrg E) Hb CrtGen.tables st (fun o G3 G2 G5 => D o G3 G2 G5 E)
        (@hyb3 (icPrg E) (recB Hb st w c.2.1 c.2.2.2) CrtGen.tables st w c.1.2
          (hiddenIdeal (ba (deltaOf c.1.2.2)) c.1.1)) c.1.2.2 c.2)
    (fun (c : SimCoins st.params × Vis2 st.params) (E : Cipher) =>
      D (simulate st.params c.1) c.2.1
        (@simTab (icPrg E) Hb CrtGen.tables st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1)
        c.2.2.2 E)
    (fun E => @zk_post_h4 (icPrg E) Hb st w cs hlr hzk hHb (fun o G3 G2 G5 => D o G3 G2 G5 E)
      (fun o G3 G2 G5 => Q5 o G3 G2 G5 E) (fun o G3 G2 G5 G5' => hQ5 o G3 G2 G5 G5' E) q5
      (fun o G3 G2 G5 => hq5 o G3 G2 G5 E))
  refine (abs_sub_le _ _ _).trans ((add_le_add hA ((abs_sub_le _ _ _).trans
    (add_le_add hB hC))).trans (le_of_eq (by ring)))

end Main

end VoleMole.ZK.Sim
