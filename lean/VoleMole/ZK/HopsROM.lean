import VoleMole.ZK.Exec
import VoleMole.Verifier.Bridge.CtrInput

/-!
# The random-oracle hops of `ZK/Hops.lean`, with the oracle as a uniform table

The hop hypotheses `H3Hyp` and `GrindHyp` (`ZK/Hops.lean`) are stated for a fixed hash record, as
every statement against all distinguishers in `Privacy/Basic.lean`. Here the hashed domain is a
random oracle: on the finite set of inputs the hop reads, its answers are a uniform table `G`
(`Hashes.withTable`; the lazy random oracle of `ROM/Basic.lean`, restricted to finitely many keys,
is such a table: `ROM/DomainSep.lean`'s `restrictQueries` and complete tables). Averaged over the
table, both hops are proved, with the exact bounds:

* **H1** (`h3_rom`): `H3Hyp` holds with `ε = 0`: `H₃`'s answer at the seed input of any `rho` is a
  uniform 32-byte string. Against a distinguisher that also reads the `H₃` table at `q` inputs of
  its choice (`h3_rom_query`, from `Privacy.abs_pr_hidden_one_le`): `ε_rho ≤ q·2⁻¹²⁸`, the
  probability that one of them is the seed input, which contains the uniform secret `rho`. This
  is the `Q₃·2⁻¹²⁸` part of zk.md's `ε_rho` (the other part, two proofs sharing `rho`, concerns
  several proofs).
* **Grinding** (`grind_rom`): `GrindHyp` holds with `ε = 0`: the `H₂³` answers at the `2³²` distinct
  grinding points of any prefix (a function of the coins, not of the `H₂³` table) are uniform and
  independent of the coins. **Programming is perfect** (`grind_rom_program`): a distinguisher that
  reads the `H₂³` table sees the same law when the answers are sampled first and the table is
  programmed with them at the grinding points, as `Sim.simulateRO` does. zk.md's `ε_prog` concerns
  queries made before the proof's `chal2` is fixed, which a single proof does not have.

* **H6** (`lab_rom`): with `H₅` a uniform table on the sibling inputs (`sibInput`: the gate inputs
  at the labels `L^{1−γ_e}_e`, distinct across gates since they contain the gate index), the hop
  of `LabHyp` (sibling answers recomputed from `H₅` against uniform ones) is identical until a
  sibling input is read: for every run that reads the table only on a set `Q`, the gap is at most
  `Pr[some sibling input ∈ Q]`.

The remaining modelling step is that the hash record's domain is a random oracle (SHAKE128 as a
random oracle, with L0's domain separation: `ROM/DomainSep.lean`, `ROM/SingleOracle.lean`). The
side conditions are proved in `ZK/HopsRead.lean` and `ZK/HopsH6.lean`: the prover's grinding
prefix does not read `H₂³` (`realPre_pendAt_congr`; `grind_rom_prover`, `grind_rom_program_prover`
are the grinding hops for the prover's own prefix), the ideal-tape prover reads `H₅` only at the
active labels `L^{γ_e}_e` (`proveIdeal_h5_congr`), and the H6 gap is `≤ (q₅ + 1)·2⁻¹²⁸` against a
distinguisher that reads the table at `q₅` keys (`lab_rom_query`, `lab_rom_hyp`).
-/

open Finset

namespace VoleMole.ZK.Sim

-- The statements hold for any CTR PRG (`HasPrg`, `Verifier/Prg.lean`), AES included.
variable [VoleMole.Verifier.HasPrg]
set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy

/-- **The hash record with domain `k` answered by the table `G`** at the inputs `enc a` (and by `Hs`
elsewhere): a table indexed by the keys `a`, consistent on inputs with several keys. -/
noncomputable def _root_.VoleMole.Verifier.Hashes.withTable (Hs : Hashes) (k : Kind) {K : Type}
    (enc : K → ByteArray) (G : K → Bytes k.outLen) : Hashes := by
  classical
  exact ⟨fun k' x => if k' = k then (if h : ∃ a, enc a = x then ba (G h.choose) else Hs.hash k x)
    else Hs.hash k' x⟩

/-- The key the table answers the input `enc a` with (`a` itself for an injective encoding). -/
noncomputable def keyOf {K : Type} (enc : K → ByteArray) (a : K) : K :=
  (⟨a, rfl⟩ : ∃ b, enc b = enc a).choose

lemma enc_keyOf {K : Type} (enc : K → ByteArray) (a : K) : enc (keyOf enc a) = enc a :=
  (⟨a, rfl⟩ : ∃ b, enc b = enc a).choose_spec

lemma keyOf_eq {K : Type} {enc : K → ByteArray} (h : Function.Injective enc) (a : K) :
    keyOf enc a = a :=
  h (enc_keyOf enc a)

lemma _root_.VoleMole.Verifier.Hashes.withTable_enc (Hs : Hashes) (k : Kind) {K : Type}
    (enc : K → ByteArray) (G : K → Bytes k.outLen) (a : K) :
    (Hs.withTable k enc G).hash k (enc a) = ba (G (keyOf enc a)) := by
  simp only [Hashes.withTable, ite_true, dite_eq_left_of_eq_true (eq_true (⟨a, rfl⟩ : ∃ b, enc b = enc a))]
  rfl

lemma ba_injective {n : ℕ} : Function.Injective (ba (n := n)) := by
  intro b b' h
  funext i
  have := congrArg (fun x : ByteArray => x.get! i) h
  simpa only [get!_ba _ i.isLt] using this

lemma push_injective (v : UInt8) : Function.Injective fun b : ByteArray => b.push v := by
  intro b b' h
  exact ByteArray.ext (Array.push_inj_left.1 (congrArg ByteArray.data h))

/-- A uniform table read at one key is a uniform answer. -/
lemma close_eval {K R : Type*} [Fintype K] [DecidableEq K] [Fintype R] [Nonempty R] (x : K) :
    Close 0 (fun g : K → R => g x) (id : R → R) := by
  have h := close_restrict (ι := Unit) (R := R) (x := fun _ => x) (fun _ _ _ => rfl)
  have h2 := close_equiv (Equiv.funUnique Unit R).symm (id : (Unit → R) → (Unit → R))
  exact ((h.map fun u => u ()).trans
    ((h2.symm.map fun u => u ()).congr (fun _ => rfl) fun _ => rfl)).mono (by norm_num)

/-! ## H1 -/

section H1

variable (mu1 wPrefix : ByteArray)

/-- The seed input of `rho`: `w_pre ‖ mu ‖ rho ‖ 3`. -/
def seedInput (ρ : Bytes 16) : ByteArray := (wPrefix ++ mu1 ++ ba ρ).push 3

lemma seedInput_injective : Function.Injective (seedInput mu1 wPrefix) := fun _ _ h =>
  ba_injective ((ByteArray.append_right_inj _).1 (push_injective 3 h))

/-- `H₃`'s 32 answer bytes as the root seed and `iv_pre`. -/
def splitSeed (u : Bytes 32) : Bytes 16 × Bytes 16 :=
  (blk 16 ((ba u).extract 0 16), blk 16 ((ba u).extract 16 32))

lemma splitSeed_injective : Function.Injective splitSeed := by
  intro u u' h
  funext i
  simp only [splitSeed, Prod.mk.injEq] at h
  by_cases hi : i.val < 16
  · have := congrFun h.1 ⟨i, hi⟩
    simp only [get_blk] at this
    rwa [get!_extract0 _ hi (by simp), get!_extract0 _ hi (by simp), get!_ba _ i.isLt,
      get!_ba _ i.isLt] at this
  · have := congrFun h.2 ⟨i.val - 16, by omega⟩
    simp only [get_blk] at this
    rwa [get!_extract _ (by omega) (by simp), get!_extract _ (by omega) (by simp),
      show 16 + (i.val - 16) = i.val by omega, get!_ba _ i.isLt, get!_ba _ i.isLt] at this

/-- The inverse of `splitSeed`. -/
def joinSeed (x : Bytes 16 × Bytes 16) : Bytes 32 :=
  fun i => if h : i.val < 16 then x.1 ⟨i, h⟩ else x.2 ⟨i.val - 16, by omega⟩

lemma splitSeed_joinSeed (x : Bytes 16 × Bytes 16) : splitSeed (joinSeed x) = x := by
  obtain ⟨a, b⟩ := x
  simp only [splitSeed, Prod.mk.injEq]
  constructor
  · funext i
    rw [get_blk, get!_extract0 _ i.isLt (by simp), get!_ba _ (by omega)]
    simp [joinSeed, i.isLt]
  · funext i
    rw [get_blk, get!_extract _ (by omega) (by simp), get!_ba _ (by omega)]
    simp [joinSeed]

/-- `splitSeed` as a bijection. -/
def splitEquiv : Bytes 32 ≃ Bytes 16 × Bytes 16 where
  toFun := splitSeed
  invFun := joinSeed
  left_inv _ := splitSeed_injective (splitSeed_joinSeed _)
  right_inv := splitSeed_joinSeed

/-- With `H₃` answered by the table `G` on the seed inputs, the seed and `iv_pre` of `rho` are
`G`'s answer at `rho`'s seed input. -/
lemma h3Seed_withTable (Hs : Hashes) (G : Bytes 16 → Bytes 32) (ρ : Bytes 16) :
    h3Seed (Hs.withTable .h3 (seedInput mu1 wPrefix) G) mu1 wPrefix (ba ρ) = splitSeed (G ρ) := by
  simp only [h3Seed, splitSeed]
  have h := Hashes.withTable_enc Hs .h3 (seedInput mu1 wPrefix) G ρ
  rw [keyOf_eq (seedInput_injective mu1 wPrefix)] at h
  rw [show (wPrefix ++ mu1 ++ ba ρ).push 3 = seedInput mu1 wPrefix ρ from rfl, h]
  rfl

/-- **H1 in the ROM**: with `H₃` a uniform table on the seed inputs, the hypothesis `H3Hyp` holds
with `ε = 0` (averaged over the table). -/
theorem h3_rom (Hs : Hashes) :
    Close 0 (fun p : Bytes 16 × (Bytes 16 → Bytes 32) =>
        h3Seed (Hs.withTable .h3 (seedInput mu1 wPrefix) p.2) mu1 wPrefix (ba p.1))
      (id : Bytes 16 × Bytes 16 → _) := by
  have e1 : Close 0 (fun p : Bytes 16 × (Bytes 16 → Bytes 32) => splitSeed (p.2 p.1))
      (fun p : Bytes 16 × Bytes 32 => splitSeed p.2) :=
    Close.prod_right (X := fun ρ (G : Bytes 16 → Bytes 32) => splitSeed (G ρ))
      (Y := fun _ (u : Bytes 32) => splitSeed u) fun ρ => (close_eval ρ).map splitSeed
  have e2 : Close 0 (fun p : Bytes 16 × Bytes 32 => splitSeed p.2) splitSeed :=
    close_prod_snd (X := splitSeed)
  have e3 : Close 0 (fun u : Bytes 32 => splitEquiv u) (id : Bytes 16 × Bytes 16 → _) :=
    close_equiv splitEquiv id
  exact ((e1.trans e2).trans (e3.congr (fun _ => rfl) fun _ => rfl)).mono (by norm_num) |>.congr
    (fun p => h3Seed_withTable mu1 wPrefix Hs p.2 p.1) fun _ => rfl

/-- **H1 in the ROM, against a distinguisher that reads the `H₃` table**: if `A` reads the table
(at the seed inputs) only at the (at most `q`) keys `Q`, its advantage between the real seed and
`iv_pre` (`H₃`'s answer at the seed input of a uniform `rho`) and an independent uniform answer is
`≤ q·2⁻¹²⁸`. -/
theorem h3_rom_query (Hs : Hashes) (A : Bytes 16 × Bytes 16 → (Bytes 16 → Bytes 32) → Prop)
    (Q : Bytes 16 × Bytes 16 → (Bytes 16 → Bytes 32) → Finset (Bytes 16))
    (hQ : ∀ v G G', (∀ k ∈ Q v G, G k = G' k) → (A v G ↔ A v G')) {q : ℕ}
    (hq : ∀ v G, (Q v G).card ≤ q) :
    |pr (Bytes 16 × (Bytes 16 → Bytes 32)) (fun p =>
        A (h3Seed (Hs.withTable .h3 (seedInput mu1 wPrefix) p.2) mu1 wPrefix (ba p.1)) p.2) -
      pr (Bytes 16 × ((Bytes 16 → Bytes 32) × Bytes 32))
        (fun p => A (splitSeed p.2.2) p.2.1)| ≤ q / 2 ^ 128 := by
  have h := abs_pr_hidden_one_le (C := Bytes 16) (x := id) Function.injective_id
    (fun u G => A (splitSeed u) G) (fun u G => Q (splitSeed u) G) (fun u G G' h => hQ _ G G' h)
    (fun u G => hq _ G)
  rw [Prob.card_bytes] at h
  simp only [h3Seed_withTable]
  exact h.trans (le_of_eq (by norm_num))

end H1

/-! ## Grinding -/

section Grind

/-- The grinding point of counter `c`: `pre ‖ c ‖ 11`. -/
def grindInput (pre : ByteArray) (c : Fin nGrind) : ByteArray :=
  (AES.pushLE32 pre c.val.toUInt32).push 11

lemma grindInput_injective (pre : ByteArray) : Function.Injective (grindInput pre) := by
  intro c c' h
  have h1 := congrArg (fun b => AES.getLE32 b pre.size) (push_injective 11 h)
  simp only [getLE32_pushLE32] at h1
  have h2 := congrArg UInt32.toNat h1
  rw [toNat_toUInt32 (by simpa [nGrind] using c.isLt),
    toNat_toUInt32 (by simpa [nGrind] using c'.isLt)] at h2
  exact Fin.ext h2

instance : NeZero nGrind := ⟨by simp [nGrind]⟩

variable (pre : Bytes 16 × Bytes 16 → ByteArray)

/-- The keys of the `H₂³` table: the coins and a counter, encoded as the grinding point. -/
abbrev GKey := (Bytes 16 × Bytes 16) × Fin nGrind

/-- The grinding point of a key. -/
def gEnc (p : GKey) : ByteArray := grindInput (pre p.1) p.2

/-- The table key of the grinding point of counter `c` for the coins `x`. -/
noncomputable def grindKey (x : Bytes 16 × Bytes 16) (c : Fin nGrind) : GKey :=
  keyOf (gEnc pre) (x, c)

lemma grindKey_injective (x : Bytes 16 × Bytes 16) : Function.Injective (grindKey pre x) :=
  fun c c' h => grindInput_injective (pre x) (by
    have e := congrArg (gEnc pre) h
    rwa [grindKey, grindKey, enc_keyOf (gEnc pre), enc_keyOf (gEnc pre)] at e)

/-- With `H₂³` answered by the table `G` at the grinding points, the grinding answers are `G`'s
answers at the grinding points' keys. -/
lemma realGrind_withTable (Hs : Hashes) (G : GKey → Bytes 16) (x : Bytes 16 × Bytes 16) :
    realGrind (Hs.withTable .h23 (gEnc pre) G) (pre x) = G ∘ grindKey pre x := by
  funext c
  simp only [realGrind, Function.comp_apply]
  rw [show (AES.pushLE32 (pre x) c.val.toUInt32).push 11 = gEnc pre (x, c) from rfl,
    Hashes.withTable_enc Hs .h23 (gEnc pre) G (x, c)]
  exact blk_ba (n := 16) _

/-- **The grinding hop in the ROM**: with `H₂³` a uniform table on the grinding points, the
hypothesis `GrindHyp` holds with `ε = 0` (averaged over the table), for any prefix that is a
function of the coins. -/
theorem grind_rom (Hs : Hashes) :
    Close 0 (fun p : (Bytes 16 × Bytes 16) × (GKey → Bytes 16) =>
        (p.1.1, p.1.2, realGrind (Hs.withTable .h23 (gEnc pre) p.2) (pre p.1)))
      (id : Bytes 16 × Bytes 16 × Grind → _) := by
  -- (Stated pointwise in `D`: elaborating the `Close` combinators against these table types
  -- exhausts the recursion depth.)
  have e0 : ∀ x : Bytes 16 × Bytes 16, Close 0 (fun G : GKey → Bytes 16 =>
      (x.1, x.2, G ∘ grindKey pre x)) (fun g : Grind => (x.1, x.2, g)) := fun x D =>
    close_restrict (grindKey_injective pre x) (fun g => D (x.1, x.2, g))
  have e1 : Close 0 (fun p : (Bytes 16 × Bytes 16) × (GKey → Bytes 16) =>
      (p.1.1, p.1.2, p.2 ∘ grindKey pre p.1))
      (fun p : (Bytes 16 × Bytes 16) × Grind => (p.1.1, p.1.2, p.2)) := fun D =>
    abs_pr_prod_sub_le _ _ fun x => e0 x D
  have e2 : Close 0 (fun p : (Bytes 16 × Bytes 16) × Grind => (p.1.1, p.1.2, p.2))
      (id : Bytes 16 × Bytes 16 × Grind → _) := fun D =>
    close_equiv (Equiv.prodAssoc _ _ _) id D
  have hF : (fun p : (Bytes 16 × Bytes 16) × (GKey → Bytes 16) =>
      (p.1.1, p.1.2, realGrind (Hs.withTable .h23 (gEnc pre) p.2) (pre p.1))) =
      fun p => (p.1.1, p.1.2, p.2 ∘ grindKey pre p.1) :=
    funext fun p => by rw [realGrind_withTable]
  rw [hF]
  intro D
  have h1 := e1 D
  have h2 := e2 D
  have := abs_sub_le (pr ((Bytes 16 × Bytes 16) × (GKey → Bytes 16)) fun p =>
      D (p.1.1, p.1.2, p.2 ∘ grindKey pre p.1))
    (pr ((Bytes 16 × Bytes 16) × Grind) fun p => D (p.1.1, p.1.2, p.2))
    (pr (Bytes 16 × Bytes 16 × Grind) fun p => D (id p))
  linarith

/-- **Programming `H₂³` at the grinding points is perfect**: for any distinguisher `A` that reads
the coins, the grinding answers and the whole `H₂³` table, the real run (the answers read off a
uniform table) and the programmed one (uniform answers, the table programmed with them at the
grinding points, as `Sim.simulateRO` does) have the same law. -/
theorem grind_rom_program (Hs : Hashes)
    (A : Bytes 16 × Bytes 16 → Grind → (GKey → Bytes 16) → Prop) :
    pr ((Bytes 16 × Bytes 16) × (GKey → Bytes 16)) (fun p =>
        A p.1 (realGrind (Hs.withTable .h23 (gEnc pre) p.2) (pre p.1)) p.2) =
      pr ((Bytes 16 × Bytes 16) × ((GKey → Bytes 16) × Grind))
        (fun p => A p.1 p.2.2 (programAt (grindKey pre p.1) p.2.2 p.2.1)) := by
  simp only [realGrind_withTable]
  exact pr_program_eq (grindKey_injective pre) A

end Grind

/-! ## H6 -/

section H6

variable (Hs : Hashes) (T : CrtTables) (st : Statement)

lemma _root_.VoleMole.Verifier.Hashes.withTable_ne (k k' : Kind) (h : k' ≠ k) {K : Type}
    (enc : K → ByteArray) (G : K → Bytes k.outLen) (x : ByteArray) :
    (Hs.withTable k enc G).hash k' x = Hs.hash k' x := by
  simp only [Hashes.withTable, h, ite_false]

/-- The public values do not read `H₅`. -/
lemma pubOf_withTable_h5 {K : Type} (enc : K → ByteArray) (G : K → Bytes 4) (s : Shared)
    (d : Bytes 16) : pubOf (Hs.withTable .h5 enc G) st s d = pubOf Hs st s d := by
  have h : ∀ k : Kind, k ≠ .h5 → (Hs.withTable .h5 enc G).hash k = Hs.hash k := fun k hk =>
    funext (Hashes.withTable_ne Hs .h5 k hk enc G)
  simp only [pubOf, Statement.mu1, mu, h .h1 (by decide), h .h4 (by decide), h .mu (by decide),
    h .muDelayed (by decide)]

/-- **The sibling input of gate `e`** of a tape (`L^{1−γ_e}_e`, with `iv` and `e`): the `H₅` input
whose answer `sibOf` reads. -/
def sibInput (s : Shared) (t : Pads st.params) (e : Fin 312) : ByteArray :=
  let p := st.params
  let delta := deltaOf s.2.1
  let P := pubOf Hs st s delta
  let us := usOf p t
  let uu := us[0]!
  let dbit := BAVC.deltaBit (ba delta)
  let cols := tagCols dbit (qcolsOf st P delta (correctionsOf p us)) uu
  let uPre : W128 := ⟨wordAt uu p.labelRowOffset, wordAt uu (p.labelRowOffset + 64)⟩
  (if wbit (gammaOf T dbit) e then Prover.gateInputsOff p T P.iv cols W128.zero
    else Prover.gateInputsOff p T P.iv cols uPre).getD e .empty

/-- With `H₅` answered by a table, the sibling answers are its answers at the sibling inputs. -/
lemma sibOf_withTable {K : Type} (enc : K → ByteArray) (G : K → Bytes 4) (s : Shared)
    (t : Pads st.params) :
    sibOf (Hs.withTable .h5 enc G) T st s t =
      fun e => blk 4 ((Hs.withTable .h5 enc G).hash .h5 (sibInput Hs T st s t e)) := by
  funext e
  rw [sibOf_eq, pubOf_withTable_h5]
  unfold sibOfAt sibInput
  dsimp only
  rw [sibAnswers, getElem!_range_map _ _ e.isLt]

/-- The gate index sits in the 4 bytes after `iv` of a gate input. -/
lemma getLE32_gateInput (p : Params) (iv : ByteArray) (cols : Array (Array UInt64)) (off : W128)
    (e : Fin 312) :
    AES.getLE32 ((Prover.gateInputsOff p T iv cols off).getD e .empty) iv.size = e.val.toUInt32 := by
  have he : e.val < p.nMult := e.isLt
  simp only [Prover.gateInputsOff, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range he, Option.map_some, Option.getD_some]
  generalize ((W128.rowMul _ 120 _).xor off).toBytes = y
  have hs := size_pushLE32 iv e.val.toUInt32
  have hj : ∀ j < 4, ((AES.pushLE32 iv e.val.toUInt32 ++ y).push 5).get! (iv.size + j) =
      (AES.pushLE32 iv e.val.toUInt32).get! (iv.size + j) := fun j hj => by
    rw [get!_push, ite_eq_left_iff.2 fun h => absurd (by rw [ByteArray.size_append]; omega) h,
      get!_append, ite_eq_left_iff.2 fun h => absurd (by omega) h]
  have e' := getLE32_pushLE32 iv e.val.toUInt32
  simp only [AES.getLE32] at e' ⊢
  have h0 := hj 0 (by omega)
  rw [Nat.add_zero] at h0
  rw [h0, hj 1 (by omega), hj 2 (by omega), hj 3 (by omega)]
  exact e'

lemma getLE32_sibInput (s : Shared) (t : Pads st.params) (e : Fin 312) :
    AES.getLE32 (sibInput Hs T st s t e) (pubOf Hs st s (deltaOf s.2.1)).iv.size = e.val.toUInt32 := by
  unfold sibInput
  dsimp only
  split <;> exact getLE32_gateInput T _ _ _ _ e

/-- The keys of the `H₅` table: the tape (without its sibling answers) and a gate, encoded as the
gate's sibling input. -/
abbrev SKey (p : Params) := (Shared × PadsU p) × Fin 312

/-- (The keys contain functions; equality is decided classically, for the table's `Fintype`.) -/
noncomputable instance (p : Params) : DecidableEq (SKey p) := Classical.decEq _

/-- The sibling input of a key. -/
def sEnc (x : SKey st.params) : ByteArray :=
  sibInput Hs T st x.1.1 (withSib x.1.2 fun _ => fun _ => 0) x.2

/-- The table key of the sibling input of gate `e` of the tape `c`. -/
noncomputable def sibKey (c : Shared × PadsU st.params) (e : Fin 312) : SKey st.params :=
  keyOf (sEnc Hs T st) (c, e)

lemma sibKey_injective (c : Shared × PadsU st.params) : Function.Injective (sibKey Hs T st c) := by
  intro e e' h
  have h1 := congrArg (sEnc Hs T st) h
  rw [sibKey, sibKey, enc_keyOf (sEnc Hs T st), enc_keyOf (sEnc Hs T st)] at h1
  have h2 := congrArg (fun b => AES.getLE32 b (pubOf Hs st c.1 (deltaOf c.1.2.1)).iv.size) h1
  simp only [sEnc, getLE32_sibInput] at h2
  have h3 := congrArg UInt32.toNat h2
  rw [toNat_toUInt32 (by have := e.isLt; omega), toNat_toUInt32 (by have := e'.isLt; omega)] at h3
  exact Fin.ext h3

/-- With `H₅` a table on the sibling inputs, the tape with its sibling answers recomputed is the
tape with the table's answers at the sibling keys. -/
lemma fillSib_withTable (G : SKey st.params → Bytes 4) (c : Shared × PadsU st.params) (z : Sib) :
    fillSib (Hs.withTable .h5 (sEnc Hs T st) G) T st (c.1, withSib c.2 z) =
      (c.1, withSib c.2 (G ∘ sibKey Hs T st c)) := by
  have e1 : fillSib (Hs.withTable .h5 (sEnc Hs T st) G) T st (c.1, withSib c.2 z) =
      (c.1, withSib c.2 (sibOf (Hs.withTable .h5 (sEnc Hs T st) G) T st c.1 (withSib c.2 z))) := rfl
  rw [e1, sibOf_withSib' _ T st c.1 c.2 z fun _ => fun _ => 0, sibOf_withTable]
  congr 2
  funext e
  have h := Hashes.withTable_enc Hs .h5 (sEnc Hs T st) G (c, e)
  rw [show sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e = sEnc Hs T st (c, e) from rfl,
    h]
  exact blk_ba (n := 4) _

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024 in
/-- **H6 in the ROM**: with `H₅` a uniform table on the sibling inputs, the hop of `LabHyp` (the
tape's sibling answers recomputed from `H₅`, against uniform ones) is identical until a sibling
input is read, for every run `A` of a tape and the table that reads the table only on `Q`. For
`LabHyp`, `A` is a distinguisher of the ideal-tape prover's output with `H₅` the table, and `Q`
the inputs it reads: the prover's `H₅` queries at the active labels `L^{γ_e}_e` (a sibling input
only if the label offset `Θ` is zero) and the distinguisher's own queries (each a sibling input
with probability `2⁻¹²⁸`, as `Θ` is uniform given the proof). The bound is `lab_rom_query`
(`ZK/HopsH6.lean`). -/
theorem lab_rom (A : IdealTape st.params → (SKey st.params → Bytes 4) → Prop)
    (Q : IdealTape st.params → (SKey st.params → Bytes 4) → Finset (SKey st.params))
    (hQ : ∀ t G G', (∀ k ∈ Q t G, G k = G' k) → (A t G ↔ A t G')) :
    |pr ((Shared × PadsU st.params) × (SKey st.params → Bytes 4)) (fun x =>
        A (fillSib (Hs.withTable .h5 (sEnc Hs T st) x.2) T st
          (x.1.1, withSib x.1.2 fun _ => fun _ => 0)) x.2) -
      pr ((Shared × PadsU st.params) × ((SKey st.params → Bytes 4) × Sib))
        (fun x => A (x.1.1, withSib x.1.2 x.2.2) x.2.1)| ≤
      pr ((Shared × PadsU st.params) × ((SKey st.params → Bytes 4) × Sib))
        (fun x => ∃ e, sibKey Hs T st x.1 e ∈ Q (x.1.1, withSib x.1.2 x.2.2) x.2.1) := by
  simp only [fillSib_withTable]
  exact abs_pr_hidden_le (sibKey_injective Hs T st) (fun c u G => A (c.1, withSib c.2 u) G)
    (fun c u G => Q (c.1, withSib c.2 u) G) fun c u G G' h => hQ _ G G' h

end H6

end VoleMole.ZK.Sim
