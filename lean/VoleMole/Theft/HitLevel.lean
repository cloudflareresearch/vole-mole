import VoleMole.Theft.HitChain
import VoleMole.Theft.Tables
import VoleMole.Theft.ComOW
import VoleMole.EndToEnd.SpecRelations

/-!
# `ε_hit` with the chain hashes random tables: the generic part

The programming step of the theft theorems (`weakSE2_of_plain`) leaves `ε_hit`: the probability
that a fresh forgery's verifier `H₂³` point is a point a simulator programmed (`ProgEv … HitOpX`).
Here it is bounded for any two proof systems whose simulators program the grinding points of
their recomputed prefixes, in the model of the `…_leanX_plain` theorems with the concrete extra
table `XTab L M` (`hbX`: `H₂⁰`, `H₂¹`, `H₂²` and the other base hashes uniform tables on the inputs
of at most `L` bytes). `Theft/Hit.lean` (Ratatouille) and `Theft/MoussakaHit.lean` (Moussaka)
instantiate it.

* **Decision trees** (`ComOW.QTree`). `pr_hit_le`: a tree with `q` queries outputs a cell other
  than `a` whose value equals a target read off the table at `a` only, with probability
  `≤ (q + 1)/|Y|` (lazy sampling at `a`, then `pr_tree_bad_fix`). `QTree.of_two`, `QTree.of_cells`:
  reading given cells first costs one query each. `pr_set`, `pr_level_le`: the same on a tape with
  the table as one component (a lens), for the forgery's and a simulation's points as byte strings
  (`keyL`, `encL`).
* **The chain tables** of `XTab` (`getMu`/`setMu`, `get21`/`set21`, `get22`/`set22`): `hbX` with
  one of them changed agrees off its domain (`hbX_agreeOff_*`), and answers a short input by the
  table (`hbX_*_eq`).
* **A forgery** is a statement and proof bytes (`FD`), **a simulation** a statement and the
  simulator's output (`SD`). `HitG f t' t`: the verifier's `H₂³` point of `f` on `t` is a key where
  `t'` differs. `HitAt f t d`: the forgery's chain meets the simulation's at a first level where
  the inputs differ and the outputs agree: `H₂²` (the target is the first 56 bytes of the
  programmed block), `H₂¹` or `H₂⁰`.
* **`SimProg prog D`**: the programming `prog` of a simulation `D` leaves everything but `H₂³`
  unchanged, changes `H₂³` only at grinding keys of the simulation's recomputed prefix, and
  depends on the extra table only through that prefix. `simProg_progRO`: the Lean simulators'
  programming (`progRO`) with the base record read off the extra table.
* **The cases of a hit** (`hit_cases`, from `Chain.chain_hit`): a forgery whose statement is
  non-delayed with chain inputs of at most `L` bytes (`FOk`), whose `H₂⁰` input differs from the
  simulations', and that hits a point both programmings moved (`progT_moved`), hits one of the two
  simulations at one of the three levels.
* **The forgery's point is computed by a tree** (`qtree_forger`): the two simulations' points (the
  programmed `H₂³` table depends on the chain table only there, `progT_fst_congr`), then the
  adversary's tree (`AdmHit`).
* **`pr_hitAt_le`**: one simulation, on any tape with the tables as a component (`TLens`):
  `Pr[HitAt] ≤ (q₂₂+1)·2⁻⁴⁴⁸ + (q₂₁+1)·2⁻¹⁰⁸⁸ + (q_μ+1)·2⁻²⁵⁶` for a forgery whose points are
  computed by trees with `q₂₂`, `q₂₁`, `q_μ` queries.
* **`progEv_chain`**: for an adversary whose last stage reads `H₂⁰`, `H₂¹`, `H₂²` with `q_μ`, `q₂₁`,
  `q₂₂` queries (`AdmHit`), and a freshness that makes forgeries `FOk` with `H₂⁰` inputs other
  than the simulated statements',

      ε_hit ≤ 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸)   (`epsHit`).
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset

namespace VoleMole.Theft.Hit

open VoleMole.Privacy VoleMole.Theft.ComOW

/-! ## A tree that hits a target read at one cell -/

section Generic

variable {K Y : Type*} [Fintype K] [DecidableEq K] [Fintype Y] [Nonempty Y]

omit [Fintype K] [Fintype Y] [Nonempty Y] in
lemma fixAt_single (a : K) (v : Y) (T : K → Y) :
    fixAt (Function.update (fun _ => none) a (some v)) T = Function.update T a v := by
  funext k
  by_cases hk : k = a
  · subst hk
    simp [fixAt]
  · simp [fixAt, Function.update_of_ne hk]

/-- **A tree with `q` queries outputs a cell other than `a` whose value is a target read off the
table at `a` only** (or a constant, `a = none`) with probability `≤ (q + 1)/|Y|`: lazy sampling
at `a`, then `pr_tree_bad_fix` with the cell `a` fixed. -/
theorem pr_hit_le {f : (K → Y) → Option K} {q : ℕ} (hf : QTree f q) (a : Option K)
    (τ : (K → Y) → Y) (hτ : ∀ T T', (∀ k, a = some k → T k = T' k) → τ T = τ T') :
    pr (K → Y) (fun T => ∃ k, f T = some k ∧ a ≠ some k ∧ T k = τ T) ≤
      (q + 1 : ℕ) * (1 / Fintype.card Y) := by
  classical
  rcases isEmpty_or_nonempty K with hK | ⟨⟨k₀⟩⟩
  · refine (pr_mono (Q := fun _ => False) fun T ⟨k, _⟩ => hK.elim k).trans ?_
    rw [pr_def]
    simp only [filter_false, card_empty, Nat.cast_zero, zero_div]
    positivity
  have hf' : QTree (fun T => (f T).getD k₀) q := hf.map fun o => o.getD k₀
  let T₀ : K → Y := fun _ => Classical.arbitrary Y
  rcases a with _ | a
  · have hc : ∀ T, τ T = τ T₀ := fun T => hτ T T₀ (by simp)
    have h := pr_tree_bad (Bad := fun y => y = τ T₀) (pr_eq_le (τ T₀)) hf'
    refine (pr_mono fun T hT => ?_).trans h
    obtain ⟨k, hk, -, hv⟩ := hT
    show T ((f T).getD k₀) = τ T₀
    rw [hk, Option.getD_some, hv, hc]
  · rw [pr_resample a]
    refine pr_prod_le' _ fun v => ?_
    have h := pr_tree_bad_fix (Bad := fun y => y = τ (Function.update T₀ a v)) (pr_eq_le _) hf'
      (Function.update (fun _ => none) a (some v))
    refine (pr_mono fun T hT => ?_).trans h
    obtain ⟨k, hk, hka, hv⟩ := hT
    have hka' : k ≠ a := fun h => hka (h ▸ rfl)
    simp only [fixAt_single, hk, Option.getD_some]
    refine ⟨by simp [Function.update_of_ne hka'], ?_⟩
    simp only [Function.update_of_ne hka'] at hv
    rw [hv]
    exact hτ _ _ fun k hk => by cases hk; simp

omit [Fintype K] [Fintype Y] in
/-- **A computation that reads two cells and then runs a tree** is a tree with two more queries. -/
lemma QTree.of_two {O Z : Type*} {F : (K → Y) → O} (H : (K → Y) → Z) (a b : K)
    (hH : ∀ T T', T a = T' a → T b = T' b → H T = H T') (G : Z → (K → Y) → O) {q : ℕ}
    (hG : ∀ z, QTree (G z) q) (hF : ∀ T, F T = G (H T) T) : QTree F (q + 2) := by
  let T₀ : K → Y := fun _ => Classical.arbitrary Y
  let U : Y → Y → K → Y := fun v w => Function.update (Function.update T₀ a v) b w
  have hU : ∀ T, H T = H (U (T a) (T b)) := fun T => hH _ _
    (by by_cases hab : a = b <;> simp [U, hab]) (by simp [U])
  have e : F = fun T => (fun v T => (fun w T => G (H (U v w)) T) (T b) T) (T a) T := by
    funext T
    rw [hF, hU]
  rw [e]
  exact .ask a (fun v T => (fun w T => G (H (U v w)) T) (T b) T) (q + 1) fun v =>
    .ask b (fun w T => G (H (U v w)) T) q fun w => hG _

/-- **Averaging over one component.** For a component `get` with its setter `set` (the laws of a
lens), the probability of `P` is the probability of `P` at a uniform value of the component, the
rest uniform. -/
lemma pr_set {X T : Type*} [Fintype X] [Fintype T] [Nonempty T] (set : T → X → X) (get : X → T)
    (h1 : ∀ x, set (get x) x = x) (h2 : ∀ t x, get (set t x) = t)
    (h3 : ∀ t t' x, set t (set t' x) = set t x) (P : X → Prop) :
    pr X P = pr (X × T) (fun z => P (set z.2 z.1)) := by
  let e : X × T ≃ X × T :=
    ⟨fun z => (set z.2 z.1, get z.1), fun z => (set z.2 z.1, get z.1),
      fun z => by simp [h1, h2, h3], fun z => by simp [h1, h2, h3]⟩
  rw [show (fun z : X × T => P (set z.2 z.1)) = fun z => P (e z).1 from rfl,
    pr_equiv e (fun z => P z.1), pr_prod_fst]

end Generic

/-! ## The chain tables of the extra table -/

section XTab

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim

variable {L M : ℕ}

/-- **The key of a short input**: `a` with `encL a = b`, if `b` has at most `L` bytes. -/
noncomputable def keyL (L : ℕ) (b : ByteArray) : Option (KL L) := by
  classical
  exact if h : ∃ a : KL L, encL a = b then some h.choose else none

lemma keyL_encL (a : KL L) : keyL L (encL a) = some a := by
  classical
  have h : ∃ a' : KL L, encL a' = encL a := ⟨a, rfl⟩
  simp only [keyL, h, ↓reduceDIte, Option.some.injEq]
  exact encL_injective h.choose_spec

lemma encL_of_keyL {b : ByteArray} {a : KL L} (h : keyL L b = some a) : encL a = b := by
  classical
  unfold keyL at h
  split_ifs at h with h'
  · cases h
    exact h'.choose_spec

/-- An input of at most `L` bytes is a key. -/
lemma exists_encL {b : ByteArray} (h : b.size ≤ L) : ∃ a : KL L, encL a = b :=
  ⟨⟨⟨b.size, Nat.lt_succ_of_le h⟩, blk b.size b⟩, ba_blk_of_size rfl⟩

/-- The `H₂⁰` table. -/
def getMu (x : XTab L M) : KL L → Bytes 32 := x.2.1
def setMu (T : KL L → Bytes 32) (x : XTab L M) : XTab L M := (x.1, T, x.2.2)
/-- The `H₂¹` table. -/
def get21 (x : XTab L M) : KL L → Bytes 136 := x.2.2.2.2.1
def set21 (T : KL L → Bytes 136) (x : XTab L M) : XTab L M :=
  (x.1, x.2.1, x.2.2.1, x.2.2.2.1, T, x.2.2.2.2.2)
/-- The `H₂²` table. -/
def get22 (x : XTab L M) : KL L → Bytes 56 := x.2.2.2.2.2.1
def set22 (T : KL L → Bytes 56) (x : XTab L M) : XTab L M :=
  (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, T, x.2.2.2.2.2.2)

/-- `AgreeOff` survives a table on another (or the same) domain. -/
lemma agreeOff_withTable {k j : Kind} {Hs Hs' : Hashes} (h : Hs.AgreeOff k Hs') {K : Type}
    (enc : K → ByteArray) (G : K → Bytes j.outLen) :
    (Hs.withTable j enc G).AgreeOff k (Hs'.withTable j enc G) := by
  intro k' hk'
  funext b
  simp only [Hashes.withTable]
  split_ifs with h1 h2
  · rfl
  · subst h1
    rw [h _ hk']
  · rw [h k' hk']

/-- Two tables on the domain `k` agree off `k`. -/
lemma agreeOff_withTable_self (Hs : Hashes) (k : Kind) {K : Type} (enc : K → ByteArray)
    (G G' : K → Bytes k.outLen) : (Hs.withTable k enc G).AgreeOff k (Hs.withTable k enc G') := by
  intro k' hk'
  funext b
  simp only [Hashes.withTable, hk', ite_false]

open Classical in
lemma withTable_self (Hs : Hashes) (k : Kind) {K : Type} (enc : K → ByteArray)
    (G : K → Bytes k.outLen) (b : ByteArray) :
    (Hs.withTable k enc G).hash k b =
      if h : ∃ a, enc a = b then ba (G h.choose) else Hs.hash k b := by
  simp only [Hashes.withTable, ite_true]

/-- The table `encL` answers a short input at its key. -/
lemma withTable_encL (Hs : Hashes) (k : Kind) (G : KL L → Bytes k.outLen) (b : ByteArray) :
    (Hs.withTable k encL G).hash k b =
      match keyL L b with
      | some a => ba (G a)
      | none => Hs.hash k b := by
  classical
  rw [withTable_self]
  by_cases h : ∃ a : KL L, encL a = b
  · obtain ⟨a, rfl⟩ := h
    have hex : ∃ a' : KL L, encL a' = encL a := ⟨a, rfl⟩
    simp only [keyL_encL, hex, ↓reduceDIte]
    congr 2
    exact encL_injective (Exists.choose_spec (⟨a, rfl⟩ : ∃ a', encL a' = encL a))
  · have : keyL L b = none := by simp only [keyL, h, ↓reduceDIte]
    simp only [h, ↓reduceDIte, this]

lemma hbX_agreeOff_mu (T T' : KL L → Bytes 32) (x : XTab L M) :
    (hbX (setMu T x)).AgreeOff .mu (hbX (setMu T' x)) := by
  unfold hbX setMu
  simp only
  refine agreeOff_withTable (agreeOff_withTable (agreeOff_withTable (agreeOff_withTable
    (agreeOff_withTable (agreeOff_withTable_self _ _ _ _ _) _ _) _ _) _ _) _ _) _ _

lemma hbX_agreeOff_21 (T T' : KL L → Bytes 136) (x : XTab L M) :
    (hbX (set21 T x)).AgreeOff .h21 (hbX (set21 T' x)) := by
  unfold hbX set21
  simp only
  exact agreeOff_withTable (agreeOff_withTable (agreeOff_withTable_self _ _ _ _ _) _ _) _ _

lemma hbX_agreeOff_22 (T T' : KL L → Bytes 56) (x : XTab L M) :
    (hbX (set22 T x)).AgreeOff .h22 (hbX (set22 T' x)) := by
  unfold hbX set22
  simp only
  exact agreeOff_withTable (agreeOff_withTable_self _ _ _ _ _) _ _

lemma hbX_mu_eq (x : XTab L M) (b : ByteArray) :
    (hbX x).hash .mu b = match keyL L b with
      | some a => ba (x.2.1 a)
      | none => Hashes.shake.hash .mu b := by
  refine (Hashes.withTable_ne _ (.comb M) .mu (by simp) _ _ _).trans ?_
  refine (Hashes.withTable_ne _ .h22 .mu (by simp) _ _ _).trans ?_
  refine (Hashes.withTable_ne _ .h21 .mu (by simp) _ _ _).trans ?_
  refine (Hashes.withTable_ne _ .h4 .mu (by simp) _ _ _).trans ?_
  refine (Hashes.withTable_ne _ .muDelayed .mu (by simp) _ _ _).trans ?_
  refine (withTable_encL _ .mu x.2.1 b).trans ?_
  rcases keyL L b with _ | a
  · exact Hashes.withTable_ne _ .h1 .mu (by simp) _ _ _
  · rfl

lemma hbX_21_eq (x : XTab L M) (b : ByteArray) :
    (hbX x).hash .h21 b = match keyL L b with
      | some a => ba (x.2.2.2.2.1 a)
      | none => Hashes.shake.hash .h21 b := by
  refine (Hashes.withTable_ne _ (.comb M) .h21 (by simp) _ _ _).trans ?_
  refine (Hashes.withTable_ne _ .h22 .h21 (by simp) _ _ _).trans ?_
  refine (withTable_encL _ .h21 x.2.2.2.2.1 b).trans ?_
  rcases keyL L b with _ | a
  · exact (Hashes.withTable_ne _ .h4 .h21 (by simp) _ _ _).trans
      ((Hashes.withTable_ne _ .muDelayed .h21 (by simp) _ _ _).trans
      ((Hashes.withTable_ne _ .mu .h21 (by simp) _ _ _).trans
      (Hashes.withTable_ne _ .h1 .h21 (by simp) _ _ _)))
  · rfl

lemma hbX_22_eq (x : XTab L M) (b : ByteArray) :
    (hbX x).hash .h22 b = match keyL L b with
      | some a => ba (x.2.2.2.2.2.1 a)
      | none => Hashes.shake.hash .h22 b := by
  refine (Hashes.withTable_ne _ (.comb M) .h22 (by simp) _ _ _).trans ?_
  refine (withTable_encL _ .h22 x.2.2.2.2.2.1 b).trans ?_
  rcases keyL L b with _ | a
  · exact (Hashes.withTable_ne _ .h21 .h22 (by simp) _ _ _).trans
      ((Hashes.withTable_ne _ .h4 .h22 (by simp) _ _ _).trans
      ((Hashes.withTable_ne _ .muDelayed .h22 (by simp) _ _ _).trans
      ((Hashes.withTable_ne _ .mu .h22 (by simp) _ _ _).trans
      (Hashes.withTable_ne _ .h1 .h22 (by simp) _ _ _))))
  · rfl

end XTab

/-! ## One level: a lens on the tape -/

section Level

open VoleMole.ZK.Sim

variable {L : ℕ}

/-- **One level of a hit has probability `≤ (q + 1)/|Y|`.** The tape `Ω` has a component `T`
(a table on the short inputs, lens `set`/`get`). The forgery's point `Pf` is computed from `T` by
a tree with `q` queries; the simulation's point `Ps` does not depend on `T`, and its target `τ`
reads `T` only at `Ps`. -/
theorem pr_level_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] {n : ℕ} (set : (KL L → Bytes n) → Ω → Ω)
    (get : Ω → KL L → Bytes n) (h1 : ∀ x, set (get x) x = x) (h2 : ∀ t x, get (set t x) = t)
    (h3 : ∀ t t' x, set t (set t' x) = set t x) (Pf Ps τ : Ω → ByteArray) {q : ℕ}
    (hPs : ∀ T T' z, Ps (set T z) = Ps (set T' z))
    (hτ : ∀ T T' z, (∀ k, keyL L (Ps (set T z)) = some k → T k = T' k) →
      τ (set T z) = τ (set T' z))
    (hPf : ∀ z, QTree (fun T => keyL L (Pf (set T z))) q) :
    pr Ω (fun ω => ∃ k, encL k = Pf ω ∧ Pf ω ≠ Ps ω ∧ ba (get ω k) = τ ω) ≤
      (q + 1 : ℕ) * (1 / Fintype.card (Bytes n)) := by
  classical
  rw [pr_set set get h1 h2 h3]
  refine pr_prod_le' _ fun z => ?_
  let T₀ : KL L → Bytes n := fun _ _ => 0
  have h := pr_hit_le (hPf z) (keyL L (Ps (set T₀ z))) (fun T => blk n (τ (set T z)))
    fun T T' hT => by
      rw [hτ T T' z fun k hk => hT k (by rwa [hPs T₀ T z])]
  refine (Privacy.pr_mono fun T hT => ?_).trans h
  obtain ⟨k, hk, hne, hv⟩ := hT
  refine ⟨k, by rw [← hk, keyL_encL], fun he => hne ?_, ?_⟩
  · rw [← hk, encL_of_keyL he, hPs T₀ T z]
  · rw [h2] at hv
    rw [← hv, blk_ba]

end Level


/-! ## Byte strings -/

/-- Concatenations with first parts of equal sizes determine both parts. -/
lemma append_split {a b a' b' : ByteArray} (h : a ++ b = a' ++ b') (hs : a.size = a'.size) :
    a = a' ∧ b = b' := by
  have ha : a = a' := by
    have e : (a ++ b).extract 0 a.size = (a' ++ b').extract 0 a.size := by rw [h]
    rwa [ByteArray.extract_append_eq_left rfl, ByteArray.extract_append_eq_left hs] at e
  subst ha
  exact ⟨rfl, (ByteArray.append_right_inj _).1 h⟩

/-! ## Reading a list of cells first -/

section Cells

variable {K Y : Type*} [DecidableEq K] [Nonempty Y]

/-- **A computation that reads the cells of a list and then runs a tree** is a tree with one more
query per cell. -/
lemma QTree.of_cells {O Z : Type*} {q : ℕ} (G : Z → (K → Y) → O) (hG : ∀ z, QTree (G z) q) :
    ∀ (as : List K) (H : (K → Y) → Z), (∀ T T', (∀ a ∈ as, T a = T' a) → H T = H T') →
      QTree (fun T => G (H T) T) (q + as.length)
  | [], H, hH => by
    let T₀ : K → Y := fun _ => Classical.arbitrary Y
    have e : (fun T => G (H T) T) = G (H T₀) := by
      funext T
      rw [hH T T₀ (by simp)]
    rw [e]
    exact hG _
  | a :: as, H, hH => by
    have e : (fun T => G (H T) T) =
        fun T => (fun v T => G (H (Function.update T a v)) T) (T a) T := by
      funext T
      simp only [Function.update_eq_self]
    rw [e]
    refine .ask a (fun v T => G (H (Function.update T a v)) T) (q + as.length) fun v => ?_
    refine QTree.of_cells G hG as (fun T => H (Function.update T a v)) fun T T' h => hH _ _ ?_
    intro b hb
    by_cases hba : b = a
    · subst hba
      simp
    · simp only [Function.update_of_ne hba]
      exact h b ((List.mem_cons.1 hb).resolve_left hba)

end Cells

/-! ## The chain events, for any forgery and simulation -/

section Chain

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ZK
open VoleMole.Theft.Chain
open VoleMole.ROM.IC (muIn)

variable {R : Type} [CipherRow R] {p : Params} {L M : ℕ}

/-- The shared tables with the extra table `XTab L M`. -/
abbrev ShT (R : Type) (p : Params) (L M : ℕ) := ShX R p (XTab L M)

/-- **The record the chain is computed with**: the base record `hbX x` with the `H₅` table. -/
noncomputable def recT (t : ShT R p L M) : Hashes := rec5 (hbX t.2.2) t.2.1.1

/-- The PRG of the tables' cipher. -/
noncomputable abbrev prgT (t : ShT R p L M) : HasPrg := icPrg (rowFn t.2.1.2)

/-- **A forgery**: a statement and proof bytes. -/
abbrev FD := Statement × ByteArray

/-- **A simulation**: a statement and the simulator's output. -/
abbrev SD := Statement × Except String ByteArray

/-- A simulation, if there is a statement. -/
abbrev SimD := Option SD

/-- The simulation of an optional statement. -/
def sdO {I C : Type*} (D : I → C → SD) (x : Option I) (c : C) : SimD := x.map fun i => D i c

/-- The simulator's recomputed prefix on the tables. -/
noncomputable abbrev simPreT (t : ShT R p L M) (d : SD) : ByteArray :=
  @simPre (prgT t) (recT t) CrtGen.tables d.1 d.2

/-- The forgery's chain points: `H₂²`, `H₂¹`, `H₂⁰`. -/
noncomputable def fPt22 (f : FD) (t : ShT R p L M) : ByteArray :=
  @cin2 (prgT t) (recT t) CrtGen.tables f.1 f.2
noncomputable def fPt21 (f : FD) (t : ShT R p L M) : ByteArray :=
  @cin1 (prgT t) (recT t) f.1 f.2
def fPtMu (f : FD) : ByteArray := muIn f.1

/-- A simulation's chain points. -/
noncomputable def sPt22 (d : SimD) (t : ShT R p L M) : ByteArray :=
  match d with
  | some (st, o) => @sim2 (prgT t) (recT t) CrtGen.tables st o
  | none => ByteArray.empty
noncomputable def sPt21 (d : SimD) (t : ShT R p L M) : ByteArray :=
  match d with
  | some (st, o) => @sim1 (prgT t) (recT t) st o
  | none => ByteArray.empty
def sPtMu (d : SimD) : ByteArray :=
  match d with
  | some (st, _) => muIn st
  | none => ByteArray.empty

/-- A simulation's targets: the first 56 bytes of its programmed block, and its `H₂¹`, `H₂⁰`
answers. -/
noncomputable def sTau22 (d : SimD) (t : ShT R p L M) : ByteArray :=
  match d with
  | some d => (ba (blk (preLen p) (simPreT t d))).extract 0 56
  | none => ByteArray.empty
noncomputable def sTau21 (d : SimD) (t : ShT R p L M) : ByteArray :=
  (recT t).hash .h21 (sPt21 d t)
noncomputable def sTauMu (d : SimD) (t : ShT R p L M) : ByteArray :=
  (recT t).hash .mu (sPtMu d)

/-- **A hit at one level**: the forgery's point `Pf` is a short input other than the simulation's
`Ps`, and the table answers it with the target `τ`. -/
def Ev {n : ℕ} (Pf Ps τ : ByteArray) (G : KL L → ZK.Sim.Bytes n) : Prop :=
  ∃ k, encL k = Pf ∧ Pf ≠ Ps ∧ ba (G k) = τ

/-- **A hit on one simulation**, at one of the three levels. -/
def HitAt (f : FD) (t : ShT R p L M) (d : SimD) : Prop :=
  Ev (fPt22 f t) (sPt22 d t) (sTau22 d t) (get22 t.2.2) ∨
    Ev (fPt21 f t) (sPt21 d t) (sTau21 d t) (get21 t.2.2) ∨
    Ev (fPtMu f) (sPtMu d) (sTauMu d t) (getMu t.2.2)

/-- **The forgery's verifier reads `H₂³` at a key where the tables `t'` and `t` differ.** -/
def HitG (f : FD) (t' t : ShT R p L M) : Prop :=
  ∃ k : K2 p, enc2 p k = (@vPre (prgT t) (recT t) CrtGen.tables f.1 f.2 ++
    (pfOf f.1 f.2).ctr).push 11 ∧ t'.1 k ≠ t.1 k

/-- **A statement whose chain inputs are table points**: not delayed, no binders, and `H₂¹`,
`H₂²`, `H₂⁰` inputs of at most `L` bytes. -/
def FOk (L : ℕ) (st : Statement) : Prop :=
  st.delayed = false ∧ st.binder1.size = 0 ∧ st.binder2.size = 0 ∧
    64 + 16 * st.params.correctionBytes + st.params.nMask * st.params.nMultBytes + 16 + 0 + 1 ≤ L ∧
    264 + 0 + st.params.witnessBytes + 1 ≤ L ∧ (muIn st).size ≤ L

/-! ### Helpers -/

omit [CipherRow R] in
lemma recT_hash_ne (t : ShT R p L M) {k : Kind} (hk : k ≠ .h5) :
    (recT t).hash k = (hbX t.2.2).hash k :=
  funext (Hashes.withTable_ne _ .h5 k hk enc5 t.2.1.1)

omit [CipherRow R] in
lemma recT_wf (t : ShT R p L M) : HashesWF (recT t) := (hbX_wf t.2.2).withTable .h5 enc5 t.2.1.1

/-- The forger's verifier point is computed with the `H₅` record (`vPre` does not read `H₂³`). -/
lemma vPoint_eq (Hb : Hashes) (st : Statement) (pf : ByteArray) (s : ShG R p) :
    vPoint Hb st pf s =
      (@vPre (icPrg (rowFn s.2.2)) (rec5 Hb s.2.1) CrtGen.tables st pf ++ (pfOf st pf).ctr).push 11 := by
  unfold vPoint
  have hA : (recV p Hb s.1 s.2.1).AgreeOff .h23 (rec5 Hb s.2.1) :=
    agreeOff_withTable (fun k hk => funext (Hashes.withTable_ne Hb .h23 k hk _ _)) _ _
  rw [@vPre_agreeOff (icPrg (rowFn s.2.2)) _ _ _ unread_h23 hA]
  rfl

/-- **A hit of the verifier on the tables (`HitPt`) is a hit of the forgery** (`HitG`). -/
lemma hitG_of_hitPt (st : Statement) (pf : ByteArray) (t' t : ShT R p L M)
    (h : HitPt (hbX t.2.2) st pf (shOf t') (shOf t)) : HitG (st, pf) t' t := by
  obtain ⟨k, hk, hmv⟩ := h
  rw [vPoint_eq] at hk
  exact ⟨k, hk, hmv⟩

/-- The simulator's `outPre` is `simPre` with `recT`. -/
lemma outPre_eq (st : Statement) (o : Except String ByteArray) (t : ShT R p L M) :
    @outPre (prgT t) (hbX t.2.2) CrtGen.tables st t.2.1.1 o = simPreT t (st, o) := by
  cases o <;> rfl

lemma progRO_moved_at (st : Statement) (c : SimCoins p) (s : ShG R p) (u : ShT R p L M)
    (hs : s.2 = u.2.1) (k : K2 p) (h : (progRO p (hbX u.2.2) st c s).1 k ≠ s.1 k) :
    k.1 = blk (preLen p) (simPreT u (st, simulate p c)) := by
  obtain ⟨s1, s2⟩ := s
  simp only at hs
  subst hs
  rw [progRO_moved (hbX u.2.2) st c _ k h]
  exact congrArg _ (outPre_eq st _ u)

omit [CipherRow R] in
lemma recT_22 (t : ShT R p L M) (k : KL L) : (recT t).hash .h22 (encL k) = ba (get22 t.2.2 k) := by
  rw [recT_hash_ne t (by decide), hbX_22_eq, keyL_encL]
  rfl

omit [CipherRow R] in
lemma recT_21 (t : ShT R p L M) (k : KL L) : (recT t).hash .h21 (encL k) = ba (get21 t.2.2 k) := by
  rw [recT_hash_ne t (by decide), hbX_21_eq, keyL_encL]
  rfl

omit [CipherRow R] in
lemma recT_mu (t : ShT R p L M) (k : KL L) : (recT t).hash .mu (encL k) = ba (getMu t.2.2 k) := by
  rw [recT_hash_ne t (by decide), hbX_mu_eq, keyL_encL]
  rfl

/-- The recomputed prefix reads the tables but `H₂³`. -/
lemma simPreT_congr {t t' : ShT R p L M} (h : t'.2 = t.2) (d : SD) : simPreT t' d = simPreT t d := by
  obtain ⟨a', b'⟩ := t'
  obtain ⟨a, b⟩ := t
  simp only at h
  subst h
  rfl

/-- **A hit on one simulation's prefix** (`chain_hit` with the tables' record): one of the three
level events, unless the simulation produced a proof whose statement has the forgery's `H₂⁰`
input. -/
lemma hitAt_of (f : FD) (hf : FOk L f.1) (t : ShT R p L M) (d : SD) (hds : d.1.delayed = false)
    (k : K2 p)
    (hk : enc2 p k = (@vPre (prgT t) (recT t) CrtGen.tables f.1 f.2 ++ (pfOf f.1 f.2).ctr).push 11)
    (hkp' : k.1 = blk (preLen p) (simPreT t d))
    (hne : (∃ b, d.2 = .ok b) → muIn f.1 ≠ muIn d.1) : HitAt f t (some d) := by
  obtain ⟨hdf, hb1, hb2, hl1, hl2, hlm⟩ := hf
  obtain ⟨hv, hc⟩ := @chain_hit (prgT t) (recT t) CrtGen.tables (recT_wf t) p f.1 d.1 f.2 d.2 hdf hds
    k hk hkp'
  rcases hc with ⟨h2, he⟩ | ⟨h1, he⟩ | ⟨hm, he⟩ | ⟨hok, hm⟩
  · left
    have hs := @size_cin2_le (prgT t) (recT t) CrtGen.tables f.1 f.2 (recT_wf t) hdf
    obtain ⟨a, ha⟩ := exists_encL (L := L)
      (b := @cin2 (prgT t) (recT t) CrtGen.tables f.1 f.2) (by omega)
    refine ⟨a, ha, h2, ?_⟩
    rw [← recT_22, ha, he]
    rfl
  · right; left
    have hs := @size_cin1_le (prgT t) (recT t) f.1 f.2 (recT_wf t)
    obtain ⟨a, ha⟩ := exists_encL (L := L)
      (b := @cin1 (prgT t) (recT t) f.1 f.2) (by omega)
    refine ⟨a, ha, h1, ?_⟩
    rw [← recT_21, ha]
    exact he
  · right; right
    obtain ⟨a, ha⟩ := exists_encL (L := L) (b := muIn f.1) (by omega)
    refine ⟨a, ha, hm, ?_⟩
    rw [← recT_mu, ha]
    exact he
  · exact absurd hm (hne hok)

/-! ### Programmings of simulations -/

/-- **A programming of a simulation.** `prog i c` programs the tables for the simulation `D i c`
(statement and output): it leaves everything but `H₂³` unchanged, changes `H₂³` only at grinding
keys of the simulation's recomputed prefix, and depends on the extra table only through that
prefix; the statement is not delayed. -/
def SimProg {I C : Type*} (prog : I → C → ShT R p L M → ShT R p L M) (D : I → C → SD) : Prop :=
  (∀ i c t, (prog i c t).2 = t.2) ∧
    (∀ i c t k, (prog i c t).1 k ≠ t.1 k → k.1 = blk (preLen p) (simPreT t (D i c))) ∧
    (∀ i c G2 G5E x x', simPreT (p := p) (G2, (G5E, x)) (D i c) = simPreT (G2, (G5E, x')) (D i c) →
      (prog i c (G2, (G5E, x))).1 = (prog i c (G2, (G5E, x'))).1) ∧
    ∀ i c, (D i c).1.delayed = false

/-- **The Lean simulators' programming**, the base record read off the extra table. -/
lemma simProg_progRO {I : Type*} (stOf : I → Statement) (hd : ∀ i, (stOf i).delayed = false) :
    SimProg (R := R) (p := p) (L := L) (M := M)
      (progX fun x i c => progRO p (hbX x) (stOf i) c) (fun i c => (stOf i, simulate p c)) := by
  refine ⟨fun _ _ _ => rfl, fun i c t k h => progRO_moved_at (stOf i) c (shOf t) t rfl k h,
    fun i c G2 G5E x x' e => ?_, fun i _ => hd i⟩
  show (progRO p (hbX x) _ c (G2, G5E)).1 = (progRO p (hbX x') _ c (G2, G5E)).1
  simp only [progRO]
  rw [outPre_eq (t := (G2, (G5E, x))), outPre_eq (t := (G2, (G5E, x'))), e]

section Two

variable {I₁ I₂ : Type*} {C₁ C₂ : Type} {prog₁ : I₁ → C₁ → ShT R p L M → ShT R p L M}
  {prog₂ : I₂ → C₂ → ShT R p L M → ShT R p L M} {D₁ : I₁ → C₁ → SD} {D₂ : I₂ → C₂ → SD}

/-- **The keys both programmings change** are grinding keys of one of the two simulations'
prefixes. -/
lemma progT_moved (h₁ : SimProg prog₁ D₁) (h₂ : SimProg prog₂ D₂) (x₁ : Option I₁) (c₁ : C₁)
    (x₂ : Option I₂) (c₂ : C₂) (t : ShT R p L M) (k : K2 p)
    (h : (progT prog₁ prog₂ x₁ c₁ x₂ c₂ t).1 k ≠ t.1 k) :
    (∃ i, x₁ = some i ∧ k.1 = blk (preLen p) (simPreT t (D₁ i c₁))) ∨
      (∃ i, x₂ = some i ∧ k.1 = blk (preLen p) (simPreT t (D₂ i c₂))) := by
  -- the second programming acts first, on `t`; the first on its output
  have h2 : (progO prog₂ x₂ c₂ t).2 = t.2 := progO_snd h₂.1 _ _ _
  by_cases hk : (progO prog₂ x₂ c₂ t).1 k = t.1 k
  · left
    rcases x₁ with _ | i
    · exact absurd hk h
    · refine ⟨i, rfl, ?_⟩
      rw [← simPreT_congr h2]
      exact h₁.2.1 i c₁ _ k fun he => h (he.trans hk)
  · right
    rcases x₂ with _ | i
    · exact absurd rfl hk
    · exact ⟨i, rfl, h₂.2.1 i c₂ t k hk⟩

/-- **The cases of a hit.** A forgery with table-point chain inputs (`FOk`) and an `H₂⁰` input
other than those of the simulations that produced a proof, whose verifier's `H₂³` point is a point
the two programmings moved, hits one of the two simulations at one of the three levels. -/
theorem hit_cases (h₁ : SimProg prog₁ D₁) (h₂ : SimProg prog₂ D₂) (f : FD) (hf : FOk L f.1)
    (x₁ : Option I₁) (c₁ : C₁) (x₂ : Option I₂) (c₂ : C₂) (t : ShT R p L M)
    (hne₁ : ∀ i, x₁ = some i → (∃ b, (D₁ i c₁).2 = .ok b) → muIn f.1 ≠ muIn (D₁ i c₁).1)
    (hne₂ : ∀ i, x₂ = some i → (∃ b, (D₂ i c₂).2 = .ok b) → muIn f.1 ≠ muIn (D₂ i c₂).1)
    (hhit : HitG f (progT prog₁ prog₂ x₁ c₁ x₂ c₂ t) t) :
    HitAt f t (sdO D₁ x₁ c₁) ∨ HitAt f t (sdO D₂ x₂ c₂) := by
  obtain ⟨k, hk, hmv⟩ := hhit
  rcases progT_moved h₁ h₂ x₁ c₁ x₂ c₂ t k hmv with ⟨i, rfl, hkp⟩ | ⟨i, rfl, hkp⟩
  · exact Or.inl (hitAt_of f hf t _ (h₁.2.2.2 i c₁) k hk hkp (hne₁ i rfl))
  · exact Or.inr (hitAt_of f hf t _ (h₂.2.2.2 i c₂) k hk hkp (hne₂ i rfl))

/-- **The programmed `H₂³` table depends on the extra table only through the two simulations'
prefixes.** -/
lemma progT_fst_congr (h₁ : SimProg prog₁ D₁) (h₂ : SimProg prog₂ D₂) (x₁ : Option I₁) (c₁ : C₁)
    (x₂ : Option I₂) (c₂ : C₂) (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x x' : XTab L M)
    (hp1 : ∀ i, x₁ = some i →
      simPreT (p := p) (G2, (G5E, x)) (D₁ i c₁) = simPreT (G2, (G5E, x')) (D₁ i c₁))
    (hp2 : ∀ i, x₂ = some i →
      simPreT (p := p) (G2, (G5E, x)) (D₂ i c₂) = simPreT (G2, (G5E, x')) (D₂ i c₂)) :
    (progT prog₁ prog₂ x₁ c₁ x₂ c₂ (G2, (G5E, x))).1 =
      (progT prog₁ prog₂ x₁ c₁ x₂ c₂ (G2, (G5E, x'))).1 := by
  have e2 : (progO prog₂ x₂ c₂ (G2, (G5E, x))).1 = (progO prog₂ x₂ c₂ (G2, (G5E, x'))).1 := by
    rcases x₂ with _ | j
    · rfl
    · exact h₂.2.2.1 j c₂ G2 G5E x x' (hp2 j rfl)
  have s2 : ∀ y, progO prog₂ x₂ c₂ (G2, (G5E, y)) =
      ((progO prog₂ x₂ c₂ (G2, (G5E, y))).1, (G5E, y)) :=
    fun y => Prod.ext rfl (progO_snd h₂.1 _ _ _)
  unfold progT
  rw [s2 x, s2 x', e2]
  rcases x₁ with _ | i
  · rfl
  · exact h₁.2.2.1 i c₁ _ G5E x x' (hp1 i rfl)

instance : Inhabited (KL L) := ⟨⟨0, Fin.elim0⟩⟩

/-- **The forgery's point at one level is computed by a tree** with two more queries than the
adversary's: the two simulations' points (which fix the programmed `H₂³` table), then the
adversary's tree. -/
lemma qtree_forger {Out : Type*} {n : ℕ} (setX : (KL L → ZK.Sim.Bytes n) → XTab L M → XTab L M)
    {q : ℕ} (Pf : Out → ShT R p L M → ByteArray) (Ps : SimD → ShT R p L M → ByteArray)
    (hPf : ∀ op G2 G5E x T T', Pf op (G2, (G5E, setX T x)) = Pf op (G2, (G5E, setX T' x)))
    (hPs : ∀ d G2 G5E x T T', Ps d (G2, (G5E, setX T x)) = Ps d (G2, (G5E, setX T' x)))
    (hpre : ∀ (d : SD) G2 G5E x T T', d.1.delayed = false →
      (∀ k, keyL L (Ps (some d) (G2, (G5E, setX T x))) = some k → T k = T' k) →
      simPreT (p := p) (G2, (G5E, setX T x)) d = simPreT (G2, (G5E, setX T' x)) d)
    (h₁ : SimProg prog₁ D₁) (h₂ : SimProg prog₂ D₂) (F : ShT R p L M → Out)
    (hF : ∀ G2 G5E x, QTree (fun T => F (G2, (G5E, setX T x))) q)
    (x₁ : Option I₁) (c₁ : C₁) (x₂ : Option I₂) (c₂ : C₂)
    (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M) :
    QTree (fun T => keyL L (Pf (F (progT prog₁ prog₂ x₁ c₁ x₂ c₂ (G2, (G5E, setX T x))))
      (G2, (G5E, setX T x)))) (q + 2) := by
  let T₀ : KL L → ZK.Sim.Bytes n := fun _ _ => 0
  let a₁ : KL L := (keyL L (Ps (sdO D₁ x₁ c₁) (G2, (G5E, setX T₀ x)))).getD default
  let a₂ : KL L := (keyL L (Ps (sdO D₂ x₂ c₂) (G2, (G5E, setX T₀ x)))).getD default
  have hag : ∀ (d : SimD) (a : KL L), ∀ T T' : KL L → ZK.Sim.Bytes n,
      T ((keyL L (Ps d (G2, (G5E, setX T₀ x)))).getD a) =
        T' ((keyL L (Ps d (G2, (G5E, setX T₀ x)))).getD a) →
      ∀ k, keyL L (Ps d (G2, (G5E, setX T x))) = some k → T k = T' k := by
    intro d a T T' hT k hk
    rw [hPs d G2 G5E x T T₀] at hk
    rw [hk] at hT
    exact hT
  refine QTree.of_two (fun T => (progT prog₁ prog₂ x₁ c₁ x₂ c₂ (G2, (G5E, setX T x))).1) a₁ a₂ ?_
    (fun H2 T => keyL L (Pf (F (H2, (G5E, setX T x))) (G2, (G5E, setX T₀ x))))
    (fun H2 => (hF H2 G5E x).map fun op => keyL L (Pf op (G2, (G5E, setX T₀ x)))) fun T => ?_
  · intro T T' h1 h2
    refine progT_fst_congr h₁ h₂ x₁ c₁ x₂ c₂ G2 G5E _ _
      (fun i hi => hpre _ G2 G5E x T T' (h₁.2.2.2 i c₁) (hag _ default T T' (by subst hi; exact h1)))
      (fun i hi => hpre _ G2 G5E x T T' (h₂.2.2.2 i c₂) (hag _ default T T' (by subst hi; exact h2)))
  · have e : progT prog₁ prog₂ x₁ c₁ x₂ c₂ (G2, (G5E, setX T x)) =
        ((progT prog₁ prog₂ x₁ c₁ x₂ c₂ (G2, (G5E, setX T x))).1, (G5E, setX T x)) :=
      Prod.ext rfl (progT_snd h₁.1 h₂.1 _ _ _ _ _)
    show keyL L (Pf _ _) = keyL L (Pf _ _)
    rw [e, hPf _ G2 G5E x T T₀]

end Two

/-! ## The three levels -/

omit [CipherRow R] in
lemma recT_agree22 (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M) (T T' : KL L → ZK.Sim.Bytes 56) :
    (recT (G2, (G5E, set22 T x))).AgreeOff .h22 (recT (G2, (G5E, set22 T' x))) :=
  agreeOff_withTable (hbX_agreeOff_22 T T' x) _ _

omit [CipherRow R] in
lemma recT_agree21 (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M) (T T' : KL L → ZK.Sim.Bytes 136) :
    (recT (G2, (G5E, set21 T x))).AgreeOff .h21 (recT (G2, (G5E, set21 T' x))) :=
  agreeOff_withTable (hbX_agreeOff_21 T T' x) _ _

omit [CipherRow R] in
lemma recT_agreeMu (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M) (T T' : KL L → ZK.Sim.Bytes 32) :
    (recT (G2, (G5E, setMu T x))).AgreeOff .mu (recT (G2, (G5E, setMu T' x))) :=
  agreeOff_withTable (hbX_agreeOff_mu T T' x) _ _

omit [CipherRow R] in
/-- The record answers a point the same for two tables that agree at the point's key. -/
lemma recT_hash22 (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M) (T T' : KL L → ZK.Sim.Bytes 56)
    (b : ByteArray) (h : ∀ k, keyL L b = some k → T k = T' k) :
    (recT (G2, (G5E, set22 T x))).hash .h22 b = (recT (G2, (G5E, set22 T' x))).hash .h22 b := by
  rw [recT_hash_ne _ (by decide), recT_hash_ne _ (by decide), hbX_22_eq, hbX_22_eq]
  rcases hk : keyL L b with _ | k
  · rfl
  · simp only
    rw [show (set22 T x).2.2.2.2.2.1 = T from rfl, show (set22 T' x).2.2.2.2.2.1 = T' from rfl,
      h k hk]

omit [CipherRow R] in
lemma recT_hash21 (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M) (T T' : KL L → ZK.Sim.Bytes 136)
    (b : ByteArray) (h : ∀ k, keyL L b = some k → T k = T' k) :
    (recT (G2, (G5E, set21 T x))).hash .h21 b = (recT (G2, (G5E, set21 T' x))).hash .h21 b := by
  rw [recT_hash_ne _ (by decide), recT_hash_ne _ (by decide), hbX_21_eq, hbX_21_eq]
  rcases hk : keyL L b with _ | k
  · rfl
  · simp only
    rw [show (set21 T x).2.2.2.2.1 = T from rfl, show (set21 T' x).2.2.2.2.1 = T' from rfl,
      h k hk]

omit [CipherRow R] in
lemma recT_hashMu (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M) (T T' : KL L → ZK.Sim.Bytes 32)
    (b : ByteArray) (h : ∀ k, keyL L b = some k → T k = T' k) :
    (recT (G2, (G5E, setMu T x))).hash .mu b = (recT (G2, (G5E, setMu T' x))).hash .mu b := by
  rw [recT_hash_ne _ (by decide), recT_hash_ne _ (by decide), hbX_mu_eq, hbX_mu_eq]
  rcases hk : keyL L b with _ | k
  · rfl
  · simp only
    rw [show (setMu T x).2.1 = T from rfl, show (setMu T' x).2.1 = T' from rfl, h k hk]

/-! ### `H₂²` -/

lemma hPf22 (f : FD) (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M)
    (T T' : KL L → ZK.Sim.Bytes 56) :
    fPt22 f (G2, (G5E, set22 T x)) = fPt22 f (G2, (G5E, set22 T' x)) :=
  @cin2_congr22 (icPrg (rowFn G5E.2)) _ _ _ _ _ (recT_agree22 G2 G5E x T T')

lemma hPs22 (d : SimD) (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M)
    (T T' : KL L → ZK.Sim.Bytes 56) :
    sPt22 d (G2, (G5E, set22 T x)) = sPt22 d (G2, (G5E, set22 T' x)) := by
  rcases d with _ | ⟨st, _ | b⟩
  · rfl
  · simp only [sPt22, sim2]
  · simp only [sPt22, sim2]
    exact @cin2_congr22 (icPrg (rowFn G5E.2)) _ _ _ _ _ (recT_agree22 G2 G5E x T T')

lemma hpre22 (d : SD) (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M)
    (T T' : KL L → ZK.Sim.Bytes 56)
    (h : ∀ k, keyL L (sPt22 (some d) (G2, (G5E, set22 T x))) = some k → T k = T' k) :
    simPreT (p := p) (G2, (G5E, set22 T x)) d = simPreT (G2, (G5E, set22 T' x)) d := by
  obtain ⟨st, o⟩ := d
  rcases o with _ | b
  · simp only [simPreT, simPre]
  · simp only [sPt22, sim2] at h
    simp only [simPreT, simPre]
    exact @vPre_congr22 (icPrg (rowFn G5E.2)) _ _ _ _ _ (recT_agree22 G2 G5E x T T')
      (recT_hash22 G2 G5E x T T' _ h)

lemma hτ22 (d : SimD) (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M)
    (T T' : KL L → ZK.Sim.Bytes 56)
    (h : ∀ k, keyL L (sPt22 d (G2, (G5E, set22 T x))) = some k → T k = T' k) :
    sTau22 (p := p) d (G2, (G5E, set22 T x)) = sTau22 d (G2, (G5E, set22 T' x)) := by
  rcases d with _ | d
  · rfl
  · simp only [sTau22]
    rw [hpre22 d G2 G5E x T T' h]

/-! ### `H₂¹` -/

lemma hPf21 (f : FD) (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M)
    (T T' : KL L → ZK.Sim.Bytes 136) :
    fPt21 f (G2, (G5E, set21 T x)) = fPt21 f (G2, (G5E, set21 T' x)) :=
  @cin1_congr21 (icPrg (rowFn G5E.2)) _ _ _ _ (recT_agree21 G2 G5E x T T')

lemma hPs21 (d : SimD) (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M)
    (T T' : KL L → ZK.Sim.Bytes 136) :
    sPt21 d (G2, (G5E, set21 T x)) = sPt21 d (G2, (G5E, set21 T' x)) := by
  rcases d with _ | ⟨st, _ | b⟩
  · rfl
  · simp only [sPt21, sim1]
  · simp only [sPt21, sim1]
    exact @cin1_congr21 (icPrg (rowFn G5E.2)) _ _ _ _ (recT_agree21 G2 G5E x T T')

lemma hpre21 (d : SD) (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M)
    (T T' : KL L → ZK.Sim.Bytes 136)
    (h : ∀ k, keyL L (sPt21 (some d) (G2, (G5E, set21 T x))) = some k → T k = T' k) :
    simPreT (p := p) (G2, (G5E, set21 T x)) d = simPreT (G2, (G5E, set21 T' x)) d := by
  obtain ⟨st, o⟩ := d
  rcases o with _ | b
  · simp only [simPreT, simPre]
  · simp only [sPt21, sim1] at h
    simp only [simPreT, simPre]
    exact @vPre_congr21 (icPrg (rowFn G5E.2)) _ _ _ _ _ (recT_agree21 G2 G5E x T T')
      (recT_hash21 G2 G5E x T T' _ h)

lemma hτ21 (d : SimD) (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M)
    (T T' : KL L → ZK.Sim.Bytes 136)
    (h : ∀ k, keyL L (sPt21 d (G2, (G5E, set21 T x))) = some k → T k = T' k) :
    sTau21 d (G2, (G5E, set21 T x)) = sTau21 d (G2, (G5E, set21 T' x)) := by
  simp only [sTau21]
  rw [recT_hash21 G2 G5E x T T' _ h, hPs21 d G2 G5E x T T']

/-! ### `H₂⁰` -/

lemma hpreMu (d : SD) (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M)
    (T T' : KL L → ZK.Sim.Bytes 32) (hdl : d.1.delayed = false)
    (h : ∀ k, keyL L (sPtMu (some d)) = some k → T k = T' k) :
    simPreT (p := p) (G2, (G5E, setMu T x)) d = simPreT (G2, (G5E, setMu T' x)) d := by
  obtain ⟨st, o⟩ := d
  rcases o with _ | b
  · simp only [simPreT, simPre]
  · simp only [sPtMu] at h
    simp only [simPreT, simPre]
    exact @vPre_congrMu (icPrg (rowFn G5E.2)) _ _ _ _ _ hdl (recT_agreeMu G2 G5E x T T')
      (recT_hashMu G2 G5E x T T' _ h)

omit [CipherRow R] in
lemma hτMu (d : SimD) (G2 : Tab2G p) (G5E : Tab5F × (Blk → R)) (x : XTab L M)
    (T T' : KL L → ZK.Sim.Bytes 32) (h : ∀ k, keyL L (sPtMu d) = some k → T k = T' k) :
    sTauMu d (G2, (G5E, setMu T x)) = sTauMu d (G2, (G5E, setMu T' x)) := by
  simp only [sTauMu]
  rw [recT_hashMu G2 G5E x T T' _ h]

/-! ## `ε_hit` -/

/-- **A computation that reads each chain table** (`H₂⁰`, `H₂¹`, `H₂²` on the short inputs) **by a
decision tree** with `q_μ`, `q₂₁`, `q₂₂` queries, at every value of everything else (`H₂³`, `H₅`,
the cipher and the other tables, which it reads freely). -/
def TreeT {Out : Type*} (qMu q21 q22 : ℕ) (F : ShT R p L M → Out) : Prop :=
  (∀ G2 G5E x, QTree (fun T => F (G2, (G5E, setMu T x))) qMu) ∧
    (∀ G2 G5E x, QTree (fun T => F (G2, (G5E, set21 T x))) q21) ∧
    (∀ G2 G5E x, QTree (fun T => F (G2, (G5E, set22 T x))) q22)

/-- **The adversaries of `ε_hit`**: the last stage reads each chain table by a decision tree with
`q_μ`, `q₂₁`, `q₂₂` queries (`TreeT`), at every value of the slices. -/
def AdmHit {G Out : Type*} (qMu q21 q22 : ℕ) (F : G → G → ShT R p L M → Out) : Prop :=
  ∀ g₁ g₂, TreeT qMu q21 q22 (F g₁ g₂)

omit [CipherRow R] in
/-- A last stage that does not read the tables is admissible with no queries. -/
lemma admHit_const {G Out : Type*} (o : Out) :
    AdmHit (R := R) (p := p) (L := L) (M := M) (G := G) 0 0 0 fun _ _ _ => o :=
  fun _ _ => ⟨fun _ _ _ => .ret _ _, fun _ _ _ => .ret _ _, fun _ _ _ => .ret _ _⟩

/-- **The bound**: `2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸)`. -/
noncomputable def epsHit (qMu q21 q22 : ℕ) : ℝ :=
  2 * ((qMu + 3 : ℕ) * (1 / 2 ^ 256) + (q21 + 3 : ℕ) * (1 / 2 ^ 1088) +
    (q22 + 3 : ℕ) * (1 / 2 ^ 448))

lemma card_bytes (n : ℕ) : Fintype.card (ZK.Sim.Bytes n) = 2 ^ (8 * n) := by
  rw [Fintype.card_fun, Fintype.card_fin, Prob.card_uint8, pow_mul]

/-- **A tape with the tables as a component**: the tables of a tape, and the tape with the extra
table replaced. -/
structure TLens (Ω : Type*) (R : Type) (p : Params) (L M : ℕ) where
  sh : Ω → ShT R p L M
  stX : XTab L M → Ω → Ω
  get_set : ∀ z, stX (sh z).2.2 z = z
  sh_set : ∀ x z, sh (stX x z) = ((sh z).1, ((sh z).2.1, x))
  set_set : ∀ x x' z, stX x (stX x' z) = stX x z

/-- The tapes `W × ShT`. -/
def lensS (W : Type*) : TLens (W × ShT R p L M) R p L M :=
  ⟨fun z => z.2, fun x z => (z.1, (z.2.1, (z.2.2.1, x))), fun _ => rfl, fun _ _ => rfl,
    fun _ _ _ => rfl⟩

/-- The tapes `W₁ × (W₂ × ShT)` (the tape of `ProgEv`). -/
def lensR (W₁ W₂ : Type*) : TLens (W₁ × (W₂ × ShT R p L M)) R p L M :=
  ⟨fun z => z.2.2, fun x z => (z.1, (z.2.1, (z.2.2.1, (z.2.2.2.1, x)))), fun _ => rfl,
    fun _ _ => rfl, fun _ _ _ => rfl⟩

section Tape

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] (ℓ : TLens Ω R p L M)

lemma pr_E22_le (d : Ω → SimD) (hd : ∀ x z, d (ℓ.stX x z) = d z) (f : Ω → FD) {q : ℕ}
    (hop : ∀ z, QTree (fun T => keyL L (fPt22 (f (ℓ.stX (set22 T (ℓ.sh z).2.2) z))
      ((ℓ.sh z).1, ((ℓ.sh z).2.1, set22 T (ℓ.sh z).2.2)))) q) :
    pr Ω (fun z => Ev (fPt22 (f z) (ℓ.sh z)) (sPt22 (d z) (ℓ.sh z)) (sTau22 (d z) (ℓ.sh z))
      (get22 (ℓ.sh z).2.2)) ≤ (q + 1 : ℕ) * (1 / 2 ^ (8 * 56)) := by
  have h := pr_level_le (fun T z => ℓ.stX (set22 T (ℓ.sh z).2.2) z) (fun z => get22 (ℓ.sh z).2.2)
    (fun z => ℓ.get_set z) (fun T z => by rw [ℓ.sh_set]; rfl)
    (fun T T' z => by rw [ℓ.sh_set, ℓ.set_set]; rfl) (fun z => fPt22 (f z) (ℓ.sh z))
    (fun z => sPt22 (d z) (ℓ.sh z)) (fun z => sTau22 (d z) (ℓ.sh z))
    (fun T T' z => by
      simp only [hd, ℓ.sh_set]
      exact hPs22 _ _ _ _ _ _)
    (fun T T' z hT => by
      simp only [hd, ℓ.sh_set] at hT ⊢
      exact hτ22 _ _ _ _ _ _ hT)
    (fun z => by simpa only [ℓ.sh_set] using hop z)
  rw [card_bytes] at h
  exact_mod_cast h

lemma pr_E21_le (d : Ω → SimD) (hd : ∀ x z, d (ℓ.stX x z) = d z) (f : Ω → FD) {q : ℕ}
    (hop : ∀ z, QTree (fun T => keyL L (fPt21 (f (ℓ.stX (set21 T (ℓ.sh z).2.2) z))
      ((ℓ.sh z).1, ((ℓ.sh z).2.1, set21 T (ℓ.sh z).2.2)))) q) :
    pr Ω (fun z => Ev (fPt21 (f z) (ℓ.sh z)) (sPt21 (d z) (ℓ.sh z)) (sTau21 (d z) (ℓ.sh z))
      (get21 (ℓ.sh z).2.2)) ≤ (q + 1 : ℕ) * (1 / 2 ^ (8 * 136)) := by
  have h := pr_level_le (fun T z => ℓ.stX (set21 T (ℓ.sh z).2.2) z) (fun z => get21 (ℓ.sh z).2.2)
    (fun z => ℓ.get_set z) (fun T z => by rw [ℓ.sh_set]; rfl)
    (fun T T' z => by rw [ℓ.sh_set, ℓ.set_set]; rfl) (fun z => fPt21 (f z) (ℓ.sh z))
    (fun z => sPt21 (d z) (ℓ.sh z)) (fun z => sTau21 (d z) (ℓ.sh z))
    (fun T T' z => by
      simp only [hd, ℓ.sh_set]
      exact hPs21 _ _ _ _ _ _)
    (fun T T' z hT => by
      simp only [hd, ℓ.sh_set] at hT ⊢
      exact hτ21 _ _ _ _ _ _ hT)
    (fun z => by simpa only [ℓ.sh_set] using hop z)
  rw [card_bytes] at h
  exact_mod_cast h

omit [CipherRow R] in
lemma pr_EMu_le (d : Ω → SimD) (hd : ∀ x z, d (ℓ.stX x z) = d z) (f : Ω → FD) {q : ℕ}
    (hop : ∀ z, QTree (fun T => keyL L (fPtMu (f (ℓ.stX (setMu T (ℓ.sh z).2.2) z)))) q) :
    pr Ω (fun z => Ev (fPtMu (f z)) (sPtMu (d z)) (sTauMu (d z) (ℓ.sh z))
      (getMu (ℓ.sh z).2.2)) ≤ (q + 1 : ℕ) * (1 / 2 ^ (8 * 32)) := by
  have h := pr_level_le (fun T z => ℓ.stX (setMu T (ℓ.sh z).2.2) z) (fun z => getMu (ℓ.sh z).2.2)
    (fun z => ℓ.get_set z) (fun T z => by rw [ℓ.sh_set]; rfl)
    (fun T T' z => by rw [ℓ.sh_set, ℓ.set_set]; rfl) (fun z => fPtMu (f z))
    (fun z => sPtMu (d z)) (fun z => sTauMu (d z) (ℓ.sh z))
    (fun T T' z => by simp only [hd])
    (fun T T' z hT => by
      simp only [hd, ℓ.sh_set] at hT ⊢
      exact hτMu _ _ _ _ _ _ hT)
    hop
  rw [card_bytes] at h
  exact_mod_cast h

/-- **A hit on one simulation**: for a forgery whose three chain points are computed by trees
with `q₂₂`, `q₂₁`, `q_μ` queries, and a simulation that does not depend on the extra table,

    Pr[HitAt] ≤ (q₂₂+1)·2⁻⁴⁴⁸ + (q₂₁+1)·2⁻¹⁰⁸⁸ + (q_μ+1)·2⁻²⁵⁶. -/
theorem pr_hitAt_le (d : Ω → SimD) (hd : ∀ x z, d (ℓ.stX x z) = d z) (f : Ω → FD)
    {q22 q21 qMu : ℕ}
    (h22 : ∀ z, QTree (fun T => keyL L (fPt22 (f (ℓ.stX (set22 T (ℓ.sh z).2.2) z))
      ((ℓ.sh z).1, ((ℓ.sh z).2.1, set22 T (ℓ.sh z).2.2)))) q22)
    (h21 : ∀ z, QTree (fun T => keyL L (fPt21 (f (ℓ.stX (set21 T (ℓ.sh z).2.2) z))
      ((ℓ.sh z).1, ((ℓ.sh z).2.1, set21 T (ℓ.sh z).2.2)))) q21)
    (hMu : ∀ z, QTree (fun T => keyL L (fPtMu (f (ℓ.stX (setMu T (ℓ.sh z).2.2) z)))) qMu) :
    pr Ω (fun z => HitAt (f z) (ℓ.sh z) (d z)) ≤
      (q22 + 1 : ℕ) * (1 / 2 ^ (8 * 56)) + (q21 + 1 : ℕ) * (1 / 2 ^ (8 * 136)) +
        (qMu + 1 : ℕ) * (1 / 2 ^ (8 * 32)) := by
  refine (pr_or_le _ _).trans ?_
  refine add_assoc _ _ (_ : ℝ) ▸ add_le_add (pr_E22_le ℓ d hd f h22) ?_
  exact (pr_or_le _ _).trans (add_le_add (pr_E21_le ℓ d hd f h21) (pr_EMu_le ℓ d hd f hMu))

end Tape

-- (the final `ring` step multiplies out `2⁴⁴⁸` and `2¹⁰⁸⁸`)
set_option exponentiation.threshold 1100 in
/-- **`ε_hit` for two simulated proofs, with the chain hashes random tables.** With `H₂⁰`, `H₂¹`,
`H₂²` uniform tables on the inputs of at most `L` bytes (`hbX`), two simulators whose programmings
are `SimProg`, and a freshness `Fresh` under which a forgery (`fd`) has chain inputs of at most
`L` bytes (`hfd`) and an `H₂⁰` input other than those of the simulated statements (`hfr₁`,
`hfr₂`): against adversaries that read the chain tables with `q_μ`, `q₂₁`, `q₂₂` queries
(`AdmHit`), a fresh forgery whose verifier reads a programmed `H₂³` point (`hE`) has probability

    ≤ 2·((q_μ+3)·2⁻²⁵⁶ + (q₂₁+3)·2⁻¹⁰⁸⁸ + (q₂₂+3)·2⁻⁴⁴⁸).

Per simulation and level the forgery must answer a target the simulation fixed, at a point it
did not query (`hit_cases`, `pr_level_le`); its point is computed by a tree with the adversary's
queries plus the two simulations' points (`qtree_forger`). -/
theorem progEv_chain [Fintype R] [Nonempty R] {I₁ I₂ P₁ P₂ Out G : Type} {C₁ C₂ : Type}
    [Fintype C₁] [Fintype C₂] [Fintype G] [Nonempty C₁] [Nonempty C₂] [Nonempty G]
    {sim₁ : I₁ → C₁ → Option P₁} {prog₁ : I₁ → C₁ → ShT R p L M → ShT R p L M}
    {sim₂ : I₂ → C₂ → Option P₂} {prog₂ : I₂ → C₂ → ShT R p L M → ShT R p L M}
    {D₁ : I₁ → C₁ → SD} {D₂ : I₂ → C₂ → SD} (h₁ : SimProg prog₁ D₁) (h₂ : SimProg prog₂ D₂)
    (fd : Out → FD) {Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop}
    {E : Out → ShT R p L M → ShT R p L M → Prop}
    (hfd : ∀ p₁ p₂ op, Fresh p₁ p₂ op → FOk L (fd op).1)
    (hE : ∀ op t' t, E op t' t → HitG (fd op) t' t)
    (hfr₁ : ∀ x₁ c₁ p₂ op i, Fresh (pairO x₁ (simO sim₁ x₁ c₁)) p₂ op → x₁ = some i →
      (∃ b, (D₁ i c₁).2 = .ok b) → muIn (fd op).1 ≠ muIn (D₁ i c₁).1)
    (hfr₂ : ∀ p₁ x₂ c₂ op i, Fresh p₁ (pairO x₂ (simO sim₂ x₂ c₂)) op → x₂ = some i →
      (∃ b, (D₂ i c₂).2 = .ok b) → muIn (fd op).1 ≠ muIn (D₂ i c₂).1)
    (qMu q21 q22 : ℕ) :
    ProgEv sim₁ prog₁ sim₂ prog₂ Fresh E (AdmHit (G := G) qMu q21 q22) (epsHit qMu q21 q22) := by
  intro α _ _ x₁ x₂ out hout
  let Tp := (α × (C₁ × G)) × ((C₂ × G) × ShT R p L M)
  let ℓ : TLens Tp R p L M := lensR _ _
  let i₂ : Tp → Option I₂ := fun z => x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)
  let op : Tp → Out := fun z =>
    out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1) (simO sim₂ (i₂ z) z.2.1.1) z.1.2.2 z.2.1.2
      (progT prog₁ prog₂ (x₁ z.1.1) z.1.2.1 (i₂ z) z.2.1.1 z.2.2)
  let d₁ : Tp → SimD := fun z => sdO D₁ (x₁ z.1.1) z.1.2.1
  let d₂ : Tp → SimD := fun z => sdO D₂ (i₂ z) z.2.1.1
  have hH : ∀ (d : Tp → SimD), (∀ x z, d (ℓ.stX x z) = d z) →
      pr Tp (fun z => HitAt (fd (op z)) z.2.2 (d z)) ≤
        (q22 + 2 + 1 : ℕ) * (1 / 2 ^ (8 * 56)) + (q21 + 2 + 1 : ℕ) * (1 / 2 ^ (8 * 136)) +
          (qMu + 2 + 1 : ℕ) * (1 / 2 ^ (8 * 32)) := by
    intro d hd
    refine pr_hitAt_le ℓ d hd (fun z => fd (op z)) (fun z => ?_) (fun z => ?_) (fun z => ?_)
    · exact qtree_forger set22 (fun o t => fPt22 (fd o) t) sPt22 (fun o => hPf22 (fd o)) hPs22
        (fun d G2 G5E x T T' _ h => hpre22 d G2 G5E x T T' h) h₁ h₂
        (out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1) (simO sim₂ (i₂ z) z.2.1.1) z.1.2.2 z.2.1.2)
        (fun G2 G5E x => (hout _ _ _ z.1.2.2 z.2.1.2).2.2 G2 G5E x)
        (x₁ z.1.1) z.1.2.1 (i₂ z) z.2.1.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2
    · exact qtree_forger set21 (fun o t => fPt21 (fd o) t) sPt21 (fun o => hPf21 (fd o)) hPs21
        (fun d G2 G5E x T T' _ h => hpre21 d G2 G5E x T T' h) h₁ h₂
        (out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1) (simO sim₂ (i₂ z) z.2.1.1) z.1.2.2 z.2.1.2)
        (fun G2 G5E x => (hout _ _ _ z.1.2.2 z.2.1.2).2.1 G2 G5E x)
        (x₁ z.1.1) z.1.2.1 (i₂ z) z.2.1.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2
    · exact qtree_forger setMu (fun o _ => fPtMu (fd o)) (fun d _ => sPtMu d)
        (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
        (fun d G2 G5E x T T' hdl h => hpreMu d G2 G5E x T T' hdl h) h₁ h₂
        (out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1) (simO sim₂ (i₂ z) z.2.1.1) z.1.2.2 z.2.1.2)
        (fun G2 G5E x => (hout _ _ _ z.1.2.2 z.2.1.2).1 G2 G5E x)
        (x₁ z.1.1) z.1.2.1 (i₂ z) z.2.1.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2
  refine (Privacy.pr_mono (Q := fun z => HitAt (fd (op z)) z.2.2 (d₁ z) ∨
    HitAt (fd (op z)) z.2.2 (d₂ z)) fun z hz =>
      hit_cases h₁ h₂ (fd (op z)) (hfd _ _ _ hz.1) _ _ _ _ _
        (fun i hi => hfr₁ _ _ _ _ i hz.1 hi) (fun i hi => hfr₂ _ _ _ _ i hz.1 hi)
        (hE _ _ _ hz.2)).trans ?_
  refine (pr_or_le _ _).trans ?_
  refine (add_le_add (hH d₁ fun _ _ => rfl) (hH d₂ fun _ _ => rfl)).trans (le_of_eq ?_)
  simp only [epsHit, show 8 * 56 = 448 from rfl, show 8 * 136 = 1088 from rfl,
    show 8 * 32 = 256 from rfl]
  push_cast
  ring

end Chain

end VoleMole.Theft.Hit
